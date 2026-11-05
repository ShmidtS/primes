#!/usr/bin/env python3
"""Environment-derived registry of Hagi's named formal premises.

Operational contract: build Hagi normally, run AssumptionBinders.lean,
and consume its actual forall-telescope JSON. No source/comment regex
participates in the inventory. Different declaration/ordinal binders
are never collapsed by identifier spelling. Labels are not semantic
closures, physical measurements, or counts of distinct mathematical goals.
"""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOCK = Path(__file__).resolve().parent / "assumptions.lock"

CANONICAL_INFO = {
    f"Hagi.Prelude.{name}" for name in
    ["klDef", "ceDef", "entDef", "tvDef", "softDef"]
}
LEGACY_INFO = {
    "Hagi.Core.lse", "Hagi.Core.softmaxP",
    "Hagi.Energy.entropyProduction", "Hagi.Information.shannon",
    "Hagi.Information.tvHalf", "Hagi.Step.sourceEntropy",
    "Hagi.Data.softmaxW",
}
MATRIX_INFO = {"Hagi.Information.entropy"}
EXCLUDED_PRIMITIVES = {"Hagi.Omni.entryCount": "index-counter, not entropy"}
ALL_CURATED_PRIMITIVES = (
    CANONICAL_INFO | LEGACY_INFO | MATRIX_INFO | set(EXCLUDED_PRIMITIVES)
)
VALID_RECORD_KINDS = {"declaration", "empirical", "structural", "primitive_candidate"}


def run_checked(args, log_name):
    """Return UTF-8 output only after the actual subprocess exits zero."""
    result = subprocess.run(
        args, cwd=ROOT, text=True, encoding="utf-8", errors="replace",
        capture_output=True, timeout=1800,
    )
    log_dir = ROOT / ".tmp"
    log_dir.mkdir(exist_ok=True)
    (log_dir / f"{log_name}.stdout.log").write_text(result.stdout, encoding="utf-8")
    (log_dir / f"{log_name}.stderr.log").write_text(result.stderr, encoding="utf-8")
    if result.returncode != 0:
        raise RuntimeError(
            f"command failed ({result.returncode}): {' '.join(args)}; "
            f"see .tmp/{log_name}.stdout.log and .tmp/{log_name}.stderr.log"
        )
    return result.stdout


def read_inventory():
    """Always rebuild normally before importing the root environment."""
    run_checked(["lake", "build", "Hagi"], "assumption-scan-root-build")
    return run_checked(
        ["lake", "env", "lean", "scripts/AssumptionBinders.lean"],
        "assumption-binders",
    )


def parse_inventory(text):
    """Strict JSONL parsing: malformed records are not a zero inventory."""
    records = []
    for line_number, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise ValueError(f"invalid inventory JSON at line {line_number}: {exc}") from exc
        if not isinstance(row, dict):
            raise ValueError(f"inventory line {line_number} is not an object")
        kind = row.get("kind")
        if kind == "header":
            if row.get("format") != "v2" or row.get("root") != "Hagi":
                raise ValueError("unsupported inventory root/version")
            if row.get("binder_source") != "Lean.Environment.forallTelescope":
                raise ValueError("unexpected inventory source")
        elif kind in VALID_RECORD_KINDS:
            for key in ["module", "declaration"]:
                if not isinstance(row.get(key), str) or not row[key] or row[key] == "?":
                    raise ValueError(f"invalid {key} at line {line_number}")
            if kind == "primitive_candidate":
                if row.get("declaration") not in ALL_CURATED_PRIMITIVES:
                    raise ValueError(
                        f"uncurated information candidate: {row.get('declaration')}"
                    )
                records.append(row)
                continue
            if not isinstance(row.get("declaration_kind"), str):
                raise ValueError(f"missing declaration kind at line {line_number}")
            if not isinstance(row.get("type"), str) or not row["type"]:
                raise ValueError(f"missing type at line {line_number}")
            if kind in {"empirical", "structural"}:
                binder = row.get("binder")
                if not isinstance(binder, str) or not binder.startswith("h"):
                    raise ValueError(f"invalid named binder at line {line_number}")
                if kind == "empirical" and not binder.startswith("h_emp_"):
                    raise ValueError(f"invalid empirical binder at line {line_number}")
                if type(row.get("ordinal")) is not int or row["ordinal"] < 1:
                    raise ValueError(f"invalid binder ordinal at line {line_number}")
                if not isinstance(row.get("execution_name_candidate"), bool):
                    raise ValueError(f"invalid execution marker at line {line_number}")
                lower_name = binder.lower()
                expected_marker = any(word in lower_name for word in
                                      ["exec", "descent", "sample"])
                if row["execution_name_candidate"] != expected_marker:
                    raise ValueError(f"execution marker does not match binder at line {line_number}")
        else:
            raise ValueError(f"invalid inventory kind at line {line_number}: {kind}")
        records.append(row)
    if sum(row.get("kind") == "header" for row in records) != 1:
        raise ValueError("expected exactly one valid inventory header")
    return records


def _scope(rows, kind):
    return [row for row in rows if row.get("kind") == kind]


def source(row, include_type=True):
    text = f"{row['module']} | {row['declaration']}"
    if "ordinal" in row:
        text += f" | {row['ordinal']}"
    if "binder" in row:
        text += f" | {row['binder']}"
    if row.get("execution_name_candidate") and row["kind"] == "structural":
        text += " | execution-name-candidate"
    if include_type:
        text += f" | {' '.join(row['type'].split())}"
    return text


def registry(records):
    empirical = sorted(_scope(records, "empirical"),
                       key=lambda r: (r["module"], r["declaration"], r["ordinal"]))
    structural = sorted(_scope(records, "structural"),
                        key=lambda r: (r["module"], r["declaration"], r["ordinal"]))
    named = sorted(_scope(records, "declaration"),
                   key=lambda r: (r["module"], r["declaration"]))
    primitives = sorted(_scope(records, "primitive_candidate"),
                        key=lambda r: (r["module"], r["declaration"]))
    expected = ALL_CURATED_PRIMITIVES
    present = {row["declaration"] for row in primitives}
    missing = expected - present
    if missing:
        raise ValueError(f"curated information definitions missing: {sorted(missing)}")
    excluded = [row for row in primitives
                if row["declaration"] in EXCLUDED_PRIMITIVES]
    accepted = [row for row in primitives
                if row["declaration"] not in EXCLUDED_PRIMITIVES]
    unknown = [row["declaration"] for row in primitives
               if row["declaration"] not in ALL_CURATED_PRIMITIVES]
    if unknown:
        raise ValueError(f"unclassified information definitions: {unknown}")
    keys = {(row["declaration"], row["ordinal"]) for row in empirical}
    structural_keys = {(row["declaration"], row["ordinal"]) for row in structural}
    operational = [row for row in structural if row["execution_name_candidate"]]
    operational_keys = {(row["declaration"], row["ordinal"]) for row in operational}
    lines = [
        "# HAGI assumption inventory v2",
        "source: Lean.Environment.forallTelescope over Hagi's root",
        "scope: top-level formal parameters whose elaborated names start with h",
        "meaning: occurrences, NOT counts of distinct theorems or unproved goals",
        "Named h-prefix occurrences include repeatable parameter hypotheses; types are authoritative.",
        "",
        "[empirical summary]",
        f"h_emp binder occurrences: {len(empirical)}",
        f"h_emp declaration+ordinal keys: {len(keys)}",
        f"h_emp source modules: {len({row['module'] for row in empirical})}",
        f"h_emp distinct binder labels: {len({row['binder'] for row in empirical})}",
        f"h_emp-named declaration records: {len(named)}",
        "",
        "[structural/math summary]",
        f"named structural binder occurrences: {len(structural)}",
        f"named structural declaration+ordinal keys: {len(structural_keys)}",
        f"named structural source modules: {len({row['module'] for row in structural})}",
        "Execution candidates require a complete h-prefixed formal identifier with",
        "exec/descent/sample in its name; this is a name-subset, NOT proof of execution.",
        f"execution-name candidate occurrences: {len(operational)}",
        f"execution-name declaration+ordinal keys: {len(operational_keys)}",
        f"execution-name distinct labels: {len({row['binder'] for row in operational})}",
        "",
        "[information primitive summary]",
        "Definitions are explicit curated FQ constants, not ent-* regex matches.",
        f"canonical finite-real information definitions: {len(CANONICAL_INFO & present)}",
        f"legacy named information definitions: {len(LEGACY_INFO & present)}",
        f"matrix spectral entropy definitions: {len(MATRIX_INFO & present)}",
        f"excluded primitive candidates: {len(excluded)}",
        "Spectral matrix entropy and finite Shannon entropy are distinct objects.",
        "",
        "[empirical binders]",
    ]
    lines.extend(source(row) for row in empirical)
    lines.extend(["", "[structural/math named binders]"])
    lines.extend(source(row) for row in structural)
    lines.extend(["", "[h_emp-named declaration records]"])
    lines.extend(source(row) for row in named)
    lines.extend(["", "[information primitives]"])
    for row in accepted:
        declaration = row["declaration"]
        if declaration in CANONICAL_INFO:
            group = "canonical-finite-real"
        elif declaration in LEGACY_INFO:
            group = "legacy-information"
        else:
            group = "matrix-spectral-entropy"
        lines.append(f"{row['module']} | {declaration} | {group}")
    lines.extend(["", "[excluded primitive candidates]"])
    for row in excluded:
        name = row["declaration"]
        lines.append(f"{row['module']} | {name} | {EXCLUDED_PRIMITIVES[name]}")
    lines.extend([
        "",
        "[closure meaning]",
        "These rows describe formal inputs at named public interfaces.",
        "They do not prove physical fidelity, independence, semantic optimality or closure.",
        "Analytical discharge needs a new specialization/proof; h_emp legacy types stay intact.",
        "A repeated h_emp label across public declarations is counted per actual declaration+ordinal.",
        "",
    ])
    return "\n".join(lines)


def main():
    update = "--update" in sys.argv
    try:
        records = parse_inventory(read_inventory())
        text = registry(records)
    except (RuntimeError, ValueError) as exc:
        print(f"ASSUMPTIONSCAN: FAIL ({exc})")
        return 1
    if update or not LOCK.exists():
        LOCK.write_text(text, encoding="utf-8", newline="\n")
        print(f"ASSUMPTIONSCAN: wrote {LOCK.name} (environment v2, "
              f"{sum(r.get('kind') == 'empirical' for r in records)} empirical binders)")
        return 0
    if LOCK.read_text(encoding="utf-8") != text:
        print("ASSUMPTIONSCAN: FAIL (registry drifted; inspect v2 changes and then "
              "run `python scripts/AssumptionScan.py --update` deliberately)")
        return 1
    empirical = _scope(records, "empirical")
    structural = _scope(records, "structural")
    print(f"ASSUMPTIONSCAN: PASS (environment v2; {len(empirical)} empirical binders "
          f"in {len({r['module'] for r in empirical})} modules; "
          f"{len(structural)} named structural binders; "
          f"{len(LEGACY_INFO)} legacy info defs, matrix separate)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
