#!/usr/bin/env python3
"""GenTheoremIndex orchestrator (C361, audit step 2.1).

Combines three inputs into .omc/analysis/generated/theorem-index.md:

  1. `lake env lean --run scripts/GenTheoremIndex.lean` — per-module
     environment census (theorem/def counts, noncomputable decls)
     and the global axiom traversal (AllAxiomCheck algorithm,
     allowed = propext / Classical.choice / Quot.sound);
  2. a fresh AssumptionScan scan (per-file premise names);
  3. the typed premise registry (scripts/premise_registry.toml).

Per-module premise status (enum Proven|Conditional|Empirical|
Speculative|Deprecated):
  Speculative  — module in the C347 growth quarantine or under
                 Hagi/Research/;
  Deprecated   — module under Hagi/Research/Legacy/ (C456);
  Empirical    — an empirical-class premise appears in the module;
  Conditional  — only mathematical/model/operational/approximation
                 premises appear;
  Proven       — no premises appear.

The output file is GENERATED (header says so) — never hand-edit.
Regenerate: python scripts/GenTheoremIndex.py
"""
import subprocess
import sys
from pathlib import Path

import AssumptionScan
import PremiseRegistry

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / ".omc" / "analysis" / "generated" / "theorem-index.md"
LEAN_SCRIPT = "scripts/GenTheoremIndex.lean"


def run_lean_census():
    proc = subprocess.run(
        ["lake", "env", "lean", "--run", LEAN_SCRIPT],
        capture_output=True, text=True, encoding="utf-8",
        errors="replace", cwd=ROOT)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise RuntimeError(f"{LEAN_SCRIPT} failed (exit {proc.returncode})")
    stats, nc, axioms = {}, {}, None
    for line in proc.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) != 3:
            continue
        mod, kind, val = parts
        if mod == "AXIOMS":
            axioms = (val, set(filter(None, val and parts[1].split(","))))
        elif kind == "theorems":
            stats.setdefault(mod, {"theorems": 0, "defs": 0})
            stats[mod]["theorems"] = int(val)
        elif kind == "defs":
            stats.setdefault(mod, {"theorems": 0, "defs": 0})
            stats[mod]["defs"] = int(val)
        elif kind == "noncomputable":
            nc.setdefault(mod, []).append(val)
    return stats, nc, axioms


def module_file(module):
    return module.replace(".", "/") + ".lean"


def classify_modules(hmap, operational_by_file, data):
    """Per-file premise status map (pre-quarantine/deprecated)."""
    premises = data.get("premises", {})
    status = {}
    all_files = sorted(set(hmap) | set(operational_by_file) |
                       {k.split("::")[0] for k in premises if "::" in k})
    for rel in all_files:
        names = set(hmap.get(rel, ())) | set(operational_by_file.get(rel, ()))
        kinds = set()
        for n in names:
            entry = premises.get(n)
            if entry:
                kinds.add(entry.get("type"))
        for key in premises:
            if "::" in key and key.split("::")[0] == rel:
                kinds.add(premises[key].get("type"))
        if "empirical" in kinds:
            status[rel] = "Empirical"
        elif kinds:
            status[rel] = "Conditional"
        else:
            status[rel] = "Proven"
    return status


def module_status(rel, base_status, modules):
    # C456: deprecated_prefixes (Hagi/Research/Legacy/) checked BEFORE
    # research_prefixes — Deprecated is more specific than Speculative,
    # or archived Legacy modules would silently reclassify.
    for p in modules.get("deprecated_prefixes", []):
        if rel.startswith(p):
            return "Deprecated"
    if rel in modules.get("quarantine", []):
        return "Speculative"
    for p in modules.get("research_prefixes", []):
        if rel.startswith(p):
            return "Speculative"
    return base_status


def operational_by_file():
    from pathlib import Path as P
    out = {}
    for f in sorted((ROOT / "Hagi").rglob("*.lean")):
        code = AssumptionScan.strip_comments(
            f.read_text(encoding="utf-8", errors="replace"))
        ops = sorted(set(AssumptionScan.OPERATIONAL.findall(code)))
        if ops:
            out[f.relative_to(ROOT).as_posix()] = ops
    return out


def generate(stats, nc, axioms, hmap, op_by_file, data):
    modules = data.get("modules", {})
    base = classify_modules(hmap, op_by_file, data)
    lines = [
        "# Theorem index (generated)",
        "",
        "GENERATED - do not edit. Regenerate with",
        "`python scripts/GenTheoremIndex.py` (runs a Lean environment",
        "census, a fresh AssumptionScan scan, and the typed premise",
        "registry).",
        "",
        "Per-module theorem/def counts, noncomputable declarations,",
        "premise status (Proven|Conditional|Empirical|Speculative|",
        "Deprecated), and the global axiom profile of all Hagi.*",
        "theorems.",
        "",
        "## Summary",
        "",
    ]
    n_th = sum(m["theorems"] for m in stats.values())
    n_def = sum(m["defs"] for m in stats.values())
    counts = {}
    for mod in sorted(stats):
        rel = module_file(mod)
        st = module_status(rel, base.get(rel, "Proven"), modules)
        counts[st] = counts.get(st, 0) + 1
    lines.append(f"- modules: {len(stats)}")
    lines.append(f"- theorems: {n_th}")
    lines.append(f"- defs: {n_def}")
    lines.append(f"- noncomputable decls: {sum(len(v) for v in nc.values())}")
    for st in PremiseRegistry.STATUS_ENUM:
        lines.append(f"- status {st}: {counts.get(st, 0)} modules")
    marker, found = axioms
    lines.append(f"- global axioms of all Hagi.* theorems: "
                 f"{', '.join(sorted(found)) if found else 'none'} "
                 f"({marker})")
    lines += ["", "## Per-module index", "",
              "| module | theorems | defs | noncomputable | premises | status |",
              "|---|---|---|---|---|---|"]
    for mod in sorted(stats):
        rel = module_file(mod)
        st = module_status(rel, base.get(rel, "Proven"), modules)
        ncs = nc.get(mod, [])
        nc_cell = ", ".join(n.split(".")[-1] for n in ncs) or "-"
        has = bool(base.get(rel, "Proven") != "Proven")
        lines.append(f"| {mod} | {stats[mod]['theorems']} | "
                     f"{stats[mod]['defs']} | {nc_cell} | "
                     f"{'yes' if has else 'no'} | {st} |")
    lines.append("")
    return "\n".join(lines)


def main():
    stats, nc, axioms = run_lean_census()
    hmap, _prims, _proven, _op = AssumptionScan.scan()
    data, problems = PremiseRegistry.load_registry()
    if problems:
        for p in problems:
            print(f"GENTHEOREMINDEX: FAIL (registry: {p})")
        return 1
    text = generate(stats, nc, axioms, hmap, operational_by_file(), data)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(text, encoding="utf-8", newline="\n")
    print(f"GENTHEOREMINDEX: wrote {OUT.relative_to(ROOT).as_posix()} "
          f"({len(stats)} modules)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
