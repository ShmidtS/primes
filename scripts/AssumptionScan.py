#!/usr/bin/env python3
"""AssumptionScan (audit stage 1): assumption & duplication registry.

Scans the Hagi sources and writes a reproducible registry:
  * every `h_emp_*` identifier (the external empirical premises
    each theorem consumes), grouped by file;
  * every definition of an information primitive
    (kl / tv / entropy / softmax / lse) — the canonical layer
    must stay the only non-bridge definition.
Fails if the registry drifts from scripts/assumptions.lock;
update deliberately with `--update` (same workflow as Freeze).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOCK = Path(__file__).resolve().parent / "assumptions.lock"

IDENT = re.compile(r"\bh_emp_[A-Za-z0-9_]+")
# Audit #7 premise classes: Empirical = h_emp_* binders;
# Operational = execution-link binders (exec/descent/sample);
# Structural/Math = all other parameter hypotheses.
OPERATIONAL = re.compile(r"(h[A-Za-z0-9_']*(?:Exec|exec|Descent|descent|Sample|sample))")

DECL = re.compile(
    r'^(?:\s|(?:private|protected|noncomputable)\s+)*'
    r'(theorem|lemma|def|structure|abbrev|instance|inductive)\s+'
    r"([A-Za-z_][A-Za-z0-9_']*)", re.M)
PRIM = re.compile(
    r"^\s*(?:noncomputable\s+)?def\s+((?:kl|tv|ent|entropy|softmax|lse)[A-Za-z0-9_']*)",
    re.M)


def scan():
    hmap = {}
    prims = []
    proven = set()
    operational = set()
    for f in sorted((ROOT / "Hagi").rglob("*.lean")):
        rel = f.relative_to(ROOT).as_posix()
        text = f.read_text(encoding="utf-8", errors="replace")
        # Spec 1.4: comments/docstrings are NOT a source of truth, so
        # they must not register premises either. A docstring saying
        # "analytic derivation of h_emp_dist" is documentation OF the
        # elimination, not a premise. Strip comments before scanning.
        code = re.sub(r"/-.*?-/s", "", text, flags=re.S)
        code = re.sub(r'--[^\n]*', '', code)
        names = sorted(set(IDENT.findall(code)))
        # R265+: distinguish PROVEN h_emp-named theorems/defs
        # (derived results with a historical empirical name, e.g.
        # PerronCone.h_emp_takeoff_exponential) from genuine premise
        # BINDERS. A proven theorem is not a premise.
        for dm in DECL.finditer(code):
            if dm.group(2).startswith('h_emp_'):
                proven.add(dm.group(2))
        if names:
            hmap[rel] = names
        # operational premise registry (execution-link binders)
        for om in OPERATIONAL.finditer(code):
            operational.add(om.group(1))
        for m in PRIM.finditer(text):
            prims.append(f"{rel}:{m.group(1)}")
    return hmap, prims, proven, operational


def registry(hmap, prims, proven, operational):
    total = sum(len(v) for v in hmap.values())
    lines = [f"h_emp files: {len(hmap)}",
             f"h_emp identifiers: {total}",
             f"h_emp proven theorems: {len(proven)}",
             f"primitive defs: {len(prims)}",
             f"operational premise names: {len(operational)}",
             "", "[premise classes]",
             "Empirical: h_emp_* binders (statistical, external)",
             f"Operational: {len(operational)} execution-link binders",
             "Structural/Math: all other parameter hypotheses",
             "", "[h_emp]"]
    for rel in sorted(hmap):
        lines.append(f"{rel}: {' '.join(hmap[rel])}")
    lines += ["", "[derived h_emp-named theorems (PROVEN, not premises)]"]
    for n in sorted(proven):
        lines.append(n)
    lines += ["", "[primitives]"]
    lines += sorted(prims)
    return "\n".join(lines) + "\n"


def main():
    hmap, prims, proven, operational = scan()
    reg = registry(hmap, prims, proven, operational)
    update = "--update" in sys.argv
    if update or not LOCK.exists():
        LOCK.write_text(reg, encoding="utf-8", newline="\n")
        print(f"ASSUMPTIONSCAN: wrote {LOCK.name} "
              f"({len(hmap)} h_emp files, {len(prims)} primitive defs, "
              f"{len(operational)} operational names)")
        return 0
    if LOCK.read_text(encoding="utf-8") != reg:
        print("ASSUMPTIONSCAN: FAIL (registry drifted; "
              "run `python scripts/AssumptionScan.py --update` "
              "and review the diff)")
        return 1
    print(f"ASSUMPTIONSCAN: PASS ({len(hmap)} h_emp files, "
          f"{sum(len(v) for v in hmap.values())} occurrences "
          f"({len(proven)} proven theorems + "
          f"{sum(len(v) for v in hmap.values()) - len(proven)} premise binders), "
          f"{len(prims)} primitive defs, "
          f"{len(operational)} operational names)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
