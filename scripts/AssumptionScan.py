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
PRIM = re.compile(
    r"^\s*(?:noncomputable\s+)?def\s+((?:kl|tv|ent|entropy|softmax|lse)[A-Za-z0-9_']*)",
    re.M)


def scan():
    hmap = {}
    prims = []
    for f in sorted((ROOT / "Hagi").rglob("*.lean")):
        rel = f.relative_to(ROOT).as_posix()
        text = f.read_text(encoding="utf-8", errors="replace")
        names = sorted(set(IDENT.findall(text)))
        if names:
            hmap[rel] = names
        for m in PRIM.finditer(text):
            prims.append(f"{rel}:{m.group(1)}")
    return hmap, prims


def registry(hmap, prims):
    lines = [f"h_emp files: {len(hmap)}",
             f"h_emp identifiers: {sum(len(v) for v in hmap.values())}",
             f"primitive defs: {len(prims)}", "", "[h_emp]"]
    for rel in sorted(hmap):
        lines.append(f"{rel}: {' '.join(hmap[rel])}")
    lines += ["", "[primitives]"]
    lines += sorted(prims)
    return "\n".join(lines) + "\n"


def main():
    hmap, prims = scan()
    reg = registry(hmap, prims)
    update = "--update" in sys.argv
    if update or not LOCK.exists():
        LOCK.write_text(reg, encoding="utf-8", newline="\n")
        print(f"ASSUMPTIONSCAN: wrote {LOCK.name} "
              f"({len(hmap)} h_emp files, {len(prims)} primitive defs)")
        return 0
    if LOCK.read_text(encoding="utf-8") != reg:
        print("ASSUMPTIONSCAN: FAIL (registry drifted; "
              "run `python scripts/AssumptionScan.py --update` "
              "and review the diff)")
        return 1
    print(f"ASSUMPTIONSCAN: PASS ({len(hmap)} h_emp files, "
          f"{sum(len(v) for v in hmap.values())} premises, "
          f"{len(prims)} primitive defs)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
