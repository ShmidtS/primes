#!/usr/bin/env python3
"""NsLint: file namespace must match its folder .

Rule: every Hagi/<Folder>/**.lean must declare a namespace
`Hagi.<Folder>` (or a child of it). Known exceptions are tracked as a
SHRINKING baseline (like DupLint): verify fails only if the violation
count exceeds nslint_baseline.txt.

`--update` rewrites the baseline. Print NSLINT: PASS/FAIL.
"""
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "Hagi"
BASELINE = os.path.join(os.path.dirname(__file__), "nslint_baseline.txt")
NS_RE = re.compile(r"^namespace\s+([\w.]+)", re.M)


def violations():
    out = []
    for p in sorted(ROOT.rglob("*.lean")):
        rel = p.relative_to(ROOT.parent).as_posix()
        folder = rel.split("/")[1]
        ns_prefix = "Hagi." + folder
        nss = NS_RE.findall(p.read_text(encoding="utf-8", errors="replace"))
        if not any(n == ns_prefix or n.startswith(ns_prefix + ".")
                   for n in nss):
            out.append(f"{rel} -> {','.join(nss[:2]) or 'NONE'}")
    return out


def main() -> int:
    update = "--update" in sys.argv
    v = violations()
    if update or not os.path.exists(BASELINE):
        with open(BASELINE, "w", encoding="utf-8", newline="\n") as fh:
            fh.write("\n".join(v) + "\n")
        print(f"NSLINT: wrote baseline ({len(v)} violations)")
        return 0
    with open(BASELINE, encoding="utf-8") as fh:
        base = {line.strip() for line in fh if line.strip()}
    new_extra = sorted(set(v) - base)
    if new_extra:
        print(f"NSLINT : FAIL "
              f"({len(v)} violations, baseline {len(base)}, "
              f"+{len(new_extra)} new)")
        for x in new_extra:
            print("  " + x)
        return 1
    print(f"NSLINT: PASS ({len(v)} violations vs baseline {len(base)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
