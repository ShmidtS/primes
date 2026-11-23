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

from _shared import (BENCH_PREFIX, LEGACY_PREFIX, RESEARCH_PREFIX,
                     lean_files, read_baseline)

ROOT = Path(__file__).resolve().parent.parent / "Hagi"
BASELINE = os.path.join(os.path.dirname(__file__), "nslint_baseline.txt")
NS_RE = re.compile(r"^namespace\s+([\w.]+)", re.M)

# C217/C239/C240 quarantine: files under the shared quarantine prefixes
# (see scripts/_shared.py) keep their original namespaces (avoids
# declaration-name churn); exempt from the namespace-matches-folder rule.


def violations():
    out = []
    for p in lean_files(ROOT):
        rel = p.relative_to(ROOT.parent).as_posix()
        if rel.startswith(LEGACY_PREFIX) or rel == "Hagi/Legacy.lean":
            continue
        if rel.startswith(BENCH_PREFIX) or rel == "Hagi/Benchmarks.lean":
            continue
        if rel.startswith(RESEARCH_PREFIX) or rel == "Hagi/Research.lean":
            continue
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
    base = read_baseline(BASELINE)
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
