#!/usr/bin/env python3
"""ReachLint: every Hagi source module must be reachable from
the root import Hagi.lean (default lake build target).

Audit #8 finding: modules can exist with fresh oleans (built
ad hoc) while being INVISIBLE to lake build, TrivialLint,
AllAxiomCheck and inventory. This gate fails CI if any module
under Hagi/ is not in the transitive import closure of the
root, so new files MUST be wired into Hagi.lean (or removed).
"""
import re
import sys
from pathlib import Path

from _shared import BENCH_PREFIX, HAGI_MODULE, LEGACY_PREFIX, lean_files, RESEARCH_PREFIX

ROOT = Path(__file__).resolve().parent.parent
HAGI_ROOT = ROOT / "Hagi.lean"

# C217/C239/C240 quarantine: modules under the shared quarantine prefixes
# (see scripts/_shared.py) are intentionally outside the root import
# closure (vacuous-stack and toy-witness quarantines). They must still
# build (separate lean_lib, default target).
# C456: Legacy archived under Hagi/Research/Legacy/ (covered by
# RESEARCH_PREFIX); legacy prefix kept for history, dir scan is a no-op.

# C347 quarantine (A14 QW7): speculative growth modules stay in repo at
# their frozen FQNs (no dir move of DECLARATIONS), outside the root import
# closure. A19.1 (C448): Ceilings, ChainUnification,
# RecursiveSelfDevelopment, RoundViability, RsiCriterion, SeedOnly moved
# to Hagi/Research/ (Research-prefix quarantine; FQNs and namespaces
# preserved, now compiled by the Hagi.Research target).
QUARANTINED = {
    "Hagi.Growth.Takeoff",
    "Hagi.Growth.LinearCone",
    "Hagi.Growth.Saturation",
    "Hagi.Growth.GainDecomposition",
    "Hagi.Growth.StateBinding",
    "Hagi.Dynamics.GrowthBridge",
}

IMPORT = re.compile(rf"^\s*import\s+({HAGI_MODULE})", re.M)


def module_of(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def imports_of(path: Path):
    text = path.read_text(encoding="utf-8", errors="replace")
    return set(IMPORT.findall(text))


def main() -> int:
    all_modules = {module_of(p) for p in lean_files(ROOT / "Hagi")}
    legacy = {module_of(p) for p in lean_files(ROOT / "Hagi" / "Legacy")}
    legacy |= {module_of(p) for p in lean_files(ROOT / "Hagi" / "Benchmarks")}
    legacy.add("Hagi.Benchmarks")  # umbrella module of the quarantine lib
    legacy |= {module_of(p) for p in lean_files(ROOT / "Hagi" / "Research")}
    legacy.add("Hagi.Research")  # umbrella module of the quarantine lib
    # BFS from the root
    seen = set()
    frontier = imports_of(HAGI_ROOT)
    while frontier:
        nxt = set()
        for m in frontier:
            if m in seen:
                continue
            seen.add(m)
            f = ROOT / (m.replace(".", "/") + ".lean")
            if f.exists():
                nxt |= imports_of(f)
        frontier = nxt - seen
    unreachable = sorted((all_modules - seen) - legacy - QUARANTINED)
    if unreachable:
        print(f"REACHLINT: FAIL — {len(unreachable)} module(s) not "
              f"reachable from Hagi.lean (wire the import or delete):")
        for m in unreachable:
            print(f"  {m}")
        return 1
    print(f"REACHLINT: PASS — all {len(all_modules)} Hagi modules "
          f"reachable ({len(legacy)} legacy/benchmark/research-exempt, "
          f"quarantine C217/C239/C240; "
          f"{len(QUARANTINED)} growth-quarantine-exempt, C347)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
