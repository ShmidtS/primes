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

ROOT = Path(__file__).resolve().parent.parent
HAGI_ROOT = ROOT / "Hagi.lean"

# C217 quarantine: modules under Hagi/Legacy/ are intentionally
# outside the root import closure (vacuous-stack quarantine, audit
# P0a). They must still build (separate lean_lib, default target).
LEGACY_PREFIX = "Hagi/Legacy/"

IMPORT = re.compile(r"^\s*import\s+(Hagi\.[A-Za-z0-9_.]+)", re.M)


def module_of(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def imports_of(path: Path):
    text = path.read_text(encoding="utf-8", errors="replace")
    return set(IMPORT.findall(text))


def main() -> int:
    all_modules = {module_of(p) for p in (ROOT / "Hagi").rglob("*.lean")}
    legacy = {module_of(p) for p in (ROOT / "Hagi" / "Legacy").rglob("*.lean")}
    legacy.add("Hagi.Legacy")  # umbrella module of the quarantine lib
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
    unreachable = sorted((all_modules - seen) - legacy)
    if unreachable:
        print(f"REACHLINT: FAIL — {len(unreachable)} module(s) not "
              f"reachable from Hagi.lean (wire the import or delete):")
        for m in unreachable:
            print(f"  {m}")
        return 1
    print(f"REACHLINT: PASS — all {len(all_modules)} Hagi modules "
          f"reachable ({len(legacy)} legacy-exempt, quarantine C217)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
