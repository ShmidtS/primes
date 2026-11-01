#!/usr/bin/env python3
"""DepAudit — Phase 0 (tact 313) static import-graph audit.

1. Builds the full `import Hagi.*` DAG over Hagi/ Lean modules.
2. Reports modules whose transitive import closure pulls in a Gen-1
   legacy module (GrowthState / GenState / CorePremises) while not
   pulling in any Gen-3 module (StageSemantics / CertifiedLoop) —
   the Gen-1-only consumer list for the retirement plan.
3. Prints per-legacy-module direct importers and a summary.

Read-only: noLean elaboration, purely textual `import` lines.
Output: human-readable report (stdout). Exit code 0 always.
"""
import os
import re
import sys
from collections import defaultdict

ROOT = os.path.join(os.path.dirname(__file__), "..", "Hagi")

IMPORT = re.compile(r"^\s*import\s+(Hagi\.[A-Za-z0-9_.]+)\s*$", re.M)

GEN1 = {
    "Hagi.System.GrowthState",
    "Hagi.Unified.CorePremises",
    "Hagi.Unified.CorePremisesDerived",
}
GEN3 = {
    "Hagi.Unified.CertifiedLoop",
    "Hagi.Unified.HonestTransition",
}


def module_name(path: str) -> str:
    rel = os.path.relpath(path, os.path.dirname(ROOT))
    return rel[:-5].replace(os.sep, ".")


def main() -> None:
    mods = {}
    for dirpath, _, files in os.walk(ROOT):
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(dirpath, f)
                mods[module_name(p)] = p

    deps: dict[str, set[str]] = {}
    for m, p in mods.items():
        with open(p, encoding="utf-8", errors="replace") as fh:
            deps[m] = {
                i for i in IMPORT.findall(fh.read()) if i in mods
            }

    # transitive closure (iterative)
    closure: dict[str, set[str]] = {}
    for m in mods:
        seen: set[str] = set()
        stack = list(deps[m])
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            stack.extend(deps.get(x, ()))
        closure[m] = seen

    print(f"modules: {len(mods)}")

    gen1_only = sorted(
        m
        for m in mods
        if (closure[m] & GEN1 or m in GEN1)
        and not (closure[m] & GEN3 or m in GEN3)
    )
    gen1_any = sorted(
        m for m in mods if closure[m] & GEN1 or m in GEN1
    )

    print(f"\n=== Gen-1 reach (direct or transitive): {len(gen1_any)} ===")
    for g in sorted(GEN1):
        direct = sorted(m for m in mods if g in deps[m])
        total = sorted(m for m in mods if g in closure[m])
        print(f"{g}: direct={len(direct)} transitive={len(total)}")

    print(f"\n=== Gen-1 WITHOUT Gen-3 (retirement targets): {len(gen1_only)} ===")
    for m in gen1_only:
        print(f"  {m}")

    # reverse-dependency counts for legacy modules
    print("\n=== reverse deps (who imports them, direct) ===")
    for g in sorted(GEN1):
        if g in mods:
            direct = sorted(m for m in mods if g in deps[m])
            print(f"{g}:")
            for d in direct:
                print(f"    {d}")


if __name__ == "__main__":
    main()
