#!/usr/bin/env python3
"""ReachLint: cross-module theorem reachability metric (audit v2 item 4).

Informational metric (does not fail CI):
- builds the declaration-reference graph by name (heuristic: exact-name
  occurrences outside the defining module);
- reports: islands (modules none of whose theorems are referenced from
  another module), and the share of theorems referenced cross-module.

Known limitations (same as the external audit's heuristic): implicit uses
(@[simp] lemmas, instances) are undercounted; treat numbers as a lower
bound on integration, not a verdict.
"""
import re, sys, pathlib, json

ROOT = pathlib.Path(__file__).resolve().parent.parent / "Hagi"

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:theorem|lemma|def|structure|class)\s+([A-Za-z_][A-Za-z0-9_\'!?]*)', re.M)

def main():
    modules = {}   # module -> set of declared names
    name_to_mod = {}
    for f in ROOT.rglob("*.lean"):
        mod = "Hagi." + str(f.relative_to(ROOT)).replace("\\", "/")[:-5].replace("/", ".")
        text = f.read_text(encoding="utf-8", errors="replace")
        names = set(DECL.findall(text))
        modules[mod] = names
        for nm in names:
            name_to_mod.setdefault(nm, mod)
    # reference pass
    cross_used = set()
    for f in ROOT.rglob("*.lean"):
        mod = "Hagi." + str(f.relative_to(ROOT)).replace("\\", "/")[:-5].replace("/", ".")
        text = f.read_text(encoding="utf-8", errors="replace")
        # remove declaration lines themselves
        body = DECL.sub(lambda m: m.group(0).replace(m.group(1), "_" * len(m.group(1))), text)
        for nm, owner in name_to_mod.items():
            if owner != mod and re.search(r'(?<![A-Za-z0-9_\'!?])' + re.escape(nm) + r'(?![A-Za-z0-9_\'!?])', body):
                cross_used.add(nm)
    total_theorems = 0
    used_theorems = 0
    islands = []
    for mod, names in modules.items():
        mod_used = any(nm in cross_used for nm in names)
        if not mod_used and names:
            islands.append(mod)
    for nm in name_to_mod:
        if nm in cross_used:
            used_theorems += 1
    n = len(name_to_mod)
    print(f"REACHLINT: modules={len(modules)} decls={n} cross-used={used_theorems} "
          f"({100*used_theorems/max(1,n):.1f}%) islands={len(islands)} "
          f"({100*len(islands)/max(1,len(modules)):.1f}%)")
    if "--islands" in sys.argv:
        for m in sorted(islands):
            print("  island:", m)

if __name__ == "__main__":
    main()
