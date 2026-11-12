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
from Freeze import strip_comments
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOCK = Path(__file__).resolve().parent / "assumptions.lock"

IDENT = re.compile(r"\bh_emp_[A-Za-z0-9_]+")
# Audit #7 premise classes: Empirical = h_emp_* binders;
# Operational = execution-link binders (exec/descent/sample);
# Structural/Math = all other parameter hypotheses.
# Match a whole h-prefixed identifier, never an embedded fragment of an
# ordinary identifier's name.  In particular,
# `ceQuantWitness_shortcutScales_strict_descent` is not a premise
# named `hortcutScales_strict_descent`.  Both guards exclude partial matches;
# suffixes and primed identifiers are preserved instead of truncated.
# C218 (audit P0b): unprefixed empirical premise registry.
# PER-FILE, SHRINK-ONLY: each entry names binder names that are
# acknowledged empirical premises in that specific file (MasterHAGI
# docstring 84-92; ModeState). NOT a name-registry: names like hbeta
# have ~60 structural binder sites elsewhere in the repo, so
# cross-file matching would misregister structural hypotheses as
# empirical (documented blindness). The list may only shrink in
# future cycles; growth or drift in registered files FAILs.
UNPREFIXED_EMPIRICAL = {
    'Hagi/Unified/MasterHAGI.lean':
        {'h_step': 3, 'h_gain_prod': 3, 'h_dyn': 2, 'h_C_cap': 2,
         'hβ': 2},
    'Hagi/Generalization/ModeState.lean':
        {'h_C_cap': 2, 'hβ_eased': 2},
}

OPERATIONAL = re.compile(
    r"(?<![A-Za-z0-9_'])h[A-Za-z0-9_']*"
    r"(?:Exec|exec|Descent|descent|Sample|sample)[A-Za-z0-9_']*"
    r"(?![A-Za-z0-9_'])")

DECL = re.compile(
    r'^(?:\s|(?:private|protected|noncomputable)\s+)*'
    r'(theorem|lemma|def|structure|class|abbrev|instance|inductive)\s+'
    r"([A-Za-z_][A-Za-z0-9_']*)", re.M)
PRIM = re.compile(
    r"^\s*(?:noncomputable\s+)?def\s+((?:kl|tv|ent|entropy|softmax|lse)[A-Za-z0-9_']*)",
    re.M)


def unprefixed_check():
    """Per-file binder-count verification for UNPREFIXED_EMPIRICAL.

    A binder site is `(NAME :` in comment-stripped source. The
    registered count is the acknowledged baseline; the registry
    may only shrink (count decrease = deliberate shrink, FAILs
    until the registry is updated through plan review; count
    increase = growth, FAILs outright).
    """
    problems = []
    for rel, counts in UNPREFIXED_EMPIRICAL.items():
        f = ROOT / rel
        if not f.exists():
            problems.append(f"unprefixed registry: file missing: {rel}")
            continue
        code = strip_comments(f.read_text(encoding="utf-8",
                                          errors="replace"))
        for n, want in counts.items():
            pat = re.compile(r"[(]\s*" + re.escape(n) + r"\s*:")
            got = len(pat.findall(code))
            if got != want:
                direction = ("shrink (update registry deliberately)"
                             if got < want else "GROWTH (forbidden)")
                problems.append(
                    f"unprefixed registry: binder {n} in {rel}: "
                    f"{got} sites vs {want} registered — {direction}")
    return problems


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
        code = strip_comments(text)
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
            operational.add(om.group(0))
        for m in PRIM.finditer(code):
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
    lines += ["", "[operational]"]
    lines += sorted(operational)
    lines += ["", "[unprefixed empirical premises "
              "(per-file counts, shrink-only, not a name-registry)]"]
    for rel in sorted(UNPREFIXED_EMPIRICAL):
        lines.append(rel + ": " + " ".join(
            f"{n}={c}" for n, c in UNPREFIXED_EMPIRICAL[rel].items()))
    return "\n".join(lines) + "\n"


def main():
    problems = unprefixed_check()
    if problems:
        for p in problems:
            print(f"ASSUMPTIONSCAN: FAIL ({p})")
        return 1
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
