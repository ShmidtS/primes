#!/usr/bin/env python3
"""LayerLint: import graph must respect layer order.

Layer map (pre-migration, by current folder). A module may
import only from STRICTLY LOWER layers. Violations must be
listed in LAYER_EXCEPTIONS (a shrinking allowlist).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "Hagi"
# layer assignment of Hagi/<Folder> (higher = later = may
# import lower). Unification target per audit 2026-10-05.
LAYERS = {
    # A7 target 5-layer DAG (C244). Dirs do NOT exist yet — entries are
    # inert until Phase 1-3 create them; they activate automatically then.
    "HagiMath": 0,
    "HagiCert": 1,
    "HagiModel": 2,
    "HagiLoop": 3,
    "HagiRecipes": 4,
    "Prelude": -1,
    "Cert": 2,        # C224: canonical certification kernel (master plan v3 S1+S2)
    "Information": 1,   # R200: information-theoretic capacity layer      # R198: the information-theory prelude below everything
    "Foundations": 0,
    "Audit": 0,          # de-facto foundations (to be split)
    "Core": 1,           # component algebra (Spec-to-be)
    "Spectral": 1,
    "Sparsity": 1,
    "Depth": 1,
    "Geometry": 1,
    "Planning": 1,
    "Percolation": 1,
    "Architecture": 2,
    "Data": 2,
    "Energy": 2,
    "Probability": 2,
    "External": 2,
    "Ensemble": 3,
    "Step": 3,
    "Optimization": 3,
    "Runtime": 3,
    "System": 3,   # R331: state layer (GrowthState) per audit v3 3
    "State": 3,     # audit TD-05: canonical TrainState layer (was silently skipped)
    "Contracts": 7,  # audit TD-05: certificate contracts above Unified/State
    "Challenge": 7,  # audit TD-05: capstone consumers above Unified
    "Model": 4,
    "Numerics": 4,
    "Growth": 4,
    "Generalization": 4,
    "Budget": 4,
    "Dynamics": 5,
    "Deployment": 5,
    "Pretraining": 5,
    "Discovery": 5,
    "Autonomy": 5,
    "Omni": 5,
    "Unified": 6,
    "Examples": 7,
}

# known violations, to be removed one by one (audit list):
LAYER_EXCEPTIONS = {
    # сокращающийся baseline межпапочных рёбер
    # аудит 2026-10-24: External/MemT/GDN2 -> Optimization.InexactContraction
    # (внешний остров MemT; кандидат на вынос из дерева после миграции)
    ("External/MemT/GDN2.lean", "Optimization/InexactContraction.lean"),
    # (R169: 49; R170: 46; R171: 26; R172: 24; R173: 23)
    
    
    
    
    
}

IMPORT_RE = re.compile(r"^import\s+Hagi\.([A-Za-z0-9_.]+)\s*$", re.M)

def rel(p: Path) -> str:
    return p.relative_to(ROOT).as_posix()

def check_source(src: str, text: str) -> list:
    """Layer violations for one Hagi file (path relative to Hagi/)."""
    folder = src.split("/")[0]
    my = LAYERS.get(folder)
    if my is None:
        return []
    violations = []
    for m in IMPORT_RE.finditer(text):
        segs = m.group(1).split(".")
        tgt = "/".join(segs) + ".lean"
        tfolder = segs[0]
        tl = LAYERS.get(tfolder)
        if tl is None:
            continue
        # правило: импорт только из СТРОГО НИЖНИХ слоёв;
        # внутри своей папки (same folder) допустим DAG
        violates = tl > my or (tl == my and tfolder != folder)
        if violates and (src, tgt) not in LAYER_EXCEPTIONS:
            violations.append(f"{src} -> {tgt} (import layer {tl} >= own {my})")
    return violations

def main() -> int:
    bad = []
    for f in sorted(ROOT.rglob("*.lean")):
        src = rel(f)
        bad += check_source(src, f.read_text(encoding="utf-8"))
    if bad:
        print("LAYERLINT: FAIL")
        for b in bad:
            print("  " + b)
        return 1
    print("LAYERLINT: PASS")
    return 0

if __name__ == "__main__":
    sys.exit(main())
