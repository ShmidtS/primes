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
    "Audit": 0,          # de-facto foundations (to be split)
    "Core": 1,           # component algebra (Spec-to-be)
    "Spectral": 1,
    "Sparsity": 1,
    "Depth": 1,
    "Architecture": 2,
    "Data": 2,
    "Energy": 2,
    "Probability": 2,
    "External": 2,
    "Ensemble": 3,
    "Step": 3,
    "Runtime": 3,
    "Model": 4,
    "Growth": 4,
    "Generalization": 4,
    "Budget": 4,
    "Dynamics": 5,
    "Deployment": 5,
    "Pretraining": 5,
    "Discovery": 5,
    "Autonomy": 5,
    "Unified": 6,
}

# known violations, to be removed one by one (audit list):
LAYER_EXCEPTIONS = {

    ("Core/RoPE.lean", "Unified/ArchitectureTheorem.lean"),
    ("Core/NonlinearStep0.lean", "Ensemble/MergePrice.lean"),
    ("Energy/QuantBridge.lean", "Unified/MacroCycle.lean"),
    ("Step/SafeQPRobust.lean", "Unified/Unified.lean"),
    ("Data/DField.lean", "Step/Compound.lean"),
}

IMPORT_RE = re.compile(r"^import\s+Hagi\.([A-Za-z0-9_.]+)\s*$", re.M)

def rel(p: Path) -> str:
    return p.relative_to(ROOT).as_posix()

def main() -> int:
    bad = []
    for f in sorted(ROOT.rglob("*.lean")):
        src = rel(f)
        folder = src.split("/")[0]
        my = LAYERS.get(folder)
        if my is None:
            continue
        m = IMPORT_RE.search(f.read_text(encoding="utf-8"))
        for m in IMPORT_RE.finditer(f.read_text(encoding="utf-8")):
            tgt = m.group(1) + ".lean"
            tfolder = tgt.split("/")[0]
            tl = LAYERS.get(tfolder)
            if tl is None:
                continue
            if tl >= my and (src, tgt) not in LAYER_EXCEPTIONS:
                bad.append(f"{src} -> {tgt} (import layer {tl} >= own {my})")
    if bad:
        print("LAYERLINT: FAIL")
        for b in bad:
            print("  " + b)
        return 1
    print("LAYERLINT: PASS")
    return 0

if __name__ == "__main__":
    sys.exit(main())
