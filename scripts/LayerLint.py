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
    "Foundations": 0,
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
    # сокращающийся baseline межпапочных рёбер (аудит 2026-10-05,
    # 52 фактических; каждое разворачивается переносом лемм вниз)
    ("Architecture/FactorRank.lean", "Unified/GrowthState.lean"),
    ("Audit/EqualBudget.lean", "Budget/JointCost.lean"),
    ("Audit/Exactness.lean", "Step/SafeQP.lean"),
    ("Audit/Foundations.lean", "External/Transfer.lean"),
    ("Audit/Foundations.lean", "Step/SafeQP.lean"),
    ("Autonomy/Insight.lean", "Unified/GlobalDynamics.lean"),
    ("Autonomy/Insight.lean", "Unified/TopLevel.lean"),
    ("Budget/JointCost.lean", "Growth/SeedOnly.lean"),
    ("Core/NonlinearStep0.lean", "Ensemble/MergePrice.lean"),
    ("Core/RoPE.lean", "Unified/ArchitectureTheorem.lean"),
    ("Data/ChunkedCE.lean", "Ensemble/QFormerBridge.lean"),
    ("Data/DBridge.lean", "Dynamics/Contraction.lean"),
    ("Data/DBridge.lean", "Ensemble/GenCycle.lean"),
    ("Data/DField.lean", "Step/Compound.lean"),
    ("Data/PuncturedCE.lean", "Step/CausalFilter.lean"),
    ("Data/TernaryChinchilla.lean", "Step/Muon.lean"),
    ("Depth/RootContrast.lean", "External/Layers.lean"),
    ("Discovery/PPT.lean", "Unified/GrowthState.lean"),
    ("Dynamics/CapabilityGain.lean", "Unified/TopLevel.lean"),
    ("Energy/FreeEnergy.lean", "Data/DBridge.lean"),
    ("Energy/FreeEnergy.lean", "Data/Distill.lean"),
    ("Energy/PoEBound.lean", "Ensemble/Hoeffding.lean"),
    ("Energy/QuantBridge.lean", "Unified/MacroCycle.lean"),
    ("Ensemble/GenCycle.lean", "Step/Joint.lean"),
    ("Ensemble/MergeCancellation.lean", "Step/SafeQP.lean"),
    ("Ensemble/MergePrice.lean", "Step/GPM.lean"),
    ("Ensemble/MergeScaling.lean", "Step/Decompose.lean"),
    ("External/Diversity.lean", "Budget/DesignOpt.lean"),
    ("External/Diversity.lean", "Step/Dominate.lean"),
    ("External/Transport.lean", "Data/SinkCost.lean"),
    ("Generalization/ModeState.lean", "Growth/FrontierScaling.lean"),
    ("Generalization/ModeState.lean", "Unified/GrowthState.lean"),
    ("Growth/GainRenewal.lean", "Unified/GrowthBridge.lean"),
    ("Growth/GainRenewal.lean", "Unified/Liveness.lean"),
    ("Growth/GrowthGate.lean", "Budget/ComputeBudget.lean"),
    ("Growth/StateBinding.lean", "Unified/GrowthState.lean"),
    ("Pretraining/SyntheticPretrain.lean", "Unified/GrowthState.lean"),
    ("Probability/Azuma.lean", "Ensemble/Hoeffding.lean"),
    ("Probability/CertifiedEstimator.lean", "Energy/PoEBound.lean"),
    ("Probability/ConditionalSuccess.lean", "Dynamics/FastGrowth.lean"),
    ("Probability/ConditionalSuccess.lean", "Step/StochasticSafeQP.lean"),
    ("Sparsity/SparseStep0.lean", "Unified/RecursiveGrowth.lean"),
    ("Spectral/SpectralProjector.lean", "Step/SafeQP.lean"),
    ("Step/Compound.lean", "Ensemble/GenCycle.lean"),
    ("Step/JointPreserve.lean", "Budget/ElementQuant.lean"),
    ("Step/LazyAdamMomentum.lean", "Dynamics/Contraction.lean"),
    ("Step/SafeQPRobust.lean", "Unified/Unified.lean"),
    ("Step/SafeQPStep.lean", "Dynamics/CurvatureSafe.lean"),
    ("Step/Upgrades.lean", "Budget/DesignOpt.lean"),
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
            segs = m.group(1).split(".")
            tgt = "/".join(segs) + ".lean"
            tfolder = segs[0]
            myfolder = src.split("/")[0]
            tl = LAYERS.get(tfolder)
            if tl is None:
                continue
            # правило: импорт только из СТРОГО НИЖНИХ слоёв;
            # внутри своей папки (same folder) допустим DAG
            violates = tl > my or (tl == my and tfolder != myfolder)
            if violates and (src, tgt) not in LAYER_EXCEPTIONS:
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
