#!/usr/bin/env python3
"""LeafClassify — Phase 0 (tact 314) classification of isolated library
leaves (modules outside the capstone closure) into the four functional
classes of the Gen-3 refactoring plan:

  A (Objective/Descent)    — models with a loss and a gradient
  B (Step Compressors)     — optimizers and quantizers
  C (Efficiency/Budget)    — architecture blocks with proven FLOPs/memory saving
  D (Alignment/Quality)    — quality metrics, regularizers, alignment methods
  E (Math foundation)      — pure-math leaves consumed by the above
                             (kept for Phase 4 package extraction)

Classification is keyword+content based; output is a reviewable matrix.
Read-only. Exit code 0.
"""
import os
import re
import subprocess
import sys
from collections import defaultdict

SCRIPTS = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(SCRIPTS, "..", "Hagi")

# explicit plan-mandated assignments (module name -> class)
PLAN = {
    # Class A — Objective/Descent
    "Hagi.Optimization.SAM": "A", "Hagi.Model.VicReg": "A", "Hagi.Model.BYOL": "A",
    "Hagi.Model.TripletLoss": "A", "Hagi.Model.NTXent": "A",
    "Hagi.Model.Mixup": "A",
    # Class B — Step Compressors
    "Hagi.Optimization.Lion": "B", "Hagi.Optimization.AdaGrad": "B",
    "Hagi.Optimization.AdamW": "B",
    "Hagi.Step.Muon": "B", "Hagi.Step.MuonAlign": "B", "Hagi.Step.MuonTwoLevel": "B",
    "Hagi.Step.MuonWD": "B",
    "Hagi.Step.SignSGD": "B", "Hagi.Optimization.CautiousOptimizer": "B",
    # Class C — Efficiency/Budget
    "Hagi.Model.GQA": "C", "Hagi.Model.FlashAttention": "C",
    "Hagi.Model.SWA": "C", "Hagi.Model.MoD": "C", "Hagi.Model.Perceiver": "C",
    "Hagi.Model.MLA": "C", "Hagi.Model.StreamingLLM": "C",
    "Hagi.Model.HNet": "C", "Hagi.Model.BytePatch": "C",
    # Class D — Alignment/Quality
    "Hagi.Model.DPO": "D", "Hagi.Optimization.PPOClip": "D", "Hagi.Model.GRPO": "D",
    "Hagi.Model.GAE": "D", "Hagi.Model.RLHF": "D",
    "Hagi.Model.LabelSmoothing": "D",
}

KEYWORDS = [
    ("A", re.compile(r"\b(gradient|descent|loss|objective|contrast|cosine|triplet|byol|vicreg|mixup|ntxent|sam\b|sharpness)", re.I)),
    ("B", re.compile(r"\b(optimizer|optimis|adam|lion|adagrad|signsgd|sign sgd|cautious|muon|momentum|quant|ternary|round|lattice|compress step|step size|learning rate)", re.I)),
    ("C", re.compile(r"\b(flops|memory|kv|cache|attention|gqa|mla|swa|sliding|mod\b|mixture of depth|perceiver|streaming|patch|sparse|rank|low.?rank|saving|budget|cost|token|latency|throughput|economy)", re.I)),
    ("D", re.compile(r"\b(align|reward|preference|dpo|ppo|grpo|gae|rlhf|policy|kl.?penalt|entropy reg|label smooth|quality|metric|calibrat|evaluat)", re.I)),
]


def classify(name: str, text: str) -> str:
    if name in PLAN:
        return PLAN[name]
    scores = defaultdict(int)
    for cls, rx in KEYWORDS:
        scores[cls] = len(rx.findall(text))
    if max(scores.values(), default=0) == 0:
        return "E"
    # C beats A/B on ties because "budget/cost" language is plan class C
    order = {"C": 1.05, "D": 1.0, "B": 1.0, "A": 1.0}
    return max(scores, key=lambda c: scores[c] * order[c])


def main() -> None:
    out = subprocess.run(
        [sys.executable, os.path.join(SCRIPTS, "ClosureReport.py")],
        capture_output=True, text=True, check=True,
    ).stdout
    leaves = [
        ln.split("lib:")[1].strip()
        for ln in out.splitlines()
        if ln.startswith("  lib:")
    ]
    matrix = defaultdict(list)
    unmatched_plan = []
    for name in leaves:
        parts = name.split(".")[1:]  # first component IS the Hagi/ dir
        path = os.path.join(ROOT, *parts) + ".lean"
        text = open(path, encoding="utf-8", errors="replace").read() if os.path.exists(path) else ""
        matrix[classify(name, text)].append(name)
        if not text:
            print(f"MISSING FILE for leaf {name}")

    print(f"closure leaves: {len(leaves)}")
    for cls in sorted(matrix):
        print(f"\n=== Class {cls}: {len(matrix[cls])} modules ===")
        for m in sorted(matrix[cls]):
            print(f"  {m}")
    if unmatched_plan:
        print(f"\nWARNING: plan-mandated modules not found as leaves: {unmatched_plan}")


if __name__ == "__main__":
    main()
