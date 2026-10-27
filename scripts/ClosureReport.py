#!/usr/bin/env python3
"""ClosureReport (аудит v2 P0 / v3 Phase 4): какие модули лежат
в транзитивном замыкании импортов капстоунов (используются
итоговыми теоремами), а какие — библиотечные (вне замыкания).
Отчёт, не гейт: библиотечные модули легальны, но должны быть
осознанным выбором. Baseline-файл фиксирует текущее состояние.
"""
import os, re, sys, subprocess

ROOT = os.path.join(os.path.dirname(__file__), "..", "Hagi")
CAPSTONES = [
    "Hagi.Unified.MasterHAGI", "Hagi.Unified.GrandSynthesis",
    "Hagi.Model.StageSemantics",
    # semantic closure extensions (audit v3 Phase 4):
    "Hagi.Unified.DerivAlong",        # operational bridges (joint/compress)
    "Hagi.Model.ConsolidationMirror",  # grow bridge + KL distillation
    "Hagi.Examples.Nonvacuity",        # merge bridge + obstruction theorems
    "Hagi.Probability.CertifiedEstimator",  # epistemic chain (Freedman/union)
    # refactor-plan facades (P1.4-P2.11):
    "Hagi.Unified.Master",         # master theorem hierarchy
    "Hagi.Unified.SafeStep",       # safe step contract
    "Hagi.Unified.GrowthTheory",   # dynamics/saturation theory
    "Hagi.Unified.Concentration",  # concentration layer
    "Hagi.System.GrowthStateViews" # P2.9 entity decomposition
    "Hagi.Unified.Budget",         # budget economy facade
    "Hagi.Unified.ArchitectureCore",  # architecture facade
    "Hagi.Unified.CoreAlgebra",      # core component algebra facade
    "Hagi.Unified.EnsembleTheory",   # ensemble theory facade
    "Hagi.Unified.DataCentric",    # data-centric facade
    "Hagi.Unified.Robustness",     # robustness corridor facade
]

IMP = re.compile(r"^import\s+(Hagi\.[A-Za-z0-9_.]+)\s*$", re.M)

def modules():
    mods = {}
    for dp, _, fs in os.walk(ROOT):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                mod = "Hagi." + os.path.relpath(p, ROOT)[:-5].replace(os.sep, ".")
                mods[mod] = IMP.findall(open(p, encoding="utf-8", errors="replace").read())
    return mods

def closure(mods, roots):
    seen = set()
    st = [r for r in roots if r in mods]
    while st:
        m = st.pop()
        if m in seen:
            continue
        seen.add(m)
        st.extend(i for i in mods.get(m, []) if i in mods and i not in seen)
    return seen

def main():
    mods = modules()
    cl = closure(mods, CAPSTONES)
    lib = sorted(set(mods) - cl)
    print(f"CLOSURE: {len(cl)}/{len(mods)} modules under capstones "
          f"({100*len(cl)/len(mods):.0f}%); library: {len(lib)}")
    for m in lib:
        print(f"  lib: {m}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
