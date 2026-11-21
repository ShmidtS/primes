/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Runtime.CertChecker
import Hagi.Theory.Continual
import Mathlib.Tactic

/-!
# Mini-HAGI bench bridge

Roadmap C492: the consumption bit tying the five certified bench
components into ONE run on the real corpus
(`scripts/bench_bridge.py`, `--mode mini-hagi`): trunk training
(C481 admission form), fiber grow (C444 margin), continual GPM
(C485/C488 span projection), ternary quantization (C443 gate)
and the Ville holdout stop (C446).

## The canonical objective rule

Heterogeneous phases are chained on ONE metric — the canonical
objective `miniHagiCanonical a b = (a + b) / 2`, the mean MSE of
all live tasks. Every trajectory step records obj = the
canonical objective of the CURRENT model state, is admitted only
by a measured canonical drop > 0, and the executable checker
`Hagi.Runtime.CertChecker.checkTrajectory` re-verifies the whole
chain.

## The bridges

`mini_hagi_canonical_drop`: per-task nonincrease with at least
one strict decrease forces a strict canonical drop — why each
phase's admission (measured on its own task surface) is valid on
the canonical chain whenever the other task losses do not grow.

`mini_hagi_gpm_canonical_descent`: the phase-C bridge —
`Hagi.Theory.ContinualBench.gpm_bench_bridge` (C485) makes the task-A loss EXACTLY
invariant under a GPM step, so a measured task-B decrease is a
canonical decrease: continual training descends the canonical
objective with zero forgetting, certified.

## Honest pins

1. The model is a linear head over the FIXED byte-feature trunk
   (C484 family): GPM zero-forgetting and the C444 grow mechanics
   are linear-readout statements; a nonlinear trunk (C481 mode)
   stays its own certified bench.
2. η = 1/10 fixed with snap-to-grid candidates; the admission is
   the C481 guarded measured drop (provable minimum).
3. The corpus is LIVE and prunes across sessions (185 → ~31
   usable); the bench asserts N > 0 and reports the run-time N.
4. A rejected grow/quant and a never-firing stop are honest
   OUTCOMES (telemetry), not failures.
-/

namespace Hagi.Theory.MiniHagi

/-- The canonical objective: mean MSE over the live tasks. -/
noncomputable def miniHagiCanonical (a b : ℝ) : ℝ := (a + b) / 2

/-- **mini_hagi_canonical_drop (C492)**: if neither task loss
grows and at least one strictly decreases, the canonical
objective strictly decreases — the admission contract every
mini-HAGI phase satisfies on the shared chain. -/
theorem mini_hagi_canonical_drop {a a' b b' : ℝ}
    (ha : a' ≤ a) (hb : b' ≤ b)
    (h : a' < a ∨ b' < b) :
    miniHagiCanonical a' b' < miniHagiCanonical a b := by
  unfold miniHagiCanonical
  rcases h with h | h <;> linarith

/-- **mini_hagi_gpm_canonical_descent (C492)**: the phase-C
bridge. A GPM step (each row of `ΔW` orthogonal to every task-A
input) leaves the task-A bench loss EXACTLY invariant
(`Hagi.Theory.ContinualBench.gpm_bench_bridge`, C485); a measured task-B loss decrease then
forces a strict canonical-objective decrease — continual
training descends the chain with certified zero forgetting. -/
theorem mini_hagi_gpm_canonical_descent
    {n KA KB : ℕ} (W ΔW : Matrix (Fin 1) (Fin n) ℝ)
    (xsA : Fin KA → (Fin n → ℝ)) (ysA : Fin KA → ℝ)
    (xsB : Fin KB → (Fin n → ℝ)) (ysB : Fin KB → ℝ)
    (horth : Hagi.Step.gpmOrth ΔW xsA)
    (hB : Hagi.Theory.ContinualBench.gpmBenchLoss (W + ΔW) xsB ysB < Hagi.Theory.ContinualBench.gpmBenchLoss W xsB ysB) :
    miniHagiCanonical (Hagi.Theory.ContinualBench.gpmBenchLoss (W + ΔW) xsA ysA)
        (Hagi.Theory.ContinualBench.gpmBenchLoss (W + ΔW) xsB ysB)
      < miniHagiCanonical (Hagi.Theory.ContinualBench.gpmBenchLoss W xsA ysA)
        (Hagi.Theory.ContinualBench.gpmBenchLoss W xsB ysB) := by
  have hA : Hagi.Theory.ContinualBench.gpmBenchLoss (W + ΔW) xsA ysA
      = Hagi.Theory.ContinualBench.gpmBenchLoss W xsA ysA :=
    Hagi.Theory.ContinualBench.gpm_bench_bridge W ΔW xsA ysA horth
  exact mini_hagi_canonical_drop (le_of_eq hA)
      (le_of_lt hB) (Or.inr hB)
end Hagi.Theory.MiniHagi
