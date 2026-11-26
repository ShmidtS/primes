/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Runtime.CertChecker
import Hagi.Theory.MiniHagi
import Mathlib.Tactic

/-!
# Mini-HAGI 2 bench bridge (scaled mini bench)

The SCALED mini bench
(`scripts/bench_bridge.py`, `--mode mini-hagi2`) — a deeper
trunk (2 sequential L1-rms → W1 → ReLU → W2 blocks, joint
finite-difference training through BOTH blocks in phase A), 3
continual tasks (split family), 2 fiber grow events
(margin each), accumulated GPM continual phases, ternary
quantization (gate) and the Ville holdout stop, all
on ONE canonical-objective `CertStepData` chain.

## The canonical objective rule (T = 3)

`miniHagi2Canonical a b c = (a + b + c) / 3` — та же канон-правка
MiniHagi (mean MSE живых задач; шаг допускается только измеренным
канон-ским drop > 0; `Hagi.Runtime.CertChecker.checkTrajectory`
проверяет цепь), инстанцированная на T = 3.

## The bridges

`mini_hagi2_canonical_drop`: per-task nonincrease with at least
one strict decrease forces a strict canonical drop — the 3-task
admission contract.

`mini_hagi2_gpm_descent`: the accumulated-GPM bridge — a step
orthogonal to the input spans of BOTH past tasks leaves their
bench losses EXACTLY invariant
(`Hagi.Theory.ContinualBench.gpm_bench_bridge`), so a
measured current-task decrease is a canonical decrease: the
third continual phase descends the canonical objective with
certified zero forgetting on both past tasks.

## Limits

1. The 2-block trunk is trained ONLY in phase A (joint fd
   gradients through both blocks, form) and FROZEN
   afterwards: GPM zero-forgetting and the grow mechanics
   are linear-readout statements, so phases B–E operate on the
   linear head over the frozen trunk features.
2. η = 1/10 with snap-to-grid candidates (1/10000 head /
   candidate grid; grow fibers and trunk-input features on the
   1/1000 grid; fd step h = 1/1000) — stated in the docstring in the
   bridge script.
3. The corpus is LIVE and prunes across sessions; the bench
   asserts N > 0 and reports the run-time N.
4. A rejected grow/quant and a never-firing stop are honest
   OUTCOMES (telemetry), not failures.
-/

namespace Hagi.Theory.MiniHagi2

/-- The canonical objective: mean MSE over the 3 live tasks. -/
noncomputable def miniHagi2Canonical (a b c : ℝ) : ℝ :=
  (a + b + c) / 3

/-- **mini_hagi2_canonical_drop**: if no task loss grows
and at least one strictly decreases, the 3-task canonical
objective strictly decreases — the admission contract every
mini-hagi2 phase satisfies on the shared chain. -/
theorem mini_hagi2_canonical_drop {a a' b b' c c' : ℝ}
    (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c)
    (h : a' < a ∨ b' < b ∨ c' < c) :
    miniHagi2Canonical a' b' c' < miniHagi2Canonical a b c := by
  unfold miniHagi2Canonical
  rcases h with h | h | h <;> linarith

/-- **mini_hagi2_gpm_descent**: the accumulated-GPM
bridge for the third continual phase. A step (each row of `ΔW`
orthogonal to every past-task input) leaves the bench losses of
BOTH past tasks EXACTLY invariant
(`Hagi.Theory.ContinualBench.gpm_bench_bridge`); a
measured current-task loss decrease then forces a strict
3-task canonical-objective decrease — continual training
descends the chain with certified zero forgetting on tasks 1
and 2. -/
theorem mini_hagi2_gpm_descent
    {n K1 K2 K3 : ℕ} (W ΔW : Matrix (Fin 1) (Fin n) ℝ)
    (xs1 : Fin K1 → (Fin n → ℝ)) (ys1 : Fin K1 → ℝ)
    (xs2 : Fin K2 → (Fin n → ℝ)) (ys2 : Fin K2 → ℝ)
    (xs3 : Fin K3 → (Fin n → ℝ)) (ys3 : Fin K3 → ℝ)
    (horth1 : Hagi.Step.gpmOrth ΔW xs1)
    (horth2 : Hagi.Step.gpmOrth ΔW xs2)
    (h3 : Hagi.Theory.ContinualBench.gpmBenchLoss (W + ΔW) xs3 ys3 <
      Hagi.Theory.ContinualBench.gpmBenchLoss W xs3 ys3) :
    miniHagi2Canonical
        (Hagi.Theory.ContinualBench.gpmBenchLoss (W + ΔW) xs1 ys1)
        (Hagi.Theory.ContinualBench.gpmBenchLoss (W + ΔW) xs2 ys2)
        (Hagi.Theory.ContinualBench.gpmBenchLoss (W + ΔW) xs3 ys3)
      < miniHagi2Canonical
        (Hagi.Theory.ContinualBench.gpmBenchLoss W xs1 ys1)
        (Hagi.Theory.ContinualBench.gpmBenchLoss W xs2 ys2)
        (Hagi.Theory.ContinualBench.gpmBenchLoss W xs3 ys3) := by
  have h1 : Hagi.Theory.ContinualBench.gpmBenchLoss (W + ΔW) xs1 ys1
      = Hagi.Theory.ContinualBench.gpmBenchLoss W xs1 ys1 :=
    Hagi.Theory.ContinualBench.gpm_bench_bridge W ΔW xs1 ys1 horth1
  have h2 : Hagi.Theory.ContinualBench.gpmBenchLoss (W + ΔW) xs2 ys2
      = Hagi.Theory.ContinualBench.gpmBenchLoss W xs2 ys2 :=
    Hagi.Theory.ContinualBench.gpm_bench_bridge W ΔW xs2 ys2 horth2
  exact mini_hagi2_canonical_drop (le_of_eq h1)
      (le_of_eq h2) (le_of_lt h3) (Or.inr (Or.inr h3))

end Hagi.Theory.MiniHagi2
