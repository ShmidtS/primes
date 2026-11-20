/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.GPM
import Mathlib.Tactic

set_option relaxedAutoImplicit false

/-!
# Continual bench — GPM zero forgetting bridge (C485, beat C484)

The C483 roadmap continual front: a real continual scenario —
task A → task B — where the model must not lose task A while
learning task B. The bench (`scripts/bench_bridge.py`,
`--mode continual`) trains a certified linear head on task A
(few-shot, real unified_ledger data), then retrains on task B
two ways: (a) naive certified GD (forgetting on A is MEASURED),
(b) GPM — the step is projected onto the orthogonal complement
of `span` of the task-A inputs (exact rational Gram-Schmidt
projector `Q = I − Σ u uᵀ/(u·u)`, Saha et al. ICLR'21, honest
full-span version without spectral truncation).

## Coordination only — the mathematics lives in `Hagi.Step.GPM`

- `gpm_bench_bridge`: the projected step satisfies `gpmOrth`, so
  per-point outputs on task A are EXACTLY invariant
  (`Hagi.Step.gpm_zero_forgetting`), hence the bench loss on A is
  bit-exact invariant. NEW here is only the per-point-to-sum
  glue on the bench structure.
- `naive_step_can_forget`: the mini-negative — an explicit naive
  step (no orthogonality) that MOVES the task-A output: without
  `gpmOrth` no preservation follows. Machine-checked witness.

Layer decision: Theory (7) — the module consumes the GPM step
theory (`Hagi.Step.GPM`, layer 5) and is consumed by the C485
bench witness.
-/

open scoped Matrix

namespace Hagi.Theory.ContinualBench

variable {n K : ℕ}

/-- The continual bench loss on one task: sum of squared errors
of the scalar linear head `W` over the task inputs `xs` and
targets `ys` (the C485 bench uses the mean; the sum scales by a
positive constant and the invariance statement is identical). -/
def gpmBenchLoss (W : Matrix (Fin 1) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (ys : Fin K → ℝ) : ℝ :=
  ∑ k, ((W *ᵥ xs k) 0 - ys k) ^ 2

/-- **gpm_bench_bridge (C485)**: a GPM step (each row of `ΔW`
orthogonal to every task-A input, `gpmOrth`) leaves the bench
loss on task A EXACTLY invariant — `gpm_zero_forgetting` applied
per point of the bench structure. This is the machine-checked
statement behind the bench telemetry line `loss_A before/after
GPM phase` being equal Fractions. -/
theorem gpm_bench_bridge (W ΔW : Matrix (Fin 1) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (ys : Fin K → ℝ)
    (horth : Hagi.Step.gpmOrth ΔW xs) :
    gpmBenchLoss (W + ΔW) xs ys = gpmBenchLoss W xs ys := by
  unfold gpmBenchLoss
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hagi.Step.gpm_zero_forgetting W ΔW xs horth k]

/-- **naive_step_can_forget (C485)**: the mini-negative — without
the GPM orthogonality the task-A output is NOT preserved: an
explicit `W`, `ΔW` and task-A input where `gpmOrth` fails and the
head output on the old input moves (`1 ≠ 0`, machine-checked).
The naive bench path has no preservation guarantee; its actual
forgetting is measured, not certified away. -/
theorem naive_step_can_forget :
    ∃ (W ΔW : Matrix (Fin 1) (Fin 2) ℝ)
      (xs : Fin 1 → (Fin 2 → ℝ)),
      ¬ Hagi.Step.gpmOrth ΔW xs
        ∧ (W + ΔW) *ᵥ xs 0 ≠ W *ᵥ xs 0 := by
  refine ⟨Matrix.of (fun _ _ => (0 : ℝ)),
    Matrix.of fun _ j => if j = 0 then 1 else 0,
    fun _ j => if j = 0 then 1 else 0, ?_, ?_⟩
  · intro h
    have h0 := h 0 0
    norm_num [dotProduct, Matrix.of_apply] at h0
  · intro h
    have h0 := congrFun h 0
    norm_num [Matrix.add_mulVec, Matrix.mulVec, dotProduct,
      Matrix.of_apply, Fin.sum_univ_two, Pi.add_apply,
      Matrix.zero_apply, Pi.zero_apply] at h0

end Hagi.Theory.ContinualBench
