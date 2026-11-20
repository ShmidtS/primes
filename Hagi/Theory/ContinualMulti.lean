/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.ContinualBench
import Hagi.Spectral.RankGrowth
import Mathlib.Tactic

set_option relaxedAutoImplicit false

/-!
# Continual multi-task — accumulated GPM subspace (C488, beat C487)

The C486 roadmap top-3 continual front: THREE OR MORE sequential
tasks with GPM subspace ACCUMULATION. Before phase `t+1` the bench
projects every step onto the orthogonal complement of the span of
the inputs of ALL tasks `1..t` (union of spans, exact rational
Gram-Schmidt). The rank of the accumulated basis grows per task by
the number of genuinely new independent directions — the setting
of `Hagi.Spectral.rank_orthogonal_growth` (k linearly independent
new rows orthogonal to all old rows grow the rank by EXACTLY k),
which is the rank-track certificate behind the bench telemetry
`rank_track`.

## Statements

- `gpm_multi_step_invariant`: a step of phase `t+1` orthogonal to
  every input of every task `s ≤ t` leaves the bench loss on EACH
  past task exactly invariant (direct application of
  `Hagi.Theory.ContinualBench.gpm_bench_bridge`, which applies
  `Hagi.Step.gpm_zero_forgetting` per point).
- `gpm_multi_zero_forgetting` (main): chained by induction on the
  phase index — the loss of task `s` at ANY later time `t ≥ s+1`
  equals its value right after phase `s`. This is the
  machine-checked statement behind the bench forgetting matrix
  being exactly zero on all past tasks (the numeric bench asserts
  the per-commit invariance as its realization).

Layer decision: Theory (7) — consumes `Hagi.Theory.ContinualBench`
(theory) and cites `Hagi.Spectral.RankGrowth` for the rank track;
consumed by the C488 bench witness.
-/

open scoped Matrix

namespace Hagi.Theory.ContinualMulti

variable {n K : ℕ}

/-- **gpm_multi_step_invariant (C488)**: if the step `dW t` of
phase `t+1` is GPM-orthogonal to every input of every task `s ≤ t`
(orthogonality to the ACCUMULATED span of tasks `1..t`), then the
bench loss on each past task is exactly invariant under the step. -/
theorem gpm_multi_step_invariant
    (dW : ℕ → Matrix (Fin 1) (Fin n) ℝ)
    (xs : ℕ → Fin K → (Fin n → ℝ))
    (ys : ℕ → Fin K → ℝ)
    (W : ℕ → Matrix (Fin 1) (Fin n) ℝ)
    (hchain : ∀ t, W (t+1) = W t + dW t)
    (horth : ∀ t s, s ≤ t → Hagi.Step.gpmOrth (dW t) (xs s)) :
    ∀ t s, s ≤ t →
      Hagi.Theory.ContinualBench.gpmBenchLoss (W (t+1)) (xs s) (ys s)
        = Hagi.Theory.ContinualBench.gpmBenchLoss (W t) (xs s) (ys s) := by
  intro t s hs
  rw [hchain t]
  exact Hagi.Theory.ContinualBench.gpm_bench_bridge (W t) (dW t)
    (xs s) (ys s) (horth t s hs)

/-- **gpm_multi_zero_forgetting (C488, main)**: with each phase
step orthogonal to all inputs of all past tasks (GPM on the
accumulated subspace), the bench loss of task `s` at ANY later
phase end `t ≥ s+1` equals its value right after phase `s` —
zero forgetting across the whole multi-task sequence, chained
from `gpm_zero_forgetting` step by step (induction on `t`).
Rank track: the accumulated Gram-Schmidt basis grows per task by
its number of linearly independent new directions —
`Hagi.Spectral.rank_orthogonal_growth` (k new orthogonal
independent rows ⇒ rank grows by exactly k). -/
theorem gpm_multi_zero_forgetting
    (dW : ℕ → Matrix (Fin 1) (Fin n) ℝ)
    (xs : ℕ → Fin K → (Fin n → ℝ))
    (ys : ℕ → Fin K → ℝ)
    (W : ℕ → Matrix (Fin 1) (Fin n) ℝ)
    (hchain : ∀ t, W (t+1) = W t + dW t)
    (horth : ∀ t s, s ≤ t → Hagi.Step.gpmOrth (dW t) (xs s)) :
    ∀ t s, s < t →
      Hagi.Theory.ContinualBench.gpmBenchLoss (W t) (xs s) (ys s)
        = Hagi.Theory.ContinualBench.gpmBenchLoss (W (s+1)) (xs s)
            (ys s) := by
  intro t
  induction t with
  | zero => intro s hs; omega
  | succ t ih =>
      intro s hs
      by_cases h : s = t
      · subst h; rfl
      · have hst : s ≤ t := by omega
        rw [hchain t]
        rw [Hagi.Theory.ContinualBench.gpm_bench_bridge (W t) (dW t)
          (xs s) (ys s) (horth t s hst)]
        exact ih s (by omega)

end Hagi.Theory.ContinualMulti
