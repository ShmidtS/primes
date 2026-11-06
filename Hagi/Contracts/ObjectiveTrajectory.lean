/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-! Objective-height helpers over real sequences. -/

namespace Hagi.Contracts.ObjectiveTrajectory

open Filter Topology

/-- Dominating drops telescope against the actual objective differences. -/
theorem sum_drop_le_initial_sub
    (E δ : ℕ → ℝ) (T : ℕ)
    (hδ : ∀ t, δ t ≤ E t - E (t + 1)) :
    ∑ t ∈ Finset.range T, δ t ≤ E 0 - E T := by
  calc
    ∑ t ∈ Finset.range T, δ t ≤
        ∑ t ∈ Finset.range T, (E t - E (t + 1)) :=
      Finset.sum_le_sum fun t _ht => hδ t
    _ = E 0 - E T := by
      simpa using Finset.sum_range_sub' E T

/-- A nonnegative antitone sequence converges to its real infimum. -/
theorem tendsto_ciInf_of_antitone_nonneg
    (E : ℕ → ℝ) (hanti : Antitone E) (hnn : ∀ t, 0 ≤ E t) :
    Tendsto E atTop (𝓝 (⨅ t, E t)) := by
  apply tendsto_atTop_ciInf hanti
  refine ⟨0, ?_⟩
  exact fun x hx => by rcases hx with ⟨t, rfl⟩; exact hnn t

/-- Nonnegative infimum follows from nonnegative sequence values. -/
theorem ciInf_nonneg (E : ℕ → ℝ) (hnn : ∀ t, 0 ≤ E t) :
    0 ≤ ⨅ t, E t := le_ciInf hnn

end Hagi.Contracts.ObjectiveTrajectory
