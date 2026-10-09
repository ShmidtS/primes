/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# StageCalculus — pure stage-arithmetic of the macro cycle

Layer-0 arithmetic lemmas with no Hagi dependencies:
`compress_stage`, `adaptive_ns_exists`, `compound_budget`.
-/

namespace Hagi.Foundations

/-- If `dnorm ≤ 1/2` and `E3 - E2pre ≤ kappa * s * dnorm`,
then `E3 - E2pre ≤ kappa * s / 2`. -/
theorem compress_stage (kappa s dnorm E3 E2pre : ℝ)
    (hkappa : 0 ≤ kappa) (hs : 0 ≤ s) (_hdn : 0 ≤ dnorm)
    (h_emp_dist : dnorm ≤ 1 / 2)
    (h_emp_lip : E3 - E2pre ≤ kappa * s * dnorm) :
    E3 - E2pre ≤ kappa * s / 2 := by
  have h1 : kappa * s * dnorm ≤ kappa * s * (1/2) :=
    mul_le_mul_of_nonneg_left h_emp_dist (by positivity)
  have h3 : kappa * s * (1/2) = kappa * s / 2 := by ring
  rw [h3] at h1
  linarith

/-- If `e 100 = 0` and `0 ≤ eps`, then `∃ s, e s ≤ eps`. -/
theorem adaptive_ns_exists (e : ℕ → ℝ) (eps : ℝ)
    (heps : 0 ≤ eps) (he0 : e 100 = 0) :
    ∃ s : ℕ, e s ≤ eps := by
  refine ⟨100, ?_⟩
  rw [he0]
  exact heps

/-- If `α * D + J ≤ ε_c` and `G_next ≤ D`, then
`α * G_next + J ≤ ε_c`. -/
theorem compound_budget (α D J ε_c : ℝ)
    (hα : 0 ≤ α) (hpos : α * D + J ≤ ε_c) :
    ∀ (G_next : ℝ), G_next ≤ D → α * G_next + J ≤ ε_c := by
  intro G_next hG
  calc α * G_next + J ≤ α * D + J := by
        refine add_le_add_left ?_ J
        exact mul_le_mul_of_nonneg_left hG hα
    _ ≤ ε_c := hpos

end Hagi.Foundations
