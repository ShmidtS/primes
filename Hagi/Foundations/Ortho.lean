/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# Ortho — координатные тождества для ортонормальных семейств

(R328: перенесено из Unified/RecursiveGrowth — аудит v3 §2.2:
чистая линейная алгебра живёт в низком слое.)

* `ortho_norm_sq` (Parseval-типа): `‖∑ c i • v i‖² = ∑ c i²`;
* `gating_tail_bound`: хвостовая энергия гейтинга —
  `‖(∑ c i • v i) − ∑ i ∈ s, c i • v i‖² = ∑ i ∈ sᶜ, c i²`.
-/

open Finset Real

namespace Hagi.Foundations

/-- Parseval-тождество на произвольном Finset: норма частичной
линейной комбинации ортонормального семейства равна сумме
квадратов коэффициентов. Канон R333: `ortho_norm_sq`,
`gating_tail_bound` (Sparsity) и `spectral_tail_energy`
(Spectral) — следствия этого принципа. -/
theorem ortho_norm_sq_finset {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] {v : ι → E} (hv : Orthonormal ℝ v) (c : ι → ℝ)
    (t : Finset ι) :
    ‖∑ i ∈ t, c i • v i‖ ^ 2 = ∑ i ∈ t, c i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, Orthonormal.inner_sum hv c c t]
  exact Finset.sum_congr rfl fun i _ => by simp; ring

theorem ortho_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] {v : ι → E} (hv : Orthonormal ℝ v) (c : ι → ℝ) :
    ‖∑ i, c i • v i‖ ^ 2 = ∑ i, c i ^ 2 := ortho_norm_sq_finset hv c Finset.univ

theorem gating_tail_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → E} (hv : Orthonormal ℝ v)
    (c : ι → ℝ) (s : Finset ι) :
    ‖(∑ i, c i • v i) - ∑ i ∈ s, c i • v i‖ ^ 2 = ∑ i ∈ sᶜ, c i ^ 2 := by
  have hsplit : (∑ i, c i • v i) - ∑ i ∈ s, c i • v i
      = ∑ i ∈ sᶜ, c i • v i := by
    rw [Finset.compl_eq_univ_sdiff s, ← Finset.sum_sdiff (Finset.subset_univ s)]
    abel
  rw [hsplit]
  exact ortho_norm_sq_finset hv c sᶜ

end Hagi.Foundations

namespace Hagi
export Hagi.Foundations (ortho_norm_sq_finset ortho_norm_sq gating_tail_bound)
end Hagi
