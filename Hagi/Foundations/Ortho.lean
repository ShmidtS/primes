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

theorem ortho_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] {v : ι → E} (hv : Orthonormal ℝ v) (c : ι → ℝ) :
    ‖∑ i, c i • v i‖ ^ 2 = ∑ i, c i ^ 2 := by
  have hdiag : ∀ i, inner ℝ (v i) (v i) = 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, hv.1 i, one_pow]
  have key : ∀ i, inner ℝ (c i • v i) (∑ j, c j • v j) = c i ^ 2 := by
    intro i
    rw [real_inner_smul_left, inner_sum]
    rw [Finset.sum_eq_single i]
    · rw [real_inner_smul_right, hdiag i, mul_one, ← pow_two]
    · intro j _hj hne
      rw [real_inner_smul_right, hv.2 (i := i) (j := j) (Ne.symm hne), mul_zero]

    · intro hni
      exact absurd (Finset.mem_univ i) hni
  rw [show ‖∑ i, c i • v i‖ ^ 2 = inner ℝ (∑ i, c i • v i) (∑ i, c i • v i) from by
      rw [real_inner_self_eq_norm_sq]]
  rw [real_inner_comm, inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [real_inner_comm]
  exact key i


/-- For orthonormal `v`, the squared reconstruction error of
routing to `s` equals the tail energy:
`‖(∑ i, c i • v i) − ∑ i ∈ s, c i • v i‖ ^ 2 = ∑ i ∈ sᶜ, c i ^ 2`. -/
theorem gating_tail_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → E} (hv : Orthonormal ℝ v)
    (c : ι → ℝ) (s : Finset ι) :
    ‖(∑ i, c i • v i) - ∑ i ∈ s, c i • v i‖ ^ 2 = ∑ i ∈ sᶜ, c i ^ 2 := by
  have heq : sᶜ = Finset.univ \ s := (Finset.compl_eq_univ_sdiff s).symm
  have hsplit : (∑ i, c i • v i) - ∑ i ∈ s, c i • v i = ∑ i ∈ sᶜ, c i • v i := by
    rw [heq, ← Finset.sum_sdiff (Finset.subset_univ s)]
    abel
  rw [hsplit]
  -- apply ortho_norm_sq to the tail coefficient function directly
  have horth := ortho_norm_sq hv (fun i => if i ∈ sᶜ then c i else 0)
  -- rewrite LHS sum: Σ (if...) • v = Σ_{sᶜ} c • v  (it IS the tail, same function)
  -- pull the smul inside the ite, then use sum_filter both directions
  have hmulite : ∀ i : ι, (if i ∈ sᶜ then c i else 0) • v i
      = if i ∈ sᶜ then c i • v i else 0 := fun i => by
    by_cases h : i ∈ sᶜ
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, zero_smul]
  have hfil : (Finset.univ : Finset ι).filter (fun j => j ∈ sᶜ) = sᶜ := by
    ext j; simp [Finset.mem_filter]
  have htail : ∑ i ∈ sᶜ, c i • v i = ∑ i, (if i ∈ sᶜ then c i else 0) • v i := by
    simp only [hmulite]
    rw [← Finset.sum_filter (s := (Finset.univ : Finset ι)) (p := fun j => j ∈ sᶜ)
      (f := fun j => c j • v j), hfil]
  have hsqite : ∀ i : ι, (if i ∈ sᶜ then c i else 0) ^ 2
      = if i ∈ sᶜ then c i ^ 2 else 0 := fun i => by
    by_cases h : i ∈ sᶜ
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      norm_num
  have htail2 : ∑ i ∈ sᶜ, c i ^ 2 = ∑ i, (if i ∈ sᶜ then c i else 0) ^ 2 := by
    simp only [hsqite]
    rw [← Finset.sum_filter (s := (Finset.univ : Finset ι)) (p := fun j => j ∈ sᶜ)
      (f := fun j => c j ^ 2), hfil]
  rw [htail, htail2]
  exact horth

end Hagi.Foundations

namespace Hagi
export Hagi.Foundations (ortho_norm_sq gating_tail_bound)
end Hagi
