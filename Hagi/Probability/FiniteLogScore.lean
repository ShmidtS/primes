/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Prelude.Info
import Hagi.Probability.FiniteBayes

/-!
Support-aware finite categorical log score.

The coordinate argument adapts `Hagi.Prelude.kl_nonneg_of_nonneg` and the
strict/nonstrict bounds from `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
No support-indexed loss definition is introduced.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Probability.FiniteLogScore

open Hagi.Prelude
open Hagi.Probability.FiniteBayes
open scoped BigOperators

variable {X : Type*} [Fintype X]

private theorem coordinate_gap (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a → 0 < b) :
    0 ≤ a * Real.log (a / b) - (a - b) ∧
      (a * Real.log (a / b) - (a - b) = 0 ↔ b = a) := by
  by_cases ha0 : a = 0
  · simp [ha0, hb]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb_pos : 0 < b := hab ha_pos
    have hlog : Real.log (b / a) = -Real.log (a / b) := by
      rw [Real.log_div (ne_of_gt hb_pos) (ne_of_gt ha_pos),
        Real.log_div (ne_of_gt ha_pos) (ne_of_gt hb_pos)]
      ring
    have hnonneg : 0 ≤ a * Real.log (a / b) - (a - b) := by
      have h1 : Real.log (b / a) ≤ b / a - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hb_pos ha_pos)
      rw [hlog] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 ha
      have harith : a * (b / a - 1) = b - a := by
        field_simp [ha0]
      rw [harith] at h2
      linarith
    refine ⟨hnonneg, ?_⟩
    constructor
    · intro hgap
      by_contra hba
      have hratio : b / a ≠ 1 := by
        exact mt (div_eq_one_iff_eq ha0).mp hba
      have h1 : Real.log (b / a) < b / a - 1 :=
        Real.log_lt_sub_one_of_pos (div_pos hb_pos ha_pos) hratio
      rw [hlog] at h1
      have h2 := mul_lt_mul_of_pos_left h1 ha_pos
      have harith : a * (b / a - 1) = b - a := by
        field_simp [ha0]
      rw [harith] at h2
      linarith
    · intro hba
      subst b
      rw [div_self ha0, Real.log_one]
      ring

private theorem support_subset_iff_toReal_pos {X : Type*} (p q : PMF X) :
    p.support ⊆ q.support ↔
      ∀ x, 0 < (p x).toReal → 0 < (q x).toReal := by
  constructor
  · intro h x hpx
    have hpx' : 0 < p x := (ENNReal.toReal_pos_iff.mp hpx).1
    have hxp : x ∈ p.support := (p.apply_pos_iff x).mp hpx'
    have hqx : 0 < q x := (q.apply_pos_iff x).mpr (h hxp)
    exact ENNReal.toReal_pos (ne_of_gt hqx) (q.apply_ne_top x)
  · intro h x hx
    have hpx0 : p x ≠ 0 := (p.mem_support_iff x).mp hx
    have hpx : 0 < (p x).toReal :=
      ENNReal.toReal_pos hpx0 (p.apply_ne_top x)
    have hqx : 0 < (q x).toReal := h x hpx
    exact (q.apply_pos_iff x).mp (ENNReal.toReal_pos_iff.mp hqx).1

/-- KL is excess cross-entropy over self-CE on the support-aware domain. -/
theorem klDef_eq_ceDef_sub_of_support
    (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x)
    (hpq : ∀ x, 0 < p x → 0 < q x) :
    klDef p q = ceDef p q - ceDef p p := by
  classical
  unfold klDef ceDef
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : p x = 0
  · simp [hx]
  · have hpx : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hx)
    rw [Real.log_div (ne_of_gt hpx) (ne_of_gt (hpq x hpx))]
    ring

/-- Support-aware Gibbs nonnegativity, including target-zero cells. -/
theorem klDef_nonneg_of_support
    (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hsum_p : ∑ x, p x = 1) (hsum_q : ∑ x, q x = 1)
    (hpq : ∀ x, 0 < p x → 0 < q x) :
    0 ≤ klDef p q := by
  classical
  have hgap_nonneg : ∀ x ∈ Finset.univ,
      0 ≤ p x * Real.log (p x / q x) - (p x - q x) := by
    intro x _
    exact (coordinate_gap (p x) (q x) (hp x) (hq x) (hpq x)).1
  have hsum_nonneg := Finset.sum_nonneg hgap_nonneg
  have hsum_id :
      (∑ x, (p x * Real.log (p x / q x) - (p x - q x))) = klDef p q := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum_p, hsum_q]
    unfold klDef
    ring
  rw [hsum_id] at hsum_nonneg
  exact hsum_nonneg

/-- On normalized support-aware vectors, zero KL forces full equality. -/
theorem klDef_eq_zero_iff_of_support
    (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hsum_p : ∑ x, p x = 1) (hsum_q : ∑ x, q x = 1)
    (hpq : ∀ x, 0 < p x → 0 < q x) :
    klDef p q = 0 ↔ q = p := by
  classical
  constructor
  · intro hkl
    have hsum_id :
        (∑ x, (p x * Real.log (p x / q x) - (p x - q x))) = klDef p q := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum_p, hsum_q]
      unfold klDef
      ring
    have hsum_zero :
        (∑ x, (p x * Real.log (p x / q x) - (p x - q x))) = 0 := by
      rw [hsum_id]
      exact hkl
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
      (coordinate_gap (p x) (q x) (hp x) (hq x) (hpq x)).1)).mp hsum_zero
    funext x
    exact ((coordinate_gap (p x) (q x) (hp x) (hq x) (hpq x)).2.mp
      (hzero x (Finset.mem_univ x)))
  · intro hqp
    subst q
    unfold klDef
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : p x = 0
    · simp [hx]
    · rw [div_self hx, Real.log_one, mul_zero]

/-- Self-CE minimizes CE over normalized candidates covering the target support. -/
theorem ceDef_self_le_of_support
    (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hsum_p : ∑ x, p x = 1) (hsum_q : ∑ x, q x = 1)
    (hpq : ∀ x, 0 < p x → 0 < q x) :
    ceDef p p ≤ ceDef p q := by
  have hdecomp := klDef_eq_ceDef_sub_of_support p q hp hpq
  have hnonneg := klDef_nonneg_of_support p q hp hq hsum_p hsum_q hpq
  linarith

/-- The support-aware normalized CE minimizer is unique. -/
theorem ceDef_eq_self_iff_of_support
    (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hsum_p : ∑ x, p x = 1) (hsum_q : ∑ x, q x = 1)
    (hpq : ∀ x, 0 < p x → 0 < q x) :
    ceDef p q = ceDef p p ↔ q = p := by
  constructor
  · intro hce
    apply (klDef_eq_zero_iff_of_support p q hp hq hsum_p hsum_q hpq).mp
    have hdecomp := klDef_eq_ceDef_sub_of_support p q hp hpq
    linarith
  · intro hqp
    subst q
    rfl

/-- Arbitrary finite-PMF self-CE lower bound under support inclusion. -/
theorem fromPMF_ceDef_self_le
    {X : Type} [Fintype X] (p q : PMF X)
    (hpq : p.support ⊆ q.support) :
    ceDef (Hagi.Probability.fromPMF p) (Hagi.Probability.fromPMF p) ≤
      ceDef (Hagi.Probability.fromPMF p) (Hagi.Probability.fromPMF q) := by
  obtain ⟨x, hx⟩ := p.support_nonempty
  let _ : Nonempty X := ⟨x⟩
  exact ceDef_self_le_of_support _ _
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (Hagi.Probability.fromPMF_sum p) (Hagi.Probability.fromPMF_sum q)
    ((support_subset_iff_toReal_pos p q).mp hpq)

/-- Support inclusion makes the arbitrary finite-PMF CE minimizer unique. -/
theorem fromPMF_ceDef_eq_self_iff
    {X : Type} [Fintype X] (p q : PMF X)
    (hpq : p.support ⊆ q.support) :
    ceDef (Hagi.Probability.fromPMF p) (Hagi.Probability.fromPMF q) =
      ceDef (Hagi.Probability.fromPMF p) (Hagi.Probability.fromPMF p) ↔
        q = p := by
  obtain ⟨x, hx⟩ := p.support_nonempty
  let _ : Nonempty X := ⟨x⟩
  have hce := ceDef_eq_self_iff_of_support
    (Hagi.Probability.fromPMF p) (Hagi.Probability.fromPMF q)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (Hagi.Probability.fromPMF_sum p) (Hagi.Probability.fromPMF_sum q)
    ((support_subset_iff_toReal_pos p q).mp hpq)
  constructor
  · intro h
    have hvec := hce.mp h
    apply PMF.ext
    intro x
    have hx := congrFun hvec x
    exact (ENNReal.toReal_eq_toReal_iff'
      (q.apply_ne_top x) (p.apply_ne_top x)).mp hx
  · intro h
    subst q
    rfl

/-- The exact posterior minimizes CE among support-covering finite PMFs. -/
theorem posterior_ceDef_self_le
    {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y)
    (q : PMF X)
    (hpq : (posterior p₀ K y hobs).support ⊆ q.support) :
    ceDef (Hagi.Probability.fromPMF (posterior p₀ K y hobs))
      (Hagi.Probability.fromPMF (posterior p₀ K y hobs)) ≤
    ceDef (Hagi.Probability.fromPMF (posterior p₀ K y hobs))
      (Hagi.Probability.fromPMF q) := by
  exact fromPMF_ceDef_self_le (posterior p₀ K y hobs) q hpq

/-- The exact posterior is the unique support-aware finite-PMF CE minimizer. -/
theorem posterior_ceDef_eq_self_iff
    {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y)
    (q : PMF X)
    (hpq : (posterior p₀ K y hobs).support ⊆ q.support) :
    ceDef (Hagi.Probability.fromPMF (posterior p₀ K y hobs))
      (Hagi.Probability.fromPMF q) =
    ceDef (Hagi.Probability.fromPMF (posterior p₀ K y hobs))
      (Hagi.Probability.fromPMF (posterior p₀ K y hobs)) ↔
        q = posterior p₀ K y hobs := by
  exact fromPMF_ceDef_eq_self_iff (posterior p₀ K y hobs) q hpq

end Hagi.Probability.FiniteLogScore
