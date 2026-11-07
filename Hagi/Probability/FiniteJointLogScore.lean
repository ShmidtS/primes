/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Prelude.Info
import Hagi.Probability.FiniteLogScore

/-!
Support-aware finite conditional cross-entropy and KL chain rules.

Zero-mass rows use the zero function as a totalization policy; they are not
asserted to be conditional probability laws.  The guarded logarithm splitting
and Fubini algebra adapt `Hagi.Probability.EntropyConvexity.entropy_chain`;
the old positive-only theorem is not imported or applied.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Probability.FiniteJointLogScore

open Hagi.Prelude
open scoped BigOperators

/-- First-coordinate marginal of a finite real joint vector. -/
def leftMarginal {X Y : Type*} [Fintype Y]
    (p : X × Y → ℝ) : X → ℝ :=
  fun x => ∑ y, p (x, y)

/-- Conditional row on positive first-coordinate mass, zero otherwise. -/
noncomputable def conditionalRow {X Y : Type*} [Fintype Y]
    (p : X × Y → ℝ) (x : X) : Y → ℝ :=
  if 0 < leftMarginal p x then
    fun y => p (x, y) / leftMarginal p x
  else
    0

private theorem leftMarginal_nonneg {X Y : Type*} [Fintype Y]
    (p : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z) (x : X) :
    0 ≤ leftMarginal p x :=
  Finset.sum_nonneg fun y _ => hp (x, y)

private theorem leftMarginal_pos_of_pos {X Y : Type*} [Fintype Y]
    (p : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z) (x : X) (y : Y)
    (hxy : 0 < p (x, y)) : 0 < leftMarginal p x := by
  apply (Finset.sum_pos_iff_of_nonneg (fun y _ => hp (x, y))).2
  exact ⟨y, Finset.mem_univ y, hxy⟩

private theorem leftMarginal_eq_zero_of_not_pos {X Y : Type*} [Fintype Y]
    (p : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z) (x : X)
    (hx : ¬0 < leftMarginal p x) : leftMarginal p x = 0 :=
  le_antisymm (le_of_not_gt hx) (leftMarginal_nonneg p hp x)

private theorem leftMarginal_mul_conditionalRow_of_pos {X Y : Type*} [Fintype Y]
    (p : X × Y → ℝ) (x : X) (hx : 0 < leftMarginal p x) (y : Y) :
    leftMarginal p x * conditionalRow p x y = p (x, y) := by
  rw [conditionalRow, ite_eq_left hx]
  field_simp [hx.ne']

private theorem leftMarginal_mul_conditionalRow {X Y : Type*} [Fintype Y]
    (p : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z) (x : X) (y : Y) :
    leftMarginal p x * conditionalRow p x y = p (x, y) := by
  by_cases hx : 0 < leftMarginal p x
  · exact leftMarginal_mul_conditionalRow_of_pos p x hx y
  · have hx0 := leftMarginal_eq_zero_of_not_pos p hp x hx
    have hxy : p (x, y) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hp (x, y))).1
        hx0 y (Finset.mem_univ y)
    rw [hx0, hxy, zero_mul]

private theorem conditionalRow_eq_zero_of_eq_zero {X Y : Type*} [Fintype Y]
    (p : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z) (x : X) (y : Y)
    (hxy : p (x, y) = 0) : conditionalRow p x y = 0 := by
  by_cases hx : 0 < leftMarginal p x
  · apply (mul_eq_zero.mp ((leftMarginal_mul_conditionalRow p hp x y).trans hxy)).resolve_left
    exact hx.ne'
  · rw [conditionalRow, ite_eq_right hx]
    rfl

private theorem conditionalRow_sum {X Y : Type*} [Fintype Y]
    (p : X × Y → ℝ) (x : X) (hx : 0 < leftMarginal p x) :
    ∑ y, conditionalRow p x y = 1 := by
  rw [conditionalRow, ite_eq_left hx, ← Finset.sum_div]
  exact div_self hx.ne'

private theorem conditionalRow_nonneg {X Y : Type*} [Fintype Y]
    (p : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z) (x : X) (y : Y) :
    0 ≤ conditionalRow p x y := by
  by_cases hx : 0 < leftMarginal p x
  · rw [conditionalRow, ite_eq_left hx]
    exact div_nonneg (hp (x, y)) hx.le
  · rw [conditionalRow, ite_eq_right hx]
    exact le_rfl

private theorem conditionalRow_pos_of_pos {X Y : Type*} [Fintype Y]
    (p q : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hpq : ∀ z, 0 < p z → 0 < q z)
    (hμ : ∀ x, 0 < leftMarginal p x → 0 < leftMarginal q x)
    (x : X) (y : Y) (hxy : 0 < conditionalRow p x y) :
    0 < conditionalRow q x y := by
  have hx : 0 < leftMarginal p x := by
    by_contra hx
    simp [conditionalRow, hx] at hxy
  have hp_pos : 0 < p (x, y) := by
    rw [← leftMarginal_mul_conditionalRow p hp x y]
    exact mul_pos hx hxy
  have hμq := hμ x hx
  rw [conditionalRow, ite_eq_left hμq]
  exact div_pos (hpq (x, y) hp_pos) hμq

private theorem ce_cell_split {X Y : Type*} [Fintype Y]
    (p q : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hpq : ∀ z, 0 < p z → 0 < q z)
    (hμ : ∀ x, 0 < leftMarginal p x → 0 < leftMarginal q x)
    (x : X) (y : Y) :
    p (x, y) * Real.log (q (x, y)) =
      p (x, y) * Real.log (leftMarginal q x) +
        leftMarginal p x *
          (conditionalRow p x y * Real.log (conditionalRow q x y)) := by
  by_cases hxy : p (x, y) = 0
  · have hρp := conditionalRow_eq_zero_of_eq_zero p hp x y hxy
    rw [hxy, hρp]
    ring
  · have hp_pos : 0 < p (x, y) := lt_of_le_of_ne (hp (x, y)) (Ne.symm hxy)
    have hμp := leftMarginal_pos_of_pos p hp x y hp_pos
    have hμq := hμ x hμp
    have hρp : 0 < conditionalRow p x y := by
      rw [conditionalRow, ite_eq_left hμp]
      exact div_pos hp_pos hμp
    have hρq := conditionalRow_pos_of_pos p q hp hpq hμ x y hρp
    have hrecp := leftMarginal_mul_conditionalRow p hp x y
    have hrecq := leftMarginal_mul_conditionalRow_of_pos q x hμq y
    rw [← hrecq, Real.log_mul hμq.ne' hρq.ne', ← hrecp]
    ring

private theorem klDef_self {X : Type*} [Fintype X] (p : X → ℝ) :
    klDef p p = 0 := by
  unfold klDef
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : p x = 0
  · simp [hx]
  · rw [div_self hx, Real.log_one, mul_zero]

/-- Conditional CE chain, without global normalization assumptions. -/
theorem ceDef_chain {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X × Y → ℝ)
    (hp : ∀ z, 0 ≤ p z)
    (hpq : ∀ z, 0 < p z → 0 < q z)
    (hμ : ∀ x, 0 < leftMarginal p x → 0 < leftMarginal q x) :
    ceDef p q = ceDef (leftMarginal p) (leftMarginal q) +
      ∑ x, leftMarginal p x *
        ceDef (conditionalRow p x) (conditionalRow q x) := by
  have hA : (∑ z : X × Y, p z * Real.log (leftMarginal q z.1)) =
      ∑ x, leftMarginal p x * Real.log (leftMarginal q x) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    rw [leftMarginal, Finset.sum_mul]
  have hB : (∑ z : X × Y, leftMarginal p z.1 *
      (conditionalRow p z.1 z.2 * Real.log (conditionalRow q z.1 z.2))) =
      ∑ x, leftMarginal p x *
        (∑ y, conditionalRow p x y * Real.log (conditionalRow q x y)) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  have hsum : (∑ z, p z * Real.log (q z)) =
      (∑ x, leftMarginal p x * Real.log (leftMarginal q x)) +
        ∑ x, leftMarginal p x *
          (∑ y, conditionalRow p x y * Real.log (conditionalRow q x y)) := by
    rw [Finset.sum_congr rfl (fun z _ => ce_cell_split p q hp hpq hμ z.1 z.2),
      Finset.sum_add_distrib, hA, hB]
  calc
    ceDef p q = -(∑ z, p z * Real.log (q z)) := rfl
    _ = -((∑ x, leftMarginal p x * Real.log (leftMarginal q x)) +
        ∑ x, leftMarginal p x *
          (∑ y, conditionalRow p x y * Real.log (conditionalRow q x y))) := by rw [hsum]
    _ = -(∑ x, leftMarginal p x * Real.log (leftMarginal q x)) +
        ∑ x, leftMarginal p x *
          (-(∑ y, conditionalRow p x y * Real.log (conditionalRow q x y))) := by
      rw [neg_add]
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ceDef (leftMarginal p) (leftMarginal q) +
        ∑ x, leftMarginal p x *
          ceDef (conditionalRow p x) (conditionalRow q x) := rfl

/-- Conditional KL chain, obtained from the joint, marginal, and row CE gaps. -/
theorem klDef_chain {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X × Y → ℝ)
    (hp : ∀ z, 0 ≤ p z)
    (hpq : ∀ z, 0 < p z → 0 < q z)
    (hμ : ∀ x, 0 < leftMarginal p x → 0 < leftMarginal q x) :
    klDef p q = klDef (leftMarginal p) (leftMarginal q) +
      ∑ x, leftMarginal p x *
        klDef (conditionalRow p x) (conditionalRow q x) := by
  have hrow (x : X) :
      klDef (conditionalRow p x) (conditionalRow q x) =
        ceDef (conditionalRow p x) (conditionalRow q x) -
          ceDef (conditionalRow p x) (conditionalRow p x) :=
    FiniteLogScore.klDef_eq_ceDef_sub_of_support _ _
      (conditionalRow_nonneg p hp x)
      (conditionalRow_pos_of_pos p q hp hpq hμ x)
  rw [FiniteLogScore.klDef_eq_ceDef_sub_of_support p q hp hpq,
    ceDef_chain p q hp hpq hμ,
    ceDef_chain p p hp (fun _ h => h) (fun _ h => h),
    FiniteLogScore.klDef_eq_ceDef_sub_of_support (leftMarginal p) (leftMarginal q)
      (leftMarginal_nonneg p hp) hμ]
  simp_rw [hrow]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- With equal first marginals, exact CE agreement is precisely agreement of
all conditionals on positive target rows. -/
theorem ceDef_eq_self_iff_conditionalRow_eq_of_leftMarginal_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X × Y → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z)
    (hpq : ∀ z, 0 < p z → 0 < q z)
    (hqm : leftMarginal q = leftMarginal p) :
    ceDef p q = ceDef p p ↔
      ∀ x, 0 < leftMarginal p x →
        conditionalRow q x = conditionalRow p x := by
  have hμ : ∀ x, 0 < leftMarginal p x → 0 < leftMarginal q x := by
    intro x hx
    obtain ⟨y, _, hy⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun y _ => hp (x, y))).1 hx
    apply (Finset.sum_pos_iff_of_nonneg (fun y _ => hq (x, y))).2
    exact ⟨y, Finset.mem_univ y, hpq (x, y) hy⟩
  have hrow (x : X) :
      klDef (conditionalRow p x) (conditionalRow q x) =
        ceDef (conditionalRow p x) (conditionalRow q x) -
          ceDef (conditionalRow p x) (conditionalRow p x) :=
    FiniteLogScore.klDef_eq_ceDef_sub_of_support _ _
      (conditionalRow_nonneg p hp x)
      (conditionalRow_pos_of_pos p q hp hpq hμ x)
  have hresidual : ceDef p q - ceDef p p =
      ∑ x, leftMarginal p x *
        klDef (conditionalRow p x) (conditionalRow q x) := by
    rw [ceDef_chain p q hp hpq hμ,
      ceDef_chain p p hp (fun _ h => h) (fun _ h => h), hqm]
    simp_rw [hrow]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hterm (x : X) :
      0 ≤ leftMarginal p x *
        klDef (conditionalRow p x) (conditionalRow q x) := by
    by_cases hx : 0 < leftMarginal p x
    · apply mul_nonneg hx.le
      exact FiniteLogScore.klDef_nonneg_of_support _ _
        (conditionalRow_nonneg p hp x) (conditionalRow_nonneg q hq x)
        (conditionalRow_sum p x hx) (conditionalRow_sum q x (hμ x hx))
        (conditionalRow_pos_of_pos p q hp hpq hμ x)
    · rw [leftMarginal_eq_zero_of_not_pos p hp x hx, zero_mul]
  constructor
  · intro hce x hx
    have hsumzero : (∑ x, leftMarginal p x *
        klDef (conditionalRow p x) (conditionalRow q x)) = 0 := by
      rw [← hresidual, hce]
      ring
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => hterm x)).1 hsumzero x (Finset.mem_univ x)
    have hkl : klDef (conditionalRow p x) (conditionalRow q x) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hx.ne'
    exact (FiniteLogScore.klDef_eq_zero_iff_of_support _ _
      (conditionalRow_nonneg p hp x) (conditionalRow_nonneg q hq x)
      (conditionalRow_sum p x hx) (conditionalRow_sum q x (hμ x hx))
      (conditionalRow_pos_of_pos p q hp hpq hμ x)).1 hkl
  · intro hrows
    have hsumzero : (∑ x, leftMarginal p x *
        klDef (conditionalRow p x) (conditionalRow q x)) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : 0 < leftMarginal p x
      · rw [hrows x hx, klDef_self, mul_zero]
      · rw [leftMarginal_eq_zero_of_not_pos p hp x hx, zero_mul]
    have hd : ceDef p q - ceDef p p = 0 := hresidual.trans hsumzero
    linarith

end Hagi.Probability.FiniteJointLogScore
