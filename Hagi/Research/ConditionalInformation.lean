/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Research.CrossModalGap
import Hagi.Probability.FiniteJointLogScore

/-!
Bounded finite conditional mutual information.

The reference-ratio identity is stated for strictly positive normalized joints.
Its external reference need not match the joint's outcome marginal; the
reference-mismatch KL is subtracted explicitly.  No continuous likelihood or
independence claim is made.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Omni

open Hagi.Prelude
open Hagi.Probability.FiniteJointLogScore
open scoped BigOperators

private theorem nonempty_of_sum_eq_one {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hsum : ∑ i, p i = 1) : Nonempty ι := by
  classical
  by_contra h
  have : IsEmpty ι := not_nonempty_iff.mp h
  simp at hsum

private theorem leftMarginal_pos_of_positive {X Y : Type*} [Fintype Y]
    [Nonempty Y] (p : X × Y → ℝ) (hp : ∀ a, 0 < p a) (x : X) :
    0 < leftMarginal p x := by
  exact Finset.sum_pos (fun y _ => hp (x, y)) Finset.univ_nonempty

private theorem conditionalRow_pos_of_positive {X Y : Type*} [Fintype Y]
    [Nonempty Y] (p : X × Y → ℝ) (hp : ∀ a, 0 < p a) (x : X) (y : Y) :
    0 < conditionalRow p x y := by
  have hx := leftMarginal_pos_of_positive p hp x
  rw [conditionalRow, ite_eq_left hx]
  exact div_pos (hp (x, y)) hx

private theorem conditionalRow_sum_of_positive {X Y : Type*} [Fintype Y]
    [Nonempty Y] (p : X × Y → ℝ) (hp : ∀ a, 0 < p a) (x : X) :
    ∑ y, conditionalRow p x y = 1 := by
  have hx := leftMarginal_pos_of_positive p hp x
  rw [conditionalRow, ite_eq_left hx, ← Finset.sum_div]
  exact div_self hx.ne'

private theorem leftMarginal_mul_conditionalRow_of_positive {X Y : Type*}
    [Fintype Y] [Nonempty Y] (p : X × Y → ℝ) (hp : ∀ a, 0 < p a)
    (x : X) (y : Y) :
    leftMarginal p x * conditionalRow p x y = p (x, y) := by
  have hx := leftMarginal_pos_of_positive p hp x
  rw [conditionalRow, ite_eq_left hx]
  field_simp [hx.ne']

private theorem klDef_self_of_pos {Y : Type*} [Fintype Y]
    (p : Y → ℝ) (hp : ∀ y, 0 < p y) : klDef p p = 0 := by
  unfold klDef
  apply Finset.sum_eq_zero
  intro y _
  rw [div_self (hp y).ne', Real.log_one, mul_zero]

/-- Conditional mutual information of a finite joint on `X × (Z × Y)`. -/
noncomputable def conditionalMutualInformation {X Z Y : Type}
    [Fintype X] [Fintype Z] [Fintype Y] (p : X × (Z × Y) → ℝ) : ℝ :=
  ∑ x, leftMarginal p x * crossModalGap (conditionalRow p x)

/-- Conditional mutual information is the expected log reference ratio minus
exactly the reference-mismatch KL. -/
theorem conditionalMutualInformation_eq_expected_log_ratio_sub_reference_kl
    {X Z Y : Type} [Fintype X] [Fintype Z] [Fintype Y]
    (p : X × (Z × Y) → ℝ) (q : X → Y → ℝ)
    (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hq : ∀ x y, 0 < q x y) (hqsum : ∀ x, ∑ y, q x y = 1) :
    conditionalMutualInformation p =
      (∑ x, ∑ z, ∑ y, p (x, (z, y)) *
        Real.log ((conditionalRow p x (z, y) / margX (conditionalRow p x) z) /
          q x y)) -
      ∑ x, leftMarginal p x * klDef (margY (conditionalRow p x)) (q x) := by
  classical
  let : Nonempty (X × (Z × Y)) := nonempty_of_sum_eq_one p hsum
  let : Nonempty X := Nonempty.map (fun a : X × (Z × Y) => a.1) inferInstance
  let : Nonempty Z := Nonempty.map (fun a : X × (Z × Y) => a.2.1) inferInstance
  let : Nonempty Y :=
    nonempty_of_sum_eq_one (q (Classical.arbitrary X)) (hqsum (Classical.arbitrary X))
  have hμ : ∀ x, 0 < leftMarginal p x :=
    fun x => leftMarginal_pos_of_positive p hp x
  have hr : ∀ x a, 0 < conditionalRow p x a :=
    fun x a => conditionalRow_pos_of_positive p (fun a => hp a) x a
  have hrec (x : X) (a : Z × Y) :
      leftMarginal p x * conditionalRow p x a = p (x, a) :=
    leftMarginal_mul_conditionalRow_of_positive p hp x a
  have hgap (x : X) : crossModalGap (conditionalRow p x) =
      klDef (conditionalRow p x)
        (fun a => margX (conditionalRow p x) a.1 *
          margY (conditionalRow p x) a.2) :=
    crossModalGap_eq_kl (conditionalRow p x) (hr x)
      (conditionalRow_sum_of_positive p hp x)
  have hmy (x : X) (y : Y) : 0 < margY (conditionalRow p x) y :=
    margY_pos (conditionalRow p x) (hr x) y
  have hlog (x : X) (z : Z) (y : Y) :
      Real.log ((conditionalRow p x (z, y) / margX (conditionalRow p x) z) /
          q x y) =
        Real.log (conditionalRow p x (z, y) /
            (margX (conditionalRow p x) z * margY (conditionalRow p x) y)) +
          Real.log (margY (conditionalRow p x) y / q x y) := by
    rw [Real.log_div
        (div_pos (hr x (z, y)) (margX_pos (conditionalRow p x) (hr x) z)).ne'
        (hq x y).ne',
      Real.log_div (hr x (z, y)).ne'
        (margX_pos (conditionalRow p x) (hr x) z).ne',
      Real.log_div (hr x (z, y)).ne'
        (mul_pos (margX_pos (conditionalRow p x) (hr x) z) (hmy x y)).ne',
      Real.log_mul (margX_pos (conditionalRow p x) (hr x) z).ne' (hmy x y).ne',
      Real.log_div (hmy x y).ne' (hq x y).ne']
    ring
  have hcmi : conditionalMutualInformation p =
      ∑ x, ∑ z, ∑ y, p (x, (z, y)) *
        Real.log (conditionalRow p x (z, y) /
          (margX (conditionalRow p x) z * margY (conditionalRow p x) y)) := by
    unfold conditionalMutualInformation
    apply Finset.sum_congr rfl
    intro x _
    rw [hgap x]
    unfold klDef
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [← hrec x (z, y)]
    ring
  have hD :
      (∑ x, ∑ z, ∑ y, p (x, (z, y)) *
        Real.log (margY (conditionalRow p x) y / q x y)) =
      ∑ x, leftMarginal p x * klDef (margY (conditionalRow p x)) (q x) := by
    unfold klDef
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [margY, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [← hrec x (z, y)]
    ring
  have hraw :
      (∑ x, ∑ z, ∑ y, p (x, (z, y)) *
        Real.log ((conditionalRow p x (z, y) / margX (conditionalRow p x) z) /
          q x y)) = conditionalMutualInformation p +
        ∑ x, leftMarginal p x * klDef (margY (conditionalRow p x)) (q x) := by
    rw [hcmi, ← hD]
    simp_rw [hlog]
    simp only [mul_add, Finset.sum_add_distrib]
  linarith

private theorem margY_conditionalRow_apply {X Z Y : Type}
    [Fintype Z] [Fintype Y] [Nonempty Z] [Nonempty Y] (p : X × (Z × Y) → ℝ)
    (hp : ∀ a, 0 < p a) (x : X) (y : Y) :
    margY (conditionalRow p x) y =
      (∑ z, p (x, (z, y))) / leftMarginal p x := by
  have hx := leftMarginal_pos_of_positive p hp x
  rw [margY]
  simp_rw [conditionalRow, ite_eq_left hx]
  rw [← Finset.sum_div]

private theorem conditionalRow_div_margX {X Z Y : Type}
    [Fintype Z] [Fintype Y] [Nonempty Y] (p : X × (Z × Y) → ℝ)
    (hp : ∀ a, 0 < p a) (x : X) (a : Z × Y) :
    conditionalRow p x a / margX (conditionalRow p x) a.1 =
      p (x, a) / ∑ y, p (x, (a.1, y)) := by
  let : Nonempty Z := ⟨a.1⟩
  have hx := leftMarginal_pos_of_positive p hp x
  have hz : 0 < ∑ y, p (x, (a.1, y)) :=
    Finset.sum_pos (fun y _ => hp (x, (a.1, y))) Finset.univ_nonempty
  rw [conditionalRow, ite_eq_left hx]
  unfold margX
  rw [← Finset.sum_div]
  field_simp [hx.ne', hz.ne']

private theorem conditionalMutualInformation_eq_matched_log_ratio
    {X Z Y : Type} [Fintype X] [Fintype Z] [Fintype Y]
    (p : X × (Z × Y) → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1) :
    conditionalMutualInformation p =
      ∑ x, ∑ z, ∑ y, p (x, (z, y)) *
        Real.log ((conditionalRow p x (z, y) / margX (conditionalRow p x) z) /
          margY (conditionalRow p x) y) := by
  classical
  let : Nonempty (X × (Z × Y)) := nonempty_of_sum_eq_one p hsum
  let : Nonempty X := Nonempty.map (fun a : X × (Z × Y) => a.1) inferInstance
  let : Nonempty Z := Nonempty.map (fun a : X × (Z × Y) => a.2.1) inferInstance
  let : Nonempty Y := Nonempty.map (fun a : X × (Z × Y) => a.2.2) inferInstance
  have hmy (x : X) (y : Y) : 0 < margY (conditionalRow p x) y :=
    margY_pos (conditionalRow p x)
      (conditionalRow_pos_of_positive p hp x) y
  have hmysum (x : X) : ∑ y, margY (conditionalRow p x) y = 1 :=
    margY_sum_one (conditionalRow p x) (conditionalRow_sum_of_positive p hp x)
  rw [conditionalMutualInformation_eq_expected_log_ratio_sub_reference_kl
    p (fun x => margY (conditionalRow p x)) hp hsum hmy hmysum]
  have hzero : (∑ x, leftMarginal p x *
      klDef (margY (conditionalRow p x)) (margY (conditionalRow p x))) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [klDef_self_of_pos _ (hmy x), mul_zero]
  rw [hzero, sub_zero]

/-- The finite conditional mutual-information chain rule, with the prefix
latent obtained by summing out exactly `W` and the extension conditioned on
exactly `(X, Z)`. -/
theorem conditionalMutualInformation_pair_eq_prefix_add_extension
    {X Z W Y : Type} [Fintype X] [Fintype Z] [Fintype W] [Fintype Y]
    (p : X × ((Z × W) × Y) → ℝ)
    (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1) :
    conditionalMutualInformation p =
      conditionalMutualInformation
        (fun (x, (z, y)) => ∑ w, p (x, ((z, w), y))) +
      conditionalMutualInformation
        (fun ((x, z), (w, y)) => p (x, ((z, w), y))) := by
  classical
  let pPrefix : X × (Z × Y) → ℝ :=
    fun (x, (z, y)) => ∑ w, p (x, ((z, w), y))
  let pExtension : (X × Z) × (W × Y) → ℝ :=
    fun ((x, z), (w, y)) => p (x, ((z, w), y))
  change conditionalMutualInformation p =
    conditionalMutualInformation pPrefix + conditionalMutualInformation pExtension
  let : Nonempty (X × ((Z × W) × Y)) := nonempty_of_sum_eq_one p hsum
  let : Nonempty X := Nonempty.map (fun a : X × ((Z × W) × Y) => a.1) inferInstance
  let : Nonempty Z := Nonempty.map (fun a : X × ((Z × W) × Y) => a.2.1.1) inferInstance
  let : Nonempty W := Nonempty.map (fun a : X × ((Z × W) × Y) => a.2.1.2) inferInstance
  let : Nonempty Y := Nonempty.map (fun a : X × ((Z × W) × Y) => a.2.2) inferInstance
  have hpPrefix : ∀ a, 0 < pPrefix a := by
    rintro ⟨x, z, y⟩
    exact Finset.sum_pos (fun w _ => hp (x, ((z, w), y))) Finset.univ_nonempty
  have hsumPrefix : ∑ a, pPrefix a = 1 := by
    rw [← hsum]
    simp only [pPrefix, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    exact Finset.sum_comm
  have hpExtension : ∀ a, 0 < pExtension a := by
    rintro ⟨⟨x, z⟩, w, y⟩
    exact hp (x, ((z, w), y))
  have hsumExtension : ∑ a, pExtension a = 1 := by
    rw [← hsum]
    simp only [pExtension, Fintype.sum_prod_type]
  have hμPrefix (x : X) : leftMarginal pPrefix x = leftMarginal p x := by
    simp only [leftMarginal, pPrefix, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    exact Finset.sum_comm
  have hOutcomePrefix (x : X) (y : Y) :
      (∑ z, pPrefix (x, (z, y))) = ∑ a : Z × W, p (x, (a, y)) := by
    simp only [pPrefix, Fintype.sum_prod_type]
  have hY (x : X) (y : Y) :
      margY (conditionalRow pPrefix x) y = margY (conditionalRow p x) y := by
    rw [margY_conditionalRow_apply pPrefix hpPrefix,
      margY_conditionalRow_apply p hp, hOutcomePrefix, hμPrefix]
  have hYExt (x : X) (z : Z) (y : Y) :
      margY (conditionalRow pExtension (x, z)) y =
        conditionalRow pPrefix x (z, y) / margX (conditionalRow pPrefix x) z := by
    rw [margY_conditionalRow_apply pExtension hpExtension,
      conditionalRow_div_margX pPrefix hpPrefix]
    have hleft : leftMarginal pExtension (x, z) =
        ∑ w, ∑ y, p (x, ((z, w), y)) := by
      simp only [leftMarginal, pExtension, Fintype.sum_prod_type]
    have hmass : (∑ y, pPrefix (x, (z, y))) =
        ∑ w, ∑ y, p (x, ((z, w), y)) := by
      simp only [pPrefix]
      exact Finset.sum_comm
    rw [hleft, hmass]
  have hPost (x : X) (z : Z) (w : W) (y : Y) :
      conditionalRow p x ((z, w), y) / margX (conditionalRow p x) (z, w) =
        conditionalRow pExtension (x, z) (w, y) /
          margX (conditionalRow pExtension (x, z)) w := by
    rw [conditionalRow_div_margX p hp,
      conditionalRow_div_margX pExtension hpExtension]
  have hRatio (x : X) (z : Z) (w : W) (y : Y) :
      (conditionalRow p x ((z, w), y) / margX (conditionalRow p x) (z, w)) /
          margY (conditionalRow p x) y =
        ((conditionalRow pPrefix x (z, y) / margX (conditionalRow pPrefix x) z) /
          margY (conditionalRow pPrefix x) y) *
        ((conditionalRow pExtension (x, z) (w, y) /
            margX (conditionalRow pExtension (x, z)) w) /
          margY (conditionalRow pExtension (x, z)) y) := by
    rw [← hY x y, hYExt x z y, hPost x z w y]
    have hpostPrefix : 0 < conditionalRow pPrefix x (z, y) /
        margX (conditionalRow pPrefix x) z :=
      div_pos (conditionalRow_pos_of_positive pPrefix hpPrefix x (z, y))
        (margX_pos (conditionalRow pPrefix x)
          (conditionalRow_pos_of_positive pPrefix hpPrefix x) z)
    have houtPrefix : 0 < margY (conditionalRow pPrefix x) y :=
      margY_pos (conditionalRow pPrefix x)
        (conditionalRow_pos_of_positive pPrefix hpPrefix x) y
    have hpostExtension : 0 < conditionalRow pExtension (x, z) (w, y) /
        margX (conditionalRow pExtension (x, z)) w :=
      div_pos (conditionalRow_pos_of_positive pExtension hpExtension (x, z) (w, y))
        (margX_pos (conditionalRow pExtension (x, z))
          (conditionalRow_pos_of_positive pExtension hpExtension (x, z)) w)
    field_simp [hpostPrefix.ne', houtPrefix.ne', hpostExtension.ne',
      (conditionalRow_pos_of_positive pPrefix hpPrefix x (z, y)).ne',
      (margX_pos (conditionalRow pPrefix x)
        (conditionalRow_pos_of_positive pPrefix hpPrefix x) z).ne',
      (margX_pos (conditionalRow pExtension (x, z))
        (conditionalRow_pos_of_positive pExtension hpExtension (x, z)) w).ne']
  have hlog (x : X) (z : Z) (w : W) (y : Y) :
      Real.log ((conditionalRow p x ((z, w), y) /
          margX (conditionalRow p x) (z, w)) / margY (conditionalRow p x) y) =
        Real.log ((conditionalRow pPrefix x (z, y) /
            margX (conditionalRow pPrefix x) z) /
          margY (conditionalRow pPrefix x) y) +
        Real.log ((conditionalRow pExtension (x, z) (w, y) /
            margX (conditionalRow pExtension (x, z)) w) /
          margY (conditionalRow pExtension (x, z)) y) := by
    rw [hRatio x z w y]
    apply Real.log_mul
    · exact (div_pos
        (div_pos (conditionalRow_pos_of_positive pPrefix hpPrefix x (z, y))
          (margX_pos (conditionalRow pPrefix x)
            (conditionalRow_pos_of_positive pPrefix hpPrefix x) z))
        (margY_pos (conditionalRow pPrefix x)
          (conditionalRow_pos_of_positive pPrefix hpPrefix x) y)).ne'
    · exact (div_pos
        (div_pos (conditionalRow_pos_of_positive pExtension hpExtension (x, z) (w, y))
          (margX_pos (conditionalRow pExtension (x, z))
            (conditionalRow_pos_of_positive pExtension hpExtension (x, z)) w))
        (margY_pos (conditionalRow pExtension (x, z))
          (conditionalRow_pos_of_positive pExtension hpExtension (x, z)) y)).ne'
  have hPrefixExpanded : conditionalMutualInformation pPrefix =
      ∑ x, ∑ z, ∑ w, ∑ y, p (x, ((z, w), y)) *
        Real.log ((conditionalRow pPrefix x (z, y) /
            margX (conditionalRow pPrefix x) z) /
          margY (conditionalRow pPrefix x) y) := by
    rw [conditionalMutualInformation_eq_matched_log_ratio pPrefix hpPrefix hsumPrefix]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.sum_mul]
  have hExtensionExpanded : conditionalMutualInformation pExtension =
      ∑ x, ∑ z, ∑ w, ∑ y, p (x, ((z, w), y)) *
        Real.log ((conditionalRow pExtension (x, z) (w, y) /
            margX (conditionalRow pExtension (x, z)) w) /
          margY (conditionalRow pExtension (x, z)) y) := by
    rw [conditionalMutualInformation_eq_matched_log_ratio
      pExtension hpExtension hsumExtension]
    simp only [pExtension]
    rw [Fintype.sum_prod_type]
  calc
    conditionalMutualInformation p =
        (∑ x, ∑ z, ∑ w, ∑ y, p (x, ((z, w), y)) *
          Real.log ((conditionalRow pPrefix x (z, y) /
              margX (conditionalRow pPrefix x) z) /
            margY (conditionalRow pPrefix x) y)) +
        (∑ x, ∑ z, ∑ w, ∑ y, p (x, ((z, w), y)) *
          Real.log ((conditionalRow pExtension (x, z) (w, y) /
              margX (conditionalRow pExtension (x, z)) w) /
            margY (conditionalRow pExtension (x, z)) y)) := by
      rw [conditionalMutualInformation_eq_matched_log_ratio p hp hsum]
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro y _
      rw [hlog x z w y, mul_add]
    _ = conditionalMutualInformation pPrefix + conditionalMutualInformation pExtension := by
      rw [hPrefixExpanded, hExtensionExpanded]

end Hagi.Omni
