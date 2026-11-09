/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.CertifiedEstimator

/-!
# Confidence for a fixed finite family on a finite independent product

This module promotes the reviewed Cycle87 prototypes by composing the existing
one-sided Hoeffding certificate with the existing finite union bound.  The
family is fixed before the product sample is observed.  The result is a
probability calculation on the explicitly supplied independent product; it
does not assert that any external training or deployment sample is
representative.
-/

set_option relaxedAutoImplicit false

open Finset Real

namespace Hagi.Probability.FiniteFamilyConfidence

open Hagi.Probability

variable {V : Type} [Fintype V] [Nonempty V]

/-- Coordinate-average population loss under the exact finite product. -/
noncomputable def populationMean {n : ℕ} (p : Fin n → V → ℝ)
    (X : Fin n → V → ℝ) : ℝ :=
  (∑ i, coordMean p X i) / (n : ℝ)

/-- Empirical coordinate-average loss on one product sample. -/
noncomputable def empiricalMean {n : ℕ} (X : Fin n → V → ℝ)
    (ω : Fin n → V) : ℝ :=
  (∑ i, X i (ω i)) / (n : ℝ)

omit [Nonempty V] in
/-- Population means commute with multiplication by an arbitrary real
constant.  No probability or nonzero-sample assumption is needed for this
algebraic identity. -/
theorem populationMean_const_mul {V : Type} [Fintype V] {n : ℕ}
    (p : Fin n → V → ℝ) (L : Fin n → V → ℝ) (B : ℝ) :
    populationMean p (fun i t => B * L i t) = B * populationMean p L := by
  unfold populationMean
  calc
    (∑ i, coordMean p (fun j t => B * L j t) i) / (n : ℝ) =
        (∑ i, B * coordMean p L i) / (n : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      unfold coordMean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    _ = B * ((∑ i, coordMean p L i) / (n : ℝ)) := by
      rw [← Finset.mul_sum, mul_div_assoc]

omit [Nonempty V] in
/-- Empirical means commute with multiplication by an arbitrary real
constant, including when the finite sample is empty. -/
theorem empiricalMean_const_mul {V : Type} {n : ℕ}
    (L : Fin n → V → ℝ) (ω : Fin n → V) (B : ℝ) :
    empiricalMean (fun i t => B * L i t) ω = B * empiricalMean L ω := by
  unfold empiricalMean
  calc
    (∑ i, B * L i (ω i)) / (n : ℝ) =
        (B * ∑ i, L i (ω i)) / (n : ℝ) := by rw [Finset.mul_sum]
    _ = B * ((∑ i, L i (ω i)) / (n : ℝ)) := by rw [mul_div_assoc]

omit [Nonempty V] in
/-- A normalized mean comparison implies the corresponding comparison for
any genuine pointwise positive rescaling.  The raw loss is an explicit
argument, so the premise cannot silently substitute another loss. -/
theorem populationMean_le_empiricalMean_of_scale {V : Type} [Fintype V]
    {n : ℕ} (p : Fin n → V → ℝ) (normalized raw : Fin n → V → ℝ)
    (ω : Fin n → V) (B eps : ℝ) (hB : 0 < B)
    (hraw : ∀ i t, B * normalized i t = raw i t)
    (h : populationMean p normalized ≤ empiricalMean normalized ω + eps) :
    populationMean p raw ≤ empiricalMean raw ω + B * eps := by
  have hfun : (fun i t => B * normalized i t) = raw := by
    funext i t
    exact hraw i t
  rw [← hfun, populationMean_const_mul, empiricalMean_const_mul]
  calc
    B * populationMean p normalized ≤
        B * (empiricalMean normalized ω + eps) :=
      mul_le_mul_of_nonneg_left h hB.le
    _ = B * empiricalMean normalized ω + B * eps := by rw [mul_add]

omit [Nonempty V] in
/-- The centered-sum certificate implies the corresponding mean comparison. -/
theorem population_le_empirical_of_centered {n : ℕ} (p : Fin n → V → ℝ)
    (X : Fin n → V → ℝ) (ω : Fin n → V) (eps : ℝ) (hn : 0 < n)
    (h : -(n : ℝ) * eps ≤ centeredSum p X ω) :
    populationMean p X ≤ empiricalMean X ω + eps := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [populationMean, empiricalMean, div_le_iff₀ hnR]
  have heq : ((∑ i, X i (ω i)) / (n : ℝ) + eps) * (n : ℝ) =
      (∑ i, X i (ω i)) + eps * (n : ℝ) := by
    field_simp
  rw [heq]
  unfold centeredSum at h
  linarith

/-- Universal one-sided Hoeffding confidence for a fixed finite family of
normalized loss functions on an independent finite product. -/
theorem finite_family_upper_confidence {n : ℕ} {ι : Type} [Fintype ι]
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : ι → Fin n → V → ℝ)
    (hX : ∀ m i v, 0 ≤ X m i v ∧ X m i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) :
    1 - (Fintype.card ι : ℝ) * Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤
      prodPq p (fun ω => ∀ m,
        populationMean p (X m) ≤ empiricalMean (X m) ω + eps) := by
  classical
  have hA : ∀ m ∈ (Finset.univ : Finset ι),
      1 - Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤
        prodPq p (fun ω =>
          populationMean p (X m) ≤ empiricalMean (X m) ω + eps) := by
    intro m _hm
    refine le_trans (cert_lower p hp (X m) (hX m) hn eps heps) ?_
    exact prodPq_mono p hp _ _ (fun ω hω =>
      population_le_empirical_of_centered p (X m) ω eps hn hω)
  simpa using premises_union_confidence p hp (Finset.univ : Finset ι)
    (fun m ω => populationMean p (X m) ≤ empiricalMean (X m) ω + eps)
    (Real.exp (-2 * (n : ℝ) * eps ^ 2)) hA

/-- Two fresh independent, nonconstant labels with `P(1) = 3/4`. -/
noncomputable def twoModelP : Fin 2 → Fin 2 → ℝ :=
  fun _i v => if v = 0 then 1 / 4 else 3 / 4

/-- The explicit nonconstant label distribution is a probability system. -/
theorem twoModelP_prob : IsProbSys twoModelP := by
  intro i
  constructor
  · intro v
    fin_cases v <;> norm_num [twoModelP]
  · norm_num [twoModelP, Fin.sum_univ_two]

/-- Model zero predicts label one; model one predicts label zero. -/
def twoModelLoss : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun m _i v => if m = 0 then (v.val : ℝ) else 1 - (v.val : ℝ)

/-- Both numerical losses take values in the unit interval. -/
theorem twoModelLoss_unit :
    ∀ m i v, 0 ≤ twoModelLoss m i v ∧ twoModelLoss m i v ≤ 1 := by
  intro m i v
  fin_cases m <;> fin_cases v <;> norm_num [twoModelLoss]

/-- Simultaneous success of both mean comparisons at `eps = 1/2`. -/
noncomputable def twoModelGood (ω : Fin 2 → Fin 2) : Prop := by
  classical
  exact ∀ m, populationMean twoModelP (twoModelLoss m) ≤
    empiricalMean (twoModelLoss m) ω + 1 / 2

noncomputable instance : DecidablePred twoModelGood :=
  fun ω => Classical.propDecidable (twoModelGood ω)

/-- The only simultaneous failure is the all-zero sample. -/
theorem twoModelGood_iff (ω : Fin 2 → Fin 2) :
    twoModelGood ω ↔ ¬ (ω 0 = 0 ∧ ω 1 = 0) := by
  rcases (show ω 0 = 0 ∨ ω 0 = 1 by omega) with h0 | h0 <;>
    rcases (show ω 1 = 0 ∨ ω 1 = 1 by omega) with h1 | h1 <;>
    norm_num [twoModelGood, populationMean, empiricalMean, coordMean,
      twoModelLoss, twoModelP, Fin.sum_univ_two, Fin.forall_fin_two, h0, h1]

/-- The exact bad event has mass `1/16`, rather than being assigned mass by
an independence or `p = 1` assumption. -/
theorem twoModelBad_probability :
    prodPq twoModelP (fun ω => ω 0 = 0 ∧ ω 1 = 0) = 1 / 16 := by
  classical
  unfold prodPq prodE
  rw [Finset.sum_eq_single (fun _i => (0 : Fin 2))]
  · norm_num [prodDens, twoModelP, Fin.prod_univ_two]
  · intro ω _hω hne
    have hnot : ¬ (ω 0 = 0 ∧ ω 1 = 0) := by
      rintro ⟨h0, h1⟩
      apply hne
      funext i
      fin_cases i
      · exact h0
      · exact h1
    simp [hnot]
  · simp

/-- Exact nondegenerate good-event mass for the two independent labels. -/
theorem twoModelGood_probability : prodPq twoModelP twoModelGood = 15 / 16 := by
  classical
  have hbad : prodPq twoModelP (fun ω => ¬ twoModelGood ω) = 1 / 16 := by
    rw [prodPq_iff twoModelP (fun ω => ¬ twoModelGood ω)
      (fun ω => ω 0 = 0 ∧ ω 1 = 0)
      (fun ω => by simp only [twoModelGood_iff, not_not])]
    exact twoModelBad_probability
  have hcomp := prodPq_compl twoModelP twoModelP_prob twoModelGood
  linarith

/-- The generic theorem at two samples, two models, and `eps = 1/2`. -/
theorem twoModel_confidence :
    1 - 2 * Real.exp (-1) ≤ prodPq twoModelP twoModelGood := by
  rw [prodPq_iff twoModelP twoModelGood (fun ω =>
    ∀ m, populationMean twoModelP (twoModelLoss m) ≤
      empiricalMean (twoModelLoss m) ω + 1 / 2)
    (fun _ω => Iff.rfl)]
  have h := finite_family_upper_confidence twoModelP twoModelP_prob twoModelLoss
    twoModelLoss_unit (by norm_num : 0 < 2) (1 / 2) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The union-bound confidence is strictly positive in this finite test. -/
theorem twoModel_confidence_pos : 0 < 1 - 2 * Real.exp (-1) := by
  rw [Real.exp_neg]
  change 0 < 1 - 2 / Real.exp 1
  have he := Real.exp_one_gt_two
  have hp := Real.exp_pos 1
  apply sub_pos.mpr
  rw [div_lt_one hp]
  linarith

omit [Nonempty V] in
private theorem mean_abs_error_of_not_two_tails {n : ℕ}
    (p : Fin n → V → ℝ) (X : Fin n → V → ℝ)
    (ω : Fin n → V) (eps : ℝ) (hn : 0 < n)
    (hupper : ¬ (n : ℝ) * eps ≤ centeredSum p X ω)
    (hlower : ¬ centeredSum p X ω ≤ -(n : ℝ) * eps) :
    |populationMean p X - empiricalMean X ω| ≤ eps := by
  have hu : centeredSum p X ω < (n : ℝ) * eps := lt_of_not_ge hupper
  have hl : -(n : ℝ) * eps < centeredSum p X ω := lt_of_not_ge hlower
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have heq : centeredSum p X ω =
      (n : ℝ) * (empiricalMean X ω - populationMean p X) := by
    unfold centeredSum populationMean empiricalMean
    field_simp
  have hu' : empiricalMean X ω - populationMean p X < eps := by
    apply (mul_lt_mul_iff_of_pos_left hnR).mp
    rw [← heq]
    exact hu
  have hl' : -eps < empiricalMean X ω - populationMean p X := by
    apply (mul_lt_mul_iff_of_pos_left hnR).mp
    rw [← heq]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- Simultaneous two-sided Hoeffding confidence for a fixed finite family on
an independent finite product. The family may be empty and the confidence
need not be positive. -/
theorem finite_family_abs_error_confidence {n : ℕ} {ι : Type} [Fintype ι]
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : ι → Fin n → V → ℝ)
    (hX : ∀ m i v, 0 ≤ X m i v ∧ X m i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) :
    1 - 2 * (Fintype.card ι : ℝ) * Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤
      prodPq p (fun ω => ∀ m,
        |populationMean p (X m) - empiricalMean (X m) ω| ≤ eps) := by
  classical
  have hA : ∀ m ∈ (Finset.univ : Finset ι),
      1 - 2 * Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤
        prodPq p (fun ω =>
          |populationMean p (X m) - empiricalMean (X m) ω| ≤ eps) := by
    intro m _hm
    let Bad : (Fin n → V) → Prop := fun ω =>
      (n : ℝ) * eps ≤ centeredSum p (X m) ω ∨
        centeredSum p (X m) ω ≤ -(n : ℝ) * eps
    have htail := hoeffding_two_sided p hp (X m) (hX m) hn eps heps
    have hmono : prodPq p (fun ω => ¬ Bad ω) ≤
        prodPq p (fun ω =>
          |populationMean p (X m) - empiricalMean (X m) ω| ≤ eps) := by
      apply prodPq_mono p hp
      intro ω hω
      exact mean_abs_error_of_not_two_tails p (X m) ω eps hn
        (not_or.mp hω).1 (not_or.mp hω).2
    rw [prodPq_compl p hp Bad] at hmono
    linarith
  calc
    1 - 2 * (Fintype.card ι : ℝ) * Real.exp (-2 * (n : ℝ) * eps ^ 2) =
        1 - (Fintype.card ι : ℝ) *
          (2 * Real.exp (-2 * (n : ℝ) * eps ^ 2)) := by ring
    _ ≤ prodPq p (fun ω => ∀ m,
          |populationMean p (X m) - empiricalMean (X m) ω| ≤ eps) := by
      simpa only [Finset.card_univ, Finset.mem_univ, forall_const] using
        premises_union_confidence p hp (Finset.univ : Finset ι)
          (fun m ω =>
            |populationMean p (X m) - empiricalMean (X m) ω| ≤ eps)
          (2 * Real.exp (-2 * (n : ℝ) * eps ^ 2)) hA

/-- On the same simultaneous absolute-error good event, the empirical mean
gap is a lower bound on the population mean gap after subtracting `2 * eps`. -/
theorem finite_family_population_mean_gap_lower_confidence {n : ℕ} {ι : Type}
    [Fintype ι] (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : ι → Fin n → V → ℝ)
    (hX : ∀ m i v, 0 ≤ X m i v ∧ X m i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps)
    (baseline candidate : ι) :
    1 - 2 * (Fintype.card ι : ℝ) * Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤
      prodPq p (fun ω => empiricalMean (X baseline) ω -
        empiricalMean (X candidate) ω - 2 * eps ≤
          populationMean p (X baseline) - populationMean p (X candidate)) := by
  refine le_trans (finite_family_abs_error_confidence p hp X hX hn eps heps) ?_
  apply prodPq_mono p hp
  intro ω hω
  have hb := abs_le.mp (hω baseline)
  have hc := abs_le.mp (hω candidate)
  linarith

end Hagi.Probability.FiniteFamilyConfidence
