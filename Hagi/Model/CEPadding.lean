/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CECoupledShortcut
import Hagi.Model.CEConfidenceScale

/-!
# Arbitrary finite CE dimensions by exact zero padding

A `d`-dimensional feature row and parameter vector are null-extended to
`5 * paddedGroups d` coordinates.  The existing finite categorical CE,
residual-transpose optimizer, joint five-cell quantizer and packed codec are
then used unchanged.  `paddedLogicalBits` counts only the logical fixed-width
scale/trit payload, not ABI layout, RAM, native execution or training memory.
All fixed-codebook statements must fix the padded group count before sampling.
-/

set_option relaxedAutoImplicit false
set_option linter.style.openClassical false

open scoped Matrix

namespace Hagi.Model.CEPadding

open Hagi.Model
open Hagi.Model.CEGroupedScale
open Hagi.Model.CEJointScale
open Hagi.Model.CECoupledShortcut
open Hagi.Runtime

/-- Number of complete five-cell groups needed for `d` coordinates. -/
abbrev paddedGroups (d : ℕ) : ℕ := (d + 4) / 5

/-- The complete five-cell carrier containing the original coordinates. -/
abbrev paddedDimension (d : ℕ) : ℕ := 5 * paddedGroups d

/-- Exact logical 16-bit group-codec payload; this is not a RAM bound. -/
def paddedLogicalBits (d : ℕ) : ℕ := 16 * paddedGroups d

/-- Zero padding never drops an original coordinate. -/
theorem le_paddedDimension (d : ℕ) : d ≤ paddedDimension d := by
  unfold paddedDimension paddedGroups
  omega

/-- A complete multiple of five requires no additional group. -/
@[simp] theorem paddedDimension_five_mul (G : ℕ) :
    paddedDimension (5 * G) = 5 * G := by
  unfold paddedDimension paddedGroups
  congr 1
  omega

/-- The logical payload formula in the original ceiling-division notation. -/
theorem paddedLogicalBits_eq (d : ℕ) :
    paddedLogicalBits d = 16 * ((d + 4) / 5) := rfl

@[simp] theorem paddedDimension_zero : paddedDimension 0 = 0 := by
  norm_num [paddedDimension, paddedGroups]

@[simp] theorem paddedDimension_one : paddedDimension 1 = 5 := by
  norm_num [paddedDimension, paddedGroups]

@[simp] theorem paddedDimension_five : paddedDimension 5 = 5 := by
  norm_num [paddedDimension, paddedGroups]

@[simp] theorem paddedDimension_six : paddedDimension 6 = 10 := by
  norm_num [paddedDimension, paddedGroups]

@[simp] theorem paddedDimension_eleven : paddedDimension 11 = 15 := by
  norm_num [paddedDimension, paddedGroups]

/-- Null-extension of real parameters to the complete padded carrier. -/
def padVector {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (paddedDimension d)) :=
  WithLp.toLp 2 (fun j => if h : j.val < d then w.ofLp ⟨j.val, h⟩ else 0)

/-- Restriction of a full padded parameter vector to its original prefix. -/
def unpadVector {d : ℕ} (w : EuclideanSpace ℝ (Fin (paddedDimension d))) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => w.ofLp (Fin.castLE (le_paddedDimension d) i))

/-- Null-extension of every feature row, independently of the labels. -/
def padFeatures {V : Type} {d : ℕ} (X : Matrix V (Fin d) ℝ) :
    Matrix V (Fin (paddedDimension d)) ℝ :=
  fun v j => if h : j.val < d then X v ⟨j.val, h⟩ else 0

/-- An original padded parameter coordinate is exactly its input coordinate. -/
@[simp] theorem padVector_castLE {d : ℕ} (w : EuclideanSpace ℝ (Fin d))
    (i : Fin d) :
    (padVector w).ofLp (Fin.castLE (le_paddedDimension d) i) = w.ofLp i := by
  simp [padVector, i.isLt]

/-- Value form of originality, without identifying arbitrary finite types. -/
theorem padVector_of_lt {d : ℕ} (w : EuclideanSpace ℝ (Fin d))
    (j : Fin (paddedDimension d)) (hj : j.val < d) :
    (padVector w).ofLp j = w.ofLp ⟨j.val, hj⟩ := by
  simp [padVector, hj]

/-- Every coordinate beyond the original dimension is an exact real zero. -/
theorem padVector_of_not_lt {d : ℕ} (w : EuclideanSpace ℝ (Fin d))
    (j : Fin (paddedDimension d)) (hj : d ≤ j.val) :
    (padVector w).ofLp j = 0 := by
  simp [padVector, Nat.not_lt.mpr hj]

/-- Restriction is literal value-preserving `Fin.castLE` indexing. -/
@[simp] theorem unpadVector_apply {d : ℕ}
    (w : EuclideanSpace ℝ (Fin (paddedDimension d))) (i : Fin d) :
    (unpadVector w).ofLp i = w.ofLp (Fin.castLE (le_paddedDimension d) i) := rfl

/-- Original feature values survive padding coordinatewise. -/
@[simp] theorem padFeatures_castLE {V : Type} {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (v : V) (i : Fin d) :
    padFeatures X v (Fin.castLE (le_paddedDimension d) i) = X v i := by
  simp [padFeatures, i.isLt]

/-- Padded features vanish at every coordinate outside the original prefix. -/
theorem padFeatures_of_not_lt {V : Type} {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (v : V) (j : Fin (paddedDimension d))
    (hj : d ≤ j.val) : padFeatures X v j = 0 := by
  simp [padFeatures, Nat.not_lt.mpr hj]

/-- Restriction exactly undoes null-extension of parameters. -/
@[simp] theorem unpadVector_padVector {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) :
    unpadVector (padVector w) = w := by
  ext i
  simp

/-- Null-extension sends the zero parameter vector to zero. -/
@[simp] theorem padVector_zero {d : ℕ} :
    padVector (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
  ext j
  by_cases hj : j.val < d <;> simp [padVector]

/-- Null-extension sends the zero feature matrix to zero. -/
@[simp] theorem padFeatures_zero {V : Type} {d : ℕ} :
    padFeatures (0 : Matrix V (Fin d) ℝ) = 0 := by
  ext v j
  by_cases hj : j.val < d <;> simp [padFeatures]

/-- Null-extension identifies a finite sum with the sum over the original
prefix.  This one lemma is shared by logits, feature mass and alignment. -/
theorem sum_fin_null_extend {d n : ℕ} (h : d ≤ n) (f : Fin n → ℝ)
    (hf : ∀ j, d ≤ j.val → f j = 0) :
    (∑ j, f j) = ∑ i, f (Fin.castLE h i) := by
  classical
  symm
  calc
    (∑ i, f (Fin.castLE h i)) =
        ∑ j ∈ Finset.univ.map (Fin.castLEEmb h), f j := by
      exact (Finset.sum_map Finset.univ (Fin.castLEEmb h) f).symm
    _ = ∑ j, f j := by
      apply Finset.sum_subset (by simp)
      intro j _hj hnot
      apply hf j
      by_contra hj
      have hjlt : j.val < d := Nat.lt_of_not_ge hj
      apply hnot
      rw [Finset.mem_map]
      exact ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, Fin.ext rfl⟩

/-- Restricting an arbitrary full padded vector gives exactly the same
original-feature logits.  No five-cell or quantization premise is needed. -/
theorem ceLogits_unpadVector {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin (paddedDimension d))) (v : V) :
    ceLogits X (unpadVector θ) v = ceLogits (padFeatures X) θ v := by
  change (∑ i, X v i * θ.ofLp (Fin.castLE (le_paddedDimension d) i)) =
    ∑ j, padFeatures X v j * θ.ofLp j
  symm
  rw [sum_fin_null_extend (le_paddedDimension d)
    (fun j => padFeatures X v j * θ.ofLp j) (fun j hj => by
      rw [padFeatures_of_not_lt X v j hj, zero_mul])]
  exact Finset.sum_congr rfl (fun i _hi => by rw [padFeatures_castLE])

/-- Raw logits are unchanged by null-extension of both features and weights. -/
theorem ceLogits_padVector {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (v : V) :
    ceLogits X w v = ceLogits (padFeatures X) (padVector w) v := by
  have h := ceLogits_unpadVector X (padVector w) v
  rwa [unpadVector_padVector] at h

/-- Function-level raw logit preservation. -/
theorem ceLogits_padVector_fun {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    ceLogits X w = ceLogits (padFeatures X) (padVector w) := by
  funext v
  exact ceLogits_padVector X w v

/-- Actual categorical cross-entropy is preserved, with every label retained. -/
theorem ceOneHot_padVector {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (t : V) :
    Hagi.ceOneHot t (ceLogits X w) =
      Hagi.ceOneHot t (ceLogits (padFeatures X) (padVector w)) := by
  rw [ceLogits_padVector_fun]

/-- Absolute feature mass is invariant under null-extension. -/
theorem featureAbsSum_padFeatures {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) :
    featureAbsSum (padFeatures X) = featureAbsSum X := by
  unfold featureAbsSum
  apply Finset.sum_congr rfl
  intro v _hv
  rw [sum_fin_null_extend (le_paddedDimension d)
    (fun j => |padFeatures X v j|) (fun j hj => by
      rw [padFeatures_of_not_lt X v j hj, abs_zero])]
  exact Finset.sum_congr rfl (fun i _hi => by rw [padFeatures_castLE])

/-- The exact positive held-out CE normalizer is unchanged by padding. -/
theorem ceBound_padFeatures {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) :
    CEHeldout.ceBound (padFeatures X) = CEHeldout.ceBound X := by
  unfold CEHeldout.ceBound
  rw [featureAbsSum_padFeatures]

/-- Positivity of the transported normalizer, including zero features. -/
theorem ceBound_padFeatures_pos {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) : 0 < CEHeldout.ceBound (padFeatures X) := by
  rw [ceBound_padFeatures]
  exact CEHeldout.ceBound_pos X

/-- Null-extension is additive on the actual parameter carrier. -/
theorem padVector_add {d : ℕ} (w u : EuclideanSpace ℝ (Fin d)) :
    padVector (w + u) = padVector w + padVector u := by
  ext j
  by_cases hj : j.val < d <;> simp [padVector, hj]

/-- Null-extension commutes with real scalar multiplication. -/
theorem padVector_smul {d : ℕ} (eta : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    padVector (eta • w) = eta • padVector w := by
  ext j
  by_cases hj : j.val < d <;> simp [padVector, hj]

/-- The exact softmax residual is preserved by padding. -/
theorem ceResidual_padVector {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (t : V) :
    ceResidual (padFeatures X) (padVector w) t = ceResidual X w t := by
  unfold ceResidual
  rw [← ceLogits_padVector_fun]

/-- Residual-transpose agrees at every original coordinate. -/
theorem residualTranspose_padVector_castLE {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (t : V)
    (i : Fin d) :
    residualTranspose (padFeatures X) (padVector w) t
        (Fin.castLE (le_paddedDimension d) i) =
      residualTranspose X w t i := by
  unfold residualTranspose
  apply Finset.sum_congr rfl
  intro v _hv
  rw [ceResidual_padVector, padFeatures_castLE]

/-- Residual-transpose is exactly zero beyond the original coordinates. -/
theorem residualTranspose_padVector_of_not_lt {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (t : V)
    (j : Fin (paddedDimension d)) (hj : d ≤ j.val) :
    residualTranspose (padFeatures X) (padVector w) t j = 0 := by
  unfold residualTranspose
  apply Finset.sum_eq_zero
  intro v _hv
  rw [padFeatures_of_not_lt X v j hj, mul_zero]

/-- The actual negative residual-transpose direction is exactly padded. -/
theorem ceDirection_padVector {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (t : V) :
    ceDirection (padFeatures X) (padVector w) t =
      padVector (ceDirection X w t) := by
  ext j
  by_cases hj : j.val < d
  · let i : Fin d := ⟨j.val, hj⟩
    have hji : Fin.castLE (le_paddedDimension d) i = j := Fin.ext rfl
    rw [← hji, ceDirection_ofLp, padVector_castLE,
      residualTranspose_padVector_castLE, ceDirection_ofLp]
  · have hd : d ≤ j.val := Nat.le_of_not_gt hj
    rw [ceDirection_ofLp, residualTranspose_padVector_of_not_lt X w t j hd,
      padVector_of_not_lt _ _ hd, neg_zero]

/-- Exact preservation of squared residual-transpose alignment. -/
theorem ceAlignment_padVector {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (t : V) :
    ceAlignment (padFeatures X) (padVector w) t = ceAlignment X w t := by
  unfold ceAlignment
  rw [sum_fin_null_extend (le_paddedDimension d)
    (fun j => residualTranspose (padFeatures X) (padVector w) t j ^ 2)
    (fun j hj => by rw [residualTranspose_padVector_of_not_lt X w t j hj,
      zero_pow (by norm_num)])]
  exact Finset.sum_congr rfl (fun i _hi => by
    rw [residualTranspose_padVector_castLE])

/-- Every one-unit directional logit is preserved. -/
theorem ceLogits_ceDirection_padVector {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (t : V) (v : V) :
    ceLogits (padFeatures X) (ceDirection (padFeatures X) (padVector w) t) v =
      ceLogits X (ceDirection X w t) v := by
  rw [ceDirection_padVector]
  exact (ceLogits_padVector X (ceDirection X w t) v).symm

/-- The actual range bound is exactly the original computed quantity. -/
theorem ceStepRange_padVector {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (t : V) :
    ceStepRange (padFeatures X) (padVector w) t = ceStepRange X w t := by
  unfold ceStepRange
  congr 1
  apply Finset.sum_congr rfl
  intro v _hv
  rw [ceLogits_ceDirection_padVector]

/-- The actual safe-step rule is preserved, including its zero-range branch. -/
theorem safeStepSize_padVector {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (t : V) :
    safeStepSize (padFeatures X) (padVector w) t = safeStepSize X w t := by
  unfold safeStepSize
  rw [ceStepRange_padVector, ceAlignment_padVector]

/-- The parameter successor is padded exactly for every real step `eta`. -/
theorem ceNextParameters_padVector {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (t : V) (eta : ℝ) :
    ceNextParameters (padFeatures X) (padVector w) t eta =
      padVector (ceNextParameters X w t eta) := by
  unfold ceNextParameters
  rw [ceDirection_padVector, ← padVector_smul, ← padVector_add]

/-- Continuous-step CE is preserved for every real `eta`. -/
theorem ceOneHot_ceNextParameters_padVector {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (t : V) (eta : ℝ) :
    Hagi.ceOneHot t (ceLogits (padFeatures X)
        (ceNextParameters (padFeatures X) (padVector w) t eta)) =
      Hagi.ceOneHot t (ceLogits X (ceNextParameters X w t eta)) := by
  rw [ceNextParameters_padVector]
  exact (ceOneHot_padVector X (ceNextParameters X w t eta) t).symm

/-- Every finite positive dyadic level quantizes real zero to zero, with
saturation included; positivity is the actual existing level premise. -/
theorem qTern_dyadic_zero (k : DyadicScaleCode) :
    qTern (dyadicLevel k) 0 = 0 := by
  have hk := dyadicLevel_pos k
  norm_num [qTern, Hagi.Energy.roundTern, ne_of_gt hk]

/-- Joint five-cell quantization preserves every exact padded zero tail. -/
theorem jointParameters_padVector_of_not_lt {d : ℕ}
    (e : (Fin (paddedGroups d) × Fin 5) ≃ Fin (5 * paddedGroups d))
    (w : EuclideanSpace ℝ (Fin d))
    (scales : Fin (paddedGroups d) → DyadicScaleCode)
    (j : Fin (5 * paddedGroups d)) (hj : d ≤ j.val) :
    (jointParameters e (padVector w) scales).ofLp j = 0 := by
  unfold jointParameters
  change qTern (dyadicLevel (scales (e.symm j).1)) ((padVector w).ofLp j) = 0
  rw [padVector_of_not_lt w j hj, qTern_dyadic_zero]

/-- Restriction of any joint-quantized padded vector preserves original
logits; no zero-tail assumption on arbitrary raw coordinates is made. -/
theorem ceLogits_unpad_jointParameters {V : Type} [Fintype V] {d : ℕ}
    (e : (Fin (paddedGroups d) × Fin 5) ≃ Fin (5 * paddedGroups d))
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d))
    (scales : Fin (paddedGroups d) → DyadicScaleCode) (v : V) :
    ceLogits X (unpadVector (jointParameters e (padVector w) scales)) v =
      ceLogits (padFeatures X) (jointParameters e (padVector w) scales) v :=
  ceLogits_unpadVector X (jointParameters e (padVector w) scales) v

/-- Actual original-dimension CE of a restricted joint update equals the
padded CE to which the existing certified estimates apply. -/
theorem ceOneHot_unpad_jointParameters {V : Type} [Fintype V] {d : ℕ}
    (e : (Fin (paddedGroups d) × Fin 5) ≃ Fin (5 * paddedGroups d))
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d))
    (scales : Fin (paddedGroups d) → DyadicScaleCode) (t : V) :
    Hagi.ceOneHot t (ceLogits X
        (unpadVector (jointParameters e (padVector w) scales))) =
      Hagi.ceOneHot t (ceLogits (padFeatures X)
        (jointParameters e (padVector w) scales)) := by
  congr 1
  funext v
  exact ceLogits_unpad_jointParameters e X w scales v

/-- The existing separable joint certificate becomes a faithful bound on
the original `Fin d` carrier, not a bound between two padded raw vectors. -/
theorem ceOneHot_unpad_joint_le_blockPenalties {V : Type} [Fintype V]
    [Nonempty V] {d : ℕ}
    (e : (Fin (paddedGroups d) × Fin 5) ≃ Fin (5 * paddedGroups d))
    (X : Matrix V (Fin d) ℝ) (t : V) (w : EuclideanSpace ℝ (Fin d))
    (scales : Fin (paddedGroups d) → DyadicScaleCode) :
    Hagi.ceOneHot t (ceLogits X
        (unpadVector (jointParameters e (padVector w) scales))) ≤
      Hagi.ceOneHot t (ceLogits X w) +
        ∑ g, blockPenalty e (padFeatures X) (padVector w) g (scales g) := by
  calc
    Hagi.ceOneHot t (ceLogits X
        (unpadVector (jointParameters e (padVector w) scales))) =
        Hagi.ceOneHot t (ceLogits (padFeatures X)
          (jointParameters e (padVector w) scales)) :=
      ceOneHot_unpad_jointParameters e X w scales t
    _ ≤ Hagi.ceOneHot t (ceLogits (padFeatures X) (padVector w)) + _ :=
      ceOneHot_joint_le_blockPenalties e (padFeatures X) t (padVector w) scales
    _ = Hagi.ceOneHot t (ceLogits X w) + _ := by
      rw [← ceOneHot_padVector X w t]

/-- Strict original-dimension descent for the actual shortcut successor in
its zero-certificate branch.  Eligibility is evaluated at the padded version
of the original safe successor; the range premise stays on `Fin d`. -/
theorem shortcutScales_unpad_strict_descent_of_coupledPenalty_eq_zero
    {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (e : (Fin (paddedGroups d) × Fin 5) ≃ Fin (5 * paddedGroups d))
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (t : V) (fast : Fin (paddedGroups d) → DyadicScaleCode)
    (hr : 0 < ceStepRange X θ t)
    (h : coupledPenalty e (padFeatures X)
      (padVector (ceNextParameters X θ t (safeStepSize X θ t))) fast = 0) :
    Hagi.ceOneHot t (ceLogits X
      (unpadVector (jointParameters e
        (padVector (ceNextParameters X θ t (safeStepSize X θ t)))
        (shortcutScales e (padFeatures X)
          (padVector (ceNextParameters X θ t (safeStepSize X θ t))) fast)))) <
      Hagi.ceOneHot t (ceLogits X θ) := by
  have hrpad : 0 < ceStepRange (padFeatures X) (padVector θ) t := by
    rwa [ceStepRange_padVector]
  have hnext : ceNextParameters (padFeatures X) (padVector θ) t
      (safeStepSize (padFeatures X) (padVector θ) t) =
      padVector (ceNextParameters X θ t (safeStepSize X θ t)) := by
    rw [safeStepSize_padVector, ceNextParameters_padVector]
  have hpad : coupledPenalty e (padFeatures X)
      (ceNextParameters (padFeatures X) (padVector θ) t
        (safeStepSize (padFeatures X) (padVector θ) t)) fast = 0 := by
    rwa [hnext]
  have hstrict := shortcutScales_strict_descent_of_coupledPenalty_eq_zero
    e (padFeatures X) (padVector θ) t fast hrpad hpad
  rw [hnext] at hstrict
  calc
    Hagi.ceOneHot t (ceLogits X
      (unpadVector (jointParameters e
        (padVector (ceNextParameters X θ t (safeStepSize X θ t)))
        (shortcutScales e (padFeatures X)
          (padVector (ceNextParameters X θ t (safeStepSize X θ t))) fast)))) =
        Hagi.ceOneHot t (ceLogits (padFeatures X)
          (jointParameters e
            (padVector (ceNextParameters X θ t (safeStepSize X θ t)))
            (shortcutScales e (padFeatures X)
              (padVector (ceNextParameters X θ t (safeStepSize X θ t))) fast))) :=
      ceOneHot_unpad_jointParameters e X _ _ t
    _ < Hagi.ceOneHot t (ceLogits (padFeatures X) (padVector θ)) := hstrict
    _ = Hagi.ceOneHot t (ceLogits X θ) := (ceOneHot_padVector X θ t).symm

/-- The general eligible-shortcut route on the original carrier.  No
extra empirical/executive hypothesis or zero-fast-candidate is invented. -/
theorem shortcutScales_unpad_strict_descent_of_exists
    {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (e : (Fin (paddedGroups d) × Fin 5) ≃ Fin (5 * paddedGroups d))
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (t : V) (fast : Fin (paddedGroups d) → DyadicScaleCode)
    (hr : 0 < ceStepRange X θ t)
    (h : ∃ scales : Fin (paddedGroups d) → DyadicScaleCode,
      coupledPenalty e (padFeatures X)
        (padVector (ceNextParameters X θ t (safeStepSize X θ t))) scales <
        2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2) :
    Hagi.ceOneHot t (ceLogits X
      (unpadVector (jointParameters e
        (padVector (ceNextParameters X θ t (safeStepSize X θ t)))
        (shortcutScales e (padFeatures X)
          (padVector (ceNextParameters X θ t (safeStepSize X θ t))) fast)))) <
      Hagi.ceOneHot t (ceLogits X θ) := by
  have hrpad : 0 < ceStepRange (padFeatures X) (padVector θ) t := by
    rwa [ceStepRange_padVector]
  have hnext : ceNextParameters (padFeatures X) (padVector θ) t
      (safeStepSize (padFeatures X) (padVector θ) t) =
      padVector (ceNextParameters X θ t (safeStepSize X θ t)) := by
    rw [safeStepSize_padVector, ceNextParameters_padVector]
  have hpad : ∃ scales : Fin (paddedGroups d) → DyadicScaleCode,
      coupledPenalty e (padFeatures X)
        (ceNextParameters (padFeatures X) (padVector θ) t
          (safeStepSize (padFeatures X) (padVector θ) t)) scales <
        2 * (ceAlignment (padFeatures X) (padVector θ) t) ^ 2 /
          (ceStepRange (padFeatures X) (padVector θ) t) ^ 2 := by
    rw [hnext, ceAlignment_padVector, ceStepRange_padVector]
    exact h
  have hstrict := shortcutScales_strict_descent_of_exists
    e (padFeatures X) (padVector θ) t fast hrpad hpad
  rw [hnext] at hstrict
  calc
    Hagi.ceOneHot t (ceLogits X
      (unpadVector (jointParameters e
        (padVector (ceNextParameters X θ t (safeStepSize X θ t)))
        (shortcutScales e (padFeatures X)
          (padVector (ceNextParameters X θ t (safeStepSize X θ t))) fast)))) =
        Hagi.ceOneHot t (ceLogits (padFeatures X)
          (jointParameters e
            (padVector (ceNextParameters X θ t (safeStepSize X θ t)))
            (shortcutScales e (padFeatures X)
              (padVector (ceNextParameters X θ t (safeStepSize X θ t))) fast))) :=
      ceOneHot_unpad_jointParameters e X _ _ t
    _ < Hagi.ceOneHot t (ceLogits (padFeatures X) (padVector θ)) := hstrict
    _ = Hagi.ceOneHot t (ceLogits X θ) := (ceOneHot_padVector X θ t).symm

/-! ## Concrete noncanonical, saturated and degenerate checks -/

/-- Swap the two complete blocks before applying the existing canonical
product equivalence; no canonical indexing is assumed by the proofs above. -/
def swappedTwoBlockEquiv : (Fin 2 × Fin 5) ≃ Fin (5 * 2) :=
  (Equiv.prodCongr (Equiv.swap (0 : Fin 2) (1 : Fin 2))
    (Equiv.refl (Fin 5))).trans (canonicalBlockEquiv 2)

/-- Six original coordinates: both ends carry values far beyond either
chosen ternary saturation range. -/
def exampleSixParameters : EuclideanSpace ℝ (Fin 6) :=
  WithLp.toLp 2 (fun i =>
    if i = 0 then 100 else if i = 5 then -100 else 0)

/-- Two different legal dyadic levels, `1/128` and `1/64`. -/
def exampleSixScales : Fin 2 → DyadicScaleCode :=
  fun g => if g = 0 then 0 else 1

/-- A nonzero six-dimensional feature row shared by two labels. -/
def exampleSixFeatures : Matrix (Fin 2) (Fin 6) ℝ :=
  fun _v i => if i = 0 then 1 else 0

/-- The swap really exchanges the two block origins. -/
theorem swappedTwoBlockEquiv_origins :
    swappedTwoBlockEquiv (0, 0) = 5 ∧ swappedTwoBlockEquiv (1, 0) = 0 := by
  constructor <;> decide

/-- The explicit six-dimensional raw logit is numerically nonzero. -/
theorem exampleSix_logit :
    ceLogits exampleSixFeatures exampleSixParameters 0 = 100 := by
  norm_num [ceLogits, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    exampleSixFeatures, exampleSixParameters]

/-- Exact raw logit and CE preservation on the explicit six-dimensional data. -/
theorem exampleSix_raw_preservation :
    ceLogits exampleSixFeatures exampleSixParameters =
      ceLogits (padFeatures exampleSixFeatures)
        (padVector exampleSixParameters) ∧
    Hagi.ceOneHot 0 (ceLogits exampleSixFeatures exampleSixParameters) =
      Hagi.ceOneHot 0 (ceLogits (padFeatures exampleSixFeatures)
        (padVector exampleSixParameters)) :=
  ⟨ceLogits_padVector_fun exampleSixFeatures exampleSixParameters,
    ceOneHot_padVector exampleSixFeatures exampleSixParameters 0⟩

/-- The same explicit data preserves the actual continuous optimizer mechanics
for every real step, not merely a raw inference pass. -/
theorem exampleSix_continuous_preservation (eta : ℝ) :
    ceNextParameters (padFeatures exampleSixFeatures)
        (padVector exampleSixParameters) 0 eta =
      padVector (ceNextParameters exampleSixFeatures exampleSixParameters 0 eta) ∧
    safeStepSize (padFeatures exampleSixFeatures)
        (padVector exampleSixParameters) 0 =
      safeStepSize exampleSixFeatures exampleSixParameters 0 ∧
    ceStepRange (padFeatures exampleSixFeatures)
        (padVector exampleSixParameters) 0 =
      ceStepRange exampleSixFeatures exampleSixParameters 0 :=
  ⟨ceNextParameters_padVector exampleSixFeatures exampleSixParameters 0 eta,
    safeStepSize_padVector exampleSixFeatures exampleSixParameters 0,
    ceStepRange_padVector exampleSixFeatures exampleSixParameters 0⟩

/-- With swapped blocks and mixed scales, the actual joint parameter at the
upper end saturates exactly to `1/64`. -/
theorem exampleSix_joint_upper_saturation :
    (jointParameters swappedTwoBlockEquiv (padVector exampleSixParameters)
      exampleSixScales).ofLp (swappedTwoBlockEquiv (1, 0)) = 1 / 64 := by
  rw [jointParameters_own, (swappedTwoBlockEquiv_origins.2)]
  norm_num [exampleSixScales, exampleSixParameters, padVector,
    qTern, Hagi.Energy.roundTern, dyadicLevel]

/-- At the opposite swapped end, the actual joint parameter saturates to
`-1/128`; this uses a different level from the preceding example. -/
theorem exampleSix_joint_lower_saturation :
    (jointParameters swappedTwoBlockEquiv (padVector exampleSixParameters)
      exampleSixScales).ofLp (swappedTwoBlockEquiv (0, 0)) = -1 / 128 := by
  rw [jointParameters_own, (swappedTwoBlockEquiv_origins.1)]
  norm_num [exampleSixScales, exampleSixParameters, padVector,
    qTern, Hagi.Energy.roundTern, dyadicLevel]

/-- The last padded coordinate remains exactly zero after the same joint
quantization; saturation has not manufactured a nonzero tail value. -/
theorem exampleSix_joint_zero_tail :
    (jointParameters swappedTwoBlockEquiv (padVector exampleSixParameters)
      exampleSixScales).ofLp (9 : Fin (5 * 2)) = 0 := by
  unfold jointParameters
  change qTern (dyadicLevel (exampleSixScales
    (swappedTwoBlockEquiv.symm 9).1))
    ((padVector exampleSixParameters).ofLp 9) = 0
  rw [padVector_of_not_lt _ _ (by norm_num), qTern_dyadic_zero]

/-- Empty original feature rows have exactly zero logits. -/
theorem zeroDimension_logits_zero {V : Type} [Fintype V]
    (X : Matrix V (Fin 0) ℝ) (w : EuclideanSpace ℝ (Fin 0)) (v : V) :
    ceLogits X w v = 0 := by
  simp [ceLogits, Matrix.mulVec, dotProduct]

/-- A complete five-dimensional carrier uses the same raw CE after padding. -/
theorem fiveDimension_rawCE_preservation {V : Type} [Fintype V]
    (X : Matrix V (Fin 5) ℝ) (w : EuclideanSpace ℝ (Fin 5)) (t : V) :
    Hagi.ceOneHot t (ceLogits X w) =
      Hagi.ceOneHot t (ceLogits (padFeatures X) (padVector w)) :=
  ceOneHot_padVector X w t

/-- The existing finite-codebook normalized loss is exactly raw CE on the
original restricted carrier divided by the original positive normalizer. -/
theorem normalizedCE_unpad_jointParameters {V : Type} [Fintype V]
    [Nonempty V] {d : ℕ}
    (e : (Fin (paddedGroups d) × Fin 5) ≃ Fin (5 * paddedGroups d))
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d))
    (scales : Fin (paddedGroups d) → DyadicScaleCode) (t : V) :
    CEHeldout.normalizedCE e (padFeatures X)
        (CEHeldout.encodeJoint e (padVector w) scales) t =
      Hagi.ceOneHot t (ceLogits X
        (unpadVector (jointParameters e (padVector w) scales))) /
        CEHeldout.ceBound X := by
  unfold CEHeldout.normalizedCE
  rw [CEHeldout.decodeJoint_encodeJoint, ceBound_padFeatures,
    ← ceOneHot_unpad_jointParameters]

/-- The correctly oriented restricted raw-CE risk ratio lies in `[0,1]`. -/
theorem normalizedCE_unpad_mem_unit {V : Type} [Fintype V]
    [Nonempty V] {d : ℕ}
    (e : (Fin (paddedGroups d) × Fin 5) ≃ Fin (5 * paddedGroups d))
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d))
    (scales : Fin (paddedGroups d) → DyadicScaleCode) (t : V) :
    0 ≤ Hagi.ceOneHot t (ceLogits X
        (unpadVector (jointParameters e (padVector w) scales))) /
          CEHeldout.ceBound X ∧
      Hagi.ceOneHot t (ceLogits X
        (unpadVector (jointParameters e (padVector w) scales))) /
          CEHeldout.ceBound X ≤ 1 := by
  rw [← normalizedCE_unpad_jointParameters]
  exact CEHeldout.normalizedCE_mem_unit e (padFeatures X)
    (CEHeldout.encodeJoint e (padVector w) scales) t

end Hagi.Model.CEPadding
