/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEGroupedScale
import Hagi.Probability.FiniteFamilyConfidence

/-!
# Held-out confidence for the decoded finite CE codebook

The proofs are promoted from the reviewed Cycle87 prototype
`.tmp/Cycle87HeldoutAPI.lean`.  The codebook contains decoded finite
scale/trit codes, not arbitrary real raw weights, and is fixed before the
independent categorical labels are sampled.  Consequently every actual
`CEGroupedScale.jointParameters`, including one selected by a shortcut,
is covered without a union bound over an unbounded real family.

The normalizer is the reviewed prototype's
`1 + log |V| + 4 * featureMass X`, with `featureMass` replaced by the equal
existing definition `Hagi.Model.CEGroupedScale.featureAbsSum` from
`Hagi/Model/CEGroupedScale.lean`.  The elementary CE estimate uses
nonnegativity from the target term in log-sum-exp and, for `|z v| ≤ r`,
`CE(t,z) ≤ 2r + log |V|`.  Only CE divided by the positive normalizer is
claimed to lie in `[0,1]`; raw CE need not.  The confidence statement is a
conditional fixed-feature, finite-categorical-label probability calculation,
not a claim about representative IID external data or deployment accuracy.
No bit-width, entropy, or physical-storage assertion is made.
-/

set_option relaxedAutoImplicit false

open Finset Real

namespace Hagi.Model.CEHeldout

open scoped Matrix
open Hagi.Model Hagi.Runtime
open Hagi.Probability
open Hagi.Probability.FiniteFamilyConfidence

/-- Cross-entropy is nonnegative because the target exponential is one
term of the log-sum-exp normalizer. -/
theorem ceOneHot_nonneg {V : Type} [Fintype V] [Nonempty V]
    (t : V) (z : V → ℝ) : 0 ≤ Hagi.ceOneHot t z := by
  have hterm : Real.exp (z t) ≤ ∑ v, Real.exp (z v) :=
    Finset.single_le_sum (fun v _hv => (Real.exp_pos (z v)).le)
      (Finset.mem_univ t)
  have hlog := Real.log_le_log (Real.exp_pos (z t)) hterm
  rw [Real.log_exp] at hlog
  unfold Hagi.ceOneHot Hagi.Core.lse
  linarith

/-- A uniform absolute logit bound gives a finite-vocabulary CE bound. -/
theorem ceOneHot_le_two_add_log_card {V : Type} [Fintype V] [Nonempty V]
    (t : V) (z : V → ℝ) (r : ℝ) (hz : ∀ v, |z v| ≤ r) :
    Hagi.ceOneHot t z ≤ 2 * r + Real.log (Fintype.card V : ℝ) := by
  have hsum : (∑ v, Real.exp (z v)) ≤
      (Fintype.card V : ℝ) * Real.exp r := by
    calc
      (∑ v, Real.exp (z v)) ≤ ∑ _v : V, Real.exp r :=
        Finset.sum_le_sum (fun v _hv => Real.exp_le_exp.mpr
          ((le_abs_self (z v)).trans (hz v)))
      _ = (Fintype.card V : ℝ) * Real.exp r := by simp
  have hlog := Real.log_le_log (Hagi.Core.exp_sum_pos z) hsum
  rw [Real.log_mul (by exact_mod_cast (Fintype.card_ne_zero (α := V)))
    (Real.exp_ne_zero r), Real.log_exp] at hlog
  have ht : -r ≤ z t := by
    have h := hz t
    rw [abs_le] at h
    exact h.1
  unfold Hagi.ceOneHot Hagi.Core.lse
  linarith

/-- Finite logical codebook index for independently scaled five-trit blocks. -/
abbrev JointCode (G : ℕ) := Fin G → (DyadicScaleCode × (Fin 5 → Fin 3))

/-- Decode a complete finite codebook index to the actual parameter carrier. -/
noncomputable def decodeJoint {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (c : JointCode G) :
    EuclideanSpace ℝ (Fin (5 * G)) :=
  WithLp.toLp 2 (fun j =>
    ternaryValueDecode
      (dyadicLevel (c (e.symm j).1).1)
      ((c (e.symm j).1).2 (e.symm j).2))

/-- The exact finite code of any actual jointly quantized parameter vector. -/
noncomputable def encodeJoint {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → DyadicScaleCode) : JointCode G :=
  fun g => (scales g, fun i => ternaryValueEncode
    (dyadicLevel (scales g)) (w.ofLp (e (g, i))))

/-- Encoding an actual joint update and decoding it are identities. -/
theorem decodeJoint_encodeJoint {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → DyadicScaleCode) :
    decodeJoint e (encodeJoint e w scales) =
      CEGroupedScale.jointParameters e w scales := by
  ext j
  obtain ⟨⟨g, i⟩, rfl⟩ := e.surjective j
  simp [decodeJoint, encodeJoint, CEGroupedScale.jointParameters,
    ternaryValueDecode_encode]

/-- Every actual joint update, including every shortcut through its scales,
belongs to the predeclared decoded finite codebook. -/
theorem jointParameters_mem_codebook {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → DyadicScaleCode) :
    CEGroupedScale.jointParameters e w scales ∈ Set.range (decodeJoint e) :=
  ⟨encodeJoint e w scales, decodeJoint_encodeJoint e w scales⟩

/-- Exact cardinality of the decoded logical dictionary. -/
theorem card_jointCode (G : ℕ) : Fintype.card (JointCode G) = 61965 ^ G := by
  simp [JointCode]

/-- Every finite scale is below two; no unbounded real scale occurs. -/
theorem dyadicLevel_lt_two (k : DyadicScaleCode) : dyadicLevel k < 2 := by
  have hk : k.val + 1 ≤ 255 := by omega
  have hkR : (k.val : ℝ) + 1 ≤ 255 := by exact_mod_cast hk
  unfold dyadicLevel
  linarith

/-- Every decoded parameter has absolute value below two. -/
theorem abs_decodeJoint_lt_two {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (c : JointCode G)
    (j : Fin (5 * G)) : |(decodeJoint e c).ofLp j| < 2 := by
  let k := (c (e.symm j).1).1
  let trit := (c (e.symm j).1).2 (e.symm j).2
  change |ternaryValueDecode (dyadicLevel k) trit| < 2
  have ht : |((trit.val : ℝ) - 1)| ≤ 1 := by
    clear_value trit
    fin_cases trit <;> norm_num
  calc
    |ternaryValueDecode (dyadicLevel k) trit| =
        |dyadicLevel k| * |((trit.val : ℝ) - 1)| := by
      rw [ternaryValueDecode, abs_mul]
    _ ≤ |dyadicLevel k| * 1 :=
      mul_le_mul_of_nonneg_left ht (abs_nonneg _)
    _ = dyadicLevel k := by
      rw [mul_one, abs_of_pos (dyadicLevel_pos k)]
    _ < 2 := dyadicLevel_lt_two k

/-- The existing full absolute feature mass is nonnegative. -/
theorem featureAbsSum_nonneg {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) : 0 ≤ CEGroupedScale.featureAbsSum X := by
  exact Finset.sum_nonneg (fun _v _hv =>
    Finset.sum_nonneg (fun _j _hj => abs_nonneg _))

/-- Actual decoded logits have a uniform bound determined by the features. -/
theorem abs_ceLogits_decodeJoint_le {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (c : JointCode G) (v : V) :
    |ceLogits X (decodeJoint e c) v| ≤ 2 * CEGroupedScale.featureAbsSum X := by
  change |∑ j, X v j * (decodeJoint e c).ofLp j| ≤ _
  calc
    |∑ j, X v j * (decodeJoint e c).ofLp j| ≤
        ∑ j, |X v j * (decodeJoint e c).ofLp j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |X v j| * |(decodeJoint e c).ofLp j| := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [abs_mul]
    _ ≤ ∑ j : Fin (5 * G), |X v j| * 2 := by
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left (abs_decodeJoint_lt_two e c j).le
        (abs_nonneg _)
    _ = 2 * ∑ j, |X v j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ 2 * CEGroupedScale.featureAbsSum X := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      exact Finset.single_le_sum
        (fun u _hu => Finset.sum_nonneg (fun j _hj => abs_nonneg (X u j)))
        (Finset.mem_univ v)

/-- Raw decoded CE has the advertised logarithmic-plus-feature-mass bound. -/
theorem ceOneHot_decodeJoint_le_log_card_add {G : ℕ} {V : Type}
    [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (t : V) (c : JointCode G) :
    Hagi.ceOneHot t (ceLogits X (decodeJoint e c)) ≤
      Real.log (Fintype.card V : ℝ) + 4 * CEGroupedScale.featureAbsSum X := by
  have h := ceOneHot_le_two_add_log_card t
    (ceLogits X (decodeJoint e c)) (2 * CEGroupedScale.featureAbsSum X)
    (fun v => abs_ceLogits_decodeJoint_le e X c v)
  linarith

/-- Positive finite safe CE normalizer.  The extra one handles saturation,
a singleton vocabulary, and zero feature data without division by zero. -/
noncomputable def ceBound {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) : ℝ :=
  1 + Real.log (Fintype.card V : ℝ) + 4 * CEGroupedScale.featureAbsSum X

/-- The explicit CE normalizer is strictly positive. -/
theorem ceBound_pos {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) : 0 < ceBound X := by
  have hcard : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := V)
  have hlog : 0 ≤ Real.log (Fintype.card V : ℝ) := Real.log_nonneg hcard
  have hmass := featureAbsSum_nonneg X
  unfold ceBound
  linarith

/-- Decoded raw CE is at most the positive normalizer, not at most one. -/
theorem ceOneHot_decodeJoint_le_ceBound {G : ℕ} {V : Type}
    [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (t : V) (c : JointCode G) :
    Hagi.ceOneHot t (ceLogits X (decodeJoint e c)) ≤ ceBound X := by
  have h := ceOneHot_decodeJoint_le_log_card_add e X t c
  have hmass := featureAbsSum_nonneg X
  unfold ceBound
  linarith

/-- Normalized decoded CE used as the Hoeffding coordinate loss. -/
noncomputable def normalizedCE {G : ℕ} {V : Type} [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (c : JointCode G) (t : V) : ℝ :=
  Hagi.ceOneHot t (ceLogits X (decodeJoint e c)) / ceBound X

/-- Normalized decoded CE lies in `[0,1]`, including saturated and zero
feature cases, by the proved raw bounds and positivity of `ceBound`. -/
theorem normalizedCE_mem_unit {G : ℕ} {V : Type} [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (c : JointCode G) (t : V) :
    0 ≤ normalizedCE e X c t ∧ normalizedCE e X c t ≤ 1 := by
  have hpos := ceBound_pos X
  constructor
  · exact div_nonneg (ceOneHot_nonneg _ _) hpos.le
  · exact (div_le_one hpos).mpr (ceOneHot_decodeJoint_le_ceBound e X t c)

/-- Fixed-codebook fresh-label confidence for every decoded parameter at
once.  The finite class is fixed by `e` before sampling; no raw real weight
family is quantified over and no training-CE guarantee is asserted. -/
theorem codebook_upper_confidence {G n : ℕ} {V : Type}
    [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ)
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) :
    1 - (61965 ^ G : ℕ) * Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤
      prodPq p (fun ω => ∀ c : JointCode G,
        populationMean p (fun _i t => normalizedCE e X c t) ≤
          empiricalMean (fun _i t => normalizedCE e X c t) ω + eps) := by
  simpa [card_jointCode] using
    (finite_family_upper_confidence p hp
      (fun (c : JointCode G) (_i : Fin n) (t : V) => normalizedCE e X c t)
      (fun c _i t => normalizedCE_mem_unit e X c t) hn eps heps)

/-- The same fixed-codebook confidence seen through every actual joint scale
assignment for one fixed raw `w`.  In particular, a shortcut scale function
is covered by instantiating `scales`; raw real weights are not an additional
member of the finite class, and the dictionary is not grown after labels. -/
theorem joint_upper_confidence {G n : ℕ} {V : Type}
    [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) :
    1 - (61965 ^ G : ℕ) * Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤
      prodPq p (fun ω => ∀ scales : Fin G → DyadicScaleCode,
        populationMean p (fun _i t =>
          Hagi.ceOneHot t (ceLogits X (CEGroupedScale.jointParameters e w scales)) /
            ceBound X) ≤
          empiricalMean (fun _i t =>
            Hagi.ceOneHot t (ceLogits X (CEGroupedScale.jointParameters e w scales)) /
              ceBound X) ω + eps) := by
  refine le_trans (codebook_upper_confidence e X p hp hn eps heps) ?_
  apply prodPq_mono p hp
  intro ω hω scales
  have h := hω (encodeJoint e w scales)
  unfold normalizedCE at h
  rw [decodeJoint_encodeJoint e w scales] at h
  exact h

/-- Fixed-codebook fresh-label lower confidence for a population mean gap.
Both normalized losses use the same finite dictionary fixed before sampling;
the two codes are selected from that dictionary, not from observed labels. -/
theorem codebook_population_mean_gap_lower_confidence {G n : ℕ} {V : Type}
    [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ)
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps)
    (baseline candidate : JointCode G) :
    1 - 2 * (61965 ^ G : ℕ) * Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤
      prodPq p (fun ω => empiricalMean (fun _i t => normalizedCE e X baseline t) ω -
        empiricalMean (fun _i t => normalizedCE e X candidate t) ω - 2 * eps ≤
          populationMean p (fun _i t => normalizedCE e X baseline t) -
            populationMean p (fun _i t => normalizedCE e X candidate t)) := by
  simpa [card_jointCode] using
    (finite_family_population_mean_gap_lower_confidence p hp
      (fun (c : JointCode G) (_i : Fin n) (t : V) => normalizedCE e X c t)
      (fun c _i t => normalizedCE_mem_unit e X c t) hn eps heps baseline candidate)

/-- Raw-CE lower confidence after sample-adaptive selection inside the
fixed decoded codebook.  Only the two code indices may depend on the
observed product sample; the codebook, features, decoder, coordinate laws,
and normalized loss family remain fixed.  The proof transports the generic
selected finite-family theorem at radius `eps / ceBound X`. -/
theorem codebook_raw_selected_population_mean_gap_lower_confidence {G n : ℕ}
    {V : Type} [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ)
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps)
    (baseline candidate : (Fin n → V) → JointCode G) :
    1 - 2 * (61965 ^ G : ℕ) * Real.exp (-2 * (n : ℝ) * (eps / ceBound X) ^ 2) ≤
      prodPq p (fun ω =>
        empiricalMean (fun _i t =>
          Hagi.ceOneHot t (ceLogits X (decodeJoint e (baseline ω)))) ω -
        empiricalMean (fun _i t =>
          Hagi.ceOneHot t (ceLogits X (decodeJoint e (candidate ω)))) ω - 2 * eps ≤
          populationMean p (fun _i t =>
            Hagi.ceOneHot t (ceLogits X (decodeJoint e (baseline ω)))) -
          populationMean p (fun _i t =>
            Hagi.ceOneHot t (ceLogits X (decodeJoint e (candidate ω))))) := by
  classical
  have hB : 0 < ceBound X := ceBound_pos X
  have hnormalized :
      1 - 2 * (61965 ^ G : ℕ) *
          Real.exp (-2 * (n : ℝ) * (eps / ceBound X) ^ 2) ≤
        prodPq p (fun ω =>
          empiricalMean (fun _i t => normalizedCE e X (baseline ω) t) ω -
            empiricalMean (fun _i t => normalizedCE e X (candidate ω) t) ω -
              2 * (eps / ceBound X) ≤
            populationMean p (fun _i t => normalizedCE e X (baseline ω) t) -
              populationMean p (fun _i t => normalizedCE e X (candidate ω) t)) := by
    simpa [card_jointCode] using
      (finite_family_selected_population_mean_gap_lower_confidence p hp
        (fun (c : JointCode G) (_i : Fin n) (t : V) => normalizedCE e X c t)
        (fun c _i t => normalizedCE_mem_unit e X c t) hn
        (eps / ceBound X) (div_pos heps hB) baseline candidate)
  refine le_trans hnormalized ?_
  apply prodPq_mono p hp
  intro ω hω
  let RawBase : Fin n → V → ℝ := fun _i t =>
    Hagi.ceOneHot t (ceLogits X (decodeJoint e (baseline ω)))
  let RawCandidate : Fin n → V → ℝ := fun _i t =>
    Hagi.ceOneHot t (ceLogits X (decodeJoint e (candidate ω)))
  let NormBase : Fin n → V → ℝ := fun _i t => normalizedCE e X (baseline ω) t
  let NormCandidate : Fin n → V → ℝ := fun _i t =>
    normalizedCE e X (candidate ω) t
  change empiricalMean NormBase ω - empiricalMean NormCandidate ω -
    2 * (eps / ceBound X) ≤
      populationMean p NormBase - populationMean p NormCandidate at hω
  change empiricalMean RawBase ω - empiricalMean RawCandidate ω - 2 * eps ≤
    populationMean p RawBase - populationMean p RawCandidate
  have hRawBase : (fun i t => ceBound X * NormBase i t) = RawBase := by
    funext i t
    dsimp [NormBase, RawBase, normalizedCE]
    exact mul_div_cancel₀ _ (ne_of_gt hB)
  have hRawCandidate : (fun i t => ceBound X * NormCandidate i t) = RawCandidate := by
    funext i t
    dsimp [NormCandidate, RawCandidate, normalizedCE]
    exact mul_div_cancel₀ _ (ne_of_gt hB)
  have hEB := Hagi.Probability.FiniteFamilyConfidence.empiricalMean_const_mul
    NormBase ω (ceBound X)
  have hEC := Hagi.Probability.FiniteFamilyConfidence.empiricalMean_const_mul
    NormCandidate ω (ceBound X)
  have hPB := Hagi.Probability.FiniteFamilyConfidence.populationMean_const_mul
    p NormBase (ceBound X)
  have hPC := Hagi.Probability.FiniteFamilyConfidence.populationMean_const_mul
    p NormCandidate (ceBound X)
  rw [← hRawBase, ← hRawCandidate, hEB, hEC, hPB, hPC]
  calc
    ceBound X * empiricalMean NormBase ω -
        ceBound X * empiricalMean NormCandidate ω - 2 * eps =
      ceBound X * (empiricalMean NormBase ω - empiricalMean NormCandidate ω -
        2 * (eps / ceBound X)) := by
      field_simp [ne_of_gt hB]
    _ ≤ ceBound X *
        (populationMean p NormBase - populationMean p NormCandidate) :=
      mul_le_mul_of_nonneg_left hω hB.le
    _ = ceBound X * populationMean p NormBase -
        ceBound X * populationMean p NormCandidate := by ring

/-- For one fixed linear head, cross-entropy at the midpoint of two
parameter vectors is at most the mean of their endpoint cross-entropies.
The inverse-scalar notation is the EuclideanSpace midpoint operation.
This is a non-strict pointwise bound for the stated features only. -/
theorem ceOneHot_mean_ceLogits_le {V : Type} [Fintype V] [Nonempty V]
    {d : ℕ} (X : Matrix V (Fin d) ℝ)
    (w1 w2 : EuclideanSpace ℝ (Fin d)) (t : V) :
    Hagi.ceOneHot t (ceLogits X ((2 : ℝ)⁻¹ • (w1 + w2))) ≤
      (Hagi.ceOneHot t (ceLogits X w1) +
        Hagi.ceOneHot t (ceLogits X w2)) / 2 := by
  have hlogits : ceLogits X ((2 : ℝ)⁻¹ • (w1 + w2)) =
      (ceLogits X w1 + ceLogits X w2) / 2 := by
    change X *ᵥ ((2 : ℝ)⁻¹ • (w1.ofLp + w2.ofLp)) =
      (X *ᵥ w1.ofLp + X *ᵥ w2.ofLp) / 2
    rw [Matrix.mulVec_smul, Matrix.mulVec_add]
    ext v
    change (2 : ℝ)⁻¹ * ((X *ᵥ w1.ofLp) v + (X *ᵥ w2.ofLp) v) =
      ((X *ᵥ w1.ofLp) v + (X *ᵥ w2.ofLp) v) / 2
    ring
  rw [hlogits]
  exact Hagi.Core.ensemble_ce_le_mean t (ceLogits X w1) (ceLogits X w2)

end Hagi.Model.CEHeldout
