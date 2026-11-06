/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEDescent
import Hagi.Runtime.TernaryExact

/-!
# Quality bounds for ternary-quantized cross-entropy steps

For a finite nonempty class carrier, one-hot cross-entropy changes by at
most twice a uniform bound on the logit change.  Combining this with the
actual saturating ternary quantizer gives two certificates: an observed
logit-displacement penalty and a structural penalty using the proved
squared quantization-error budget.  Their minimum is used only after
both branches have been certified.

These are finite post-training quality bounds.  They make no claim about
metadata size, validation accuracy, generalization, or an optimal model
architecture.
-/

set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Model.CEQuantized

/-- One-hot cross-entropy is `2`-Lipschitz for a uniform bound on the
change of all logits.  The proof uses only exp/log monotonicity and the
target coordinate. -/
theorem ceOneHot_le_of_abs_sub_le {V : Type} [Fintype V] [Nonempty V]
    (t : V) (z y : V → ℝ) (r : ℝ)
    (h : ∀ v, |z v - y v| ≤ r) :
    Hagi.ceOneHot t z ≤ Hagi.ceOneHot t y + 2 * r := by
  have hzy : ∀ v, z v ≤ y v + r := by
    intro v
    have habs := h v
    have hself := le_abs_self (z v - y v)
    linarith
  have hexp : (∑ v, Real.exp (z v)) ≤ ∑ v, Real.exp (y v + r) := by
    apply Finset.sum_le_sum
    intro v _hv
    exact Real.exp_le_exp.mpr (hzy v)
  have hsum : (∑ v, Real.exp (y v + r)) =
      Real.exp r * ∑ v, Real.exp (y v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    rw [Real.exp_add, mul_comm]
  have hlog := Real.log_le_log (Hagi.Core.exp_sum_pos z) hexp
  rw [hsum, Real.log_mul (Real.exp_ne_zero r)
    (ne_of_gt (Hagi.Core.exp_sum_pos y)), Real.log_exp] at hlog
  have ht : y t - z t ≤ r := by
    have habs := h t
    rw [abs_sub_comm] at habs
    have hself := le_abs_self (y t - z t)
    linarith
  unfold Hagi.ceOneHot Hagi.Core.lse
  linarith

/-- Coordinatewise application of the actual saturating ternary
quantizer on the Euclidean parameter carrier. -/
noncomputable def ternaryCEParameters {d : ℕ} (s : ℝ)
    (w : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => Hagi.Runtime.qTern s (w.ofLp j))

/-- The observed penalty is twice the actual sum of absolute logit
changes after quantizing `w`. -/
noncomputable def ceQuantObservedPenalty {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (s : ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 * ∑ v, |ceLogits X (ternaryCEParameters s w) v - ceLogits X w v|

/-- The structural penalty combines the finite absolute feature sum with
the saturation-aware squared-error budget for the actual quantizer. -/
noncomputable def ceQuantStructuralPenalty {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (s : ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 * (∑ v, ∑ j, |X v j|) *
    Real.sqrt ((d : ℝ) * (s / 2) ^ 2 + Hagi.Runtime.satTail s w.ofLp)

/-- The observed logit-displacement certificate, valid for every real
scale (including zero and negative scales). -/
theorem ceOneHot_ternary_le_observed {V : Type} [Fintype V] [Nonempty V]
    {d : ℕ} (X : Matrix V (Fin d) ℝ) (t : V) (s : ℝ)
    (w : EuclideanSpace ℝ (Fin d)) :
    Hagi.ceOneHot t (ceLogits X (ternaryCEParameters s w)) ≤
      Hagi.ceOneHot t (ceLogits X w) + ceQuantObservedPenalty X s w := by
  unfold ceQuantObservedPenalty
  apply ceOneHot_le_of_abs_sub_le
  intro v
  exact Finset.single_le_sum
    (fun u _hu => abs_nonneg
      (ceLogits X (ternaryCEParameters s w) u - ceLogits X w u))
    (Finset.mem_univ v)

/-- Each coordinate of the round-trip error is bounded by the common
square-root budget.  The orientation here is intentionally `w - qTern`. -/
private theorem abs_qTern_sub_le_sqrt_sum {d : ℕ} (s : ℝ)
    (w : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    |Hagi.Runtime.qTern s (w.ofLp j) - w.ofLp j| ≤
      Real.sqrt (∑ k, (w.ofLp k - Hagi.Runtime.qTern s (w.ofLp k)) ^ 2) := by
  rw [abs_sub_comm, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum
    (fun k _hk => sq_nonneg
      (w.ofLp k - Hagi.Runtime.qTern s (w.ofLp k)))
    (Finset.mem_univ j)

/-- The feature-error algebra for one logit.  No matrix norm or in-range
premise is introduced. -/
private theorem abs_ceLogits_ternary_sub_le {V : Type} [Fintype V]
    {d : ℕ} (X : Matrix V (Fin d) ℝ) (s : ℝ)
    (w : EuclideanSpace ℝ (Fin d)) (v : V) :
    |ceLogits X (ternaryCEParameters s w) v - ceLogits X w v| ≤
      (∑ u, ∑ j, |X u j|) *
        Real.sqrt (∑ j, (w.ofLp j - Hagi.Runtime.qTern s (w.ofLp j)) ^ 2) := by
  have hdiff :
      ceLogits X (ternaryCEParameters s w) v - ceLogits X w v =
        ∑ j, X v j * (Hagi.Runtime.qTern s (w.ofLp j) - w.ofLp j) := by
    change (∑ j, X v j * Hagi.Runtime.qTern s (w.ofLp j)) -
      (∑ j, X v j * w.ofLp j) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hA : (∑ j, |X v j|) ≤ ∑ u, ∑ j, |X u j| := by
    exact Finset.single_le_sum
      (fun u _hu => Finset.sum_nonneg (fun j _hj => abs_nonneg (X u j)))
      (Finset.mem_univ v)
  rw [hdiff]
  calc
    |∑ j, X v j * (Hagi.Runtime.qTern s (w.ofLp j) - w.ofLp j)| ≤
        ∑ j, |X v j * (Hagi.Runtime.qTern s (w.ofLp j) - w.ofLp j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |X v j| * |Hagi.Runtime.qTern s (w.ofLp j) - w.ofLp j| := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [abs_mul]
    _ ≤ ∑ j, |X v j| *
        Real.sqrt (∑ k, (w.ofLp k - Hagi.Runtime.qTern s (w.ofLp k)) ^ 2) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left (abs_qTern_sub_le_sqrt_sum s w j)
        (abs_nonneg (X v j))
    _ = (∑ j, |X v j|) *
        Real.sqrt (∑ k, (w.ofLp k - Hagi.Runtime.qTern s (w.ofLp k)) ^ 2) := by
      rw [Finset.sum_mul]
    _ ≤ (∑ u, ∑ j, |X u j|) *
        Real.sqrt (∑ k, (w.ofLp k - Hagi.Runtime.qTern s (w.ofLp k)) ^ 2) :=
      mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _)

/-- The saturation-aware structural certificate.  Its only quantizer
premise is positive scale; saturation is accounted for by `satTail`. -/
theorem ceOneHot_ternary_le_structural {V : Type} [Fintype V] [Nonempty V]
    {d : ℕ} (X : Matrix V (Fin d) ℝ) (t : V) (s : ℝ)
    (w : EuclideanSpace ℝ (Fin d)) (hs : 0 < s) :
    Hagi.ceOneHot t (ceLogits X (ternaryCEParameters s w)) ≤
      Hagi.ceOneHot t (ceLogits X w) + ceQuantStructuralPenalty X s w := by
  have hA : 0 ≤ ∑ u, ∑ j, |X u j| :=
    Finset.sum_nonneg (fun u _hu => Finset.sum_nonneg
      (fun j _hj => abs_nonneg (X u j)))
  unfold ceQuantStructuralPenalty
  rw [mul_assoc]
  apply ceOneHot_le_of_abs_sub_le
  intro v
  exact (abs_ceLogits_ternary_sub_le X s w v).trans
    (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (Hagi.Runtime.ternary_split_le s hs w.ofLp)) hA)

/-- The certified penalty is the sharper of the two proved upper bounds. -/
noncomputable def ceQuantPenalty {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (s : ℝ) : ℝ :=
  min (ceQuantObservedPenalty X s w) (ceQuantStructuralPenalty X s w)

/-- The minimum of the observed and structural penalties also bounds the
actual quantized cross-entropy increase. -/
theorem ceOneHot_ternary_le_ceQuantPenalty {V : Type} [Fintype V]
    [Nonempty V] {d : ℕ} (X : Matrix V (Fin d) ℝ) (t : V) (s : ℝ)
    (w : EuclideanSpace ℝ (Fin d)) (hs : 0 < s) :
    Hagi.ceOneHot t (ceLogits X (ternaryCEParameters s w)) ≤
      Hagi.ceOneHot t (ceLogits X w) + ceQuantPenalty X w s := by
  by_cases h : ceQuantObservedPenalty X s w ≤ ceQuantStructuralPenalty X s w
  · rw [ceQuantPenalty, min_eq_left h]
    exact ceOneHot_ternary_le_observed X t s w
  · have h' : ceQuantStructuralPenalty X s w ≤ ceQuantObservedPenalty X s w :=
      le_of_not_ge h
    rw [ceQuantPenalty, min_eq_right h']
    exact ceOneHot_ternary_le_structural X t s w hs

/-- If the certified quantization penalty is smaller than the exact
Cycle81 safe-step residual, actual ternary quantization preserves strict
cross-entropy descent. -/
theorem ceOneHot_ternary_safeStep_lt {V : Type} [Fintype V] [Nonempty V]
    {d : ℕ} (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (t : V) (s : ℝ) (hs : 0 < s) (hr : 0 < ceStepRange X θ t)
    (hp : ceQuantPenalty X
        (ceNextParameters X θ t (safeStepSize X θ t)) s <
      2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2) :
    Hagi.ceOneHot t (ceLogits X (ternaryCEParameters s
      (ceNextParameters X θ t (safeStepSize X θ t)))) <
      Hagi.ceOneHot t (ceLogits X θ) := by
  have hquant := ceOneHot_ternary_le_ceQuantPenalty X t s
    (ceNextParameters X θ t (safeStepSize X θ t)) hs
  have hsafe := ceOneHot_safeStep_le_residual X θ t hr
  change Hagi.ceOneHot t (ceLogits X
    (ceNextParameters X θ t (safeStepSize X θ t))) ≤ _ at hsafe
  linarith

/-- Zero features make both penalties, and hence their minimum, vanish.
This also covers the zero-dimensional feature carrier. -/
theorem ceQuantPenalty_zeroMatrix {V : Type} [Fintype V] {d : ℕ}
    (s : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    ceQuantPenalty (0 : Matrix V (Fin d) ℝ) w s = 0 := by
  have hobs : ceQuantObservedPenalty (0 : Matrix V (Fin d) ℝ) s w = 0 := by
    simp [ceQuantObservedPenalty, ceLogits, Matrix.mulVec, dotProduct]
  have hstruct : 0 ≤ ceQuantStructuralPenalty (0 : Matrix V (Fin d) ℝ) s w := by
    unfold ceQuantStructuralPenalty
    positivity
  rw [ceQuantPenalty, hobs, min_eq_left hstruct]

/-- The two-class identity extended by three intentionally zero feature
columns.  This is a small nondegenerate test carrier, not a sparsity or
architecture-optimality claim. -/
def ceQuantWitnessFeatures : Matrix (Fin 2) (Fin 5) ℝ :=
  fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

/-- The witness has the same nonzero range as the two-class identity. -/
theorem ceQuantWitness_range :
    ceStepRange ceQuantWitnessFeatures 0 0 = 2 := by
  norm_num [ceStepRange, ceAlignment, residualTranspose, ceResidual,
    ceDirection, ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef,
    ceQuantWitnessFeatures, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Fin.sum_univ_succ]

/-- The witness has nonzero alignment `1/2`. -/
theorem ceQuantWitness_alignment :
    ceAlignment ceQuantWitnessFeatures 0 0 = 1 / 2 := by
  norm_num [ceAlignment, residualTranspose, ceResidual, ceLogits,
    Hagi.Energy.smax, Hagi.Prelude.softDef, ceQuantWitnessFeatures,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_succ]

/-- The actual Cycle81 safe successor, derived by expanding
`ceNextParameters` and `safeStepSize`, is the stated raw vector. -/
theorem ceQuantWitness_safeSuccessor :
    (ceNextParameters ceQuantWitnessFeatures 0 0
      (safeStepSize ceQuantWitnessFeatures 0 0)).ofLp =
      ![1 / 4, -1 / 4, 0, 0, 0] := by
  have heta : safeStepSize ceQuantWitnessFeatures 0 0 = 1 / 2 := by
    rw [safeStepSize, ite_eq_right (by rw [ceQuantWitness_range]; norm_num),
      ceQuantWitness_alignment, ceQuantWitness_range]
    norm_num
  rw [heta]
  ext j
  fin_cases j <;>
    norm_num [ceNextParameters, ceDirection, residualTranspose, ceResidual,
      ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef,
      ceQuantWitnessFeatures, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Fin.sum_univ_succ]

/-- At scale `1/4` the actual saturating quantizer fixes every coordinate
of the computed safe successor. -/
theorem ceQuantWitness_ternaryCEParameters :
    ternaryCEParameters (1 / 4)
      (ceNextParameters ceQuantWitnessFeatures 0 0
        (safeStepSize ceQuantWitnessFeatures 0 0)) =
      ceNextParameters ceQuantWitnessFeatures 0 0
        (safeStepSize ceQuantWitnessFeatures 0 0) := by
  ext j
  change Hagi.Runtime.qTern (1 / 4)
    ((ceNextParameters ceQuantWitnessFeatures 0 0
      (safeStepSize ceQuantWitnessFeatures 0 0)).ofLp j) = _
  rw [ceQuantWitness_safeSuccessor]
  fin_cases j <;> norm_num [Hagi.Runtime.qTern, Hagi.Energy.roundTern]

/-- Exact representability makes the observed logit-displacement penalty
zero. -/
theorem ceQuantWitness_observedPenalty :
    ceQuantObservedPenalty ceQuantWitnessFeatures (1 / 4)
      (ceNextParameters ceQuantWitnessFeatures 0 0
        (safeStepSize ceQuantWitnessFeatures 0 0)) = 0 := by
  rw [ceQuantObservedPenalty, ceQuantWitness_ternaryCEParameters]
  simp

/-- The minimum penalty is zero through the observed branch; no numerical
optimality is asserted for the structural branch. -/
theorem ceQuantWitness_ceQuantPenalty :
    ceQuantPenalty ceQuantWitnessFeatures
      (ceNextParameters ceQuantWitnessFeatures 0 0
        (safeStepSize ceQuantWitnessFeatures 0 0)) (1 / 4) = 0 := by
  have hstruct : 0 ≤ ceQuantStructuralPenalty ceQuantWitnessFeatures (1 / 4)
      (ceNextParameters ceQuantWitnessFeatures 0 0
        (safeStepSize ceQuantWitnessFeatures 0 0)) := by
    unfold ceQuantStructuralPenalty
    positivity
  rw [ceQuantPenalty, ceQuantWitness_observedPenalty, min_eq_left hstruct]

/-- The strict safe-step premise holds because the observed-certified
minimum is zero while the residual is `1/8`. -/
theorem ceQuantWitness_strict_margin :
    ceQuantPenalty ceQuantWitnessFeatures
      (ceNextParameters ceQuantWitnessFeatures 0 0
        (safeStepSize ceQuantWitnessFeatures 0 0)) (1 / 4) <
      2 * (ceAlignment ceQuantWitnessFeatures 0 0) ^ 2 /
        (ceStepRange ceQuantWitnessFeatures 0 0) ^ 2 := by
  rw [ceQuantWitness_ceQuantPenalty, ceQuantWitness_alignment,
    ceQuantWitness_range]
  norm_num

/-- Instantiated actual quantized safe-step CE descent for the `2 × 5`
witness. -/
theorem ceQuantWitness_strict_descent :
    Hagi.ceOneHot 0 (ceLogits ceQuantWitnessFeatures
      (ternaryCEParameters (1 / 4)
        (ceNextParameters ceQuantWitnessFeatures 0 0
          (safeStepSize ceQuantWitnessFeatures 0 0)))) <
      Hagi.ceOneHot 0 (ceLogits ceQuantWitnessFeatures 0) := by
  apply ceOneHot_ternary_safeStep_lt ceQuantWitnessFeatures 0 0 (1 / 4)
  · norm_num
  · rw [ceQuantWitness_range]
    norm_num
  · exact ceQuantWitness_strict_margin

end Hagi.Model.CEQuantized
