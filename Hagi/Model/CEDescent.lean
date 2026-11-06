/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Concat
import Hagi.Energy.PoEBound
import Hagi.Model.CEGradient

/-!
# A finite categorical cross-entropy descent step

For fixed features `X : Matrix V (Fin d) ℝ`, the direction below is the
literal transpose of the exact softmax residual, not an arbitrary descent
vector.  The one-step certificate is obtained from
`Hagi.Energy.lse_shift_upper`; no derivative and no global smoothness or
Lipschitz hypothesis is used.

The computed range is a range bound for the actual logit displacement.
The selected step size minimizes only the resulting quadratic majorizer.
It is not asserted to minimize cross-entropy globally, and no iterative
convergence claim is made.
-/

set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Model

/-- Logits of a fixed finite categorical linear head. -/
noncomputable def ceLogits {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) : V → ℝ :=
  X *ᵥ θ.ofLp

/-- The exact residual `softmax (Xθ) - oneHot t`. -/
noncomputable def ceResidual {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) : V → ℝ := by
  classical
  exact fun v => Hagi.Energy.smax (ceLogits X θ) v - if v = t then 1 else 0

/-- The transpose of the actual residual through the current features. -/
noncomputable def residualTranspose {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) : Fin d → ℝ :=
  fun j => ∑ v, ceResidual X θ t v * X v j

/-- Negative residual-transpose, represented on the Euclidean carrier. -/
noncomputable def ceDirection {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => -residualTranspose X θ t j)

/-- Nonnegative alignment of the residual-transpose direction. -/
noncomputable def ceAlignment {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) : ℝ :=
  ∑ j, residualTranspose X θ t j ^ 2

/-- Parameters after moving by `eta` in the residual-transpose direction. -/
noncomputable def ceNextParameters {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (eta : ℝ) : EuclideanSpace ℝ (Fin d) :=
  θ + eta • ceDirection X θ t

/-- Logits after the parameter step. -/
noncomputable def ceNextLogits {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (eta : ℝ) : V → ℝ :=
  ceLogits X (ceNextParameters X θ t eta)

/-- A computable range bound for the actual one-eta logit displacement. -/
noncomputable def ceStepRange {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) : ℝ :=
  2 * ∑ v, |ceLogits X (ceDirection X θ t) v|

/-- The full quadratic majorizer, including the current loss. -/
noncomputable def ceMajorizer {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (eta : ℝ) : ℝ :=
  Hagi.ceOneHot t (ceLogits X θ) - eta * ceAlignment X θ t
    + (eta * ceStepRange X θ t) ^ 2 / 8

/-- Total minimizer of the computed majorizer; it is zero at zero range. -/
noncomputable def safeStepSize {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) : ℝ :=
  if ceStepRange X θ t = 0 then 0
  else 4 * ceAlignment X θ t / (ceStepRange X θ t) ^ 2

@[simp] theorem ceDirection_ofLp {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (j : Fin d) :
    (ceDirection X θ t).ofLp j = -residualTranspose X θ t j := rfl

/-! ## Exact algebra of the displacement -/

/-- Matrix multiplication makes the parameter displacement a weighted
logit displacement. -/
theorem ceNextLogits_apply {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (eta : ℝ) (v : V) :
    ceNextLogits X θ t eta v = ceLogits X θ v
      + eta * ceLogits X (ceDirection X θ t) v := by
  simp only [ceNextLogits, ceLogits, ceNextParameters, Matrix.mulVec,
    dotProduct, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_add,     Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The first-order term is exactly the negative scaled alignment.
This is a sum exchange from the displayed definitions. -/
theorem ce_first_order_eq {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (eta : ℝ) :
    ∑ v, ceResidual X θ t v * (ceNextLogits X θ t eta v - ceLogits X θ v)
      = -eta * ceAlignment X θ t := by
  let D : Fin d → ℝ := residualTranspose X θ t
  have hterm : ∀ v : V,
      ceResidual X θ t v * (ceNextLogits X θ t eta v - ceLogits X θ v)
        = -eta * ∑ j, (ceResidual X θ t v * X v j) * D j := by
    intro v
    rw [ceNextLogits_apply]
    simp only [ceLogits, ceDirection, Matrix.mulVec, dotProduct]
    dsimp [D]
    rw [add_sub_cancel_left, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  calc
    ∑ v, ceResidual X θ t v * (ceNextLogits X θ t eta v - ceLogits X θ v)
        = -eta * ∑ v, ∑ j, (ceResidual X θ t v * X v j) * D j := by
          rw [Finset.sum_congr rfl (fun v _hv => hterm v), ← Finset.mul_sum]
    _ = -eta * ∑ j, ∑ v, (ceResidual X θ t v * X v j) * D j := by
          rw [Finset.sum_comm]
    _ = -eta * ∑ j, D j * D j := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _hj
          rw [← Finset.sum_mul]
          rfl
    _ = -eta * ceAlignment X θ t := by
          rw [ceAlignment]
          congr 1
          exact Finset.sum_congr rfl (fun j _hj => by rw [pow_two])

/-! ## Computed range and nondegeneracy -/

theorem ceStepRange_nonneg {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    0 ≤ ceStepRange X θ t := by
  unfold ceStepRange
  positivity

theorem ceAlignment_nonneg {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    0 ≤ ceAlignment X θ t := by
  unfold ceAlignment
  positivity

/-- The actual eta-scaled displacement has range at most `eta * range`. -/
theorem ce_displacement_range {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    {eta : ℝ} (heta : 0 ≤ eta) (u v : V) :
    (ceNextLogits X θ t eta u - ceLogits X θ u)
      - (ceNextLogits X θ t eta v - ceLogits X θ v)
      ≤ eta * ceStepRange X θ t := by
  have hsub : ∀ w : V,
      |ceLogits X (ceDirection X θ t) w|
        ≤ ∑ z, |ceLogits X (ceDirection X θ t) z| := by
    intro w
    exact Finset.single_le_sum
      (fun z _hz => abs_nonneg (ceLogits X (ceDirection X θ t) z))
      (Finset.mem_univ w)
  have htri : ceLogits X (ceDirection X θ t) u
      - ceLogits X (ceDirection X θ t) v
      ≤ |ceLogits X (ceDirection X θ t) u|
        + |ceLogits X (ceDirection X θ t) v| := by
    exact le_trans (le_abs_self _) (abs_sub _ _)
  rw [ceNextLogits_apply, ceNextLogits_apply]
  have hmul := mul_le_mul_of_nonneg_left
    (add_le_add (hsub u) (hsub v)) heta
  have hmul' := mul_le_mul_of_nonneg_left htri heta
  dsimp [ceStepRange]
  linarith

/-- Zero range means that every one-unit directional logit vanishes. -/
theorem ceStepRange_eq_zero_iff {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    ceStepRange X θ t = 0 ↔ ∀ v, ceLogits X (ceDirection X θ t) v = 0 := by
  constructor
  · intro hr v
    have hsum : ∑ w, |ceLogits X (ceDirection X θ t) w| = 0 := by
      dsimp [ceStepRange] at hr
      linarith
    have habs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun w _hw => abs_nonneg (ceLogits X (ceDirection X θ t) w))).mp hsum
      v (Finset.mem_univ v)
    exact abs_eq_zero.mp habs
  · intro hv
    simp [ceStepRange, hv]

/-- Positive actual range forces strictly positive alignment. -/
theorem ceAlignment_pos_of_range_pos {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepRange X θ t) : 0 < ceAlignment X θ t := by
  apply lt_of_le_of_ne (ceAlignment_nonneg X θ t)
  intro hA
  have hA0 : ceAlignment X θ t = 0 := hA.symm
  have hD : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      residualTranspose X θ t j = 0 := by
    apply (Finset.sum_sq_eq_zero_iff Finset.univ
      (residualTranspose X θ t)).mp
    simpa [ceAlignment] using hA0
  have hdir : ceDirection X θ t = 0 := by
    ext j
    simp [ceDirection_ofLp, hD j (Finset.mem_univ j)]
  have hr0 : ceStepRange X θ t = 0 := by
    simp [ceStepRange, ceLogits, hdir, Matrix.mulVec, dotProduct]
  exact (ne_of_gt hr) hr0

/-- The converse relevant to the total step rule: at zero range the
alignment is zero, by the exact first-order identity. -/
theorem ceAlignment_eq_zero_of_range_eq_zero {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : ceStepRange X θ t = 0) : ceAlignment X θ t = 0 := by
  have hlin := ce_first_order_eq X θ t 1
  have hzero := (ceStepRange_eq_zero_iff X θ t).mp hr
  have hnext : ∀ v, ceNextLogits X θ t 1 v = ceLogits X θ v := by
    intro v
    rw [ceNextLogits_apply, hzero v]
    ring
  have hsum : ∑ v, ceResidual X θ t v *
      (ceNextLogits X θ t 1 v - ceLogits X θ v) = 0 := by
    apply Finset.sum_eq_zero
    intro v _hv
    rw [hnext v]
    ring
  rw [hsum] at hlin
  linarith

/-- At zero range the actual logits do not move, for any real eta. -/
theorem ceNextLogits_eq_of_range_eq_zero {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : ceStepRange X θ t = 0) (eta : ℝ) :
    ceNextLogits X θ t eta = ceLogits X θ := by
  funext v
  rw [ceNextLogits_apply, (ceStepRange_eq_zero_iff X θ t).mp hr v]
  ring

/-! ## One-step majorization -/

/-- The computed second-order majorizer bounds the actual cross-entropy
after every nonnegative step. -/
theorem ceOneHot_next_le_majorizer {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    {eta : ℝ} (heta : 0 ≤ eta) :
    Hagi.ceOneHot t (ceNextLogits X θ t eta) ≤ ceMajorizer X θ t eta := by
  have hlse := Hagi.Energy.lse_shift_upper (ceLogits X θ)
    (ceNextLogits X θ t eta) (eta * ceStepRange X θ t)
    (ce_displacement_range X θ t heta)
  have hlin := ce_first_order_eq X θ t eta
  have ht := ceNextLogits_apply X θ t eta t
  classical
  have honehot : ∑ v, (if v = t then (1 : ℝ) else 0)
      * (ceNextLogits X θ t eta v - ceLogits X θ v)
      = ceNextLogits X θ t eta t - ceLogits X θ t := by
    simp
  simp only [ceResidual, sub_mul, Finset.sum_sub_distrib] at hlin
  rw [honehot, ht] at hlin
  have hsoft : ∑ v, Hagi.Energy.smax (ceLogits X θ) v
      * (ceNextLogits X θ t eta v - ceLogits X θ v)
      = -eta * ceAlignment X θ t + eta * ceLogits X (ceDirection X θ t) t := by
    linarith
  rw [hsoft] at hlse
  unfold Hagi.ceOneHot Hagi.Core.lse
  unfold ceMajorizer
  rw [ht]
  dsimp [Hagi.Core.ceOneHot, Hagi.Core.lse]
  linarith

/-- Expanded form of the one-step certificate: the linear coefficient is
the exact sum of squared residual-transpose coordinates. -/
theorem ceOneHot_next_le {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    {eta : ℝ} (heta : 0 ≤ eta) :
    Hagi.ceOneHot t (ceNextLogits X θ t eta)
      ≤ Hagi.ceOneHot t (ceLogits X θ) - eta * ceAlignment X θ t
        + (eta * ceStepRange X θ t) ^ 2 / 8 :=
  ceOneHot_next_le_majorizer X θ t heta

@[simp] theorem safeStepSize_of_range_eq_zero {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : ceStepRange X θ t = 0) : safeStepSize X θ t = 0 := by
  simp [safeStepSize, hr]

/-- In the zero-range case the safe step is zero and the CE is unchanged. -/
theorem ceOneHot_eq_of_range_eq_zero {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : ceStepRange X θ t = 0) (eta : ℝ) :
    Hagi.ceOneHot t (ceNextLogits X θ t eta) = Hagi.ceOneHot t (ceLogits X θ) := by
  rw [ceNextLogits_eq_of_range_eq_zero X θ t hr eta]

/-! ## The safe majorizer step -/

theorem safeStepSize_pos_of_range_pos {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepRange X θ t) : 0 < safeStepSize X θ t := by
  have hA := ceAlignment_pos_of_range_pos X θ t hr
  rw [safeStepSize, ite_eq_right (ne_of_gt hr)]
  exact div_pos (by positivity) (by positivity)

theorem safeStepSize_nonneg {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    0 ≤ safeStepSize X θ t := by
  by_cases hr : ceStepRange X θ t = 0
  · rw [safeStepSize_of_range_eq_zero X θ t hr]
  · exact (safeStepSize_pos_of_range_pos X θ t
      (lt_of_le_of_ne (ceStepRange_nonneg X θ t) (Ne.symm hr))).le

/-- The total safe step minimizes the computed quadratic majorizer.
Indeed, at positive range it is its nonnegative stationary point, and at
zero range the first-order identity makes the majorizer constant. -/
theorem ceMajorizer_safeStep_le {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (eta : ℝ) : ceMajorizer X θ t (safeStepSize X θ t)
      ≤ ceMajorizer X θ t eta := by
  by_cases hr : ceStepRange X θ t = 0
  · have hA := ceAlignment_eq_zero_of_range_eq_zero X θ t hr
    simp [ceMajorizer, hr, hA]
  · have hrpos : 0 < ceStepRange X θ t :=
      lt_of_le_of_ne (ceStepRange_nonneg X θ t) (Ne.symm hr)
    have hdiff : ceMajorizer X θ t eta
        - ceMajorizer X θ t (safeStepSize X θ t)
        = (ceStepRange X θ t) ^ 2 / 8
          * (eta - 4 * ceAlignment X θ t / (ceStepRange X θ t) ^ 2) ^ 2 := by
      simp only [ceMajorizer, safeStepSize, ite_eq_right hr]
      field_simp
      ring
    have hsquare : 0 ≤ (ceStepRange X θ t) ^ 2 / 8
        * (eta - 4 * ceAlignment X θ t / (ceStepRange X θ t) ^ 2) ^ 2 := by
      positivity
    linarith

/-- Safe-step evaluation of the majorizer gives the exact residual
`2 * alignment² / range²`. -/
theorem ceMajorizer_safeStep_eq {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepRange X θ t) :
    ceMajorizer X θ t (safeStepSize X θ t)
      = Hagi.ceOneHot t (ceLogits X θ)
        - 2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2 := by
  simp only [ceMajorizer, safeStepSize, ite_eq_right (ne_of_gt hr)]
  field_simp
  ring

/-- The safe step loses at least the computed positive residual in the
certified upper bound. -/
theorem ceOneHot_safeStep_le_residual {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepRange X θ t) :
    Hagi.ceOneHot t (ceNextLogits X θ t (safeStepSize X θ t))
      ≤ Hagi.ceOneHot t (ceLogits X θ)
        - 2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2 := by
  rw [← ceMajorizer_safeStep_eq X θ t hr]
  exact ceOneHot_next_le_majorizer X θ t (safeStepSize_nonneg X θ t)

/-- Positive range gives strict actual CE descent.  This is a one-step
certificate, not a statement about a global CE optimum. -/
theorem ceOneHot_safeStep_lt {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepRange X θ t) :
    Hagi.ceOneHot t (ceNextLogits X θ t (safeStepSize X θ t))
      < Hagi.ceOneHot t (ceLogits X θ) := by
  have hA := ceAlignment_pos_of_range_pos X θ t hr
  have hbound := ceOneHot_safeStep_le_residual X θ t hr
  have hpos : 0 < 2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2 := by
    positivity
  linarith

/-! ## Elementary checks -/

/-- The mathematical derivative in the chosen parameter direction equals
the negative quadratic alignment used by the range-majorizer step. -/
theorem fderiv_ceDirection {V : Type} [Fintype V] [Nonempty V]
    {d : ℕ} (X : Matrix V (Fin d) ℝ) (t : V)
    (θ : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun w : EuclideanSpace ℝ (Fin d) =>
      Hagi.ceOneHot t (ceLogits X w)) θ (ceDirection X θ t) =
      -ceAlignment X θ t := by
  classical
  simp only [ceLogits]
  rw [CEGradient.fderiv_ceOneHot_mulVec]
  have hlin := ce_first_order_eq X θ t 1
  simp only [ceNextLogits_apply, add_sub_cancel_left, one_mul] at hlin
  rw [neg_one_mul] at hlin
  rw [← hlin]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hv : v = t <;>
    simp [ceResidual, ceLogits, Hagi.Energy.smax, hv]

/-! ## Elementary checks -/

/-- Zero features give zero range and the zero safe step. -/
theorem zeroMatrix_safeStepSize_test :
    safeStepSize (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 0 := by
  apply safeStepSize_of_range_eq_zero
  simp [ceStepRange, ceLogits, Matrix.mulVec, dotProduct]

/-- Identity features over two classes at zero parameters have nonzero
alignment `1/2`. -/
theorem identityTwoClass_alignment_test :
    ceAlignment (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 / 2 := by
  norm_num [ceAlignment, residualTranspose, ceResidual, ceLogits,
    Hagi.Energy.smax, Hagi.Prelude.softDef, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-- The same nondegenerate two-class example has computed range `2`. -/
theorem identityTwoClass_range_test :
    ceStepRange (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 2 := by
  norm_num [ceStepRange, ceAlignment, residualTranspose, ceResidual,
    ceDirection, ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Consequently its total safe step is positive and equals `1/2`. -/
theorem identityTwoClass_safeStepSize_test :
    safeStepSize (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 / 2 := by
  have hr : ceStepRange (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 2 := by
    norm_num [ceStepRange, ceAlignment, residualTranspose, ceResidual,
      ceDirection, ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hA : ceAlignment (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 / 2 := by
    norm_num [ceAlignment, residualTranspose, ceResidual, ceLogits,
      Hagi.Energy.smax, Hagi.Prelude.softDef, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  simp [safeStepSize, hr, hA]
  norm_num

end Hagi.Model
