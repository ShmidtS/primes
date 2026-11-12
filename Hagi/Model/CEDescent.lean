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


variable {V : Type} [Fintype V] [Nonempty V] {d : ℕ}

/-- Fixed nonemptiness witness so `sup'` terms share syntax. -/
private theorem c216_univNE : (Finset.univ : Finset V).Nonempty :=
  Finset.univ_nonempty_iff.mpr ‹_›

/-! ## The range-based quantity -/

/-- The logit RANGE of the one-unit directional displacement `d`:
`sup d − inf d`, written as `sup' d + sup' (-d)` over the vocabulary. -/
noncomputable def ceStepLogitRange (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : ℝ :=
  Finset.sup' Finset.univ c216_univNE
      (fun v => ceLogits X (ceDirection X θ t) v)
  + Finset.sup' Finset.univ c216_univNE
      (fun v => -ceLogits X (ceDirection X θ t) v)

theorem ceStepLogitRange_nonneg (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    0 ≤ ceStepLogitRange X θ t := by
  obtain ⟨v₀, _⟩ : (Finset.univ : Finset V).Nonempty := c216_univNE
  have h1 : ceLogits X (ceDirection X θ t) v₀
      ≤ Finset.sup' Finset.univ c216_univNE
          (fun v => ceLogits X (ceDirection X θ t) v) :=
    Finset.le_sup' _ (Finset.mem_univ v₀)
  have h2 : -ceLogits X (ceDirection X θ t) v₀
      ≤ Finset.sup' Finset.univ c216_univNE
          (fun w => -ceLogits X (ceDirection X θ t) w) :=
    Finset.le_sup' (fun w => -ceLogits X (ceDirection X θ t) w)
      (Finset.mem_univ v₀)
  unfold ceStepLogitRange
  linarith

/-- The range bounds every pairwise difference of directional logits. -/
theorem ceDirectionLogit_sub_le (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) (u v : V) :
    ceLogits X (ceDirection X θ t) u - ceLogits X (ceDirection X θ t) v
      ≤ ceStepLogitRange X θ t := by
  have h1 : ceLogits X (ceDirection X θ t) u
      ≤ Finset.sup' Finset.univ c216_univNE
          (fun v => ceLogits X (ceDirection X θ t) v) :=
    Finset.le_sup' _ (Finset.mem_univ u)
  have h2 : -ceLogits X (ceDirection X θ t) v
      ≤ Finset.sup' Finset.univ c216_univNE
          (fun w => -ceLogits X (ceDirection X θ t) w) :=
    Finset.le_sup' (fun w => -ceLogits X (ceDirection X θ t) w)
      (Finset.mem_univ v)
  unfold ceStepLogitRange
  linarith

/-- The actual eta-scaled displacement has pairwise difference at most
`eta * range`. -/
theorem ce_logitDisplacement_range (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    {eta : ℝ} (heta : 0 ≤ eta) (u v : V) :
    (ceNextLogits X θ t eta u - ceLogits X θ u)
      - (ceNextLogits X θ t eta v - ceLogits X θ v)
      ≤ eta * ceStepLogitRange X θ t := by
  rw [ceNextLogits_apply, ceNextLogits_apply]
  have h := mul_le_mul_of_nonneg_left
    (ceDirectionLogit_sub_le X θ t u v) heta
  ring_nf
  linarith

/-- The new range quantity never exceeds the engine's vocabulary-sum
range: `range ≤ 2·Σ_v |d v| = ceStepRange`. -/
theorem ceStepLogitRange_le_ceStepRange (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    ceStepLogitRange X θ t ≤ ceStepRange X θ t := by
  have h1 : Finset.sup' Finset.univ c216_univNE
        (fun v => ceLogits X (ceDirection X θ t) v)
      ≤ ∑ v, |ceLogits X (ceDirection X θ t) v| := by
    refine (Finset.sup'_le_iff c216_univNE _).mpr fun v _hv => ?_
    exact le_trans (le_abs_self _) (Finset.single_le_sum
      (f := fun z => |ceLogits X (ceDirection X θ t) z|)
      (fun z _hz => abs_nonneg _) (Finset.mem_univ v))
  have h2 : Finset.sup' Finset.univ c216_univNE
        (fun v => -ceLogits X (ceDirection X θ t) v)
      ≤ ∑ v, |ceLogits X (ceDirection X θ t) v| := by
    refine (Finset.sup'_le_iff c216_univNE _).mpr fun v _hv => ?_
    exact le_trans (neg_le_abs _) (Finset.single_le_sum
      (f := fun z => |ceLogits X (ceDirection X θ t) z|)
      (fun z _hz => abs_nonneg _) (Finset.mem_univ v))
  dsimp [ceStepLogitRange, ceStepRange]
  linarith

/-- Vanishing directional logits force vanishing range. -/
theorem ceStepLogitRange_eq_zero_of_eq_zero (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (h : ∀ v, ceLogits X (ceDirection X θ t) v = 0) :
    ceStepLogitRange X θ t = 0 := by
  have hneg : ∀ v, -ceLogits X (ceDirection X θ t) v = 0 :=
    fun v => by rw [h v]; ring
  unfold ceStepLogitRange
  rw [Finset.sup'_congr c216_univNE rfl (fun v _hv => h v),
    Finset.sup'_congr c216_univNE rfl (fun v _hv => hneg v)]
  simp

/-- Positive range forces strictly positive alignment. -/
theorem ceAlignment_pos_of_logitRange_pos (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepLogitRange X θ t) : 0 < ceAlignment X θ t := by
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
  have hr0 : ceStepLogitRange X θ t = 0 := by
    exact ceStepLogitRange_eq_zero_of_eq_zero X θ t
      (fun v => by simp [ceLogits, hdir, Matrix.mulVec, dotProduct])
  exact (ne_of_gt hr) hr0

/-! ## The range-based majorizer and safe step -/

/-- The range-based quadratic majorizer: identical to `ceMajorizer`
but with `ceStepLogitRange` in place of `ceStepRange`. -/
noncomputable def ceRangeMajorizer (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) (eta : ℝ) : ℝ :=
  Hagi.ceOneHot t (ceLogits X θ) - eta * ceAlignment X θ t
    + (eta * ceStepLogitRange X θ t) ^ 2 / 8

/-- The total minimizer of the range-based majorizer. -/
noncomputable def ceRangeSafeStep (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : ℝ :=
  if ceStepLogitRange X θ t = 0 then 0
  else 4 * ceAlignment X θ t / (ceStepLogitRange X θ t) ^ 2

/-- The range-based majorizer bounds the actual CE after every
nonnegative step. Same assembly as `ceOneHot_next_le_majorizer`,
with the pairwise range supplied by `ce_logitDisplacement_range`. -/
theorem ceOneHot_next_le_rangeMajorizer (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    {eta : ℝ} (heta : 0 ≤ eta) :
    Hagi.ceOneHot t (ceNextLogits X θ t eta)
      ≤ ceRangeMajorizer X θ t eta := by
  have hlse := Hagi.Energy.lse_shift_upper (ceLogits X θ)
    (ceNextLogits X θ t eta) (eta * ceStepLogitRange X θ t)
    (ce_logitDisplacement_range X θ t heta)
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
  unfold ceRangeMajorizer
  rw [ht]
  dsimp [Hagi.Core.ceOneHot, Hagi.Core.lse]
  linarith

theorem ceRangeSafeStep_nonneg (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    0 ≤ ceRangeSafeStep X θ t := by
  by_cases hr : ceStepLogitRange X θ t = 0
  · simp [ceRangeSafeStep, hr]
  · have hrpos : 0 < ceStepLogitRange X θ t :=
      lt_of_le_of_ne (ceStepLogitRange_nonneg X θ t) (Ne.symm hr)
    have hA := ceAlignment_pos_of_logitRange_pos X θ t hrpos
    rw [ceRangeSafeStep, ite_eq_right (ne_of_gt hrpos)]
    exact (div_pos (by positivity) (pow_pos hrpos 2)).le

theorem ceRangeSafeStep_pos_of_logitRange_pos (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepLogitRange X θ t) : 0 < ceRangeSafeStep X θ t := by
  have hA := ceAlignment_pos_of_logitRange_pos X θ t hr
  rw [ceRangeSafeStep, ite_eq_right (ne_of_gt hr)]
  exact div_pos (by positivity) (pow_pos hr 2)

/-- The range-based safe step minimizes the range-based majorizer. -/
theorem ceRangeMajorizer_safeStep_eq (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepLogitRange X θ t) :
    ceRangeMajorizer X θ t (ceRangeSafeStep X θ t)
      = Hagi.ceOneHot t (ceLogits X θ)
        - 2 * (ceAlignment X θ t) ^ 2 / (ceStepLogitRange X θ t) ^ 2 := by
  simp only [ceRangeMajorizer, ceRangeSafeStep,
    ite_eq_right (ne_of_gt hr)]
  field_simp
  ring

/-- MAIN THEOREM (P0c): the range-based safe step loses at least
`2·A²/R'²` with `R' = sup d − inf d`, and `R' ≤ ceStepRange`, so the
certified descent is never smaller than the engine's. -/
theorem ceOneHot_rangeSafeStep_le_residual (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepLogitRange X θ t) :
    Hagi.ceOneHot t (ceNextLogits X θ t (ceRangeSafeStep X θ t))
      ≤ Hagi.ceOneHot t (ceLogits X θ)
        - 2 * (ceAlignment X θ t) ^ 2 / (ceStepLogitRange X θ t) ^ 2 := by
  rw [← ceRangeMajorizer_safeStep_eq X θ t hr]
  exact ceOneHot_next_le_rangeMajorizer X θ t (ceRangeSafeStep_nonneg X θ t)

theorem ceOneHot_rangeSafeStep_lt (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepLogitRange X θ t) :
    Hagi.ceOneHot t (ceNextLogits X θ t (ceRangeSafeStep X θ t))
      < Hagi.ceOneHot t (ceLogits X θ) := by
  have hA := ceAlignment_pos_of_logitRange_pos X θ t hr
  have hbound := ceOneHot_rangeSafeStep_le_residual X θ t hr
  have hpos : 0 < 2 * (ceAlignment X θ t) ^ 2
      / (ceStepLogitRange X θ t) ^ 2 := by
    positivity
  linarith

/-! ## Comparison with the existing engine -/

/-- The new step is never smaller than the engine's step (at positive
new range; note `0 < ceStepLogitRange ↔ 0 < ceStepRange` is NOT needed
for this direction — whenever the new range is positive so is the old). -/
theorem ceRangeSafeStep_ge_safeStepSize (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepLogitRange X θ t) :
    safeStepSize X θ t ≤ ceRangeSafeStep X θ t := by
  have hA := ceAlignment_pos_of_logitRange_pos X θ t hr
  have hRle := ceStepLogitRange_le_ceStepRange X θ t
  have hRold : 0 < ceStepRange X θ t :=
    lt_of_lt_of_le hr hRle
  have hAold := ceAlignment_pos_of_range_pos X θ t hRold
  rw [safeStepSize, ite_eq_right (ne_of_gt hRold),
    ceRangeSafeStep, ite_eq_right (ne_of_gt hr)]
  have hs : (ceStepLogitRange X θ t) ^ 2
      ≤ (ceStepRange X θ t) ^ 2 := by
    nlinarith [hRle, sq_nonneg (ceStepLogitRange X θ t),
      ceStepLogitRange_nonneg X θ t]
  exact div_le_div_of_nonneg_left (by positivity : (0:ℝ)
      ≤ 4 * ceAlignment X θ t) (pow_pos hr 2) hs

/-- The new certified residual is never smaller than the engine's. -/
theorem ceRange_residual_ge (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepLogitRange X θ t) :
    2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2
      ≤ 2 * (ceAlignment X θ t) ^ 2 / (ceStepLogitRange X θ t) ^ 2 := by
  have hRle := ceStepLogitRange_le_ceStepRange X θ t
  have hA := ceAlignment_pos_of_logitRange_pos X θ t hr
  have hs : (ceStepLogitRange X θ t) ^ 2
      ≤ (ceStepRange X θ t) ^ 2 := by
    nlinarith [hRle, sq_nonneg (ceStepLogitRange X θ t),
      ceStepLogitRange_nonneg X θ t]
  exact div_le_div_of_nonneg_left (by positivity : (0:ℝ)
      ≤ 2 * (ceAlignment X θ t) ^ 2) (pow_pos hr 2) hs

/-! ## Numeric controls: the two-class identity example -/

/-- On two indices the supremum is the pointwise maximum. -/
private theorem c216_sup_univ_two (f : Fin 2 → ℝ) :
    Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨0⟩) f = max (f 0) (f 1) := by
  apply le_antisymm
  · refine (Finset.sup'_le_iff _ _).mpr fun v _hv => ?_
    fin_cases v <;> simp
  · exact max_le (Finset.le_sup' f (by simp))
      (Finset.le_sup' f (by simp))

/-- The identity two-class example has new range `1` (vs old `2`). -/
theorem identityTwoClass_logitRange_test :
    ceStepLogitRange (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := by
  unfold ceStepLogitRange
  show Finset.sup' Finset.univ _
      (fun v => ceLogits (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (ceDirection (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0) v)
    + Finset.sup' Finset.univ _
      (fun v => -ceLogits (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (ceDirection (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0) v) = 1
  rw [c216_sup_univ_two, c216_sup_univ_two]
  norm_num [ceDirection, ceLogits, ceResidual, ceAlignment,
    residualTranspose, Hagi.Energy.smax, Hagi.Prelude.softDef,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Its range-based safe step is `2`, vs the engine's `1/2`. -/
theorem identityTwoClass_rangeSafeStep_test :
    ceRangeSafeStep (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 2 := by
  have hr : ceStepLogitRange (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 :=
    identityTwoClass_logitRange_test
  have hA : ceAlignment (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 / 2 :=
    identityTwoClass_alignment_test
  simp [ceRangeSafeStep, hr, hA]
  norm_num

/-- Explicit ordering control: new step `2` exceeds old step `1/2`. -/
theorem identityTwoClass_step_comparison_test :
    safeStepSize (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0
      < ceRangeSafeStep (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
  rw [identityTwoClass_safeStepSize_test,
    identityTwoClass_rangeSafeStep_test]
  norm_num

/-- Explicit ordering control: new residual `1/2` exceeds old `1/8`. -/
theorem identityTwoClass_residual_comparison_test :
    2 * (ceAlignment (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ^ 2
        / (ceStepRange (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ^ 2
      < 2 * (ceAlignment (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ^ 2
        / (ceStepLogitRange (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ^ 2 := by
  rw [identityTwoClass_alignment_test,
    identityTwoClass_range_test, identityTwoClass_logitRange_test]
  norm_num
end Hagi.Model
