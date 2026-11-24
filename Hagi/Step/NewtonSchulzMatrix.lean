/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Hagi.Step.Muon


/-!
# Newton–polar iteration, scalar core

The scalar engine of the Newton polar-factorization
iteration (Higham 1986 quadratic convergence; plan §2
Muon two-level structure — exact O_t = UVᵀ vs NS
approximation with explicit error):

  x ↦ (x + x⁻¹)/2,   x_{k+1} − 1 = (x_k − 1)² / (2 x_k).

The error recursion is EXACTLY quadratic — the mechanism
behind Higham's convergence analysis; the scaling step
(Byers–Xu) only keeps x in the monotone branch x ≥ 1 where
|newtonStep x − 1| ≤ |x − 1|²/2.
-/

open Real

namespace Hagi.Step

noncomputable def newtonStep (x : ℝ) : ℝ := (x + x⁻¹) / 2

theorem newton_polar_scalar_error (x : ℝ) (hx : 0 < x) :
    newtonStep x - 1 = (x - 1)^2 / (2 * x) := by
  unfold newtonStep
  field_simp
  ring

theorem newton_error_ratio (x : ℝ) (hx : 1 ≤ x) :
    abs (newtonStep x - 1) ≤ (x - 1)^2 / 2 := by
  have hx0 : 0 < x := by linarith
  rw [newton_polar_scalar_error x hx0, abs_of_nonneg (by positivity)]
  refine (div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * x)
    (by norm_num : (0:ℝ) < 2)).mpr ?_
  nlinarith [sq_nonneg (x - 1)]

/-!
### T-step quadratic convergence

Composing the scalar error recursion over `T` Newton steps:
the error exponent DOUBLES each step —

  |newtonIter x₀ T − 1| ≤ 2·((x₀ − 1)/2)^{2^T}

— the formal quadratic-convergence rate of the Newton polar
iteration (Higham 1986), with the branch invariant
`newtonStep x ≥ 1` (AM–GM) kept by Byers–Xu scaling. -/
theorem newtonStep_ge_one (x : ℝ) (hx : 0 < x) :
    1 ≤ Hagi.Step.newtonStep x := by
  unfold Hagi.Step.newtonStep
  have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ (by linarith : (x:ℝ) ≠ 0)
  nlinarith [sq_nonneg (x - 1)]

noncomputable def newtonIter (x₀ : ℝ) : ℕ → ℝ :=
  fun T => (Hagi.Step.newtonStep^[T]) x₀

theorem newton_polar_convergence (x₀ : ℝ) (hx₀ : 1 ≤ x₀) (T : ℕ) :
    abs (newtonIter x₀ T - 1) ≤ 2 * ((x₀ - 1)/2) ^ (2 ^ T) := by
  induction T generalizing x₀ with
  | zero =>
      unfold newtonIter
      simp only [Function.iterate_zero_apply]
      rw [abs_of_nonneg (by linarith), pow_zero, pow_one]
      field_simp
      exact le_rfl
  | succ T ih =>
      have hx0 : (0:ℝ) < x₀ := by linarith
      have hge1 : 1 ≤ Hagi.Step.newtonStep x₀ := newtonStep_ge_one x₀ hx0
      have hstep := Hagi.Step.newton_error_ratio x₀ hx₀
      -- iterate shift
      have hiter : newtonIter x₀ (T+1) = newtonIter (Hagi.Step.newtonStep x₀) T := by
        unfold newtonIter
        rw [Function.iterate_succ_apply]
      rw [hiter]
      have hnext := ih (Hagi.Step.newtonStep x₀) hge1
      -- |e| bound chain
      have hpos : (0:ℝ) ≤ newtonStep x₀ - 1 := by
        have := newtonStep_ge_one x₀ hx0
        linarith
      rw [abs_of_nonneg hpos] at hstep
      have hsq : (newtonStep x₀ - 1) / 2 ≤ ((x₀ - 1) / 2) ^ 2 := by
        rw [div_pow]
        norm_num
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (0:ℝ) < 4)]
        rw [show Hagi.Step.newtonStep x₀ - 1 = (x₀ - 1) ^ 2 / (2 * x₀) from
          Hagi.Step.newton_polar_scalar_error x₀ hx0]
        field_simp
        nlinarith [sq_nonneg (x₀ - 1), sq_nonneg (x₀ + 1)]
      -- final pow composition
      have hnn : (0:ℝ) ≤ (newtonStep x₀ - 1) / 2 := by
        have := newtonStep_ge_one x₀ hx0
        positivity
      have hmono : ((newtonStep x₀ - 1) / 2) ^ (2 ^ T)
          ≤ (((x₀ - 1) / 2) ^ 2) ^ (2 ^ T) :=
        pow_le_pow_left₀ hnn hsq (2 ^ T)
      have hcomb : 2 * ((newtonStep x₀ - 1) / 2) ^ (2 ^ T)
          ≤ 2 * ((x₀ - 1) / 2) ^ (2 ^ (T + 1)) := by
        have hexp : 2 ^ (T + 1) = 2 * 2 ^ T := by rw [pow_succ]; ring
        rw [hexp, pow_mul]
        exact mul_le_mul_of_nonneg_left hmono (by norm_num)
      calc abs (newtonIter (Hagi.Step.newtonStep x₀) T - 1)
          ≤ 2 * ((newtonStep x₀ - 1) / 2) ^ (2 ^ T) := hnext
        _ ≤ 2 * ((x₀ - 1) / 2) ^ (2 ^ (T + 1)) := hcomb

/-!
### Convergence

Turning the rate into an actual limit: for
`1 ≤ x₀ < 3` the iterates converge to the polar factor 1.

  newtonIter x₀ T ⟶ 1  (T → ∞)

Proof: the majorant `2·r^{2^T}` with `r = (x₀−1)/2 < 1` is
squeezed by `r^{2^T} ≤ r^T` (`T ≤ 2^T`, proved by induction)
against `tendsto_pow_atTop_nhds_zero_of_lt_one`. -/
open Filter in
theorem newton_polar_tendsto_one (x₀ : ℝ) (hx₀ : 1 ≤ x₀)
    (hx₃ : x₀ < 3) :
    Tendsto (fun T => newtonIter x₀ T) atTop (nhds 1) := by
  have hr0 : (0:ℝ) ≤ (x₀ - 1) / 2 := by positivity
  have hr1 : (x₀ - 1) / 2 < 1 := by linarith
  have hbdd : ∀ T, |newtonIter x₀ T - 1|
      ≤ 2 * ((x₀ - 1) / 2) ^ ((2:ℕ) ^ T) :=
    fun T => newton_polar_convergence x₀ hx₀ T
  have hmono : ∀ T, ((x₀ - 1) / 2) ^ ((2:ℕ) ^ T)
      ≤ ((x₀ - 1) / 2) ^ T := by
    intro T
    have h2 : T ≤ (2:ℕ) ^ T := by
      induction T with
      | zero => norm_num
      | succ n ih =>
        have hexp : (2:ℕ)^(n+1) = (2:ℕ)^n + (2:ℕ)^n := by
          rw [pow_succ]; ring
        have hpos : 0 < (2:ℕ)^n := pow_pos (by norm_num : (1:ℕ) ≤ 2) n
        omega
    exact pow_le_pow_of_le_one hr0 (le_of_lt hr1) h2
  have hle : ∀ T, |newtonIter x₀ T - 1|
      ≤ 2 * ((x₀ - 1) / 2) ^ T := fun T =>
    (hbdd T).trans (by
      exact mul_le_mul_of_nonneg_left (hmono T) (by norm_num : (0:ℝ) ≤ 2))
  have hlim : Tendsto (fun T => 2 * ((x₀ - 1) / 2) ^ T)
      atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul 2
  -- two-sided squeeze: -g T <= e T <= g T
  have hkey : Tendsto (fun T => newtonIter x₀ T - 1)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun T => -(2 * ((x₀ - 1) / 2) ^ T))
      (f := fun T => newtonIter x₀ T - 1)
      (h := fun T => 2 * ((x₀ - 1) / 2) ^ T)
      (by simpa using hlim.neg) hlim (fun T => (abs_le.mp (hle T)).1)
      (fun T => (abs_le.mp (hle T)).2)
  have hgo : Tendsto (fun T => (1:ℝ) + (newtonIter x₀ T - 1))
      atTop (nhds (1 + 0)) := hkey.const_add 1
  simpa [add_sub_cancel] using hgo

end Hagi.Step
namespace Hagi.Step

/-- **Монотонный спуск полярного Ньютона**: при x ≥ 1
newtonStep x ≤ x, при x > 1 строго. С квадратичной скоростью и
сходимостью траектория монотонно спускается к 1. -/
theorem newton_step_descent (x : ℝ) (hx : 1 ≤ x) :
    newtonStep x ≤ x := by
  have herr := newton_polar_scalar_error x (by linarith)
  have h5 : (x - 1)^2 / (2 * x) ≤ x - 1 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * x)]
    nlinarith
  linarith

theorem newton_step_descent_lt (x : ℝ) (hx : 1 < x) :
    newtonStep x < x := by
  have herr := newton_polar_scalar_error x (by linarith)
  have h5 : (x - 1)^2 / (2 * x) < x - 1 := by
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < 2 * x)]
    nlinarith
  linarith


/-- **Скобка траектории полярного Ньютона**:
1 ≤ newtonIter x₀ T ≤ x₀ при x₀ ≥ 1 (индукция: спуск +
инвариант ≥ 1). -/
theorem newton_iter_bracket (x₀ : ℝ) (hx₀ : 1 ≤ x₀) (T : ℕ) :
    1 ≤ newtonIter x₀ T ∧ newtonIter x₀ T ≤ x₀ := by
  induction T with
  | zero =>
    unfold newtonIter
    exact ⟨hx₀, le_refl _⟩
  | succ t ih =>
    have hstep : newtonIter x₀ (t+1) = newtonStep (newtonIter x₀ t) := by
      unfold newtonIter
      exact Function.iterate_succ_apply' Hagi.Step.newtonStep t x₀
    rw [hstep]
    obtain ⟨h1, h2⟩ := ih
    refine ⟨newtonStep_ge_one _ (by linarith), ?_⟩
    exact le_trans (newton_step_descent _ h1) h2

end Hagi.Step

/-!
### Newton–Schulz polar iteration — scalar certificate

The Muon mid-speed body orthogonalizes with the Newton–Schulz
polynomial; on the singular spectrum in (0, √3) each singular value
flows under the scalar map `φ(t) = t(3 − t²)/2`. This section
certifies the SCALAR lemma rigorously; the matrix statement (ℓ∞/ℓ2
operator-norm non-expansion of the matrix NS map) remains the
documented hypothesis `hP : ‖P‖ ≤ 1` of `Hagi.Step.Muon` — the
Muon/Newton-Schulz connection here is scalar-only, honestly.
-/

namespace Hagi.Step

section NewtonSchulzScalar

/-- The Newton–Schulz scalar map `φ(t) = t (3 − t²) / 2`. -/
noncomputable def nsStep (t : ℝ) : ℝ := t * (3 - t ^ 2) / 2

/-- EXACT identity: `1 − φ(t) = (1 − t)² (t + 2) / 2` — the whole
scalar theory hangs off this polynomial identity (by `ring`). -/
theorem one_sub_nsStep (t : ℝ) :
    1 - nsStep t = (1 - t) ^ 2 * (t + 2) / 2 := by
  unfold nsStep
  ring

/-- `φ` maps `[0, √3]` into the nonnegative reals. -/
theorem nsStep_nonneg (t : ℝ) (ht0 : 0 ≤ t) (_ht3 : t ^ 2 ≤ 3) :
    0 ≤ nsStep t := by
  have h3 : 0 ≤ 3 - t ^ 2 := by linarith
  unfold nsStep
  positivity

/-- `φ` maps `[0, √3]` into `[0, 1]`: the deficit is exactly
`(1 − t)² (t + 2) / 2 ≥ 0`. -/
theorem nsStep_le_one (t : ℝ) (ht0 : 0 ≤ t) (_ht3 : t ^ 2 ≤ 3) :
    nsStep t ≤ 1 := by
  have h := one_sub_nsStep t
  have hp : 0 ≤ (1 - t) ^ 2 * (t + 2) / 2 := by
    have h2 : 0 ≤ t + 2 := by linarith
    positivity
  unfold nsStep at h ⊢
  linarith

/-- On `[0, 1]` the map ascends: `t ≤ φ(t) ≤ 1` (ascent half; the
upper half is `nsStep_le_one`). -/
theorem le_nsStep_of_le_one (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ≤ nsStep t := by
  have h : nsStep t - t = t * (1 - t ^ 2) / 2 := by
    unfold nsStep
    ring
  have h1 : 0 ≤ 1 - t ^ 2 := by nlinarith
  have h2 : 0 ≤ t * (1 - t ^ 2) / 2 := by positivity
  linarith

/-- Quadratic distance contraction on `[0, 1]`:
`1 − φ(t) ≤ (3/2) (1 − t)²` (constant sharp at `t = 1`). -/
theorem nsStep_dist_sq (t : ℝ) (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 - nsStep t ≤ 3 / 2 * (1 - t) ^ 2 := by
  have h := one_sub_nsStep t
  have h2 : (t + 2) / 2 ≤ 3 / 2 := by linarith
  have hp : 0 ≤ (1 - t) ^ 2 := sq_nonneg _
  have hm := mul_le_mul_of_nonneg_right h2 hp
  linarith

/-- The NS scalar trajectory: `nsIter t₀ k = φ^(k)(t₀)`. -/
noncomputable def nsIter (t₀ : ℝ) : ℕ → ℝ := fun k => Nat.iterate nsStep k t₀

theorem nsIter_succ (t₀ : ℝ) (k : ℕ) :
    nsIter t₀ (k + 1) = nsStep (nsIter t₀ k) := by
  unfold nsIter nsStep
  exact Function.iterate_succ_apply' _ _ _

/-- Invariance: the trajectory from `[0, 1]` stays in `[0, 1]`. -/
theorem nsIter_mem (t₀ : ℝ) (ht0 : 0 ≤ t₀) (ht1 : t₀ ≤ 1) :
    ∀ k, 0 ≤ nsIter t₀ k ∧ nsIter t₀ k ≤ 1 := by
  intro k
  induction k with
  | zero => exact ⟨ht0, ht1⟩
  | succ k ih =>
      obtain ⟨h0, h1⟩ := ih
      rw [nsIter_succ]
      exact ⟨nsStep_nonneg _ h0 (by nlinarith), nsStep_le_one _ h0 (by nlinarith)⟩

/-- Monotone ascent along the trajectory. -/
theorem nsIter_mono (t₀ : ℝ) (ht0 : 0 ≤ t₀) (ht1 : t₀ ≤ 1) :
    ∀ k, nsIter t₀ k ≤ nsIter t₀ (k + 1) := by
  intro k
  have hmem := nsIter_mem t₀ ht0 ht1 k
  obtain ⟨h0, h1⟩ := hmem
  rw [nsIter_succ]
  exact le_nsStep_of_le_one _ h0 h1

/-- Iterated quadratic distance contraction: the deficit to 1
SQUARES (up to the sharp constant 3/2) at every step — the
quantitative content of Newton–Schulz scalar convergence. -/
theorem nsIter_dist_sq (t₀ : ℝ) (ht0 : 0 ≤ t₀) (ht1 : t₀ ≤ 1) (k : ℕ) :
    1 - nsIter t₀ (k + 1) ≤ 3 / 2 * (1 - nsIter t₀ k) ^ 2 := by
  have hmem := nsIter_mem t₀ ht0 ht1 k
  obtain ⟨h0, h1⟩ := hmem
  rw [nsIter_succ]
  exact nsStep_dist_sq _ h0 h1

end NewtonSchulzScalar

end Hagi.Step

/-!
# Newton–Schulz matrix iterate — diagonal contraction

The matrix Newton–Schulz polar iterate `X ← X(3I − XᵀX)/2`
The scalar certificate is
`Hagi.Step.nsStep`; this module lifts it to matrices on
the DIAGONAL subspace and proves orthogonal equivariance of the
iterate:

* `nsMatrixStep_diagonal` — on a diagonal input the iterate is
  diagonal with entries the scalar NS map of the input entries
  (honest matrix-multiplication computation, no functional
  calculus);
* `nsMatrixStep_diagonal_contraction` — for input entries in the
  scalar bracket `[0, 1]` the iterate acts as a contraction on
  `(n → ℝ)` with the sup norm: the hypothesis `hP` of the Muon
  bounds is DISCHARGED in the diagonal case;
* `nsMatrixStep_orth` — the iterate commutes with orthogonal
  left/right factors (`UᵀU = VᵀV = 1`), the transport ingredient
  for the general spectral route (see design note: the full
  spectral-norm statement needs a spectral-norm Matrix API absent
  from Mathlib here; NOT claimed);
* `muon_step_bound_ns_diagonal` — the consumer corollary:
  `muon_step_bound` with `P` the NS iterate of a bounded diagonal
  input, `hP` discharged.

Honest boundary: the contraction is stated for the sup norm on
`n → ℝ` (the operator norm of a diagonal matrix there is the max
of its entries' absolute values). The spectral-norm statement used
by the real Muon analyzer remains the documented follow-up.
-/

open Matrix

namespace Hagi.Step

/-- The matrix Newton–Schulz polar iterate
`X ← X(3I − XᵀX)/2`, entrywise-halved form
(defeq to the scalar-multiple form, see `nsMatrixStep_eq_smul`). -/
noncomputable def nsMatrixStep {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => (A * ((3 : ℝ) • (1 : Matrix n n ℝ) - Aᵀ * A)) i j / 2

/-- Bridge to the scalar-multiple form of the iterate. -/
theorem nsMatrixStep_eq_smul {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    nsMatrixStep A
      = (1 / 2 : ℝ) • (A * ((3 : ℝ) • (1 : Matrix n n ℝ) - Aᵀ * A)) := by
  ext i j
  simp [nsMatrixStep, Matrix.smul_apply, div_eq_mul_inv]
  ring

/-- DIAGONAL ACTION: on a diagonal input the NS iterate is diagonal
with entries the scalar NS map `Hagi.Step.nsStep` of the diagonal
entries — the scalar→matrix lift as a matrix-multiplication
computation. -/
theorem nsMatrixStep_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) :
    nsMatrixStep (Matrix.diagonal d)
      = Matrix.diagonal (fun i => Hagi.Step.nsStep (d i)) := by
  ext i j
  simp only [nsMatrixStep, Matrix.of_apply, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.transpose_apply, mul_ite]
  by_cases h : i = j
  · subst h
    simp only [ite_true]
    simp [Hagi.Step.nsStep, pow_two]
  · simp [h, Ne.symm h]

/-- DIAGONAL CONTRACTION: for a diagonal input with entries in the
scalar bracket `[0, 1]` the NS iterate is a contraction on
`(n → ℝ)` with the sup norm — the `hP` hypothesis of the Muon
bounds, discharged for the diagonal NS case. -/
theorem nsMatrixStep_diagonal_contraction {n : Type*} [Fintype n]
    [DecidableEq n] (d : n → ℝ) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (z : n → ℝ) :
    ‖nsMatrixStep (Matrix.diagonal d) *ᵥ z‖ ≤ ‖z‖ := by
  have hentries : ∀ i, 0 ≤ Hagi.Step.nsStep (d i)
      ∧ Hagi.Step.nsStep (d i) ≤ 1 :=
    fun i =>
      ⟨Hagi.Step.nsStep_nonneg _ (hd i).1 (by nlinarith [(hd i).1, (hd i).2]),
       Hagi.Step.nsStep_le_one _ (hd i).1
         (by nlinarith [(hd i).1, (hd i).2])⟩
  rw [nsMatrixStep_diagonal]
  have hvec : (Matrix.diagonal (fun i => Hagi.Step.nsStep (d i)) *ᵥ z)
      = fun i => Hagi.Step.nsStep (d i) * z i := by
    funext i
    exact Matrix.mulVec_diagonal _ _ i
  rw [hvec]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr ?_
  intro i
  have habs : |Hagi.Step.nsStep (d i) * z i| ≤ |z i| := by
    have h0 : 0 ≤ Hagi.Step.nsStep (d i) := (hentries i).1
    have h1 : Hagi.Step.nsStep (d i) ≤ 1 := (hentries i).2
    have hmulle : |Hagi.Step.nsStep (d i)| * |z i| ≤ 1 * |z i| := by
      apply mul_le_mul_of_nonneg_right
      · rw [abs_of_nonneg h0]; exact h1
      · exact abs_nonneg _
    calc |Hagi.Step.nsStep (d i) * z i|
        ≤ |Hagi.Step.nsStep (d i)| * |z i| :=
          le_of_eq (abs_mul _ _)
      _ ≤ 1 * |z i| := hmulle
      _ = |z i| := by rw [one_mul]
  exact habs.trans (norm_le_pi_norm z i)

/-- ORTHOGONAL EQUIVARIANCE: the NS iterate commutes with
orthogonal left/right factors — the iterate of `U A Vᵀ` is
`U (iterate A) Vᵀ`. Pure ring bookkeeping (the transpose product
folds to `V (AᵀA) Vᵀ`; the scalar identity matrix commutes past an
orthogonal `V`). The transport ingredient for the general spectral
route; no existence claims here. -/
theorem nsMatrixStep_orth {n : Type*} [Fintype n] [DecidableEq n]
    (A U V : Matrix n n ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    nsMatrixStep (U * A * Vᵀ) = U * nsMatrixStep A * Vᵀ := by
  have hVV : V * Vᵀ = 1 := by
    have hdet : IsUnit V.det := Matrix.isUnit_det_of_left_inverse hV
    rw [← Matrix.inv_eq_left_inv hV]
    exact Matrix.mul_nonsing_inv V hdet
  have hT : (U * A * Vᵀ)ᵀ * (U * A * Vᵀ) = V * (Aᵀ * A) * Vᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U (A * Vᵀ), hU, one_mul]
  have h3 : (3 : ℝ) • (1 : Matrix n n ℝ) - V * (Aᵀ * A) * Vᵀ
      = V * ((3 : ℝ) • (1 : Matrix n n ℝ) - Aᵀ * A) * Vᵀ := by
    have hV1 : V * ((3 : ℝ) • (1 : Matrix n n ℝ)) * Vᵀ
        = (3 : ℝ) • (1 : Matrix n n ℝ) := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hVV]
    rw [Matrix.mul_sub, Matrix.sub_mul, hV1]
  rw [nsMatrixStep_eq_smul, nsMatrixStep_eq_smul, hT, h3]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᵀ V
      (((3 : ℝ) • (1 : Matrix n n ℝ) - Aᵀ * A) * Vᵀ),
    hV, one_mul, Matrix.smul_mul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

/-- CONSUMER: the Muon step bound with `P` the NS iterate of a
diagonal input with entries in the scalar bracket `[0, 1]` — the
`hP` hypothesis is discharged by
`nsMatrixStep_diagonal_contraction` (sup-norm statement). -/
theorem muon_step_bound_ns_diagonal {n : Type} [Fintype n]
    [DecidableEq n] (d : n → ℝ) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (g : n → ℝ) :
    ‖muonDir (fun z => nsMatrixStep (Matrix.diagonal d) *ᵥ z) g‖
      ≤ ‖g‖ :=
  muon_step_bound _ g (fun z => nsMatrixStep_diagonal_contraction d hd z)

end Hagi.Step

/-!
# Newton–Schulz spectral-norm SVD transport

Route: the pinned Mathlib provides a spectral-norm Matrix API
— the scoped `Matrix.Norms.L2Operator` norm transported from
`EuclideanSpace` operator norms (`Mathlib/Analysis/CStarAlgebra/
Matrix.lean`, a `CStarRing`: `‖Aᴴ * A‖ = ‖A‖²`).

* `nsOrthogonal_mul_star_self` — companion `V Vᵀ = 1` of an
  orthogonal `VᵀV = 1` (det/unit route);
* `nsSpectralNorm_orth_inv` — THE missing piece: the L2
  operator (spectral) norm is invariant under orthogonal left/right
  multiplication, `‖U A Vᵀ‖₂ = ‖A‖₂` for `UᵀU = VᵀV = 1`;
* `ns_contraction_svd` — SVD-premise transport: for
  `A = U Σ Vᵀ` with singular values in the scalar bracket `[0,1]`
  the NS iterate has spectral norm ≤ 1 (equivariance +
  invariance + the diagonal case);
* `muon_step_bound_ns_svd` — CONSUMER: the Muon step bound on
  `EuclideanSpace ℝ n` with `hP` discharged under the SVD premise.

Honest boundary: the SVD is a PREMISE (no real-SVD existence
formalized here); one NS step only (iterate-lifting is a
mechanical induction on `nsMatrixStep_orth`, not claimed); the
norm is the scoped `Matrix.Norms.L2Operator` instance (the
ambient default matrix norm elsewhere in Hagi is untouched).
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Hagi.Step

variable {n : Type} [Fintype n] [DecidableEq n]

/-- ORTHOGONAL COMPANION: `Vᵀ V = 1` implies `V Vᵀ = 1`
(determinant/unit bookkeeping `nsMatrixStep_orth`
route). -/
theorem nsOrthogonal_mul_star_self (V : Matrix n n ℝ) (hV : Vᵀ * V = 1) :
    V * Vᵀ = 1 := by
  have hdet : IsUnit V.det := Matrix.isUnit_det_of_left_inverse hV
  rw [← Matrix.inv_eq_left_inv hV]
  exact Matrix.mul_nonsing_inv V hdet

/-- ORTHOGONAL INVARIANCE (the missing piece): the spectral
(L2 operator) norm is invariant under orthogonal left and right
factors — `‖U A Vᵀ‖₂ = ‖A‖₂` for `UᵀU = VᵀV = 1`. Route: C*
identity `‖XᴴX‖ = ‖X‖²` (left factor peeling, square
cancellation) + adjoint symmetry `‖Aᴴ‖ = ‖A‖` (right factor
peeling). -/
theorem nsSpectralNorm_orth_inv (A U V : Matrix n n ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    ‖U * A * Vᵀ‖ = ‖A‖ := by
  have hU' : Uᴴ * U = 1 := by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hU
  have hleft : ∀ Y X : Matrix n n ℝ, Yᴴ * Y = 1 → ‖Y * X‖ = ‖X‖ := by
    intro Y X hY
    have hkey : ‖Y * X‖ * ‖Y * X‖ = ‖X‖ * ‖X‖ := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self,
        ← Matrix.l2_opNorm_conjTranspose_mul_self]
      have hstep : (Y * X)ᴴ * (Y * X) = Xᴴ * X := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc Xᴴ Yᴴ (Y * X),
          ← Matrix.mul_assoc Yᴴ Y X, hY, Matrix.one_mul]
      rw [hstep]
    have h1 : 0 ≤ ‖Y * X‖ := norm_nonneg _
    have h2 : 0 ≤ ‖X‖ := norm_nonneg _
    nlinarith [h1, h2, sq_nonneg (‖Y * X‖ - ‖X‖), hkey]
  -- right peeling: ‖X * W‖ = ‖X‖ from W * Wᴴ = 1
  have hright : ∀ X W : Matrix n n ℝ, W * Wᴴ = 1 → ‖X * W‖ = ‖X‖ := by
    intro X W hW
    rw [← Matrix.l2_opNorm_conjTranspose, Matrix.conjTranspose_mul,
      hleft Wᴴ Xᴴ (by rw [Matrix.conjTranspose_conjTranspose]; exact hW),
      Matrix.l2_opNorm_conjTranspose]
  -- the right factor here is Vᵀ, whose companion is VᵀV = 1 itself
  have hW : Vᵀ * (Vᵀ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    exact hV
  exact (hright (U * A) Vᵀ hW).trans (hleft U A hU')

/-- SVD TRANSPORT CONTRACTION: for an input with a (premise-form)
SVD `A = U Σ Vᵀ` (`UᵀU = VᵀV = 1`, Σ diagonal with entries in the
scalar bracket `[0,1]`), the NS iterate has spectral norm ≤ 1.
Composition: equivariance `nsMatrixStep_orth` first, then
peel `Vᵀ` (right), then peel `U` (left), then collapse via
`nsMatrixStep_diagonal` + `l2_opNorm_diagonal` (sup-norm RHS) +
the scalar bracket. -/
theorem ns_contraction_svd (A U V : Matrix n n ℝ) (σ : n → ℝ)
    (hσ : ∀ i, 0 ≤ σ i ∧ σ i ≤ 1)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hA : A = U * Matrix.diagonal σ * Vᵀ) :
    ‖nsMatrixStep A‖ ≤ 1 := by
  rw [hA, nsMatrixStep_orth (Matrix.diagonal σ) U V hU hV,
    nsSpectralNorm_orth_inv (nsMatrixStep (Matrix.diagonal σ)) U V hU hV,
    nsMatrixStep_diagonal, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  have hnn : 0 ≤ nsStep (σ i) := nsStep_nonneg _ (hσ i).1
    (by nlinarith [(hσ i).1, (hσ i).2])
  have hle : nsStep (σ i) ≤ 1 := nsStep_le_one _ (hσ i).1
    (by nlinarith [(hσ i).1, (hσ i).2])
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

/-- CONSUMER: the Muon step bound on `EuclideanSpace ℝ n` with
`hP` DISCHARGED under the SVD premise — the honest spectral Muon
bound. `P` is the NS iterate acting as a continuous linear map;
contraction follows from the operator-norm bound
`ns_contraction_svd` (one step; general Muon statements with `hP`
as an explicit hypothesis are untouched). -/
theorem muon_step_bound_ns_svd (A U V : Matrix n n ℝ) (σ : n → ℝ)
    (hσ : ∀ i, 0 ≤ σ i ∧ σ i ≤ 1)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hA : A = U * Matrix.diagonal σ * Vᵀ)
    (g : EuclideanSpace ℝ n) :
    ‖muonDir
      (fun z => (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)
        (nsMatrixStep A)) z) g‖
      ≤ ‖g‖ := by
  refine muon_step_bound _ g fun z => ?_
  have h1 := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)
    (nsMatrixStep A)).le_opNorm z
  have h2 : ‖nsMatrixStep A‖ * ‖z‖ ≤ ‖z‖ :=
    mul_le_of_le_one_left (norm_nonneg z) (ns_contraction_svd A U V σ hσ hU hV hA)
  exact h1.trans h2

end Hagi.Step
