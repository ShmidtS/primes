/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic


/-!
# Newton–polar iteration, scalar core (R379)

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
### T-step quadratic convergence (R380)

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
### Convergence (R382)

Turning the R380 rate into an actual limit: for
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

/-- **Монотонный спуск полярного Ньютона (R423)**:
при x ≥ 1: newtonStep x ≤ x (нестрого),
при x > 1: строго. Вместе с R380/R382
(quad-скорость + сходимость)
траектория полностью
сертифицирована: монотонно
спускается и квадратично
сжимается к 1. -/
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


/-- **Скобка траектории полярного Ньютона (R424)**:
1 ≤ newtonIter x₀ T ≤ x₀ при x₀ ≥ 1 —
инвариант вдоль всей
траектории (индукция:
спуск R423 + инвариант ≥1
R53). Траектория живёт в
отрезке [1, x₀] и монотонно
спускается к 1 с quad-скоростью. -/
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
