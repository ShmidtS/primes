/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# Exponential-weights routing

The per-step potential bound for Hedge routing, the product
telelescope, and the router regret bound.
-/

open Real Finset Set

namespace Hagi

theorem exp_neg_le_quad (y : ℝ) (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  by_cases hy0 : y = 0
  · simp [hy0]
  set f : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - Real.exp (-x) with hf
  have hderiv : ∀ x : ℝ, HasDerivAt f (x - 1 + Real.exp (-x)) x := by
    intro x
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
      have h3 : HasDerivAt (fun x => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
      have h4 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) (2 * x / 2) x := h3.div_const (2 : ℝ)
      simpa using h4
    have hA : HasDerivAt (fun x : ℝ => x ^ 2 / 2 - x) (x - 1) x :=
      HasDerivAt.sub h2 (hasDerivAt_id x)
    have hB : HasDerivAt (fun x : ℝ => 1 + (x ^ 2 / 2 - x)) (0 + (x - 1)) x :=
      HasDerivAt.add (hasDerivAt_const x (1 : ℝ)) hA
    have hC : HasDerivAt (fun x : ℝ => 1 + (x ^ 2 / 2 - x) - Real.exp (-x))
      ((0 + (x - 1)) - (-Real.exp (-x))) x := by
      have hE : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
        have hE0 : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) x := (hasDerivAt_id x).neg
        have hE2 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * -1) x :=
          HasDerivAt.comp x (hasDerivAt_exp (-x)) hE0
        exact hE2.congr_deriv (by ring)
      exact HasDerivAt.sub hB hE
    exact hC.congr_of_eventuallyEq (by filter_upwards with z; ring) |>.congr_deriv (by ring)
  -- MVT on [0, y]
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hcont : ContinuousOn f (Set.Icc 0 y) :=
    (show Continuous f from by continuity).continuousOn
  obtain ⟨ξ, hξm, hξ2⟩ := exists_hasDerivAt_eq_slope f
    (fun x => x - 1 + Real.exp (-x)) hypos hcont
    (fun x hx => hderiv x)
  -- f y - f 0 = f'(ξ) * (y - 0), and f' ξ ≥ 0
  have hposξ : 0 ≤ ξ - 1 + Real.exp (-ξ) := by
    have := add_one_le_exp (-ξ)
    linarith
  have hval : (ξ - 1 + Real.exp (-ξ)) = (f y - f 0) / (y - 0) := hξ2
  have h0 : f 0 = 0 := by simp [hf]
  rw [h0, sub_zero] at hval
  have hmul : (ξ - 1 + Real.exp (-ξ)) * y = f y := by
    rw [hval]
    rw [div_mul_eq_mul_div, div_eq_iff (by linarith : (y:ℝ) - 0 ≠ 0)]
    ring
  -- f y = y · f' ξ ≥ 0
  have hnn : 0 ≤ (ξ - 1 + Real.exp (-ξ)) * y := by positivity
  rw [hmul] at hnn
  simp only [hf] at hnn
  linarith

open Finset

/-- For losses `l i ∈ [0, 1]`, weights `p` with `p i ≥ 0` and
`Σ p = 1`, and `η ∈ [0, 1]`:
`Σ p i * exp (-η * l i) ≤ 1 - η * Σ p i * l i + η ^ 2 / 2`. -/
theorem hedge_step {ι : Type} [Fintype ι] (p l : ι → ℝ) (eta : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hl : ∀ i, 0 ≤ l i ∧ l i ≤ 1) (heta : 0 ≤ eta ∧ eta ≤ 1) :
    ∑ i, p i * Real.exp (-eta * l i) ≤ 1 - eta * ∑ i, p i * l i + eta ^ 2 / 2 := by
  have hquad : ∀ i, Real.exp (-eta * l i) ≤ 1 - eta * l i + (eta * l i) ^ 2 / 2 := by
    intro i
    have h := exp_neg_le_quad (eta * l i) (mul_nonneg heta.1 (hl i).1)
    convert h using 1 <;> ring
  have hmul : ∀ i, p i * Real.exp (-eta * l i)
      ≤ p i * (1 - eta * l i + (eta * l i) ^ 2 / 2) :=
    fun i => mul_le_mul_of_nonneg_left (hquad i) (hp i)
  have hsumle := Finset.sum_le_sum (s := Finset.univ) (f := fun i => p i * Real.exp (-eta * l i))
    (g := fun i => p i * (1 - eta * l i + (eta * l i) ^ 2 / 2)) (fun i _ => hmul i)
  have hsplit : ∑ i, p i * (1 - eta * l i + (eta * l i) ^ 2 / 2)
      = (∑ i, p i) - eta * (∑ i, p i * l i)
        + ∑ i, p i * ((eta * l i) ^ 2 / 2) := by
    have e1 : ∑ i : ι, p i * (1 - eta * l i + (eta * l i) ^ 2 / 2)
        = ∑ i : ι, (p i - eta * (p i * l i) + p i * ((eta * l i) ^ 2 / 2)) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [e1]
    have e2 : ∑ i : ι, (p i - eta * (p i * l i) + p i * ((eta * l i) ^ 2 / 2))
        = (∑ i : ι, (p i - eta * (p i * l i))) + ∑ i : ι, p i * ((eta * l i) ^ 2 / 2) :=
      sum_add_distrib
    have e3 : ∑ i : ι, (p i - eta * (p i * l i))
        = (∑ i : ι, p i) - eta * (∑ i : ι, p i * l i) := by
      rw [sum_sub_distrib]
      rw [Finset.mul_sum (s := Finset.univ) (f := fun i => p i * l i) (a := eta)]
    rw [e2, e3]
  -- last term ≤ η²/2 · Σp = η²/2 (since l ≤ 1)
  have hsq : ∀ i, p i * ((eta * l i) ^ 2 / 2) ≤ p i * (eta ^ 2 / 2) := by
    intro i
    have h1 : (eta * l i) ^ 2 ≤ eta ^ 2 := by
      have := hl i
      nlinarith [sq_nonneg (eta * l i - eta)]
    calc p i * ((eta * l i) ^ 2 / 2) ≤ p i * (eta ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (hp i)
      _ = p i * (eta ^ 2 / 2) := rfl
  have hlast : ∑ i, p i * ((eta * l i) ^ 2 / 2) ≤ eta ^ 2 / 2 := by
    calc ∑ i, p i * ((eta * l i) ^ 2 / 2)
        ≤ ∑ i, p i * (eta ^ 2 / 2) :=
          Finset.sum_le_sum (s := Finset.univ) (f := fun i => p i * ((eta * l i) ^ 2 / 2))
            (g := fun i => p i * (eta ^ 2 / 2)) (fun i _ => hsq i)
      _ = (∑ i, p i) * (eta ^ 2 / 2) :=
          (Finset.sum_mul (s := Finset.univ) (f := fun i => p i)
            (a := eta ^ 2 / 2)).symm
      _ = eta ^ 2 / 2 := by rw [hsum, one_mul]
  calc ∑ i, p i * Real.exp (-eta * l i)
      ≤ (∑ i, p i) - eta * (∑ i, p i * l i)
        + ∑ i, p i * ((eta * l i) ^ 2 / 2) := hsplit ▸ hsumle
    _ ≤ (∑ i, p i) - eta * (∑ i, p i * l i) + eta ^ 2 / 2 := by
          have hadd : ∑ i, p i * ((eta * l i) ^ 2 / 2) ≤ eta ^ 2 / 2 := hlast
          linarith
    _ = 1 - eta * (∑ i, p i * l i) + eta ^ 2 / 2 := by
          rw [hsum]

theorem hedge_telescope (u : ℕ → ℝ) (hnn : ∀ t, (0:ℝ) ≤ 1 + u t) (T : ℕ) :
    ∏ t ∈ Finset.range T, (1 + u t) ≤ Real.exp (∑ t ∈ Finset.range T, u t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := ih
      have h2 : (1:ℝ) + u T ≤ Real.exp (u T) := by
        have := add_one_le_exp (u T)
        linarith
      calc ∏ t ∈ Finset.range (T+1), (1 + u t)
          = (∏ t ∈ Finset.range T, (1 + u t)) * (1 + u T) :=
            Finset.prod_range_succ (fun t => 1 + u t) T
      _ ≤ Real.exp (∑ t ∈ Finset.range T, u t) * Real.exp (u T) :=
          mul_le_mul h1 h2 (hnn T) (le_of_lt (Real.exp_pos (∑ t ∈ Finset.range T, u t)))
      _ = Real.exp (∑ t ∈ Finset.range T, u t + u T) := by rw [Real.exp_add]
      _ = Real.exp (∑ t ∈ Finset.range (T+1), u t) := by
          rw [Finset.sum_range_succ]

/-- Assuming the survivor bound `(1/K) * exp (-η * Lstar) ≤
exp (-η * A + T * η ^ 2 / 2)` with `η > 0` and `K > 0`, the
cumulative-loss gap satisfies `A - Lstar ≤ log K / η + η * T / 2`.
At `η = √(ln K / T)` this is `2√(T * ln K)`. -/
theorem router_regret_bound (K T : ℕ) (eta A Lstar : ℝ)
    (hK : 0 < K) (heta : 0 < eta)
    (hsurv : (1:ℝ) / K * Real.exp (-eta * Lstar)
      ≤ Real.exp (-eta * A + T * eta ^ 2 / 2)) :
    A - Lstar ≤ Real.log K / eta + eta * T / 2 := by
  have hlogle : Real.log ((1:ℝ) / K * Real.exp (-eta * Lstar))
      ≤ -eta * A + T * eta ^ 2 / 2 := by
    have h1 := Real.log_le_log (x := (1:ℝ) / K * Real.exp (-eta * Lstar))
      (y := Real.exp (-eta * A + T * eta ^ 2 / 2)) (by positivity) hsurv
    rw [Real.log_exp] at h1
    exact h1
  rw [Real.log_mul (by positivity) (by positivity)] at hlogle
  rw [Real.log_exp] at hlogle
  -- log(1/K) = -log K
  have hlog1 : Real.log ((1:ℝ) / K) = -Real.log K := by
    rw [Real.log_div (by norm_num) (by positivity)]
    norm_num
  rw [hlog1] at hlogle
  -- now: -log K - eta*Lstar <= -eta*A + T*eta^2/2; divide by eta and finish
  field_simp
  linarith

end Hagi
