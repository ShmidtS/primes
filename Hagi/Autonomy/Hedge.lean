/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# R74: exponential-weights routing (roadmap #4, step 1)
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
    have hC : HasDerivAt (fun x : ℝ => 1 + (x ^ 2 / 2 - x) - Real.exp (-x)) ((0 + (x - 1)) - (-Real.exp (-x))) x := by
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

/-- **Hedge per-step bound (roadmap #4, step 1)**: for losses
l ∈ [0,1], any mixed weight p with Σp = 1, and η ∈ [0,1]:
Σ_i p_i e^{−ηl_i} ≤ 1 − η⟨p,l⟩ + η²/2 — the exp_neg quad
bound averaged against the weights, with l² ≤ 1. This is
the multiplicative potential drop of exponential-weights
routing: the router's potential never collapses. -/
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

end Hagi
