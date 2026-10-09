/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# TokenWeightBias — the token-weighting bias law
(source arXiv:2610.02179v1 Eq. (5))

The multi-teacher loss with token-count weights Tᵢ and
domain gradients gᵢ has the exact decomposition:

  (∑ Tᵢ gᵢ) / (∑ Tᵢ) = ḡ + Cov(T, g) / T̄

— the token-weighted direction equals the plain domain mean
plus a covariance bias: when long answers correlate with
their gradients, the effective domain mixture drifts (their
measurement: math got ~44% effective weight under
global-token averaging vs 25% under domain-balanced).

* `token_weight_decomposition`: the exact identity (finite
  sums, no asymptotics) — the controller-relevant content:
  equal prompt counts do not mean equal domain weights;
  the bias term is exactly Cov(T,g)/T̄;
* `zero_bias_iff_uncorrelated`: the bias vanishes EXACTLY
  when the token counts are uncorrelated with the gradients
  on the family — the certification condition for
  "domain-balanced" weighting.

This feeds the ControllerPolicy line: weights wᵢ,ₜ are part
of the controller state, and this law is the measurable
reason fixed averaging is not neutral transport.
-/

namespace Hagi

open Finset

variable {n : ℕ}

/-- **The token-weighting bias law (Eq. 5)**: the
token-weighted average gradient is the plain mean plus the
covariance bias Cov(T,g)/T̄ — an exact finite identity. -/
theorem token_weight_decomposition (T g : Fin n → ℝ)
    (hTpos : 0 < ∑ i, T i) :
    (∑ i, T i * g i) / (∑ i, T i)
      = (∑ i, g i) / n
        + ((∑ i, (T i - (∑ j, T j) / n) * (g i - (∑ j, g j) / n)) / n)
          / ((∑ j, T j) / n) := by
  have hn : (n : ℝ) ≠ 0 := by
    cases n with
    | zero => exact absurd hTpos (by simp)
    | succ m => exact_mod_cast (Nat.succ_ne_zero m)
  have hTne : (∑ i, T i) ≠ 0 := ne_of_gt hTpos
  -- covariance expansion: C = X - S*G/n
  have hexp : ∑ i, (T i - (∑ j, T j) / n) * (g i - (∑ j, g j) / n)
      = (∑ i, T i * g i) - (∑ i, T i) * (∑ i, g i) / n := by
    have h1 : ∀ i, (T i - (∑ j, T j) / n) * (g i - (∑ j, g j) / n)
        = T i * g i - (T i * ((∑ j, g j) / n)
          + g i * ((∑ j, T j) / n)
          - ((∑ j, T j) / n) * ((∑ j, g j) / n)) := by
      intro i
      ring
    have hA : ∑ i, T i * ((∑ j, g j) / (n : ℝ))
        = (∑ i, T i) * ((∑ j, g j) / (n : ℝ)) :=
      (Finset.sum_mul Finset.univ (fun i => T i) ((∑ j, g j) / (n : ℝ))).symm
    have hB : ∑ i, g i * ((∑ j, T j) / (n : ℝ))
        = ((∑ j, T j) / (n : ℝ)) * (∑ i, g i) :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
        |>.trans (Finset.mul_sum Finset.univ (fun i => g i)
          ((∑ j, T j) / (n : ℝ))).symm
    have hC : (∑ j, T j) / (n : ℝ) * ((∑ j, g j) / (n : ℝ))
        * (Fintype.card (Fin n) : ℝ)
        = n * (((∑ j, T j) / (n : ℝ)) * ((∑ j, g j) / (n : ℝ))) := by
      norm_num
      ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hA, hB]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
    field_simp
    ring
  -- the two-divisors collapse: (C/n)/(S/n) = C/S
  have hdiv : ((∑ i, (T i - (∑ j, T j) / n) * (g i - (∑ j, g j) / n)) / n)
      / ((∑ j, T j) / n)
      = (∑ i, (T i - (∑ j, T j) / n) * (g i - (∑ j, g j) / n))
        / (∑ j, T j) := by
    rw [div_div, mul_comm]
    rw [show ((∑ j, T j) / n) * n = ∑ j, T j from div_mul_cancel₀ _ hn]
  rw [hdiv, hexp]
  field_simp
  ring

/-- **Zero bias ⟺ uncorrelated**: the token-weighting bias
vanishes EXACTLY when the counts and the gradients are
uncorrelated on the family — the certification condition
for a genuinely domain-balanced weighting (equal prompts do
not certify it; zero covariance does). -/
theorem zero_bias_iff_uncorrelated (T g : Fin n → ℝ)
    (hTpos : 0 < ∑ i, T i) :
    ((∑ i, T i * g i) / (∑ i, T i)) = (∑ i, g i) / n
      ↔ ∑ i, (T i - (∑ j, T j) / n) * (g i - (∑ j, g j) / n) = 0 := by
  have hdec := token_weight_decomposition T g hTpos
  constructor
  · intro h
    rw [h] at hdec
    have hn : (n : ℝ) ≠ 0 := by
      cases n with
      | zero => exact absurd hTpos (by simp)
      | succ m => exact_mod_cast (Nat.succ_ne_zero m)
    have hTbar : (∑ j, T j) / n ≠ 0 := by
      intro h0
      have hc : ((∑ j : Fin n, T j) / n) * n = 0 := by rw [h0, zero_mul]
      have hcancel : ((∑ j : Fin n, T j) / n) * n = ∑ j, T j :=
        div_mul_cancel₀ _ hn
      exact absurd (by linarith) (ne_of_gt hTpos)
    have hz : ((∑ i, (T i - (∑ j, T j) / n) * (g i - (∑ j, g j) / n)) / n)
        / ((∑ j, T j) / n) = 0 := by linarith
    have hne : ((∑ j, T j) / n) ≠ 0 := hTbar
    have h1 : (∑ i, (T i - (∑ j, T j) / n) * (g i - (∑ j, g j) / n)) / n = 0 := by
      rcases div_eq_zero_iff.mp hz with h | h
      · exact h
      · exact absurd h hne
    have hn2 : (n : ℝ) ≠ 0 := hn
    exact (div_eq_zero_iff.mp h1).resolve_right hn2
  · intro h
    rw [hdec, h, zero_div, zero_div, add_zero]


end Hagi
