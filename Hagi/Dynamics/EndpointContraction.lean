/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Dynamics.Contraction

/-!
# EndpointContraction — the looped-model fixed-point budget

The HAGI reading of "looped models done right": a contractive
recurrent map with drifting inputs obeys the BIVARIATE
contraction law

  x_{t+1} ≤ κ · x_t + β · c_t,

where x_t is the state-to-endpoint distance and c_t the
per-step input/config drift. The finite-depth error then splits
into a VANISHING initial-condition part (κ^T) and an
ACCUMULATED input part — geometric memory with exponential
forgetting of the start:

* `endpoint_bivariate_bound`: the general law — κ^T · x₀ plus
  the κ-weighted reversed sum of the input drifts;
* `endpoint_geometric_tail`: if the input drift is bounded
  (c_t ≤ cbar), the endpoint error is at most κ^T · x₀ +
  β·cbar/(1 − κ): depth beyond log(1/ε) buys nothing — the
  truncated-depth and endpoint views coincide;
* `endpoint_depth_budget`: to push the initial-condition part
  under ε it suffices to run T ≥ log(1/ε)/log(1/κ) steps —
  the explicit loop-count budget (the "when to stop looping"
  answer, conditional on the contraction premises).
-/

namespace Hagi

open Finset

/-- **The bivariate contraction law**: state error to the
endpoint under drifting inputs — vanishing initial part plus
κ-weighted accumulated input drift. -/
theorem endpoint_bivariate_bound (x c : ℕ → ℝ) (κ β : ℝ)
    (T : ℕ) (hκ : 0 ≤ κ) (hκ1 : κ < 1) (hβ : 0 ≤ β)
    (hstep : ∀ t, x (t + 1) ≤ κ * x t + β * c t) :
    x T ≤ κ ^ T * x 0
      + β * ∑ i ∈ Finset.range T, κ ^ i * c (T - 1 - i) := by
  have hexact : ∀ t : ℕ,
      x t ≤ κ ^ t * x 0
        + β * ∑ i ∈ Finset.range t, κ ^ i * c (t - 1 - i) := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
        have h1 := hstep n
        have hih := ih
        have hsum : β * ∑ i ∈ Finset.range (n + 1), κ ^ i * c (n - i)
            = κ * (β * ∑ i ∈ Finset.range n, κ ^ i * c (n - 1 - i))
              + β * c n := by
          have hsucc := Finset.sum_range_succ'
            (fun i => κ ^ i * c (n - i)) n
          rw [hsucc]
          simp only [Nat.sub_zero, pow_zero, mul_one]
          have hbody : ∑ k ∈ Finset.range n, κ ^ (k + 1) * c (n - (k + 1))
              = κ * ∑ i ∈ Finset.range n, κ ^ i * c (n - 1 - i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            have hke : k + 1 = (k : ℕ) + 1 := rfl
            rw [hke, pow_succ]
            have hn1 : n - (k + 1) = n - 1 - k := by omega
            rw [hn1]
            ring
          rw [hbody]
          ring
        calc x (n + 1) ≤ κ * x n + β * c n := h1
          _ ≤ κ * (κ ^ n * x 0
                + β * ∑ i ∈ Finset.range n, κ ^ i * c (n - 1 - i))
              + β * c n := by
                nlinarith [mul_le_mul_of_nonneg_left hih hκ]
          _ = κ ^ (n + 1) * x 0
              + β * ∑ i ∈ Finset.range (n + 1), κ ^ i * c (n - i) := by
                rw [pow_succ]
                nlinarith [hsum]
  exact hexact T


/-- **The geometric tail**: bounded input drift caps the
endpoint error at κ^T · x₀ + β·cbar/(1 − κ) — depth beyond the
geometric scale buys nothing; truncated depth and the endpoint
view coincide. -/
theorem endpoint_geometric_tail (x c : ℕ → ℝ) (κ β cbar : ℝ)
    (T : ℕ) (hκ : 0 ≤ κ) (hκ1 : κ < 1) (hβ : 0 ≤ β)
    (hcbar : 0 ≤ cbar) (hcbound : ∀ t, c t ≤ cbar)
    (hstep : ∀ t, x (t + 1) ≤ κ * x t + β * c t) :
    x T ≤ κ ^ T * x 0 + β * cbar / (1 - κ) := by
  have hmain := endpoint_bivariate_bound x c κ β T hκ hκ1 hβ hstep
  have hsum : ∑ i ∈ Finset.range T, κ ^ i * c (T - 1 - i)
      ≤ cbar / (1 - κ) := by
    have h1 : ∑ i ∈ Finset.range T, κ ^ i * c (T - 1 - i)
        ≤ cbar * ∑ i ∈ Finset.range T, κ ^ i := by
      have hsum' : ∑ i ∈ Finset.range T, κ ^ i * c (T - 1 - i)
          ≤ ∑ i ∈ Finset.range T, κ ^ i * cbar :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hcbound _) (pow_nonneg hκ _)
      refine le_trans hsum' ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => le_of_eq (mul_comm _ _)
    have h2 := geom_sum_le_inv κ hκ hκ1 T
    have h3 : cbar * ∑ i ∈ Finset.range T, κ ^ i ≤ cbar * (1 / (1 - κ)) :=
      mul_le_mul_of_nonneg_left h2 hcbar
    have h4 : cbar * (1 / (1 - κ)) = cbar / (1 - κ) := by field_simp
    linarith
  have hfin : β * (cbar / (1 - κ)) = β * cbar / (1 - κ) := by
    field_simp
  have h1' : β * ∑ i ∈ Finset.range T, κ ^ i * c (T - 1 - i)
      ≤ β * (cbar / (1 - κ)) := mul_le_mul_of_nonneg_left hsum hβ
  linarith

/-- **The explicit loop-count budget**: to push the
initial-condition part of the endpoint error under ε it
suffices to run T steps with (1/κ)^T ≥ x₀/ε — the "when to
stop looping" answer, conditional on the contraction premises
(the looped-model truncated-depth certificate). -/
theorem endpoint_depth_budget (x c : ℕ → ℝ) (κ β cbar ε : ℝ)
    (T : ℕ) (hκ : 0 < κ) (hκ1 : κ < 1) (hβ : 0 ≤ β)
    (hcbar : 0 ≤ cbar) (hcbound : ∀ t, c t ≤ cbar)
    (hstep : ∀ t, x (t + 1) ≤ κ * x t + β * c t)
    (heps : 0 < ε)
    (hT : x 0 / ε ≤ (1 / κ) ^ T) :
    x T ≤ β * cbar / (1 - κ) + ε := by
  have htail := endpoint_geometric_tail x c κ β cbar T hκ.le hκ1 hβ hcbar
    hcbound hstep
  have hbound : κ ^ T * x 0 ≤ ε := by
    rcases le_or_gt (x 0) 0 with hx | hx
    · have hnonneg : 0 ≤ κ ^ T := pow_nonneg hκ.le _
      nlinarith [hnonneg, hx]
    · have hposq : (0:ℝ) < (1 / κ) ^ T := by positivity
      have hdiv : (1 / κ) ^ T ≥ x 0 / ε := hT
      have hinv : ((1 / κ) ^ T)⁻¹ ≤ (x 0 / ε)⁻¹ :=
        (inv_le_inv₀ hposq (by positivity)).2 hdiv
      have hkeq : ((1 / κ) ^ T)⁻¹ = κ ^ T := by
        rw [one_div, inv_pow, inv_inv]
      rw [hkeq] at hinv
      rw [inv_div] at hinv
      rwa [le_div_iff₀ hx] at hinv
  linarith

end Hagi

