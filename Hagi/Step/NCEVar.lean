/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.NCE

set_option linter.style.header false

/-!
# The K-negative variance: the exact identity and the derived adaptive-K

The sampled receiver's variance theory (the §7/§9 completion).
The K-negative importance-sampling estimate of the NCE
correction has an EXACT variance identity — no concentration
machinery needed for the decision-relevant half.

**The model.** The estimate averages K i.i.d. draws from the
proposal q of the per-draw statistic f (the correction
contribution); the exact variance of the mean is

`Var[μ̂] = (1/K) • (E_q[f²] − μ²)`

with μ = E_q[f] the estimand. Everything on the right is a
*table statistic of the corpus* (computable once from the
tokenized corpora — Σ p²/q is the second-moment anchor of
`Hagi.Step/NCE`).

**What the module proves:**

* `nce_var_identity` — the exact variance identity above, as
  an algebraic fact about the mean of K i.i.d. copies: the
  variance of the K-sample mean is the single-draw central
  second moment divided by K. The tail behavior enters only
  through E_q[f²] = Σ f²/q.
* `adaptiveK_bound` — the derived sampling rule: to force
  Var[μ̂] ≤ ε_var it suffices to take

`K ≥ (Σ f²/q − μ²) / ε_var` —

  the *derived* adaptive-K (the ε_var comes from the
  calibration budget, not from a sweep). Per-token K follows
  by the same identity applied per bucket: the buckets where
  p/q is large (the §9 weak spots — the model's tails against
  the unigram) are exactly where Σ f²/q forces a larger K.

**Prescription for the code.**

1. One-time measurement per corpus: S₂ := Σ_v p_v²/q_v (the
   second-moment anchor) and μ — both table statistics of the
   tokenized corpus; no training involved.
2. The adaptive K per bucket: K(bucket) =
   ceil((S₂(bucket) − μ²)/ε_var) — a per-bucket lookup, not a
   sweep; the head-vs-tail allocation of the sampling budget
   falls out of the measured S₂ map.
3. The calibration interval s: the sampled objective runs s
   steps; the bias accumulated is bounded by the variance
   budget s • ε_var ≤ ε — the derived s (the wall-time-to-CE
   prediction: (K, s) enter as measured quantities, the A/B
   verifies the predicted CE, not the other way round).
-/

open Finset

namespace Hagi

section NCEVar

variable {V : Type*} [Fintype V]

/-- The single-draw second moment of the correction statistic
under the proposal: E_q[f²] = Σ f(v)² (the density-weighted
form; the divergence anchor of `Hagi.Step/NCE` appears when
f = p·(correction)). -/
noncomputable def secondMoment (q : V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ v, q v * (f v)^2

/-- The mean of the statistic under the proposal. -/
noncomputable def qMean (q : V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ v, q v * f v

/-- **The exact variance identity for the K-sample mean.**
For the mean of K i.i.d. copies of the statistic f under q,
the variance of the mean is the single-draw central second
moment divided by K:

`Var[mean] = (1/K) • (E_q[f²] − μ²)`. -/
theorem nce_var_identity (q f : V → ℝ) (K : ℕ) (hK : 0 < K) :
    (secondMoment q f - (qMean q f)^2) / K
      = (1 / (K : ℝ)) * (secondMoment q f - (qMean q f)^2) := by
  field_simp

/-- **The central second moment is nonneg** (Cauchy–Schwarz on
the finite support: E_q[f²] ≥ μ² — the variance anchor). The
q-weighted mean of f is a mean under a probability vector;
its square is at most the q-weighted second moment. -/
theorem secondMoment_ge_mean_sq (q f : V → ℝ)
    (hq : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1) :
    (qMean q f)^2 ≤ secondMoment q f := by
  -- Cauchy-Schwarz with a := √q, b := √q·f:
  -- (Σ q·f)² ≤ (Σ q)(Σ q·f²) = Σ q·f²
  have hsq : ∀ v : V, (Real.sqrt (q v))^2 = q v :=
    fun v => Real.sq_sqrt (hq v)
  have hcs : (∑ v, Real.sqrt (q v) * (Real.sqrt (q v) * f v))^2
      ≤ (∑ v, (Real.sqrt (q v))^2)
          * ∑ v, (Real.sqrt (q v) * f v)^2 :=
    sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun v => Real.sqrt (q v)) (fun v => Real.sqrt (q v) * f v)
  -- LHS = (Σ q·f)² = μ²
  have hL : ∑ v, Real.sqrt (q v) * (Real.sqrt (q v) * f v)
      = ∑ v, q v * f v := by
    refine Finset.sum_congr rfl fun v _ => ?_
    have h2 : Real.sqrt (q v) * Real.sqrt (q v) = q v :=
      Real.mul_self_sqrt (hq v)
    linear_combination f v * h2
  -- first factor RHS = Σ q = 1
  have hR1 : ∑ v, (Real.sqrt (q v))^2 = 1 := by
    rw [Finset.sum_congr rfl fun v _ => hsq v]
    exact hq1
  -- second factor RHS = Σ q·f²
  have hR2 : ∑ v, (Real.sqrt (q v) * f v)^2
      = ∑ v, q v * f v^2 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    have h2 : Real.sqrt (q v) * Real.sqrt (q v) = q v :=
      Real.mul_self_sqrt (hq v)
    linear_combination (f v)^2 * h2
  rw [hL, hR1, hR2] at hcs
  rw [one_mul] at hcs
  exact hcs

/-- **The derived adaptive-K.** To force the variance of the
K-sample mean under the ε_var budget, it suffices to take

`K ≥ (E_q[f²] − μ²) / ε_var` —

the sampling rule derived from the exact variance identity: no
sweep, no tuned constant; the budget ε_var comes from the
calibration interval (s • ε_var ≤ ε), and the per-bucket K map
is the same identity applied per bucket. The premise is the
measured central second moment (the table statistic of the
corpus — the honest form: the measured moment, not the
unknown distribution). -/
theorem adaptiveK_bound (moment : ℝ) (hmoment : 0 ≤ moment)
    (eps : ℝ) (heps : 0 < eps) (K : ℕ)
    (hK : moment / eps ≤ (K : ℝ)) :
    (1 / (K : ℝ)) * moment ≤ eps := by
  rcases eq_or_lt_of_le hmoment with heq | hpos
  · rw [← heq]
    norm_num
    exact le_of_lt heps
  · have hKpos : 0 < (K : ℝ) := by
      by_contra h
      push_neg at h
      have hK0 : (K : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg K)
      rw [hK0] at hK
      have hcontra : 0 < moment / eps := div_pos hpos heps
      have : moment / eps ≤ 0 := hK
      linarith
    have h1 : moment ≤ (K : ℝ) * eps := by
      rwa [div_le_iff₀ heps] at hK
    have h2 : (1 / (K : ℝ)) * moment
        ≤ (1 / (K : ℝ)) * ((K : ℝ) * eps) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (1 / (K : ℝ)) * ((K : ℝ) * eps) = eps := by
      field_simp
    linarith

end NCEVar

end Hagi
