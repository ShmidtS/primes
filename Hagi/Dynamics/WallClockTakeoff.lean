/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Dynamics.FastGrowth
import Hagi.Probability.ConditionalSuccess
set_option linter.style.header false

/-!
# R110: wall-clock takeoff — per-cycle time-rate k ⟹ exponential in WALL-CLOCK time

The audit's §18 ask: growth must be measured against WALL-CLOCK
time, not generation count or FLOPs. If every cycle t costs τ_t of
wall-clock and multiplies capability by ≥ (1 + k·τ_t) — the
per-cycle multiplicative law with rate k per unit time — then the
capability at accumulated wall time T_wall = Στ is exponential in
T_wall with rate k (up to explicit second-order slack).

Results:

* `log_one_add_ge_sub_half_sq` — the honest per-factor
  inequality: log(1+x) ≥ x − x²/2 for ALL x ≥ 0 (derivative
  analysis: d/dt[log(1+t) − t + t²/2] = t²/(1+t) ≥ 0, f(0)=0).
  The audit's x ∈ [0,1] restriction is NOT needed — the bound
  holds on the whole nonneg half-line.
* `exp_le_one_add` — the exponentiated form exp(x − x²/2) ≤ 1+x.
* `wallclock_takeoff_product` — the product law: C_T ≥
  C₀·∏_{t<T}(1 + k·τ_t) (induction, the per-cycle law composed).
* `wallclock_takeoff` (MAIN) — C_T ≥ C₀·exp(k·Στ_t −
  (k²/2)·Στ_t²): the exponent is k·T_wall minus the EXPLICIT
  second-order slack (k²/2)Στ² — the price of discretization,
  paid only by long cycles.
* `wallclock_takeoff_small_steps` — the regime corollary: if
  k·τ_t ≤ η for all t, the slack collapses to (η/2)·k·T_wall and
  C_T ≥ C₀·exp(k·T_wall·(1 − η/2)). As η → 0 (cheap cycles) the
  effective rate approaches k exactly — the audit's "dC/dT ≥ kC
  ⟹ exp(kT)" in honest discrete form.
* `counted_takeoff_exp` — the exp-form twin of R83's
  `capability_takeoff_counted` (needed for the composition).
* `wallclock_rate_from_cone` (composition) — under the R107
  cone/success machinery (per-SUCCESS multiplier (1+α), success
  count concentrated at p₀T − Δ per R95), with CONSTANT cycle
  cost τ, the wall-clock rate constant is exactly

  k_eff = p₀·ln(1+α)/τ

  with the explicit concentration correction −ln(1+α)·Δ:
  C_T ≥ C₀·exp(k_eff·W − ln(1+α)·Δ), W = T·τ.
* `wallclock_rate_from_cone_concentrated` — instantiates Δ with
  R95's Hoeffding value √(2T·log(1/δ)).

Honesty notes: (a) the per-cycle law C_{t+1} ≥ (1+kτ_t)·C_t is a
HYPOTHESIS (as in R83's capability_multiplicative — the composition
law, not a derivation); what THIS module derives is the wall-clock
exponent: the second-order slack algebra and the k_eff composition.
(b) the success-count floor in the composition is given as a
deterministic hypothesis; the probabilistic guarantee that it holds
w.p. ≥ 1−δ is R95's `success_count_lower_p0`, NOT reproved here.
-/

open Real Finset

namespace Hagi

/-! ## The per-factor inequality -/

/-- **The honest per-factor inequality**: log(1+x) ≥ x − x²/2 for
ALL x ≥ 0. Proof: f(t) := log(1+t) − t + t²/2 has
f'(t) = t²/(1+t) ≥ 0 on t > 0 and f(0) = 0, so f is monotone on
[0,x]. The audit's x ∈ [0,1] restriction is not needed. -/
theorem log_one_add_ge_sub_half_sq {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  -- the derivative fact: f' t = t²/(1+t) for t ≥ 0
  have hderivAt : ∀ t : ℝ, 0 ≤ t → HasDerivAt
      (fun t => Real.log (1 + t) - t + t ^ 2 / 2) (t ^ 2 / (1 + t)) t := by
    intro t ht
    have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + t)) t := by
      have hc : HasDerivAt (fun t : ℝ => 1 + t) 1 t := (hasDerivAt_id' t).const_add 1
      have hl2 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) ((1 + t)⁻¹ * 1) t := by
        have := (Real.hasDerivAt_log
          (ne_of_gt (by linarith : (0:ℝ) < 1 + t))).comp t hc
        exact this
      simpa [div_eq_inv_mul] using hl2
    have hsq : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
      simpa using (hasDerivAt_pow 2 t).div_const 2
    have hf' : HasDerivAt (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
        (1 / (1 + t) - 1 + t) t := (hlog.sub (hasDerivAt_id' t)).add hsq
    have heq : 1 / (1 + t) - 1 + t = t ^ 2 / (1 + t) := by
      field_simp
      ring
    rw [heq] at hf'
    exact hf'
  -- continuity on the closed interval
  have hcont : ContinuousOn (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
      (Set.Icc 0 x) := by
    have h1 : ContinuousOn (fun t : ℝ => 1 + t) (Set.Icc 0 x) :=
      (continuous_const.add continuous_id).continuousOn
    have h2 : ContinuousOn (fun t : ℝ => Real.log (1 + t)) (Set.Icc 0 x) :=
      ContinuousOn.comp Real.continuousOn_log h1
        (fun t ht => by
          change (1:ℝ) + t ∉ {(0:ℝ)}
          intro h
          simp only [Set.mem_singleton_iff] at h
          exact absurd h (by have := ht.1; linarith))
    have h3 : ContinuousOn (fun t : ℝ => t ^ 2 / 2) (Set.Icc 0 x) :=
      Continuous.continuousOn
        (Continuous.div (continuous_id.pow 2) continuous_const (by norm_num))
    exact (h2.sub continuous_id.continuousOn).add h3
  -- differentiability + nonneg derivative on the interior
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
      (interior (Set.Icc 0 x)) := by
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    exact (hderivAt t ht0).differentiableAt.differentiableWithinAt
  have hnn : ∀ t ∈ interior (Set.Icc 0 x),
      0 ≤ deriv (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2) t := by
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    rw [(hderivAt t ht0).deriv]
    exact div_nonneg (sq_nonneg t) (by linarith : (0:ℝ) ≤ 1 + t)
  have hmono : MonotoneOn (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
      (Set.Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hcont hdiff hnn
  have m0 : (0:ℝ) ∈ Set.Icc 0 x := ⟨le_rfl, hx⟩
  have mx : x ∈ Set.Icc 0 x := ⟨hx, le_rfl⟩
  have hfx := hmono m0 mx hx
  beta_reduce at hfx
  have hzero : Real.log (1 + 0) - 0 + 0 ^ 2 / 2 = (0:ℝ) := by
    simp [Real.log_one]
  rw [hzero] at hfx
  linarith

/-- **The exponentiated per-factor bound**: exp(x − x²/2) ≤ 1 + x
for all x ≥ 0 — each multiplicative factor (1+x) dominates its
first-order exponent minus the second-order slack. -/
theorem exp_le_one_add {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (x - x ^ 2 / 2) ≤ 1 + x := by
  have h2 : Real.exp (x - x ^ 2 / 2) ≤ Real.exp (Real.log (1 + x)) :=
    Real.exp_le_exp.mpr (log_one_add_ge_sub_half_sq hx)
  exact h2.trans_eq (Real.exp_log (by linarith : (0:ℝ) < 1 + x))

/-! ## The per-cycle time-rate hypothesis -/

/-- **The per-cycle time-rate law (hypothesis form)**: each cycle
t costs τ_t of wall-clock and multiplies capability by ≥ (1 + k·τ_t)
— the multiplicative law with rate k per unit of wall-clock time.
This is the HYPOTHESIS the takeoff theorems below compose (as in
R83's `capability_multiplicative`: the composition law, not a
derivation from deeper principles). -/
def per_cycle_time_rate (C τ : ℕ → ℝ) (k : ℝ) : Prop :=
  ∀ t, C (t + 1) ≥ C t * (1 + k * τ t)

/-! ## The product law -/
/-- **The product form of the per-cycle time-rate law**: if every
cycle t multiplies capability by ≥ (1 + k·τ_t) with k, τ_t ≥ 0,
then after T cycles C_T ≥ C₀·∏_{t<T}(1 + k·τ_t) — the T-fold
composition (induction, as in `capability_multiplicative` but
with the time-indexed factor). -/
theorem wallclock_takeoff_product (C τ : ℕ → ℝ) (k : ℝ)
    (hk : 0 ≤ k) (hτ : ∀ t, 0 ≤ τ t)
    (hstep : per_cycle_time_rate C τ k)
    (T : ℕ) :
    C T ≥ C 0 * ∏ t ∈ Finset.range T, (1 + k * τ t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hstep T
      rw [Finset.prod_range_succ]
      have hpos : (0:ℝ) ≤ ∏ t ∈ Finset.range T, (1 + k * τ t) :=
        Finset.prod_nonneg fun t _ =>
          add_nonneg zero_le_one (mul_nonneg hk (hτ t))
      calc C (T + 1) ≥ C T * (1 + k * τ T) := h1
        _ ≥ (C 0 * ∏ t ∈ Finset.range T, (1 + k * τ t)) * (1 + k * τ T) := by
            refine mul_le_mul_of_nonneg_right ih ?_
            exact add_nonneg zero_le_one (mul_nonneg hk (hτ T))
        _ = C 0 * ((∏ t ∈ Finset.range T, (1 + k * τ t)) * (1 + k * τ T)) := by
            ring

/-! ## The wall-clock exponent (MAIN) -/

/-- Product monotonicity over `ℝ` factors (mathlib 4.34 `Finset.prod_le_prod`
requires `MulLeftMono`, not satisfiable for `ℝ`). -/
private lemma prod_exp_le_prod_one_add (τ : ℕ → ℝ) (k : ℝ) (n : ℕ)
    (hk : 0 ≤ k) (hτ : ∀ t, 0 ≤ τ t) :
    ∏ t ∈ Finset.range n, Real.exp (k * τ t - (k * τ t) ^ 2 / 2)
      ≤ ∏ t ∈ Finset.range n, (1 + k * τ t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      have hc := exp_le_one_add (mul_nonneg hk (hτ n))
      have hzc : 0 ≤ 1 + k * τ n := by
        have := exp_le_one_add (mul_nonneg hk (hτ n))
        linarith [Real.exp_nonneg (k * τ n - (k * τ n) ^ 2 / 2)]
      calc (∏ t ∈ Finset.range n, Real.exp (k * τ t - (k * τ t) ^ 2 / 2))
            * Real.exp (k * τ n - (k * τ n) ^ 2 / 2)
          ≤ (∏ t ∈ Finset.range n, Real.exp (k * τ t - (k * τ t) ^ 2 / 2))
            * (1 + k * τ n) :=
              mul_le_mul_of_nonneg_left hc
                (Finset.prod_nonneg fun t _ => Real.exp_nonneg _)
        _ ≤ (∏ t ∈ Finset.range n, (1 + k * τ t)) * (1 + k * τ n) :=
              mul_le_mul_of_nonneg_right ih hzc


/-- **The wall-clock takeoff (MAIN)**: if every cycle t costs τ_t ≥ 0
wall-clock and multiplies capability by ≥ (1 + k·τ_t) with k ≥ 0
(rate k per unit time), then after T cycles

  C_T ≥ C₀ · exp(k·Στ_t − (k²/2)·Στ_t²).

The exponent is k·T_wall (T_wall = Στ the accumulated wall-clock
time) minus the EXPLICIT second-order slack (k²/2)·Στ² — the price
of discretization, paid only by long cycles (slack per factor is
(kτ_t)²/2). Derived from the per-factor bound
exp(x − x²/2) ≤ 1+x (valid for ALL x ≥ 0 — no [0,1] cap needed)
applied factor-wise and telescoped via exp(Σ) = ∏exp. -/
theorem wallclock_takeoff (C τ : ℕ → ℝ) (k : ℝ)
    (hk : 0 ≤ k) (hC0 : 0 ≤ C 0) (hτ : ∀ t, 0 ≤ τ t)
    (hstep : per_cycle_time_rate C τ k)
    (T : ℕ) :
    C T ≥ C 0 * Real.exp (k * ∑ t ∈ Finset.range T, τ t
      - (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2) := by
  have hprod := wallclock_takeoff_product C τ k hk hτ hstep T
  -- each factor dominates its slack-ed exponent
  have hf : ∀ t ∈ Finset.range T,
      Real.exp (k * τ t - (k * τ t) ^ 2 / 2) ≤ 1 + k * τ t := fun t _ =>
    exp_le_one_add (mul_nonneg hk (hτ t))
  have hprod' : ∏ t ∈ Finset.range T, Real.exp (k * τ t - (k * τ t) ^ 2 / 2)
      ≤ ∏ t ∈ Finset.range T, (1 + k * τ t) :=
    prod_exp_le_prod_one_add τ k T hk hτ
  rw [← Real.exp_sum] at hprod'
  -- the exponent collapses to k·Στ − (k²/2)·Στ²
  have hsum : ∑ t ∈ Finset.range T, (k * τ t - (k * τ t) ^ 2 / 2)
      = k * ∑ t ∈ Finset.range T, τ t - (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2 := by
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ t ∈ Finset.range T, k * τ t = k * ∑ t ∈ Finset.range T, τ t :=
      (Finset.mul_sum _ _ _).symm
    have h2 : ∑ t ∈ Finset.range T, (k * τ t) ^ 2 / 2
        = (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2 := by
      have h3 : ∑ t ∈ Finset.range T, (k * τ t) ^ 2
          = k ^ 2 * ∑ t ∈ Finset.range T, (τ t) ^ 2 := by
        rw [show k ^ 2 * ∑ t ∈ Finset.range T, (τ t) ^ 2
            = ∑ t ∈ Finset.range T, k ^ 2 * (τ t) ^ 2 from Finset.mul_sum _ _ _]
        exact Finset.sum_congr rfl fun t _ => by ring
      rw [← Finset.sum_div, h3]
      ring
    rw [h1, h2]
  rw [hsum] at hprod'
  calc C T ≥ C 0 * ∏ t ∈ Finset.range T, (1 + k * τ t) := hprod
    _ ≥ C 0 * Real.exp (k * ∑ t ∈ Finset.range T, τ t
        - (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2) :=
        mul_le_mul_of_nonneg_left hprod' hC0

/-! ## The small-steps regime -/

/-- **The small-steps regime corollary**: if every cycle's scaled
cost satisfies k·τ_t ≤ η, the second-order slack collapses:
(k²/2)Στ² = (k/2)Σ(kτ_t)·τ_t ≤ (η/2)·k·Στ_t, giving

  C_T ≥ C₀ · exp(k·T_wall·(1 − η/2)),

T_wall = Στ_t. As η → 0 (cheap cycles) the effective rate
approaches k exactly — the audit's "dC/dT_wall ≥ kC ⟹ exponential
rate k" in honest discrete form, with the explicit (1−η/2) rate
discount for finite cycles. -/
theorem wallclock_takeoff_small_steps (C τ : ℕ → ℝ) (k η : ℝ)
    (hk : 0 ≤ k) (hC0 : 0 ≤ C 0) (hτ : ∀ t, 0 ≤ τ t)
    (hη : ∀ t, k * τ t ≤ η)
    (hstep : per_cycle_time_rate C τ k)
    (T : ℕ) :
    C T ≥ C 0 * Real.exp (k * (∑ t ∈ Finset.range T, τ t) * (1 - η / 2)) := by
  have hmain := wallclock_takeoff C τ k hk hC0 hτ hstep T
  -- the slack bound: (k²/2)Στ² ≤ (η/2)·k·Στ
  have hslack : (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2
      ≤ (η / 2) * (k * ∑ t ∈ Finset.range T, τ t) := by
    have hper : ∀ t ∈ Finset.range T, (k ^ 2 / 2) * (τ t) ^ 2
        ≤ (η / 2) * (k * τ t) := by
      intro t _
      have hkτ : (0:ℝ) ≤ k * τ t := mul_nonneg hk (hτ t)
      have h1 : k ^ 2 * (τ t) ^ 2 = (k * τ t) * (k * τ t) := by ring
      have h2 : (k * τ t) * (k * τ t) ≤ η * (k * τ t) :=
        mul_le_mul_of_nonneg_right (hη t) hkτ
      nlinarith
    have hsum : (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2
        = ∑ t ∈ Finset.range T, (k ^ 2 / 2) * (τ t) ^ 2 := Finset.mul_sum _ _ _
    rw [hsum]
    calc ∑ t ∈ Finset.range T, (k ^ 2 / 2) * (τ t) ^ 2
        ≤ ∑ t ∈ Finset.range T, (η / 2) * (k * τ t) := Finset.sum_le_sum hper
      _ = (η / 2) * ∑ t ∈ Finset.range T, (k * τ t) := (Finset.mul_sum _ _ _).symm
      _ = (η / 2) * (k * ∑ t ∈ Finset.range T, τ t) := by rw [← Finset.mul_sum]
  -- exponent comparison
  have hexp : Real.exp (k * (∑ t ∈ Finset.range T, τ t) * (1 - η / 2))
      ≤ Real.exp (k * ∑ t ∈ Finset.range T, τ t
        - (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [hslack])
  calc C T ≥ C 0 * Real.exp (k * ∑ t ∈ Finset.range T, τ t
        - (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2) := hmain
    _ ≥ C 0 * Real.exp (k * (∑ t ∈ Finset.range T, τ t) * (1 - η / 2)) :=
        mul_le_mul_of_nonneg_left hexp hC0

/-! ## The composition with the cone/success machinery -/

/-- **The counted takeoff in exponent form** (real success
sequence): if each cycle multiplies capability by ≥ exp(a·s_t)
with a ≥ 0, then C_T ≥ C₀·exp(a·Σs_t) — the exp-factor
composition (the exp twin of `capability_takeoff_counted`;
failures s_t = 0 are neutral). -/
theorem counted_takeoff_exp (C s : ℕ → ℝ) (a : ℝ)
    (hmul : ∀ t, C (t + 1) ≥ C t * Real.exp (a * s t))
    (T : ℕ) :
    C T ≥ C 0 * Real.exp (a * ∑ t ∈ Finset.range T, s t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hmul T
      rw [Finset.sum_range_succ, mul_add, Real.exp_add]
      calc C (T + 1) ≥ C T * Real.exp (a * s T) := h1
        _ ≥ (C 0 * Real.exp (a * ∑ t ∈ Finset.range T, s t)) * Real.exp (a * s T) := by
            refine mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)
        _ = C 0 * (Real.exp (a * ∑ t ∈ Finset.range T, s t) * Real.exp (a * s T)) := by
            ring

/-- **The composed wall-clock rate (cone + success concentration
+ constant cycle cost)**: if each cycle t multiplies capability by
(1+α)^(s_t) (s_t the success indicator — supplied by the R107 cone
invariant via the gate: cone ⟹ C_{t+1} ≥ (1+α)·C_t on successes),
the success count over T cycles is at least p₀·T − Δ (R95's
concentration floor; Δ = 0 is the deterministic all-success case),
and every cycle costs the SAME wall-clock τ, then at accumulated
wall time W = T·τ

  C_T ≥ C₀ · exp(k_eff · W − ln(1+α) · Δ),

with the explicit wall-clock rate constant

  k_eff = p₀ · ln(1+α) / τ

— capability grows exponentially in WALL-CLOCK time at rate
p₀·ln(1+α)/τ, corrected by the concentration deficit
ln(1+α)·Δ. The Δ → 0, α → 0 shadow recovers the continuous
dC/dT ≥ (p₀α/τ)·C: the audit's effective time-rate. -/
theorem wallclock_rate_from_cone (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha tau p0 Delta : ℝ)
    (halpha : 0 < alpha) (htau : 0 < tau) (hC0 : 0 < C 0)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T : ℕ)
    (hcount : p0 * (T : ℝ) - Delta ≤ ∑ t ∈ Finset.range T, (s t : ℝ)) :
    C T ≥ C 0 * Real.exp ((p0 * Real.log (1 + alpha) / tau) * ((T : ℝ) * tau)
      - Real.log (1 + alpha) * Delta) := by
  set L := Real.log (1 + alpha) with hL
  have hLpos : 0 < L := Real.log_pos (by linarith)
  -- rewrite the per-cycle factor in exp form
  have hpowexp : ∀ t, (1 + alpha) ^ (s t) = Real.exp ((s t : ℝ) * L) := by
    intro t
    have h1 : Real.exp ((s t : ℝ) * L) = Real.exp (L) ^ (s t) := by
      rw [← Real.exp_nat_mul L (s t)]
    rw [h1, Real.exp_log (by linarith : (0:ℝ) < 1 + alpha)]
  have hmul' : ∀ t, C (t + 1) ≥ C t * Real.exp (L * (s t : ℝ)) := by
    intro t
    have h := hmul t
    rw [hpowexp t, mul_comm ((s t : ℝ)) L] at h
    exact h
  have hmain := counted_takeoff_exp C (fun t => (s t : ℝ)) L hmul' T
  -- the exponent with the concentration floor substituted
  have hcount' : L * (p0 * (T : ℝ) - Delta)
      ≤ L * ∑ t ∈ Finset.range T, (s t : ℝ) :=
    mul_le_mul_of_nonneg_left hcount hLpos.le
  have hexp : Real.exp ((p0 * L / tau) * ((T : ℝ) * tau) - L * Delta)
      ≤ Real.exp (L * ∑ t ∈ Finset.range T, (s t : ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    have heq : L * (p0 * (T : ℝ) - Delta)
        = (p0 * L / tau) * ((T : ℝ) * tau) - L * Delta := by
      field_simp
    linarith [hcount', heq]
  calc C T ≥ C 0 * Real.exp (L * ∑ t ∈ Finset.range T, (s t : ℝ)) := hmain
    _ ≥ C 0 * Real.exp ((p0 * L / tau) * ((T : ℝ) * tau) - L * Delta) :=
        mul_le_mul_of_nonneg_left hexp hC0.le

/-- **The instantiation with R95's Hoeffding concentration**: the
success-count floor Δ = concDelta T δ = √(2T·log(1/δ)) holds with
probability ≥ 1−δ by `success_count_lower_p0` (R95, NOT reproved
here — this theorem takes the concentrated floor as a deterministic
hypothesis, the standard conditioning step on the good event). With
it, the composed wall-clock rate law holds with the explicit √T
fluctuation penalty ln(1+α)·√(2T·log(1/δ)) in the exponent. -/
theorem wallclock_rate_from_cone_concentrated (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha tau p0 delta : ℝ)
    (halpha : 0 < alpha) (htau : 0 < tau)
    (_hdelta : 0 < delta) (_hdelta1 : delta < 1)
    (hC0 : 0 < C 0)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T : ℕ)
    (hcount : p0 * (T : ℝ) - concDelta T delta
      ≤ ∑ t ∈ Finset.range T, (s t : ℝ)) :
    C T ≥ C 0 * Real.exp ((p0 * Real.log (1 + alpha) / tau) * ((T : ℝ) * tau)
      - Real.log (1 + alpha) * concDelta T delta) :=
  wallclock_rate_from_cone C s alpha tau p0 (concDelta T delta)
    halpha htau hC0 hmul T hcount


/-- **R116 (audit §17): the wall-clock rate with VARIABLE cycle
time**. The `wallclock_rate_from_cone` form assumed a constant
τ per cycle; for a growing model the cycle cost τ_t changes.
The honest finite-horizon form bounds only the AVERAGE cycle
time: if the total wall-clock spent is W_T = Σ τ_t with
Σ τ_t ≤ T·τ̄, and the success count has the p₀-floor, then
C_T ≥ C₀·exp((p₀·ln(1+α)/τ̄)·W_T − ln(1+α)·Δ) — exponential
in ACTUAL wall-clock, with the same fluctuation penalty. -/
theorem wallclock_rate_avg_tau (C : ℕ → ℝ) (s : ℕ → ℕ) (tau : ℕ → ℝ)
    (alpha tauBar p0 Delta : ℝ)
    (halpha : 0 < alpha) (htauBar : 0 < tauBar) (hp0 : 0 ≤ p0)
    (hC0 : 0 < C 0)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T : ℕ)
    (htau : T ≠ 0)
    (havg : ∑ t ∈ Finset.range T, tau t ≤ (T : ℝ) * tauBar)
    (hcount : p0 * (T : ℝ) - Delta
      ≤ ∑ t ∈ Finset.range T, (s t : ℝ)) :
    C T ≥ C 0 * Real.exp ((p0 * Real.log (1 + alpha) / tauBar)
      * (∑ t ∈ Finset.range T, tau t) - Real.log (1 + alpha) * Delta) := by
  set L := Real.log (1 + alpha) with hL
  have hLpos : 0 < L := Real.log_pos (by linarith)
  set W : ℝ := ∑ t ∈ Finset.range T, tau t with hW
  have hTw : W / tauBar ≤ (T : ℝ) := by
    rw [div_le_iff₀ htauBar]
    linarith
  have hsumfloor : p0 * (W / tauBar) - Delta
      ≤ ∑ t ∈ Finset.range T, (s t : ℝ) := by
    have hpw : p0 * (W / tauBar) ≤ p0 * (T : ℝ) :=
      mul_le_mul_of_nonneg_left hTw hp0
    linarith
  have hpowexp : ∀ t, (1 + alpha) ^ (s t) = Real.exp ((s t : ℝ) * L) := by
    intro t
    have h1 : Real.exp ((s t : ℝ) * L) = Real.exp (L) ^ (s t) := by
      rw [← Real.exp_nat_mul L (s t)]
    rw [h1, Real.exp_log (by linarith : (0:ℝ) < 1 + alpha)]
  have hmul' : ∀ t, C (t + 1) ≥ C t * Real.exp (L * (s t : ℝ)) := by
    intro t
    have h := hmul t
    rw [hpowexp t, mul_comm ((s t : ℝ)) L] at h
    exact h
  have hmain := counted_takeoff_exp C (fun t => (s t : ℝ)) L hmul' T
  have hexpfloor : Real.exp (L * (p0 * (W / tauBar) - Delta))
      ≤ Real.exp (L * ∑ t ∈ Finset.range T, (s t : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsumfloor hLpos.le)
  have hexponent : (p0 * L / tauBar) * W - L * Delta
      = L * (p0 * (W / tauBar) - Delta) := by
    field_simp
    try ring
  rw [hexponent]
  calc C T ≥ C 0 * Real.exp (L * ∑ t ∈ Finset.range T, (s t : ℝ)) := hmain
    _ ≥ C 0 * Real.exp (L * (p0 * (W / tauBar) - Delta)) :=
        mul_le_mul_of_nonneg_left hexpfloor hC0.le

end Hagi

