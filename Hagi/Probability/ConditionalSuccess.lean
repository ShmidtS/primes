/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.TakeoffCounted
import Mathlib
import Mathlib.Probability.Moments.SubGaussian
set_option linter.style.header false

/-!
# R95: conditional success probability → concentration → exponential capability growth

The CENTRAL missing stochastic half of the fast-growth chain
(roadmap §12–14, external review §10): `Hagi.Dynamics.FastGrowth`
proved the deterministic core `capability_takeoff_counted`
(C_T ≥ C₀·(1+α)^{Σs_t}) — exponential in the SUCCESS COUNT —
but the probability layer that turns the success count into
p·T was open. This module closes that gap at the composition
level.

**Route (independent-but-not-identical successes, the honest
middle).** S : ℕ → Ω → ℝ are [0,1]-valued success indicators
(Bernoulli included), MEASURABLE and INDEPENDENT (h_emp_*),
with per-step success means μ[S t] ≥ p₀. Then:

* `success_count_lower` — Hoeffding concentration of the
  success count (exact means version):
  Pr[ Σ_{t<T} S t ≥ (Σ_{t<T} μ[S t]) − Δ ] ≥ 1 − δ
  with the EXPLICIT Δ(T,δ) = √(2·T·log(1/δ)) (sub-Gaussian
  parameter 1 per step: Hoeffding's lemma +
  measure_sum_range_ge_le_of_iIndepFun over the T
  independent terms).
* `success_count_lower_p0` — the per-step floor version:
  μ[S t] ≥ p₀ for all t gives
  Pr[ Σ_{t<T} S t ≥ p₀·T − Δ ] ≥ 1 − δ.
* `log_growth` — the composition: if the log-form capability
  law holds pointwise (log C_{t+1} − log C_t ≥ a·S t − ε_t,
  the bridge the deterministic side provides, ε_t explicit
  friction), then
  Pr[ log C_T ≥ log C₀ + a·(p₀·T − Δ) − Σ_{t<T} ε_t ] ≥ 1 − δ.
  NO independence between S_t and C_t is assumed BEYOND the
  pointwise bridge hypothesis — the composition is a
  per-sample-point telescope on the concentration good event.
* `takeoff_time_form` — the exponential form:
  Pr[ C_T ≥ C₀·exp(a·(p₀·T − Δ) − Σ_{t<T} ε_t) ] ≥ 1 − δ.
  With p₀ > 0, a > 0 and constant friction ε_t = ε̄ < a·p₀,
  the growth exponent a·p₀·T − a·√(2T·log(1/δ)) − ε̄·T is
  linear in T: exponential takeoff with the explicit
  √T-horizon concentration cost.

**Honest boundaries.** (1) The fully ADAPTED conditional
formulation — μ({S t = 1} | 𝒩_t) ≥ p per step w.r.t. a
filtration, via Azuma–Hoeffding — is NOT taken here: mathlib
has measure_sum_ge_le_of_hasCondSubgaussianMGF but no
conditional Hoeffding lemma (bounded + conditionally mean
zero ⇒ conditionally sub-Gaussian) that would let us feed it
without kernel-level MGF arguments. The adapted case is the
open upgrade; independence here is the h_emp_ hypothesis.
(2) Independence of the S_t themselves is assumed; identical
distribution is NOT (per-step means μ[S t] may vary, only the
uniform floor p₀ matters). (3) The bridge hypothesis of
`log_growth` is pointwise in ω — no measurability of C is
needed for the conclusion as stated.
-/

open Finset Real MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Hagi

section ConditionalSuccess

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The explicit concentration price of T independent
success indicators at confidence δ:
Δ(T,δ) = √(2·T·log(1/δ)) — the Hoeffding scale for T bounded
steps with sub-Gaussian parameter 1 each. -/
noncomputable def concDelta (T : ℕ) (delta : ℝ) : ℝ :=
  Real.sqrt (2 * (T : ℝ) * Real.log (1 / delta))

theorem concDelta_nonneg (T : ℕ) (delta : ℝ) :
    0 ≤ concDelta T delta :=
  Real.sqrt_nonneg _

/-- **The success-count concentration (Hoeffding, exact
means)**: T independent [0,1]-valued success indicators
S t (measurable, independent — h_emp_) satisfy

  Pr[ Σ_{t<T} S t ≥ (Σ_{t<T} μ[S t]) − Δ(T,δ) ] ≥ 1 − δ

with the EXPLICIT Δ(T,δ) = √(2·T·log(1/δ)).

Proof: the centered process X_t = μ[S t] − S_t is measurable,
independent (`iIndepFun.comp`), takes values in [−1,1] with
mean 0, hence is sub-Gaussian with parameter
((1−(−1))/2)² = 1 by Hoeffding's lemma
(`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`);
measure_sum_range_ge_le_of_iIndepFun gives the upper tail
Pr[Δ ≤ ΣX_t] ≤ exp(−Δ²/(2T)) = δ, and we pass to the
complement. -/
theorem success_count_lower {S : ℕ → Ω → ℝ} {T : ℕ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (h_emp_meas : ∀ t, Measurable (S t))
    (h_emp_01 : ∀ t ω, S t ω ∈ Set.Icc 0 1)
    (h_emp_indep : iIndepFun S μ) :
    μ.real {ω | ∑ t ∈ Finset.range T, S t ω
      ≥ (∑ t ∈ Finset.range T, μ[S t]) - concDelta T delta} ≥ 1 - delta := by
  classical
  rcases Nat.eq_zero_or_pos T with rfl | hTpos
  · simp only [Finset.sum_range_zero, concDelta]
    norm_num
    linarith
  -- the centered process X_t = μ[S t] − S t ω
  set X : ℕ → Ω → ℝ := fun t ω => μ[S t] - S t ω with hXdef
  have hXmeas : ∀ t, Measurable (X t) := fun t => measurable_const.sub (h_emp_meas t)
  have hSint : ∀ t, Integrable (S t) μ := fun t =>
    Integrable.of_bound (h_emp_meas t).aestronglyMeasurable 1
      (ae_of_all μ fun ω => abs_le.mpr
        ⟨le_trans (by norm_num) (h_emp_01 t ω).1, (h_emp_01 t ω).2⟩)
  -- mean zero of the centered process
  have hmean0 : ∀ t, μ[X t] = 0 := by
    intro t
    have hXeq : X t = fun ω => μ[S t] - S t ω := rfl
    rw [hXeq, integral_sub (integrable_const _) (hSint t), integral_const,
      smul_eq_mul, probReal_univ, one_mul, sub_self]
  -- the means live in [0,1]
  have hSlow : ∀ t, 0 ≤ μ[S t] := fun t =>
    integral_nonneg fun _ => (h_emp_01 t _).1
  have hShigh : ∀ t, μ[S t] ≤ 1 := fun t =>
    (integral_mono (hSint t) (integrable_const 1) fun ω => (h_emp_01 t ω).2).trans_eq
      (by simp)
  -- the centered process is [−1,1]-valued
  have hX01 : ∀ t, ∀ᵐ ω ∂μ, X t ω ∈ Set.Icc (-1) 1 := by
    intro t
    refine MeasureTheory.ae_of_all μ fun ω => ?_
    simp only [Set.mem_Icc]
    constructor <;> simp only [hXdef] <;> linarith [hSlow t, hShigh t,
      (h_emp_01 t ω).1, (h_emp_01 t ω).2]
  -- independence of the centered process
  have hXindep : iIndepFun X μ :=
    h_emp_indep.comp _ fun t => measurable_const.sub measurable_id
  -- sub-Gaussian parameter ((1 − (−1))/2)² = 1
  have hc1 : ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : ℝ≥0) = 1 := by
    have h2 : ((1 : ℝ) - (-1)) = 2 := by ring
    rw [h2, Real.nnnorm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    change ((2 : ℝ≥0) / 2) ^ 2 = 1
    rw [div_self two_ne_zero, one_pow]
  have hsubG : ∀ t, HasSubgaussianMGF (X t) ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2) μ :=
    fun t => hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (a := -1) (b := 1) (hm := (hXmeas t).aemeasurable) (hb := hX01 t) (hc := hmean0 t)
  -- measurability of the summed process
  have hsummeas : Measurable fun ω => ∑ t ∈ Finset.range T, X t ω :=
    Finset.measurable_fun_sum _ fun t _ => hXmeas t
  -- the Hoeffding tail bound
  have hΔnonneg : 0 ≤ concDelta T delta := concDelta_nonneg T delta
  have htail := ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
    (X := X) (c := ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2)) (n := T) hXindep
    (fun i _ => hsubG i) (ε := concDelta T delta) hΔnonneg
  rw [hc1] at htail
  -- the exponent evaluates to δ (T ≥ 1 here)
  have hlogpos : (0 : ℝ) ≤ Real.log (1 / delta) :=
    Real.log_nonneg (by field_simp; linarith)
  have hsq : concDelta T delta ^ 2 = 2 * (T : ℝ) * Real.log (1 / delta) := by
    rw [concDelta, Real.sq_sqrt (mul_nonneg
      (mul_nonneg (by norm_num) (by exact_mod_cast hTpos.le)) hlogpos)]
  have hlog : Real.log (1 / delta) = -Real.log delta := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hdelta.ne', Real.log_one, zero_sub]
  have hexpδ : Real.exp (- concDelta T delta ^ 2 / (2 * (T : ℝ) * 1)) = delta := by
    have hTne : ((T : ℝ)) ≠ 0 := by rw [Nat.cast_ne_zero]; exact hTpos.ne'
    have hcancel : -(2 * (T : ℝ) * Real.log (1 / delta)) / (2 * (T : ℝ) * 1)
        = -Real.log (1 / delta) := by
      field_simp
    rw [hsq, hcancel, hlog, neg_neg, Real.exp_log hdelta]
  -- complement bound
  set A : Set Ω := {ω | concDelta T delta ≤ ∑ t ∈ Finset.range T, X t ω} with hA
  have hAmeas : MeasurableSet A := measurableSet_le measurable_const hsummeas
  have hAcompl : μ.real Aᶜ ≥ 1 - delta := by
    rw [probReal_compl_eq_one_sub₀ hAmeas.nullMeasurableSet]
    have h1 : μ.real A ≤ delta := le_trans htail (le_of_eq hexpδ)
    linarith
  -- the complement of the tail set is contained in the good set
  refine le_trans hAcompl ?_
  apply measureReal_mono _ (measure_ne_top μ _)
  intro ω hω
  simp only [hA, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
  have hsumsplit : ∑ t ∈ Finset.range T, X t ω
      = (∑ t ∈ Finset.range T, μ[S t]) - ∑ t ∈ Finset.range T, S t ω := by
    simp only [hXdef, Finset.sum_sub_distrib]
  rw [hsumsplit] at hω
  simp only [Set.mem_ofPred_eq]
  linarith

/-- **The success-count concentration (per-step floor form)**:
independent [0,1]-valued indicators with per-step success
means μ[S t] ≥ p₀ (h_emp_) satisfy

  Pr[ Σ_{t<T} S t ≥ p₀·T − Δ(T,δ) ] ≥ 1 − δ,

Δ(T,δ) = √(2·T·log(1/δ)) as in `success_count_lower`. This is
the bridge form the growth composition needs: the success
count is, with probability ≥ 1 − δ, at least the linear rate
p₀·T minus the explicit √T·√log(1/δ) fluctuation. -/
theorem success_count_lower_p0 {S : ℕ → Ω → ℝ} {T : ℕ} {delta p0 : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (h_emp_meas : ∀ t, Measurable (S t))
    (h_emp_01 : ∀ t ω, S t ω ∈ Set.Icc 0 1)
    (h_emp_indep : iIndepFun S μ)
    (h_emp_p : ∀ t, p0 ≤ μ[S t]) :
    μ.real {ω | ∑ t ∈ Finset.range T, S t ω ≥ p0 * (T : ℝ) - concDelta T delta}
      ≥ 1 - delta := by
  have hmain := success_count_lower (S := S) (T := T) (delta := delta)
    hdelta hdelta1 h_emp_meas h_emp_01 h_emp_indep
  have hsum : p0 * (T : ℝ) ≤ ∑ t ∈ Finset.range T, μ[S t] := by
    calc p0 * (T : ℝ) = ∑ t ∈ Finset.range T, p0 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ ∑ t ∈ Finset.range T, μ[S t] := Finset.sum_le_sum fun t _ => h_emp_p t
  have hsub : {ω | ∑ t ∈ Finset.range T, S t ω
        ≥ (∑ t ∈ Finset.range T, μ[S t]) - concDelta T delta}
      ⊆ {ω | ∑ t ∈ Finset.range T, S t ω ≥ p0 * (T : ℝ) - concDelta T delta} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith
  exact le_trans hmain (measureReal_mono hsub (measure_ne_top μ _))

variable {C : ℕ → Ω → ℝ}

/-- **The composed stochastic growth law (log form)**: with
independent [0,1]-valued success indicators bounded below in
mean by p₀, and the POINTWISE log-form capability bridge

  log C_{t+1} − log C_t ≥ a·S_t − ε_t

(the bridge the deterministic side of
`Hagi.Dynamics.FastGrowth` provides; ε_t is the explicit
friction sequence), then with probability ≥ 1 − δ:

  log C_T ≥ log C₀ + a·(p₀·T − Δ(T,δ)) − Σ_{t<T} ε_t.

No independence between S_t and C_t is assumed beyond the
pointwise bridge — the composition telescopes per sample
point on the concentration good event. a ≥ 0 is honest: for
negative a the monotonicity step from ΣS_t ≥ p₀T − Δ to
a·ΣS_t ≥ a·(p₀T − Δ) would flip. -/
theorem log_growth {S : ℕ → Ω → ℝ} {T : ℕ} {delta p0 a : ℝ} {eps : ℕ → ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (ha : 0 ≤ a)
    (_hCpos : ∀ t ω, 0 < C t ω)
    (hbridge : ∀ t ω, Real.log (C (t + 1) ω) - Real.log (C t ω) ≥ a * S t ω - eps t)
    (h_emp_meas : ∀ t, Measurable (S t))
    (h_emp_01 : ∀ t ω, S t ω ∈ Set.Icc 0 1)
    (h_emp_indep : iIndepFun S μ)
    (h_emp_p : ∀ t, p0 ≤ μ[S t]) :
    μ.real {ω | Real.log (C T ω) ≥ Real.log (C 0 ω)
      + a * (p0 * (T : ℝ) - concDelta T delta) - ∑ t ∈ Finset.range T, eps t}
      ≥ 1 - delta := by
  have hcount := success_count_lower_p0 (S := S) (T := T) (delta := delta)
    hdelta hdelta1 h_emp_meas h_emp_01 h_emp_indep h_emp_p
  have hsub : {ω | ∑ t ∈ Finset.range T, S t ω ≥ p0 * (T : ℝ) - concDelta T delta}
      ⊆ {ω | Real.log (C T ω) ≥ Real.log (C 0 ω)
        + a * (p0 * (T : ℝ) - concDelta T delta) - ∑ t ∈ Finset.range T, eps t} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    -- telescope the log differences
    have h0 := Finset.sum_range_sub' (fun t => Real.log (C t ω)) T
    have htele : ∑ t ∈ Finset.range T,
        (Real.log (C (t + 1) ω) - Real.log (C t ω))
        = Real.log (C T ω) - Real.log (C 0 ω) := by
      have heq : ∑ t ∈ Finset.range T, (Real.log (C (t + 1) ω) - Real.log (C t ω))
          = -∑ t ∈ Finset.range T, (Real.log (C t ω) - Real.log (C (t + 1) ω)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun t _ => by ring
      rw [heq, h0]
      ring
    -- sum the bridge inequalities
    have hstep : a * ∑ t ∈ Finset.range T, S t ω - ∑ t ∈ Finset.range T, eps t
        ≤ ∑ t ∈ Finset.range T, (Real.log (C (t + 1) ω) - Real.log (C t ω)) := by
      have hle : ∑ t ∈ Finset.range T, (a * S t ω - eps t)
          ≤ ∑ t ∈ Finset.range T, (Real.log (C (t + 1) ω) - Real.log (C t ω)) :=
        Finset.sum_le_sum fun t _ => hbridge t ω
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact hle
    -- monotone rescale of the count bound
    have hcount' : a * (p0 * (T : ℝ) - concDelta T delta)
        ≤ a * ∑ t ∈ Finset.range T, S t ω :=
      mul_le_mul_of_nonneg_left hω ha
    linarith
  exact le_trans hcount (measureReal_mono hsub (measure_ne_top μ _))

/-- **The takeoff-time form (exponential growth)**: under the
same hypotheses as `log_growth`,

  Pr[ C_T ≥ C₀·exp(a·(p₀·T − Δ(T,δ)) − Σ_{t<T} ε_t) ] ≥ 1 − δ.

With p₀ > 0, a > 0 and constant friction ε̄ < a·p₀ the
exponent a·p₀·T − a·√(2T·log(1/δ)) − ε̄·T is linear in T:
exponential capability takeoff, with the explicit
√T·√(log(1/δ))·a concentration price — the stochastic half of
`capability_takeoff_counted`. -/
theorem takeoff_time_form {S : ℕ → Ω → ℝ} {T : ℕ} {delta p0 a : ℝ} {eps : ℕ → ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (ha : 0 ≤ a)
    (hCpos : ∀ t ω, 0 < C t ω)
    (hbridge : ∀ t ω, Real.log (C (t + 1) ω) - Real.log (C t ω) ≥ a * S t ω - eps t)
    (h_emp_meas : ∀ t, Measurable (S t))
    (h_emp_01 : ∀ t ω, S t ω ∈ Set.Icc 0 1)
    (h_emp_indep : iIndepFun S μ)
    (h_emp_p : ∀ t, p0 ≤ μ[S t]) :
    μ.real {ω | C T ω ≥ C 0 ω * Real.exp
      (a * (p0 * (T : ℝ) - concDelta T delta) - ∑ t ∈ Finset.range T, eps t)}
      ≥ 1 - delta := by
  have hcount := success_count_lower_p0 (S := S) (T := T) (delta := delta)
    hdelta hdelta1 h_emp_meas h_emp_01 h_emp_indep h_emp_p
  have hsub : {ω | ∑ t ∈ Finset.range T, S t ω ≥ p0 * (T : ℝ) - concDelta T delta}
      ⊆ {ω | C T ω ≥ C 0 ω * Real.exp
        (a * (p0 * (T : ℝ) - concDelta T delta) - ∑ t ∈ Finset.range T, eps t)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    -- the log-form bound on this sample point
    have h0 := Finset.sum_range_sub' (fun t => Real.log (C t ω)) T
    have htele : ∑ t ∈ Finset.range T,
        (Real.log (C (t + 1) ω) - Real.log (C t ω))
        = Real.log (C T ω) - Real.log (C 0 ω) := by
      have heq : ∑ t ∈ Finset.range T, (Real.log (C (t + 1) ω) - Real.log (C t ω))
          = -∑ t ∈ Finset.range T, (Real.log (C t ω) - Real.log (C (t + 1) ω)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun t _ => by ring
      rw [heq, h0]
      ring
    have hstep : a * ∑ t ∈ Finset.range T, S t ω - ∑ t ∈ Finset.range T, eps t
        ≤ ∑ t ∈ Finset.range T, (Real.log (C (t + 1) ω) - Real.log (C t ω)) := by
      have hle : ∑ t ∈ Finset.range T, (a * S t ω - eps t)
          ≤ ∑ t ∈ Finset.range T, (Real.log (C (t + 1) ω) - Real.log (C t ω)) :=
        Finset.sum_le_sum fun t _ => hbridge t ω
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact hle
    have hcount' : a * (p0 * (T : ℝ) - concDelta T delta)
        ≤ a * ∑ t ∈ Finset.range T, S t ω :=
      mul_le_mul_of_nonneg_left hω ha
    have hlog : Real.log (C T ω) ≥ Real.log (C 0 ω)
        + a * (p0 * (T : ℝ) - concDelta T delta) - ∑ t ∈ Finset.range T, eps t := by
      linarith
    -- exponentiate
    have hexpT : C T ω = Real.exp (Real.log (C T ω)) := (Real.exp_log (hCpos T ω)).symm
    have hexp0 : Real.exp (Real.log (C 0 ω)
        + (a * (p0 * (T : ℝ) - concDelta T delta) - ∑ t ∈ Finset.range T, eps t))
        = C 0 ω * Real.exp (a * (p0 * (T : ℝ) - concDelta T delta)
          - ∑ t ∈ Finset.range T, eps t) := by
      rw [Real.exp_add, Real.exp_log (hCpos 0 ω)]
    rw [hexpT, ← hexp0]
    exact Real.exp_le_exp.mpr (by linarith)
  exact le_trans hcount (measureReal_mono hsub (measure_ne_top μ _))

end ConditionalSuccess

end Hagi
