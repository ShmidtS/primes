/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.SafeQP
import Mathlib.Probability.Moments.SubGaussian

set_option linter.style.header false

/-!
# Stochastic SafeQP: minibatch gradients + high-probability feasibility

Phase 3a of the roadmap: the SafeQP controller of
`Hagi.Step.SafeQP` assumed the per-corpus gradients g_i are
EXACT. Real training estimates them by minibatches:
`ĝ_i = g_i + (1/m)·Σ_j ξ_{i,j}` with ξ_{i,j} the per-sample
noise vectors. This module proves that the safety margin
survives the noise, with EXPLICIT constants.

**Model (bounded noise + Hoeffding).** Chosen deliberately
over sub-Gaussian vectors: mathlib's
`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`
(Hoeffding for sums of independent sub-Gaussians) plus
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`
(Hoeffding's lemma for bounded mean-zero variables) give the
whole chain. The noise enters the SafeQP constraints ONLY
through the projections ⟪ξ_{i,j}, d*⟫ — so the statistical
hypotheses are stated on those projections (honest: they
follow from i.i.d. mean-zero vectors with ‖ξ‖ ≤ σ, the
i.i.d. structure itself stays an h_emp_ hypothesis; only the
per-domain independence of the m batch terms is needed, no
cross-domain independence — the union bound does not
require it).

**The explicit constants.** With batch size m, per-sample
noise radius σ, step direction d (‖d‖ the effective
magnitude), K protected domains and confidence δ ∈ (0,1):

  ε_noise = σ·‖d‖·√(2·log(|K|/δ)/m).

**What the module proves:**

* `minibatch_inner_tail` — the per-domain one-sided tail:
  Pr[ m·ε ≤ Σ_j (−⟪ξ_{i,j}, d⟩) ] ≤ exp(−m·ε²/(2·σ²‖d‖²))
  — the m in the exponent is the minibatch variance
  reduction (Hoeffding for the m independent bounded terms).
* `minibatch_inner_concentration` — the simultaneous
  bound (lower tail): with probability ≥ 1 − δ, EVERY
  domain's stochastic constraint value is within ε_noise
  of the exact one:
  Pr[ ∀ i, ⟪g_i, d⟫ − ε_noise ≤ ⟪ĝ_i, d⟫ ] ≥ 1 − δ.
  The |K| enters through the union bound (the log(|K|/δ)).
  `minibatch_inner_concentration_upper` is the mirrored
  UPPER tail (Pr[ ⟪ĝ_i, d⟫ ≤ ⟪g_i, d⟫ + ε_noise ] ≥ 1 − δ)
  — the direction the feasibility transfer needs.
* `stochastic_safeQP_feasibility` — the high-probability
  feasibility transfer: with probability ≥ 1 − δ, IF the
  realized stochastic constraints hold (d certified against
  the ĝ_i, i.e. d ∈ safeSet ĝ(·) ε as solved by the
  stochastic QP at that ω), THEN the TRUE gradients also
  satisfy the safety margin inflated by ε_noise:
  ⟪g_i, d⟫ ≥ −(ε_i + ε_noise) for all i.

**Honest boundary.** d is a FIXED direction here (the
analysis conditions on the step direction; the adaptively
selected d*(ω) is NOT formalized in this module — see
`Hagi.Step.AdaptiveSafeQP` (R97), which closes this gap by the
covering-number route for any pointwise-D-bounded d*(ω) in
`EuclideanSpace ℝ (Fin n)`). The mean-zero and
boundedness of the noise are empirical hypotheses
(h_emp_*). The i.i.d. structure across the batch enters only
through per-domain independence + mean zero; identical
distribution is not needed. Two-sided bounds and the
sub-Gaussian (unbounded) noise regime are left open.
-/

open Finset Real MeasureTheory ProbabilityTheory InnerProductSpace
open scoped NNReal

namespace Hagi

section StochasticSafeQP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {K : Type*} [Fintype K] [Nonempty K]

/-- The explicit minibatch noise margin:
`ε_noise = σ·‖d‖·√(2·log(|K|/δ)/m)` — the price of using a
batch of size m instead of the exact gradient, at confidence
δ over K protected domains. -/
noncomputable def noiseEps (K : Type*) [Fintype K] (sigma : ℝ) (d : X) (m : ℕ) (delta : ℝ) : ℝ :=
  sigma * ‖d‖ * Real.sqrt (2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ))

/-- **The per-domain one-sided Hoeffding tail** for the
minibatch inner product. N j is the j-th batch-sample noise
projection ⟪ξ_j, d⟫ (measurable, mean zero, |·| ≤ R, the m
projections independent). Then the DOWNWARD deviation of the
batch sum obeys the Hoeffding bound with the m-fold variance
reduction:

  Pr[ m·ε ≤ Σ_j (−N_j) ] ≤ exp(−m·ε²/(2·R²)).

Proof: Hoeffding's lemma (bounded mean-zero ⇒ sub-Gaussian
with parameter ((2R)/2)² = R²) applied to each −N_j, then
`measure_sum_ge_le_of_iIndepFun` over the m independent
terms: ∑c = m·R², ε' = m·ε. -/
theorem minibatch_inner_tail {m : ℕ} (hm : 0 < m)
    (N : Fin m → Ω → ℝ) (R : ℝ) (hR : 0 < R)
    (h_meas : ∀ j, Measurable (N j))
    (h_indep : iIndepFun N μ)
    (h_zero : ∀ j, μ[N j] = 0)
    (h_bound : ∀ j ω, |N j ω| ≤ R)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | (m : ℝ) * ε ≤ ∑ j, -N j ω}
      ≤ Real.exp (- (m : ℝ) * ε ^ 2 / (2 * R ^ 2)) := by
  classical
  -- the negated family is still independent
  have hindep' : iIndepFun (fun j : Fin m => -N j) μ :=
    h_indep.comp _ (fun _ => measurable_id.neg)
  -- each -N_j is sub-Gaussian (Hoeffding's lemma), parameter (2R/2)² = R²
  have hc : ∀ j, HasSubgaussianMGF (-N j) ((‖R - (-R)‖₊ / 2) ^ 2) μ := by
    intro j
    have hmem : ∀ᵐ ω ∂μ, (-N j) ω ∈ Set.Icc (-R) R := by
      filter_upwards with ω
      have hb := abs_le.mp (h_bound j ω)
      simp only [Pi.neg_apply, Set.mem_Icc]
      constructor <;> linarith
    have hzero' : μ[-N j] = 0 := by
      show ∫ (x : Ω), -(N j x) ∂μ = 0
      rw [integral_neg, h_zero j]
      ring
    exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (a := -R) (b := R) (X := -N j)
      (hm := (h_meas j).neg.aemeasurable) (hb := hmem) (hc := hzero')
  -- the parameter simplifies to R^2
  have habs : |2 * R| = 2 * R := abs_of_nonneg (by linarith [hR])
  have h2 : ((‖R - (-R)‖₊ : ℝ)) = 2 * R := by
    have hrw : (R : ℝ) - (-R) = 2 * R := by ring
    rw [hrw]
    push_cast
    simp [hR.le]
  have hRabs : (((‖R - (-R)‖₊ : ℝ)) / 2) ^ 2 = R ^ 2 := by
    rw [h2]
    field_simp
  -- the Hoeffding inequality over the m independent terms, at level m·ε
  have hεm : 0 ≤ (m : ℝ) * ε := by positivity
  have htail := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (ι := Fin m)
    (X := fun j => -N j) (c := fun _ => ((‖R - (-R)‖₊ / 2) ^ 2))
    hindep' (s := Finset.univ) (fun j _ => hc j) (ε := (m : ℝ) * ε) hεm
  -- per-term parameter cast: each c_j = R² (as a real)
  have hpt : ∀ j : Fin m, (((‖R - (-R)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = R ^ 2 := by
    intro j
    push_cast
    exact hRabs
  rw [NNReal.coe_sum, Finset.sum_congr rfl (fun j _ => hpt j),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin] at htail
  simp at htail
  -- exponent arithmetic: (m·ε)² / (2·(m·R²)) = m·ε²/(2·R²)
  have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have htail' : μ.real {ω | (m : ℝ) * ε ≤ ∑ j, -N j ω}
      ≤ Real.exp (- ((m : ℝ) * ε) ^ 2 / (2 * ((m : ℝ) * R ^ 2))) := by
    have hset : {ω : Ω | (m : ℝ) * ε ≤ ∑ j, -N j ω}
        = {ω : Ω | (m : ℝ) * ε ≤ -∑ j, N j ω} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;> simpa using h
    rw [hset]
    exact htail
  calc μ.real {ω | (m : ℝ) * ε ≤ ∑ j, -N j ω}
      ≤ Real.exp (- ((m : ℝ) * ε) ^ 2 / (2 * ((m : ℝ) * R ^ 2))) := htail'
    _ = Real.exp (- (m : ℝ) * ε ^ 2 / (2 * R ^ 2)) := by
        congr 1
        field_simp


/-- **The simultaneous minibatch concentration (the main
stochastic-SafeQP noise bound)**: with the explicit margin

  ε_noise = σ·‖d‖·√(2·log(|K|/δ)/m),

with probability ≥ 1 − δ EVERY protected domain's stochastic
inner product is within ε_noise below the exact one:

  Pr[ ∀ i, ⟪g_i, d⟫ − ε_noise ≤ ⟪ĝ_i, d⟫ ] ≥ 1 − δ,
  ĝ_i = g_i + (1/m)·Σ_j ξ_{i,j}.

Hypotheses (honest, empirical): the per-sample noise vectors
are bounded (‖ξ‖ ≤ σ), their d-projections are measurable and
mean zero, and the m batch terms are independent per domain
(cross-domain independence is NOT needed — the union bound
does not use it). Proof: `minibatch_inner_tail` per domain
(Hoeffding), then the union bound over the |K| domains — the
|K| enters through log(|K|/δ) inside ε_noise, making each
per-domain tail exactly δ/|K|. -/
theorem minibatch_inner_concentration {m : ℕ} (hm : 0 < m)
    (g : K → X) (d : X) (hd : d ≠ 0) (sigma : ℝ) (hsigma : 0 < sigma)
    (xi : K → Fin m → Ω → X)
    (h_emp_noise_meas : ∀ i j, Measurable (fun ω => ⟪xi i j ω, d⟫_ℝ))
    (h_emp_noise_zero : ∀ i j, μ[fun ω => ⟪xi i j ω, d⟫_ℝ] = 0)
    (h_emp_noise_indep : ∀ i, iIndepFun (fun j : Fin m => fun ω => ⟪xi i j ω, d⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) :
    μ.real {ω | ∀ i, ⟪g i, d⟫_ℝ - noiseEps K sigma d m delta
        ≤ ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ} ≥ 1 - delta := by
  classical
  set R := sigma * ‖d‖ with hRdef
  have hR : 0 < R := by
    rw [hRdef]
    exact mul_pos hsigma (norm_pos_iff.mpr hd)
  -- the noise projections are bounded by R = σ‖d‖ (Cauchy-Schwarz)
  have hB : ∀ i j ω, |⟪xi i j ω, d⟫_ℝ| ≤ R := by
    intro i j ω
    calc |⟪xi i j ω, d⟫_ℝ| = ‖⟪xi i j ω, d⟫_ℝ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖xi i j ω‖ * ‖d‖ := norm_inner_le_norm _ _
      _ ≤ R := by
          rw [hRdef]
          exact mul_le_mul_of_nonneg_right (h_emp_noise_bound i j ω) (norm_nonneg d)
  -- ε_noise ≥ 0 (the log is nonnegative: |K| ≥ 1 > δ)
  have hcard : (1 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨hd1, hd2⟩ := Set.mem_Ioo.mp hdelta
  have hLpos : 0 < Real.log ((Fintype.card K : ℝ) / delta) := by
    have h1 : 1 < (Fintype.card K : ℝ) / delta :=
      (one_lt_div hd1).mpr (lt_of_lt_of_le hd2 hcard)
    exact Real.log_pos h1
  have heps : 0 ≤ noiseEps K sigma d m delta := by
    unfold noiseEps
    positivity
  -- the exponent identity: m·ε_noise² / (2R²) = log(|K|/δ)
  have hsq : m * (noiseEps K sigma d m delta) ^ 2
      = 2 * R ^ 2 * Real.log ((Fintype.card K : ℝ) / delta) := by
    have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hs2 : 0 ≤ 2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ) := by
      apply div_nonneg _ hmp.le
      linarith
    unfold noiseEps
    have hnn : (sigma * ‖d‖) ^ 2 = R ^ 2 := by rw [hRdef]
    have hsqr : (Real.sqrt (2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ))) ^ 2
        = 2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ) :=
      Real.sq_sqrt hs2
    rw [mul_pow, hsqr, hnn]
    field_simp
  -- the per-domain tail equals exactly δ/|K|
  have htailval : ∀ i : K,
      μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
        ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)}
      ≤ delta / (Fintype.card K : ℝ) := by
    intro i
    have ht := minibatch_inner_tail hm
      (fun j ω => ⟪xi i j ω, d⟫_ℝ) R hR
      (h_emp_noise_meas i) (h_emp_noise_indep i) (h_emp_noise_zero i) (hB i) heps
    have hex : Real.exp (- (m : ℝ) * (noiseEps K sigma d m delta) ^ 2 / (2 * R ^ 2))
        = delta / (Fintype.card K : ℝ) := by
      have hrw : - (m : ℝ) * (noiseEps K sigma d m delta) ^ 2 / (2 * R ^ 2)
          = - Real.log ((Fintype.card K : ℝ) / delta) := by
        rw [neg_mul, hsq]
        field_simp
      have hcd : 0 < (Fintype.card K : ℝ) / delta :=
        div_pos (by exact_mod_cast Fintype.card_pos) hd1
      rw [hrw, Real.exp_neg, Real.exp_log hcd, inv_div]
    rw [hex] at ht
    exact ht
  -- the union bound over the K protected domains
  have hcardne : (Fintype.card K : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith
  have hsum : ∑ i, μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)} ≤ delta := by
    calc ∑ i, μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
          ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)}
        ≤ ∑ i, delta / (Fintype.card K : ℝ) :=
          Finset.sum_le_sum (fun i _ => htailval i)
      _ = delta := by
          rw [Finset.sum_const, Finset.card_univ]
          simp
          field_simp
  have huni : μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)}) ≤ delta := by
    calc μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
          ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)})
        ≤ ∑ i, μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
            ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)} :=
          measureReal_iUnion_fintype_le
            (fun i => {ω | (m : ℝ) * noiseEps K sigma d m delta
              ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)})
      _ ≤ delta := hsum
  -- the failure events are measurable
  have hE : ∀ i : K, MeasurableSet {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)} := by
    intro i
    have hf : Measurable (fun ω => ∑ j, -(⟪xi i j ω, d⟫_ℝ)) := by fun_prop
    exact measurableSet_le measurable_const hf
  have huniMeas : MeasurableSet (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)}) :=
    MeasurableSet.iUnion hE
  have hcomp : 1 - delta ≤ μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)})ᶜ := by
    rw [measureReal_compl huniMeas, probReal_univ]
    linarith
  -- the good event contains the complement of the failure event
  have hinner : ∀ (i : K) (ω : Ω),
      ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ
        = ⟪g i, d⟫_ℝ + (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, d⟫_ℝ := by
    intro i ω
    rw [inner_add_left, inner_smul_left, sum_inner]
    simp
  have hsub : (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)})ᶜ
      ⊆ {ω | ∀ i, ⟪g i, d⟫_ℝ - noiseEps K sigma d m delta
        ≤ ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hω
    intro i
    rw [hinner i]
    by_contra hcontra
    push_neg at hcontra
    have hnot := hω i
    simp only [Set.mem_setOf_eq] at hnot
    push_neg at hnot
    have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hneg : ∑ j, -(⟪xi i j ω, d⟫_ℝ) = -∑ j, ⟪xi i j ω, d⟫_ℝ := by
      simp [Finset.sum_neg_distrib]
    have h1 : -((m : ℝ) * noiseEps K sigma d m delta)
        < ∑ j, ⟪xi i j ω, d⟫_ℝ := by linarith
    have h2 : -(noiseEps K sigma d m delta)
        < (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, d⟫_ℝ := by
      rw [inv_mul_eq_div, lt_div_iff₀ hmp]
      linarith
    linarith
  calc (1 : ℝ) - delta ≤ μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
        ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)})ᶜ := hcomp
    _ ≤ μ.real {ω | ∀ i, ⟪g i, d⟫_ℝ - noiseEps K sigma d m delta
        ≤ ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ} := measureReal_mono hsub

theorem minibatch_inner_concentration_upper {m : ℕ} (hm : 0 < m)
    (g : K → X) (d : X) (hd : d ≠ 0) (sigma : ℝ) (hsigma : 0 < sigma)
    (xi : K → Fin m → Ω → X)
    (h_emp_noise_meas : ∀ i j, Measurable (fun ω => ⟪xi i j ω, d⟫_ℝ))
    (h_emp_noise_zero : ∀ i j, μ[fun ω => ⟪xi i j ω, d⟫_ℝ] = 0)
    (h_emp_noise_indep : ∀ i, iIndepFun (fun j : Fin m => fun ω => ⟪xi i j ω, d⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) :
    μ.real {ω | ∀ i, ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ
        ≤ ⟪g i, d⟫_ℝ + noiseEps K sigma d m delta} ≥ 1 - delta := by
  classical
  set R := sigma * ‖d‖ with hRdef
  have hR : 0 < R := by
    rw [hRdef]
    exact mul_pos hsigma (norm_pos_iff.mpr hd)
  -- the noise projections are bounded by R = σ‖d‖ (Cauchy-Schwarz)
  have hB : ∀ i j ω, |⟪xi i j ω, d⟫_ℝ| ≤ R := by
    intro i j ω
    calc |⟪xi i j ω, d⟫_ℝ| = ‖⟪xi i j ω, d⟫_ℝ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖xi i j ω‖ * ‖d‖ := norm_inner_le_norm _ _
      _ ≤ R := by
          rw [hRdef]
          exact mul_le_mul_of_nonneg_right (h_emp_noise_bound i j ω) (norm_nonneg d)
  -- ε_noise ≥ 0 (the log is nonnegative: |K| ≥ 1 > δ)
  have hcard : (1 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨hd1, hd2⟩ := Set.mem_Ioo.mp hdelta
  have hLpos : 0 < Real.log ((Fintype.card K : ℝ) / delta) := by
    have h1 : 1 < (Fintype.card K : ℝ) / delta :=
      (one_lt_div hd1).mpr (lt_of_lt_of_le hd2 hcard)
    exact Real.log_pos h1
  have heps : 0 ≤ noiseEps K sigma d m delta := by
    unfold noiseEps
    positivity
  -- the exponent identity: m·ε_noise² / (2R²) = log(|K|/δ)
  have hsq : m * (noiseEps K sigma d m delta) ^ 2
      = 2 * R ^ 2 * Real.log ((Fintype.card K : ℝ) / delta) := by
    have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hs2 : 0 ≤ 2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ) := by
      apply div_nonneg _ hmp.le
      linarith
    unfold noiseEps
    have hnn : (sigma * ‖d‖) ^ 2 = R ^ 2 := by rw [hRdef]
    have hsqr : (Real.sqrt (2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ))) ^ 2
        = 2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ) :=
      Real.sq_sqrt hs2
    rw [mul_pow, hsqr, hnn]
    field_simp
  -- the per-domain tail equals exactly δ/|K|
  have htailval : ∀ i : K,
      μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
        ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ}
      ≤ delta / (Fintype.card K : ℝ) := by
    intro i
    have ht := minibatch_inner_tail hm
      (fun j ω => -(⟪xi i j ω, d⟫_ℝ)) R hR
      (fun j => (h_emp_noise_meas i j).neg)
      ((h_emp_noise_indep i).comp _ (fun _ => measurable_id.neg))
      (fun j => by
        show ∫ (x : Ω), -(⟪xi i j x, d⟫_ℝ) ∂μ = 0
        rw [integral_neg, h_emp_noise_zero i j]
        ring)
      (fun j ω => by simpa using hB i j ω) heps
    simp only [neg_neg] at ht
    have hex : Real.exp (- (m : ℝ) * (noiseEps K sigma d m delta) ^ 2 / (2 * R ^ 2))
        = delta / (Fintype.card K : ℝ) := by
      have hrw : - (m : ℝ) * (noiseEps K sigma d m delta) ^ 2 / (2 * R ^ 2)
          = - Real.log ((Fintype.card K : ℝ) / delta) := by
        rw [neg_mul, hsq]
        field_simp
      have hcd : 0 < (Fintype.card K : ℝ) / delta :=
        div_pos (by exact_mod_cast Fintype.card_pos) hd1
      rw [hrw, Real.exp_neg, Real.exp_log hcd, inv_div]
    rw [hex] at ht
    exact ht
  -- the union bound over the K protected domains
  have hcardne : (Fintype.card K : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith
  have hsum : ∑ i, μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ} ≤ delta := by
    calc ∑ i, μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
          ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ}
        ≤ ∑ i, delta / (Fintype.card K : ℝ) :=
          Finset.sum_le_sum (fun i _ => htailval i)
      _ = delta := by
          rw [Finset.sum_const, Finset.card_univ]
          simp
          field_simp
  have huni : μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ}) ≤ delta := by
    calc μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
          ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ})
        ≤ ∑ i, μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
            ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ} :=
          measureReal_iUnion_fintype_le
            (fun i => {ω | (m : ℝ) * noiseEps K sigma d m delta
              ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ})
      _ ≤ delta := hsum
  -- the failure events are measurable
  have hE : ∀ i : K, MeasurableSet {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ} := by
    intro i
    have hf : Measurable (fun ω => ∑ j, ⟪xi i j ω, d⟫_ℝ) := by fun_prop
    exact measurableSet_le measurable_const hf
  have huniMeas : MeasurableSet (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ}) :=
    MeasurableSet.iUnion hE
  have hcomp : 1 - delta ≤ μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ})ᶜ := by
    rw [measureReal_compl huniMeas, probReal_univ]
    linarith
  -- the good event contains the complement of the failure event
  have hinner : ∀ (i : K) (ω : Ω),
      ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ
        = ⟪g i, d⟫_ℝ + (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, d⟫_ℝ := by
    intro i ω
    rw [inner_add_left, inner_smul_left, sum_inner]
    simp
  have hsub : (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ})ᶜ
      ⊆ {ω | ∀ i, ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ
        ≤ ⟪g i, d⟫_ℝ + noiseEps K sigma d m delta} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hω
    intro i
    rw [hinner i]
    by_contra hcontra
    push_neg at hcontra
    have hnot := hω i
    simp only [Set.mem_setOf_eq] at hnot
    push_neg at hnot
    have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have h1 : ∑ j, ⟪xi i j ω, d⟫_ℝ
        < (m : ℝ) * noiseEps K sigma d m delta := by linarith
    have h2 : (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, d⟫_ℝ
        < noiseEps K sigma d m delta := by
      rw [inv_mul_eq_div, div_lt_iff₀ hmp]
      linarith
    linarith
  calc (1 : ℝ) - delta ≤ μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
        ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ})ᶜ := hcomp
    _ ≤ μ.real {ω | ∀ i, ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ
        ≤ ⟪g i, d⟫_ℝ + noiseEps K sigma d m delta} := measureReal_mono hsub

/-- **The high-probability feasibility transfer (the
stochastic SafeQP margin)**: with probability ≥ 1 − δ, IF the
stochastic constraints hold for the realized minibatch
gradients (d certified against ĝ_i with budgets ε_i —
d ∈ safeSet ĝ(·) ε, what the stochastic QP enforces by
construction), THEN the TRUE gradients satisfy the same
constraints with the margin inflated by the explicit noise
term ε_noise = σ·‖d‖·√(2·log(|K|/δ)/m):

  ⟪g_i, d⟫ ≥ −(ε_i + ε_noise) for all i.

This is the feasibility guarantee of the stochastic SafeQP
step: the safety budgets pay for the gradient noise
explicitly, with no hidden constants. -/
theorem stochastic_safeQP_feasibility {m : ℕ} (hm : 0 < m)
    (g : K → X) (d : X) (hd : d ≠ 0) (sigma : ℝ) (hsigma : 0 < sigma)
    (xi : K → Fin m → Ω → X)
    (h_emp_noise_meas : ∀ i j, Measurable (fun ω => ⟪xi i j ω, d⟫_ℝ))
    (h_emp_noise_zero : ∀ i j, μ[fun ω => ⟪xi i j ω, d⟫_ℝ] = 0)
    (h_emp_noise_indep : ∀ i, iIndepFun (fun j : Fin m => fun ω => ⟪xi i j ω, d⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) (eps : K → ℝ) :
    μ.real {ω | (∀ i, -eps i ≤ ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ)
        → (∀ i, -(eps i + noiseEps K sigma d m delta) ≤ ⟪g i, d⟫_ℝ)} ≥ 1 - delta := by
  have hgood := minibatch_inner_concentration_upper hm g d hd sigma hsigma xi
    h_emp_noise_meas h_emp_noise_zero h_emp_noise_indep h_emp_noise_bound delta hdelta
  refine le_trans hgood (measureReal_mono ?_)
  rintro ω hω hcert i
  have h1 := hω i
  have h2 := hcert i
  linarith

end StochasticSafeQP

end Hagi
