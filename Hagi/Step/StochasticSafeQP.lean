/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.SafeQP
import Mathlib.Probability.Moments.SubGaussian

set_option linter.style.header false

/-!
# StochasticSafeQP — минибатч-градиенты и допустимость с высокой вероятностью

Минибатч-оценка `ĝ_i = g_i + (1/m)·Σⱼ ξ_{i,j}`; шум входит в
ограничения только через проекции `⟪ξ_{i,j}, d⟫`.
Явная константа:
`ε_noise = σ·‖d‖·√(2·log(|K|/δ)/m)`.

* `minibatch_inner_tail`: односторонний хвост Hoeffding —
  `μ{m·ε ≤ Σⱼ (−Nⱼ)} ≤ exp(−m·ε²/(2R²))` для измеримых,
  средне-нулевых независимых `|Nⱼ| ≤ R`;
* `minibatch_inner_concentration` (нижний хвост) и
  `minibatch_inner_concentration_upper` (верхний): с
  вероятностью ≥ 1 − δ для всех i
  `⟪g i, d⟫ − ε_noise ≤ ⟪ĝ i, d⟫ ≤ ⟪g i, d⟫ + ε_noise`;
* `stochastic_safeQP_feasibility`: с вероятностью ≥ 1 − δ
  из стохастической сертификации d по ĝ_i с бюджетами
  `eps i` следует `⟪g i, d⟫ ≥ −(eps i + ε_noise)` для всех i.

d — фиксированное направление (адаптивный выбор — в
`Hagi.Step.AdaptiveSafeQP`); среднее-нулевость, ограниченность
`‖ξ‖ ≤ σ` и поштучная независимость — эмпирические
посылки; двусторонние/sub-Gaussian режимы — открыто.
-/

open Finset Real MeasureTheory ProbabilityTheory InnerProductSpace
open scoped NNReal

namespace Hagi

section StochasticSafeQP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {K : Type*} [Fintype K] [Nonempty K]

/-- Явный шумовой порог минибатча:
`noiseEps K sigma d m delta = σ·‖d‖·√(2·log(|K|/δ)/m)`. -/
noncomputable def noiseEps (K : Type*) [Fintype K] (sigma : ℝ) (d : X) (m : ℕ) (delta : ℝ) : ℝ :=
  sigma * ‖d‖ * Real.sqrt (2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ))

/-- Односторонний хвост Hoeffding: если `N j` измеримы,
независимы, средне-нулевые с `|N j ω| ≤ R` и `0 ≤ ε`, то
`μ.real {ω | m·ε ≤ Σⱼ −N j ω} ≤ exp(−m·ε²/(2R²))`. -/
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
      change ∫ (x : Ω), -(N j x) ∂μ = 0
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
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> simpa using h
    rw [hset]
    exact htail
  calc μ.real {ω | (m : ℝ) * ε ≤ ∑ j, -N j ω}
      ≤ Real.exp (- ((m : ℝ) * ε) ^ 2 / (2 * ((m : ℝ) * R ^ 2))) := htail'
    _ = Real.exp (- (m : ℝ) * ε ^ 2 / (2 * R ^ 2)) := by
        congr 1
        field_simp


/-- При `d ≠ 0`, `0 < σ`, статистических посылках на
проекции шума (измеримость, среднее нулевое, поштучная
независимость, `‖ξ‖ ≤ σ`) и `δ ∈ (0,1)`:
с вероятностью ≥ 1 − δ для всех i
`⟪g i, d⟫ − noiseEps ≤ ⟪g i + (1/m)·Σⱼ ξ_{i,j}, d⟫`
(нижний хвост; |K| — через union bound). -/
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
    push Not at hcontra
    have hnot := hω i
    simp only [Set.mem_ofPred_eq] at hnot
    push Not at hnot
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
    push Not at hcontra
    have hnot := hω i
    simp only [Set.mem_ofPred_eq] at hnot
    push Not at hnot
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

/-- При тех же посылках и бюджетах `eps`: с вероятностью
≥ 1 − δ, если `−eps i ≤ ⟪g i + (1/m)·Σⱼ ξ_{i,j}, d⟫` для
всех i, то
`−(eps i + noiseEps) ≤ ⟪g i, d⟫` для всех i`. -/
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
