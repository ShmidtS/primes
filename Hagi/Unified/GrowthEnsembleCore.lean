import Mathlib
import Hagi.Ensemble.CompressionCert
import Hagi.Ensemble.MergeIdentity
import Hagi.Ensemble.MergeMixture
import Hagi.Ensemble.MergePrice
import Hagi.Ensemble.MergeScaling
import Hagi.Ensemble.PolicyCompatibility
import Hagi.Ensemble.SigmaKernel
import Hagi.Ensemble.UniformCert
import Hagi.Foundations.GrowthDynamics
import Hagi.Growth.ChainUnification
import Hagi.Growth.NoiseDisentangle
import Hagi.Growth.NonlinearCone
import Hagi.Growth.PlasticityLedger
import Hagi.Growth.RecursiveSelfDevelopment
import Hagi.Growth.RoundViability
import Hagi.Growth.RsiCriterion
import Hagi.Growth.SeedOnly
import Hagi.Growth.T3Ignition
import Hagi.Growth.Thermostat

/-!
# GrowthEnsembleCore — рост/ансамбль/двойственный потолок
(слияние одно-теоремных фасадов GrowthExt/EnsembleTheory/DualCeiling, аудит v9 P3).
-/

namespace Hagi.Unified

/-!
# Unified.GrowthExt — фасад расширений роста

Слой-6 фасад: обновление возможностей (self-development),
затухание посевного цикла, нелинейный конус, пластичность,
термостат, T3-зажигание.
-/


export Hagi.Growth (opportunity_renewal cycle_decay_mono
  round_exhausted thermostat_stop kl_le_log_card
  training_core_is_measurement_tail orthogonal_noise_averaging)

/-- САМОРАЗВИТИЕ (сводка): (1) при конусной динамике с полом
возможностей фронт строго растёт (D + ΔO ≤ D'); (2)
посевной капитал затухает монотонно, оставаясь
неотрицательным. Саморазвитие возобновляет ресурс и не
истощает посев. -/
theorem growth_renews_and_seed_survives
    (D D' C rho beta xi deltaO : ℝ)
    (hdyn : rho * D + beta * C - xi ≤ D')
    (hfloor : (1 - rho) * D + deltaO ≤ beta * C - xi)
    (F k s : ℝ) (hs : 0 ≤ s) (hF : 0 < F)
    (hk : 0 < k) (hklt : k < F + s) :
    D + deltaO ≤ D'
      ∧ F * (1 - k/(F + s)) < F
        ∧ 0 ≤ F * (1 - k/(F + s)) :=
  ⟨opportunity_renewal D D' C rho beta xi deltaO hdyn hfloor,
    cycle_decay_mono F k s hs hF hk hklt⟩


/-!
# Unified.EnsembleTheory — фасад теории ансамблей

Слой-6 фасад: слияние и маршрутизация — shift-инвариантность
softmax, точность смешанной продукции, квадратичная цена
слияния, sigma-ядро, совместимость политик.
-/

open Matrix Finset


export Hagi.Ensemble (softmax_shift_invariance
  geometric_mean_logit_mean merged_output_exact routing_drift_bound
  merge_price_quad uniform_good_mass integration_net_gain_pos)

/-- ПРИНЦИП СЛИЯНИЯ (сводка): (1) softmax-маршрутизация
инвариантна к сдвигу логитов (выбор не зависит от калибровки);
(2) смешанная продукция точна (линейность по построению). -/
theorem merge_calibrated_and_exact {V : Type} [Fintype V]
    (z : V → ℝ) (c : ℝ) {m d : ℕ} (w : Fin m → ℝ)
    (x : Fin d → ℝ)
    {W : Fin m → Matrix (Fin d) (Fin d) ℝ} :
    (fun v => Real.exp (z v + c) / ∑ u, Real.exp (z u + c))
      = (fun v => Real.exp (z v) / ∑ u, Real.exp (z u))
      ∧ (∑ i, w i • W i) *ᵥ x = ∑ i, w i • (W i *ᵥ x) :=
  ⟨Hagi.Ensemble.softmax_shift_invariance V z c,
    merged_output_exact W w x⟩


/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

/-!
# DualCeiling — двойной потолок термостата (R559)

Объединение двух ограничительных каналов: полоса-потолок
(R556) и γ-бюджет-потолок (R530-гейт). Capability ограничен
минимумом двух потолков.
-/

open scoped BigOperators


/-- **Двойной потолок (R559)**: при затухающей полосе прироста
и γ-гейте (α·C t ≤ G t ≤ γ·D̄) capability ограничен обоими
потолками сразу: C T ≤ C 0 + b/σ (полоса, R556) и
C T ≤ γ·D̄/α (γ-бюджет через гейт). -/
theorem dual_ceiling (C G D : ℕ → ℝ) (b σ Dbar alpha gamma : ℝ)
    (T : ℕ)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hband : ∀ t, G t ≤ b * (1 - σ) ^ t)
    (hb : 0 ≤ b) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hgate : ∀ t, alpha * C t ≤ G t)
    (hgain : ∀ t, G t ≤ gamma * Dbar)
    (hα : 0 < alpha) :
    C T ≤ C 0 + b / σ ∧ C T ≤ gamma * Dbar / alpha := by
  classical
  obtain ⟨_, hceil⟩ := Hagi.Foundations.geometric_band_ceiling
    C G b σ T hstep hband hb hσ hσ1
  refine ⟨hceil, ?_⟩
  have hgateT : C T * alpha ≤ gamma * Dbar := by
    have h1 : alpha * C T ≤ G T := hgate T
    have h2 : G T ≤ gamma * Dbar := hgain T
    have h3 : alpha * C T ≤ gamma * Dbar := le_trans h1 h2
    rw [mul_comm] at h3
    exact h3
  exact (le_div_iff₀ hα).mpr hgateT

