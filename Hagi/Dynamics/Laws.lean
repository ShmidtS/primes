/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Foundations.Telescope
import Mathlib.Tactic
import Hagi.Dynamics.EndpointContraction

/-!
# Законы динамики (объединённые)

SpeedLimit, CapabilityGain, UrgencyDepth, DistillationRate.
Имена деклараций сохранены.
-/

/-!
# SpeedLimit — нижняя граница времени обучения

Дискретный аналог speed limits for deep learning
(Seroussi et al., arXiv 2307.14653): скорость убывания
целевой энергии ограничена максимумом M за шаг, поэтому
спуск на Δ требует не менее Δ/M шагов.
-/

namespace Hagi.Dynamics

/-- SPEED LIMIT ОБУЧЕНИЯ (дискретный аналог Seroussi et al.
arXiv 2307.14653): если целевая энергия убывает не быстрее
M за шаг (E (t+1) ≥ E t − M), то спуск на Δ требует
не менее Δ/M шагов: E 0 − E T ≤ T·M. Никакой алгоритм не
обгоняет лимит скорости, заданный максимальной скоростью
рассеяния. -/
theorem learning_time_lower_bound (E : ℕ → ℝ) (M : ℝ)
    (hstep : ∀ t, E (t + 1) ≥ E t - M) (T : ℕ) :
    E 0 - E T ≤ (T : ℝ) * M := by
  have h := Hagi.Foundations.telescope_sum_le
    (f := fun t => -E t) (c := fun _ => M) (T := T)
    (fun t _ => by
      have := hstep t
      linarith)
  have hcast : (∑ i ∈ Finset.range T, (M : ℝ)) = (T : ℝ) * M := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  rw [hcast] at h
  linarith

end Hagi.Dynamics

set_option linter.style.header false

/-!
# CapabilityGain — перенос внутреннего спуска во внешний прирост

Условная бухгалтерия переноса (настоящий мост — в
эмпирических посылках, открыт):

* `capability_gain_transfer`: при декомпозициях
  `Rext1 = E1 + g1`, `Rext2 = E2 + g2`, внутреннем
  сертификате `E2 ≤ E1 − Γ` и неухудшении зазора `g2 ≤ g1` —
  `Rext2 ≤ Rext1 − Γ`;
* `pb_gap_bound_mono`: при `KL2 ≤ KL1` —
  `KL2 + base ≤ KL1 + base` (монотонность оценки зазора
  PAC-Bayes по бюджету KL; актуальный зазор — h_emp_
  до моста CertifiedEstimator).
-/

open Real Finset

namespace Hagi.Dynamics

/-- При `Rext1 = E1 + g1`, `Rext2 = E2 + g2`, `E2 ≤ E1 − Gamma`
и `g2 ≤ g1` — `Rext2 ≤ Rext1 − Gamma` (бухгалтерская
лемма; эмпирическое содержание — в посылках hcert и hgap). -/
theorem capability_gain_transfer (E1 E2 g1 g2 Rext1 Rext2 Gamma : ℝ)
    (hR1 : Rext1 = E1 + g1) (hR2 : Rext2 = E2 + g2)
    (hcert : E2 ≤ E1 - Gamma)
    (hgap : g2 ≤ g1) :
    Rext2 ≤ Rext1 - Gamma := by
  rw [hR1, hR2]
  linarith

/-- При `KL2 ≤ KL1` — `KL2 + base ≤ KL1 + base`. -/
theorem pb_gap_bound_mono (KL1 KL2 base : ℝ)
    (hKL : KL2 ≤ KL1) :
    KL2 + base ≤ KL1 + base := by linarith

end Hagi.Dynamics

/-!
# UrgencyDepth — срочность выбирает конфигурацию

* `depth_capped_by_time`: при `0 < δ` и `T·δ ≤ τ` —
  `T ≤ τ/δ`;
* `shallow_misses_tube`: при `(1/κ)^T₀ = x₀/ε` и `T < T₀` —
  `(1/κ)^T < x₀/ε` (мелкая конфигурация не достигает
  ε-трубки); κ ∈ (0,1), `ε > 0`;
* `patient_configuration_reaches`: при
  `x 0/ε ≤ (1/κ)^T₀` — `x T₀ ≤ β·cbar/(1−κ) + ε`
  (композиция с `endpoint_depth_budget`).
-/

namespace Hagi.Dynamics

/-- При `0 < δ` и `(T:ℝ)·δ ≤ τ`: `(T:ℝ) ≤ τ/δ`. -/
theorem depth_capped_by_time (τ δ : ℝ) (T : ℕ)
    (hδ : 0 < δ)
    (hfit : (T : ℝ) * δ ≤ τ) :
    (T : ℝ) ≤ τ / δ := by
  rw [le_div_iff₀ hδ]
  exact hfit

/-- При `0 < κ < 1`, `0 < ε`, `(1/κ)^T₀ = x₀/ε` и `T < T₀`:
`(1/κ)^T < x₀/ε` — бюджет глубины `endpoint_depth_budget`
не выполнен. -/
theorem shallow_misses_tube (κ x₀ ε : ℝ) (T₀ T : ℕ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (heps : 0 < ε) (_hx₀ : 0 < x₀)
    (hneed : (1 / κ) ^ T₀ = x₀ / ε)
    (hshort : T < T₀) :
    (1 / κ) ^ T < x₀ / ε := by
  have hone : 1 < 1 / κ := one_lt_one_div hκ hκ1
  have hmono := pow_lt_pow_right₀ hone hshort
  rw [hneed] at hmono
  exact hmono

/-- При посылках `endpoint_depth_budget` и
`x 0/ε ≤ (1/κ)^T₀` — `x T₀ ≤ β·cbar/(1−κ) + ε`. -/
theorem patient_configuration_reaches (x c : ℕ → ℝ)
    (κ β cbar ε x₀ : ℝ) (T₀ : ℕ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hβ : 0 ≤ β)
    (hcbar : 0 ≤ cbar) (heps : 0 < ε) (hx₀ : 0 < x₀)
    (hcbound : ∀ t, c t ≤ cbar)
    (hstep : ∀ t, x (t + 1) ≤ κ * x t + β * c t)
    (hneed : x 0 / ε ≤ (1 / κ) ^ T₀) :
    x T₀ ≤ β * cbar / (1 - κ) + ε :=
  endpoint_depth_budget x c κ β cbar ε T₀ hκ hκ1 hβ hcbar
    hcbound hstep heps hneed

end Hagi.Dynamics

/-!
# DistillationRate — бюджет rollout-ов для policy KL

Стадия E_dev → G_policy при пошаговой контракции KL
`kl (t+1) ≤ κ_KL·kl t` (измеряемая посылка MOPD-режима).

* `kl_contraction_budget`: при `0 < κ_KL < 1`, `0 < δ` и
  `kl 0/δ ≤ (1/κ_KL)^T` — `kl T ≤ δ` (бюджет логарифмичен
  в начальном зазоре);
* `kl_half_steps`: при `κ_KL = 1/2` —
  `kl T ≤ KL₀·(1/2)^T` (каждый rollout — бит близости).
-/

namespace Hagi.Dynamics

/-- При `0 < κ_KL < 1`, `0 < δ`, `kl (t+1) ≤ κ_KL·kl t` и
`kl 0/δ ≤ (1/κ_KL)^T` — `kl T ≤ δ`. -/
theorem kl_contraction_budget (kl : ℕ → ℝ) (κ_KL δ : ℝ)
    (T : ℕ) (hκ : 0 < κ_KL) (hκ1 : κ_KL < 1)
    (hδ : 0 < δ)
    (hstep : ∀ t, kl (t + 1) ≤ κ_KL * kl t)
    (hneed : kl 0 / δ ≤ (1 / κ_KL) ^ T) :
    kl T ≤ 0 + δ := by
  have h := endpoint_depth_budget kl (fun _ => (0:ℝ)) κ_KL 0 0 δ T
    hκ hκ1 (le_refl 0) (le_refl 0) (fun _ => le_refl 0)
    (fun t => by simpa using hstep t) hδ hneed
  simpa using h

/-- При `kl 0 ≤ KL₀` и `kl (t+1) ≤ (1/2)·kl t` —
`kl T ≤ KL₀·(1/2)^T`. -/
theorem kl_half_steps (kl : ℕ → ℝ) (KL₀ : ℝ) (T : ℕ)
    (h0 : kl 0 ≤ KL₀) (_hKL₀ : 0 ≤ KL₀)
    (hstep : ∀ t, kl (t + 1) ≤ (1 / 2 : ℝ) * kl t) :
    kl T ≤ KL₀ * (1 / 2 : ℝ) ^ T := by
  have hpos : (0:ℝ) < 1 / 2 := by norm_num
  have hκ1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hstep' : ∀ t, kl (t + 1) ≤ (1 / 2 : ℝ) * kl t + 0 * 0 :=
    fun t => by simpa using hstep t
  have hmain := endpoint_bivariate_bound kl (fun _ => (0:ℝ))
    (1 / 2 : ℝ) 0 T (le_of_lt hpos) hκ1 (le_refl 0) hstep'
  have hsum : ∑ i ∈ Finset.range T, (1 / 2 : ℝ) ^ i * 0
      = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [mul_comm, mul_zero]
  rw [hsum, mul_zero, add_zero] at hmain
  have hhalf : (1 / 2 : ℝ) ^ T * kl 0 ≤ (1 / 2 : ℝ) ^ T * KL₀ :=
    mul_le_mul_of_nonneg_left h0 (pow_nonneg (le_of_lt hpos) T)
  calc kl T ≤ (1 / 2 : ℝ) ^ T * kl 0 := hmain
    _ ≤ (1 / 2 : ℝ) ^ T * KL₀ := hhalf
    _ = KL₀ * (1 / 2 : ℝ) ^ T := by ring

end Hagi.Dynamics
