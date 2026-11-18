/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Math.Foundations.Recurrence
import Hagi.Math.Foundations.Telescope
import Mathlib.Tactic
/-!
# Contraction — оператор поколения как контракция

При контракции `E (t+1) ≤ γ·E t + δ` с `γ < 1` (эмпирическая
ставка — посылка):

* `geom_sum_telescope` / `geom_sum_le_inv` — телескоп и
  оценка геометрической суммы (делегация Foundations);
* `contraction_limit`:
  `E t ≤ γ^t·E 0 + δ/(1−γ)` — экспоненциальный вход в шар
  радиуса δ/(1−γ). Метрико-абстрактная форма;
  Wasserstein/Fisher-формы — открыто.
-/

open Finset

namespace Hagi.Dynamics

/-- При `0 ≤ γ < 1` — `Σ_{i<t} γ^i ≤ 1/(1−γ)` (делегация
Foundations). -/
theorem geom_sum_le_inv (gamma : ℝ) (hg : 0 ≤ gamma) (hg1 : gamma < 1) (t : ℕ) :
    ∑ i ∈ Finset.range t, gamma ^ i ≤ 1 / (1 - gamma) :=
  Hagi.Foundations.geom_sum_le_inv gamma t hg hg1

/-- При `0 ≤ γ < 1`, `0 ≤ δ` и `E (t+1) ≤ γ·E t + δ` —
`E t ≤ γ^t·E 0 + δ/(1−γ)` (делегация Foundations). -/
theorem contraction_limit (E : ℕ → ℝ) (gamma delta : ℝ)
    (hg : 0 ≤ gamma) (hg1 : gamma < 1) (hdelta : 0 ≤ delta)
    (hstep : ∀ t, E (t + 1) ≤ gamma * E t + delta) (t : ℕ) :
    E t ≤ gamma ^ t * E 0 + delta / (1 - gamma) :=
  Hagi.Foundations.contraction_limit gamma E delta t hg hg1 hdelta hstep

end Hagi.Dynamics

namespace Hagi
export Hagi.Dynamics (geom_sum_le_inv contraction_limit)
end Hagi

/-!
# EndpointContraction — бюджет фиксированной точки looped-моделей

Бивариантная контракция `x (t+1) ≤ κ·x t + β·c t`
(x — расстояние состояния до endpoint, c — дрейф входов).

* `endpoint_bivariate_bound`:
  `x T ≤ κ^T·x 0 + β·Σ_{i<T} κ^i·c (T−1−i)`;
* `endpoint_geometric_tail`: при `c t ≤ cbar` —
  `x T ≤ κ^T·x 0 + β·cbar/(1−κ)`;
* `endpoint_depth_budget`: при `0 < ε` и
  `x 0/ε ≤ (1/κ)^T` — `x T ≤ β·cbar/(1−κ) + ε`
  (явный бюджет числа итераций — условный на посылки
  контракции).
-/

namespace Hagi.Dynamics

open Finset

/-- При `0 ≤ κ < 1`, `0 ≤ β` и `x (t+1) ≤ κ·x t + β·c t`:
`x T ≤ κ^T·x 0 + β·Σ_{i<T} κ^i·c (T−1−i)`. -/
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


/-- При посылках `endpoint_bivariate_bound` и `c t ≤ cbar`:
`x T ≤ κ^T·x 0 + β·cbar/(1−κ)`. -/
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

/-- При посылках `endpoint_geometric_tail`, `0 < κ < 1`,
`0 < ε` и `x 0/ε ≤ (1/κ)^T`:
`x T ≤ β·cbar/(1−κ) + ε`. -/
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

end Hagi.Dynamics



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
