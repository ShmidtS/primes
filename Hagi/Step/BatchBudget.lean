/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Step.StochasticSafeQP
import Hagi.Step.NoisyPL

set_option linter.style.header false

/-!
# Мост m(batch): шумовой пол как функция бюджета измерений

Связка concentration (StochasticSafeQP) -> noisy PL
(шумовой пол 3m^2/(2*mu)): мини-батч из m независимых
сигма-ограниченных нуль-средних оценок даёт
сертифицированный уровень шума
m0 = noiseEps K sigma d m delta (вероятность >= 1-delta):
m0^2 = sigma^2 ||d||^2 * 2 log(|K|/delta) / m.
Подстановка в PL-пол даёт terminal gap <=
3 sigma^2 ||d||^2 log(|K|/delta) / (mu * m).

Обратная задача (budget design): для целевой точности eps
достаточно m >= 3 sigma^2 ||d||^2 log(|K|/delta) / (mu eps)
измерений - количественный ответ "какой батч нужен для
точности eps". Это замыкает бюджетную петлю архитектуры:
точность обучения = функция бюджета измерений, и обратно.
-/

namespace Hagi.Step

variable {X : Type*} [NormedAddCommGroup X]

/-- Подстановка в шумовой пол: если certified noise
`m0^2 <= 2*mu*eps/3`, то `3*m0^2/(2*mu) <= eps`. -/
theorem batch_noise_floor {m0 : ℝ} (μ ε : ℝ)
    (hμ : 0 < μ) (heps : m0 ^ 2 ≤ 2 * μ * ε / 3) :
    3 * m0 ^ 2 / (2 * μ) ≤ ε := by
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * μ)]
  have h1 : 3 * m0 ^ 2 ≤ 2 * μ * ε := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 3)] at heps
    linarith [heps]
  linarith


/-- Квадрат сертифицированного шума: `noiseEps` в квадрате
равно `sigma^2 * ||d||^2 * (2 log(|K|/delta) / m)` — чистая
алгебра (sqrt-подстановка). -/
theorem noiseEps_sq (K : Type*) [Fintype K] [Nonempty K]
    (sigma : ℝ) (d : X)
    (m : ℕ) (hm : 0 < m) (delta : ℝ) (hsigma : 0 ≤ sigma)
    (hdelta : 0 < delta) (hdK : delta ≤ Fintype.card K) :
    noiseEps K sigma d m delta ^ 2
      = sigma ^ 2 * ‖d‖ ^ 2
        * (2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ)) := by
  unfold noiseEps
  have h1 : (sigma * ‖d‖ * Real.sqrt (2 * Real.log
      ((Fintype.card K : ℝ) / delta) / (m : ℝ))) ^ 2
      = sigma ^ 2 * ‖d‖ ^ 2 * (2 * Real.log
        ((Fintype.card K : ℝ) / delta) / (m : ℝ)) := by
    rw [mul_pow]
    have h2 : (sigma * ‖d‖) ^ 2 = sigma ^ 2 * ‖d‖ ^ 2 :=
      by rw [mul_pow]
    rw [h2]
    have h3 : (Real.sqrt (2 * Real.log ((Fintype.card K : ℝ)
        / delta) / (m : ℝ))) ^ 2
        = 2 * Real.log ((Fintype.card K : ℝ) / delta)
          / (m : ℝ) := by
      exact Real.sq_sqrt
        (div_nonneg (by
          have hcard : (0:ℝ) < (Fintype.card K : ℝ) := by
            exact_mod_cast Fintype.card_pos
          have hlog : 0 ≤ Real.log ((Fintype.card K : ℝ) / delta) :=
            Real.log_nonneg ((one_le_div hdelta).mpr
              (by exact_mod_cast hdK))
          linarith)
        (by exact_mod_cast (Nat.le_of_lt hm)))
    rw [h3]
  rw [h1]

/-- ПОЛНАЯ ЦЕПЬ: terminal gap как функция бюджета измерений.
Шумовой пол `3*noiseEps^2/(2*mu) <=
3 sigma^2 ||d||^2 2 log(|K|/delta) / (2 mu m) =
3 sigma^2 ||d||^2 log(|K|/delta) / (mu m)` — точность
обучения как функция батча `m`. -/
theorem batch_terminal_gap (K : Type*) [Fintype K] [Nonempty K]
    (sigma d : ℝ) (m : ℕ) (hm : 0 < m) (delta μ : ℝ)
    (hμ : 0 < μ) (hsigma : 0 ≤ sigma) (hdelta : 0 < delta)
    (hdK : delta ≤ (Fintype.card K : ℕ))
    (eps : ℝ) (hgoal : noiseEps K sigma d m delta ^ 2
      ≤ 2 * μ * eps / 3) :
    3 * sigma ^ 2 * ‖d‖ ^ 2
      * (2 * Real.log ((Fintype.card K : ℝ) / delta))
      / (2 * μ * (m : ℝ)) ≤ eps := by
  have hsq := noiseEps_sq K sigma d m hm delta hsigma hdelta hdK
  have hfloor := batch_noise_floor μ eps hμ hgoal
  rw [hsq] at hfloor
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * μ * (m : ℝ))]
  have hlog : (0:ℝ) ≤ Real.log ((Fintype.card K : ℝ) / delta) := by
    have hcard : (0:ℝ) < (Fintype.card K : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hge : delta ≤ (Fintype.card K : ℝ) := by
      exact_mod_cast hdK
    exact Real.log_nonneg ((one_le_div hdelta).mpr hge)
  have hmp : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h1 : 3 * (sigma ^ 2 * ‖d‖ ^ 2 * (2 * Real.log
      ((Fintype.card K : ℝ) / delta) / (m : ℝ)))
      ≤ eps * (2 * μ) := by
    have h4 := hfloor
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * μ)] at h4
    linarith
  have h2 : 3 * (sigma ^ 2 * ‖d‖ ^ 2 * (2 * Real.log
      ((Fintype.card K : ℝ) / delta) / (m : ℝ))) * (m : ℝ)
      ≤ eps * (2 * μ * (m : ℝ)) := by
    have h5 := mul_le_mul_of_nonneg_right h1 (le_of_lt hmp)
    linarith [h5, mul_assoc eps (2 * μ) (m : ℝ)]
  have h3 : 3 * (sigma ^ 2 * ‖d‖ ^ 2 * (2 * Real.log
      ((Fintype.card K : ℝ) / delta) / (m : ℝ))) * (m : ℝ)
      = 3 * sigma ^ 2 * ‖d‖ ^ 2
        * (2 * Real.log ((Fintype.card K : ℝ) / delta)) := by
    field_simp
  rw [← h3]
  exact h2

end Hagi.Step
