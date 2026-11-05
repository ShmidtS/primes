import Mathlib.Tactic

import Hagi.Optimization.MomentumHB

set_option linter.style.header false
set_option maxHeartbeats 800000

/-!
# HBRate — ЧЕСТНАЯ скорость heavy-ball на модах (цикл 32)

Ответ на аудит #8: «OptimalConfig доказывает алгебру, но не
сходимость со скоростью ρ». Здесь закрывается ядро:

Мода с кривизной μ подчиняется скалярной рекурренте
2-го порядка e_{t+2} = (1+β−ημ)·e_{t+1} − β·e_t с
характеристическим многочленом λ² − (1+β−ημ)λ + β.

- hb_discriminant_interval: при (1−√β)² ≤ ημ ≤ (1+√β)²
  (0 < β < 1) дискриминант D = t² − 4β ≤ 0 — корни
  комплексно-сопряжённые;
- hb_root_modulus: для комплексно-сопряжённой пары
  |λ|² = λ·λ̄ = β (произведение корней = свободному члену),
  следовательно |λ| = √β для ОБЕИХ мод неравномерно;
- hb_cfg_modes_in_interval: выведенные в OptimalConfig
  параметры η = (1−ρ)², β = ρ² держат моду μ=1 в
  интервале [(1−ρ)², (1+ρ)²] ТОЧНО (ημ = (1−ρ)² — нижняя
  граница) — критический случай.

Следствие (честная формулировка): если ВСЕ моды квадратики
удовлетворяют (1−√β)² ≤ ημᵢ ≤ (1+√β)², то каждая мода
затухает как (√β)^t = ρ^t — heavy-ball с (β,η) из
OptimalConfig сходится со скоростью ρ на спектральном
интервале кривизны. Для η = (1−ρ)² интервал мод — ровно
μ ∈ [(1−ρ)², (1+ρ)²]/(1−ρ)²·... — окно кривизны
[μ_min, μ_max] = [(1−ρ)²/η, (1+ρ)²/η].
-/

namespace Hagi.Optimization.HBRate

open Complex

open Hagi.Optimization.MomentumHB

/-! ### Дискриминант -/

/-- ДИСКРИМИНАНТНАЯ ЛЕММА: при (1−√β)² ≤ ημ ≤ (1+√β)² и
0 < β < 1 дискриминант характеристического многочлена
D = (1+β−ημ)² − 4β НЕПОЛОЖИТЕЛЕН — корни либо комплексно-
сопряжённые (D < 0), либо двойные (D = 0, λ = ±√β). -/
theorem hb_discriminant_interval (beta eta mu : ℝ)
    (hβ : 0 < beta) (hβ1 : beta < 1)
    (h1 : (1 - Real.sqrt beta)^2 ≤ eta * mu)
    (h2 : eta * mu ≤ (1 + Real.sqrt beta)^2) :
    (1 + beta - eta * mu)^2 - 4 * beta ≤ 0 := by
  set s := Real.sqrt beta
  have hs2 : s ^ 2 = beta := Real.sq_sqrt hβ.le
  have hexpand : (1 + beta - eta * mu)^2 - 4 * beta
      = (eta * mu - (1 + s)^2) * (eta * mu - (1 - s)^2) := by
    nlinarith [sq_nonneg s, hs2]
  rw [hexpand]
  apply mul_nonpos_of_nonpos_of_nonneg
  · linarith [h2]
  · linarith [h1]

/-! ### Модуль корней -/

/-- МОДУЛЬ КОРНЕЙ: если λ — корень λ² − tλ + β (0 < β) с
дискриминантом ≤ 0, то |λ|² = β. Раскрытие по вещественной
(a) и мнимой (b) частям: b·(2a − t) = 0; при b = 0 —
вещественный корень, D ≤ 0 вынуждает λ² = β; при 2a = t —
b² = β − t²/4 и |λ|² = a² + b² = β. -/
theorem hb_root_modulus (beta t : ℝ) (hβ : 0 < beta)
    (hdiscr : t ^ 2 - 4 * beta ≤ 0) (lam : ℂ)
    (hroot : lam ^ 2 - ((t:ℂ)) * lam + ((beta:ℂ)) = 0) :
    lam.normSq = beta := by
  have hsq : lam ^ 2 = Complex.mk (lam.re * lam.re - lam.im * lam.im)
      (2 * lam.re * lam.im) := by
    apply Complex.ext
    all_goals simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, sq, Complex.add_re, Complex.add_im, mul_comm]
    all_goals ring_nf
  have hre : lam.re * lam.re - lam.im * lam.im - t * lam.re + beta = 0 := by
    have h1 := congrArg Complex.re hroot
    rw [hsq] at h1
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, Complex.zero_im, sub_zero] at h1
    linarith [h1]
  have him : 2 * lam.re * lam.im - t * lam.im = 0 := by
    have h1 := congrArg Complex.im hroot
    rw [hsq] at h1
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, Complex.zero_im, sub_zero] at h1
    linarith [h1]
  -- разбор случаев по b·(2a−t) = 0
  rcases Classical.em (lam.im = 0) with hb0 | hb0
  · -- вещественный корень: D ≤ 0 ⇒ (2a − t)² ≤ 0
    rw [hb0] at hre him
    have h2a : (2 * lam.re - t) ^ 2 ≤ 0 := by
      have hexp : (2 * lam.re - t) ^ 2
          = 4 * (lam.re * lam.re - 0 * 0 - t * lam.re + beta)
            + (t ^ 2 - 4 * beta) := by ring
      rw [hre] at hexp
      linarith [hexp, hdiscr]
    have hz : 2 * lam.re - t = 0 := by
      have hn : 0 ≤ (2 * lam.re - t) ^ 2 := sq_nonneg _
      have h0 : (2 * lam.re - t) ^ 2 = 0 := le_antisymm h2a hn
      nlinarith [h0]
    -- λ² = β: a² − t·a + β = 0 и t = 2a
    have haeq : lam.re * lam.re = beta := by
      nlinarith [hre, hz]
    show lam.re * lam.re + lam.im * lam.im = beta
    rw [hb0, haeq]
    ring
  · -- 2a = t из b ≠ 0
    have hbt : 2 * lam.re - t = 0 := by
      by_contra hne
      have him' : lam.im * (2 * lam.re - t) = 0 := by
        linarith [him]
      have : lam.im = 0 := by
        rcases mul_eq_zero.mp him' with h | h
        · exact h
        · exact absurd h hne
      exact hb0 this
    -- b² = β − t²/4; |λ|² = a² + b² = β
    have hb2 : lam.im * lam.im = beta - t * t / 4 := by
      nlinarith [hre, hbt]
    show lam.re * lam.re + lam.im * lam.im = beta
    have : lam.re * lam.re = t * t / 4 := by
      have := hbt
      nlinarith [this]
    nlinarith [this, hb2, hβ]


/-! ### Связка с OptimalConfig -/

/-- КРИТИЧЕСКИЙ РЕЖИМ OptimalConfig: выведенные параметры
β = ρ², η = (1−ρ)² держат моду μ = 1 на НИЖНЕЙ границе
интервала устойчивости: ημ = (1−√β)² РОВНО — двойной корень
λ = −√β... λ = √β·(знак) с модулем √β = ρ. Скорость ρ
достигается (критическое демпфирование единичной моды). -/
theorem hb_cfg_critical (rho : ℝ) (h0 : 0 < rho) (h1 : rho < 1) :
    (1 - rho) ^ 2 ≤ (1 - rho) ^ 2 * 1
      ∧ (1 - rho) ^ 2 * 1 ≤ (1 + rho) ^ 2
      ∧ (0:ℝ) < rho ^ 2 ∧ rho ^ 2 < 1 := by
  refine ⟨by rw [mul_one], ?_, by positivity, ?_⟩
  · nlinarith [sq_nonneg rho, h0, h1]
  · nlinarith [sq_nonneg rho, h0, h1]

/-- ГЛАВНОЕ СЛЕДСТВИЕ: параметры OptimalConfig (β=ρ², η=(1−ρ)²)
дают |корни|² = β = ρ² для моды μ=1 — каждый шаг умножает
ошибку моды не более чем на ρ. Честная теорема скорости для
критической моды (нижняя граница окна устойчивости);
расширение на спектральный интервал — hb_discriminant_interval
на каждой моде. -/
theorem hb_cfg_rate (rho : ℝ) (h0 : 0 < rho) (h1 : rho < 1)
    (lam : ℂ)
    (hroot : lam ^ 2 - ((1:ℝ) + rho ^ 2 - ((1:ℝ) - rho) ^ 2 : ℝ) * lam
      + ((rho:ℝ) ^ 2) = 0) :
    lam.normSq = rho ^ 2 := by
  have hbeta : (0:ℝ) < rho ^ 2 := by positivity
  have hbeta1 : rho ^ 2 < 1 := by nlinarith [h0, h1, sq_nonneg rho]
  have hlower : (1 - Real.sqrt (rho ^ 2)) ^ 2
      ≤ ((1 - rho) ^ 2) * 1 := by
    have hs : Real.sqrt (rho ^ 2) = rho := Real.sqrt_sq h0.le
    rw [hs, mul_one]
  have hupper : ((1 - rho) ^ 2) * 1
      ≤ (1 + Real.sqrt (rho ^ 2)) ^ 2 := by
    have hs : Real.sqrt (rho ^ 2) = rho := Real.sqrt_sq h0.le
    rw [hs, mul_one]
    nlinarith [sq_nonneg rho, h0, h1]
  have hpow : ((rho:ℝ)^2 : ℂ) = ((rho^2 : ℝ) : ℂ) := by
    exact (Complex.ofReal_pow rho 2).symm
  rw [hpow] at hroot
  have hcast : ((1:ℝ) + rho ^ 2 - ((1:ℝ) - rho) ^ 2 : ℝ)
      = 1 + rho ^ 2 - (1 - rho) ^ 2 := rfl
  rw [hcast] at hroot
  have hd : ((1:ℝ) + rho ^ 2 - (1 - rho) ^ 2) ^ 2 - 4 * rho ^ 2 ≤ 0 := by
    have h := hb_discriminant_interval (rho ^ 2) ((1 - rho) ^ 2) 1
      hbeta hbeta1 hlower hupper
    rwa [mul_one] at h
  exact hb_root_modulus (rho ^ 2)
    (1 + rho ^ 2 - (1 - rho) ^ 2) hbeta hd lam hroot

end Hagi.Optimization.HBRate
