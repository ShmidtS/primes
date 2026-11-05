import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2

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

Следствие ограничим точно: если ВСЕ моды квадратики удовлетворяют
(1−√β)² ≤ ημᵢ ≤ (1+√β)², то доказанные здесь результаты фиксируют
модули характеристических корней. Сам по себе модуль корня ещё не
является оценкой траектории: при кратном корне возникает Jordan-
фактор n, поэтому чистая оценка |e_n| ≤ Cρ^n в общем случае неверна.

Цикл 43 добавляет траекторный результат для критической скалярной
моды. Каноническая скалярная рекуррента 2-го порядка рассматривается
отдельно от старой пары `(hbErr, hbVel)` Heavy Ball:
`hb_pair_second_order` даёт для этой пары свободный коэффициент
`β + η·(1−β)`, а не `β`. Поэтому спектральные результаты для
канонического многочлена нельзя неявно применять к указанной паре.
Для канонической рекурренты при двойном корне ρ получена точная форма
(C+D·n)·ρ^n и оценка |e_n| ≤ (|e_0|+|e_1/ρ−e_0|·n)·ρ^n.
Это критическая скалярная мода, а не утверждение о полном спектре.

Цикл 44 добавляет двухкорневую траекторию `Aλ₁^n+Bλ₂^n`,
явные коэффициенты при λ₁≠λ₂ и мост корневых модулей к
оценке `(‖A‖+‖B‖)·(√β)^n`. Различные корни и комплексные
внутренние моды теперь покрыты на scalar-носителе. Следующие
frontier — положительный дискриминант и векторная сборка.
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
λ = −√β... λ = √β·(знак) с модулем √β = ρ. Эта теорема
фиксирует только параметрическое окно и диапазон β; оценка
траектории доказывается отдельно с Jordan-фактором. -/
theorem hb_cfg_critical (rho : ℝ) (h0 : 0 < rho) (h1 : rho < 1) :
    (1 - rho) ^ 2 ≤ (1 - rho) ^ 2 * 1
      ∧ (1 - rho) ^ 2 * 1 ≤ (1 + rho) ^ 2
      ∧ (0:ℝ) < rho ^ 2 ∧ rho ^ 2 < 1 := by
  refine ⟨by rw [mul_one], ?_, by positivity, ?_⟩
  · nlinarith [sq_nonneg rho, h0, h1]
  · nlinarith [sq_nonneg rho, h0, h1]

/-- ГЛАВНОЕ СЛЕДСТВИЕ: параметры OptimalConfig (β=ρ², η=(1−ρ)²)
дают |корни|² = β = ρ² для моды μ=1. Это утверждение ТОЛЬКО о
модуле характеристического корня, а не о пошаговом умножении
ошибки на ρ: при кратном корне возникает Jordan-фактор `n`.
Оценка траектории критической скалярной моды доказана отдельно
в `hb_critical_trajectory_bound`; расширение корневого результата
на спектральный интервал — `hb_discriminant_interval` на каждой моде. -/
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


/-! ### Спектральное расширение (цикл 33) -/

/-- СПЕКТРАЛЬНАЯ МОДА: если кривизна μ лежит в окне
[(1−√β)²/η, (1+√β)²/η] (т.е. (1−√β)² ≤ ημ ≤ (1+√β)²), то
ЛЮБОЙ корень характеристического многочлена моды имеет
|λ|² = β. Это результат только о модуле корня: сам по себе он не
утверждает затухание траектории как `(√β)^t`. Композиция
hb_discriminant_interval + hb_root_modulus. -/
theorem hb_spectral_mode (beta eta mu : ℝ) (hβ : 0 < beta)
    (hβ1 : beta < 1) (hmu : 0 < mu)
    (h1 : (1 - Real.sqrt beta)^2 ≤ eta * mu)
    (h2 : eta * mu ≤ (1 + Real.sqrt beta)^2)
    (lam : ℂ)
    (hroot : lam ^ 2 - ((1 + beta - eta * mu : ℝ)) * lam
      + ((beta : ℝ)) = 0) :
    lam.normSq = beta :=
  hb_root_modulus beta (1 + beta - eta * mu) hβ
    (hb_discriminant_interval beta eta mu hβ hβ1 h1 h2) lam hroot

/-- КЛАССИЧЕСКИЙ ОПТИМАЛЬНЫЙ ТЕМП: для числа обусловленности
κ ≥ 1 выбор ρ = (√κ − 1)/(√κ + 1) даёт
(1−ρ)²/(1+ρ)² = 1/κ — окно кривизны HB с β = ρ² покрывает
масштаб [1/κ, 1] ровно. Это тождество, стоящее за
Chebyshev-оптимальностью heavy-ball (нижняя √κ-граница —
отдельная теорема, не претендуем). -/
theorem hb_rate_from_kappa (kappa : ℝ) (h : 1 ≤ kappa) :
    ((1 - (Real.sqrt kappa - 1) / (Real.sqrt kappa + 1))
        / (1 + (Real.sqrt kappa - 1) / (Real.sqrt kappa + 1))) ^ 2
      = 1 / kappa := by
  have hs : 0 < Real.sqrt kappa := by positivity
  have h1 : 1 - (Real.sqrt kappa - 1) / (Real.sqrt kappa + 1)
      = 2 / (Real.sqrt kappa + 1) := by
    field_simp
    ring
  have h2 : 1 + (Real.sqrt kappa - 1) / (Real.sqrt kappa + 1)
      = 2 * Real.sqrt kappa / (Real.sqrt kappa + 1) := by
    field_simp
    ring
  rw [h1, h2]
  have hk : Real.sqrt kappa ^ 2 = kappa := Real.sq_sqrt (by positivity)
  field_simp
  rw [hk]

/-- ρ из κ ∈ [1, ∞) корректно определён: 0 ≤ ρ < 1. -/
theorem hb_rho_range (kappa : ℝ) (h : 1 ≤ kappa) :
    0 ≤ (Real.sqrt kappa - 1) / (Real.sqrt kappa + 1)
      ∧ (Real.sqrt kappa - 1) / (Real.sqrt kappa + 1) < 1 := by
  have hs : 1 ≤ Real.sqrt kappa := by
    exact Real.one_le_sqrt.mpr h
  constructor
  · apply div_nonneg
    · linarith [hs]
    · positivity
  · rw [div_lt_iff₀ (by positivity : (0:ℝ) < Real.sqrt kappa + 1)]
    nlinarith [hs]


/-! ### Общие параметры (L, μ) — κ-оптимальность на спектре (цикл 37) -/

/-- ОБЩИЕ ПАРАМЕТРЫ HB для спектра [μ, L], 0 < μ ≤ L:
β = ((√L−√μ)/(√L+√μ))², η = 4/(√L+√μ)². Критическая мода μ:
ημ = (1−√β)² ТОЧНО (критическое демпфирование нижней моды). -/
theorem hb_general_eta_mu (L mu : ℝ) (hμ : 0 < mu) (hL : mu ≤ L) :
    (4 / (Real.sqrt L + Real.sqrt mu)^2) * mu
      = (1 - Real.sqrt (((Real.sqrt L - Real.sqrt mu)
          / (Real.sqrt L + Real.sqrt mu))^2))^2 := by
  have hLpos : (0:ℝ) < L := lt_of_lt_of_le hμ hL
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hsm : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hμ
  have hsum : 0 < Real.sqrt L + Real.sqrt mu := by positivity
  have hsbeta : Real.sqrt (((Real.sqrt L - Real.sqrt mu)
      / (Real.sqrt L + Real.sqrt mu))^2)
      = (Real.sqrt L - Real.sqrt mu) / (Real.sqrt L + Real.sqrt mu) :=
    Real.sqrt_sq (div_nonneg
      (by
        have h := Real.sqrt_le_sqrt (show mu ≤ L by assumption)
        linarith [Real.sqrt_nonneg mu, Real.sqrt_nonneg L])
      (by positivity))
  rw [hsbeta]
  have hkey : (1 - (Real.sqrt L - Real.sqrt mu)
      / (Real.sqrt L + Real.sqrt mu))
      = 2 * Real.sqrt mu / (Real.sqrt L + Real.sqrt mu) := by
    field_simp
    ring
  rw [hkey]
  have hmusq : Real.sqrt mu ^ 2 = mu := Real.sq_sqrt hμ.le
  rw [div_pow]
  field_simp
  linarith [hmusq]

/-- Верхняя мода L: ηL = (1+√β)² ТОЧНО — окно кривизны
[(1−√β)², (1+√β)²] покрывает спектр [μ, L] РОВНО по краям. -/
theorem hb_general_eta_L (L mu : ℝ) (hμ : 0 < mu) (hL : mu ≤ L) :
    (4 / (Real.sqrt L + Real.sqrt mu)^2) * L
      = (1 + Real.sqrt (((Real.sqrt L - Real.sqrt mu)
          / (Real.sqrt L + Real.sqrt mu))^2))^2 := by
  have hLpos : (0:ℝ) < L := lt_of_lt_of_le hμ hL
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hsm : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hμ
  have hsbeta : Real.sqrt (((Real.sqrt L - Real.sqrt mu)
      / (Real.sqrt L + Real.sqrt mu))^2)
      = (Real.sqrt L - Real.sqrt mu) / (Real.sqrt L + Real.sqrt mu) :=
    Real.sqrt_sq (div_nonneg
      (by
        have h := Real.sqrt_le_sqrt (show mu ≤ L by assumption)
        linarith [Real.sqrt_nonneg mu, Real.sqrt_nonneg L])
      (by positivity))
  rw [hsbeta]
  have hkey : (1 + (Real.sqrt L - Real.sqrt mu)
      / (Real.sqrt L + Real.sqrt mu))
      = 2 * Real.sqrt L / (Real.sqrt L + Real.sqrt mu) := by
    field_simp
    ring
  rw [hkey]
  have hLsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLpos.le
  rw [div_pow]
  field_simp
  linarith [hLsq]

/-- ГЛАВНАЯ ТЕОРЕМА ОКНА: при общих параметрах (β, η) из (L, μ)
ЛЮБАЯ мода λ ∈ [μ, L] попадает в окно устойчивости:
(1−√β)² ≤ ηλ ≤ (1+√β)² (монотонность между краями). Вместе с
hb_spectral_mode это фиксирует модули характеристических корней
всех мод спектра, но НЕ полный темп их траекторий. Траектории
внутренних мод и случай различных корней остаются открытыми. -/
theorem hb_general_window (L mu lam : ℝ) (hμ : 0 < mu)
    (hL : mu ≤ L) (hlam : mu ≤ lam) (hlamL : lam ≤ L) :
    (1 - Real.sqrt (((Real.sqrt L - Real.sqrt mu)
          / (Real.sqrt L + Real.sqrt mu))^2))^2
      ≤ (4 / (Real.sqrt L + Real.sqrt mu)^2) * lam
      ∧ (4 / (Real.sqrt L + Real.sqrt mu)^2) * lam
        ≤ (1 + Real.sqrt (((Real.sqrt L - Real.sqrt mu)
          / (Real.sqrt L + Real.sqrt mu))^2))^2 := by
  have hlo := hb_general_eta_mu L mu hμ hL
  have hhi := hb_general_eta_L L mu hμ hL
  have hpos : (0:ℝ) < 4 / (Real.sqrt L + Real.sqrt mu)^2 := by
    have hd : (0:ℝ) < (Real.sqrt L + Real.sqrt mu)^2 := by positivity
    positivity
  constructor
  · have := mul_le_mul_of_nonneg_left hlam hpos.le
    rw [← hlo]
    linarith [mul_le_mul_of_nonneg_left hlam hpos.le, hlo]
  · have := mul_le_mul_of_nonneg_left hlamL hpos.le
    rw [← hhi]
    linarith [mul_le_mul_of_nonneg_left hlamL hpos.le, hhi]

/-- ИТОГОВЫЙ ТЕМП: √β общих параметров = (√L−√μ)/(√L+√μ)
(эквивалентно (√κ−1)/(√κ+1) при κ = L/μ — см.
hb_rate_from_kappa). -/
theorem hb_general_rate (L mu : ℝ) (hμ : 0 < mu) (hL : mu ≤ L) :
    Real.sqrt (((Real.sqrt L - Real.sqrt mu)
      / (Real.sqrt L + Real.sqrt mu))^2)
      = (Real.sqrt L - Real.sqrt mu) / (Real.sqrt L + Real.sqrt mu) :=
  Real.sqrt_sq (div_nonneg
    (by
      have h := Real.sqrt_le_sqrt hL
      linarith [Real.sqrt_nonneg mu, Real.sqrt_nonneg L])
    (by positivity))

/-! ### Траектория критической моды (цикл 43) -/

/-- Вторая скалярная рекуррента реальной пары Heavy Ball: два шага
исключают скорость `v`. Для указанной дискретизации свободный
коэффициент равен `β + η·(1−β)` (а не просто `β`); это точное
динамическое тождество, без предположений о корнях или сходимости. -/
theorem hb_pair_second_order (e v : ℕ → ℝ) (eta beta : ℝ)
    (herr : ∀ n, e (n + 1) = (1 - eta) * e n + v n)
    (hvel : ∀ n, v (n + 1) = beta * v n - eta * e n) :
    ∀ n, e (n + 2) =
      (1 + beta - eta) * e (n + 1) - (beta + eta * (1 - beta)) * e n := by
  intro n
  calc
    e (n + 2) = (1 - eta) * e (n + 1) + v (n + 1) := by
      simpa only [Nat.add_assoc] using herr (n + 1)
    _ = (1 + beta - eta) * e (n + 1) - (beta + eta * (1 - beta)) * e n := by
      rw [hvel n]
      have hv : v n = e (n + 1) - (1 - eta) * e n := by
        rw [herr n]
        ring
      rw [hv]
      ring

/-- Обратный свидетель к `hb_repeated_root_closed_form`: каждая
последовательность `(C + D·n)·ρ^n` удовлетворяет рекурренте с
двойным корнем `ρ`. Тем самым предположение `hrec` непусто.
Переход от произвольного решения к этой форме доказан ниже
при совместимых начальных данных; явные `C = e₀` и
`D = e₁/ρ − e₀` корректны при `ρ ≠ 0`. -/
theorem hb_repeated_root_form_solves (rho C D : ℝ) :
    ∀ n : ℕ, (fun n : ℕ => (C + D * n) * rho ^ n) (n + 2) =
      2 * rho * (fun n : ℕ => (C + D * n) * rho ^ n) (n + 1)
        - rho ^ 2 * (fun n : ℕ => (C + D * n) * rho ^ n) n := by
  intro n
  simp only [pow_succ, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- Точная форма решения рекурренты с двойным корнем `ρ`:
`e_n = (C + D·n)·ρ^n`. Jordan-фактор `n` при кратном корне обязателен:
это не утверждение о чистой экспоненте `C·ρ^n`. Доказательство —
сильная индукция с двумя начальными значениями. -/
theorem hb_repeated_root_closed_form (e : ℕ → ℝ) (rho C D : ℝ)
    (hrec : ∀ n, e (n + 2) = 2 * rho * e (n + 1) - rho ^ 2 * e n)
    (h0 : e 0 = C) (h1 : e 1 = (C + D) * rho) :
    ∀ n, e n = (C + D * n) * rho ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simpa using h0
    | 1 => simpa using h1
    | n + 2 =>
      rw [hrec n, ih (n + 1) (by omega), ih n (by omega)]
      simp only [pow_succ, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      ring

/-- Оценка траектории критической скалярной моды Heavy Ball. Коэффициент
`1 + ρ² − (1−ρ)² = 2ρ` даёт двойной корень `ρ`; отсюда точная форма
`(C + D·n)·ρ^n` с `C = e_0`, `D = e_1/ρ − e_0`. Jordan-фактор `n`
нельзя в общем случае опускать при кратном корне, поэтому мы не заявляем
чистую оценку `C·ρ^n`. Это результат об одной критической скалярной
моде, а не о полном спектре или векторной динамике. -/
theorem hb_critical_trajectory_bound (e : ℕ → ℝ) (rho : ℝ)
    (h0 : 0 < rho)
    (hrec : ∀ n, e (n + 2) =
      (1 + rho ^ 2 - (1 - rho) ^ 2) * e (n + 1) - rho ^ 2 * e n) :
    ∀ n, |e n| ≤ (|e 0| + |e 1 / rho - e 0| * n) * rho ^ n := by
  have hrho : rho ≠ 0 := ne_of_gt h0
  have hcoeff : 1 + rho ^ 2 - (1 - rho) ^ 2 = 2 * rho := by ring
  have hrec' : ∀ n, e (n + 2) = 2 * rho * e (n + 1) - rho ^ 2 * e n := by
    intro n
    simpa only [hcoeff] using hrec n
  have hinit : e 1 = (e 0 + (e 1 / rho - e 0)) * rho := by
    calc
      e 1 = (e 1 / rho) * rho := (div_mul_cancel₀ (e 1) hrho).symm
      _ = (e 0 + (e 1 / rho - e 0)) * rho := by ring
  have hclosed : ∀ n, e n = (e 0 + (e 1 / rho - e 0) * n) * rho ^ n :=
    hb_repeated_root_closed_form e rho (e 0) (e 1 / rho - e 0)
      hrec' rfl hinit
  intro n
  rw [hclosed n, abs_mul, abs_of_nonneg (pow_nonneg h0.le n)]
  calc
    |e 0 + (e 1 / rho - e 0) * (n : ℝ)| * rho ^ n
      ≤ (|e 0| + |(e 1 / rho - e 0) * (n : ℝ)|) * rho ^ n :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) (pow_nonneg h0.le n)
    _ = (|e 0| + |e 1 / rho - e 0| * n) * rho ^ n := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-! ### Различные корни внутренней моды (цикл 44) -/

/-- Семейство двух экспонент удовлетворяет рекурренте, если
каждое основание — корень её характеристического многочлена.
Различность корней здесь не нужна: она понадобится только
для единственного восстановления коэффициентов по `e₀,e₁`. -/
theorem hb_two_root_form_solves (t beta lam1 lam2 A B : ℂ)
    (hroot1 : lam1 ^ 2 - t * lam1 + beta = 0)
    (hroot2 : lam2 ^ 2 - t * lam2 + beta = 0) :
    ∀ n : ℕ, A * lam1 ^ (n + 2) + B * lam2 ^ (n + 2) =
      t * (A * lam1 ^ (n + 1) + B * lam2 ^ (n + 1))
        - beta * (A * lam1 ^ n + B * lam2 ^ n) := by
  have hr1 : lam1 ^ 2 = t * lam1 - beta := by
    linear_combination hroot1
  have hr2 : lam2 ^ 2 = t * lam2 - beta := by
    linear_combination hroot2
  intro n
  calc
    A * lam1 ^ (n + 2) + B * lam2 ^ (n + 2) =
        A * (lam1 ^ n * lam1 ^ 2) + B * (lam2 ^ n * lam2 ^ 2) := by
      simp only [pow_succ]
      ring
    _ = A * (lam1 ^ n * (t * lam1 - beta))
        + B * (lam2 ^ n * (t * lam2 - beta)) := by rw [hr1, hr2]
    _ = t * (A * lam1 ^ (n + 1) + B * lam2 ^ (n + 1))
        - beta * (A * lam1 ^ n + B * lam2 ^ n) := by
      simp only [pow_succ]
      ring

/-- Решение с двумя характеристическими корнями: начальные
равенства фиксируют разложение в базисе двух экспонент,
после чего сильная индукция применяет `hb_two_root_form_solves`. -/
theorem hb_two_root_closed_form (e : ℕ → ℂ) (t beta lam1 lam2 A B : ℂ)
    (hrec : ∀ n, e (n + 2) = t * e (n + 1) - beta * e n)
    (hroot1 : lam1 ^ 2 - t * lam1 + beta = 0)
    (hroot2 : lam2 ^ 2 - t * lam2 + beta = 0)
    (h0 : e 0 = A + B) (h1 : e 1 = A * lam1 + B * lam2) :
    ∀ n, e n = A * lam1 ^ n + B * lam2 ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simpa using h0
    | 1 => simpa using h1
    | n + 2 =>
      rw [hrec n, ih (n + 1) (by omega), ih n (by omega)]
      symm
      exact hb_two_root_form_solves t beta lam1 lam2 A B hroot1 hroot2 n

/-- При РАЗЛИЧНЫХ корнях коэффициенты разложения начальных
`e₀,e₁` вычисляются явно, без скрытого деления на нуль. -/
theorem hb_distinct_root_init (e0 e1 lam1 lam2 : ℂ)
    (hne : lam1 ≠ lam2) :
    let A := (e1 - lam2 * e0) / (lam1 - lam2)
    let B := (lam1 * e0 - e1) / (lam1 - lam2)
    e0 = A + B ∧ e1 = A * lam1 + B * lam2 := by
  dsimp only
  have hden : lam1 - lam2 ≠ 0 := sub_ne_zero.mpr hne
  constructor <;> field_simp [hden] <;> ring

/-- Полная явная траектория для двух РАЗЛИЧНЫХ корней.
Формула вычислима по начальным значениям и не требует
ненулевых `lam1`, `lam2`: нулевой в знаменателе только их разность. -/
theorem hb_distinct_root_explicit (e : ℕ → ℂ) (t beta lam1 lam2 : ℂ)
    (hne : lam1 ≠ lam2)
    (hrec : ∀ n, e (n + 2) = t * e (n + 1) - beta * e n)
    (hroot1 : lam1 ^ 2 - t * lam1 + beta = 0)
    (hroot2 : lam2 ^ 2 - t * lam2 + beta = 0) :
    ∀ n, e n = ((e 1 - lam2 * e 0) / (lam1 - lam2)) * lam1 ^ n
      + ((lam1 * e 0 - e 1) / (lam1 - lam2)) * lam2 ^ n := by
  let A := (e 1 - lam2 * e 0) / (lam1 - lam2)
  let B := (lam1 * e 0 - e 1) / (lam1 - lam2)
  obtain ⟨h0, h1⟩ := hb_distinct_root_init (e 0) (e 1) lam1 lam2 hne
  exact hb_two_root_closed_form e t beta lam1 lam2 A B hrec
    hroot1 hroot2 h0 h1

/-- Норма двухкорневой траектории ограничена суммой модулей
составляющих экспонент. При `|lam1|,|lam2| ≤ ρ` это даст
единый темп без Jordan-фактора; здесь не добавляется лишняя
посылка о различности или ненулевости корней. -/
theorem hb_two_root_norm_bound (e : ℕ → ℂ) (t beta lam1 lam2 A B : ℂ)
    (hrec : ∀ n, e (n + 2) = t * e (n + 1) - beta * e n)
    (hroot1 : lam1 ^ 2 - t * lam1 + beta = 0)
    (hroot2 : lam2 ^ 2 - t * lam2 + beta = 0)
    (h0 : e 0 = A + B) (h1 : e 1 = A * lam1 + B * lam2) (n : ℕ) :
    ‖e n‖ ≤ ‖A‖ * ‖lam1‖ ^ n + ‖B‖ * ‖lam2‖ ^ n := by
  rw [hb_two_root_closed_form e t beta lam1 lam2 A B hrec
    hroot1 hroot2 h0 h1 n]
  calc
    ‖A * lam1 ^ n + B * lam2 ^ n‖
      ≤ ‖A * lam1 ^ n‖ + ‖B * lam2 ^ n‖ := norm_add_le _ _
    _ = ‖A‖ * ‖lam1‖ ^ n + ‖B‖ * ‖lam2‖ ^ n := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow]

/-- Общий модуль обоих корней сворачивает двухкорневую
оценку в одну экспоненту. Коэффициент зависит только от
разложения начальных данных; Jordan-фактор не возникает. -/
theorem hb_two_root_common_norm_bound (e : ℕ → ℂ)
    (t beta lam1 lam2 A B : ℂ) (rho : ℝ)
    (hrec : ∀ n, e (n + 2) = t * e (n + 1) - beta * e n)
    (hroot1 : lam1 ^ 2 - t * lam1 + beta = 0)
    (hroot2 : lam2 ^ 2 - t * lam2 + beta = 0)
    (h0 : e 0 = A + B) (h1 : e 1 = A * lam1 + B * lam2)
    (hnorm1 : ‖lam1‖ = rho) (hnorm2 : ‖lam2‖ = rho) (n : ℕ) :
    ‖e n‖ ≤ (‖A‖ + ‖B‖) * rho ^ n := by
  have h := hb_two_root_norm_bound e t beta lam1 lam2 A B hrec
    hroot1 hroot2 h0 h1 n
  rw [hnorm1, hnorm2] at h
  calc
    ‖e n‖ ≤ ‖A‖ * rho ^ n + ‖B‖ * rho ^ n := h
    _ = (‖A‖ + ‖B‖) * rho ^ n := by ring

/-- СПЕКТРАЛЬНАЯ ДВУХКОРНЕВАЯ ТРАЕКТОРИЯ: при β>0 и
неположительном дискриминанте оба корня имеют модуль √β,
поэтому разложение по двум корням ограничено
`(‖A‖+‖B‖)·(√β)^n`. Это мост `hb_root_modulus` к реальной
траектории, а не утверждение о любом решении кратного корня. -/
theorem hb_two_root_spectral_norm_bound (e : ℕ → ℂ)
    (t : ℝ) (beta : ℝ) (lam1 lam2 A B : ℂ)
    (hβ : 0 < beta) (hdiscr : t ^ 2 - 4 * beta ≤ 0)
    (hrec : ∀ n, e (n + 2) = (t : ℂ) * e (n + 1) - (beta : ℂ) * e n)
    (hroot1 : lam1 ^ 2 - (t : ℂ) * lam1 + (beta : ℂ) = 0)
    (hroot2 : lam2 ^ 2 - (t : ℂ) * lam2 + (beta : ℂ) = 0)
    (h0 : e 0 = A + B) (h1 : e 1 = A * lam1 + B * lam2) (n : ℕ) :
    ‖e n‖ ≤ (‖A‖ + ‖B‖) * (Real.sqrt beta) ^ n := by
  have hsq1 : lam1.normSq = beta := hb_root_modulus beta t hβ hdiscr lam1 hroot1
  have hsq2 : lam2.normSq = beta := hb_root_modulus beta t hβ hdiscr lam2 hroot2
  have hnorm1 : ‖lam1‖ = Real.sqrt beta := by
    rw [Complex.normSq_eq_norm_sq] at hsq1
    rw [← hsq1]
    exact (Real.sqrt_sq (norm_nonneg lam1)).symm
  have hnorm2 : ‖lam2‖ = Real.sqrt beta := by
    rw [Complex.normSq_eq_norm_sq] at hsq2
    rw [← hsq2]
    exact (Real.sqrt_sq (norm_nonneg lam2)).symm
  exact hb_two_root_common_norm_bound e (t : ℂ) (beta : ℂ) lam1 lam2 A B
    (Real.sqrt beta) hrec hroot1 hroot2 h0 h1 hnorm1 hnorm2 n

/-- Общая верхняя граница модулей корней: при `|λᵢ| ≤ ρ`
двухкорневая траектория ограничена одной экспонентой.
Это НЕ требует равенства модулей и работает при любом дискриминанте. -/
theorem hb_two_root_norm_cap (e : ℕ → ℂ) (t beta lam1 lam2 A B : ℂ)
    (rho : ℝ)
    (hrec : ∀ n, e (n + 2) = t * e (n + 1) - beta * e n)
    (hroot1 : lam1 ^ 2 - t * lam1 + beta = 0)
    (hroot2 : lam2 ^ 2 - t * lam2 + beta = 0)
    (h0 : e 0 = A + B) (h1 : e 1 = A * lam1 + B * lam2)
    (hnorm1 : ‖lam1‖ ≤ rho) (hnorm2 : ‖lam2‖ ≤ rho) (n : ℕ) :
    ‖e n‖ ≤ (‖A‖ + ‖B‖) * rho ^ n := by
  have h := hb_two_root_norm_bound e t beta lam1 lam2 A B hrec
    hroot1 hroot2 h0 h1 n
  have hp1 : ‖lam1‖ ^ n ≤ rho ^ n :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm1 n
  have hp2 : ‖lam2‖ ^ n ≤ rho ^ n :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm2 n
  calc
    ‖e n‖ ≤ ‖A‖ * ‖lam1‖ ^ n + ‖B‖ * ‖lam2‖ ^ n := h
    _ ≤ ‖A‖ * rho ^ n + ‖B‖ * rho ^ n := by
      exact add_le_add (mul_le_mul_of_nonneg_left hp1 (norm_nonneg A))
        (mul_le_mul_of_nonneg_left hp2 (norm_nonneg B))
    _ = (‖A‖ + ‖B‖) * rho ^ n := by ring

/-- Явный вещественный корень квадратного характеристического
многочлена: λ = (t + s√(t²−4β))/2, s=±1.
Дискриминант неотрицателен по условию, поэтому корень вещественный. -/
theorem hb_real_root_pm (t beta s : ℝ) (hs : s = 1 ∨ s = -1)
    (hd : 0 ≤ t ^ 2 - 4 * beta) :
    ((t + s * Real.sqrt (t ^ 2 - 4 * beta)) / 2) ^ 2
      - t * ((t + s * Real.sqrt (t ^ 2 - 4 * beta)) / 2) + beta = 0 := by
  have hsq : Real.sqrt (t ^ 2 - 4 * beta) ^ 2 = t ^ 2 - 4 * beta :=
    Real.sq_sqrt hd
  rcases hs with rfl | rfl <;> field_simp <;> nlinarith [hsq]

/-- Оценка абсолютного значения квадратного корневого выражения
через `(|t| + √(t²−4β))/2`. При отрицательном D этот Lean-sqrt
равен нулю, и теорема НЕ объявляет выражение вещественным корнем. -/
theorem hb_real_root_pm_norm (t beta s : ℝ) (hs : s = 1 ∨ s = -1) :
    |(t + s * Real.sqrt (t ^ 2 - 4 * beta)) / 2|
      ≤ (|t| + Real.sqrt (t ^ 2 - 4 * beta)) / 2 := by
  have hsabs : |s| = 1 := by
    rcases hs with rfl | rfl <;> simp
  have hsqrt : 0 ≤ Real.sqrt (t ^ 2 - 4 * beta) := Real.sqrt_nonneg _
  have hstep : |(t + s * Real.sqrt (t ^ 2 - 4 * beta))|
      ≤ |t| + Real.sqrt (t ^ 2 - 4 * beta) := by
    calc
      |(t + s * Real.sqrt (t ^ 2 - 4 * beta))|
        ≤ |t| + |s * Real.sqrt (t ^ 2 - 4 * beta)| := abs_add_le _ _
      _ = |t| + Real.sqrt (t ^ 2 - 4 * beta) := by
        rw [abs_mul, hsabs, one_mul, abs_of_nonneg hsqrt]
  rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  exact (div_le_div_of_nonneg_right hstep (by norm_num : (0:ℝ) ≤ 2))

/-- Двухэкспоненциальная траектория вещественных квадратных корней:
общая экспонента `((|t|+√D)/2)^n`, D=t²−4β.
Представление начальных данных задаётся отдельно: при D=0 эта
теорема НЕ покрывает Jordan-слагаемое с коэффициентом n. -/
theorem hb_real_two_root_norm_bound (e : ℕ → ℂ) (t beta : ℝ)
    (lam1 lam2 A B : ℂ)
    (hrec : ∀ n, e (n + 2) = (t : ℂ) * e (n + 1) - (beta : ℂ) * e n)
    (hroot1 : lam1 ^ 2 - (t : ℂ) * lam1 + (beta : ℂ) = 0)
    (hroot2 : lam2 ^ 2 - (t : ℂ) * lam2 + (beta : ℂ) = 0)
    (h0 : e 0 = A + B) (h1 : e 1 = A * lam1 + B * lam2)
    (hquad1 : lam1 = ((t + Real.sqrt (t ^ 2 - 4 * beta)) / 2 : ℝ))
    (hquad2 : lam2 = ((t - Real.sqrt (t ^ 2 - 4 * beta)) / 2 : ℝ))
    (n : ℕ) :
    ‖e n‖ ≤ (‖A‖ + ‖B‖) *
      ((|t| + Real.sqrt (t ^ 2 - 4 * beta)) / 2) ^ n := by
  have hnorm1 : ‖lam1‖ ≤ (|t| + Real.sqrt (t ^ 2 - 4 * beta)) / 2 := by
    rw [hquad1]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    simpa only [one_mul] using hb_real_root_pm_norm t beta 1 (Or.inl rfl)
  have hnorm2 : ‖lam2‖ ≤ (|t| + Real.sqrt (t ^ 2 - 4 * beta)) / 2 := by
    have hroot : lam2 = ((t + (-1 : ℝ) * Real.sqrt (t ^ 2 - 4 * beta)) / 2 : ℝ) := by
      rw [hquad2]
      congr 1
      ring
    rw [hroot]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact hb_real_root_pm_norm t beta (-1) (Or.inr rfl)
  exact hb_two_root_norm_cap e (t : ℂ) (beta : ℂ) lam1 lam2 A B
    ((|t| + Real.sqrt (t ^ 2 - 4 * beta)) / 2)
    hrec hroot1 hroot2 h0 h1 hnorm1 hnorm2 n

/-- Конечномерная L²-сборка по Ортонормированным Координатам.
Для каждой моды переданы свои корни и стартовое представление.
Итоговый коэффициент — L²-норма вектора модальных коэффициентов,
а не сумма абсолютных значений по всем модам. Здесь НЕ доказывается
существование спектрального разложения: оно отдельный вход задачи. -/
theorem hb_two_root_l2_bound {ι : Type*} [Fintype ι]
    (e : ℕ → EuclideanSpace ℂ ι) (t beta lam1 lam2 A B : ι → ℂ)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (hrec : ∀ n i, e (n + 2) i = t i * e (n + 1) i - beta i * e n i)
    (hroot1 : ∀ i, lam1 i ^ 2 - t i * lam1 i + beta i = 0)
    (hroot2 : ∀ i, lam2 i ^ 2 - t i * lam2 i + beta i = 0)
    (h0 : ∀ i, e 0 i = A i + B i)
    (h1 : ∀ i, e 1 i = A i * lam1 i + B i * lam2 i)
    (hnorm1 : ∀ i, ‖lam1 i‖ ≤ rho) (hnorm2 : ∀ i, ‖lam2 i‖ ≤ rho)
    (n : ℕ) :
    ‖e n‖ ≤ (Real.sqrt (∑ i, (‖A i‖ + ‖B i‖) ^ 2)) * rho ^ n := by
  have hcoord (i : ι) :
      ‖e n i‖ ≤ (‖A i‖ + ‖B i‖) * rho ^ n := by
    exact hb_two_root_norm_cap (fun k => e k i) (t i) (beta i)
      (lam1 i) (lam2 i) (A i) (B i) rho (fun k => hrec k i)
      (hroot1 i) (hroot2 i) (h0 i) (h1 i) (hnorm1 i) (hnorm2 i) n
  have hsquare (i : ι) : ‖e n i‖ ^ 2 ≤
      (‖A i‖ + ‖B i‖) ^ 2 * (rho ^ n) ^ 2 := by
    calc
      ‖e n i‖ ^ 2 ≤ ((‖A i‖ + ‖B i‖) * rho ^ n) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
      _ = (‖A i‖ + ‖B i‖) ^ 2 * (rho ^ n) ^ 2 := by ring
  have hsq : ‖e n‖ ^ 2 ≤
      (∑ i, (‖A i‖ + ‖B i‖) ^ 2) * (rho ^ n) ^ 2 := by
    calc
      ‖e n‖ ^ 2 = ∑ i, ‖e n i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
      _ ≤ ∑ i, (‖A i‖ + ‖B i‖) ^ 2 * (rho ^ n) ^ 2 := by
        exact Finset.sum_le_sum fun i _ => hsquare i
      _ = (∑ i, (‖A i‖ + ‖B i‖) ^ 2) * (rho ^ n) ^ 2 := by
        rw [Finset.sum_mul]
  calc
    ‖e n‖ = Real.sqrt (‖e n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((∑ i, (‖A i‖ + ‖B i‖) ^ 2) * (rho ^ n) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = (Real.sqrt (∑ i, (‖A i‖ + ‖B i‖) ^ 2)) * rho ^ n := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (pow_nonneg hrho _)]

/-- Перенос L²-сборки на полный конечный ортонормированный базис.
Входные уравнения уже сформулированы в выбранном базисе;
изометрия переводит оценку в исходное векторное пространство без
потери коэффициента и без ложной универсальной self-adjoint теоремы. -/
theorem hb_two_root_orthonormal_bound
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : OrthonormalBasis ι ℂ E) (e : ℕ → E)
    (t beta lam1 lam2 A B : ι → ℂ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hrec : ∀ n i, b.repr (e (n + 2)) i =
      t i * b.repr (e (n + 1)) i - beta i * b.repr (e n) i)
    (hroot1 : ∀ i, lam1 i ^ 2 - t i * lam1 i + beta i = 0)
    (hroot2 : ∀ i, lam2 i ^ 2 - t i * lam2 i + beta i = 0)
    (h0 : ∀ i, b.repr (e 0) i = A i + B i)
    (h1 : ∀ i, b.repr (e 1) i = A i * lam1 i + B i * lam2 i)
    (hnorm1 : ∀ i, ‖lam1 i‖ ≤ rho) (hnorm2 : ∀ i, ‖lam2 i‖ ≤ rho)
    (n : ℕ) :
    ‖e n‖ ≤ (Real.sqrt (∑ i, (‖A i‖ + ‖B i‖) ^ 2)) * rho ^ n := by
  rw [← b.repr.norm_map (e n)]
  exact hb_two_root_l2_bound (fun k => b.repr (e k)) t beta lam1 lam2 A B
    rho hrho hrec hroot1 hroot2 h0 h1 hnorm1 hnorm2 n

/-- Модально-зависимая L²-сборка: НЕ усредняем и НЕ заменяем
все темпы общим максимумом. Каждая мода вносит именно
`(‖A_i‖+‖B_i‖)·ρ_i^n` в квадратичную сумму. Произвольные
знаки корней и пустой набор мод не требуют гипотезы `0 ≤ ρ_i`. -/
theorem hb_two_root_l2_weighted_bound {ι : Type*} [Fintype ι]
    (e : ℕ → EuclideanSpace ℂ ι) (t beta lam1 lam2 A B : ι → ℂ)
    (rho : ι → ℝ)
    (hrec : ∀ n i, e (n + 2) i = t i * e (n + 1) i - beta i * e n i)
    (hroot1 : ∀ i, lam1 i ^ 2 - t i * lam1 i + beta i = 0)
    (hroot2 : ∀ i, lam2 i ^ 2 - t i * lam2 i + beta i = 0)
    (h0 : ∀ i, e 0 i = A i + B i)
    (h1 : ∀ i, e 1 i = A i * lam1 i + B i * lam2 i)
    (hnorm1 : ∀ i, ‖lam1 i‖ ≤ rho i) (hnorm2 : ∀ i, ‖lam2 i‖ ≤ rho i)
    (n : ℕ) :
    ‖e n‖ ≤ Real.sqrt (∑ i, ((‖A i‖ + ‖B i‖) * rho i ^ n) ^ 2) := by
  have hcoord (i : ι) :
      ‖e n i‖ ≤ (‖A i‖ + ‖B i‖) * rho i ^ n := by
    exact hb_two_root_norm_cap (fun k => e k i) (t i) (beta i)
      (lam1 i) (lam2 i) (A i) (B i) (rho i) (fun k => hrec k i)
      (hroot1 i) (hroot2 i) (h0 i) (h1 i) (hnorm1 i) (hnorm2 i) n
  have hsquare (i : ι) : ‖e n i‖ ^ 2 ≤
      ((‖A i‖ + ‖B i‖) * rho i ^ n) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
  have hsq : ‖e n‖ ^ 2 ≤ ∑ i, ((‖A i‖ + ‖B i‖) * rho i ^ n) ^ 2 := by
    calc
      ‖e n‖ ^ 2 = ∑ i, ‖e n i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
      _ ≤ ∑ i, ((‖A i‖ + ‖B i‖) * rho i ^ n) ^ 2 := by
        exact Finset.sum_le_sum fun i _ => hsquare i
  calc
    ‖e n‖ = Real.sqrt (‖e n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ i, ((‖A i‖ + ‖B i‖) * rho i ^ n) ^ 2) :=
      Real.sqrt_le_sqrt hsq

/-- Ортонормированный перенос точной модально-взвешенной L²-оценки.
Теорема не утверждает, что эта верхняя граница достигается:
равенство нормы гарантируется у базиса, а не у scalar triangle
и используемых cap-неравенств. -/
theorem hb_two_root_orthonormal_weighted_bound
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : OrthonormalBasis ι ℂ E) (e : ℕ → E)
    (t beta lam1 lam2 A B : ι → ℂ) (rho : ι → ℝ)
    (hrec : ∀ n i, b.repr (e (n + 2)) i =
      t i * b.repr (e (n + 1)) i - beta i * b.repr (e n) i)
    (hroot1 : ∀ i, lam1 i ^ 2 - t i * lam1 i + beta i = 0)
    (hroot2 : ∀ i, lam2 i ^ 2 - t i * lam2 i + beta i = 0)
    (h0 : ∀ i, b.repr (e 0) i = A i + B i)
    (h1 : ∀ i, b.repr (e 1) i = A i * lam1 i + B i * lam2 i)
    (hnorm1 : ∀ i, ‖lam1 i‖ ≤ rho i) (hnorm2 : ∀ i, ‖lam2 i‖ ≤ rho i)
    (n : ℕ) :
    ‖e n‖ ≤ Real.sqrt (∑ i, ((‖A i‖ + ‖B i‖) * rho i ^ n) ^ 2) := by
  rw [← b.repr.norm_map (e n)]
  exact hb_two_root_l2_weighted_bound (fun k => b.repr (e k))
    t beta lam1 lam2 A B rho hrec hroot1 hroot2 h0 h1 hnorm1 hnorm2 n

/-- Начальные коэффициенты через root separation: если оба
корня ограничены ρ, а `0 < gap ≤ ‖λ₁−λ₂‖`, то сумма норм
A/B ограничена начальными ошибками и обратным gap. Отдельная
посылка λ₁≠λ₂ не требуется: она следует из положительности gap. -/
theorem hb_distinct_root_coefficient_sum_bound
    (e0 e1 lam1 lam2 A B : ℂ) (rho gap : ℝ)
    (hnorm1 : ‖lam1‖ ≤ rho) (hnorm2 : ‖lam2‖ ≤ rho)
    (hgap : 0 < gap) (hsep : gap ≤ ‖lam1 - lam2‖)
    (hA : A = (e1 - lam2 * e0) / (lam1 - lam2))
    (hB : B = (lam1 * e0 - e1) / (lam1 - lam2)) :
    ‖A‖ + ‖B‖ ≤ (2 * (‖e1‖ + rho * ‖e0‖)) / gap := by
  have hrho : 0 ≤ rho := (norm_nonneg lam1).trans hnorm1
  have hdenom : 0 < ‖lam1 - lam2‖ := hgap.trans_le hsep
  have hnumA : ‖e1 - lam2 * e0‖ ≤ ‖e1‖ + rho * ‖e0‖ := by
    calc
      ‖e1 - lam2 * e0‖ ≤ ‖e1‖ + ‖lam2 * e0‖ := norm_sub_le _ _
      _ = ‖e1‖ + ‖lam2‖ * ‖e0‖ := by rw [norm_mul]
      _ ≤ ‖e1‖ + rho * ‖e0‖ := by
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hnorm2 (norm_nonneg e0))
  have hnumB : ‖lam1 * e0 - e1‖ ≤ ‖e1‖ + rho * ‖e0‖ := by
    calc
      ‖lam1 * e0 - e1‖ ≤ ‖lam1 * e0‖ + ‖e1‖ := norm_sub_le _ _
      _ = ‖lam1‖ * ‖e0‖ + ‖e1‖ := by rw [norm_mul]
      _ ≤ rho * ‖e0‖ + ‖e1‖ := by
        exact add_le_add (mul_le_mul_of_nonneg_right hnorm1 (norm_nonneg e0)) (le_refl _)
      _ = ‖e1‖ + rho * ‖e0‖ := by ring
  have hnum (x N : ℝ) (hN : 0 ≤ N) (hx : x ≤ N) :
      x / ‖lam1 - lam2‖ ≤ N / gap := by
    calc
      x / ‖lam1 - lam2‖ ≤ N / ‖lam1 - lam2‖ :=
        div_le_div_of_nonneg_right hx hdenom.le
      _ ≤ N / gap := div_le_div_of_nonneg_left hN hgap hsep
  have hN : 0 ≤ ‖e1‖ + rho * ‖e0‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg hrho (norm_nonneg _))
  rw [hA, hB, norm_div, norm_div]
  calc
    ‖e1 - lam2 * e0‖ / ‖lam1 - lam2‖ + ‖lam1 * e0 - e1‖ / ‖lam1 - lam2‖
      ≤ (‖e1‖ + rho * ‖e0‖) / gap + (‖e1‖ + rho * ‖e0‖) / gap :=
        add_le_add (hnum _ _ hN hnumA) (hnum _ _ hN hnumB)
    _ = (2 * (‖e1‖ + rho * ‖e0‖)) / gap := by ring

/-- Полная finite-mode траектория без абстрактных A/B: явные
коэффициенты восстанавливаются из e₀,e₁, после чего каждый вносит
оценку через обратный root gap. Это консервативный алгебраический
префактор, НЕ сам численный κ оптимального обучающего алгоритма. -/
theorem hb_two_root_l2_initial_gap_bound {ι : Type*} [Fintype ι]
    (e : ℕ → EuclideanSpace ℂ ι) (t beta lam1 lam2 : ι → ℂ)
    (rho gap : ι → ℝ)
    (hrec : ∀ n i, e (n + 2) i = t i * e (n + 1) i - beta i * e n i)
    (hroot1 : ∀ i, lam1 i ^ 2 - t i * lam1 i + beta i = 0)
    (hroot2 : ∀ i, lam2 i ^ 2 - t i * lam2 i + beta i = 0)
    (hnorm1 : ∀ i, ‖lam1 i‖ ≤ rho i) (hnorm2 : ∀ i, ‖lam2 i‖ ≤ rho i)
    (hgap : ∀ i, 0 < gap i) (hsep : ∀ i, gap i ≤ ‖lam1 i - lam2 i‖)
    (n : ℕ) :
    ‖e n‖ ≤ Real.sqrt (∑ i,
      ((2 * (‖e 1 i‖ + rho i * ‖e 0 i‖) / gap i) * rho i ^ n) ^ 2) := by
  let A : ι → ℂ := fun i => (e 1 i - lam2 i * e 0 i) / (lam1 i - lam2 i)
  let B : ι → ℂ := fun i => (lam1 i * e 0 i - e 1 i) / (lam1 i - lam2 i)
  have hne (i : ι) : lam1 i ≠ lam2 i := by
    have hd : 0 < ‖lam1 i - lam2 i‖ := (hgap i).trans_le (hsep i)
    intro heq
    rw [heq, sub_self, norm_zero] at hd
    exact (lt_irrefl 0) hd
  have h0 (i : ι) : e 0 i = A i + B i := by
    simpa only [A, B] using (hb_distinct_root_init (e 0 i) (e 1 i)
      (lam1 i) (lam2 i) (hne i)).1
  have h1 (i : ι) : e 1 i = A i * lam1 i + B i * lam2 i := by
    simpa only [A, B] using (hb_distinct_root_init (e 0 i) (e 1 i)
      (lam1 i) (lam2 i) (hne i)).2
  have hbound : ‖e n‖ ≤ Real.sqrt (∑ i, ((‖A i‖ + ‖B i‖) * rho i ^ n) ^ 2) :=
    hb_two_root_l2_weighted_bound e t beta lam1 lam2 A B rho
      hrec hroot1 hroot2 h0 h1 hnorm1 hnorm2 n
  have hcoef (i : ι) : ‖A i‖ + ‖B i‖ ≤
      (2 * (‖e 1 i‖ + rho i * ‖e 0 i‖) / gap i) := by
    exact hb_distinct_root_coefficient_sum_bound
      (e 0 i) (e 1 i) (lam1 i) (lam2 i) (A i) (B i)
      (rho i) (gap i) (hnorm1 i) (hnorm2 i) (hgap i) (hsep i) rfl rfl
  have hstep (i : ι) : ((‖A i‖ + ‖B i‖) * rho i ^ n) ^ 2 ≤
      ((2 * (‖e 1 i‖ + rho i * ‖e 0 i‖) / gap i) * rho i ^ n) ^ 2 := by
    have hrho : 0 ≤ rho i := (norm_nonneg (lam1 i)).trans (hnorm1 i)
    have hp : 0 ≤ rho i ^ n := pow_nonneg hrho n
    have hmul : (‖A i‖ + ‖B i‖) * rho i ^ n ≤
        (2 * (‖e 1 i‖ + rho i * ‖e 0 i‖) / gap i) * rho i ^ n :=
      mul_le_mul_of_nonneg_right (hcoef i) hp
    exact pow_le_pow_left₀
      (mul_nonneg (add_nonneg (norm_nonneg (A i)) (norm_nonneg (B i))) hp) hmul 2
  have hsum : (∑ i, ((‖A i‖ + ‖B i‖) * rho i ^ n) ^ 2) ≤
      ∑ i, ((2 * (‖e 1 i‖ + rho i * ‖e 0 i‖) / gap i) * rho i ^ n) ^ 2 :=
    Finset.sum_le_sum fun i _ => hstep i
  exact hbound.trans (Real.sqrt_le_sqrt hsum)

end Hagi.Optimization.HBRate
