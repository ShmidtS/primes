/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Unified.RecursiveClean
set_option linter.style.header false

/-!
# Gauge-квотиент и наследование темпа осцилляций (R537)

Формализация ядра QRR (Park & Rusch, «Looped Reasoning
Finishes Earlier Than You Think», arXiv:2610.18174):
рекуррентный reasoning с динамической глубиной.

Ядро статьи:
(1) медленно затухающая осцилляторная мода транслирует
    свой темп сходимости на связанные латентные динамики
    (rate inheritance, Theorem 3.2 статьи);
(2) прямое гашение осцилляций ломает computation — вместо
    этого точная token-local U(1) gauge-симметрия: движение
    по gauge-орбите не меняет quotient-состояние
    (relative equilibrium), halting — по quotient-остатку
    r_G (Eq. 19 статьи).

Формализовано:

* `rot` — фазовое вращение U(1) (gauge-действие);
* `GaugeSystem` — рекуррентный оператор с эквивариантностью
  T(g_φ z) = g_φ (T z);
* `norm_rot_invariance`, `norm_rot_sub` — перенормировка
  фаз;
* `quotientResidual` — r_G(z) = inf_φ ‖T z − e^{iφ} z‖;
* `quotientResidual_gauge_invariant` — r_G(g·z) = r_G(z):
  gauge-движение невидимо для quotient-теста сходимости;
* `relativeEquilibrium_residual_zero` — relative equilibrium
  (T z = g·z) ⟹ r_G = 0: quotient-состояние сошлось, пока
  raw-траектория движется по орбите ⟹ ранний halting;
* ядро rate inheritance (скалярная аффинная модель моды
  у корня): `seq`, `seq_dev_exact` — точное решение
  x_t − x* = s^t·(x₀ − x*), `seq_dev_modulus` — модульная
  форма |x_t − x*| = |s|^t·|x₀ − x*|.
-/

namespace Hagi.Unified.GaugeQuotient

open Complex

/-- Фазовое вращение U(1): g_φ · z = e^{iφ} z. -/
noncomputable def rot (φ : ℝ) (z : ℂ) : ℂ := z * exp (φ * I)

/-- Фазовые вращения сохраняют норму. -/
theorem norm_rot (φ : ℝ) (z : ℂ) : ‖rot φ z‖ = ‖z‖ := by
  unfold rot
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]

/-- Перенормировка разности фаз: факторизация вращения. -/
theorem norm_rot_sub (φ₀ φ' : ℝ) (a b : ℂ) :
    ‖rot φ₀ a - rot φ' b‖ = ‖a - rot (φ' - φ₀) b‖ := by
  unfold rot
  have hc : exp (φ' * I) = exp (φ₀ * I) * exp ((φ' - φ₀) * I) := by
    rw [← exp_add]; congr 1; ring
  have hp : (a * exp (φ₀ * I) - b * exp (φ' * I))
      = (a - b * exp ((φ' - φ₀) * I)) * exp (φ₀ * I) := by
    rw [hc]; ring_nf
  rw [hp, norm_mul, norm_exp_ofReal_mul_I, mul_one]
  congr 1
  congr 1
  push_cast
  ring

/-- Рекуррентная система с gauge-симметрией. -/
structure GaugeSystem where
  /-- рекуррентный оператор -/
  T : ℂ → ℂ
  /-- эквивариантность: T(g_φ z) = g_φ (T z) -/
  hequiv : ∀ (φ₀ : ℝ) (z : ℂ), T (rot φ₀ z) = rot φ₀ (T z)

/-- Quotient-остаток (Eq. 19 статьи):
r_G(z) = inf_φ ‖T z − e^{iφ} z‖. -/
noncomputable def quotientResidual (sys : GaugeSystem) (z : ℂ) : ℝ :=
  sInf (Set.range fun φ => dist (sys.T z) (rot φ z))

/-- Остаток неотрицателен. -/
theorem residual_nonneg (sys : GaugeSystem) (z : ℂ) :
    0 ≤ quotientResidual sys z :=
  Real.sInf_nonneg (by
    rintro _ ⟨φ, rfl⟩
    exact dist_nonneg)

/-- **Gauge-инвариантность остатка (R537, ядро QRR)**:
r_G(g_φ₀·z) = r_G(z) — движение по gauge-орбите невидимо
для quotient-теста. Механика: эквивариантность перебрасывает
вращение на T z, и остаток множества фаз совпадает
(фазовые сдвиги сокращаются: rot φ (rot φ₀ z) ~ rot (φ+φ₀) z). -/
theorem quotientResidual_gauge_invariant (sys : GaugeSystem)
    (φ₀ : ℝ) (z : ℂ) :
    quotientResidual sys (rot φ₀ z) = quotientResidual sys z := by
  have hpoint : ∀ φ : ℝ,
      dist (sys.T (rot φ₀ z)) (rot φ (rot φ₀ z))
        = dist (sys.T z) (rot φ z) := by
    intro φ
    rw [sys.hequiv φ₀ z, dist_eq_norm, dist_eq_norm]
    have hsplit : rot φ (rot φ₀ z) = rot (φ + φ₀) z := by
      unfold rot
      have h1 : exp (φ₀ * I) * exp (φ * I)
          = exp ((φ + φ₀) * I) := by
        rw [← exp_add]; congr 1; ring
      show z * exp (↑φ₀ * I) * exp (↑φ * I)
          = z * exp (↑(φ + φ₀) * I)
      have h1 : exp (φ₀ * I) * exp (φ * I)
          = exp ((φ + φ₀) * I) := by
        rw [← exp_add]; congr 1; ring
      rw [mul_assoc, h1]
      push_cast
      ring
    rw [hsplit]
    have h2 := norm_rot_sub φ₀ (φ + φ₀) (sys.T z) z
    have hsimp : φ + φ₀ - φ₀ = φ := by ring
    rw [hsimp] at h2
    exact h2
  unfold quotientResidual
  have hrange : (Set.range fun φ => dist (sys.T (rot φ₀ z)) (rot φ (rot φ₀ z)))
      = (Set.range fun φ => dist (sys.T z) (rot φ z)) := by
    refine Set.ext (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · obtain ⟨φ, rfl⟩ := hx
      exact ⟨φ, (hpoint φ).symm⟩
    · obtain ⟨φ, rfl⟩ := hx
      exact ⟨φ, hpoint φ⟩
  exact congrArg sInf hrange

/-- **Relative equilibrium ⟹ ранний halting (R537)**:
если T z отличается от z лишь на фазу (T z = e^{iφ₀} z), то
quotient-остаток нулевой: quotient-состояние сошлось, пока
raw-траектория движется по орбите. Обоснование
quotient-halting статьи: раннее завершение без ложного
ожидания raw-стационарности. -/
theorem relativeEquilibrium_residual_zero (sys : GaugeSystem)
    (z : ℂ) (φ₀ : ℝ) (hrel : sys.T z = rot φ₀ z) :
    quotientResidual sys z = 0 := by
  have hmem : (0:ℝ) ∈ Set.range fun φ => dist (sys.T z) (rot φ z) := by
    refine ⟨φ₀, ?_⟩
    show dist (sys.T z) (rot φ₀ z) = 0
    rw [hrel, dist_self]
  have hmem : (0:ℝ) ∈ Set.range fun φ => dist (sys.T z) (rot φ z) := by
    refine ⟨φ₀, ?_⟩
    show dist (sys.T z) (rot φ₀ z) = 0
    rw [hrel, dist_self]
  have hb : ∀ d ∈ Set.range fun φ => dist (sys.T z) (rot φ z), 0 ≤ d := by
    rintro d ⟨φ, rfl⟩
    exact dist_nonneg
  have hbdd : BddBelow (Set.range fun φ => dist (sys.T z) (rot φ z)) :=
    ⟨0, hb⟩
  have h1 : sInf (Set.range fun φ => dist (sys.T z) (rot φ z)) ≤ 0 :=
    csInf_le hbdd hmem
  have h2 : 0 ≤ sInf (Set.range fun φ => dist (sys.T z) (rot φ z)) :=
    Real.sInf_nonneg hb
  exact le_antisymm h1 h2

/-- Скалярная аффинная рекурсия — локальная модель моды у
корня: x_{t+1} = s·x_t + c, s — собственное значение моды
(для alternating-моды s = −r < 0). -/
noncomputable def seq (s c x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | (t + 1) => s * seq s c x₀ t + c

/-- **Точная динамика отклонения (R537)**: при s ≠ 1
отклонение от корня x* = c/(1−s) умножается на s^t:
x_t − x* = s^t·(x₀ − x*). Ядро rate inheritance: мода
переносит свой темп |s| на сходимость оболочки. -/
theorem seq_dev_exact {s c x₀ : ℝ} (hs : s ≠ 1) (t : ℕ) :
    seq s c x₀ t - c / (1 - s) = s ^ t * (x₀ - c / (1 - s)) := by
  induction t with
  | zero => simp [seq]
  | succ t ih =>
      have hshift : seq s c x₀ (t + 1) - c / (1 - s)
          = s * (seq s c x₀ t - c / (1 - s)) := by
        rw [seq]
        field_simp
        ring
      rw [hshift, ih, pow_succ]
      ring

/-- **Модульная форма затухания (R537)**: |x_t − x*| =
|s|^t·|x₀ − x*| — амплитуда моды контролируется точно:
alternating-мода (s = −r) с r ≥ 1 никогда не затухает;
при r < 1 затухание геометрическое с темпом r. -/
theorem seq_dev_modulus {s c x₀ : ℝ} (hs : s ≠ 1) (t : ℕ) :
    |seq s c x₀ t - c / (1 - s)|
      = |s| ^ t * |x₀ - c / (1 - s)| := by
  rw [seq_dev_exact hs t, abs_mul, abs_pow]

end Hagi.Unified.GaugeQuotient
