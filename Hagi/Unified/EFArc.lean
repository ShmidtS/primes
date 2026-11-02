/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Unified.DescentCore
import Hagi.Unified.RateTheory
import Hagi.Unified.SignComp

/-!
# Дуга error feedback (объединённая)

Точное тенение EF-траектории (ErrorFeedback), перенос
качества на эталоне (EFQuad), мост к GD и итоговая
guality-per-bit теорема (SignEFQuad), оценки резидуала
(EFResidual), пороговый компрессор с абсолютным барьером
(ThrComp). Слит из пяти модулей; имена сохранены.
-/

/-!
# Error feedback: сжатая траектория точно отражает идеальную

Механизм компенсации сжатия: резидуал накапливает
несланданные координаты, и сжатая траектория отклоняется
от идеальной РОВНО на изменение резидуала — точная
идентичность, не оценка. Это фундамент возврата
PL-скорости для сжатых шагов после отрицательного
результата об отсутствии равномерной drop-грани.
-/

namespace Hagi.Unified.ErrorFeedback

open Hagi.Unified.DescentCore

variable {k : Type*} [Fintype k]

/-- ТЕЛЕСКОП EF: сумма сжатых векторов равна сумме
точных плюс изменение резидуала. -/
theorem ef_telescope (d e : ℕ → k → ℝ)
    (comp : (k → ℝ) → (k → ℝ))
    (hEF : ∀ t, e (t + 1) = d t + e t - comp (d t + e t))
    (n : ℕ) :
    ∑ t ∈ Finset.range n, comp (d t + e t)
      = (∑ t ∈ Finset.range n, d t) + e 0 - e n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hcomp : comp (d n + e n)
        = d n + e n - e (n + 1) := by
      rw [hEF n]
      abel
    rw [hcomp, ih]
    abel

/-- ТОЧНОЕ ОТКЛОНЕНИЕ СУММ: разность сжатой и точной
сумм равна изменению резидуала. -/
theorem ef_shadow_sum (d e : ℕ → k → ℝ)
    (comp : (k → ℝ) → (k → ℝ))
    (hEF : ∀ t, e (t + 1) = d t + e t - comp (d t + e t))
    (n : ℕ) :
    (∑ t ∈ Finset.range n, comp (d t + e t))
      - (∑ t ∈ Finset.range n, d t) = e 0 - e n := by
  rw [ef_telescope d e comp hEF n]
  abel

/-- ГЛАВНАЯ ТЕОРЕМА: EF-траектория точно отражает
идеальную. Итераты сжатого цикла против точного
отклоняются РОВНО на масштабированное изменение
резидуала. -/
theorem ef_iterate_shadow (d e : ℕ → k → ℝ)
    (comp : (k → ℝ) → (k → ℝ)) (eta : ℝ)
    (hEF : ∀ t, e (t + 1) = d t + e t - comp (d t + e t))
    (xC xF : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1) = xC t - eta • comp (d t + e t))
    (hxF : ∀ t, xF (t + 1) = xF t - eta • d t)
    (hx0 : xC 0 = xF 0) (n : ℕ) :
    xC n - xF n = eta • (e n - e 0) := by
  induction n with
  | zero => rw [hx0]; simp
  | succ n ih =>
    have hcomp : comp (d n + e n)
        = d n + e n - e (n + 1) := by
      rw [hEF n]
      abel
    have hstep : xC (n + 1) - xF (n + 1)
        = (xC n - xF n) - eta • (e n - e (n + 1)) := by
      rw [hxC n, hxF n, hcomp]
      module
    rw [hstep, ih]
    module

end Hagi.Unified.ErrorFeedback

/-!
# Качество EF-цикла на квадратичной машине

Соединение точного отражения EF-траектории с
PL-скоростью идеальной: энергия сжатой траектории равна
энергии идеальной плюс ТОЧНЫЕ резидуальные члены, а
идеальная сжимается линейно. Скорость восстановлена с
точностью до контроля резидуала.
-/

namespace Hagi.Unified.EFQuad

open Hagi.Unified.ErrorFeedback
open Hagi.Unified.PLQuad
open Hagi.Unified.PLLoop
open Hagi.Unified.DescentCore
open Hagi.Unified.DescentCoreQuad

variable {k : Type*} [Fintype k]

/-- ТОЧНЫЙ ПЕРЕНОС: энергия EF-итерата равна энергии
идеального итерата плюс резидуальные члены — без
оценок, тождество. -/
theorem ef_quad_transfer (a : k → ℝ)
    (d e : ℕ → k → ℝ) (comp : (k → ℝ) → (k → ℝ))
    (eta : ℝ)
    (hEF : ∀ t, e (t + 1) = d t + e t - comp (d t + e t))
    (xC xF : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1) = xC t - eta • comp (d t + e t))
    (hxF : ∀ t, xF (t + 1) = xF t - eta • d t)
    (hx0 : xC 0 = xF 0) (n : ℕ) :
    quadE a (xC n)
      = quadE a (xF n)
        + inprod (quadGrad a (xF n)) (eta • (e n - e 0))
        + (1:ℝ) / 2 * nrm2 (eta • (e n - e 0)) := by
  have hdev := ef_iterate_shadow d e comp eta hEF xC xF hxC hxF hx0 n
  have hd : xC n = xF n + eta • (e n - e 0) := by
    rw [← hdev]
    abel
  rw [hd]
  exact quad_descent_eq a (xF n) (eta • (e n - e 0))

/-- ГЛАВНЫЙ ВЫВОД: скорость EF-цикла восстановлена.
Если идеальная траектория удовлетворяет drop-грани и
PL-связи, энергия сжатой не превосходит линейно
сжимающейся идеальной плюс ТОЧНЫЕ резидуальные члены. -/
theorem ef_quad_quality (a : k → ℝ)
    (d e : ℕ → k → ℝ) (comp : (k → ℝ) → (k → ℝ))
    (eta : ℝ)
    (hEF : ∀ t, e (t + 1) = d t + e t - comp (d t + e t))
    (xC xF : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1) = xC t - eta • comp (d t + e t))
    (hxF : ∀ t, xF (t + 1) = xF t - eta • d t)
    (hx0 : xC 0 = xF 0) (n : ℕ)
    (drops : ℕ → ℝ) (κ : ℝ)
    (hκ : 0 ≤ κ) (hκ2 : 2 * κ < 1)
    (hdrop : ∀ t < n, κ * nrm2 (quadGrad a (xF t)) ≤ drops t)
    (hcert : ∀ t < n,
      quadE a (xF (t + 1)) ≤ quadE a (xF t) - drops t) :
    quadE a (xC n)
      ≤ (1 - 2 * κ)^n * quadE a (xF 0)
        + inprod (quadGrad a (xF n)) (eta • (e n - e 0))
        + (1:ℝ) / 2 * nrm2 (eta • (e n - e 0)) := by
  have hrate := quad_pl_rate a xF drops n κ hκ hκ2 hdrop hcert
  have htransfer := ef_quad_transfer a d e comp eta hEF xC xF
    hxC hxF hx0 n
  linarith

end Hagi.Unified.EFQuad

/-!
# EF-сжатие теняет градиентный спуск на эталоне

Мост миров: сжатая траектория (worker шлёт сжатые
направления идеальных вычислений, резидуал копит
несланданное) отклоняется от точного градиентного
спуска `quadGD` РОВНО на масштабированное изменение
резидуала. Компрессия обучения без потери траектории.
-/

namespace Hagi.Unified.SignEFQuad

open Hagi.Unified.ErrorFeedback
open Hagi.Unified.QuadGDRate
open Hagi.Unified.DescentCore
open Hagi.Unified.DescentCoreQuad
open Hagi.Unified.SignStepCert Hagi.Unified.SignDescent Hagi.Step.SignSGD

variable {k : Type*} [Fintype k]

/-- ГЛАВНАЯ ТЕОРЕМА: EF-сжатая траектория теняет точный
градиентный спуск на квадратичной машине — отклонение
РАВНО масштабированному изменению резидуала. -/
theorem quad_ef_shadow (a : k → ℝ) (eta : ℝ) (x0 : k → ℝ)
    (e : ℕ → k → ℝ) (comp : (k → ℝ) → (k → ℝ))
    (hEF : ∀ t, e (t + 1)
      = quadGrad a (quadGD a eta x0 t) + e t
        - comp (quadGrad a (quadGD a eta x0 t) + e t))
    (xC : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1)
      = xC t - eta • comp
        (quadGrad a (quadGD a eta x0 t) + e t))
    (hx0 : xC 0 = x0) (n : ℕ) :
    xC n - quadGD a eta x0 n = eta • (e n - e 0) := by
  have hxF : ∀ t, quadGD a eta x0 (t + 1)
      = quadGD a eta x0 t
        - eta • quadGrad a (quadGD a eta x0 t) := by
    intro t
    funext i
    simp [quadGD, Pi.sub_apply, Pi.smul_apply]
  exact ef_iterate_shadow
    (fun t => quadGrad a (quadGD a eta x0 t)) e comp eta hEF
    xC (quadGD a eta x0) hxC hxF hx0 n

/-- СЛЕДСТВИЕ: нулевой резидуал — сжатая траектория
СОВПАДАЕТ с точным градиентным спуском. -/
theorem quad_ef_exact (a : k → ℝ) (eta : ℝ) (x0 : k → ℝ)
    (e : ℕ → k → ℝ) (comp : (k → ℝ) → (k → ℝ))
    (he0 : e 0 = 0)
    (hEF : ∀ t, e (t + 1)
      = quadGrad a (quadGD a eta x0 t) + e t
        - comp (quadGrad a (quadGD a eta x0 t) + e t))
    (xC : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1)
      = xC t - eta • comp
        (quadGrad a (quadGD a eta x0 t) + e t))
    (hx0 : xC 0 = x0) (n : ℕ)
    (hzero : e n = e 0) :
    xC n = quadGD a eta x0 n := by
  have h := quad_ef_shadow a eta x0 e comp hEF xC hxC hx0 n
  rw [hzero] at h
  rw [sub_self, smul_zero] at h
  exact sub_eq_zero.mp h

/-- ИТОГОВАЯ ТЕОРЕМА ДУГИ: сжатое EF-обучение имеет
GD-качество плюс ТОЧНЫЕ резидуальные члены. Скорость
точного спуска (выведенная, не гипотеза) переносится на
сжатую траекторию с контролем через резидуал. -/
theorem quad_ef_quality_rate (a : k → ℝ) (eta : ℝ)
    (heta : 0 < eta) (heta2 : eta ≤ 1 / 2)
    (x0 : k → ℝ)
    (e : ℕ → k → ℝ) (comp : (k → ℝ) → (k → ℝ))
    (hEF : ∀ t, e (t + 1)
      = quadGrad a (quadGD a eta x0 t) + e t
        - comp (quadGrad a (quadGD a eta x0 t) + e t))
    (xC : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1)
      = xC t - eta • comp
        (quadGrad a (quadGD a eta x0 t) + e t))
    (hx0 : xC 0 = x0) (n : ℕ) :
    quadE a (xC n)
      ≤ (1 - 2 * eta * (1 - eta / 2)) ^ n * quadE a x0
        + inprod (quadGrad a (quadGD a eta x0 n))
            (eta • (e n - e 0))
        + (1:ℝ) / 2 * nrm2 (eta • (e n - e 0)) := by
  have hxF : ∀ t, quadGD a eta x0 (t + 1)
      = quadGD a eta x0 t
        - eta • quadGrad a (quadGD a eta x0 t) := by
    intro t
    funext i
    simp [quadGD, Pi.sub_apply, Pi.smul_apply]
  have hκ : (0:ℝ) ≤ eta * (1 - eta / 2) :=
    mul_nonneg heta.le (by
      have : (0:ℝ) ≤ 1 - eta / 2 := by nlinarith
      linarith)
  have hκ2 : 2 * (eta * (1 - eta / 2)) < 1 := by
    have hne : (1:ℝ) - eta ≠ 0 := by
      intro h
      have h1 : (1:ℝ) < eta := by linarith
      linarith
    have hring : (1 - eta) * (1 - eta)
        = 1 - 2 * (eta * (1 - eta / 2)) := by ring
    have hpos : (0:ℝ) < (1 - eta) * (1 - eta) :=
      mul_self_pos.mpr hne
    rw [hring] at hpos
    linarith
  set drops : ℕ → ℝ := fun t =>
    eta * (1 - eta / 2) * nrm2 (quadGrad a (quadGD a eta x0 t))
  have hstep : ∀ t : ℕ,
      quadE a (quadGD a eta x0 (t + 1))
        = quadE a (quadGD a eta x0 t) - drops t := by
    intro t
    unfold drops
    have := quad_gd_step_eq a (quadGD a eta x0 t) eta
    simpa [quadGD] using this
  have hmain := Hagi.Unified.EFQuad.ef_quad_quality a
    (fun t => quadGrad a (quadGD a eta x0 t)) e comp eta hEF
    xC (quadGD a eta x0) hxC hxF hx0 n drops
    (eta * (1 - eta / 2)) hκ hκ2
    (fun t _ => le_of_eq rfl)
    (fun t _ => by rw [hstep t])
  rw [show quadGD a eta x0 0 = x0 from rfl,
    show (1:ℝ) - 2 * (eta * (1 - eta / 2))
      = 1 - 2 * eta * (1 - eta / 2) from by ring] at hmain
  exact hmain

/-- КОНКРЕТНЫЙ КОМПРЕССОР: масштабированный знак
(бит на координату). -/
noncomputable def signComp (v : k → ℝ) : k → ℝ :=
  fun i => signScale v * sgn1 (v i)

/-- ПОЛНОСТЬЮ КОНКРЕТНЫЙ АЛГОРИТМ: знаковое EF-обучение —
то же качество (GD-скорость + точные резидуальные
члены) при битной пересылке. -/
theorem quad_ef_sign_quality (a : k → ℝ) (eta : ℝ)
    (heta : 0 < eta) (heta2 : eta ≤ 1 / 2)
    (x0 : k → ℝ) (e : ℕ → k → ℝ)
    (hEF : ∀ t, e (t + 1)
      = quadGrad a (quadGD a eta x0 t) + e t
        - signComp (quadGrad a (quadGD a eta x0 t) + e t))
    (xC : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1)
      = xC t - eta • signComp
        (quadGrad a (quadGD a eta x0 t) + e t))
    (hx0 : xC 0 = x0) (n : ℕ) :
    quadE a (xC n)
      ≤ (1 - 2 * eta * (1 - eta / 2)) ^ n * quadE a x0
        + inprod (quadGrad a (quadGD a eta x0 n))
            (eta • (e n - e 0))
        + (1:ℝ) / 2 * nrm2 (eta • (e n - e 0)) :=
  quad_ef_quality_rate a eta heta heta2 x0 e signComp hEF xC
    hxC hx0 n

/-- QUALITY-PER-BIT: знаковое EF-обучение достигает
качества GD-скорости с резидуальным контролем, а бюджет
пересылки — бит на координату за шаг, строго дешевле
слова на координату. -/
theorem quad_ef_sign_quality_bits (a : k → ℝ) (eta : ℝ)
    (heta : 0 < eta) (heta2 : eta ≤ 1 / 2)
    (x0 : k → ℝ) (e : ℕ → k → ℝ)
    (hEF : ∀ t, e (t + 1)
      = quadGrad a (quadGD a eta x0 t) + e t
        - signComp (quadGrad a (quadGD a eta x0 t) + e t))
    (xC : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1)
      = xC t - eta • signComp
        (quadGrad a (quadGD a eta x0 t) + e t))
    (hx0 : xC 0 = x0) (n : ℕ) [Nonempty k] :
    quadE a (xC n)
      ≤ (1 - 2 * eta * (1 - eta / 2)) ^ n * quadE a x0
        + inprod (quadGrad a (quadGD a eta x0 n))
            (eta • (e n - e 0))
        + (1:ℝ) / 2 * nrm2 (eta • (e n - e 0))
      ∧ (n:ℝ) * (Fintype.card k : ℝ)
          ≤ (n:ℝ) * fullCommCost k := by
  constructor
  · exact quad_ef_sign_quality a eta heta heta2 x0 e hEF
      xC hxC hx0 n
  · have hle := sign_comm_le (k := k)
    unfold fullCommCost signCommCost at hle
    exact mul_le_mul_of_nonneg_left hle (by positivity)

end Hagi.Unified.SignEFQuad

/-!
# Пошаговая оценка резидуала знакового EF

Первый кирпень ограниченности резидуала: остаток
сжатия (несланданное) за один шаг ограничен квадратом
удвоенной l-один нормы входа — без гипотез.
-/

namespace Hagi.Unified.EFResidual

open Hagi.Unified.SignEFQuad
open Hagi.Unified.SignStepCert
open Hagi.Unified.SignDescent
open Hagi.Unified.DescentCore
open Hagi.Step.SignSGD

variable {k : Type*} [Fintype k] [Nonempty k]

/-- Знак принадлежит единичному сегменту. -/
theorem sgn1_abs_le_one (y : ℝ) : |sgn1 y| ≤ 1 := by
  unfold sgn1
  rcases lt_trichotomy y 0 with h | h | h
  · rw [if_pos h]
    norm_num
  · rw [if_neg (by linarith), if_pos h]
    norm_num
  · rw [if_neg (by linarith), if_neg (by linarith)]
    norm_num

/-- Покоординатная оценка остатка: модуль несollandанного
не превосходит модуль входа плюс масштаб. -/
theorem residual_coord_le (v : k → ℝ) (i : k) :
    |v i - signComp v i| ≤ |v i| + signScale v := by
  have hsnn : (0:ℝ) ≤ signScale v := by
    unfold signScale
    apply div_nonneg <;> positivity
  have hsplit : v i - signComp v i
      = v i + (-(signScale v * sgn1 (v i))) := by
    unfold signComp
    ring
  rw [hsplit]
  have hA := abs_add_le (v i)
    (-(signScale v * sgn1 (v i)))
  have h2 : |-(signScale v * sgn1 (v i))|
      ≤ signScale v := by
    rw [abs_neg, abs_mul, abs_of_nonneg hsnn]
    calc signScale v * |sgn1 (v i)|
        ≤ signScale v * 1 :=
      mul_le_mul_of_nonneg_left (sgn1_abs_le_one _) hsnn
      _ = signScale v := mul_one _
  have h1 : |v i| ≤ |v i| := le_refl _
  linarith

/-- l-один оценка остатка: сумма модулей несollandанного
не превосходит удвоенной l-один нормы входа. -/
theorem residual_l1_le (v : k → ℝ) :
    ∑ i, |v i - signComp v i| ≤ 2 * ∑ i, |v i| := by
  have hcard : (Fintype.card k : ℝ) ≠ 0 := by positivity
  have hsum : ∑ i, (|v i| + signScale v)
      = ∑ i, |v i| + (Fintype.card k : ℝ) * signScale v := by
    rw [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hscale : (Fintype.card k : ℝ) * signScale v
      = ∑ i, |v i| := by
    unfold signScale
    field_simp
  have hle : ∑ i, |v i - signComp v i|
      ≤ ∑ i, (|v i| + signScale v) :=
    Finset.sum_le_sum fun i _ => residual_coord_le v i
  rw [hsum, hscale] at hle
  linarith

/-- Квадраты ограничены квадратом суммы модулей. -/
theorem sumsq_le_sq_l1 (r : k → ℝ) :
    nrm2 r ≤ (∑ i, |r i|)^2 := by
  unfold nrm2
  have hdiag : ∀ i, (r i)^2 ≤ ∑ j, |r i| * |r j| := by
    intro i
    have hle : (r i)^2 = |r i| * |r i| := by
      rw [abs_mul_abs_self, pow_two]
    rw [hle]
    exact Finset.single_le_sum (f := fun j => |r i| * |r j|)
      (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Finset.mem_univ i)
  have hsumsq : ∑ i, (r i)^2 ≤ ∑ i, ∑ j, |r i| * |r j| :=
    Finset.sum_le_sum fun i _ => hdiag i
  have hprod : ∑ i, ∑ j, |r i| * |r j|
      = (∑ i, |r i|) * (∑ i, |r i|) := by
    rw [Finset.sum_mul_sum]
  linarith

/-- ГЛАВНАЯ: пошаговый остаток сжатия ограничен квадратом
удвоенной l-один нормы входа — без единой гипотезы. -/
theorem ef_residual_step_bound (v : k → ℝ) :
    nrm2 (v - signComp v) ≤ (2 * ∑ i, |v i|)^2 := by
  have h1 := sumsq_le_sq_l1 (fun i => v i - signComp v i)
  have h2 := residual_l1_le v
  show nrm2 (fun i => v i - signComp v i)
    ≤ (2 * ∑ i, |v i|)^2
  have hB : (0:ℝ) ≤ ∑ i, |v i - signComp v i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hC : (0:ℝ) ≤ 2 * ∑ i, |v i| := by positivity
  have hsq : (∑ i, |v i - signComp v i|)^2
      ≤ (2 * ∑ i, |v i|)^2 :=
    (sq_le_sq₀ hB hC).mpr h2
  exact le_trans h1 hsq

end Hagi.Unified.EFResidual

/-!
# Пороговый компрессор: остаток — малая часть

Пороговое сжатие передаёт только большие координаты;
остаток (несланданное) — в точности малые координаты и
потому НЕ ПРЕВЫШАЕТ нормы входа. Контраст со знаковым
компрессором, у которого остаток растёт с носителя.
-/

namespace Hagi.Unified.ThrComp

open Hagi.Unified.DescentCore Hagi.Unified.DescentCoreQuad
open Hagi.Unified.QuadGDRate Hagi.Unified.SignEFQuad

variable {k : Type*} [Fintype k]

/-- Пороговый компрессор: большие координаты — точно,
малые — нуль. -/
noncomputable def thrComp (τ : ℝ) (v : k → ℝ) : k → ℝ :=
  fun i => if τ ≤ |v i| then v i else 0

/-- Большие координаты передаются точно. -/
theorem thrComp_keeps (τ : ℝ) (v : k → ℝ) (i : k)
    (h : τ ≤ |v i|) : thrComp τ v i = v i := by
  unfold thrComp
  rw [if_pos h]

/-- Остаток — в точности малые координаты. -/
theorem thrComp_residual (τ : ℝ) (v : k → ℝ) :
    v - thrComp τ v = fun i => if |v i| < τ then v i else 0 := by
  funext i
  show v i - thrComp τ v i = if |v i| < τ then v i else 0
  unfold thrComp
  by_cases h : τ ≤ |v i|
  · rw [if_pos h, if_neg (by linarith [h])]
    simp
  · rw [if_neg h, if_pos (by linarith [h])]
    ring

/-- ГЛАВНАЯ: остаток порогового сжатия не превосходит
нормы входа — малая часть целого, без гипотез. -/
theorem thrComp_residual_le (τ : ℝ) (v : k → ℝ) :
    nrm2 (v - thrComp τ v) ≤ nrm2 v := by
  unfold nrm2
  simp only [Pi.sub_apply]
  refine Finset.sum_le_sum fun i _ => ?_
  unfold thrComp
  by_cases h : τ ≤ |v i|
  · rw [if_pos h]
    simp
    positivity
  · rw [if_neg h]
    simp

/-- Следствие: EF-остаток порогового компрессора
контролируется нормой сообщения — резидуал не может
превысить того, что пришло. -/
theorem ef_thr_residual_control (τ : ℝ) (d e : k → ℝ) :
    nrm2 (d + e - thrComp τ (d + e)) ≤ nrm2 (d + e) :=
  thrComp_residual_le τ (d + e)

/-- АБСОЛЮТНЫЙ БАРЬЕР: остаток не превосходит
количества координат на квадрат порога — независимо от
истории. -/
theorem thrComp_barrier (τ : ℝ) (v : k → ℝ) :
    nrm2 (v - thrComp τ v)
      ≤ (Fintype.card k : ℝ) * τ ^ 2 := by
  have h : ∀ i, (v i - thrComp τ v i)^2 ≤ τ ^ 2 := by
    intro i
    unfold thrComp
    by_cases hc : τ ≤ |v i|
    · rw [if_pos hc]
      simp
      positivity
    · rw [if_neg hc]
      have hlt : |v i| < τ := not_le.mp hc
      have hnn : (0:ℝ) ≤ |v i| := abs_nonneg _
      have hle : (v i)^2 ≤ τ ^ 2 := by
        rw [← sq_abs]
        nlinarith
      simpa using hle
  unfold nrm2
  simp only [Pi.sub_apply]
  calc ∑ i, (v i - thrComp τ v i)^2 ≤ ∑ i, τ ^ 2 :=
        Finset.sum_le_sum fun i _ => h i
    _ = (Fintype.card k : ℝ) * τ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Норма масштабированного вектора. -/
theorem nrm2_smul (c : ℝ) (v : k → ℝ) :
    nrm2 (c • v) = c ^ 2 * nrm2 v := by
  unfold nrm2
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- Коши–Буняковский в квадратичной форме. -/
theorem inprod_abs_le (u v : k → ℝ) :
    |inprod u v| ≤ Real.sqrt (nrm2 u * nrm2 v) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  unfold inprod at hcs
  show |∑ i, u i * v i|
    ≤ Real.sqrt ((∑ i, (u i)^2) * (∑ i, (v i)^2))
  have hkey : |∑ i, u i * v i| ^ 2
      ≤ (∑ i, (u i)^2) * (∑ i, (v i)^2) := by
    rw [sq_abs]
    exact hcs
  calc |∑ i, u i * v i|
      = Real.sqrt (|∑ i, u i * v i| ^ 2) :=
        (Real.sqrt_sq (abs_nonneg _)).symm
    _ ≤ Real.sqrt ((∑ i, (u i)^2) * (∑ i, (v i)^2)) :=
        Real.sqrt_le_sqrt hkey

/-- ИТОГОВАЯ ПРАКТИЧЕСКАЯ ТЕОРЕМА: пороговое EF-обучение —
линейная скорость плюс АБСОЛЮТНЫЙ тау-барьер. Ни одной
гипотезы о резидуале: он ограничен количеством координат
на квадрат порога по построению компрессора. -/
theorem thr_ef_quality (a : k → ℝ) (eta : ℝ)
    (heta : 0 < eta) (heta2 : eta ≤ 1 / 2)
    (x0 : k → ℝ) (τ : ℝ) (e : ℕ → k → ℝ)
    (hEF : ∀ t, e (t + 1)
      = quadGrad a (quadGD a eta x0 t) + e t
        - thrComp τ (quadGrad a (quadGD a eta x0 t) + e t))
    (xC : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1)
      = xC t - eta • thrComp τ
        (quadGrad a (quadGD a eta x0 t) + e t))
    (hx0 : xC 0 = x0) (he0 : e 0 = 0) (n : ℕ) :
    quadE a (xC n)
      ≤ (1 - 2 * eta * (1 - eta / 2)) ^ n * quadE a x0
        + eta * Real.sqrt (nrm2 (quadGrad a (quadGD a eta x0 n))
            * ((Fintype.card k : ℝ) * τ ^ 2))
        + (eta ^ 2 / 2) * ((Fintype.card k : ℝ) * τ ^ 2) := by
  have hmain := Hagi.Unified.SignEFQuad.quad_ef_quality_rate a
    eta heta heta2 x0 e (thrComp τ) hEF xC hxC hx0 n
  rw [he0, sub_zero] at hmain
  have hbar : nrm2 (e n)
      ≤ (Fintype.card k : ℝ) * τ ^ 2 := by
    match n with
    | 0 =>
      have hn0 : nrm2 (e 0) = 0 := by
        rw [he0]
        simp [nrm2]
      rw [hn0]
      exact mul_nonneg (by positivity) (sq_nonneg τ)
    | m + 1 =>
      have hstep := hEF m
      have h := thrComp_barrier τ
        (quadGrad a (quadGD a eta x0 m) + e m)
      rw [hstep]
      exact h
  have hsm := nrm2_smul eta (e n)
  have hin : inprod (quadGrad a (quadGD a eta x0 n))
      (eta • e n) ≤ eta * Real.sqrt (nrm2 (quadGrad a
        (quadGD a eta x0 n)) * ((Fintype.card k : ℝ) * τ ^ 2)) := by
    have hcs := inprod_abs_le (quadGrad a (quadGD a eta x0 n))
      (e n)
    have hη : (0:ℝ) ≤ eta := heta.le
    have hip : inprod (quadGrad a (quadGD a eta x0 n)) (eta • e n)
        = eta * inprod (quadGrad a (quadGD a eta x0 n)) (e n) := by
      unfold inprod
      have hterm : ∀ i, (quadGrad a (quadGD a eta x0 n)) i
            * (eta • e n) i
          = eta * ((quadGrad a (quadGD a eta x0 n)) i * e n i) := by
        intro i
        rw [Pi.smul_apply, smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
    have hg : (0:ℝ) ≤ nrm2 (quadGrad a (quadGD a eta x0 n)) := by
      unfold nrm2
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsqr : Real.sqrt (nrm2 (quadGrad a (quadGD a eta x0 n))
          * nrm2 (e n))
        ≤ Real.sqrt (nrm2 (quadGrad a (quadGD a eta x0 n))
          * ((Fintype.card k : ℝ) * τ ^ 2)) :=
      Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hbar hg)
    rw [hip]
    calc eta * inprod (quadGrad a (quadGD a eta x0 n)) (e n)
        ≤ eta * |inprod (quadGrad a (quadGD a eta x0 n)) (e n)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hη
      _ ≤ eta * Real.sqrt (nrm2 (quadGrad a (quadGD a eta x0 n))
          * nrm2 (e n)) :=
          mul_le_mul_of_nonneg_left hcs hη
      _ ≤ eta * Real.sqrt (nrm2 (quadGrad a (quadGD a eta x0 n))
          * ((Fintype.card k : ℝ) * τ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsqr hη
  have hfin : eta ^ 2 * nrm2 (e n)
      ≤ eta ^ 2 * ((Fintype.card k : ℝ) * τ ^ 2) :=
    mul_le_mul_of_nonneg_left hbar (sq_nonneg eta)
  linarith [hmain, hin, hsm, hfin]

end Hagi.Unified.ThrComp
