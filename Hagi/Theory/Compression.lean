/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.DescentCore
import Hagi.Unified.RateTheory
import Hagi.Unified.SignComp
import Hagi.Energy.Quantizer
import Hagi.Runtime.CertChecker
import Hagi.Runtime.TernaryExact
import Hagi.Benchmarks.TernaryWitness
import Hagi.Optimization.EF21Quantizer
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Compression — the error-feedback canon (C434 → C515)

One canonical module for the EF/compression family (merged from
EFTheory.lean + EF21InStep.lean + CertTernaryJump.lean; namespaces
preserved, Continual.lean precedent). Each concept is described
ONCE here.

* The EF telescope (`Hagi.Unified.ErrorFeedback`): carrying the
  compression residual in the state makes the iterate shadow
  telescope-exact — `ef_telescope` — so compression shifts the
  error budget, never hides it. Quadratic quality transfer
  (`Hagi.Unified.EFQuad`), the sign compressor and its bit price
  (`Hagi.Unified.SignEFQuad`), the per-coordinate residual barrier
  (`Hagi.Unified.EFResidual`), the threshold compressor barrier
  (`Hagi.Unified.ThrComp`), and the grid-Q energy bridge
  (`Hagi.Unified.QuantEnergyBridge`).
* EF21 in-step (`Hagi.Theory.EF21InStep`): the in-step quantized
  loop — residual, telescope, energy split, and the certified
  reject-hold `ef21_reject_hold` (bench mode `ef21-step`, C474).
* The certified ternary jump (`Hagi.Theory.CertTernaryJump`): a
  jump to the ternary grid is admissible iff the exact ternary
  witness certifies it; otherwise the round is held
  (`ternary_hold_rejected`; bench mode `cert-tern`, C443).
-/

/-! ## EFTheory — the EF telescope canon (five merged sections, names preserved) -/

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

/-!
# Аналитический мост: квантование → энергия

Векторный контракт решётчатого квантования соединяется
с энергией через ЯВНУЮ липшицевость по евклидовой норме
(аналитическое условие вместо эмпирической
предпосылки): при константе L оценка энергии после
квантования — полушаг на корень из размера носителя,
умноженный на L.
-/

namespace Hagi.Unified.QuantEnergyBridge

open Hagi.Energy

variable {k : Type*} [Fintype k]

/-- ГЛАВНЫЙ МОСТ: при явной липшицевости энергии по
евклидовой норме изменение энергии после векторного
решётчатого квантования ограничено произведением
константы, полушага и корня из числа координат. -/
theorem gridQ_energy_bound (Δ : ℝ) (hΔ : 0 < Δ)
    (w : k → ℝ)
    (E : (k → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ u v : k → ℝ,
      |E u - E v| ≤ L * Real.sqrt (∑ i, (u i - v i) ^ 2)) :
    |E (gridQVec Δ hΔ w) - E w|
      ≤ L * Real.sqrt ((Fintype.card k : ℝ)) * (Δ / 2) := by
  have hnq : ∑ i, (gridQVec Δ hΔ w i - w i) ^ 2
      ≤ (Fintype.card k : ℝ) * (Δ / 2) ^ 2 := by
    have h := gridQVec_norm_sq Δ hΔ w
    have hsymm : ∑ i, (gridQVec Δ hΔ w i - w i) ^ 2
        = ∑ i, (w i - gridQVec Δ hΔ w i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [hsymm]
    exact h
  have hLip := hlip (gridQVec Δ hΔ w) w
  have hsqrt : Real.sqrt ((Fintype.card k : ℝ) * (Δ / 2) ^ 2)
      = Real.sqrt ((Fintype.card k : ℝ)) * (Δ / 2) := by
    have habs : Real.sqrt ((Δ / 2) ^ 2) = Δ / 2 := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg (by positivity)]
    rw [Real.sqrt_mul (by positivity)]
    rw [habs]
  have hmono : Real.sqrt (∑ i, (gridQVec Δ hΔ w i - w i) ^ 2)
      ≤ Real.sqrt ((Fintype.card k : ℝ) * (Δ / 2) ^ 2) :=
    Real.sqrt_le_sqrt hnq
  have hfin : |E (gridQVec Δ hΔ w) - E w|
      ≤ L * Real.sqrt ((Fintype.card k : ℝ)) * (Δ / 2) := by
    calc |E (gridQVec Δ hΔ w) - E w|
        ≤ L * Real.sqrt
            (∑ i, (gridQVec Δ hΔ w i - w i) ^ 2) := hLip
      _ ≤ L * Real.sqrt
          ((Fintype.card k : ℝ) * (Δ / 2) ^ 2) :=
            mul_le_mul_of_nonneg_left hmono hL
      _ = L * Real.sqrt ((Fintype.card k : ℝ)) * (Δ / 2) := by
            rw [hsqrt]
            ring
  exact hfin

end Hagi.Unified.QuantEnergyBridge

/-! ## EF21InStep — the in-step quantized loop (bench: ef21-step) -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace Hagi.Theory.EF21InStep

open Hagi.Runtime
open Finset

/-! ## The recursion identities (squared-sum carrier `Fin n → ℝ`) -/

variable {n : Type*} [Fintype n]
variable (Q : (n → ℝ) → (n → ℝ)) (g m e d : ℕ → (n → ℝ))

/-- The EF21 in-step recursion residual: under the update
`e_{t+1} = m_t − Q (m_t)` with `d_t = Q (m_t)`, the residual is
exactly the unexecuted part of the message vector. -/
theorem ef21_instep_residual (hE : ∀ t, e (t + 1) = m t - Q (m t))
    (hd : ∀ t, d t = Q (m t)) (t : ℕ) :
    e (t + 1) = m t - d t := by
  rw [hE t, ← hd t]

/-- The EXACT vector telescope of the in-step loop (the EF promise):
if `m_t = g_t + e_t`, `d_t = Q (m_t)` and the residual evolves by
`e_{t+1} = m_t − Q (m_t)`, then the accumulated compressed update
equals the accumulated exact gradient plus the endpoint residual:
`Σ_{t<T} d_t = Σ_{t<T} g_t + e_0 − e_T`.  No compressor assumption —
pure telescoping (the `Hagi.Step.ErrorFeedback.ef_cumulative_exact`
pattern on the squared-sum carrier). -/
theorem ef21_instep_telescope
    (hm : ∀ t, m t = g t + e t)
    (hE : ∀ t, e (t + 1) = m t - Q (m t)) (hd : ∀ t, d t = Q (m t))
    (T : ℕ) :
    ∑ t ∈ range T, d t = ∑ t ∈ range T, g t + e 0 - e T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, sum_range_succ, ih, hd T]
    have hE' := hE T
    rw [hm T] at hE'
    have hdT : Q (m T) = g T + e T - e (T + 1) := by
      rw [hE', hm T]; abel
    rw [hdT]
    abel

/-- The projection-type energy split, one step: the message energy
decomposes against the compressed direction and the residual —
`Σᵢ (m_t i)² ≤ 2·Σᵢ (d_t i)² + 2·Σᵢ (e_{t+1} i)²`.  This is the
pointwise identity consequence of `e_{t+1} = m_t − d_t` (i.e.
`(x + y)² ≤ 2x² + 2y²` via `0 ≤ (x − y)²`); NO compressor assumption. -/
theorem ef21_instep_energy_split
    (hE : ∀ t, e (t + 1) = m t - Q (m t)) (hd : ∀ t, d t = Q (m t))
    (t : ℕ) :
    ∑ i, (m t i) ^ 2
      ≤ 2 * ∑ i, (d t i) ^ 2 + 2 * ∑ i, (e (t + 1) i) ^ 2 := by
  have h1 : ∀ i : n, (m t i) ^ 2
      ≤ 2 * (d t i) ^ 2 + 2 * (e (t + 1) i) ^ 2 := by
    intro i
    have hE' := congrFun (hE t) i
    simp only [Pi.sub_apply] at hE'
    have hd' := congrFun (hd t) i
    rw [← hd'] at hE'
    have h2 : m t i = d t i + e (t + 1) i := by
      rw [hE']; ring
    rw [h2]
    nlinarith [sq_nonneg (d t i - e (t + 1) i)]
  calc ∑ i, (m t i) ^ 2
      ≤ ∑ i, (2 * (d t i) ^ 2 + 2 * (e (t + 1) i) ^ 2) :=
        sum_le_sum (fun i _ => h1 i)
    _ = 2 * ∑ i, (d t i) ^ 2 + 2 * ∑ i, (e (t + 1) i) ^ 2 := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]

/-- The energy split accumulated over the whole loop:
`Σ_{t<T} Σᵢ (m t i)² ≤ 2·Σ_{t<T} Σᵢ (d t i)² +
2·Σ_{t<T} Σᵢ (e (t+1) i)²` — the loop-level form of
`ef21_instep_energy_split`. -/
theorem ef21_instep_sum_energy
    (hE : ∀ t, e (t + 1) = m t - Q (m t)) (hd : ∀ t, d t = Q (m t))
    (T : ℕ) :
    ∑ t ∈ range T, ∑ i, (m t i) ^ 2
      ≤ 2 * ∑ t ∈ range T, ∑ i, (d t i) ^ 2
        + 2 * ∑ t ∈ range T, ∑ i, (e (t + 1) i) ^ 2 := by
  have h1 : ∀ t ∈ range T, (∑ i, (m t i) ^ 2
      ≤ 2 * ∑ i, (d t i) ^ 2 + 2 * ∑ i, (e (t + 1) i) ^ 2) :=
    fun t _ => ef21_instep_energy_split Q m e d hE hd t
  have h2 := sum_le_sum (f := fun t => ∑ i, (m t i) ^ 2)
    (g := fun t => 2 * ∑ i, (d t i) ^ 2 + 2 * ∑ i, (e (t + 1) i) ^ 2)
    h1
  refine le_trans h2 ?_
  simp [Finset.mul_sum, Finset.sum_add_distrib]

/-! ## The inexact floor for the residual -/

/-- The inexact floor: if `Q` is an `IsInexactCompressor Q α ε`
(the `Hagi.Optimization.EF21Quantizer` additive contract — the
honest form available for the ternary quantizer, which is NOT
contractive for any `α ∈ (0, 1]`), then the residual energy is
bounded: `Σᵢ (e_{t+1} i)² ≤ ((1−α)·‖m_t‖₂ + ε)²`.  Instantiated for
the ternary quantizer via `qTernVec_inexact` (`α = 0`, `ε = 0`). -/
theorem ef21_instep_residual_inexact {α ε : ℝ}
    (hC : Hagi.Optimization.EF21Quantizer.IsInexactCompressor Q α ε)
    (hE : ∀ t, e (t + 1) = m t - Q (m t)) (t : ℕ) :
    ∑ i, (e (t + 1) i) ^ 2
      ≤ ((1 - α) * Real.sqrt (∑ i, (m t i) ^ 2) + ε) ^ 2 := by
  have hflip : ∀ i : n, (e (t + 1) i) ^ 2
      = (Q (m t) i - m t i) ^ 2 := by
    intro i
    have hE' := congrFun (hE t) i
    simp only [Pi.sub_apply] at hE'
    rw [hE']; ring
  rw [Finset.sum_congr rfl (fun i _ => hflip i)]
  exact hC (m t)

/-! ## The bench bridge (ℚ certificate trajectory) -/

/-- The final objective of a certificate list: the `obj'` of the last
step, or `start` for the empty list (the executable fold twin of the
trainer's chained readouts). -/
def trajObj (start : ℚ) : List CertStepData → ℚ
  | [] => start
  | d :: ds => trajObj d.obj' ds

/-- The bench-valid bridge: a trajectory passing the executable
`checkTrajectory` telescopes at the rational readout level — the
final objective is at most the start minus the sum of declared
drops.  The trainer emits `drop = obj − obj'` exactly and
`checkStep` demands `drop ≤ obj − obj'`, so this is the honest
descent ledger of the accepted (compressed) steps; rejected steps
never enter the list (`ef21_reject_hold`). -/
theorem ef21_bench_valid (start : ℚ) (ds : List CertStepData)
    (h : checkTrajectory start ds = true) :
    trajObj start ds ≤ start - (ds.map CertStepData.drop).sum := by
  induction ds generalizing start with
  | nil => simp [trajObj]
  | cons d rest ih =>
    rw [checkTrajectory] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hobj, hck⟩, hrest⟩ := h
    have hdesc := (checkStep_spec hck).2.1
    have hsum : ((d :: rest).map CertStepData.drop).sum
        = d.drop + (rest.map CertStepData.drop).sum := by
      simp [List.map_cons]
    rw [trajObj, hsum]
    have hih := ih d.obj' hrest
    linarith

/-! ## Rejected trials can never ride the trajectory -/

/-- A rejected trial is a HOLD: whatever the readouts, a step with
declared `drop ≤ 0` — including the NEGATIVE-drop case of a
compressed step that would climb — can never pass `checkStep`, which
demands strict `0 < drop`.  This is the machine-checked reason the
ef21-step trainer excludes rejected steps from the emitted
trajectory and logs them as reject telemetry (reject-rate). -/
theorem ef21_reject_hold {E E' bud bud' rsk rsk' dr : ℚ}
    (hdr : dr ≤ 0) :
    checkStep ⟨E, E', dr, bud, bud', rsk, rsk'⟩ = false := by
  simp [checkStep, not_lt.mpr hdr]

end Hagi.Theory.EF21InStep

/-! ## CertTernaryJump — the certified ternary jump (bench: cert-tern) -/

namespace Hagi.Theory.CertTernaryJump

open Hagi.Runtime Hagi.Unified.TernaryWitness Hagi.Unified.DescentCoreQuad

/-! ## The jump step record -/

/-- The step record a trainer emits for a ternary jump: the
declared drop is exactly the readout difference `obj − obj'`
(nothing else is claimed). -/
def ternJumpStep (E E' bud bud' rsk rsk' : ℚ) : CertStepData :=
  ⟨E, E', E - E', bud, bud', rsk, rsk'⟩

/-! ## The acceptance criterion is admissive -/

/-- **Certified ternary jump acceptance**: if the post-jump energy
readout sits below the corpus ceiling `k·s²/8` while the pre-jump
  `quantOpt_energy_bound` / quant_jump_honest premise form, the SAME
  inequality the Python trainer evaluates exactly in `Fraction` — then
  the emitted jump step passes the executable checker (strict positive
  drop included).
The budget/risk readout obligations are the checker's usual
nonnegativity demands. -/
theorem ternary_jump_checkStep {k : ℕ} {s : ℚ}
    {E E' bud bud' rsk rsk' : ℚ} (hbud : 0 ≤ bud') (hrsk : 0 ≤ rsk')
    (hceil : E' ≤ (k : ℚ) * s ^ 2 / 8)
    (hxe : (k : ℚ) * s ^ 2 / 8 < E) :
    checkStep (ternJumpStep E E' bud bud' rsk rsk') = true := by
  have hdrop : 0 < E - E' := by linarith
  simp only [checkStep, ternJumpStep, Bool.and_eq_true]
  exact ⟨⟨⟨decide_eq_true hdrop, by norm_num⟩, decide_eq_true hbud⟩,
    decide_eq_true hrsk⟩

/-! ## The ℝ-side ceiling (corpus link) -/

/-- The corpus ceiling on `Fin m`: under the in-range premise the
ternary-quantized optimum's energy is at most `m·s²/8` —
`quantOpt_energy_bound` restated, i.e. the real-side source of the
`hceil` premise feeding `ternary_jump_checkStep` whenever the
run's energy readouts are rational (they are: `Fraction` trainer). -/
theorem ternary_jump_energy {m : ℕ} (s : ℝ) (hs : 0 < s)
    (a : Fin m → ℝ) (hin : ∀ i, ternInRange s (a i)) :
    quadE a (quantOpt s a) ≤ (Fintype.card (Fin m) : ℝ) * s ^ 2 / 8 :=
  quantOpt_energy_bound s hs a hin

/-! ## Holds can never ride the trajectory -/

/-- A rejected jump is a HOLD: an identity transition with declared
`drop = 0`. The executable checker — which demands strict
`0 < drop` — rejects it: this is the machine-checked reason the
trainer EXCLUDES hold steps from the emitted trajectory and logs
them separately (bench_bridge.py `holds` telemetry). -/
theorem ternary_hold_rejected (E bud rsk : ℚ) :
    checkStep (ternJumpStep E E bud bud rsk rsk) = false := by
  simp [checkStep, ternJumpStep]

end Hagi.Theory.CertTernaryJump

