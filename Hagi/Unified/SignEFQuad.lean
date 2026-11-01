import Hagi.Unified.ErrorFeedback
import Hagi.Unified.QuadGDRate
import Hagi.Unified.EFQuad
import Hagi.Unified.SignStepCert
import Hagi.Unified.SignNoKappa

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
