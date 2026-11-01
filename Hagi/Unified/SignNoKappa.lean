import Hagi.Unified.SignStepCert

/-!
# У знакового шага нет равномерной drop-грани

Точный контрпример: на градиенте-точечной массе
(одна ненулевая координата) знаковый шаг сжимает норму
направления в квадрат числа координат. Следствие: не
существует равномерной константы, связывающей спуск
сжатого шага с квадратом градиента, — PL-скорость для
чистого знакового сжатия недостижима без дополнительных
механизмов (error feedback, покоординатная нижняя грань).
Это ЧЕСТНЫЙ ОТРИЦАТЕЛЬНЫЙ результат: компрессия без
компенсации стоит скорости.
-/

namespace Hagi.Unified.SignNoKappa

open Hagi.Unified.SignStepCert Hagi.Step.SignSGD
open Hagi.Unified.SignDescent
open Hagi.Unified.DescentCore
open Hagi.Unified.DescentCoreQuad

variable {k : Type*} [Fintype k] [Nonempty k] [DecidableEq k]

/-- Точечная масса в точке `j`: одна единичная
координата. -/
def pmX (j : k) : k → ℝ := fun i => if i = j then 1 else 0

omit [Fintype k] [Nonempty k] in
/-- Градиент точечной массы (при нулевом якоре) равен
самой массе. -/
theorem pmX_grad (j : k) : quadGrad (fun _ => 0) (pmX j) = pmX j := by
  funext i
  simp [quadGrad, pmX]

omit [Nonempty k] in
/-- Сумма модулей точечной массы равна единице. -/
theorem pmX_l1 (j : k) : ∑ i, |pmX j i| = 1 := by
  rw [Fintype.sum_eq_single j (fun b hb => by
    simp [pmX, hb])]
  simp [pmX]

omit [Nonempty k] in
/-- Норма точечной массы равна единице. -/
theorem pmX_nrm2 (j : k) : nrm2 (pmX j) = 1 := by
  unfold nrm2
  rw [Fintype.sum_eq_single j (fun b hb => by
    simp [pmX, hb])]
  simp [pmX]

/-- ТОЧНАЯ ИДЕНТИЧНОСТЬ: на точечной массе знаковый шаг
сжимает квадрат нормы направления в квадрат числа
координат. -/
theorem sign_pointmass_ratio (j : k) :
    nrm2 (signStep (fun _ => 0) (pmX j))
      * (Fintype.card k)^2 = 1 := by
  have hs : signScale (pmX j)
      = 1 / (Fintype.card k : ℝ) := by
    unfold signScale
    rw [pmX_l1]
  have key : ∑ i, (signStep (fun _ => 0) (pmX j) i)^2
      = (1 / (Fintype.card k : ℝ))^2 := by
    unfold signStep
    rw [pmX_grad]
    rw [Fintype.sum_eq_single j (fun b hb => by
      have hz : pmX j b = 0 := by simp [pmX, hb]
      simp [hz, sgn1])]
    have hsgn : sgn1 (pmX j j) = 1 := by simp [pmX, sgn1]
    rw [hsgn, hs]
    ring
  unfold nrm2
  rw [key]
  field_simp

/-- СЛЕДСТВИЕ (отрицательный результат): если константа
меньше единицы на квадрат размера, точечная масса
нарушает оценку «знаковый шаг ≥ κ · градиент». -/
theorem sign_no_uniform_floor (κ : ℝ) (_hκ : 0 < κ)
    (hκn : 1 / ((Fintype.card k : ℝ)^2) < κ) (j : k) :
    nrm2 (signStep (fun _ => 0) (pmX j))
      < κ * nrm2 (quadGrad (fun _ => 0) (pmX j)) := by
  have hg := pmX_grad j
  have hn := pmX_nrm2 j
  have hA : nrm2 (signStep (fun _ => 0) (pmX j))
      = 1 / ((Fintype.card k : ℝ)^2) := by
    have hc : ((Fintype.card k : ℝ)^2) ≠ 0 := by positivity
    exact eq_div_of_mul_eq hc (sign_pointmass_ratio j)
  rw [hA, hg, hn]
  linarith

end Hagi.Unified.SignNoKappa
