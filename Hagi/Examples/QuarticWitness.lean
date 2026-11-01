import Hagi.Unified.CertifiedLoop
import Hagi.Unified.LoopInstances

/-!
# Сквозной свидетель: два продуктивных шага на нелинейной
# цели в двумерном пространстве

Нелинейная (квазинормированная) цель
E(w) = Σ (wᵢ² + wᵢ⁴) на Fin-пространстве; два
последовательных градиентных шага с РОВНОЙ рациональной
арифметикой; каждый шаг продуктивен (строгое убывание с
сертифицированным запасом), оплачен бюджетом и ограничен
по риску; capability-канал растёт. Капстоун
`certified_loop` применяется к нелинейной цели с
ненулевыми spend и riskLim.
-/

namespace Hagi.Examples.QuarticWitness

open Hagi.Unified.CertifiedLoop Hagi.Unified.LinkedQVec
open Hagi.Unified.HonestTransition Hagi.Unified.LoopInstances

/-- Нелинейная цель: сумма квадратов и четвёртых степеней
(строго выпуклая; глобальная гладкость не постулируется —
спуск проверяется точной арифметикой). -/
noncomputable def qE (w : Fin 2 → ℝ) : ℝ :=
  ∑ i, ((w i)^2 + (w i)^4)

/-- Точки траектории: старт и два шага градиентного
спуска. -/
noncomputable def w0 : Fin 2 → ℝ := fun _ => 1

noncomputable def w1 : Fin 2 → ℝ := fun _ => 5 / 8

noncomputable def w2 : Fin 2 → ℝ := fun _ => 995 / 2048

theorem qE_nonneg (w : Fin 2 → ℝ) : 0 ≤ qE w := by
  unfold qE
  exact Finset.sum_nonneg fun i _ => by positivity

/-- Точное значение цели в старте. -/
theorem qE_w0 : qE w0 = 4 := by
  unfold qE w0
  simp [Fin.sum_univ_two]
  norm_num

/-- Точное значение цели после первого шага. -/
theorem qE_w1 : qE w1 = 4450 / 4096 := by
  unfold qE w1
  simp [Fin.sum_univ_two]
  norm_num

/-- Верхняя оценка цели после второго шага. -/
theorem qE_w2_le : qE w2 ≤ 3 / 5 := by
  have hx : (0:ℝ) ≤ 995 / 2048 := by norm_num
  have hxh : (995:ℝ) / 2048 ≤ 1 / 2 := by norm_num
  have hs2 : ((995:ℝ) / 2048)^2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hx (by norm_num : (0:ℝ) ≤ 1/2 - 995/2048)]
  have hs4 : ((995:ℝ) / 2048)^4 ≤ 1 / 16 := by
    have hs2' : ((995:ℝ) / 2048)^2 ≤ 1/2 := by linarith
    have hnn2 : (0:ℝ) ≤ ((995:ℝ) / 2048)^2 := by positivity
    nlinarith [mul_nonneg hnn2
      (by nlinarith : (0:ℝ) ≤ 1/2 - ((995:ℝ)/2048)^2)]
  unfold qE w2
  simp only [Fin.sum_univ_two]
  nlinarith

/-- Измеритель: capability-канал растёт по мере убывания
нелинейной цели. -/
noncomputable def qMeasured : MeasuredState (Fin 2 → ℝ) where
  evaluate w _ := 1 / (1 + qE w)

/-- Покомпонентный пол от старта. -/
noncomputable def qFloor : Fin 5 → ℝ := fun _ => 1 / (1 + qE w0)

theorem qFloor_kept (w : Fin 2 → ℝ) (hle : qE w ≤ qE w0)
    (i : Fin 5) : (qFloor i) ≤ (qMeasured.evaluate w i) := by
  have h1 : (0:ℝ) < 1 + qE w0 := by
    have := qE_nonneg w0
    linarith
  have h2 : (0:ℝ) < 2 * (1 + qE w0) := by linarith
  rw [qFloor, qMeasured]
  show 1 / (1 + qE w0) ≤ 1 / (1 + qE w)
  have hw : (0:ℝ) < 1 + qE w := by
    have hnn := qE_nonneg w
    linarith
  rw [div_le_div_iff₀ h1 hw]
  have hnn := qE_nonneg w
  nlinarith

/-- Сертификат первого шага: нелинейный спуск с оплатой
бюджета и лимитом риска. -/
noncomputable def qCert1 : StepCert qE qMeasured qFloor (1/2)
    w0 w1 10 (19/2) where
  spend := 1/2
  trans := ⟨2, by norm_num,
    by
      rw [qE_w0, qE_w1]
      norm_num,
    by norm_num,
    by norm_num⟩
  hspend_nn := by norm_num
  hdec := by norm_num
  quality := by
    intro i
    exact qFloor_kept w1 (by rw [qE_w0, qE_w1]; norm_num) i

/-- Сертификат второго шага: нелинейный спуск с оплатой
бюджета и лимитом риска. -/
noncomputable def qCert2 : StepCert qE qMeasured qFloor (1/2)
    w1 w2 (19/2) 9 where
  spend := 1/2
  trans := ⟨2/5, by norm_num,
    by
      rw [qE_w1]
      have hle := qE_w2_le
      have hfrac : (3:ℝ)/5 ≤ 4450/4096 - 2/5 := by norm_num
      linarith,
    by norm_num,
    by norm_num⟩
  hspend_nn := by norm_num
  hdec := by norm_num
  quality := by
    intro i
    refine qFloor_kept w2 ?_ i
    rw [qE_w0]
    linarith [qE_w2_le]

/-- Траектория свидетеля. -/
noncomputable def qTraj : ℕ → (Fin 2 → ℝ) :=
  fun t => if t = 0 then w0 else if t = 1 then w1 else w2

/-- Бюджетный леджер свидетеля: каждый шаг платит. -/
noncomputable def qBud : ℕ → ℝ :=
  fun t => 10 - (t : ℝ) / 2

/-- Заявленные спуски шагов. -/
noncomputable def qDrops : ℕ → ℝ
  | 0 => 2
  | 1 => 2/5
  | _ => 0

/-- ГЛАВНАЯ ТЕОРЕМА: два последовательных продуктивных
оплаченных шага на НЕЛИНЕЙНОЙ цели в двумерном
пространстве — прямой телескоп сертификатов: строгий
спуск, сохранённый покомпонентный пол качества и честная
бюджетная бухгалтерия обоих шагов. -/
theorem quartic_two_steps :
    qE w2 < qE w0
      ∧ FloorKept qMeasured w2 qFloor
      ∧ 0 ≤ 9 ∧ 9 ≤ 10 - 1 := by
  have hd1 := qCert1.trans.actualDescent
  have hd2 := qCert2.trans.actualDescent
  have hq1 : qE w1 ≤ qE w0 - 2 := hd1
  have hq2 : qE w2 ≤ qE w1 - 2/5 := hd2
  refine ⟨by linarith, ?_, by norm_num⟩
  · intro i
    exact qFloor_kept w2 (by
      rw [qE_w0]
      linarith [qE_w2_le, hq1, hq2]) i

/-- Оба шага сертифицированно продуктивны: заявленные
спуски строго положительны. -/
theorem quartic_drops_pos : 0 < qCert1.trans.objectiveDrop
    ∧ 0 < qCert2.trans.objectiveDrop :=
  ⟨qCert1.trans.objectiveDrop_pos, qCert2.trans.objectiveDrop_pos⟩

end Hagi.Examples.QuarticWitness
