import Mathlib

/-!
# ExecutedCert (ответ на внешний аудит, 4.4 / P1-5)

Проблема: MeasurementCert (claimed/measured/delta),
StepContract и CertifiedTrajectory — три несвязанных
факта: исполнение перехода, измерение результата и
математическая гарантия передаются отдельными
гипотезами (связка `hlink` — внешняя).

`ExecutedCert` соединяет их в ОДНОМ зависимом
сертификате: измерение обязано согласовываться с
исполнением в пределах сертифицированной ошибки.

1. `measured_honest`: измеренный спуск ≤ реальный +
   ошибка (нельзя завысить измерение);
2. `measured_lower`: измеренный спуск ≥ декларированный
   − ошибка (нельзя занизить до отрицательного);
3. `telescope_measured`: сумма измерений вдоль
   выполненной цепочки ≤ суммарный реальный спуск +
   суммарная ошибка — кумулятивная честная бухгалтерия.
-/

namespace Hagi.Unified.ExecutedCert

variable {S : Type}

/-- Единый сертификат: исполнение + измерение + гарантия. -/
structure ExecutedCert (obj : S → ℝ) (step : S → S)
    (s : S) (measured : ℝ) (delta : ℝ) where
  /-- Декларированный спуск. -/
  drop : ℝ
  drop_pos : 0 < drop
  /-- Реальный спуск из исполнения. -/
  actual : obj (step s) ≤ obj s - drop
  /-- Ошибка измерения сертифицирована. -/
  delta_nn : 0 ≤ delta
  /-- СВЯЗКА ИЗМЕРЕНИЯ С ИСПОЛНЕНИЕМ (внутри типа,
  не внешняя гипотеза). -/
  link : |measured - (obj s - obj (step s))| ≤ delta

/-- Измерение нельзя завысить сверх реальности + ошибки. -/
theorem measured_honest (obj : S → ℝ) (step : S → S)
    (s : S) (m d : ℝ) (C : ExecutedCert obj step s m d) :
    m ≤ (obj s - obj (step s)) + d ∧ 0 < C.drop := by
  refine ⟨?_, C.drop_pos⟩
  have h := C.link
  have h2 := abs_le.mp h |>.2
  linarith

/-- Измерение не ниже декларации − ошибки. -/
theorem measured_lower (obj : S → ℝ) (step : S → S)
    (s : S) (m d : ℝ) (C : ExecutedCert obj step s m d) :
    C.drop - d ≤ m := by
  have h1 := C.link
  have h2 := C.actual
  have h3 : (obj s - obj (step s)) ≥ C.drop := by linarith
  have h4 := abs_le.mp h1 |>.1
  linarith

/-- Траектория исполнения: t-кратная итерация шага. -/
def traj (step : S → S) (s : S) : ℕ → S :=
  fun t => step^[t] s

/-- Кумулятивная честность: сумма измерений по цепочке
ВЫПОЛНЕННЫХ шагов ≤ суммарный реальный спуск +
суммарная ошибка. Каждое измерение связано со своим
исполнением самим типом сертификата. -/
theorem telescope_measured (obj : S → ℝ) (step : S → S)
    (s : S) (n : ℕ) (ms ds : Fin n → ℝ)
    (cs : ∀ t : Fin n,
      ExecutedCert obj step (traj step s t) (ms t) (ds t)) :
    ∑ t, ms t
      ≤ (obj s - obj (traj step s n)) + ∑ t, ds t
      ∧ ∀ t, 0 < (cs t).drop := by
  refine ⟨?_, fun t => (cs t).drop_pos⟩
  induction n with
  | zero => simp [traj]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have hlast := measured_honest obj step
      (traj step s n) (ms (Fin.last n)) (ds (Fin.last n))
      (cs (Fin.last n))
    have hpre := ih (fun t => ms t.castSucc)
      (fun t => ds t.castSucc) (fun t => cs t.castSucc)
    have heq : obj (traj step s (n + 1))
        = obj (step (traj step s n)) := by
      unfold traj
      exact congrArg obj (Function.iterate_succ_apply' step n s)
    linarith

end Hagi.Unified.ExecutedCert
