import Mathlib
import Hagi.Foundations.Recurrence
import Hagi.Optimization.LRSchedule

/-!
# DREAM — ускорение при задержанных градиентах (источник №15)

Источник №15: Gürbüzbalaban, Rafi, Aybat, Bajwa, "DREAM:
Delay-Resistant Acceleration with Momentum" (arXiv 2610.37444).

Идея: разделить ИНЕРЦИЮ (β) и ЭКСТРАПОЛЯЦИЮ точки градиента
(ν) — классические методы их связывают (Heavy Ball ν=0,
Нестеров ν=β). При задержке градиента τ экстраполяция
настраивается по задержке (ν ≈ M − 1/2, M = 2τ+1).

Итерация:
  y_k  = x_k + ν(x_k − x_{k−1});
  x_{k+1} = x_k − α∇f(y_{k−τ}) + β(x_k − x_{k−1}).

Формализован уровень 1 (dream_delay_recurrence):
- DREAMState: текущие/предыдущие параметры, история
  градиентов, коэффициенты (α, β, ν), задержка τ;
- dreamY: экстраполяционная точка;
- dreamStep: РОВНО рекурсия статьи (задержанный градиент из
  истории, независимая инерция);
- dream_delayed_gd: частный случай β=ν=0 — обычный
  запаздывающий градиентный шаг;
- Мост знаков в advance (Hagi.Model.dream_bridge, см.
  StageSemantics): при stepDir := (α/η)g − (β/η)m шаг advance
  реализует DREAM-обновление.

Scope: рекурсия и структура точны; сходимость
(dream_quadratic_stability, dream_strongly_convex_rate) —
следующие уровни (требуют гладкости/сильной выпуклости).
-/

namespace Hagi.Optimization.DREAM

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Состояние DREAM: текущие и предыдущие параметры, история
градиентов (g_hist k = ∇f(y_k)), коэффициенты и задержка. -/
structure DREAMState (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] where
  /-- Текущие параметры x_k. -/
  x : X
  /-- Предыдущие параметры x_{k−1}. -/
  xPrev : X
  /-- История градиентов в экстраполяционных точках. -/
  gHist : ℕ → X
  /-- Шаг α. -/
  alpha : ℝ
  /-- Инерция β. -/
  beta : ℝ
  /-- Экстраполяция ν (независима от β). -/
  nu : ℝ
  /-- Задержка τ. -/
  tau : ℕ

/-- ЭКСТРАПОЛЯЦИОННАЯ ТОЧКА: y_k = x_k + ν(x_k − x_{k−1}). -/
def dreamY (s : DREAMState X) : X :=
  s.x + s.nu • (s.x - s.xPrev)

/-- ЗАПАЗДЫВАЮЩИЙ ГРАДИЕНТ: ∇f(y_{k−τ}) из истории. -/
def delayedGrad (s : DREAMState X) (k : ℕ) : X :=
  s.gHist (k - s.tau)

/-- DREAM-ШАГ (рекурсия статьи): x_{k+1} = x_k − α∇f(y_{k−τ})
+ β(x_k − x_{k−1}) — задеержанный градиент из истории,
независимая инерция. -/
def dreamStep (s : DREAMState X) (k : ℕ) : X :=
  s.x - s.alpha • delayedGrad s k + s.beta • (s.x - s.xPrev)

/-- ЗАПАЗДЫВАЮЩИЙ GD (частный случай): при β = ν = 0 DREAM —
обычный градиентный шаг с задержкой x_{k+1} = x_k − αg_{k−τ}. -/
theorem dream_delayed_gd (s : DREAMState X) (k : ℕ)
    (hbeta : s.beta = 0) :
    dreamStep s k = s.x - s.alpha • delayedGrad s k := by
  rw [dreamStep, hbeta, zero_smul, add_zero]

/-- Моментум-член DREAM: β(x_k − x_{k−1}) — направление
инерции (совпадает с momentum-конвенцией HAGI). -/
def dreamMomentum (s : DREAMState X) : X :=
  s.beta • (s.x - s.xPrev)


/-- НОРМА ЭКСТРАПОЛЯЦИИ: ‖y_k − x_k‖ = |ν|·‖x_k − x_{k−1}‖ —
смещение точки градиента пропорционально коэффициенту
экстраполяции и скорости движения. -/
theorem dreamY_gap_norm (s : DREAMState X) :
    ‖dreamY s - s.x‖ = |s.nu| * ‖s.x - s.xPrev‖ := by
  rw [dreamY]
  rw [show s.x + s.nu • (s.x - s.xPrev) - s.x
      = s.nu • (s.x - s.xPrev) from by
      rw [add_sub_cancel_left]]
  rw [norm_smul, Real.norm_eq_abs]

/-- ЭКСТРАПОЛЯЦИЯ РАСТЁТ С ЗАДЕРЖКОЙ (структура параметров
статьи): рекомендуемое ν = M − 1/2 при M = 2τ+1 даёт
ν = 2τ + 1/2 — точка вычисления градиента выносится вперёд
пропорционально задержке; смещение ‖y−x‖ = (2τ+1/2)·‖x−x⁻‖. -/
theorem dream_tau_extrapolation (s : DREAMState X)
    (hnu : s.nu = (2 * (s.tau : ℝ) + 1) - 1 / 2) :
    ‖dreamY s - s.x‖ = (2 * (s.tau : ℝ) + 1 / 2) * ‖s.x - s.xPrev‖ := by
  rw [dreamY_gap_norm, hnu]
  have hnn : (0:ℝ) ≤ 2 * ((s.tau : ℝ)) + 1 - 1 / 2 := by
    have htau : (0:ℝ) ≤ (s.tau : ℝ) := Nat.cast_nonneg s.tau
    rw [sub_nonneg]
    linarith
  rw [abs_of_nonneg hnn]
  ring



/-! ## Склейка с PL-рекуррентностью (источники №15 × №11) -/

/-- ЗАПАЗДЫВАЮЩИЙ GD КАК PL-РЕКУРРЕНТНОСТЬ: если энергия
вдоль запаздывающего градиентного шага с «ошибкой
устаревания» σ удовлетворяет PL-неравенству
e_{k+1} ≤ (1−μα)e_k + σ²α², то ВЕСЬ аппарат LR-расписаний
применим к DREAM-GD: σ кодирует цену задержки τ. -/
theorem dream_gd_as_plRec (mu sig alpha : ℝ) (e : ℕ → ℝ)
    (hpl : ∀ k : ℕ, e (k + 1) ≤ (1 - mu * alpha) * e k
      + sig ^ 2 * alpha ^ 2) :
    Hagi.Optimization.LRSchedule.plRec mu sig
      (fun _ => alpha) e := by
  intro t
  exact hpl t

/-- СЛЕДСТВИЕ — ПОЛНАЯ WSD-ОЦЕНКА ДЛЯ DREAM-GD: запаздывающий
GD в PL-режиме (стабильная фаза m + late-фаза k, η = η_max)
наследует геометрическое сжатие + шумовой бюджет + late-decay
из wsd_full_bound (источник №11): цена задержки живёт в σ. -/
theorem dream_gd_wsd (mu sig etaMax : ℝ) (e : ℕ → ℝ) (m k : ℕ)
    (hpl : Hagi.Optimization.LRSchedule.plRec mu sig
      (fun _ => etaMax) e)
    (hmu : 0 < mu) (hetaMax : 0 < etaMax)
    (hwindow : mu * etaMax ≤ 1)
    (henn : ∀ t, 0 ≤ e t) :
    e (m + k)
      ≤ (1 - mu * etaMax) ^ m * e 0
        + sig ^ 2 * etaMax ^ 2
          * ((1 - (1 - mu * etaMax) ^ m) / (1 - (1 - mu * etaMax)))
        + (k : ℝ) * sig ^ 2 * etaMax ^ 2 :=
  Hagi.Optimization.LRSchedule.wsd_full_bound mu sig etaMax
    (fun _ => etaMax) e m k hpl hmu hetaMax hwindow
    (fun _ => le_of_lt hetaMax) (fun _ => le_refl _)
    henn (fun _ _ => rfl)

end Hagi.Optimization.DREAM
