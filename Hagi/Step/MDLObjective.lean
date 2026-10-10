/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# MDL-регуляризованная цель обучения

Вычислимая цель `J(θ) = L_pred(θ) + λ·L_code(θ)`: ошибка
предсказания плюс λ-взвешенная оценка длины описания модели
(мотивация — MDL/колмогоровская сложность; сама K(x)
невычислима, поэтому L_code — явная вычислимая посылка,
например вариационная граница с гауссовым смеси-приором).

Модуль фиксирует только алгебру цели: разложение приращения J
на предсказательную и кодовую части, условия доминирования и
вырожденные случаи. Никакой связи с обобщением здесь не
утверждается (см. открытый этап 5 плана формализации).
-/

open Real Finset

namespace Hagi.MDL

/-- Полная MDL-цель: предсказание + λ · длина описания. -/
def mdlObjective (Lpred Lcode : ℝ → ℝ) (lam : ℝ) : ℝ → ℝ :=
  fun θ => Lpred θ + lam * Lcode θ

/-- Приращение цели распадается на приращения частей. -/
theorem mdlObjective_delta (Lpred Lcode : ℝ → ℝ) (lam : ℝ) (θ θ' : ℝ) :
    mdlObjective Lpred Lcode lam θ' - mdlObjective Lpred Lcode lam θ
      = (Lpred θ' - Lpred θ) + lam * (Lcode θ' - Lcode θ) := by
  unfold mdlObjective
  ring

/-- Если обе части не растут (предсказание и код), цель не
растёт — тривиальная, но корректная монотонность композиции. -/
theorem mdlObjective_nonincreasing (Lpred Lcode : ℝ → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (θ θ' : ℝ)
    (hp : Lpred θ' ≤ Lpred θ) (hc : Lcode θ' ≤ Lcode θ) :
    mdlObjective Lpred Lcode lam θ' ≤ mdlObjective Lpred Lcode lam θ := by
  have h := mdlObjective_delta Lpred Lcode lam θ θ'
  have hc' : lam * (Lcode θ' - Lcode θ) ≤ 0 := by
    have : Lcode θ' - Lcode θ ≤ 0 := by linarith
    nlinarith
  linarith

/-- Обмен «предсказание ↔ код»: цель убывает на c, если
выигрыш предсказания ≥ delta, а λ-цена удлинения кода
≤ delta − c. -/
theorem mdlObjective_tradeoff (Lpred Lcode : ℝ → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (θ θ' delta c : ℝ)
    (hp : Lpred θ - Lpred θ' ≥ delta) (hdelta : 0 ≤ delta)
    (hc : lam * (Lcode θ' - Lcode θ) ≤ delta - c) (hc0 : 0 < c) :
    mdlObjective Lpred Lcode lam θ' + c ≤ mdlObjective Lpred Lcode lam θ := by
  have hp' : Lpred θ' - Lpred θ ≤ -delta := by linarith
  have h := mdlObjective_delta Lpred Lcode lam θ θ'
  unfold mdlObjective
  linarith

/-- λ = 0 выключает кодовую часть — цель совпадает с
предсказательной. -/
theorem mdlObjective_lambda_zero (Lpred Lcode : ℝ → ℝ) (θ : ℝ) :
    mdlObjective Lpred Lcode 0 θ = Lpred θ := by
  unfold mdlObjective
  ring

/-- Отрицательный λ не имеет MDL-смысла (поощряет длинный
код); цель всё ещё определена, но tradeoff-теоремы выше его
исключают. -/
theorem mdlObjective_neg_lambda_forbidden (Lpred Lcode : ℝ → ℝ)
    (lam : ℝ) (h : lam < 0) :
    ¬ (0 ≤ lam) := by linarith

end Hagi.MDL
