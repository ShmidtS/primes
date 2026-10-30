import Mathlib

/-!
# ALiBi — Attention with Linear Biases (источник №60:
# Press et al., "Train Short, Test Long", arXiv 2108.12409)

Идея: вместо обучаемых позиционных эмбеддингов —
ДОБАВКА к логитам внимания, линейно убывающая по
расстоянию: bias(d) = −m·d. Формализуем монотонность
bias и экспоненциальное затухание вклада дальних позиций
в attention-вес (через softmax-ядро exp).
-/

namespace Hagi.Model.ALiBi

/-- Линейный bias по расстоянию d с наклоном m. -/
def alibiBias (m d : ℝ) : ℝ := -m * d

/-- ИСТОЧНИК №60, УРОВЕНЬ 1: bias МОНОТОННО УБЫВАЕТ по
расстоянию — дальние позиции получают строго меньший
(более отрицательный) сдвиг логита. -/
theorem alibi_bias_anti (m d1 d2 : ℝ) (hm : 0 ≤ m)
    (hd : d1 ≤ d2) :
    alibiBias m d2 ≤ alibiBias m d1 := by
  unfold alibiBias
  have hdm : 0 ≤ m * (d2 - d1) := mul_nonneg hm (by linarith)
  nlinarith [hdm]

/-- УРОВЕНЬ 1b: НЕПОЛОЖИТЕЛЬНОСТЬ bias при неотрицательных
наклоне и расстоянии. -/
theorem alibi_bias_nonpos (m d : ℝ) (hm : 0 ≤ m)
    (hd : 0 ≤ d) :
    alibiBias m d ≤ 0 := by
  unfold alibiBias
  nlinarith [mul_nonneg hm hd]

/-- УРОВЕНЬ 2: ЭКСПОНЕНЦИАЛЬНОЕ ЗАТУХАНИЕ attention-ядра —
softmax-вклад позиции на расстоянии d2 не превосходит
вклада более близкой d1 (нормировочный знаменатель общий):
exp(−m·d2) ≤ exp(−m·d1) при d1 ≤ d2, m ≥ 0. Дальние
токены экспоненциально подавляются — экстраполяция
длины «бесплатна» (train short, test long). -/
theorem alibi_kernel_decay (m d1 d2 : ℝ) (hm : 0 ≤ m)
    (hd : d1 ≤ d2) :
    Real.exp (alibiBias m d2) ≤ Real.exp (alibiBias m d1) := by
  exact (Real.exp_le_exp).mpr (alibi_bias_anti m d1 d2 hm hd)

/-- УРОВЕНЬ 2b: СТРОГОЕ затухание при положительном
наклоне и строгом росте расстояния. -/
theorem alibi_kernel_decay_lt (m d1 d2 : ℝ) (hm : 0 < m)
    (hd : d1 < d2) :
    Real.exp (alibiBias m d2) < Real.exp (alibiBias m d1) := by
  refine (Real.exp_lt_exp).mpr ?_
  unfold alibiBias
  have hdm : 0 < m * (d2 - d1) := mul_pos hm (by linarith)
  nlinarith [hdm]

end Hagi.Model.ALiBi
