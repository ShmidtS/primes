import Mathlib

/-!
# Weight Tying (источник №49)

Источник №49: Press & Wolf, "Using the Output Embedding to
Improve Language Models" (arXiv 1608.05859). Совместное
использование матрицы входных эмбеддингов и выходной
проекции (softmax-слой): E_out = E_in^T — параметры
проекции УДЕШАЕТСЯ ВДВОЕ (mn вместо 2mn), а связка
пространств улучшает маленькие модели.

Формализованное ядро (строгое):
- `wt_params`: связанная конфигурация — mn параметров;
- `untied_params`: раздельная — 2mn;
- `wt_saving`: при mn > 0 связывание СТРОГО экономит
  параметры (mn < 2mn).
-/

namespace Hagi.Model.WeightTying

/-- Параметры связанной конфигурации. -/
noncomputable def wtParams (m n : ℝ) : ℝ := m * n

/-- Параметры раздельной конфигурации. -/
noncomputable def untiedParams (m n : ℝ) : ℝ := 2 * m * n

/-- СТРОГАЯ экономия при ненулевом словаре. -/
theorem wt_saving (m n : ℝ) (hmn : 0 < m * n) :
    wtParams m n < untiedParams m n := by
  unfold wtParams untiedParams
  nlinarith [hmn]

end Hagi.Model.WeightTying
