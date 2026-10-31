import Mathlib

/-!
# GradAccum — накопление градиентов микробатчами
# (источник №65: практика больших батчей; математическое
# ядро — fiberwise-декомпозиция сумм)

Идея: большой батч N разбивается на k микробатчей (по
памяти); градиенты накапливаются и усредняются. Формализуем
ЭКВИВАЛЕНТНОСТЬ: среднее по полному батчу = взвешенное
среднее микробатч-средних (веса = размеры частей), через
Finset.sum_fiberwise. Следствие: накопление по частям
математически тождественно одному большому шагу.
-/

namespace Hagi.Optimization.GradAccum

open Finset

variable {N : ℕ} [Fintype (Fin N)] [DecidableEq (Fin N)]

/-- Полный градиент батча: среднее по всем примерам. -/
noncomputable def fullGrad (f : Fin N → ℝ) : ℝ :=
  (∑ x, f x) / N

/-- Градиент микробатча i (по разбиению c). -/
noncomputable def microGrad {k : ℕ} (c : Fin N → Fin k)
    (f : Fin N → ℝ) (i : Fin k) : ℝ :=
  (∑ x ∈ univ.filter (fun x => c x = i), f x) / N

/-- ИСТОЧНИК №65, УРОВЕНЬ 1: ЭКВИВАЛЕНТНОСТЬ НАКОПЛЕНИЯ —
сумма микробатч-градиентов РАВНА полному батч-градиенту
(делённые на общий N, суммы по fiber-разбиению в точности
восстанавливают полную сумму; Finset.sum_fiberwise). -/
theorem accum_equiv {k : ℕ} (c : Fin N → Fin k)
    (f : Fin N → ℝ) :
    (∑ i, microGrad c f i) = fullGrad f := by
  have hfiber := Finset.sum_fiberwise Finset.univ c f
  unfold microGrad fullGrad
  rw [← Finset.sum_div]
  exact congrArg (fun t => t / (N:ℝ)) hfiber

end Hagi.Optimization.GradAccum
