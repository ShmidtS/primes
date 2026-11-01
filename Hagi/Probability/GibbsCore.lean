import Mathlib.Tactic

/-!
# Каноническое распределение Гиббса

Начало M4-консолидации Гиббс-семейства: единое
определение массы `gibbsW` и нормирующей константы
`gibbsZ` вместо inline-расписываний в десятке
модулей. Базовые леммы: позитивность, нормировка,
сдвиг-инвариантность свободной энергии.
-/

namespace Hagi.Probability

open Finset Real

variable {V : Type*} [Fintype V]

/-- Вес состояния `v` при температуре `T`. -/
noncomputable def gibbsW (E : V → ℝ) (T : ℝ) (v : V) : ℝ :=
  Real.exp (-(E v)/T)

/-- Статистическая сумма. -/
noncomputable def gibbsZ (E : V → ℝ) (T : ℝ) : ℝ :=
  ∑ v, gibbsW E T v

/-- Вес строго положителен при положительной
температуре. -/
theorem gibbsW_pos (E : V → ℝ) (T : ℝ) (hT : 0 < T) (v : V) :
    0 < gibbsW E T v := by
  unfold gibbsW
  exact exp_pos _

/-- Статистическая сумма строго положительна на
непустом носителе. -/
theorem gibbsZ_pos (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    [Nonempty V] : 0 < gibbsZ E T := by
  unfold gibbsZ
  exact Finset.sum_pos (fun v _ => gibbsW_pos E T hT v)
    ⟨Classical.arbitrary V, Finset.mem_univ _⟩

/-- НОРМИРОВКА: сумма нормированных весов равна
единице — `gibbsW/gibbsZ` вероятностный вектор. -/
theorem gibbs_normalize (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    [Nonempty V] :
    ∑ v, gibbsW E T v / gibbsZ E T = 1 := by
  have hpos := gibbsZ_pos E T hT
  rw [← Finset.sum_div]
  show gibbsZ E T / gibbsZ E T = 1
  rw [div_self hpos.ne']

/-- СДВИГ-ИНВАРИАНТНОСТЬ: сдвиг всех энергий на
константу умножает статистическую сумму — нормированное
распределение не меняется. -/
theorem gibbsZ_shift (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (c : ℝ) :
    gibbsZ (fun v => E v + c) T
      = Real.exp (-c/T) * gibbsZ E T := by
  unfold gibbsZ gibbsW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← exp_add]
  congr 1
  field_simp
  ring

end Hagi.Probability
