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

/-- ДОМИНИРОВАНИЕ ОСНОВНОГО СОСТОЯНИЯ: вес минимума
энергии не меньше веса любого конкурента при ЛЮБОЙ
положительной температуре (экспонента антимонотонна). -/
theorem gibbsW_min_dominates (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (vstar v : V) (hle : E vstar ≤ E v) :
    gibbsW E T v ≤ gibbsW E T vstar := by
  unfold gibbsW
  exact Real.exp_le_exp.mpr
    ((div_le_div_iff_of_pos_right hT).mpr (neg_le_neg hle))

/-- ГЛАВНЫЙ ВЫВОД: нормированный вес основного состояния
не меньше равномерного — минимум доминирует в среднем. -/
theorem gibbs_min_weight_ge_uniform (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) [Nonempty V] (vstar : V)
    (hmin : ∀ v, E vstar ≤ E v) :
    1 / (Fintype.card V : ℝ)
      ≤ gibbsW E T vstar / gibbsZ E T := by
  have hZpos : 0 < gibbsZ E T := gibbsZ_pos E T hT
  have hZle : gibbsZ E T
      ≤ (Fintype.card V : ℝ) * gibbsW E T vstar := by
    calc gibbsZ E T = ∑ v, gibbsW E T v := rfl
      _ ≤ ∑ v, gibbsW E T vstar :=
        Finset.sum_le_sum fun v _ =>
          gibbsW_min_dominates E T hT vstar v (hmin v)
      _ = (Fintype.card V : ℝ) * gibbsW E T vstar := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : (1/(Fintype.card V : ℝ)) * gibbsZ E T
      ≤ (1/(Fintype.card V : ℝ))
        * ((Fintype.card V : ℝ) * gibbsW E T vstar) :=
    mul_le_mul_of_nonneg_left hZle (by positivity)
  have h2 : (1/(Fintype.card V : ℝ))
      * ((Fintype.card V : ℝ) * gibbsW E T vstar)
      = gibbsW E T vstar := by field_simp
  rw [le_div_iff₀ hZpos]
  linarith [h1, h2]

end Hagi.Probability
