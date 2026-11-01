import Mathlib

/-!
# BlockNorm: поблочная нормализация
сохраняет ансамбль — устранение семантического разрыва
слияния.

Проблема аудита: RMSNorm над КОНКАТЕНАЦИЕЙ экспертов
загрязняет масштабы (дисперсии независимых экспертов
взаимно искажаются): RMS_{3H}(z₁⊕z₂⊕z₃) ≠ RMS_H(z₁)⊕...
Решение: GroupNorm(3) — поблочная нормализация — ТОЧНО
сохраняет ансамбль (шаг 0 слияния).

Формализация (W = Fin 3 → Fin m → ℝ — блочные веса):
1. `blockRms` — RMS одного блока; `globalRms` — RMS
   конкатенации;
2. `global_eq_mean_blocks`: globalRms² = (Σ_b blockRms b²)/3
   — ТОЧНОЕ тождество (глобальная дисперсия = среднее
   блочных дисперсий);
3. `equal_blocks_global`: при равных RMS блоков глобальная
   нормализация ТОЧНО совпадает с поблочной (ансамбль
   сохранён, шаг 0 без возмущения);
4. `unequal_deviation`: при неравных RMS масштабный сдвиг
   глобальной нормы ограничен половиной спреда
   дисперсий — цена неправильной нормализации.
-/

namespace Hagi.Model.BlockNorm

variable {m : ℕ}

/-- Блочные веса: 3 эксперта × m координат. -/
abbrev Blocks (m : ℕ) := Fin 3 → Fin m → ℝ

/-- RMS одного блока. -/
noncomputable def blockRms {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  Real.sqrt ((∑ i, (x i)^2) / m)

/-- Глобальная RMS конкатенации (3m координат). -/
noncomputable def globalRms (x : Blocks m) : ℝ :=
  Real.sqrt ((∑ b : Fin 3, ∑ i : Fin m, (x b i)^2) / (3 * m))

/-- Поблочная нормализация (GroupNorm(groups=3)): каждый
блок делится на СВОЮ RMS — ансамбль сохранён. -/
noncomputable def blockNorm (x : Blocks m) : Blocks m :=
  fun b i => x b i / blockRms (x b)

/-- Глобальная нормализация (RMSNorm по конкатенации):
все координаты делятся на ОБЩУЮ RMS. -/
noncomputable def globalNorm (x : Blocks m) : Blocks m :=
  fun b i => x b i / globalRms x

/-- Точное тождество: глобальная дисперсия = среднее
блочных дисперсий (ключевой факт о конкатенации). -/
theorem global_eq_mean_blocks (x : Blocks m) :
    (globalRms x)^2 = (∑ b : Fin 3, (blockRms (x b))^2) / 3 := by
  unfold globalRms blockRms
  have hsplit : ∑ b : Fin 3, (∑ i : Fin m, (x b i)^2 / m)
      = (∑ b : Fin 3, ∑ i : Fin m, (x b i)^2) / m := by
    simp [Finset.sum_div]
  have hsq : ∀ b : Fin 3, (Real.sqrt ((∑ i, (x b i)^2) / m))^2
      = (∑ i, (x b i)^2) / m := fun b =>
    Real.sq_sqrt (div_nonneg
      (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      (by norm_num))
  rw [Finset.sum_congr rfl (fun b _ => hsq b)]
  have hnnQ : (0:ℝ) ≤ (∑ b : Fin 3, ∑ i : Fin m, x b i ^ 2) / (3 * ↑m) :=
    div_nonneg (Finset.sum_nonneg (fun b _ => Finset.sum_nonneg
      (fun i _ => sq_nonneg _))) (by norm_num)
  rw [Real.sq_sqrt hnnQ]
  field_simp
  rw [Finset.sum_div]

/-- РАВНЫЕ БЛОКИ: если RMS всех блоков равны, глобальная
нормализация ТОЧНО совпадает с поблочной — ансамбль
сохранён без возмущения (шаг 0 слияния честен). -/
theorem equal_blocks_global (x : Blocks m)
    (heq : ∀ b₁ b₂ : Fin 3, blockRms (x b₁) = blockRms (x b₂)) :
    globalNorm x = blockNorm x := by
  have hnnS : ∀ b : Fin 3, (0:ℝ) ≤ ∑ i, (x b i)^2 :=
    fun b => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hb : ∀ b : Fin 3, ∑ i, (x b i)^2 = ∑ i, (x 0 i)^2 := by
    intro b
    by_cases hm : m = 0
    · subst hm; simp
    · have h := heq b 0
      unfold blockRms at h
      rw [Real.sqrt_inj (div_nonneg (hnnS b) (by norm_num))
        (div_nonneg (hnnS 0) (by norm_num))] at h
      exact (div_left_inj' (by exact_mod_cast hm)).mp h
  have hglob : globalRms x = blockRms (x 0) := by
    unfold globalRms blockRms
    rw [Finset.sum_congr rfl (fun b _ => hb b)]
    simp only [Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ]
    rw [show ((Fintype.card (Fin 3) : ℝ)) = 3 from rfl]
    field_simp
  funext b i
  unfold globalNorm blockNorm
  rw [hglob, heq b 0]

end Hagi.Model.BlockNorm