import Mathlib
import Hagi.Foundations.SumIdentities

/-!
# GRPO: групповая нормировка advantage (источник №33)

Источник №33: Shao et al., "DeepSeekMath: Pushing the Limits
of Mathematical Reasoning" / GRPO (arXiv 2402.19327). Вместо
отдельной value-сети advantage центрируется по группе:
A_i = r_i − mean(r) — baseline = средний reward группы G
ответов на один промпт. Экономия: нет критика (половина
параметров/вычислений PPO-сети).

Формализованное ядро (строгое, |G| = n > 0):
- `groupAdv`: A i = r i − (∑ r)/n;
- `groupAdv_sum_zero`: ∑ A_i = 0 — смещение-компенсация:
  групповой baseline не вносит систематического сдвига;
- `groupAdv_sq_decomp`: ∑(r−c)² − ∑(r−mean)² = n·(mean−c)²;
- `groupAdv_sq_min`: mean — ОПТИМАЛЬНЫЙ baseline (сумма
  квадратов минимальна ровно на среднем).
-/

namespace Hagi.Model.GRPO

open Finset

variable {n : ℕ}

/-- Групповой advantage: reward минус среднее группы. -/
noncomputable def groupAdv (r : Fin n → ℝ) (i : Fin n) : ℝ :=
  r i - (∑ j, r j) / n

/-- Сумма advantage по группе равна нулю. -/
theorem groupAdv_sum_zero (r : Fin n → ℝ) (hn : 0 < n) :
    ∑ i, groupAdv r i = 0 :=
  Hagi.Foundations.SumIdentities.sum_sub_mean_zero r hn

/-- Разложение разности: ∑(r−c)² − ∑(r−mean)² = n·(mean−c)²
(среднее — проекция: разность есть неотрицательный
квадрат). -/
theorem groupAdv_sq_decomp (r : Fin n → ℝ) (hn : 0 < n) (c : ℝ) :
    ∑ i, (r i - c) ^ 2
      - ∑ i, (r i - (∑ j, r j) / n) ^ 2
      = n * ((∑ j, r j) / n - c) ^ 2 :=
  Hagi.Foundations.SumIdentities.sq_decomp r hn c

/-- Среднее группы — оптимальный baseline: сумма квадратов
отклонений от mean не превосходит отклонений от ЛЮБОЙ
константы c. -/
theorem groupAdv_sq_min (r : Fin n → ℝ) (hn : 0 < n) (c : ℝ) :
    ∑ i, (r i - (∑ j, r j) / n) ^ 2 ≤ ∑ i, (r i - c) ^ 2 := by
  have hd := groupAdv_sq_decomp r hn c
  have hsq : 0 ≤ n * ((∑ j, r j) / n - c) ^ 2 := by
    have : 0 ≤ ((∑ j, r j) / n - c) ^ 2 := sq_nonneg _
    positivity
  linarith [hd, hsq]

/-- УРОВЕНЬ 3 No33: стандартизованный advantage
A_i = (r_i - mean)/sigma имеет ЕДИНИЧНУЮ дисперсию по
группе: sum A_i^2 = n (нормировка Dr.GRPO-стиля;
sigma^2 — групповая дисперсия). -/
theorem groupAdv_std_unit (r : Fin n → ℝ) (_hn : 0 < n)
    (sigma : ℝ) (hsig : 0 < sigma)
    (hsigdef : ∑ i, (r i - (∑ j, r j) / n) ^ 2 = sigma ^ 2 * n) :
    ∑ i, ((r i - (∑ j, r j) / n) / sigma) ^ 2 = n := by
  have hs2 : sigma ^ 2 ≠ 0 := by
    have : 0 < sigma ^ 2 := by positivity
    exact ne_of_gt this
  simp only [div_pow]
  rw [← Finset.sum_div, hsigdef, mul_div_cancel_left₀ _ hs2]

end Hagi.Model.GRPO
