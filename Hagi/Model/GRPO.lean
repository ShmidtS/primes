import Mathlib

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
    ∑ i, groupAdv r i = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hS : ∑ i, groupAdv r i
      = (∑ i, r i) - n * ((∑ j, r j) / n) := by
    unfold groupAdv
    rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const]
    simp
  have hc : n * ((∑ j, r j) / n) = ∑ j, r j := by
    rw [mul_comm, div_mul_cancel₀ _ hn']
  rw [hS, hc, sub_self]

/-- Разложение разности: ∑(r−c)² − ∑(r−mean)² = n·(mean−c)²
(среднее — проекция: разность есть неотрицательный
квадрат). -/
theorem groupAdv_sq_decomp (r : Fin n → ℝ) (hn : 0 < n) (c : ℝ) :
    ∑ i, (r i - c) ^ 2
      - ∑ i, (r i - (∑ j, r j) / n) ^ 2
      = n * ((∑ j, r j) / n - c) ^ 2 := by
  have hz : ∑ i, (r i - (∑ j, r j) / n) = 0 :=
    groupAdv_sum_zero r hn
  set m : ℝ := (∑ j, r j) / n with hm
  have hpe : ∀ i, (r i - c) ^ 2 - (r i - m) ^ 2
      = 2 * (r i - m) * (m - c) + (m - c) ^ 2 := by
    intro i
    ring
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun i _ => hpe i)]
  rw [Finset.sum_add_distrib]
  have hterm1 : ∑ i, 2 * (r i - m) * (m - c) = 0 := by
    rw [show (0:ℝ) = 2 * (m - c) * ∑ i, (r i - m) from by
        rw [hz]
        ring]
    rw [Finset.mul_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => r i - m)
      (a := 2 * (m - c))]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hterm1, Finset.sum_const]
  simp [Finset.card_univ, Fintype.card_fin]

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

end Hagi.Model.GRPO

