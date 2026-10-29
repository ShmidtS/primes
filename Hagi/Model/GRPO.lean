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
- (отложено: groupAdv_sq_min — ∑ (r_i − c)² минимизируется
  на c = mean; вынос константы из Finset-суммы нестабилен
  в пине — см. LESSONS).
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

end Hagi.Model.GRPO
