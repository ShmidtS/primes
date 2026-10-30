import Mathlib

/-!
# Best-of-N: rejection sampling (источник №53)

Источник №53: Dong et al., "RAFT: Reward rAnked FineTuning"
(arXiv 2304.06767); best-of-n sampling (Stiennon et al.).
Из N сгенерированных ответов отбирается лучший по награде
(rejection sampling): fine-tuning на отобранном.

Формализованное ядро (строгое):
- `best_of_n_mean_le_sup`: средняя награда группы НЕ
  превосходит максимума — отбор лучшего никогда не хуже
  среднего по группе (порядковая гарантия);
- `best_of_n_pos`: если хоть один ответ неотрицателен,
  отбор неотрицателен (спасение от полностью плохой
  группы).
-/

namespace Hagi.Model.BestOfN

open Finset

variable {n : ℕ}

/-- Средняя награда не превосходит максимума (Finset.sup'). -/
theorem best_of_n_mean_le_sup (r : Fin n → ℝ) (hn : 0 < n) :
    (∑ i, r i) / n
      ≤ Finset.sup' Finset.univ (⟨(Fin.pos_iff_nonempty.mp hn).some,
        Finset.mem_univ _⟩) r := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨(Fin.pos_iff_nonempty.mp hn).some, Finset.mem_univ _⟩
  have hle : ∀ i ∈ Finset.univ,
      r i ≤ Finset.sup' Finset.univ hne r :=
    fun i _ => Finset.le_sup' r (Finset.mem_univ i)
  have hsum : (∑ i, r i)
      ≤ (n : ℝ) * Finset.sup' Finset.univ hne r := by
    have h2 := Finset.sum_le_sum hle
    rw [Finset.sum_const] at h2
    simp at h2
    exact h2
  have hn' : ((n : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mul_comm] at hsum
  refine (div_le_iff₀ ?_).mpr hsum
  exact_mod_cast hn

/-- Отбор неотрицателен при наличии неотрицательного
ответа. -/
theorem best_of_n_pos (r : Fin n → ℝ) (hn : 0 < n) (i : Fin n)
    (hi : 0 ≤ r i) :
    0 ≤ Finset.sup' Finset.univ (⟨(Fin.pos_iff_nonempty.mp hn).some,
        Finset.mem_univ _⟩) r :=
  le_trans hi (Finset.le_sup' r (Finset.mem_univ i))

end Hagi.Model.BestOfN
