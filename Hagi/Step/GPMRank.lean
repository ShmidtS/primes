/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# GPMRank — выбор ранга памяти GPM: забывание против скорости

`update_gpm_bases`: `k_new` направлений по доле энергии (`max_rank_frac`).
`pythagoras_k` (GPMProjection) даёт точную цену: шаг теряет энергию градиента
нового домена в памяти. Затраты ранга `k`: `cost k = tail k + E k`, где
`tail k` — энергия хвоста старого домена (забывание, убывает по `k`), `E k` —
энергия градиента нового домена в первых `k` направлениях (растёт).

* `stop_iff` — остановка на `k` ⇔ прирост цены скорости ≥ снижения забывания;
* `stop_stable` — при выпуклом `tail` и `E` остановка устойчива: следующий
  ранг тоже не улучшает (первый локальный минимум — глобальный).

Код: 90% энергии блокировали обучение (983576b) — `E k` росло быстрее, чем
падало `tail k`.
-/

namespace Hagi.Step.GPMRank

/-- Затраты ранга `k`: забывание `tail k` (энергия хвоста старого домена) плюс
потеря скорости нового домена `E k` (энергия его градиента в памяти). -/
noncomputable def cost (tail E : ℕ → ℝ) (k : ℕ) : ℝ := tail k + E k
/-- Остановка в `k` оправдана, если следующий ранг не уменьшает затраты. -/
theorem stop_iff (tail E : ℕ → ℝ) (k : ℕ) :
    cost tail E (k+1) ≤ cost tail E k ↔ E (k+1) - E k ≤ tail k - tail (k+1) := by
  unfold cost; constructor <;> intro h <;> linarith
/-- При убывающем выпуклом `tail` (приращения убывают по модулю) и `E` с
неубывающими приращениями остановка устойчива: следующий ранг тоже не улучшает
затраты. -/
theorem stop_stable (tail E : ℕ → ℝ) (htail : Antitone tail)
    (hconvT : ∀ k, tail (k+1) - tail k ≤ tail (k+2) - tail (k+1))
    (hconvE : ∀ k, E (k+1) - E k ≤ E (k+2) - E (k+1)) (k : ℕ)
    (hstop : cost tail E (k+1) ≥ cost tail E k) :
    cost tail E (k+2) ≥ cost tail E (k+1) := by
  have h1 : tail k + E k ≤ tail (k+1) + E (k+1) := hstop
  have hA : tail (k+1) ≤ tail k := htail (Nat.le_succ k)
  have hB : tail (k+1+1) ≤ tail (k+1) := htail (Nat.le_succ (k+1))
  have hE : E (k+1) - E k ≤ E (k+1+1) - E (k+1) := by
    have h := hconvE k
    rw [show k + 2 = k + 1 + 1 by omega] at h
    exact h
  have hT : tail (k+1) - tail k ≤ tail (k+1+1) - tail (k+1) := by
    have h := hconvT k
    rw [show k + 2 = k + 1 + 1 by omega] at h
    exact h
  show tail (k+1) + E (k+1) ≤ tail (k+2) + E (k+2)
  have hgoal : tail (k+1) + E (k+1) ≤ tail (k+1+1) + E (k+1+1) := by linarith
  rw [show k + 2 = k + 1 + 1 by omega]
  exact hgoal

end Hagi.Step.GPMRank
