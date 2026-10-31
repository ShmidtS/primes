import Mathlib
import Hagi.Optimization.Lookahead
import Hagi.Model.ModelSoup

/-!
# LookaheadTrajectory — сертификация якорной траектории
(связка №75 × ModelSoup/EMA, такт №238)

Якорная последовательность Lookahead
w_{n+1} = w_n + α·(x_{(n+1)·k} − w_n) — это В ТОЧНОСТИ
EMA-рекурсия (β = 1−α) от подпоследовательности быстрых
итератов. Поэтому вся мощь ema_invariant переносится:
если якорь старта и все быстрые итераты лежат в [lo,hi],
то ВСЯ якорная траектория стабильно в [lo,hi] —
двухмасштабная схема не может дрейфовать за оболочку
данных ни на каком горизонте.
-/

namespace Hagi.Model.LookaheadTrajectory

open Hagi.Model.ModelSoup

/-- Якорная траектория Lookahead по быстрым итератам x. -/
noncomputable def anchorSeq (α : ℝ) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | n + 1 => Hagi.Optimization.Lookahead.slowStep (anchorSeq α x n) (x (n + 1)) α

/-- ЯКОРНАЯ ТРАЕКТОРИЯ = EMA: slowStep-рекурсия совпадает с
EMA-рекурсией при β = 1 − α (тождество определений). -/
theorem anchor_eq_ema (α : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    anchorSeq α x n = ema (1 - α) x n := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [anchorSeq, ih]
      have h1 : Hagi.Optimization.Lookahead.slowStep
          (ema (1 - α) x m) (x (m + 1)) α
          = (1 - α) * ema (1 - α) x m + α * x (m + 1) := by
        unfold Hagi.Optimization.Lookahead.slowStep; ring
      have h2 : ema (1 - α) x (m + 1)
          = (1 - α) * ema (1 - α) x m + α * x (m + 1) := by
        simp only [ema]
        ring
      rw [h1, h2]

/-- СТАБИЛЬНОСТЬ ЯКОРНОЙ ТРАЕКТОРИИ: при α ∈ [0,1], старте
и всех быстрых итератах в [lo,hi] — вся последовательность
якорей в [lo,hi] (реюз ema_invariant; Lookahead не может
дрейфовать за оболочку данных). -/
theorem anchor_stable (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (x : ℕ → ℝ) (lo hi : ℝ) (hx : ∀ t, lo ≤ x t ∧ x t ≤ hi) :
    ∀ n, lo ≤ anchorSeq α x n ∧ anchorSeq α x n ≤ hi := by
  intro n
  rw [anchor_eq_ema]
  have hβ : 0 ≤ 1 - α := by linarith
  have hβ1 : 1 - α ≤ 1 := by linarith
  exact ema_invariant (1 - α) hβ hβ1 x lo hi hx n

end Hagi.Model.LookaheadTrajectory
