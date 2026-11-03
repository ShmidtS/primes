/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Hagi.Optimization.Lookahead
import Hagi.Model.ModelSoup

/-!
# Спекулятивное декодирование (объединённое)

LookaheadTrajectory + Speculative. Имена деклараций
сохранены.
-/

/-!
# LookaheadTrajectory — сертификация якорной траектории
(связка №75 × ModelSoup/EMA, )

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

/-!
# Speculative Decoding: ожидаемый выигрыш (источник №27)

Источник №27: Chen et al., "Accelerating Large Language Model
Decoding with Speculative Sampling" (arXiv 2302.01318).
Драфт-модель генерирует k токенов, цель проверяет их за один
параллельный проход; α — вероятность приёмки одного токена.

Формализованное ядро (строгое):
- accept_chain_prob: вероятность принятия всех k драфт-
  токенов подряд = α^k (геометрическая цепочка);
- speculative_expected_tokens: ожидаемое число принятых
  токенов за цикл = (1 - α^{k+1})/(1 - α) при α ≠ 1
  (геометрическая серия);
- speculative_win: чистый выигрыш против k+1 последовательных
  полных проходов строго положителен при α > 0, k ≥ 1 —
  амортизация цели по k+1 токенам за один проход.
-/

namespace Hagi.Model.Speculative

/-- Вероятность принять всю цепочку из k драфт-токенов. -/
theorem accept_chain_prob (α : ℝ) (k : ℕ) :
    (∏ _i ∈ Finset.range k, α) = α ^ k := by
  simp

/-- Ожидаемое число принятых токенов за один цикл:
геометрическая серия E = ∑_{i=0}^{k} α^i. -/
theorem speculative_expected_tokens (α : ℝ) (hα : α ≠ 1)
    (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), α ^ i = (1 - α ^ (k + 1)) / (1 - α) := by
  have hden : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  induction k with
  | zero => rw [Finset.sum_range_one, pow_one]; field_simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hpow : α ^ (k + 1 + 1) = α ^ (k + 1) * α := by ring
    field_simp
    ring

/-- Чистый выигрыш спекулятивного цикла: (k+1) полных
проходов заменяются на один; при α > 0 и k ≥ 1 ожидаемое
число токенов за проход СТРОГО превышает 1 (порог
безубыточности одной цели = 1 токен/проход). -/
theorem speculative_win (α : ℝ) (hpos : 0 < α)
    (k : ℕ) (hk : 1 ≤ k) :
    1 < ∑ i ∈ Finset.range (k + 1), α ^ i := by
  have hsub : Finset.range 2 ⊆ Finset.range (k + 1) := by
    intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  have hkey : Finset.range (k + 1)
      = Finset.range 2 ∪ (Finset.range (k + 1) \ Finset.range 2) := by
    ext i; simp only [Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_range]; omega
  rw [hkey, Finset.sum_union (by simp [Finset.disjoint_iff_inter_eq_empty])]
  have hbase : ∑ i ∈ Finset.range 2, α ^ i = 1 + α := by simp; ring
  have hnn : 0 ≤ ∑ i ∈ Finset.range (k + 1) \ Finset.range 2, α ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg hpos.le i)
  rw [hbase]
  linarith

end Hagi.Model.Speculative
