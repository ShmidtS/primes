import Mathlib
import Hagi.Model.SWA
import Hagi.Model.MoD

/-!
# CostComposition — синтез семейства экономии

Синтез-шаг (такт №199): ГИБРИДНАЯ архитектура — стек из L
MoD-слоёв (top-k токенов), где каждый отобранный токен
посещает только sliding window (2w+1), против dense-стека
L слоёв full attention (n²). Экономии ПЕРЕМНОЖАЮТСЯ:
k/n по отбору × (2w+1)/n по окну; суммарная стоимость
L·k·(2w+1) строго меньше L·n².
-/

namespace Hagi.Unified.CostComposition

open Hagi.Model.SWA Hagi.Model.MoD

/-- Стоимость гибрида: L MoD-слоёв × k токенов × окно. -/
def hybridCost (L k w : ℕ) : ℕ := L * k * (2 * w + 1)

/-- Стоимость dense-стека: L слоёв × n². -/
def denseCost (L n : ℕ) : ℕ := L * n * n

/-- СИНТЕЗ: гибрид (MoD отбор × SWA окно × глубина L)
строго дешевле dense-стека при k < n, 2w+1 < n, L ≥ 1.
Три механизма экономии источников №55/№56 складываются
в одну цепочку. -/
theorem hybrid_cost_lt (L n k w : ℕ) (hL : 1 ≤ L)
    (hk : k < n) (hw : 2 * w + 1 < n) :
    hybridCost L k w < denseCost L n := by
  unfold hybridCost denseCost
  -- L·k·(2w+1) < L·n·(2w+1) < L·n·n
  have hkl : k * L < n * L :=
    Nat.mul_lt_mul_of_lt_of_le hk (le_refl L)
      (Nat.pos_of_ne_zero (by omega))
  have ek : L * k < L * n := by
    rwa [Nat.mul_comm k L, Nat.mul_comm n L] at hkl
  have hAw : L * k * w ≤ L * n * w := by
    have hA := Nat.mul_le_mul_left w (le_of_lt ek)
    rwa [Nat.mul_comm w (L * k), Nat.mul_comm w (L * n)] at hA
  have h1 : L * k * (2 * w + 1) < L * n * (2 * w + 1) := by
    have e : ∀ x : ℕ, x * (2 * w + 1)
        = x * w + x * w + x := fun x => by ring
    rw [e (L * k), e (L * n)]
    omega
  have h2 : L * n * (2 * w + 1) ≤ L * n * n := by
    have hle : 2 * w + 1 ≤ n := by omega
    exact Nat.mul_le_mul_left _ hle
  exact lt_of_lt_of_le h1 h2

/-- СИНТЕЗ, НОРМИРОВАННАЯ ФОРМА: относительная стоимость
гибрида ≤ (k/n)·((2w+1)/n) < 1 — произведение факторов
экономии. -/
theorem hybrid_ratio_le (L n k w : ℕ) (hL : 1 ≤ L)
    (_hk : k < n) (hw : 2 * w + 1 < n) :
    (hybridCost L k w : ℝ) / (denseCost L n : ℝ)
      ≤ (k:ℝ) / n * ((2*w+1:ℝ) / n) := by
  have hn : (0:ℝ) < (n:ℝ) := by
    exact_mod_cast (by omega : 1 ≤ n)
  have hL0 : (0:ℝ) < (L:ℝ) := by
    exact_mod_cast (by omega : 1 ≤ L)
  have e1 : (hybridCost L k w : ℝ) / (denseCost L n : ℝ)
      = (k:ℝ) * (2*w+1:ℝ) / ((n:ℝ) * (n:ℝ)) := by
    unfold hybridCost denseCost
    push_cast
    field_simp
  have e2 : (k:ℝ) / (n:ℝ) * ((2*w+1:ℝ) / (n:ℝ))
      = (k:ℝ) * (2*w+1:ℝ) / ((n:ℝ) * (n:ℝ)) := by
    field_simp
  rw [e1, e2]

end Hagi.Unified.CostComposition
