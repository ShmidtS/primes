import Mathlib

/-!
# Mixture-of-Depths (источник №55: Raposo et al.,
# "Mixture-of-Depths: Dynamically allocating compute in
# transformer LMs", arXiv 2404.02258)

Идея: каждый слой обрабатывает только top-k из n токенов
(остальные — residual-обход). Стоимость слоя падает с n до
k; на L слоях экономия ЛИНЕЙНА по глубине. Формализуем:
строгую экономию слоя и её накопление по глубине.
-/

namespace Hagi.Model.MoD

/-- Стоимость dense-слоя: все n токенов. -/
def denseLayerCost (n d : ℕ) : ℕ := n * d

/-- Стоимость MoD-слоя: k отобранных токенов. -/
def modLayerCost (k d : ℕ) : ℕ := k * d

/-- Полная стоимость L dense-слоёв. -/
def denseStackCost (L n d : ℕ) : ℕ := L * denseLayerCost n d

/-- Полная стоимость L MoD-слоёв. -/
def modStackCost (L k d : ℕ) : ℕ := L * modLayerCost k d

/-- ИСТОЧНИК №55, УРОВЕНЬ 1: MoD-слой строго дешевле dense
при k < n и d ≥ 1. -/
theorem mod_layer_cost_lt (n k d : ℕ) (hk : k < n)
    (hd : 1 ≤ d) :
    modLayerCost k d < denseLayerCost n d := by
  unfold modLayerCost denseLayerCost
  exact Nat.mul_lt_mul_of_lt_of_le hk (le_refl d)
    (by omega)

/-- УРОВЕНЬ 2: ГЛУБИНА УМНОЖАЕТ ЭКОНОМИЮ — на стеке из L ≥ 1
слоёв экономия MoD-стека равна L-кратной послойной экономии
и строго положительна при k < n, d ≥ 1. -/
theorem mod_stack_saving (L n k d : ℕ) (hL : 1 ≤ L)
    (hk : k < n) (hd : 1 ≤ d) :
    0 < denseStackCost L n d - modStackCost L k d
      ∧ denseStackCost L n d - modStackCost L k d
        = L * (denseLayerCost n d - modLayerCost k d) := by
  have hlayer := mod_layer_cost_lt n k d hk hd
  unfold denseLayerCost modLayerCost at hlayer
  unfold denseStackCost modStackCost denseLayerCost
    modLayerCost
  have hnd : 0 < n * d - k * d := by omega
  have hdistr : L * (n * d - k * d)
      = L * (n * d) - L * (k * d) := Nat.mul_sub L _ _
  have hpos : 0 < L * (n * d - k * d) :=
    Nat.mul_pos hL hnd
  constructor
  · omega
  · omega

end Hagi.Model.MoD
