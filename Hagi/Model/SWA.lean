import Mathlib
import Hagi.Model.Perceiver

/-!
# Sliding Window Attention (источник №56: Jiang et al.,
# "Mistral 7B", arXiv 2310.06825)

Идея: каждый токен посещает только окно из w предыдущих
(и себя): стоимость внимания ~ n·(2w+1) вместо n². При
2w+1 < n — строгая экономия, линейная по длине окна;
монотонность: уменьшение окна строго уменьшает стоимость.
-/

namespace Hagi.Model.SWA

/-- Полная стоимость dense self-attention: n² пар. -/
def denseAttnCost (n : ℕ) : ℕ := n * n

/-- Стоимость sliding-window: каждый токен ≤ (2w+1) пар. -/
def swaCost (n w : ℕ) : ℕ := n * (2 * w + 1)

/-- ИСТОЧНИК №56, УРОВЕНЬ 1: при окне меньше входа
(2w + 1 < n) SWA строго дешевле dense self-attention. -/
theorem swa_cost_lt (n w : ℕ) (h : 2 * w + 1 < n) :
    swaCost n w < denseAttnCost n := by
  unfold swaCost denseAttnCost
  rw [Nat.mul_comm n (2 * w + 1), Nat.mul_comm n n]
  exact (Nat.mul_lt_mul_right
    (Nat.pos_of_ne_zero (by omega))).mpr h

/-- УРОВЕНЬ 1b: отношение стоимостей < 1 (нормированная
форма экономии). -/
theorem swa_cost_ratio_lt (n w : ℕ) (h : 2 * w + 1 < n)
    (hn : 1 ≤ n) :
    (swaCost n w : ℝ) / (denseAttnCost n : ℝ) < 1 := by
  have hlt := swa_cost_lt n w h
  have hpos : (0:ℝ) < (denseAttnCost n : ℝ) := by
    unfold denseAttnCost
    norm_num
    omega
  exact (div_lt_one hpos).mpr (by exact_mod_cast hlt)

/-- УРОВЕНЬ 2: МОНОТОННОСТЬ ПО ОКНУ — уменьшение окна
СТРОГО уменьшает стоимость: w' < w → SWA(w') < SWA(w).
Роутинг вычислений окном управляет стоимостью монотонно. -/
theorem swa_cost_mono (n w w' : ℕ) (hn : 1 ≤ n)
    (hw' : w' < w) :
    swaCost n w' < swaCost n w := by
  unfold swaCost
  have h1 : 2 * w' + 1 < 2 * w + 1 := by omega
  rw [Nat.mul_comm n (2 * w' + 1), Nat.mul_comm n (2 * w + 1)]
  exact (Nat.mul_lt_mul_right
    (Nat.pos_of_ne_zero (by omega))).mpr h1

end Hagi.Model.SWA
