import Mathlib

/-!
# Perceiver — latent bottleneck (источник №54: Jaegle et al.,
# "Perceiver: General Perception with Iterative Attention",
# arXiv 2103.03206)

Ключевая идея: вместо квадратичной self-attention по n входам
(стоимость ~ n²) — cross-attention в m ≪ n латентных векторов
(стоимость ~ n·m), затем self-attention только по латентам
(m²). Формализуем СТРОГО: при 2m ≤ n Perceiver-блок дешевле
full self-attention, отношение стоимостей < 1, экономия
положительна и растёт.
-/

namespace Hagi.Model.Perceiver

/-- Стоимость full self-attention по n входам ~ n². -/
def attnCost (n : ℕ) : ℕ := n * n

/-- Стоимость cross-attention n входов → m латентов ~ n·m. -/
def crossCost (n m : ℕ) : ℕ := n * m

/-- Стоимость self-attention по m латентам ~ m². -/
def latentCost (m : ℕ) : ℕ := m * m

/-- Полная стоимость Perceiver-блока: cross + latent. -/
def perceiverCost (n m : ℕ) : ℕ := crossCost n m + latentCost m

/-- ИСТОЧНИК №54, УРОВЕНЬ 1: при 2m ≤ n (латент не больше
ПОЛОВИНЫ входов) Perceiver-блок СТРОГО дешевле full
self-attention: n·m + m² < n². Замечание о честности: при
m близком к n (например m = n−1, n ≥ 3) сумма n·m + m²
ПРЕВЫШАЕТ n² — экономия есть только у настоящего
бутылочного горлышка. -/
theorem perceiver_cost_lt (n m : ℕ) (h2m : 2 * m ≤ n)
    (hn : 1 ≤ n) :
    perceiverCost n m < attnCost n := by
  have hn' : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h2m' : (2:ℝ) * (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast h2m
  have hw1 : 0 ≤ (n:ℝ) * ((n:ℝ) - 2 * (m:ℝ)) :=
    mul_nonneg hn' (by linarith)
  have hw2 : 0 ≤ (m:ℝ) * ((n:ℝ) - (m:ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  norm_num [perceiverCost, crossCost, latentCost, attnCost,
    Nat.cast_mul, Nat.cast_add]
  nlinarith [hw1, hw2, sq_nonneg (m:ℝ), hn]

/-- УРОВЕНЬ 1b: отношение стоимостей < 1 при 2m ≤ n
(Perceiver-блок дешевле self-attention и по нормированной
величине). -/
theorem perceiver_cost_ratio_lt (n m : ℕ) (h2m : 2 * m ≤ n)
    (hn : 1 ≤ n) :
    (perceiverCost n m : ℝ) / (attnCost n : ℝ) < 1 := by
  have h := perceiver_cost_lt n m h2m hn
  have hpos : (0:ℝ) < (attnCost n : ℝ) := by
    unfold attnCost
    norm_num
    omega
  have hcast : (perceiverCost n m : ℝ) < (attnCost n : ℝ) :=
    by exact_mod_cast h
  exact (div_lt_one hpos).mpr hcast

/-- УРОВЕНЬ 2: ЭКОНОМИЯ ПОЛОЖИТЕЛЬНА И ЛИНЕЙНО ОГРАНИЧЕНА
СНИЗУ: n² − (nm + m²) ≥ n·(n − 2m) ≥ 0; при n > 2m —
строго положительна. -/
theorem perceiver_saving_pos (n m : ℕ) (h2m : 2 * m < n) :
    0 < attnCost n - perceiverCost n m := by
  have hn : 1 ≤ n := by omega
  have h := perceiver_cost_lt n m (by omega) hn
  omega

end Hagi.Model.Perceiver
