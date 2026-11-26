/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.CommitGate

/-!
# ReliefGate — COMMIT-гейт selfdev-цикла по waste-счётчику

COMMIT (selfdev/loop.py:594) требует `W' ≤ ⌊W·(1−r)⌋`, `r = 0.02`; experts —
superset, accuracy = 1. Здесь — что даёт целочисленность порога.

* `reliefOk_zero` — при `W = 0` гейт вырожден: COMMIT без снижения.
* `reliefOk_lt` — при `W > 0`, `r > 0` снижение строго: `W' < W`; доля `r`
  превращается в минимум одну единицу.
* `relief_rounds_le` — k COMMIT-раундов дают `W k + k ≤ W 0`: рост без
  разрушения экспертов конечен по waste, дальше — смена рычага.
-/

namespace Hagi.Unified.ReliefGate

/-- Гейт relief: `W' ≤ ⌊W·(1−r)⌋`; `W` — целочисленный waste-счётчик (selfdev/loop.py:594). -/
def reliefOk (r : ℝ) (W W' : ℕ) : Prop := W' ≤ Nat.floor ((W : ℝ) * (1 - r))
/-- При `W = 0` гейт вырожден: `W' = 0` проходит без снижения. -/
theorem reliefOk_zero (r : ℝ) : reliefOk r 0 0 := by
  have : ((0:ℕ) : ℝ) * (1 - r) = 0 := by ring
  simp [reliefOk]
/-- При `0 < W` и `0 < r` гейт строго: `W' < W`; целочисленность превращает долю `r`
в снижение не меньше одной единицы. -/
theorem reliefOk_lt (r : ℝ) (hr : 0 < r) (W W' : ℕ) (hW : 0 < W) (h : reliefOk r W W') :
    W' < W := by
  have hpos : (0:ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hmul : (W : ℝ) * (1 - r) < (W : ℝ) := by nlinarith
  by_cases hnn : (0:ℝ) ≤ (W : ℝ) * (1 - r)
  · exact Nat.lt_of_le_of_lt h ((Nat.floor_lt hnn).2 hmul)
  · have hz : Nat.floor ((W : ℝ) * (1 - r)) = 0 := Nat.floor_of_nonpos (by linarith)
    unfold reliefOk at h
    omega
/-- k COMMIT-раундов при `W > 0` на каждом: `W k ≤ W 0 − k`; число раундов ≤ W 0. -/
theorem relief_rounds_le (W : ℕ → ℕ) (k : ℕ) (h : ∀ i, i < k → W (i + 1) < W i) :
    W k + k ≤ W 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
      have h2 : W (k + 1) < W k := h k (Nat.lt_succ_self k)
      omega

end Hagi.Unified.ReliefGate
