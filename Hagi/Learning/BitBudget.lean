import Mathlib.Tactic
import Hagi.Learning.TernaryPert

set_option linter.style.header false

/-!
# BitBudget — битовая граница ошибки тернарного слоя (цикл 18)

Связка размера и качества (цель HAGI: максимум качества при
минимуме объёма): тернарный слой m×r занимает
B = m·r·log₂(3) бит; его выходное возмущение (цикл 11)
ограничено √(m·r)/2·‖x‖. Композиция даёт трейдофф напрямую
в битах: err ≤ √(B / log₂3) / 2 · ‖x‖ — качество как функция
объёма.
-/

open Finset

namespace Hagi.Learning.BitBudget

open Hagi.Learning.TernaryPert

variable {m r : ℕ}

/-- Биты на тернарный вес: log₂ 3. -/
noncomputable def bitsPerTrit : ℝ := Real.log 3 / Real.log 2

/-- Общий объём тернарного слоя в битах: m·r·log₂3. -/
noncomputable def layerBits (m r : ℕ) : ℝ :=
  (m : ℝ) * (r : ℝ) * bitsPerTrit

theorem bitsPerTrit_pos : (0:ℝ) < bitsPerTrit := by
  unfold bitsPerTrit
  refine div_pos (Real.log_pos (by norm_num : (1:ℝ) < 3)) ?_
  exact Real.log_pos (by norm_num : (1:ℝ) < 2)

/-- ГЛАВНАЯ ГРАНИЦА (размер ↔ качество): для тернарного слоя
объёма B = layerBits m r бит и поэлементной ошибки
квантования ≤ 1/2:
  ‖(Q(R)−R)x‖ ≤ √(B / log₂3)/2 · ‖x‖.
-/
theorem ternary_bit_error_bound (R QR : Matrix (Fin m) (Fin r) ℝ)
    (x : Fin r → ℝ)
    (hq : ∀ i j, abs (QR i j - R i j) ≤ 1/2) :
    outNorm (fun i => dotProduct (rowVec (QR - R) i) x)
      ≤ (Real.sqrt (layerBits m r / bitsPerTrit) / 2) * eunorm x := by
  have h := ternary_layer_pert R QR x hq
  have hmr : layerBits m r / bitsPerTrit = ((m : ℝ) * (r : ℝ)) := by
    unfold layerBits
    have hb := bitsPerTrit_pos.ne'
    field_simp
  rw [hmr]
  have hpos : (0:ℝ) ≤ (m : ℝ) * (r : ℝ) :=
    mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg r)
  have heq : Real.sqrt ((m : ℝ) * (r : ℝ) * (1/2)^2)
      = Real.sqrt ((m : ℝ) * (r : ℝ)) / 2 := by
    have hq : ((1:ℝ)/2)^2 = ((1:ℝ)/4) := by norm_num
    rw [hq]
    have hsm := Real.sqrt_mul (x := (m : ℝ) * (r : ℝ))
      (y := ((1:ℝ)/4)) hpos
    rw [hsm]
    have hqrt : Real.sqrt ((1:ℝ)/4) = 1/2 := by
      rw [Real.sqrt_div (by norm_num)]
      norm_num
    rw [hqrt, mul_one_div]
  -- финальная композиция: trans-цепь
  have h2 : outNorm (fun i => dotProduct (rowVec (QR - R) i) x)
      ≤ (Real.sqrt ((m : ℝ) * (r : ℝ)) / 2) * eunorm x :=
    le_trans h (mul_le_mul_of_nonneg_right (le_of_eq heq)
      (Real.sqrt_nonneg _))
  have hgoal : (Real.sqrt (layerBits m r / bitsPerTrit) / 2)
      = Real.sqrt ((m : ℝ) * (r : ℝ)) / 2 := by rw [hmr]
  exact h2

end Hagi.Learning.BitBudget
