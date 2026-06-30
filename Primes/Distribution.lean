import Mathlib
import Primes.Basic
import Primes.GapFrequency

namespace PrimeGaps

/-! ## Distribution: bridge between computable and analytic

This module connects computable gap enumeration with analytic frequency formulas.
-/

noncomputable section

open Filter

/-- Средний масштаб простого промежутка около `x`: эвристически `log x`. -/
def meanPrimeGapScale (x : Nat) : ℝ :=
  Real.log (x : ℝ)

/-- GOE Wigner surmise для нормированных промежутков. -/
def wignerGOESurmise (t : ℝ) : ℝ :=
  (Real.pi / 2) * t * Real.exp (-(Real.pi / 4) * t ^ 2)

/-- Масштабированная точечная плотность промежутков. -/
def scaledPrimeGapDensity (g x : Nat) : ℝ :=
  meanPrimeGapScale x * primeGapRelativeFrequency g x

/-! ### Scaling theorems -/

/-- Средний масштаб положителен для `x > 1` (log x > 0 при x > 1). -/
theorem meanPrimeGapScale_pos {x : Nat} (hx : 1 < x) :
    0 < meanPrimeGapScale x := by
  unfold meanPrimeGapScale
  exact Real.log_pos (by exact_mod_cast hx)

/-- Средний масштаб неотрицателен для `x ≥ 1` (log x ≥ 0 при x ≥ 1). -/
theorem meanPrimeGapScale_nonneg {x : Nat} (hx : 1 ≤ x) :
    0 ≤ meanPrimeGapScale x := by
  unfold meanPrimeGapScale
  exact Real.log_nonneg (by exact_mod_cast hx)

/-- `meanPrimeGapScale` монотонна: `x ≤ y → log x ≤ log y` (для `x ≥ 1`). -/
theorem meanPrimeGapScale_monotone {x y : Nat} (hx : 1 ≤ x) (hxy : x ≤ y) :
    meanPrimeGapScale x ≤ meanPrimeGapScale y := by
  unfold meanPrimeGapScale
  exact Real.log_le_log (by exact_mod_cast hx) (by exact_mod_cast hxy)

/-! ### Wigner GOE surmise theorems -/

/-- Wigner GOE surmise неотрицательна при `t ≥ 0`. -/
theorem wignerGOESurmise_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ wignerGOESurmise t := by
  unfold wignerGOESurmise
  have h1 : 0 ≤ Real.pi / 2 := by positivity
  have h2 : 0 ≤ Real.exp (-(Real.pi / 4) * t ^ 2) := Real.exp_nonneg _
  exact mul_nonneg (mul_nonneg h1 ht) h2

/-- Wigner GOE surmise равна нулю при `t = 0`. -/
theorem wignerGOESurmise_zero : wignerGOESurmise 0 = 0 := by
  unfold wignerGOESurmise
  simp

/-- Wigner GOE surmise строго положительна при `t > 0`. -/
theorem wignerGOESurmise_pos {t : ℝ} (ht : 0 < t) :
    0 < wignerGOESurmise t := by
  unfold wignerGOESurmise
  have h1 : 0 < Real.pi / 2 * t := by positivity
  have h2 : 0 < Real.exp (-(Real.pi / 4) * t ^ 2) := Real.exp_pos _
  exact mul_pos h1 h2

/-- Wigner GOE surmise — нечётная функция: `p(-t) = -p(t)`. -/
theorem wignerGOESurmise_odd (t : ℝ) :
    wignerGOESurmise (-t) = -wignerGOESurmise t := by
  unfold wignerGOESurmise
  have h1 : (-t) ^ 2 = t ^ 2 := by ring
  rw [h1, show Real.pi / 2 * (-t) = -(Real.pi / 2 * t) by ring]
  ring

/-! ### Density decomposition -/

/-- Масштабированная плотность разлагается в произведение масштаба и относительной частоты. -/
theorem scaledPrimeGapDensity_eq (g x : Nat) :
    scaledPrimeGapDensity g x =
      meanPrimeGapScale x * primeGapRelativeFrequency g x := by
  rfl

/-- Масштабированная плотность равна нулю, когда нет простых `≤ x`. -/
theorem scaledPrimeGapDensity_zero_of_no_primes (g x : Nat)
    (hx : primeCountingExact x = 0) :
    scaledPrimeGapDensity g x = 0 := by
  unfold scaledPrimeGapDensity primeGapRelativeFrequency
  simp [hx, meanPrimeGapScale]

end

end PrimeGaps
