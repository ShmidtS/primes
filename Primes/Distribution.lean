import Mathlib
import Primes.Basic
import Primes.GapFrequency

namespace PrimeGaps

noncomputable section

open Filter

/-- Средний масштаб простого промежутка около `x`: эвристически `log x`. -/
def meanPrimeGapScale (x : Nat) : ℝ := Real.log (x : ℝ)

/-- GOE Wigner surmise для нормированных промежутков. -/
def wignerGOESurmise (t : ℝ) : ℝ :=
  (Real.pi / 2) * t * Real.exp (-(Real.pi / 4) * t ^ 2)

/-- Масштабированная точечная плотность промежутков. -/
def scaledPrimeGapDensity (g x : Nat) : ℝ :=
  meanPrimeGapScale x * primeGapRelativeFrequency g x

/-- Средний масштаб положителен для `x > 1` (log x > 0 при x > 1). -/
theorem meanPrimeGapScale_pos {x : Nat} (hx : 1 < x) :
    0 < meanPrimeGapScale x :=
  Real.log_pos (by exact_mod_cast hx)

/-- Wigner GOE surmise неотрицательна при `t ≥ 0`. -/
theorem wignerGOESurmise_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ wignerGOESurmise t := by
  unfold wignerGOESurmise; positivity

/-- Wigner GOE surmise равна нулю при `t = 0`. -/
theorem wignerGOESurmise_zero : wignerGOESurmise 0 = 0 := by
  simp [wignerGOESurmise]

/-- Wigner GOE surmise строго положительна при `t > 0`. -/
theorem wignerGOESurmise_pos {t : ℝ} (ht : 0 < t) :
    0 < wignerGOESurmise t := by
  unfold wignerGOESurmise
  exact mul_pos (mul_pos (by positivity) ht) (Real.exp_pos _)

/-- Wigner GOE surmise — нечётная функция: `p(-t) = -p(t)`. -/
theorem wignerGOESurmise_odd (t : ℝ) :
    wignerGOESurmise (-t) = -wignerGOESurmise t := by
  unfold wignerGOESurmise
  rw [show (-t) ^ 2 = t ^ 2 by ring, show Real.pi / 2 * (-t) = -(Real.pi / 2 * t) by ring]
  ring

end
end PrimeGaps
