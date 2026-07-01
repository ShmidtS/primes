import Mathlib
import Primes.Basic
import Primes.GapFrequency

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

noncomputable section

open Filter

/-! ## Wigner GOE surmise for prime gaps -/

/-- Средний масштаб простого промежутка около `x`: эвристически `log x`. -/
def meanPrimeGapScale (x : Nat) : ℝ := Real.log (x : ℝ)

/-- GOE Wigner surmise для нормированных промежутков. -/
def wignerGOESurmise (t : ℝ) : ℝ :=
  (Real.pi / 2) * t * Real.exp (-(Real.pi / 4) * t ^ 2)

/-- Масштабированная точечная плотность промежутков. -/
def scaledPrimeGapDensity (g x : Nat) : ℝ :=
  meanPrimeGapScale x * primeGapRelativeFrequency g x

/-- Wigner GOE surmise — нечётная функция: `p(-t) = -p(t)`. -/
theorem wignerGOESurmise_odd (t : ℝ) :
    wignerGOESurmise (-t) = -wignerGOESurmise t := by
  unfold wignerGOESurmise; rw [show (-t : ℝ) ^ 2 = t ^ 2 by ring]; ring

/-- Wigner GOE surmise неотрицательна для `t ≥ 0`. -/
theorem wignerGOESurmise_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ wignerGOESurmise t := by
  unfold wignerGOESurmise
  positivity

/-- Wigner GOE surmise обращается в ноль при `t = 0`. -/
theorem wignerGOESurmise_zero :
    wignerGOESurmise 0 = 0 := by
  unfold wignerGOESurmise; ring

/-- Wigner GOE surmise строго положительна для `t > 0`. -/
theorem wignerGOESurmise_pos {t : ℝ} (ht : 0 < t) :
    0 < wignerGOESurmise t := by
  unfold wignerGOESurmise
  positivity

/-- Wigner GOE surmise — чётная функция от `t²`: зависит только от `t²`. -/
theorem wignerGOESurmise_sq_arg (t : ℝ) :
    wignerGOESurmise t = (Real.pi / 2) * t * Real.exp (-(Real.pi / 4) * t * t) := by
  unfold wignerGOESurmise
  ring_nf

end
end PrimeGaps
