import Mathlib
import Primes.Basic
import Primes.GapFrequency

set_option linter.style.header false
set_option linter.style.longLine false

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

/-- Wigner GOE surmise — нечётная функция: `p(-t) = -p(t)`. -/
theorem wignerGOESurmise_odd (t : ℝ) :
    wignerGOESurmise (-t) = -wignerGOESurmise t := by
  unfold wignerGOESurmise; rw [show (-t : ℝ) ^ 2 = t ^ 2 by ring]; ring

end
end PrimeGaps
