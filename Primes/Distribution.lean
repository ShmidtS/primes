import Mathlib
import Primes.Basic
import Primes.GapFrequency

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

noncomputable section

open Filter

/-! ## Wigner GOE surmise: definitions and RMT conjectures

The Wigner GOE surmise `p(t) = (π/2) t exp(-πt²/4)` is the universal
gap distribution for random matrix ensembles. We define it and state
conjectures connecting it to prime gap statistics.
-/

/-- Average scale of prime gaps near `x`: heuristically `log x`. -/
def meanPrimeGapScale (x : Nat) : ℝ := Real.log (x : ℝ)

/-- GOE Wigner surmise for normalized gaps: `p(t) = (π/2) t exp(-πt²/4)`. -/
def wignerGOESurmise (t : ℝ) : ℝ :=
  (Real.pi / 2) * t * Real.exp (-(Real.pi / 4) * t ^ 2)

/-- Scaled point density of gaps: `log(x) · F(g,x)/π(x)`. -/
def scaledPrimeGapDensity (g x : Nat) : ℝ :=
  meanPrimeGapScale x * primeGapRelativeFrequency g x

/-- GOE-Wigner conjecture: scaled prime gap density converges to `C₂ · p(τ)`. -/
def GOEWignerPrimeGapConjecture (C₂ : ℝ) : Prop :=
  ∀ (g : Nat → Nat) (τ : ℝ),
    Tendsto (fun x : Nat => (g x : ℝ) / meanPrimeGapScale x) atTop (nhds τ) →
      Tendsto (fun x : Nat => scaledPrimeGapDensity (g x) x) atTop
        (nhds (C₂ * wignerGOESurmise τ))

/-- Determinantal model for prime gap frequencies (Montgomery--Odlyzko GUE hypothesis). -/
def DeterminantalPrimeGapConjecture
    (kernel : (x g m : Nat) → Fin m → Fin m → ℝ) (weight : Nat → ℝ) : Prop :=
  ∀ g : Nat,
    Tendsto (fun x : Nat =>
      primeGapRelativeFrequency g x -
        (Finset.range (g + 1)).sum fun m => weight m * Matrix.det (kernel x g m))
      atTop (nhds 0)

end
end PrimeGaps
