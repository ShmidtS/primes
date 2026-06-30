import Mathlib
import Primes.Basic
import Primes.GapFrequency
import Primes.Distribution

namespace PrimeGaps

noncomputable section

open Filter

/-- Детерминантная модель частот простых промежутков. Открытая проблема;
мотивирована GUE-гипотезой Монтгомери--Одлыжко (1973). -/
def DeterminantalPrimeGapConjecture
    (kernel : (x g m : Nat) → Fin m → Fin m → ℝ) (weight : Nat → ℝ) : Prop :=
  ∀ g : Nat,
    Tendsto (fun x : Nat =>
      primeGapRelativeFrequency g x -
        (Finset.range (g + 1)).sum fun m => weight m * Matrix.det (kernel x g m)) atTop (nhds 0)

/-- Одномерное ядро, тривиально кодирующее точную частоту. -/
def exactOneByOneGapKernel (g x : Nat) : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => primeGapRelativeFrequency g x

/-- Детерминант точного `1 × 1` ядра равен относительной частоте. -/
theorem det_exactOneByOneGapKernel (g x : Nat) :
    Matrix.det (exactOneByOneGapKernel g x) = primeGapRelativeFrequency g x := by
  simp [exactOneByOneGapKernel]

/-- Гипотеза GOE-Вигнера для простых промежутков. Открытая проблема. -/
def GOEWignerPrimeGapConjecture (C₂ : ℝ) : Prop :=
  ∀ (g : Nat → Nat) (τ : ℝ),
    Tendsto (fun x : Nat => (g x : ℝ) / meanPrimeGapScale x) atTop (nhds τ) →
      Tendsto (fun x : Nat => scaledPrimeGapDensity (g x) x) atTop
        (nhds (C₂ * wignerGOESurmise τ))

end
end PrimeGaps
