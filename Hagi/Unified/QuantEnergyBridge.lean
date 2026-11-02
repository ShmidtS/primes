import Hagi.Energy.GridVector

/-!
# Аналитический мост: квантование → энергия

Векторный контракт решётчатого квантования соединяется
с энергией через ЯВНУЮ липшицевость по евклидовой норме
(аналитическое условие вместо эмпирической
предпосылки): при константе L оценка энергии после
квантования — полушаг на корень из размера носителя,
умноженный на L.
-/

namespace Hagi.Unified.QuantEnergyBridge

open Hagi.Energy

variable {k : Type*} [Fintype k]

/-- ГЛАВНЫЙ МОСТ: при явной липшицевости энергии по
евклидовой норме изменение энергии после векторного
решётчатого квантования ограничено произведением
константы, полушага и корня из числа координат. -/
theorem gridQ_energy_bound (Δ : ℝ) (hΔ : 0 < Δ)
    (w : k → ℝ)
    (E : (k → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ u v : k → ℝ,
      |E u - E v| ≤ L * Real.sqrt (∑ i, (u i - v i) ^ 2)) :
    |E (gridQVec Δ hΔ w) - E w|
      ≤ L * Real.sqrt ((Fintype.card k : ℝ)) * (Δ / 2) := by
  have hnq : ∑ i, (gridQVec Δ hΔ w i - w i) ^ 2
      ≤ (Fintype.card k : ℝ) * (Δ / 2) ^ 2 := by
    have h := gridQVec_norm_sq Δ hΔ w
    have hsymm : ∑ i, (gridQVec Δ hΔ w i - w i) ^ 2
        = ∑ i, (w i - gridQVec Δ hΔ w i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [hsymm]
    exact h
  have hLip := hlip (gridQVec Δ hΔ w) w
  have hsqrt : Real.sqrt ((Fintype.card k : ℝ) * (Δ / 2) ^ 2)
      = Real.sqrt ((Fintype.card k : ℝ)) * (Δ / 2) := by
    have habs : Real.sqrt ((Δ / 2) ^ 2) = Δ / 2 := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg (by positivity)]
    rw [Real.sqrt_mul (by positivity)]
    rw [habs]
  have hmono : Real.sqrt (∑ i, (gridQVec Δ hΔ w i - w i) ^ 2)
      ≤ Real.sqrt ((Fintype.card k : ℝ) * (Δ / 2) ^ 2) :=
    Real.sqrt_le_sqrt hnq
  have hfin : |E (gridQVec Δ hΔ w) - E w|
      ≤ L * Real.sqrt ((Fintype.card k : ℝ)) * (Δ / 2) := by
    calc |E (gridQVec Δ hΔ w) - E w|
        ≤ L * Real.sqrt
            (∑ i, (gridQVec Δ hΔ w i - w i) ^ 2) := hLip
      _ ≤ L * Real.sqrt
          ((Fintype.card k : ℝ) * (Δ / 2) ^ 2) :=
            mul_le_mul_of_nonneg_left hmono hL
      _ = L * Real.sqrt ((Fintype.card k : ℝ)) * (Δ / 2) := by
            rw [hsqrt]
            ring
  exact hfin

end Hagi.Unified.QuantEnergyBridge
