import Hagi.Energy.Quantizer

/-!
# Векторный контракт квантования: единая решётка

Покоординатная оценка `gridQ_error` и векторная
`quant_residual_norm` соединяются в один исполняемый
контракт: вектор весов, квантованный покоординатно на
решётку с шагом дельта, имеет квадрат евклидовой
невязки не более числа координат на квадрат полушага.
Никаких гипотез за пределами положительности шага.
-/

namespace Hagi.Energy

open Finset

variable {k : Type*} [Fintype k]

/-- Векторный квантователь: покоординатная решётка. -/
noncomputable def gridQVec (Δ : ℝ) (hΔ : 0 < Δ)
    (w : k → ℝ) : k → ℝ :=
  fun i => gridQ Δ hΔ (w i)

omit [Fintype k] in
/-- Покоординатная невязка в пределах полушага. -/
theorem gridQVec_error (Δ : ℝ) (hΔ : 0 < Δ)
    (w : k → ℝ) (i : k) :
    |w i - gridQVec Δ hΔ w i| ≤ Δ / 2 := by
  have h := gridQ_error Δ hΔ (w i)
  rw [abs_sub_comm]
  exact h

/-- ГЛАВНЫЙ КОНТРАКТ: квадрат евклидовой невязки
векторного квантования не превосходит количества
координат на квадрат полушага — без единой эмпирической
предпосылки. -/
theorem gridQVec_norm_sq (Δ : ℝ) (hΔ : 0 < Δ)
    (w : k → ℝ) :
    (∑ i, (w i - gridQVec Δ hΔ w i) ^ 2)
      ≤ (Fintype.card k : ℝ) * (Δ / 2) ^ 2 := by
  have hres : ∀ i : k, |w i - gridQVec Δ hΔ w i| ≤ Δ / 2 :=
    fun i => gridQVec_error Δ hΔ w i
  have hn : (Fintype.card k : ℝ) = (Fintype.card k : ℝ) := rfl
  -- сводим к Fin-форме quant_residual_norm через произвольный Fintype
  calc (∑ i, (w i - gridQVec Δ hΔ w i) ^ 2)
      ≤ ∑ i, (Δ / 2) ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          have hle := hres i
          rw [abs_le] at hle
          nlinarith [hle.1, hle.2]
    _ = (Fintype.card k : ℝ) * (Δ / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Hagi.Energy
