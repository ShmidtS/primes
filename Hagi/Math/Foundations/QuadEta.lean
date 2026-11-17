import Mathlib.Tactic

/-!
# QuadEta — канонические η-теоремы квадратичного шага (слой 0)

Чистая математика над произвольным Fintype-носителем: точное
тождество E(w − η·∇E(w)) = (1−η)²·E(w) и строгий спуск при
0 < η < 2. Градиент — истинный градиент квадратичной функции
потерь E(w) = ½‖w − a‖², никакой постулируемой динамики.
-/

namespace Hagi.Foundations

variable {k : Type*} [Fintype k]

/-- Квадратичная функция потерь: E(w) = ½Σ(w − a)². -/
noncomputable def quadLossAt (a w : k → ℝ) : ℝ :=
  ∑ i, (w i - a i) ^ 2 / 2

/-- Градиент quadLossAt (истинный): w − a. -/
def quadLossGrad (a w : k → ℝ) : k → ℝ := fun i => w i - a i

/-- ТОЧНОЕ тождество η-шага вдоль истинного градиента. -/
theorem quad_eta_identity (a w : k → ℝ) (eta : ℝ) :
    quadLossAt a (fun i => w i - eta * quadLossGrad a w i)
      = (1 - eta) ^ 2 * quadLossAt a w := by
  have hper : ∀ i, (w i - eta * quadLossGrad a w i - a i)
      = (1 - eta) * (w i - a i) := by
    intro i
    unfold quadLossGrad
    ring
  unfold quadLossAt
  rw [Finset.sum_congr rfl (fun i _ => by rw [hper i])]
  have hfac : ∑ i, ((1 - eta) * (w i - a i)) ^ 2 / 2
      = (1 - eta) ^ 2 * ∑ i, (w i - a i) ^ 2 / 2 := by
    simp [mul_pow, mul_div_assoc, Finset.mul_sum]
  rw [hfac]

/-- Строгий спуск при 0 < η < 2 (единственная гипотеза —
измеримый выбор шага). -/
theorem quad_eta_descent (a w : k → ℝ) (eta : ℝ)
    (h0 : 0 < eta) (h2 : eta < 2) (hpos : 0 < quadLossAt a w) :
    quadLossAt a (fun i => w i - eta * quadLossGrad a w i)
      < quadLossAt a w := by
  rw [quad_eta_identity]
  have hlt : (1 - eta) ^ 2 < 1 := by
    have h1 : -1 < 1 - eta := by linarith
    have h2' : 1 - eta < 1 := by linarith
    nlinarith [h1, h2', sq_nonneg (1 - eta)]
  have := mul_lt_mul_of_pos_right hlt hpos
  linarith

end Hagi.Foundations
