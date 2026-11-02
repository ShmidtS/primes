import Mathlib
import Hagi.Unified.DescentCore

/-!
# DescentCoreDiag: второй реальный инстанс
Objective — ВЗВЕШЕННАЯ квадратичная цель с нетривиальной
константой гладкости L = max aᵢ.

E(w) = ½·Σ aᵢ(wᵢ − yᵢ)², aᵢ ≥ 0 (диагональная метрика;
частный случай линейной регрессии с диагональным
гессианом). В отличие от DescentCoreQuad (L = 1):
- градиент: aᵢ(wᵢ − yᵢ);
- L-гладкость: L = maxᵢ aᵢ — ДОКАЗЫВАЕТСЯ из точного
  тождества E(w+d) = E(w) + ⟨g, d⟩ + ½Σaᵢdᵢ² ≤
  E(w) + ⟨g, d⟩ + (L/2)‖d‖² (поточечное aᵢ ≤ L);
- контракт aligned/descent_drop наследуется из DescentCore
  без изменений — проверка, что контракт работает при
  произвольном L, а не только L = 1.
-/

namespace Hagi.Unified.DescentCoreDiag

open Hagi.Unified.DescentCore

variable {k : Type*} [Fintype k] [Nonempty k]

/-- Взвешенная квадратичная цель (a ≥ 0 поточечно). -/
noncomputable def diagE (a y w : k → ℝ) : ℝ :=
  (∑ i, a i * (w i - y i)^2) / 2

/-- Градиент взвешенной цели. -/
def diagGrad (a y w : k → ℝ) : k → ℝ :=
  fun i => a i * (w i - y i)

/-- Точное тождество разложения для взвешенной цели. -/
theorem diag_descent_eq (a y x d : k → ℝ) :
    diagE a y (x + d) = diagE a y x
      + inprod (diagGrad a y x) d
      + (∑ i, a i * (d i)^2) / 2 := by
  have hexp : ∀ i, a i * ((x + d) i - y i)^2
      = a i * (x i - y i)^2
        + 2 * (a i * (x i - y i)) * d i
        + a i * (d i)^2 := by
    intro i
    have h : (x + d) i - y i = (x i - y i) + d i := by
      simp only [Pi.add_apply]; ring
    rw [h]
    ring
  have hsum : ∑ i, a i * ((x + d) i - y i)^2
      = ∑ i, a i * (x i - y i)^2
        + ∑ i, 2 * (a i * (x i - y i)) * d i
        + ∑ i, a i * (d i)^2 := by
    rw [Finset.sum_congr rfl (fun i _ => hexp i),
      Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h2 : ∑ i, 2 * (a i * (x i - y i)) * d i
      = 2 * ∑ i, (a i * (x i - y i)) * d i := by
    rw [show (2 * ∑ i, (a i * (x i - y i)) * d i)
      = ∑ i, 2 * ((a i * (x i - y i)) * d i) from
      Finset.mul_sum _ _ 2]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  unfold diagE diagGrad inprod
  rw [hsum, h2]
  field_simp

/-- ИНСТАНС OBJECTIVE при ограниченных весах: L-гладкость
ВЫВЕДЕНА (поточечное aᵢ ≤ L + точное тождество). -/
theorem diag_descent_le (a y x d : k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (L : ℝ) (hL : 0 < L)
    (hLmax : ∀ i, a i ≤ L) :
    diagE a y (x + d) ≤ diagE a y x
      + inprod (diagGrad a y x) d
      + L / 2 * nrm2 d := by
  have hsq : ∀ i, a i * (d i)^2 ≤ L * (d i)^2 :=
    fun i => mul_le_mul_of_nonneg_right (hLmax i)
      (sq_nonneg _)
  have hsum : ∑ i, a i * (d i)^2 ≤ L * nrm2 d := by
    have h1 : ∑ i, a i * (d i)^2 ≤ ∑ i, L * (d i)^2 :=
      Finset.sum_le_sum (fun i _ => hsq i)
    have h2 : ∑ i, L * (d i)^2 = L * nrm2 d := by
      rw [show nrm2 d = ∑ i, (d i)^2 from rfl]
      exact (Finset.mul_sum _ _ L).symm
    exact h1.trans_eq h2
  have htol : (∑ i, a i * (d i)^2) / 2 ≤ L / 2 * nrm2 d := by
    have : (∑ i, a i * (d i)^2) / 2 = (1/2) * (∑ i, a i * (d i)^2) := by ring
    have h2 : L / 2 * nrm2 d = (1/2) * (L * nrm2 d) := by ring
    rw [this, h2]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  rw [diag_descent_eq a y x d]
  linarith

/-- Максимум кривизны. -/
def cMax (c : k → ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty c

theorem cMax_ge (c : k → ℝ) (i : k) : c i ≤ cMax c := by
  apply Finset.le_sup'
  exact Finset.mem_univ i

/-- Контрактный инстанс: анизотропная цель с L = максимум
кривизны. -/
noncomputable def diagObjective (c a : k → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hcp : ∃ j, 0 < c j) : Objective k where
  f := diagE c a
  grad := diagGrad c a
  L := cMax c
  hL := by
    obtain ⟨jstar, hjp⟩ := hcp
    have h1 : c jstar ≤ cMax c := by
      apply Finset.le_sup'
      exact Finset.mem_univ jstar
    exact lt_of_lt_of_le hjp h1
  descentLemma := by
    intro x d
    have heq := diag_descent_eq c a x d
    have hterm : ∀ i, c i * (d i) ^ 2
        ≤ cMax c * (d i) ^ 2 :=
      fun i => mul_le_mul_of_nonneg_right (cMax_ge c i)
        (sq_nonneg _)
    have hsum : ∑ i, c i * (d i) ^ 2
        ≤ cMax c * ∑ i, (d i) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hterm i
    have hhalf : (∑ i, c i * (d i) ^ 2) / 2
        ≤ (cMax c * ∑ i, (d i) ^ 2) / 2 := by
      linarith [hsum]
    have hconv : (cMax c * ∑ i, (d i) ^ 2) / 2
        = cMax c / 2 * nrm2 d := by
      unfold nrm2
      ring
    show diagE c a (x + d)
      ≤ diagE c a x + inprod (diagGrad c a x) d
        + cMax c / 2 * nrm2 d
    rw [heq]
    linarith

end Hagi.Unified.DescentCoreDiag
