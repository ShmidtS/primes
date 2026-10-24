import Hagi.Prelude.Info
-- Формализация ядра arXiv 2610.31592v1 (углы сферического симплекса).
open Finset Real

namespace Hagi.Geometry

/-!
Формализация ядра arXiv 2610.31592v1: углы сферического n-симплекса.
Число двугранных углов K(n) = n(n+1)/2; евклидов угол θ(n)=arccos(1/n)
строго возрастает к π/2; сферический эксцесс на угол = π−θ > 0;
границы евклидовой суммы (π/3)·K ≤ S < (π/2)·K при n ≥ 2.
-/

/-- Число двугранных углов n-симплекса: K(n) = n(n+1)/2 —
неупорядоченные пары различных граней из (n+1); упорядоченных
пар вдвое больше (offDiag). -/
theorem dihedral_count (n : ℕ) :
    (Finset.range (n+1)).offDiag.card = n * (n + 1) := by
  rw [Finset.offDiag_card, Finset.card_range]
  have hexp : (n+1)*(n+1) = n*(n+1) + (n+1) := by ring
  omega

/-- Евклидов двугранный угол правильного n-симплекса
θ(x) = arccos(1/x) строго возрастает на (1, ∞). -/
theorem dihedral_angle_strictMono {x y : ℝ} (hx : 1 < x) (hy : 1 < y)
    (hxy : x < y) : Real.arccos (1/x) < Real.arccos (1/y) := by
  have hxy' : 1/y < 1/x := by field_simp; linarith
  have hp1 : (0:ℝ) < 1/y := by positivity
  have hp2 : (0:ℝ) < 1/x := by positivity
  have hy1 : (1:ℝ)/x ≤ 1 := by field_simp; linarith
  exact Real.arccos_lt_arccos (by linarith) hxy' hy1

/-- Евклидов двугранный угол строго меньше π (супремум π
сферического двугранного угла недостижим). -/
theorem dihedral_angle_lt_pi {x : ℝ} (hx : 1 ≤ x) :
    Real.arccos (1/x) < π := by
  have hp : (0:ℝ) < 1/x := by positivity
  exact Real.arccos_lt_pi.mpr (by linarith)

/-- Сферический эксцесс на один угол: π − θ = arccos(−1/x). -/
theorem excess_as_supplement {x : ℝ} (_hx : 1 ≤ x) :
    π - Real.arccos (1/x) = Real.arccos (-(1/x)) := by
  rw [Real.arccos_neg]

/-- Сферический эксцесс на угол строго положителен. -/
theorem excess_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < π - Real.arccos (1/x) :=
  sub_pos.mpr (dihedral_angle_lt_pi hx)

/-- Евклидов угол не меньше π/3 при x ≥ 2 (n ≥ 2). -/
theorem dihedral_angle_ge_pi_div_three {x : ℝ} (hx : 2 ≤ x) :
    π / 3 ≤ Real.arccos (1/x) := by
  have h2 : 1/x ≤ 1 / 2 := by field_simp; linarith
  have h3 : Real.arccos (1/2) ≤ Real.arccos (1/x) :=
    Real.arccos_le_arccos h2
  have h4 : Real.arccos ((1:ℝ)/2) = π/3 :=
    Real.arccos_eq_of_eq_cos (by positivity)
      (by linarith [Real.pi_pos]) Real.cos_pi_div_three.symm
  exact h4 ▸ h3

/-- Евклидов угол строго меньше π/2 для всех конечных x. -/
theorem dihedral_angle_lt_pi_div_two {x : ℝ} (hx : 1 < x) :
    Real.arccos (1/x) < π / 2 :=
  Real.arccos_lt_pi_div_two.mpr (by positivity)

/-- ГРАНИЦЫ евклидовой суммы двугранных углов правильного
n-симплекса при n ≥ 2: (π/3)·K(n) ≤ S_euc(n) < (π/2)·K(n). -/
theorem euclid_sum_bounds (n : ℕ) (hn : 2 ≤ n) :
    π / 3 * (n * (n + 1) / 2 : ℝ)
      ≤ (n * (n + 1) / 2 : ℝ) * Real.arccos ((1:ℝ)/n)
      ∧ (n * (n + 1) / 2 : ℝ) * Real.arccos ((1:ℝ)/n)
        < π / 2 * (n * (n + 1) / 2 : ℝ) := by
  have hn' : (1:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hK : (0:ℝ) < n * (n + 1) / 2 := by positivity
  constructor
  · calc π / 3 * (n * (n + 1) / 2 : ℝ)
        = (n * (n + 1) / 2 : ℝ) * (π / 3) := by ring
      _ ≤ (n * (n + 1) / 2 : ℝ) * Real.arccos ((1:ℝ)/n) :=
          mul_le_mul_of_nonneg_left
            (dihedral_angle_ge_pi_div_three (by exact_mod_cast hn))
            hK.le
  · calc (n * (n + 1) / 2 : ℝ) * Real.arccos ((1:ℝ)/n)
        < (n * (n + 1) / 2 : ℝ) * (π / 2) :=
          (mul_lt_mul_of_pos_left
            (dihedral_angle_lt_pi_div_two hn') hK)
      _ = π / 2 * (n * (n + 1) / 2 : ℝ) := by ring

end Hagi.Geometry
