/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# Foundations.Chord — хорда exp и cosh-граница

Миграция-2026-10-05 (R170): канонический дом чистых calculus-лемм
без Hagi-зависимостей: хорда exp на [a,b] и квадратичная
cosh-граница. Перенесены из Energy/PoEBound (exp_chord_ab) и
Ensemble/Hoeffding (log_cosh_le) — потребители Probability
(Azuma/Freedman/CertifiedEstimator) и Energy/Ensemble больше
не тянут верхние слои ради этих лемм.
-/

open Finset Real

namespace Hagi.Foundations

/-- **Хорда exp на [a, b]**: выпуклость exp даёт поточечную
мажорацию хордой между концами. -/
theorem exp_chord_ab (a b x : ℝ) (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    Real.exp x ≤ (b - x) / (b - a) * Real.exp a
      + (x - a) / (b - a) * Real.exp b := by
  have hconv : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
  have w1 : (0:ℝ) ≤ (b - x) / (b - a) := by
    apply div_nonneg <;> linarith
  have w2 : (0:ℝ) ≤ (x - a) / (b - a) := by
    apply div_nonneg <;> linarith
  have hne : (b - a : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp
    ring
  have key := hconv.2 (Set.mem_univ a) (Set.mem_univ b) w1 w2 hsum
  have hm1 : ((b - x) / (b - a)) * a = ((b - x) * a) / (b - a) :=
    (div_mul_eq_mul_div _ _ _)
  have hm2 : ((x - a) / (b - a)) * b = ((x - a) * b) / (b - a) :=
    (div_mul_eq_mul_div _ _ _)
  have hcomb : ((b - x) / (b - a)) * a + ((x - a) / (b - a)) * b = x := by
    rw [hm1, hm2, ← add_div, div_eq_iff hne]
    ring
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at key
  rw [hcomb] at key
  exact key

/-- **Квадратичная cosh-граница**: log cosh M ≤ M²/2
(Mathlib cosh_le_exp_half_sq + монотонность log). -/
theorem log_cosh_le (M : ℝ) : Real.log (Real.cosh M) ≤ M ^ 2 / 2 := by
  have hpos : 0 < Real.cosh M := Real.cosh_pos M
  have hlog : Real.log (Real.cosh M) ≤ Real.log (Real.exp (M ^ 2 / 2)) :=
    Real.log_le_log hpos (cosh_le_exp_half_sq M)
  rw [Real.log_exp] at hlog
  exact hlog

end Hagi.Foundations
