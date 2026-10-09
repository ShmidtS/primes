/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Concat

set_option linter.style.header false

/-!
# Ambiguity: consensus is the zero point of the ensemble gain

Two results. `lse_shift`: adding a constant to every coordinate
shifts `lse` by that constant. `consensus_no_gain`: if the
children are shifts of one another (`z a = z₀ + const a`), the
merged CE equals the CE of the shared child at the mean shift, so
the ensemble bound `ensemble_ce_le_mean_general` is tight.
-/

namespace Hagi

section Ambiguity

variable {k : Type*} [Fintype k] [Nonempty k]

/-- The shift-invariance of `lse`: adding a constant to every
coordinate shifts `lse` by that constant. -/
theorem lse_shift (z : k → ℝ) (c : ℝ) :
    lse (fun v => z v + c) = lse z + c := by
  unfold lse
  have hexp : ∑ v, Real.exp (z v + c) = Real.exp c * ∑ v, Real.exp (z v) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by
      rw [Real.exp_add]
      ring
  rw [hexp, Real.log_mul (by positivity : (Real.exp c) ≠ 0)
    (by positivity : (∑ v, Real.exp (z v)) ≠ 0), Real.log_exp]
  ring

/-- If the children are shifts of one another
(`z a = z₀ + const a`), the merged CE equals `lse z₀ - z₀ t`:
the ensemble bound `ensemble_ce_le_mean_general` is tight. -/
theorem consensus_no_gain {N : ℕ} [NeZero N] (z₀ : k → ℝ)
    (const : Fin N → ℝ) (t : k) :
    ceOneHot t (fun v => (∑ a, (z₀ v + const a)) / N)
      = lse z₀ - z₀ t := by
  -- the mean logit = z₀ + mean const
  have hmean : ∀ v : k,
      (∑ a, (z₀ v + const a)) / N = z₀ v + (∑ a, const a) / N := by
    intro v
    rw [Finset.sum_add_distrib, add_div]
    have hconst : ∑ a : Fin N, z₀ v = (N:ℝ) * z₀ v := by
      simp
    rw [hconst]
    have hN : ((N:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
    field_simp
  have hc : ceOneHot t (fun v => z₀ v + (∑ a, const a) / N)
      = lse z₀ - z₀ t := by
    unfold ceOneHot
    rw [lse_shift]
    ring
  have hfun : (fun v => (∑ a, (z₀ v + const a)) / N)
      = fun v => z₀ v + (∑ a, const a) / N :=
    funext fun v => hmean v
  rw [hfun]
  exact hc

end Ambiguity

end Hagi
