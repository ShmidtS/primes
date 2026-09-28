/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Concat

set_option linter.style.header false

/-!
# Ambiguity and the saturation of the ensemble

The growth trigger needs to distinguish "the ladder still gains
from more leaves" from "the ladder is saturated". This module
fixes the two theoretical anchor points of that distinction.

**Consensus is the zero point.** When all children agree up to a
per-child constant (`z a = z₀ + const a` — the temperature-shaped
consensus), the merged logit *is* the shared child (up to the mean
constant), and the ensemble CE equals the shared child's CE:
the ensemble gain is exactly zero (`consensus_no_gain`). Every
bit of ensemble gain above zero comes from *disagreement* — the
Jensen gap — and nowhere else. This is the formal content of
"the merged model cannot beat a child it reproduces".

**Prescription for the code (the τ-trigger).** The measured
ensemble gain as a function of pool size N tracks the Jensen gap,
which grows with the disagreement of the children. The saturation
criterion is therefore not a round constant but a *rate*: the
expected gain of the next leaf scales with the residual
disagreement the pool has not yet averaged out. Operationally:
compute the pairwise logit disagreement of the pool (the
per-position spread of the z a, e.g. the mean |z a v - z b v| over
pairs); the expected CE gain of adding a leaf is bounded by the
second-moment theory (`Hagi.ErrorProp.propagate_sq_bound`): the
variance of the mean falls as (spread)²/N — so the trigger
should stop when (spread)²/(N·(N+1)) < ε² with ε the measured
resolution floor (0.0021 nats, i.e. ε ≈ 0.0021): the next leaf's
*certifiable* gain is below the floor. This replaces the magic
constant with a computable rate that goes to zero exactly at
consensus.
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

/-- **Consensus is the zero point of the ensemble gain.** If the
children are all shifts of one another (`z a = z₀ + const a`),
the merged CE equals the CE of the shared child z₀ at the mean
shift: the ensemble reproduces the child exactly, and the
ensemble bound (`ensemble_ce_le_mean_general`) is tight — there
is no gain left. -/
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
