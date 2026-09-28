/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Select
import Hagi.Ambig

set_option linter.style.header false

/-!
# The GROW trigger as functional-gradient descent with an ε-criterion

The FGD literature (arXiv:2606.16926, "adaptive basis refinement")
fixes the abstract shape of our growth loop: a functional gradient
is infinite-dimensional, any finite representation (basis) plateaus
on a resolution-dependent error, and the fix is to *refine the
representation while the certified residual is above ε*. Their
criterion (Theorem 3.1): refine while `(1+ε)·U_t ≥ ε·‖g_t‖`, where
`U_t` is a computable upper bound on the representation error.

This module translates that criterion into the ladder's language,
honestly:

* **The basis is the pool.** N leaves = N basis elements for the
  functional "predict the next token"; the concat at 1/n is the
  finite representation.
* **The certified residual is the mean-CE bound.** By
  `ensemble_ce_le_mean_general`, the merged CE is certified by the
  mean child CE `M = (1/N)∑ c_a`. The *certified gain* of adding a
  candidate leaf with standalone CE `c` is exactly
  `certifiedGain N M c = (M − c)/(N + 1)`: the new bound is
  `(N·M + c)/(N+1)`.
* **The ε-stop, our version.** `grow_epsilon_stop`: if the best
  candidate (smallest `c`) certifies a gain below ε, then *every*
  candidate does — widening the pool cannot help the certificate
  anymore, and the remaining growth axis is the EXHAUSTED one
  (change the data/the leaf kind), which has no FGD analogue.
* **Bound ranking is certified; ensemble ranking is not.** For the
  certificate, ranking candidates by `c` is correct
  (`certifiedGain_monotone`); but the *actual* merged CE is not the
  bound — `selection_hurts` shows the ensemble ranking can invert.
  So the ε-criterion certifies *when to stop*, not *whom to add*;
  the pool choice still goes through the ensemble measurement.

**The honest divergence from FGD.** Their Hilbert-space theory with
a PL condition gives convergence to a *global optimum*. Our
`lse`-Jensen bound certifies only the mean child CE — the ladder
provably converges to the *average of the leaves*, not to the
optimum. The ε-criterion inherits exactly this strength and no
more: it stops when the *certificate* is exhausted, which is the
right trigger, but it does not import global optimality. Their
experiments (RKHS, wave equation, radiance fields) are not LM-scale
either — the scale transfer is ours to measure.
-/

namespace Hagi

section Grow

variable {k : Type*} [Fintype k] [Nonempty k]

/-- The certified gain of adding a candidate leaf with standalone CE
`c` to a pool of `N` leaves whose mean CE is `M`: the new mean-CE
bound is `(N·M + c)/(N+1)`, so the certificate improves exactly by
`(M − c)/(N+1)` — positive iff the candidate beats the pool mean. -/
noncomputable def certifiedGain (N : ℕ) (M c : ℝ) : ℝ :=
  (M - c) / (N + 1)

/-- The new mean-CE bound after adding the candidate: the convex
combination of the old mean and the newcomer. -/
theorem newBound (N : ℕ) (M c : ℝ) :
    (N * M + c) / (N + 1) = M - certifiedGain N M c := by
  unfold certifiedGain
  field_simp
  ring

/-- **Bound ranking is certified.** For the certificate, a smaller
standalone CE is always at least as good: if `c ≤ c'` then adding
the `c`-candidate gives an at-least-as-large certified gain. This is
the FGD "refine by the upper bound" step — valid *for the bound*,
with the explicit caveat that the actual merged CE ranking may
invert (`Hagi.selection_hurts`). -/
theorem certifiedGain_monotone (N : ℕ) (M c c' : ℝ) (h : c' ≤ c) :
    certifiedGain N M c' ≥ certifiedGain N M c := by
  have hN : (0:ℝ) < (N:ℝ) + 1 := by
    exact_mod_cast Nat.succ_pos N
  have hkey : (M - c') / ((N:ℝ) + 1) ≥ (M - c) / ((N:ℝ) + 1) := by
    have h3 : (0:ℝ) ≤ ((M - c') - (M - c)) / ((N:ℝ) + 1) :=
      div_nonneg (by linarith) (le_of_lt hN)
    have h4 : (M - c') / ((N:ℝ) + 1) - (M - c) / ((N:ℝ) + 1)
        = ((M - c') - (M - c)) / ((N:ℝ) + 1) := by
      field_simp
    linarith
  unfold certifiedGain
  norm_num
  exact_mod_cast hkey

/-- **The ε-stop.** If the *best* candidate (smallest standalone CE
`c*`) certifies a gain below ε, then every candidate does: widening
the pool cannot improve the certificate by more than ε, and the
GROW axis is certified-exhausted. The remaining move is the
EXHAUSTED axis (change the data or the leaf kind), which has no FGD
analogue — this is the ladder's own contribution to the FGD shape.

Formally: `c* ≤ c` for every candidate (it is the infimum), so
`certifiedGain N M c ≤ certifiedGain N M c* < ε`. -/
theorem grow_epsilon_stop {N : ℕ} {M ε : ℝ}
    (cstar c : ℝ)
    (hbest : cstar ≤ c)
    (hstop : certifiedGain N M cstar < ε) :
    certifiedGain N M c < ε := by
  have h1 : certifiedGain N M c ≤ certifiedGain N M cstar :=
    certifiedGain_monotone N M c cstar hbest
  linarith

/-- **The certified gain is real (when positive).** If the candidate
beats the pool mean (`c < M`), the new bound is strictly better
than the old one — the certificate actually moves. This is the
"refine while the residual is above ε" direction: the trigger has a
witnessed, computable quantity to test, exactly like FGD's `U_t`. -/
theorem certifiedGain_positive (N : ℕ) (M c : ℝ) (h : c < M) :
    0 < certifiedGain N M c ∧
      M - certifiedGain N M c < M := by
  have hN : (0:ℝ) < (N:ℝ) + 1 := by
    exact_mod_cast Nat.succ_pos N
  have hpos : 0 < certifiedGain N M c := by
    unfold certifiedGain
    exact div_pos (by linarith) hN
  constructor
  · exact hpos
  · unfold certifiedGain
    have hnum : (0:ℝ) < (M - c) / ((N:ℝ) + 1) :=
      div_pos (by linarith) hN
    linarith

end Grow

end Hagi
