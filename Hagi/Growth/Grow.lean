/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Ambig

set_option linter.style.header false

/-!
# Grow — certified-gain criterion for the GROW trigger

The pool's mean-CE bound (via `ensemble_ce_le_mean_general`)
improves by exactly `certifiedGain N M c = (M − c)/(N + 1)` when a
leaf with standalone CE `c` is added to a pool of `N` leaves
with mean `M`.

* `newBound`: the new bound is `(N·M + c)/(N+1) = M − certifiedGain`;
* `certifiedGain_monotone`: smaller `c` gives an at-least-as-large
  certified gain;
* `grow_epsilon_stop`: if the smallest candidate CE certifies gain
  below `ε`, every candidate does;
* `certifiedGain_positive`: `c < M` implies a strictly positive
  gain and a strictly smaller bound;
* `pl_stop_certificate`: from a PL premise `μ(Lw − L*) ≤ gnorm²/2`
  conclude `Lw − L* ≤ gnorm²/(2μ)`.

Note: ranking by the bound is certified, but the actual merged CE
is not the bound (`selection_hurts` shows the ensemble ranking can
invert); nothing here claims convergence to an optimum.
-/

namespace Hagi.Growth

section Grow

variable {k : Type*} [Fintype k] [Nonempty k]

/-- `certifiedGain N M c = (M − c)/(N + 1)`: the improvement of the
mean-CE bound when a leaf with CE `c` joins a pool of `N` leaves
with mean `M`; positive iff `c < M`. -/
noncomputable def certifiedGain (N : ℕ) (M c : ℝ) : ℝ :=
  (M - c) / (N + 1)

/-- `(N * M + c) / (N + 1) = M - certifiedGain N M c`. -/
theorem newBound (N : ℕ) (M c : ℝ) :
    (N * M + c) / (N + 1) = M - certifiedGain N M c := by
  unfold certifiedGain
  field_simp
  ring

/-- If `c' ≤ c` then `certifiedGain N M c' ≥ certifiedGain N M c`.
(Valid for the bound only; the actual merged CE ranking may
invert — see `Hagi.selection_hurts`.) -/
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

/-- If `cstar ≤ c` and `certifiedGain N M cstar < ε`, then
`certifiedGain N M c < ε`. -/
theorem grow_epsilon_stop {N : ℕ} {M ε : ℝ}
    (cstar c : ℝ)
    (hbest : cstar ≤ c)
    (hstop : certifiedGain N M cstar < ε) :
    certifiedGain N M c < ε := by
  have h1 : certifiedGain N M c ≤ certifiedGain N M cstar :=
    certifiedGain_monotone N M c cstar hbest
  linarith

/-- If `c < M` then `0 < certifiedGain N M c` and
`M - certifiedGain N M c < M`. -/
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

/-- If `0 < μ` and `μ * (Lw − Lstar) ≤ gnorm ^ 2 / 2`, then
`Lw − Lstar ≤ gnorm ^ 2 / (2 * μ)`. -/
theorem pl_stop_certificate (Lw Lstar mu gnorm : ℝ)
    (hmu : 0 < mu)
    (h_emp_pl : mu * (Lw - Lstar) ≤ gnorm ^ 2 / 2) :
    Lw - Lstar ≤ gnorm ^ 2 / (2 * mu) := by
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * mu)]
  nlinarith [h_emp_pl]

end Hagi.Growth

namespace Hagi
export Hagi.Growth (certifiedGain newBound certifiedGain_monotone grow_epsilon_stop certifiedGain_positive pl_stop_certificate)
end Hagi
