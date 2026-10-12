/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Foundations.StageCalculus
import Hagi.Foundations.Telescope
set_option linter.style.header false

/-!
# The per-stage Lyapunov decomposition of the macro cycle

Each stage of Grow → Merge → Joint → Compress is bounded
separately: `merge_stage` (merged energy ≤ mean expert
energy, via the nonnegative Jensen gap), `joint_stage` (an
L-smooth SafeQP step with `eta ≤ 1/L` decreases energy by at
least `eta * ‖d*‖² / 2`), `compress_stage` (ternary rounding
costs at most `kappa * s / 2`). `macro_step_decrease`
composes them into one decrease of at least
`G + eta * ‖d*‖² / 2 − kappa * s / 2`; `macro_termination`
turns a per-step decrease ≥ ε into the horizon bound.

The per-stage hypotheses (smoothness, Lipschitz curvature,
merge tracking) are h_emp_ premises; what is proved is the
decomposition.
-/

open Finset Real

namespace Hagi.Unified

/-! ## The macro-cycle contraction -/

/-- Composing the three stage bounds (each h_emp_): the macro
step satisfies
`E4 ≤ Emean − (G + eta * dnorm² / 2 − kappa * s / 2)`. -/
theorem macro_step_decrease (_E1 E2 E3 E4 Emean G L eta dnorm inner kappa s dnormq : ℝ)
    (h_emp_merge : E2 ≤ Emean - G) (hgap : 0 ≤ G)
    (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (hdescent : dnorm ^ 2 ≤ inner)
    (h_emp_smooth : E3 ≤ E2 - eta * inner + L * eta ^ 2 * dnorm ^ 2 / 2)
    (hkappa : 0 ≤ kappa) (hs : 0 ≤ s) (hdnq : 0 ≤ dnormq)
    (h_emp_dist : dnormq ≤ 1 / 2)
    (h_emp_lip : E4 - E3 ≤ kappa * s * dnormq) :
    E4 ≤ Emean - (G + eta * dnorm ^ 2 / 2 - kappa * s / 2) := by
  have hm : E2 ≤ Emean := Hagi.Foundations.merge_stage Emean G E2 h_emp_merge hgap
  have hj : E3 ≤ E2 - eta * dnorm ^ 2 / 2 :=
    Hagi.Foundations.joint_stage L eta dnorm inner E3 E2 hL heta heta0 hdescent h_emp_smooth
  have hc : E4 - E3 ≤ kappa * s / 2 :=
    Hagi.Foundations.compress_stage kappa s dnormq E4 E3 hkappa hs hdnq h_emp_dist h_emp_lip
  have hchain : E4 ≤ Emean - eta * dnorm ^ 2 / 2 + kappa * s / 2 := by linarith
  linarith

/-- If `Emin ≤ E t` for `t ≤ k` and each step decreases by
at least `eps > 0`, then `k ≤ (E 0 − Emin) / eps`
(delegation to `lyapunov_termination_fin`). -/
theorem macro_termination {E : ℕ → ℝ} (Emin eps : ℝ) (k : ℕ)
    (hE : ∀ t ≤ k, Emin ≤ E t)
    (hstep : ∀ t < k, E (t+1) ≤ E t - eps)
    (heps : 0 < eps) :
    (k : ℝ) ≤ (E 0 - Emin) / eps :=
  Hagi.Foundations.lyapunov_termination_fin Emin eps k hE hstep heps

end Hagi.Unified

namespace Hagi
export Hagi.Unified (macro_step_decrease macro_termination)
end Hagi
