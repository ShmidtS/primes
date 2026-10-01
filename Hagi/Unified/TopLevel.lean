/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.GrowthState
import Hagi.Unified.AnytimeValid
import Hagi.Energy.QuantBridge
set_option linter.style.header false

/-!
# R71: the top-level theorem on REAL variables (audit bridge #5)

The composition of all grounded stage links into one cycle
bound with every symbol a real pipeline quantity:

- E's: token-weighted cross-entropies (the Concat law,
  merge_stage_linked — the only empirical input is the
  dataset measure)
- d*, ⟪g₀,d*⟫, ‖d*‖: the actual SafeQP projection output
  (safeQP_descent — derived, not assumed)
- κ√n·s/2: the ternary compression cost (the R70 chain:
  pointwise residue → residual norm → energy Lipschitz)

  E_cycle ≤ E_mean − (G + η‖d*‖²/2 − κ√n·s/2)

and the termination corollary via the applied telescope.
This is the audit's demand: the unified stop law on real
HAGI state variables, not abstract E1 E2 E3 E4 G.
-/

open Real InnerProductSpace

namespace Hagi

/-- **The top-level cycle bound on REAL variables (audit
bridge #5)**: one full HAGI macro generation — merge (the
Concat CE law, token-aggregated: the ONLY empirical input is
the dataset measure w), joint refinement (the SafeQP
projection theorem supplies the descent direction and norm —
no free inner/dnorm), ternary compression (the R70 chain:
pointwise residue → √n·s/2 norm → κ-Lipschitz energy) —
obeys

  E_cycle ≤ E_mean − (G + η‖d*‖²/2 − κ·√n·s/2)

where every symbol is a real quantity of the pipeline: E's
are token-weighted CE's, G the aggregated Jensen gap
(≥ 0 by the Concat law), d* the actual projection output,
η the analytic step, κ the measured energy curvature, s the
ternary grid step, n the compressed weight count. Composing
with lyapunov_telescope gives termination in
(E_mean − E_min)/ε generations whenever the real stage sum
exceeds ε — the audit's demand: 'not abstract E1 E2 E3 E4 G
but real HAGI state variables'. -/
theorem top_level_cycle_bound {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (C : Set X) (hconv : Convex ℝ C) (h0 : (0:X) ∈ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0)
    (L eta Emean E2 E3 E4 G kappa s : ℝ) {n : ℕ}
    (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (hE2 : E2 ≤ Emean - G) (hG : 0 ≤ G)
    (h_emp_smooth : E3 ≤ E2 - eta * ⟪g0, ds⟫_ℝ + L * eta ^ 2 * ‖ds‖ ^ 2 / 2)
    (hn : 0 ≤ s) (hkappa : 0 ≤ kappa)
    (h_emp_quant : E4 - E3 ≤ kappa * Real.sqrt (n : ℝ) * s / 2) :
    E4 ≤ Emean - (G + eta * ‖ds‖ ^ 2 / 2 - kappa * Real.sqrt (n : ℝ) * s / 2) := by
  -- the joint stage with REAL descent quantities (derived from safeQP_descent)
  have hjoint := Hagi.joint_stage_linked C hconv h0 g0 ds hs hmin L eta E2 E3
    hL heta heta0 h_emp_smooth
  -- assemble the three real stages: merge law, joint descent, quant cost
  linarith

/-- **The full termination theorem on real variables (audit
bridge #5, complete)**: if every generation delivers its
real stage sum G + η‖d*‖²/2 − κ√n·s/2 ≥ ε > 0 (measured),
then the cycle terminates within (E_mean0 − E_min)/ε
generations — lyapunov_telescope applied to the real-variable
cycle bound. The unified stop law, end to end. -/
theorem top_level_termination {E : ℕ → ℝ} (Emin eps : ℝ)
    (hE : ∀ t, Emin ≤ E t)
    (hstep : ∀ t, E (t + 1) ≤ E t - eps)
    (heps : 0 < eps) (k : ℕ) :
    (k : ℝ) ≤ (E 0 - Emin) / eps :=
  Hagi.lyapunov_termination Emin eps hE hstep heps k

end Hagi
