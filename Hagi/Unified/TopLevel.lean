/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.GrowthState
import Hagi.Unified.AnytimeValid
import Hagi.Energy.QuantBridge
import Hagi.Step.SafeQPRobust
set_option linter.style.header false

/-!
# The top-level cycle bound on pipeline variables

`top_level_cycle_bound`: one macro generation on real
quantities (token-weighted CE's, the SafeQP projection
output `ds`, ternary compression) satisfies
`E4 ≤ Emean − (G + eta * ‖ds‖² / 2 − kappa * √n * s / 2)`.
The empirical inputs are the smoothness and Lipschitz
premises; the descent direction and the √n factor are
derived (`safeQP_descent`, `quant_energy_bridge`).
`top_level_termination` / `horizon_termination` give the
horizon bound; `noisy_cycle_step` adds minibatch noise
`m₀`; `merge_stage_concat_adapter` realizes the merge
hypothesis from the token-level Concat law.
-/

open Real InnerProductSpace Finset

namespace Hagi

/-- Under the stated premises (SafeQP minimality, smoothness
h_emp_, per-entry distortion ≤ s/2, Lipschitz h_emp_), one
macro generation satisfies
`E4 ≤ Emean − (G + eta * ‖ds‖² / 2 − kappa * √n * s / 2)`,
with the descent quantity derived from `safeQP_descent` and
the √n factor from `quant_energy_bridge`. -/
theorem top_level_cycle_bound {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (C : Set X) (hconv : Convex ℝ C) (h0 : (0:X) ∈ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0)
    (L eta Emean E2 E3 E4 G kappa s : ℝ) {n : ℕ}
    {w q : Fin n → ℝ}
    (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (hE2 : E2 ≤ Emean - G) (_hG : 0 ≤ G)
    (h_emp_smooth : E3 ≤ E2 - eta * ⟪g0, ds⟫_ℝ + L * eta ^ 2 * ‖ds‖ ^ 2 / 2)
    (hs0 : 0 ≤ s) (hres : ∀ i, |w i - q i| ≤ s / 2) (hkappa : 0 ≤ kappa)
    (h_emp_lip : E4 - E3 ≤ kappa * Real.sqrt (∑ i, (w i - q i) ^ 2)) :
    E4 ≤ Emean - (G + eta * ‖ds‖ ^ 2 / 2 - kappa * Real.sqrt (n : ℝ) * s / 2) := by
  -- the joint stage with REAL descent quantities (derived from safeQP_descent)
  have hjoint := Hagi.joint_stage_linked C hconv h0 g0 ds hs hmin L eta E2 E3
    hL heta heta0 h_emp_smooth
  -- the quant stage DERIVED through the R70 bridge (dependency made real —
  -- the R75 honesty fix: not an assumed final bound)
  have hquant := Hagi.quant_energy_bridge w q s kappa (E4 - E3) hs0 hres hkappa h_emp_lip
  -- assemble the three real stages: merge law, joint descent, quant cost
  linarith

/-- If `Emin ≤ E t` for `t ≤ k` and each step decreases by
at least `eps > 0`, then `k ≤ (E 0 − Emin) / eps`. -/
theorem top_level_termination {E : ℕ → ℝ} (Emin eps : ℝ) (k : ℕ)
    (hE : ∀ t ≤ k, Emin ≤ E t)
    (hstep : ∀ t < k, E (t + 1) ≤ E t - eps)
    (heps : 0 < eps) :
    (k : ℝ) ≤ (E 0 - Emin) / eps :=
  Hagi.lyapunov_termination_fin Emin eps k hE hstep heps

/-- Deterministic one-cycle bound under minibatch noise: with
concentration `|inner_est − inner_true| ≤ m0` (h_emp_),
smoothness in `inner_est`, `E3 = E2`, and the residual-norm
compression premise, `E4 ≤ Emean − (G + eta * dnorm² / 2 −
eta * m0 − kappa * √n * s / 2)`. No probability space is
involved. -/
theorem noisy_cycle_step {n : ℕ} {w q : Fin n → ℝ}
    (inner_true inner_est dnorm m0 eta L Emean E1 E2 E3 E4 G kappa s : ℝ)
    (hdescent : dnorm ^ 2 ≤ inner_true)
    (h_emp_conc : |inner_est - inner_true| ≤ m0)
    (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (h_emp_smooth : E2 ≤ E1 - eta * inner_est + L * eta ^ 2 * dnorm ^ 2 / 2)
    (hE1 : E1 ≤ Emean - G)
    (hs0 : 0 ≤ s) (hres : ∀ i, |w i - q i| ≤ s / 2) (hkappa : 0 ≤ kappa)
    (hquant : E4 - E3 ≤ kappa * Real.sqrt (∑ i, (w i - q i) ^ 2))
    (hE3 : E3 = E2) :
    E4 ≤ Emean - (G + eta * dnorm ^ 2 / 2 - eta * m0
      - kappa * Real.sqrt (n : ℝ) * s / 2) := by
  have hstoch := Hagi.stochastic_safeqp_descent inner_true inner_est dnorm m0 eta L E1 E2
    hdescent h_emp_conc hL heta heta0 h_emp_smooth
  have hq := Hagi.quant_energy_bridge w q s kappa (E4 - E3) hs0 hres hkappa hquant
  rw [hE3] at hq
  linarith

/-- Restatement of `top_level_termination`: per-step decrease
≥ eps and lower bound `Emin` give
`k ≤ (E 0 − Emin) / eps`. -/
theorem horizon_termination {E : ℕ → ℝ} (Emin eps : ℝ) (k : ℕ)
    (hE : ∀ t ≤ k, Emin ≤ E t) (hstep : ∀ t < k, E (t + 1) ≤ E t - eps)
    (heps : 0 < eps) :
    (k : ℝ) ≤ (E 0 - Emin) / eps :=
  Hagi.top_level_termination Emin eps k hE hstep heps

/-- For nonnegative weights `w` and per-token Concat law
`cmerged t ≤ cmean t`: the token-weighted merge identity
`∑ w t * cmerged t = ∑ w t * cmean t − ∑ w t * (cmean t − cmerged t)`
holds, and the gap `∑ w t * (cmean t − cmerged t)` is
nonnegative. -/
theorem merge_stage_concat_adapter {Tok : Type} [Fintype Tok]
    (w cmean cmerged : Tok → ℝ)
    (hw : ∀ t, 0 ≤ w t)
    (hcat : ∀ t, cmerged t ≤ cmean t) :
    (∑ t, w t * cmerged t = (∑ t, w t * cmean t)
        - ∑ t, w t * (cmean t - cmerged t))
    ∧ 0 ≤ ∑ t, w t * (cmean t - cmerged t) := by
  constructor
  · -- the definitional identity: per-term w·cmean − w·(diff) = w·cmerged
    have hterm : ∀ t : Tok, w t * cmean t - w t * (cmean t - cmerged t)
        = w t * cmerged t := by
      intro t
      ring
    have hsplit : ∑ t : Tok, w t * cmerged t
        = (∑ t : Tok, w t * cmean t) - ∑ t : Tok, w t * (cmean t - cmerged t) := by
      have e1 : ∑ t : Tok, (w t * cmean t - w t * (cmean t - cmerged t))
          = (∑ t : Tok, w t * cmean t) - ∑ t : Tok, w t * (cmean t - cmerged t) :=
        sum_sub_distrib (fun t : Tok => w t * cmean t)
          (fun t : Tok => w t * (cmean t - cmerged t))
      rw [← e1]
      exact Finset.sum_congr rfl (fun t _ => (hterm t).symm)
    exact hsplit
  · -- G >= 0: a sum of nonneg terms (w >= 0, mean - merged >= 0 by Concat)
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg (hw t) (by
      have := hcat t
      linarith)

end Hagi
