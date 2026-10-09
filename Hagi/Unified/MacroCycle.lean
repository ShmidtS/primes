/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Foundations.StageCalculus
import Hagi.Unified.GlobalConvergence
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

namespace Hagi

/-! ## Stage 1: Merge — the Jensen gap buys energy -/

/-- If `Em ≤ Emean − G` (h_emp_merge) and `0 ≤ G`, then
`Em ≤ Emean`. -/
theorem merge_stage (Emean G Em : ℝ)
    (h_emp_merge : Em ≤ Emean - G) (hgap : 0 ≤ G) :
    Em ≤ Emean := by linarith

/-- If `Em ≤ Emean − G` (h_emp_merge) and `0 < G`, then
`Em < Emean`. -/
theorem merge_stage_decrease (Emean G Em : ℝ)
    (h_emp_merge : Em ≤ Emean - G) (hgap : 0 < G) :
    Em < Emean := by linarith

/-! ## Stage 2: Joint — the SafeQP step is certified descent -/

/-- With `0 < L`, `0 ≤ eta ≤ 1/L`, certified descent
`dnorm² ≤ inner`, and the smoothness premise
`E2 ≤ E1 − eta * inner + L * eta² * dnorm² / 2` (h_emp_),
one gets `E2 ≤ E1 − eta * dnorm² / 2`. -/
theorem joint_stage (L eta dnorm inner E2 E1 : ℝ)
    (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (hdescent : dnorm ^ 2 ≤ inner)
    (h_emp_smooth : E2 ≤ E1 - eta * inner + L * eta ^ 2 * dnorm ^ 2 / 2) :
    E2 ≤ E1 - eta * dnorm ^ 2 / 2 := by
  have hd2 : 0 ≤ dnorm ^ 2 := by positivity
  have hkey : L * eta ≤ 2 := by
    have hmono : L * eta ≤ L * (1 / L) := mul_le_mul_of_nonneg_left heta (by linarith)
    have hdiv : L * (1 / L) = 1 := by field_simp
    rw [hdiv] at hmono
    linarith
  have hLe : L * eta ≤ 1 := by
    have hmono : L * eta ≤ L * (1 / L) := mul_le_mul_of_nonneg_left heta (by linarith)
    have hdiv : L * (1 / L) = 1 := by field_simp
    rw [hdiv] at hmono
    exact hmono
  have hsecond : L * eta ^ 2 * dnorm ^ 2 / 2 ≤ eta * dnorm ^ 2 / 2 := by
    have hpos : 0 ≤ eta * dnorm ^ 2 := by nlinarith
    have hm : L * eta * (eta * dnorm ^ 2) ≤ 1 * (eta * dnorm ^ 2) :=
      mul_le_mul_of_nonneg_right hLe hpos
    have hp : L * eta ^ 2 * dnorm ^ 2 ≤ eta * dnorm ^ 2 := by
      rw [show L * eta ^ 2 * dnorm ^ 2 = L * eta * (eta * dnorm ^ 2) from by ring]
      simpa using hm
    have hd2' : 2 * (L * eta ^ 2 * dnorm ^ 2 / 2) = L * eta ^ 2 * dnorm ^ 2 := by ring
    have hd3 : 2 * (eta * dnorm ^ 2 / 2) = eta * dnorm ^ 2 := by ring
    nlinarith [hp, hd2', hd3]
  have hterm : eta * dnorm ^ 2 ≤ eta * inner := mul_le_mul_of_nonneg_left hdescent heta0
  linarith

/-! ## Stage 3: Compress — ternary rounding costs at most κs/2 -/

/-- If the per-entry distortion is at most `1/2` (h_emp_dist)
and the energy increment satisfies
`E3 − E2pre ≤ kappa * s * dnorm` (h_emp_lip), then
`E3 − E2pre ≤ kappa * s / 2`. -/
theorem compress_stage (kappa s dnorm E3 E2pre : ℝ)
    (hkappa : 0 ≤ kappa) (hs : 0 ≤ s) (_hdn : 0 ≤ dnorm)
    (h_emp_dist : dnorm ≤ 1 / 2)
    (h_emp_lip : E3 - E2pre ≤ kappa * s * dnorm) :
    E3 - E2pre ≤ kappa * s / 2 :=
  Hagi.Foundations.compress_stage kappa s dnorm E3 E2pre hkappa hs _hdn
    h_emp_dist h_emp_lip

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
  have hm : E2 ≤ Emean := merge_stage Emean G E2 h_emp_merge hgap
  have hj : E3 ≤ E2 - eta * dnorm ^ 2 / 2 :=
    joint_stage L eta dnorm inner E3 E2 hL heta heta0 hdescent h_emp_smooth
  have hc : E4 - E3 ≤ kappa * s / 2 :=
    compress_stage kappa s dnormq E4 E3 hkappa hs hdnq h_emp_dist h_emp_lip
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
  lyapunov_termination_fin Emin eps k hE hstep heps

end Hagi
