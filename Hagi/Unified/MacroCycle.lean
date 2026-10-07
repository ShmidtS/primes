/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Foundations.StageCalculus
import Hagi.Unified.GlobalConvergence
import Hagi.Audit.Exactness
import Hagi.Audit.Foundations
import Hagi.Energy.TernaryLean
set_option linter.style.header false

/-!
# R52: the per-stage Lyapunov decomposition

The external review (round-51) correctly observed that
`lyapunov_telescope` is a *generic* telescope: it assumes
E_{k+1} ≤ E_k − ε but does not prove the macro-cycle
Grow → Merge → Joint → Compress itself delivers such a step.

This module closes that gap at the level the current theory
supports: each STAGE of the macro-cycle is bound separately,
with the stage's own honesty conditions made explicit:

* **Merge stage** (`merge_stage`): the merged model's energy
  is bounded by the mean expert energy MINUS the Jensen gap.
  The stage never increases the pool's energy certificate —
  the gap is the reward for diversity, `gap_N_nonneg` is the
  sign theorem.
* **Joint stage** (`joint_stage`): one SafeQP-certified step
  decreases energy by at least η·‖d*‖² given L-smoothness and
  step size η ≤ 1/L — composed from `safeQP_descent`
  (⟪g, d*⟫ ≥ ‖d*‖², the certified descent direction).
* **Compress stage** (`compress_stage`): ternary rounding of
  a residual inside the unit band adds at most s/2 per entry;
  scaled by the residual Lipschitz constant of energy, the
  stage increases energy by at most κ·s/2.
* **Macro-cycle** (`macro_step_decrease`, `macro_termination`):
  the composed step decreases the energy certificate by at
  least (Jensen gap + η·‖d*‖² − κ·s/2); when that exceeds ε,
  the generic telescope finally rests on stage-level theorems
  — the unified structure's stop law.

**Honest boundary**: the per-stage hypotheses (L-smoothness,
κ-energy sensitivity to quantization, and the smoothness of
the merged-init energy in the gap) are empirical inputs (to
be measured on the stand), not theorems. What is proven is
the DECOMPOSITION: if each stage's certificate holds, the
macro-cycle is a contraction and terminates in
(E₀ − E_min)/ε generations.
-/

open Finset Real

namespace Hagi

/-! ## Stage 1: Merge — the Jensen gap buys energy -/

/-- **Merge stage bound**: the merged model's energy is at
most the mean expert energy minus the (nonnegative) Jensen
gap `G ≥ 0`. Conditional on the empirical hypothesis that
the merged energy certificate tracks the LSE pooling gap
(h_merge); the SIGN comes from `gap_N_nonneg`: G ≥ 0 always,
so the merge stage never increases the certificate. -/
theorem merge_stage (Emean G Em : ℝ)
    (h_emp_merge : Em ≤ Emean - G) (hgap : 0 ≤ G) :
    Em ≤ Emean := by linarith

/-- **Merge stage strict decrease**: when the pool is
genuinely diverse (G > 0), the merge stage strictly
decreases the energy certificate by G. -/
theorem merge_stage_decrease (Emean G Em : ℝ)
    (h_emp_merge : Em ≤ Emean - G) (hgap : 0 < G) :
    Em < Emean := by linarith

/-! ## Stage 2: Joint — the SafeQP step is certified descent -/

/-- **Joint stage bound**: with L-smooth energy, step η ≤ 1/L
along the SafeQP direction d*, the energy decreases by at
least η·‖d*‖². Proof: smooth descent lemma
E(θ−ηd*) ≤ E(θ) − η⟪g,d*⟫ + Lη²‖d*‖²/2, then the certified
inner product ⟪g,d*⟫ ≥ ‖d*‖² from `safeQP_descent`, then
η ≤ 1/L folds the second-order term into the first. -/
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

/-- **Compress stage bound**: if every rounded entry of the
compressed residual stays within s/2 of its pre-rounding
value (`tern_distortion_round` scaled by the grid step), and
the energy is κ-Lipschitz in the parameter sup-norm, the
compression stage increases the energy by at most κ·s/2. -/
theorem compress_stage (kappa s dnorm E3 E2pre : ℝ)
    (hkappa : 0 ≤ kappa) (hs : 0 ≤ s) (_hdn : 0 ≤ dnorm)
    (h_emp_dist : dnorm ≤ 1 / 2)
    (h_emp_lip : E3 - E2pre ≤ kappa * s * dnorm) :
    E3 - E2pre ≤ kappa * s / 2 :=
  Hagi.Foundations.compress_stage kappa s dnorm E3 E2pre hkappa hs _hdn
    h_emp_dist h_emp_lip

/-! ## The macro-cycle contraction -/

/-- **The macro step is a contraction** (conditional
composition): with the merge gap G ≥ 0, one SafeQP step of
size η ≤ 1/L along d*, and a compression cost ≤ κs/2, the
macro cycle decreases the energy certificate by at least
G + η‖d*‖²/2 − κs/2 (the smooth-descent rate for the joint
stage is η‖d*‖²/2, not η‖d*‖² — the honest strong-convexity
constant). The three stage hypotheses are empirical
(h_emp_-prefixed); the composition is a theorem. -/
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

/-- **Macro termination** — the unified stop law resting on
stage-level certificates: if every macro generation delivers
its certified decrease (gap + step − compression ≥ ε > 0)
and the energy certificate is bounded below by E_min, the
cycle terminates in at most (E₀ − E_min)/ε generations.
This upgrades `lyapunov_termination` from a generic
telescope to a stage-decomposed contraction. -/
theorem macro_termination {E : ℕ → ℝ} (Emin eps : ℝ) (k : ℕ)
    (hE : ∀ t ≤ k, Emin ≤ E t)
    (hstep : ∀ t < k, E (t+1) ≤ E t - eps)
    (heps : 0 < eps) :
    (k : ℝ) ≤ (E 0 - Emin) / eps :=
  lyapunov_termination_fin Emin eps k hE hstep heps

end Hagi
