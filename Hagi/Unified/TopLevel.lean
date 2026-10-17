/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.System.GrowthState
import Hagi.Step.ProjectionDescent
import Hagi.Unified.AnytimeValid
import Hagi.Energy.QuantBridge
import Mathlib.Tactic
/-!
# SafeQPRobust — устойчивая к возмущениям допустимость

* `robust_feasibility`: при `eps + m ≤ g*d` и
  `|g*d − gdhat| ≤ m` — `eps ≤ gdhat` (запас eps + m
  поглощает шум батча);
* `stochastic_safeqp_feasible`: построчная версия для всех
  доменов i;
* `stochastic_safeqp_descent`: при `dnorm² ≤ inner_true`,
  `|inner_est − inner_true| ≤ m0`, `0 < L`, `eta ≤ 1/L` и
  гладкости — `E₂ ≤ E₁ − eta·dnorm²/2 + eta·m0`
  (чистый спуск при `m0 < dnorm²`).

Полная проекционно-возмущенческая оценка `‖d̂*−d*‖` — не
доказана (матричная теория возмущений).
-/

open Finset

namespace Hagi.Step

/-- При `eps + m ≤ g*d` и `|g*d − gdhat| ≤ m`:
`eps ≤ gdhat`. -/
theorem robust_feasibility (g d gdhat : ℝ) (eps m : ℝ)
    (htrue : eps + m ≤ g * d) (hpert : |g * d - gdhat| ≤ m) :
    eps ≤ gdhat := by
  nlinarith [abs_le.mp hpert]

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- Если для всех i выполнено `eps i + m i ≤ g i * d i` и
`|g i * d i − gdhat i| ≤ m i`, то `eps i ≤ gdhat i` для
всех i. -/
theorem stochastic_safeqp_feasible {K : Type} [Fintype K]
    (g d gdhat : K → ℝ) (eps m : K → ℝ)
    (htrue : ∀ i, eps i + m i ≤ g i * d i)
    (h_emp_conc : ∀ i, |g i * d i - gdhat i| ≤ m i) :
    ∀ i, eps i ≤ gdhat i :=
  fun i => robust_feasibility (g i) (d i) (gdhat i) (eps i) (m i)
    (htrue i) (h_emp_conc i)

/-- При `dnorm² ≤ inner_true`, `|inner_est − inner_true| ≤ m0`,
`0 < L`, `0 ≤ eta ≤ 1/L` и гладкости
`E₂ ≤ E₁ − eta·inner_est + L·eta²·dnorm²/2` —
`E₂ ≤ E₁ − eta·dnorm²/2 + eta·m0`. -/
theorem stochastic_safeqp_descent (inner_true inner_est dnorm m0 eta L E1 E2 : ℝ)
    (hdescent : dnorm ^ 2 ≤ inner_true)
    (h_emp_conc : |inner_est - inner_true| ≤ m0)
    (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (h_emp_smooth : E2 ≤ E1 - eta * inner_est + L * eta ^ 2 * dnorm ^ 2 / 2) :
    E2 ≤ E1 - eta * dnorm ^ 2 / 2 + eta * m0 := by
  have heff : dnorm ^ 2 - m0 ≤ inner_est := by
    rw [abs_le] at h_emp_conc
    have h1 : -(m0) ≤ inner_est - inner_true := h_emp_conc.1
    have h2 : inner_est - inner_true ≤ m0 := h_emp_conc.2
    have h3 : inner_true - m0 ≤ inner_est := by linarith
    linarith
  have hsecond : L * eta ^ 2 * dnorm ^ 2 / 2 ≤ eta * dnorm ^ 2 / 2 := by
    have hLe : L * eta ≤ 1 := by
      have hmono : L * eta ≤ L * (1 / L) := mul_le_mul_of_nonneg_left heta (by linarith)
      have hdiv : L * (1 / L) = 1 := by field_simp
      linarith
    by_cases hd : dnorm ^ 2 = 0
    · rw [hd]
      norm_num
    · have hd2 : 0 < dnorm ^ 2 := by
        have hnn : 0 ≤ dnorm ^ 2 := sq_nonneg dnorm
        by_contra hc
        push Not at hc
        apply hd
        linarith
      have hsplit : L * eta ^ 2 * dnorm ^ 2 = (L * eta) * (eta * dnorm ^ 2) := by ring
      rw [hsplit]
      have hmono : (L * eta) * (eta * dnorm ^ 2) ≤ 1 * (eta * dnorm ^ 2) :=
        mul_le_mul_of_nonneg_right hLe (by nlinarith)
      calc L * eta * (eta * dnorm ^ 2) / 2
          = (L * eta) * (eta * dnorm ^ 2) / 2 := by ring
        _ ≤ 1 * (eta * dnorm ^ 2) / 2 := by
            have hd2' : 2 * ((L * eta) * (eta * dnorm ^ 2) / 2)
                = (L * eta) * (eta * dnorm ^ 2) := by ring
            have hd3' : 2 * (1 * (eta * dnorm ^ 2) / 2) = eta * dnorm ^ 2 := by ring
            nlinarith [hmono, hd2', hd3']
        _ = eta * dnorm ^ 2 / 2 := by ring
  nlinarith [h_emp_smooth, heff, hsecond, heta0]

end Hagi.Step

namespace Hagi
export Hagi.Step (robust_feasibility stochastic_safeqp_feasible stochastic_safeqp_descent)
end Hagi
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

namespace Hagi.Unified

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

/-- **Терминация из телескопа с риск-бюджетом (R529)**:
композиция `stage_certificate_telescope` + лиапуновской терминации.
Каждое поколение сертифицировано: после ≤ before − decrease + riskSpend
(soundность телескопа), decrease ≥ ε > 0 в каждом поколении, а
суммарный risk-спенд ограничен R (риск-бюджет). Тогда потенциал на
выходе T поколений остаётся ≥ Emin − R, и горизонт ограничен:
T ≤ (Φ₀ − Emin + R) / ε. Риск-бюджет входит в числитель горизонта —
менеджмент риска линеен по времени жизни процесса. -/
theorem risk_budget_termination (cs : ℕ → Hagi.StageCertificate)
    (Φ₀ Emin eps R : ℝ) (T : ℕ)
    (hT : 0 < T)
    (heps : 0 < eps)
    (h0 : (cs 0).before = Φ₀)
    (hcontig : ∀ t, t + 1 < T → (cs (t + 1)).before = (cs t).after)
    (hsound : ∀ t, t < T →
      (cs t).after ≤ (cs t).before - ((cs t).cert).decrease
        + ((cs t).cert).riskSpend)
    (hdec : ∀ t, t < T → eps ≤ ((cs t).cert).decrease)
    (hsum : ∑ t ∈ Finset.range T, ((cs t).cert).riskSpend ≤ R)
    (hR0 : 0 ≤ R)
    (hfloor : Emin ≤ (cs (T - 1)).after) :
    (T : ℝ) ≤ (Φ₀ - Emin + R) / eps := by
  have htel := Hagi.stage_certificate_telescope cs hT hcontig hsound
  rw [h0] at htel
  -- sum of decreases ≥ T * eps
  have hsumdec : ∑ t ∈ Finset.range T, ((cs t).cert).decrease ≥ eps * (T:ℝ) := by
    calc eps * (T:ℝ) = ∑ t ∈ Finset.range T, eps := by
          rw [Finset.sum_const]; simp; ring
      _ ≤ ∑ t ∈ Finset.range T, ((cs t).cert).decrease :=
          Finset.sum_le_sum fun t ht => hdec t (Finset.mem_range.mp ht)
  -- after_{T-1} ≤ Φ₀ − Tε + R
  have hbound : (cs (T - 1)).after ≤ Φ₀ - eps * (T:ℝ) + R := by
    calc (cs (T - 1)).after
        ≤ Φ₀ - ∑ t ∈ Finset.range T, ((cs t).cert).decrease
          + ∑ t ∈ Finset.range T, ((cs t).cert).riskSpend := htel
      _ ≤ Φ₀ - eps * (T:ℝ) + R := by linarith
  -- close: Emin − R ≤ after ≤ Φ₀ − Tε + R
  have hcomm : eps * (T:ℝ) = (T:ℝ) * eps := mul_comm _ _
  rw [le_div_iff₀ heps]
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
  top_level_termination Emin eps k hE hstep heps

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

end Hagi.Unified

namespace Hagi
export Hagi.Unified (top_level_cycle_bound top_level_termination noisy_cycle_step horizon_termination merge_stage_concat_adapter risk_budget_termination)
end Hagi
