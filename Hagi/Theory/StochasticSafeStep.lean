/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.CEChain
import Hagi.Cert.StepGen
import Hagi.State.CanonicalTrainState
import Hagi.Unified.StochasticCELearning
import Hagi.Probability.Concentration

/-!
# The central stochastic safe step with the Freedman radius (C388)

Audit A17 §5.2, the CENTRAL theorem of the unified proof chain: ONE
certified decision mechanism for every update.  Given a proposal
(direction from ANY provider, an estimated alignment, an estimated
curvature) and a state-conditioned noise model, the controller EITHER

* ACCEPTS: `0 < Â − r ∧ 0 < Ĉ + u`, executes the conservative step
  `η = (Â − r) / (2 (Ĉ + u))` and — with high probability
  `1 − exp(−r²/(4σ))` over the minibatch draw — the realized loss
  obeys `L(θ + ηd) ≤ L(θ) − (Â − r)²/(4(Ĉ+u))`, OR
* REFUSES: the accept condition fails and the controller holds the
  state ENTIRELY (the C363 `Hold` path — a theorem: nothing changes,
  `hold_refusal_safe`).

The radius `r` is DERIVED from the existing Freedman machinery: the
single-draw variance-form tail `noise_tail_le`
(`P[g ≥ r] ≤ exp(−r²/(4σ))` in the regime `c·r ≤ 2σ`) is the
one-measurement instance of `Hagi.Probability.freedman_variance_radius`
(C356), applied to the alignment estimator
`Â(θ, ω) = A(θ) + noise(θ, ω)` on one minibatch.

## Composition (the audit's Proposal → SafeStep → Certificate arrows)

* `StochasticProposal` — the proposal record: a deterministic carrier
  `U : UniversalSafeStep Θ` (loss, η-parametrized update direction,
  true alignment `A`, true curvature `C`, the quadratic majorizer
  law), the state-conditioned minibatch kernel `noiseLaw θ`, the
  noise `noise θ ω` with the honest identification
  `Â(θ,ω) = A(θ) + noise(θ,ω)`, the curvature estimate `Ĉ` with the
  uncertainty binder `u`, and the noise premises AT EVERY state.
* `certified_descent_of_noise_le` — SafeStep: on a good draw
  (`noise ≤ r`) with accept, the conservative quadratic minimization
  gives the certified drop straight from the majorizer law.
* `stochastic_safe_step_certified` — the CENTRAL whp theorem: the
  probability that the controller accepts AND the certified descent
  fails is at most `exp(−r²/(4σ))`.
* `stochastic_safe_step_certificate` — the `CertStochasticStep`
  packaging (C356 pattern) under a uniform alignment floor.
* `acceptStepCert` — the `CertStepGen` adapter: an accepted step is a
  certified step of the general kernel (drops into the certified
  loop `trajectory_telescope_gen`).

## Honest ledger: estimated vs derived vs binder

- ESTIMATED (observable): `Â` (one minibatch measurement of the
  alignment, `= A + noise`), `Ĉ` (curvature estimate) with the
  explicit uncertainty `u`.
- DERIVED: the radius `r` (from the noise model `c`, `σ` — the
  Freedman closed form), the step size `η`, the certified drop.
- BINDERS (premise-form, not estimated here): the quadratic
  majorizer law `majorizes`, the curvature upper bound
  `curvature_bound : C ≤ Ĉ + u`, the floors in the adapter, the
  uniform alignment floor of the packaged certificate.

## Honest scope (premise-form limitations)

- Freedman does NOT cover the direction choice: `d` may be
  data-dependent (any `DirectionProvider`-style proposal, C366), but
  it is fixed BEFORE the measurement — it lives in the deterministic
  carrier `U` and the noise premises are conditioned on the state
  (`noiseLaw` is a function of `θ`, matching the C360 conditioning
  `∀ a ∈ (markovLaw …).support`).  The tail statement is about the
  noise GIVEN the state and direction, never about selecting `d`.
- The variance-form regime `c·r ≤ 2σ` is a premise (C356 regime);
  outside it the C350 radius `exp(−r²/(4(σ + c·r)))` applies and is
  NOT restated here.
- The T-step chaining is cited, not reproved: `stochasticLoop`
  (the C360 whp loop) and `trajectoryTelescope` (the C353/C387
  drop telescope of the general kernel).
- `universal_accept_form` (C387) proves the drop at the
  TRUE-value step `A/(2C)`; the present module proves the
  conservative-estimate step `(Â−r)/(2(Ĉ+u))` — a different object,
  the one an actual controller can execute.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.StochasticSafeStep

open Hagi.Probability Hagi.Theory.CEChain

/-! ## Stage 1 — the single-draw Freedman tail (the radius of Â) -/

variable {Ω : Type} [Fintype Ω]

/-- The single-draw Freedman tail (C388, the radius of the alignment
estimate): for a bounded, centered noise `g` with variance at most
`σ`, in the variance regime `c·r ≤ 2σ`, the one-sided tail obeys
`P[r ≤ g] ≤ exp(−r²/(4σ))`.  This is the one-measurement instance of
`freedman_variance_radius` (C356): `V := const σ`,
`λ := r/(2σ)` with `λ·c ≤ 1` from the regime premise. -/

theorem noise_tail_le (law : PMF Ω) (g : Ω → ℝ) (c σ r : ℝ)
    (hσ : 0 < σ) (hr : 0 < r) (hrc : c * r ≤ 2 * σ)
    (hbounded : ∀ ω ∈ law.support, |g ω| ≤ c)
    (hmean : pmfMean law g = 0)
    (hvar : pmfMean law (fun ω => g ω ^ 2) ≤ σ) :
    pmfMean law (fun ω => if r ≤ g ω then 1 else 0)
      ≤ Real.exp (-r ^ 2 / (4 * σ)) := by
  exact Hagi.Probability.concOneDrawRadius law g c σ r hσ hr hrc hbounded hmean hvar

/-! ## Stage 2 — the stochastic proposal record -/

variable {Θ : Type}

/-- The stochastic proposal record (C388): everything the certified
decision mechanism sees before committing.  `carrier` is the
deterministic `UniversalSafeStep` (C387) — the direction `d` is
already baked into `carrier.step`, possibly data-dependent but FIXED
BEFORE the measurement; `noiseLaw θ` is the minibatch kernel
conditioned on the state; `noise θ ω` identifies the estimated
alignment `alignEst θ ω = carrier.alignment θ + noise θ ω`;
`curvEst`/`curvUnc` carry the curvature estimate with its explicit
uncertainty binder; `noiseBound`/`noiseVar`/`radius` are the noise
model from which the Freedman radius is read. -/

structure StochasticProposal (Θ : Type) (Ω : Type) [Fintype Ω] where
  /-- The deterministic carrier: loss, η-parametrized update,
  true alignment, true curvature, quadratic majorizer (C387). -/
  carrier : UniversalSafeStep Θ
  /-- The minibatch sampling kernel, conditioned on the state. -/
  noiseLaw : Θ → PMF Ω
  /-- The alignment noise: `alignEst θ ω − carrier.alignment θ`. -/
  noise : Θ → Ω → ℝ
  /-- The measured alignment estimate (one minibatch draw). -/
  alignEst : Θ → Ω → ℝ
  /-- The identification: the estimate is the truth plus noise. -/
  alignEst_ident : ∀ θ ω, alignEst θ ω = carrier.alignment θ + noise θ ω
  /-- The estimated curvature. -/
  curvEst : ℝ
  /-- The curvature uncertainty binder `u` (premise-form). -/
  curvUnc : ℝ
  /-- The noise bound `c`. -/
  noiseBound : ℝ
  /-- The conditional variance bound `σ`. -/
  noiseVar : ℝ
  /-- The confidence radius `r` (Freedman closed form, derived). -/
  radius : ℝ
  /-- The noise is bounded by `c` at every state. -/
  noise_bounded : ∀ θ, ∀ ω ∈ (noiseLaw θ).support, |noise θ ω| ≤ noiseBound
  /-- The noise is centered at every state. -/
  noise_mean : ∀ θ, pmfMean (noiseLaw θ) (noise θ) = 0
  /-- The conditional variance is at most `σ` at every state. -/
  noise_var : ∀ θ, pmfMean (noiseLaw θ) (fun ω => noise θ ω ^ 2) ≤ noiseVar
  /-- The curvature upper binder: `C ≤ Ĉ + u` (premise-form). -/
  curvature_bound : ∀ θ, carrier.curvature θ ≤ curvEst + curvUnc

namespace StochasticProposal

/-- The accept condition of the central mechanism: positive
conservative alignment `0 < Â − r` AND positive curvature upper
bound `0 < Ĉ + u`. -/
def acceptCondition (P : StochasticProposal Θ Ω) (θ : Θ) (ω : Ω) : Prop :=
  0 < P.alignEst θ ω - P.radius ∧ 0 < P.curvEst + P.curvUnc

/-- The conservative certified step size `η = (Â − r)/(2 (Ĉ + u))`:
the only step size an actual controller (which sees estimates, not
truth) can execute. -/
noncomputable def certifiedStepSize (P : StochasticProposal Θ Ω)
    (θ : Θ) (ω : Ω) : ℝ :=
  (P.alignEst θ ω - P.radius) / (2 * (P.curvEst + P.curvUnc))

/-- The certified drop `(Â − r)²/(4 (Ĉ + u))`: the guaranteed
decrease of the conservative step on a good draw. -/
noncomputable def certifiedDrop (P : StochasticProposal Θ Ω)
    (θ : Θ) (ω : Ω) : ℝ :=
  (P.alignEst θ ω - P.radius) ^ 2 / (4 * (P.curvEst + P.curvUnc))

/-- Decidability of the accept condition (the controller's branch). -/
noncomputable instance (P : StochasticProposal Θ Ω) (θ : Θ) (ω : Ω) :
    Decidable (P.acceptCondition θ ω) :=
  decidable_of_iff (0 < P.alignEst θ ω - P.radius ∧ 0 < P.curvEst + P.curvUnc)
    Iff.rfl

end StochasticProposal

/-! ## Stage 3 — the deterministic core (SafeStep arrow) -/

/-- The deterministic core of the central theorem: on a good draw
(`noise ≤ r`) with the accept condition, the conservative step
satisfies the certified drop.  One quadratic minimization from the
majorizer law `majorizes` — the estimate-form sibling of
`universal_descent` (C387), at the controller's step size. -/
theorem certified_descent_of_noise_le (P : StochasticProposal Θ Ω)
    (θ : Θ) (ω : Ω)
    (hnoise : P.noise θ ω ≤ P.radius)
    (hacc : P.acceptCondition θ ω) :
    P.carrier.loss (P.carrier.step θ (P.certifiedStepSize θ ω))
      ≤ P.carrier.loss θ - P.certifiedDrop θ ω := by
  have hAl : 0 < P.alignEst θ ω - P.radius := hacc.1
  have hCu : 0 < P.curvEst + P.curvUnc := hacc.2
  set x : ℝ := P.alignEst θ ω - P.radius with hx
  set y : ℝ := P.curvEst + P.curvUnc with hy
  have hη : 0 ≤ x / (2 * y) := by positivity
  have h := P.carrier.majorizes θ (x / (2 * y)) hη
  have hA : x ≤ P.carrier.alignment θ := by
    have hident := P.alignEst_ident θ ω
    linarith
  have hC := P.curvature_bound θ
  have key : x / (2 * y) * x - (x / (2 * y)) ^ 2 * y = x ^ 2 / (4 * y) := by
    field_simp
    ring
  unfold StochasticProposal.certifiedStepSize StochasticProposal.certifiedDrop
  nlinarith

/-! ## Stage 4 — the CENTRAL theorem -/

/-- THE CENTRAL THEOREM (C388, audit 5.2): under the noise premises
of `StochasticProposal` and in the variance regime
`c·r ≤ 2σ`, the probability that the controller ACCEPTS the update
AND the certified descent fails is at most `exp(−r²/(4σ))`.  With
probability `≥ 1 − exp(−r²/(4σ))` the mechanism is sound: every
accepted update delivers its certified drop; a refusal is the safe
`Hold` path (`hold_refusal_safe`).  Proof: the bad event implies
`r < noise` (contrapositive of `certified_descent_of_noise_le`),
then the single-draw Freedman tail `noise_tail_le`. -/
theorem stochastic_safe_step_certified (P : StochasticProposal Θ Ω)
    (θ : Θ) (hσ : 0 < P.noiseVar) (hr : 0 < P.radius)
    (hrc : P.noiseBound * P.radius ≤ 2 * P.noiseVar) :
    pmfMean (P.noiseLaw θ) (fun ω =>
      if P.acceptCondition θ ω ∧
        P.carrier.loss θ - P.certifiedDrop θ ω
          < P.carrier.loss (P.carrier.step θ (P.certifiedStepSize θ ω))
        then 1 else 0)
      ≤ Real.exp (-P.radius ^ 2 / (4 * P.noiseVar)) := by
  have ht := noise_tail_le (P.noiseLaw θ) (P.noise θ) P.noiseBound
    P.noiseVar P.radius hσ hr hrc (P.noise_bounded θ) (P.noise_mean θ)
    (P.noise_var θ)
  refine le_trans ?_ ht
  apply pmfMean_mono
  intro ω _
  by_cases hbad : P.acceptCondition θ ω ∧
      P.carrier.loss θ - P.certifiedDrop θ ω
        < P.carrier.loss (P.carrier.step θ (P.certifiedStepSize θ ω))
  · have hnr : P.radius ≤ P.noise θ ω := by
      by_contra hcon
      push Not at hcon
      exact absurd (certified_descent_of_noise_le P θ ω hcon.le hbad.1)
        (not_le.mpr hbad.2)
    simp [hbad, hnr]
  · have h0 : (if P.acceptCondition θ ω ∧
        P.carrier.loss θ - P.certifiedDrop θ ω
          < P.carrier.loss (P.carrier.step θ (P.certifiedStepSize θ ω))
        then (1 : ℝ) else 0) = 0 := by simp [hbad]
    rw [h0]
    split_ifs <;> norm_num

/-- The refusal path is a theorem: when the accept condition fails,
the controller holds the state ENTIRELY (the C363 `Hold` semantics —
`hold_rollback_total`), so the loss is exactly preserved.  Refusing
is always safe; the central theorem certifies accepting. -/
theorem hold_refusal_safe (P : StochasticProposal Θ Ω) (θ : Θ) (ω : Ω)
    (_h : ¬ P.acceptCondition θ ω) :
    P.carrier.loss (Hagi.State.applyStep θ Hagi.State.Outcome.hold)
      = P.carrier.loss θ := by
  rw [Hagi.State.hold_rollback_total]

/-! ## Stage 5 — the CertStochasticStep packaging -/

/-- The packaged certificate (C356 pattern): if additionally the
estimated conservative alignment is uniformly at least `a₀` over the
noise space and every draw is accepted, the accepted step is a
`CertStochasticStep` with the constant drop
`a₀²/(4(Ĉ+u))` and failure `exp(−r²/(4σ))` — the form that drops
into probabilistic consumers. -/
noncomputable def stochastic_safe_step_certificate
    (P : StochasticProposal Θ Ω) (θ : Θ) (a₀ : ℝ)
    (hσ : 0 < P.noiseVar) (hr : 0 < P.radius)
    (hrc : P.noiseBound * P.radius ≤ 2 * P.noiseVar)
    (hCu : 0 < P.curvEst + P.curvUnc) (h₀ : 0 < a₀)
    (hfloor : ∀ ω, a₀ ≤ P.alignEst θ ω - P.radius)
    (hacc : ∀ ω, P.acceptCondition θ ω) :
    CertStochasticStep (P.noiseLaw θ)
      (fun ω => P.carrier.loss θ
        - P.carrier.loss (P.carrier.step θ (P.certifiedStepSize θ ω))) where
  drop := a₀ ^ 2 / (4 * (P.curvEst + P.curvUnc))
  drop_pos := div_pos (pow_pos h₀ 2) (mul_pos (by norm_num) hCu)
  failure := Real.exp (-P.radius ^ 2 / (4 * P.noiseVar))
  descent_whp := by
    have hsw : ∀ ω : Ω, (if P.noise θ ω ≤ P.radius then (1 : ℝ) else 0)
        + (if P.radius ≤ P.noise θ ω then (1 : ℝ) else 0) ≥ 1 := by
      intro ω
      by_cases h : P.noise θ ω ≤ P.radius
      · by_cases h2 : P.radius ≤ P.noise θ ω
        · simp [h, h2]
        · simp [h, h2]
      · have h2 : P.radius ≤ P.noise θ ω := (not_le.mp h).le
        simp [h, h2]
    have hsum : (1 : ℝ) ≤ pmfMean (P.noiseLaw θ)
        (fun ω => (if P.noise θ ω ≤ P.radius then (1 : ℝ) else 0)
          + (if P.radius ≤ P.noise θ ω then (1 : ℝ) else 0)) := by
      calc (1 : ℝ) = pmfMean (P.noiseLaw θ) 1 := (pmfMean_const _ 1).symm
        _ ≤ _ := pmfMean_mono _ (fun ω _ => hsw ω)
    rw [pmfMean_add] at hsum
    have ht := noise_tail_le (P.noiseLaw θ) (P.noise θ) P.noiseBound
      P.noiseVar P.radius hσ hr hrc (P.noise_bounded θ) (P.noise_mean θ)
      (P.noise_var θ)
    have hge : pmfMean (P.noiseLaw θ)
        (fun ω => if P.noise θ ω ≤ P.radius then (1 : ℝ) else 0)
        ≥ 1 - Real.exp (-P.radius ^ 2 / (4 * P.noiseVar)) := by linarith
    refine le_trans hge ?_
    apply pmfMean_mono
    intro ω _
    by_cases h : P.noise θ ω ≤ P.radius
    · have hd := certified_descent_of_noise_le P θ ω h (hacc ω)
      have hx : a₀ ≤ P.alignEst θ ω - P.radius := hfloor ω
      have hmono : a₀ ^ 2 / (4 * (P.curvEst + P.curvUnc))
          ≤ P.certifiedDrop θ ω := by
        have hx2 : 0 < P.alignEst θ ω - P.radius := by
          have := hfloor ω
          linarith
        unfold StochasticProposal.certifiedDrop
        have hsq : a₀ ^ 2 ≤ (P.alignEst θ ω - P.radius) ^ 2 := by nlinarith
        have hy4 : (0 : ℝ) < 4 * (P.curvEst + P.curvUnc) := by
          have := hCu
          nlinarith
        rw [div_le_div_iff₀ hy4 hy4]
        nlinarith
      have hgood : a₀ ^ 2 / (4 * (P.curvEst + P.curvUnc))
          ≤ P.carrier.loss θ
            - P.carrier.loss (P.carrier.step θ (P.certifiedStepSize θ ω)) := by
        linarith
      simp [h, hgood]
    · have h0 : (if P.noise θ ω ≤ P.radius then (1 : ℝ) else 0) = 0 := by
        simp [h]
      rw [h0]
      split_ifs <;> norm_num

/-! ## Stage 6 — the CertStepGen adapter (Certificate arrow) -/

variable {TaskId : Type*}

/-- The system metrics of the adapter: the objective IS the carrier
loss; risk and budget are state-dependent zero channels
(`loss s * 0`, the `StepProvider.quadMetrics` pattern) and the task
tag is constant — the adapter certifies the OPTIMIZATION step, not
the resource ledger: those channels are spent zero and kept whole. -/
noncomputable def proposalMetrics (U : UniversalSafeStep Θ)
    (t : TaskId) : Hagi.Cert.SystemMetrics Θ TaskId where
  objective := U.loss
  risk := fun s => U.loss s * 0
  budget := fun s => U.loss s * 0
  task := fun _ => t

/-- The CertStepGen adapter (the audit's Certificate arrow): an
ACCEPTED step on a good draw is a certified step of the general
kernel at the zero delta level — positive certified drop, real
descent (from `certified_descent_of_noise_le`), the resource
channels spent zero and kept whole, floors as an explicit
premise-form binder.  Composed trajectories telescope via
`trajectoryTelescope` (the C353 kernel law, cited not reproved). -/
noncomputable def acceptStepCert (P : StochasticProposal Θ Ω)
    (t : TaskId) (obl : Hagi.Cert.StepObligations TaskId)
    (θ : Θ) (ω : Ω)
    (hnoise : P.noise θ ω ≤ P.radius)
    (hacc : P.acceptCondition θ ω)
    (hfloor : ∀ t', obl.floor t' ≤ P.carrier.loss
      (P.carrier.step θ (P.certifiedStepSize θ ω))) :
    Hagi.Cert.CertStepGen (proposalMetrics P.carrier t) obl
      (fun _ => 0) θ (P.carrier.step θ (P.certifiedStepSize θ ω)) where
  drop := P.certifiedDrop θ ω
  drop_pos := by
    unfold StochasticProposal.certifiedDrop
    exact div_pos (pow_pos hacc.1 2) (mul_pos (by norm_num) hacc.2)
  descent := by
    simpa [proposalMetrics] using
      certified_descent_of_noise_le P θ ω hnoise hacc
  budgetSpend := 0
  budget_next := by simp only [proposalMetrics]; ring
  budget_nonneg := by
    simp only [proposalMetrics]
    exact le_of_eq (mul_zero _).symm
  riskSpend := 0
  riskRem := 0
  risk_next := by simp only [proposalMetrics]; ring
  risk_split := by simp only [proposalMetrics]; ring
  risk_nonneg := by norm_num
  delta := 0
  delta_next := by simp
  delta_nonneg := by simp
  floorsKept := fun t' => hfloor t'

/-! ## Stage 7 — the T-step chaining pointers (cited, not reproved) -/

/-- Chain pointer to the drop telescope of the general kernel (C353 /
C387 `Hagi.Cert.trajectory_telescope_gen`): a trajectory of
`acceptStepCert` steps telescopes — the terminal objective is the
initial objective minus the sum of certified drops. -/
alias trajectoryTelescope := Hagi.Cert.trajectory_telescope_gen

/-- Chain pointer to the end-to-end stochastic learning theorem
(C360): whp descent of the real regularized CE head over the SGD
loop with the Freedman radius — the T-step stochastic head this
module's single-step mechanism composes into. -/
alias stochasticLoop :=
  Hagi.Unified.StochasticCELearning.stochastic_ce_loop_whp_pl

end Hagi.Theory.StochasticSafeStep
