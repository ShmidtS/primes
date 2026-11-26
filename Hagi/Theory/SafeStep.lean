/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Cert.StepGen
import Hagi.Model.CEGlobalConvergence
import Hagi.Model.CEMarginPL
import Hagi.Probability.Concentration
import Hagi.Runtime.TernaryExact
import Hagi.State.CanonicalTrainState
import Hagi.Theory.CEChain
import Hagi.Theory.Compression
import Hagi.Unified.StochasticCELearning

/-!
# The central stochastic safe step with the Freedman radius

The CENTRAL theorem of the unified proof chain: ONE
certified decision mechanism for every update.  Given a proposal
(direction from ANY provider, an estimated alignment, an estimated
curvature) and a state-conditioned noise model, the controller EITHER

* ACCEPTS: `0 < Â − r ∧ 0 < Ĉ + u`, executes the conservative step
  `η = (Â − r) / (2 (Ĉ + u))` and — with high probability
  `1 − exp(−r²/(4σ))` over the minibatch draw — the realized loss
  obeys `L(θ + ηd) ≤ L(θ) − (Â − r)²/(4(Ĉ+u))`, OR
* REFUSES: the accept condition fails and the controller holds the
  state ENTIRELY (`Hold` path — a theorem: nothing changes,
  `hold_refusal_safe`).

The radius `r` is DERIVED from the existing Freedman machinery: the
single-draw variance-form tail `noise_tail_le`
(`P[g ≥ r] ≤ exp(−r²/(4σ))` in the regime `c·r ≤ 2σ`) is the
one-measurement instance of `Hagi.Probability.freedman_variance_radius`
applied to the alignment estimator
`Â(θ, ω) = A(θ) + noise(θ, ω)` on one minibatch.

## Composition

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
  packaging under a uniform alignment floor.
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
  data-dependent (any `DirectionProvider`-style proposal), but
  it is fixed BEFORE the measurement — it lives in the deterministic
  carrier `U` and the noise premises are conditioned on the state
  (`noiseLaw` is a function of `θ`, matching the conditioning
  `∀ a ∈ (markovLaw …).support`).  The tail statement is about the
  noise GIVEN the state and direction, never about selecting `d`.
- The variance-form regime `c·r ≤ 2σ` is a premise;
  outside it the radius `exp(−r²/(4(σ + c·r)))` applies and is
  NOT restated here.
- The T-step chaining is cited, not reproved: `stochasticLoop`
  (the whp loop) and `trajectoryTelescope` (drop telescope of the
general kernel).
- `universal_accept_form` proves the drop at the
  TRUE-value step `A/(2C)`; the present module proves the
  conservative-estimate step `(Â−r)/(2(Ĉ+u))` — a different object,
  the one an actual controller can execute.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.StochasticSafeStep

open Hagi.Probability Hagi.Theory.CEChain

/-! ## Stage 1 — the single-draw Freedman tail (the radius of Â) -/

variable {Ω : Type} [Fintype Ω]

/-- The single-draw Freedman tail (the radius of the alignment
estimate): for a bounded, centered noise `g` with variance at most
`σ`, in the variance regime `c·r ≤ 2σ`, the one-sided tail obeys
`P[r ≤ g] ≤ exp(−r²/(4σ))`.  This is the one-measurement instance of
`freedman_variance_radius`: `V := const σ`,
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

/-- The stochastic proposal record: everything the certified
decision mechanism sees before committing.  `carrier` is the
deterministic `UniversalSafeStep` — the direction `d` is
already baked into `carrier.step`, possibly data-dependent but FIXED
BEFORE the measurement; `noiseLaw θ` is the minibatch kernel
conditioned on the state; `noise θ ω` identifies the estimated
alignment `alignEst θ ω = carrier.alignment θ + noise θ ω`;
`curvEst`/`curvUnc` carry the curvature estimate with its explicit
uncertainty binder; `noiseBound`/`noiseVar`/`radius` are the noise
model from which the Freedman radius is read. -/

structure StochasticProposal (Θ : Type) (Ω : Type) [Fintype Ω] where
  /-- The deterministic carrier: loss, η-parametrized update,
  true alignment, true curvature, quadratic majorizer. -/
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
`universal_descent`, at the controller's step size. -/
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

/-- THE CENTRAL THEOREM: under the noise premises
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
the controller holds the state ENTIRELY (`Hold` semantics —
`hold_rollback_total`), so the loss is exactly preserved.  Refusing
is always safe; the central theorem certifies accepting. -/
theorem hold_refusal_safe (P : StochasticProposal Θ Ω) (θ : Θ) (ω : Ω)
    (_h : ¬ P.acceptCondition θ ω) :
    P.carrier.loss (Hagi.State.applyStep θ Hagi.State.Outcome.hold)
      = P.carrier.loss θ := by
  rw [Hagi.State.hold_rollback_total]

/-! ## Stage 5 — the CertStochasticStep packaging -/

/-- The packaged certificate: if additionally the
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

/-- The CertStepGen adapter: an
ACCEPTED step on a good draw is a certified step of the general
kernel at the zero delta level — positive certified drop, real
descent (from `certified_descent_of_noise_le`), the resource
channels spent zero and kept whole, floors as an explicit
premise-form binder.  Composed trajectories telescope via
`trajectoryTelescope` (the kernel law, cited not reproved). -/
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

/-- Chain pointer to the drop telescope of the general kernel (`Hagi.Cert.trajectory_telescope_gen`): a trajectory of
`acceptStepCert` steps telescopes — the terminal objective is the
initial objective minus the sum of certified drops. -/
alias trajectoryTelescope := Hagi.Cert.trajectory_telescope_gen

/-- Chain pointer to the end-to-end stochastic learning theorem:
whp descent of the real regularized CE head over the SGD
loop with the Freedman radius — the T-step stochastic head this
module's single-step mechanism composes into. -/
alias stochasticLoop :=
  Hagi.Unified.StochasticCELearning.stochastic_ce_loop_whp_pl

end Hagi.Theory.StochasticSafeStep

/-! ## CompressedSafeStep — safe step with in-step EF compression (ns Hagi.Theory.CompressedSafeStep preserved) -/

/-!
# Compression-aware safe step with error budget

The compression penalty lives INSIDE the safe step
— optimization and quantization stop being independent systems.
The controller knows how much of the descent margin is EATEN by
compression, and refuses when nothing survives.

The setting: the stored trajectory is COMPRESSED.  Both endpoints of
each step are quantized states, so the certified descent is measured
on the compressed trajectory — the only one that exists in memory.
Each endpoint pays one Lipschitz transport of the quantization error
`ε_q`, giving the exact additive penalty

  `L(compress(step θ η)) ≤ L(compress θ) − η·A + η²·C + 2·L_lip·ε_q`

(both transports used once, no cross terms dropped).  The penalty is
η-INDEPENDENT, so the optimal step size stays `A / (2C)` and the
certified drop becomes `A²/(4C) − 2·L_lip·ε_q`: the accept rule
requires this to be positive — the compression-aware REFUSAL
(`compressedRefusal`: when `A²/(4C) ≤ 2·L_lip·ε_q`, NO step size has
a positive certified margin; holding the state is the only sound
action — the `Hold` path).

The fractional form `A_eff = A − 2·L_lip·ε_q/η` was considered and
REJECTED as dishonest: the penalty does not scale with `η`; dividing
by `η` creates an artificial singularity at small steps and moves
the argmin for no mathematical reason.  The constant-offset form is
exact.

## EF comparison

Plain compression pays `2·L_lip·ε_q` per step — linear in the
horizon.  With error feedback the iterate deviation is the EXACT
endpoint identity `xC n − xF n = η•(e n − e 0)`
(`Hagi.Unified.ErrorFeedback.ef_iterate_shadow`), so the
Lipschitz transport pays ONCE, at the endpoints: the penalty is
`L_lip·2·η·√B` under a residual barrier `nrm2 (e t) ≤ B`
(`Hagi.Unified.ThrComp.thrComp_barrier` instantiates
`B = card·τ²` absolutely) — CONSTANT in the horizon.  The crossover
`ef_crossover_ternary_thr`: the EF penalty beats the plain penalty
once `2·η·τ ≤ (s/2)·n` (the `√card` factors cancel exactly).

## Honest ledger: estimated vs derived vs binder

- BINDERS (premise-form, per-model): the Lipschitz constant `L_lip`
  (`transport`, the `gridQ_energy_bound` pattern).  The only PROVED
  Lipschitz law for the CE objective is logit-level
  (`Model.CEQuantized.ceOneHot_le_of_abs_sub_le`: one-hot CE is
  2-Lipschitz in a uniform logit displacement); a parameter-level
  `L_lip` needs the head's logit-map Lipschitz constant and stays a
  per-model premise.  The distance is an abstract symmetric
  pseudometric (`dist`); the Euclidean instantiation `dist2` below
  makes `ε_q = √card·s/2` a THEOREM for `qTern`
  (`ternaryCompress_l2_le`).
- DERIVED: the penalty `2·L_lip·ε_q`, the adjusted certified drop,
  the unchanged step size `A/(2C)`, the EF crossover.
- Integration (documented, not reproved): the stochastic
  central step composes by the same algebra — its accept condition
  `0 < Â−r ∧ 0 < Ĉ+u` with the certified drop
  `(Â−r)²/(4(Ĉ+u))` folds the same constant penalty into the drop
  comparison; the refusal theorem there (`hold_refusal_safe`) covers
  the refusal path verbatim.

## Honest scope

- The compression operator itself is abstract (`compress` with the
  error binder `compress_err`); `ternaryCompress` is the concrete
  ternary instantiation, in-range only (`ternInRange` per
  coordinate — the saturation tail `satTail` is outside).
- The EF theorems take the shadow identity as a premise (cite,
  not reprove — the StochasticSafeStep citing pattern), with the
  proved `thrComp_barrier` as the documented instantiation of the
  residual barrier.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.CompressedSafeStep

open Hagi.Theory.CEChain Hagi.Theory.StochasticSafeStep Hagi.Runtime
open Hagi.Unified.DescentCore

/-! ## Stage 1 — the compressed-parameter carrier -/

/-- The compression data of a safe step: a deterministic
`UniversalSafeStep` carrier plus a compression operator with
its error budget.  The Lipschitz constant `lip` is a per-model
PREMISE binder (the `gridQ_energy_bound` pattern); the quantization
error `eps_q` bounds the displacement of every compressed state from
its exact state. -/
structure CompressedParams (Θ : Type) where
  /-- The deterministic safe-step carrier (loss, update, A, C, majorizer). -/
  carrier : UniversalSafeStep Θ
  /-- A symmetric pseudo-distance on parameter states. -/
  dist : Θ → Θ → ℝ
  /-- The distance is symmetric. -/
  dist_symm : ∀ a b : Θ, dist a b = dist b a
  /-- The distance is nonnegative. -/
  dist_nonneg : ∀ a b : Θ, 0 ≤ dist a b
  /-- The per-model Lipschitz constant of the loss in `dist`. -/
  lip : ℝ
  /-- The Lipschitz constant is nonnegative. -/
  lip_nonneg : 0 ≤ lip
  /-- The per-step quantization error budget. -/
  eps_q : ℝ
  /-- The error budget is nonnegative. -/
  eps_nonneg : 0 ≤ eps_q
  /-- The compression operator. -/
  compress : Θ → Θ
  /-- Lipschitz transport: the loss moves by at most `lip * dist`. -/
  transport : ∀ a b : Θ,
    carrier.loss a ≤ carrier.loss b + lip * dist a b
  /-- The compressed state is within `eps_q` of the exact state. -/
  compress_err : ∀ θ : Θ, dist θ (compress θ) ≤ eps_q

namespace CompressedParams

/-- One-endpoint Lipschitz transport: compressing a state costs at
most `lip * eps_q` of loss — the price of ONE quantized endpoint. -/
theorem lipschitz_transport (P : CompressedParams Θ) (θ : Θ) :
    P.carrier.loss (P.compress θ) ≤ P.carrier.loss θ + P.lip * P.eps_q := by
  have hbd : P.dist (P.compress θ) θ ≤ P.eps_q := by
    rw [P.dist_symm (P.compress θ) θ]; exact P.compress_err θ
  have hb : P.lip * P.dist (P.compress θ) θ ≤ P.lip * P.eps_q :=
    mul_le_mul_of_nonneg_left hbd P.lip_nonneg
  have h := P.transport (P.compress θ) θ
  linarith [h, hb]

/-- MAIN THEOREM: the safe step WITH the
compression penalty folded in.  Executing the step at the exact
state but reading BOTH endpoints from compressed storage, the loss
obeys the universal majorizer law with the exact additive penalty
`2·L_lip·ε_q` — one transport per endpoint, no cross terms.  The
system knows how much descent margin compression eats. -/
theorem compressed_safe_step (P : CompressedParams Θ) (θ : Θ)
    (η : ℝ) (hη : 0 ≤ η) :
    P.carrier.loss (P.compress (P.carrier.step θ η))
      ≤ P.carrier.loss (P.compress θ) - η * P.carrier.alignment θ
        + η ^ 2 * P.carrier.curvature θ + 2 * P.lip * P.eps_q := by
  have hbdS : P.dist (P.compress (P.carrier.step θ η))
      (P.carrier.step θ η) ≤ P.eps_q := by
    rw [P.dist_symm (P.compress (P.carrier.step θ η)) (P.carrier.step θ η)]
    exact P.compress_err (P.carrier.step θ η)
  have hnear0 : P.lip * P.dist θ (P.compress θ) ≤ P.lip * P.eps_q :=
    mul_le_mul_of_nonneg_left (P.compress_err θ) P.lip_nonneg
  have hnear : P.lip * P.dist (P.compress θ) θ ≤ P.lip * P.eps_q := by
    rw [P.dist_symm (P.compress θ) θ]
    exact hnear0
  have hfar : P.lip * P.dist (P.compress (P.carrier.step θ η))
      (P.carrier.step θ η) ≤ P.lip * P.eps_q :=
    mul_le_mul_of_nonneg_left hbdS P.lip_nonneg
  have h1 := P.transport θ (P.compress θ)
  have h2 := P.carrier.majorizes θ η hη
  have h3 := P.transport (P.compress (P.carrier.step θ η))
    (P.carrier.step θ η)
  linarith [h1, h2, h3, hnear0, hnear, hfar]

/-- The compression-aware certified drop: the universal drop
`A²/(4C)` minus the exact penalty `2·L_lip·ε_q`.  The optimal step
size is UNCHANGED (`universalStepSize`, `A/(2C)`) because the
penalty does not depend on `η`. -/
noncomputable def compressedCertifiedDrop (P : CompressedParams Θ)
    (θ : Θ) : ℝ :=
  (P.carrier.alignment θ) ^ 2 / (4 * P.carrier.curvature θ)
    - 2 * P.lip * P.eps_q

/-- The accept path: when the compression-aware certified drop is
positive (the penalty has NOT eaten the descent margin), the optimal
step certifies exactly that drop on the compressed trajectory. -/
theorem compressed_descent (P : CompressedParams Θ) (θ : Θ)
    (hC : 0 < P.carrier.curvature θ)
    (hdrop : 0 < compressedCertifiedDrop P θ) :
    P.carrier.loss (P.compress
        (P.carrier.step θ (universalStepSize P.carrier θ)))
      ≤ P.carrier.loss (P.compress θ) - compressedCertifiedDrop P θ := by
  have hη : 0 ≤ universalStepSize P.carrier θ :=
    div_nonneg (P.carrier.alignment_nonneg θ) (by positivity)
  have h := compressed_safe_step P θ (universalStepSize P.carrier θ) hη
  have hkey : universalStepSize P.carrier θ * P.carrier.alignment θ
      - (universalStepSize P.carrier θ) ^ 2 * P.carrier.curvature θ
      = (P.carrier.alignment θ) ^ 2 / (4 * P.carrier.curvature θ) := by
    simp only [universalStepSize]
    field_simp
    ring
  unfold compressedCertifiedDrop at hdrop ⊢
  linarith

/-- The REFUSAL direction (compression-aware): when the penalty eats
the whole descent margin (`A²/(4C) ≤ 2·L_lip·ε_q`), NO step size has
a positive certified margin — the guaranteed descent never beats the
penalty, so the controller holds the state entirely (the safe `Hold`
path `hold_refusal_safe`).
ternary compression is enabled only where it provably does not
destroy the descent budget. -/
theorem compressedRefusal (P : CompressedParams Θ) (θ : Θ)
    (hC : 0 < P.carrier.curvature θ)
    (heat : (P.carrier.alignment θ) ^ 2 / (4 * P.carrier.curvature θ)
      ≤ 2 * P.lip * P.eps_q) (η : ℝ) (hη : 0 ≤ η) :
    η * P.carrier.alignment θ - η ^ 2 * P.carrier.curvature θ
      ≤ 2 * P.lip * P.eps_q := by
  have hkey : (P.carrier.alignment θ) ^ 2 / (4 * P.carrier.curvature θ)
      - (η * P.carrier.alignment θ
          - η ^ 2 * P.carrier.curvature θ)
      = P.carrier.curvature θ
          * (η - P.carrier.alignment θ / (2 * P.carrier.curvature θ)) ^ 2 := by
    field_simp
    ring
  have hsq : (0:ℝ) ≤ P.carrier.curvature θ
      * (η - P.carrier.alignment θ / (2 * P.carrier.curvature θ)) ^ 2 :=
    mul_nonneg hC.le (sq_nonneg _)
  linarith

end CompressedParams

/-! ## Stage 2 — the ternary instantiation of `ε_q` -/

variable {k : Type} [Fintype k]

/-- The concrete ternary compression operator: coordinate-wise
`qTern s` nearest-grid rounding (the `Runtime.TernaryExact`
quantizer). -/
noncomputable def ternaryCompress (s : ℝ) (θ : k → ℝ) : k → ℝ :=
  fun i => qTern s (θ i)

/-- The Euclidean pseudo-distance on parameter vectors (the
instantiation of `CompressedParams.dist` for coordinate quantizers):
the root of the summed squared coordinate displacement. -/
noncomputable def dist2 (x y : k → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i - y i) ^ 2)

/-- The ternary error budget is a THEOREM: compressing every
coordinate in range with `qTern` displaces the vector by at most
`√card · s/2` in `dist2` — half a ternary step per coordinate,
squared and summed.  This is the concrete `ε_q` binder for the
ternary instantiation. -/
theorem ternaryCompress_l2_le (s : ℝ) (hs : 0 < s) (θ : k → ℝ)
    (hin : ∀ i, ternInRange s (θ i)) :
    dist2 (ternaryCompress s θ) θ
      ≤ Real.sqrt ((Fintype.card k : ℝ)) * (s / 2) := by
  have hle : ∀ i : k, (qTern s (θ i) - θ i) ^ 2 ≤ (s / 2) ^ 2 :=
    fun i => by
      have h := qTern_error_in s (θ i) hs (hin i)
      have h2 := abs_le.mp h
      nlinarith [h2.1, h2.2, sq_nonneg (s / 2)]
  have hsq : ∑ i, (qTern s (θ i) - θ i) ^ 2
      ≤ (Fintype.card k : ℝ) * (s / 2) ^ 2 := by
    calc ∑ i, (qTern s (θ i) - θ i) ^ 2
        ≤ ∑ i, (s / 2) ^ 2 := Finset.sum_le_sum fun i _ => hle i
      _ = (Fintype.card k : ℝ) * (s / 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsplit : Real.sqrt ((Fintype.card k : ℝ) * (s / 2) ^ 2)
      = Real.sqrt ((Fintype.card k : ℝ)) * (s / 2) := by
    rw [Real.sqrt_mul (by positivity),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  unfold dist2 ternaryCompress
  exact le_trans (Real.sqrt_le_sqrt hsq) (le_of_eq hsplit)

/-! ## Stage 3 — the trajectory bounds: plain vs EF -/

/-- The full (uncompressed) trajectory telescope: each step obeys
the majorizer, so after `n` steps the loss is below the start minus
the summed per-step margins `η·A − η²·C`. -/
theorem full_step_telescope (U : UniversalSafeStep Θ)
    (θF : ℕ → Θ) (η : ℝ) (hη : 0 ≤ η)
    (hstep : ∀ t : ℕ, θF (t + 1) = U.step (θF t) η) (n : ℕ) :
    U.loss (θF n) ≤ U.loss (θF 0)
      - ∑ t ∈ Finset.range n,
          (η * U.alignment (θF t) - η ^ 2 * U.curvature (θF t)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstepn : U.loss (θF (n + 1)) = U.loss (U.step (θF n) η) := by
      rw [hstep n]
    have hm := U.majorizes (θF n) η hη
    rw [hstepn, Finset.sum_range_succ]
    linarith

/-- The plain compressed trajectory bound: with the exact
trajectory `θF` following the majorizer steps and EVERY stored
iterate compressed (`hstore`), the penalty is paid at EVERY step —
`2·L_lip·ε_q` per step, LINEAR in the horizon. -/
theorem plain_compressed_trajectory (P : CompressedParams Θ)
    (θF : ℕ → Θ) (η : ℝ) (hη : 0 ≤ η)
    (hstepF : ∀ t : ℕ, θF (t + 1) = P.carrier.step (θF t) η)
    (θq : ℕ → Θ) (hstore : ∀ t : ℕ, θq t = P.compress (θF t))
    (n : ℕ) :
    P.carrier.loss (θq n) ≤ P.carrier.loss (θq 0)
      - ∑ t ∈ Finset.range n,
          (η * P.carrier.alignment (θF t)
            - η ^ 2 * P.carrier.curvature (θF t))
      + 2 * P.lip * P.eps_q * (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstoren : P.carrier.loss (θq (n + 1))
        = P.carrier.loss (P.compress (P.carrier.step (θF n) η)) := by
      rw [hstore (n + 1), hstepF n]
    have hstoren0 : P.carrier.loss (θq n)
        = P.carrier.loss (P.compress (θF n)) := by
      rw [hstore n]
    have hm := CompressedParams.compressed_safe_step P (θF n) η hη
    rw [hstoren, Finset.sum_range_succ]
    rw [hstoren0] at ih
    have hcast : ((n + 1 : ℕ) : ℝ) = ((n : ℝ) + 1) := by norm_num
    rw [hcast]
    linarith

/-- The EF endpoint shadow in `dist2`: if the compressed iterate
deviates from the full one by the identity
`xC n − xF n = η•(e n − e 0)` and the residual carries a barrier
`nrm2 (e t) ≤ B` (instantiated by the PROVED
`Hagi.Unified.ThrComp.thrComp_barrier`), the parameter displacement
is at most `2·η·√B` — CONSTANT in the horizon `n`. -/
theorem ef_shadow_dist2 (η : ℝ) (hη : 0 ≤ η)
    (e : ℕ → k → ℝ) (B : ℝ) (hB : ∀ t : ℕ, nrm2 (e t) ≤ B)
    (xC xF : ℕ → k → ℝ)
    (hshadow : ∀ n : ℕ, xC n - xF n = η • (e n - e 0)) (n : ℕ) :
    dist2 (xC n) (xF n) ≤ 2 * η * Real.sqrt B := by
  have hnrm : ∑ i, ((η : ℝ) • (e n - e 0)) i ^ 2
      = η ^ 2 * nrm2 (e n - e 0) :=
    Hagi.Unified.ThrComp.nrm2_smul (k := k) η (e n - e 0)
  have hcoord : ∀ i : k, (e n i - e 0 i) ^ 2
      ≤ 2 * (e n i) ^ 2 + 2 * (e 0 i) ^ 2 := by
    intro i
    nlinarith [sq_nonneg (e n i + e 0 i)]
  have hn0 : (0:ℝ) ≤ nrm2 (e n - e 0) := by
    unfold nrm2
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsum : nrm2 (e n - e 0) ≤ 4 * B := by
    have h1 : nrm2 (e n - e 0)
        ≤ ∑ i, (2 * (e n i) ^ 2 + 2 * (e 0 i) ^ 2) :=
      Finset.sum_le_sum fun i _ => hcoord i
    have h2 : ∑ i, (2 * (e n i) ^ 2 + 2 * (e 0 i) ^ 2)
        = 2 * nrm2 (e n) + 2 * nrm2 (e 0) := by
      unfold nrm2
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum]
    have h3 : 2 * nrm2 (e n) + 2 * nrm2 (e 0) ≤ 4 * B := by
      nlinarith [hB n, hB 0]
    linarith [h1, h2, h3]
  have hnn : (0:ℝ) ≤ 4 * B := by nlinarith [hB n, hn0]
  have hfour : Real.sqrt (4 * B) = 2 * Real.sqrt B := by
    have h := Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) B
    rw [h]; norm_num
  have hfinal : Real.sqrt (η ^ 2 * nrm2 (e n - e 0))
      ≤ Real.sqrt (η ^ 2 * (4 * B)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsplit : Real.sqrt (η ^ 2 * (4 * B))
      = η * (2 * Real.sqrt B) := by
    rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hη, hfour]
  unfold dist2
  rw [show ∑ i, (xC n i - xF n i) ^ 2
      = ∑ i, ((η : ℝ) • (e n - e 0)) i ^ 2 from
    Finset.sum_congr rfl fun i _ => by
      rw [show xC n i - xF n i = (xC n - xF n) i from rfl, hshadow n]]
  calc Real.sqrt (∑ i, ((η : ℝ) • (e n - e 0)) i ^ 2)
      = Real.sqrt (η ^ 2 * nrm2 (e n - e 0)) := by rw [hnrm]
    _ ≤ Real.sqrt (η ^ 2 * (4 * B)) := hfinal
    _ = 2 * η * Real.sqrt B := by rw [hsplit]; ring

/-- The EF compressed step bound: with error feedback the Lipschitz
transport pays only at the ENDPOINTS — the total penalty is
`L_lip·2·η·√B`, CONSTANT in the horizon (the exact shadow
identity, cited as the premise `hshadow`; `hdist` instantiates the
abstract distance by `dist2`). -/
theorem ef_compressed_step_bound
    (P : CompressedParams (k → ℝ))
    (hdist : ∀ x y : k → ℝ, P.dist x y ≤ dist2 x y)
    (η : ℝ) (hη : 0 ≤ η)
    (θF : ℕ → k → ℝ)
    (hstepF : ∀ t : ℕ, θF (t + 1) = P.carrier.step (θF t) η)
    (xC : ℕ → k → ℝ) (e : ℕ → k → ℝ)
    (hshadow : ∀ n : ℕ, xC n - θF n = η • (e n - e 0))
    (B : ℝ) (hB : ∀ t : ℕ, nrm2 (e t) ≤ B) (n : ℕ) :
    P.carrier.loss (xC n) ≤ P.carrier.loss (θF 0)
      - ∑ t ∈ Finset.range n,
          (η * P.carrier.alignment (θF t)
            - η ^ 2 * P.carrier.curvature (θF t))
      + P.lip * (2 * η * Real.sqrt B) := by
  have htele := full_step_telescope P.carrier θF η hη hstepF n
  have hd : P.dist (xC n) (θF n) ≤ 2 * η * Real.sqrt B :=
    le_trans (hdist (xC n) (θF n))
      (ef_shadow_dist2 η hη e B hB xC θF hshadow n)
  have htr := P.transport (xC n) (θF n)
  have hpen : P.lip * P.dist (xC n) (θF n)
      ≤ P.lip * (2 * η * Real.sqrt B) :=
    mul_le_mul_of_nonneg_left hd P.lip_nonneg
  linarith

/-- The quantitative EF-vs-plain penalty comparison (abstract form):
when the endpoint shadow displacement `2·η·√B` fits inside `n`
per-step error budgets `ε_q·n`, the EF penalty is below the plain
compression penalty — the abstract crossover. -/
theorem ef_penalty_le_plain (P : CompressedParams Θ)
    (η B : ℝ) (n : ℕ)
    (hcrossover : 2 * η * Real.sqrt B ≤ P.eps_q * (n : ℝ)) :
    P.lip * (2 * η * Real.sqrt B)
      ≤ 2 * P.lip * P.eps_q * (n : ℝ) := by
  have h3 : P.lip * (2 * η * Real.sqrt B)
      ≤ P.lip * (P.eps_q * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hcrossover P.lip_nonneg
  have h5 : P.lip * (P.eps_q * (n : ℝ)) + P.lip * (P.eps_q * (n : ℝ))
      = 2 * P.lip * P.eps_q * (n : ℝ) := by ring
  have hge : (0:ℝ) ≤ P.lip * (P.eps_q * (n : ℝ)) :=
    mul_nonneg P.lip_nonneg
      (mul_nonneg P.eps_nonneg (Nat.cast_nonneg n))
  linarith [h3, h5, hge]

/-- The INSTANTIATED crossover (EF beats plain, both constants are
theorems): with the threshold compressor's absolute residual barrier
`B = card·τ²` (`Hagi.Unified.ThrComp.thrComp_barrier`) and the
ternary budget `ε_q = √card·s/2`
(`ternaryCompress_l2_le`), the `√card` factors cancel and the EF
penalty beats the plain ternary penalty exactly when
`2·η·τ ≤ (s/2)·n` — a half-step of ternary grid per step against
the residual barrier per step. -/
theorem ef_crossover_ternary_thr (P : CompressedParams (k → ℝ))
    (hcard : (Fintype.card k : ℝ) ≠ 0) (η τ s : ℝ)
    (hτ : 0 < τ) (hs : 0 < s) (n : ℕ)
    (hcrossover : 2 * η * τ ≤ (s / 2) * (n : ℝ)) :
    P.lip * (2 * η * Real.sqrt ((Fintype.card k : ℝ) * τ ^ 2))
      ≤ P.lip * (Real.sqrt ((Fintype.card k : ℝ)) * (s / 2))
          * (n : ℝ) := by
  have hcardpos : (0:ℝ) < Fintype.card k := by positivity
  have hsq : Real.sqrt ((Fintype.card k : ℝ) * τ ^ 2)
      = Real.sqrt ((Fintype.card k : ℝ)) * τ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hτ.le]
  rw [hsq]
  have hl : (0:ℝ) ≤ P.lip * Real.sqrt ((Fintype.card k : ℝ)) :=
    mul_nonneg P.lip_nonneg (Real.sqrt_nonneg _)
  calc P.lip * (2 * η * (Real.sqrt ((Fintype.card k : ℝ)) * τ))
      = P.lip * Real.sqrt ((Fintype.card k : ℝ)) * (2 * η * τ) := by
        ring
    _ ≤ P.lip * Real.sqrt ((Fintype.card k : ℝ))
        * ((s / 2) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hcrossover hl
    _ = P.lip * (Real.sqrt ((Fintype.card k : ℝ)) * (s / 2))
        * (n : ℝ) := by
        ring

end Hagi.Theory.CompressedSafeStep


/-! ## Confinement — PL confinement geometry (ns Hagi.Theory.Confinement preserved) -/

/-!
# Confinement for safe-step dynamics

A safe step that (weakly) decreases the loss keeps the
whole trajectory inside the start sublevel set; if that sublevel set
is bounded (coercivity), the trajectory is CONFINED to a ball — and
on a ball the margin-PL inequality (`Hagi.Model.CEMarginPL.margin_pl_ball`,
μ = `muBall a B = a²·e^{−a·B}/8`) applies at every iterate, turning
the ball-scoped PL into a global-on-the-sublevel PL regime with the
geometric rate `(1 − μ/L)^T`.

## The two halves assembled here

* MONOTONICITY (`sublevel_confinement`, `universal_safeStep_confinement`,
  `plStep_nonincreasing`): any dynamics with `f (s θ) ≤ f θ` stays in
  `{x | f x ≤ f θ₀}` — a one-induction fact. For the CE chain the
  monotone map is the universal safe step (`Theory.CEChain.safeStepMap`,
  drop `A²/4C ≥ 0` from `universal_descent`); for gradient steps it is
  the smoothness-only descent lemma.
* COERCIVITY (`ceReg_sublevel_bounded`, `ceReg_safe_step_confinement`):
  boundedness of the sublevel set. For the ridge objective `ceReg`
  (λ > 0) this is DERIVED from `ceReg_coerce` with the explicit
  radius `√(2·ceReg θ₀/λ)`; for a general objective it is a premise.

## The rate theorem

`safe_step_margin_pl_rate` is `Hagi.Model.CEMarginPL.margin_pl_convergence`
with its confinement premise h_conf DISCHARGED: the iterates of a
smooth gradient step stay in the θ₀-sublevel (monotonicity), the
sublevel lies in the ball `‖x‖ ≤ B` (coercivity premise `h_bounded`),
so the ball-scoped PL applies at every iterate and the geometric rate
follows.

## Limits (what genuinely remains a premise)

- UNREGULARIZED CE sublevel sets are UNBOUNDED (logit shift): for the
  strictly decreasing `scalarCE a` the sublevel of `θ₀` is the ray
  `[θ₀, ∞)`, and the plStep increments `(2/a)·ρ` are positive, so the
  trajectory drifts to +∞ while the loss → 0. Ball confinement is
  FALSE there, not merely unproven; the unregularized margin rate
  keeps its ball premise (`ce_global_convergence_margin` stays SSOT).
  A scalar instantiation of `h_bounded` for `scalarCE` would be
  unsatisfiable (vacuous) — deliberately not stated.
- The PL constant is ball-scoped (`muBall a B`, decreasing in `a·B`);
  the margin condition is a data-dependent premise, not derived.
- Strictly-decreasing safe steps need `A > 0` (majorizer);
  confinement only uses the weak inequality (sublevels are `≤`-sets).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.Confinement

/-! ## Monotone dynamics stay in the start sublevel -/

/-- The confinement induction: if every step weakly decreases the
loss, then every iterate stays in the sublevel set of the start
point.  This is the whole mechanism — everything else is
obtaining the monotonicity and bounding the sublevel. -/
theorem sublevel_confinement {Θ : Type} (s : Θ → Θ) (f : Θ → ℝ)
    (hmono : ∀ θ, f (s θ) ≤ f θ) (θ₀ : Θ) (t : ℕ) :
    f (s^[t] θ₀) ≤ f θ₀ := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (hmono _) ih

/-- With the sublevel set `{x | f x ≤ f θ₀}` contained in a ball
(the coercivity premise, with the center absorbed into `f`/the norm
shift), the monotone trajectory is CONFINED to that ball. -/
theorem ball_confinement_of_sublevel {E : Type} [NormedAddCommGroup E]
    (s : E → E) (f : E → ℝ) (hmono : ∀ θ, f (s θ) ≤ f θ)
    (θ₀ : E) (R' : ℝ) (t : ℕ)
    (h_bounded : ∀ x : E, f x ≤ f θ₀ → ‖x‖ ≤ R') :
    ‖s^[t] θ₀‖ ≤ R' :=
  h_bounded _ (sublevel_confinement s f hmono θ₀ t)

/-! ## The CE-chain universal safe step is monotone -/

/-- The safe-step map of a `UniversalSafeStep`: each point moves to
its safe-step update `U.step θ (universalStepSize U θ)`. -/
noncomputable def safeStepMap {Θ : Type} (U : Theory.CEChain.UniversalSafeStep Θ) :
    Θ → Θ :=
  fun θ => U.step θ (Theory.CEChain.universalStepSize U θ)

/-- Monotonicity of the universal safe step at one point (the
`universal_descent` inequality with `universalDrop ≥ 0`). -/
private theorem universal_safeStep_mono {Θ : Type}
    (U : Theory.CEChain.UniversalSafeStep Θ)
    (hC : ∀ θ : Θ, 0 < U.curvature θ) (θ : Θ) :
    U.loss (safeStepMap U θ) ≤ U.loss θ := by
  have hd := Theory.CEChain.universal_descent U θ (hC θ)
  have hdnn : (0:ℝ) ≤ Theory.CEChain.universalDrop U θ := by
    rw [Theory.CEChain.universalDrop]
    exact div_nonneg (sq_nonneg _)
      (le_of_lt (mul_pos (by norm_num : (0:ℝ) < 4) (hC θ)))
  unfold safeStepMap
  linarith

/-- At positive curvature the universal safe step weakly decreases
the loss (`universal_descent` with `universalDrop ≥ 0`), so the CE
chain (single-sample / batch / gated instances of
`Theory.CEChain.UniversalSafeStep`) is a monotone dynamics and its
trajectories stay in the start sublevel set. -/
theorem universal_safeStep_confinement {Θ : Type}
    (U : Theory.CEChain.UniversalSafeStep Θ)
    (hC : ∀ θ : Θ, 0 < U.curvature θ) (θ₀ : Θ) (t : ℕ) :
    U.loss ((safeStepMap U)^[t] θ₀) ≤ U.loss θ₀ :=
  sublevel_confinement (safeStepMap U) U.loss
    (universal_safeStep_mono U hC) θ₀ t

/-- Ball version: the CE-chain safe-step trajectory is confined once
the start sublevel set is bounded (coercivity premise).  For the
ridge CE this premise is DERIVED (`ceReg_safe_step_confinement`). -/
theorem universal_safeStep_ball_confinement {Θ : Type} [NormedAddCommGroup Θ]
    (U : Theory.CEChain.UniversalSafeStep Θ)
    (hC : ∀ θ : Θ, 0 < U.curvature θ) (θ₀ : Θ) (R' : ℝ) (t : ℕ)
    (h_bounded : ∀ x : Θ, U.loss x ≤ U.loss θ₀ → ‖x‖ ≤ R') :
    ‖(safeStepMap U)^[t] θ₀‖ ≤ R' :=
  ball_confinement_of_sublevel (safeStepMap U) U.loss
    (universal_safeStep_mono U hC) θ₀ R' t h_bounded

/-! ## The gradient step is monotone (smoothness alone) -/

open scoped InnerProductSpace in
/-- Descent lemma, no PL needed: for an `L`-smooth objective (in
inner-product form) the gradient step `plStep` weakly decreases the
loss.  This is the monotonicity key that discharges the confinement
premise of `margin_pl_convergence` below; the proof core is the
smoothness half of `Hagi.Model.CEMarginPL.pl_descent_step_at`. -/
theorem plStep_nonincreasing {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (L : ℝ) (θ : E) (hL : 0 < L)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2) :
    f (Model.CEGlobalConvergence.plStep grad L θ) ≤ f θ := by
  rw [Model.CEGlobalConvergence.plStep]
  have hstep := h_smooth θ (θ - (1 / L) • grad θ)
  have hin : ⟪grad θ, θ - (1 / L) • grad θ - θ⟫_ℝ
      = -(1 / L) * ‖grad θ‖ ^ 2 := by
    rw [show θ - (1 / L) • grad θ - θ = -(1 / L) • grad θ by module,
      inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hin] at hstep
  have hcoef : L / 2 * ((1 / L) ^ 2 * ‖grad θ‖ ^ 2)
      = ‖grad θ‖ ^ 2 / (2 * L) := by field_simp
  have hnorm : ‖θ - (1 / L) • grad θ - θ‖ ^ 2
      = (1 / L) ^ 2 * ‖grad θ‖ ^ 2 := by
    rw [show θ - (1 / L) • grad θ - θ = -(1 / L) • grad θ by module,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    ring
  rw [hnorm, hcoef] at hstep
  have hXY : f θ + -(1 / L) * ‖grad θ‖ ^ 2 + ‖grad θ‖ ^ 2 / (2 * L)
      = f θ - ‖grad θ‖ ^ 2 / (2 * L) := by
    field_simp
    ring
  rw [hXY] at hstep
  have hpos : (0:ℝ) ≤ ‖grad θ‖ ^ 2 / (2 * L) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith

/-! ## The rate theorem: confinement discharges the ball premise -/

open scoped InnerProductSpace in
/-- THE RATE THEOREM.  `margin_pl_convergence` with its
confinement premise h_conf REPLACED by a derivation: the gradient
step is monotone by smoothness alone (`plStep_nonincreasing`), the
monotone trajectory stays in the θ₀-sublevel (`sublevel_confinement`),
and the coercivity premise `h_bounded` (the sublevel set of `θ₀` lies
in the ball `‖x‖ ≤ B`, on which PL holds) confines every iterate to
the ball — so the ball-scoped PL applies along the whole trajectory
and the loss gap contracts geometrically at rate `1 − μ/L`.

Limits: `h_bounded` is DERIVED for coercive objectives (the ridge CE,
`ceReg_safe_step_confinement` below, radius `√(2·ceReg θ₀/λ)`) and is
a data-dependent premise for the unregularized CE, whose sublevel
sets are unbounded (logit shift — see the module docstring). -/
theorem safe_step_margin_pl_rate {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (L μ fstar B : ℝ) (hL : 0 < L) (hμL : μ ≤ L)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (h_floor : ∀ x : E, fstar ≤ f x)
    (h_pl_ball : ∀ x : E, ‖x‖ ≤ B → 2 * μ * (f x - fstar) ≤ ‖grad x‖ ^ 2)
    (θ₀ : E) (T : ℕ)
    (h_bounded : ∀ x : E, f x ≤ f θ₀ → ‖x‖ ≤ B) :
    f ((Model.CEGlobalConvergence.plStep grad L)^[T] θ₀) - fstar
      ≤ (1 - μ / L) ^ T * (f θ₀ - fstar) := by
  have hmono : ∀ θ, f (Model.CEGlobalConvergence.plStep grad L θ) ≤ f θ :=
    fun θ => plStep_nonincreasing f grad L θ hL h_smooth
  exact Model.CEMarginPL.margin_pl_convergence f grad L μ fstar B hL hμL
    h_smooth h_floor h_pl_ball θ₀ T
    (fun t _ => ball_confinement_of_sublevel _ f hmono θ₀ B t h_bounded)

/-! ## The ridge case: coercivity derived -/

variable {V : Type} [Fintype V] [Nonempty V] [DecidableEq V] {d : ℕ}

/-- The sublevel-boundedness theorem for the ridge objective, derived
from coercivity (`ceReg_coerce`): `ceReg ≥ (λ/2)‖θ‖²`, so any
sub-`c` point has `‖θ‖ ≤ √(2·c/λ)`.  The standalone extraction of the
bound that `ceReg_attains` uses internally, here consumed for
confinement instead of attainment. -/
theorem ceReg_sublevel_bounded (X : Matrix V (Fin d) ℝ) (t : V) (lam : ℝ)
    (hlam : 0 < lam) (θ : EuclideanSpace ℝ (Fin d)) {c : ℝ}
    (hle : Model.CEGlobalConvergence.ceReg X t lam θ ≤ c) :
    ‖θ‖ ≤ Real.sqrt (2 * c / lam) := by
  have h := Model.CEGlobalConvergence.ceReg_coerce X t lam hlam.le θ
  have hnn : (0:ℝ) ≤ lam / 2 * ‖θ‖ ^ 2 :=
    mul_nonneg (div_nonneg hlam.le (by norm_num)) (by positivity)
  have hc : (0:ℝ) ≤ c := by linarith [h.trans hle, hnn]
  refine (Real.le_sqrt (norm_nonneg θ)
    (div_nonneg (by linarith) hlam.le)).2 ?_
  rw [le_div_iff₀ hlam, mul_comm]
  have h5 := h.trans hle
  have heq : lam * ‖θ‖ ^ 2 = 2 * (lam / 2 * ‖θ‖ ^ 2) := by ring
  linarith

/-- DERIVED CONFINEMENT for the ridge case: any safe-step dynamics on
the ridge CE (λ > 0) — in particular every `UniversalSafeStep`
instance of `Theory.CEChain` whose loss is `ceReg` — is confined to
the ball of radius `√(2·ceReg θ₀/λ)`, with no confinement premise.
This is the nonvacuity witness for the `h_bounded` premise class of
`safe_step_margin_pl_rate`. -/
theorem ceReg_safe_step_confinement (X : Matrix V (Fin d) ℝ) (t : V) (lam : ℝ)
    (hlam : 0 < lam) (s : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hmono : ∀ θ, Model.CEGlobalConvergence.ceReg X t lam (s θ)
      ≤ Model.CEGlobalConvergence.ceReg X t lam θ)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (τ : ℕ) :
    ‖s^[τ] θ₀‖ ≤
      Real.sqrt (2 * Model.CEGlobalConvergence.ceReg X t lam θ₀ / lam) :=
  ball_confinement_of_sublevel s (Model.CEGlobalConvergence.ceReg X t lam)
    hmono θ₀ _ τ
    (fun x hx => ceReg_sublevel_bounded X t lam hlam x hx)

end Hagi.Theory.Confinement

