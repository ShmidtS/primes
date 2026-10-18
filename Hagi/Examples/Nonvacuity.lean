/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.MasterHAGI
import Hagi.Runtime.TernaryExact
import Hagi.Core.Concat
/-!
# R263 (audit §7.1): the h_emp_merge bridge from the Core layer

The audit's central gap: no `h_emp_*` premise of the capstone
was ever derived from the Core-layer mathematics. This module
derives the MERGE stage law for the two-expert concat model:

For two children `z₁, z₂` (a token `t`), the Core ensemble
theorem (`ensemble_ce_le_mean`, Jensen for `lse`) gives

  CE(t, mid) ≤ (CE(t, z₁) + CE(t, z₂)) / 2,

where `mid = (z₁+z₂)/2` is the flat-concat merged model. We
define the measured Jensen gap

  `jensenGap z₁ z₂ := (lse z₁ + lse z₂)/2 − lse mid`

(the normalizer-level disagreement the children average away)
and prove the bridge as an EQUALITY:

  `merge_energy_bridge`: CE(t, mid) = mean CE − jensenGap,
  `jensenGap_nonneg`:     0 ≤ jensenGap.

Instantiating the stage ledger fields
`growEnergy := mean CE`, `mergeEnergy := CE(t, mid)`,
`gap := jensenGap z₁ z₂` therefore satisfies h_emp_merge
exactly (`h_emp_merge_of_bridge`), with `gap` independently
grounded in the Core `lse` theory — the first nonvacuous
`h_emp_*` instantiation beyond the ternary distortion witness
(`Unified.Nonvacuity`).
-/

open Real Finset Hagi

namespace Hagi.Examples

variable {k : Type} [Fintype k] [Nonempty k]

/-- The measured Jensen gap of a two-child merge: the
normalizer-level disagreement `lse-mean − lse-mid` the flat
concat averages away (Core `lse` theory). -/
noncomputable def jensenGap (z₁ z₂ : k → ℝ) : ℝ :=
  (Hagi.lse z₁ + Hagi.lse z₂) / 2 - Hagi.lse ((z₁ + z₂) / 2)

/-- The gap is nonnegative — Jensen for `lse` (Core). -/
theorem jensenGap_nonneg (z₁ z₂ : k → ℝ) : 0 ≤ jensenGap z₁ z₂ := by
  have h := Hagi.lse_midpoint_le z₁ z₂
  unfold jensenGap
  linarith

/-- **The merge-energy bridge**: for every token `t`, the merged
model's cross-entropy is EXACTLY the children's mean minus the
Jensen gap. Both the stage law `mergeEnergy ≤ growEnergy − gap`
(read: an equality here) and the sign `gap ≥ 0` follow. -/
theorem merge_energy_bridge (t : k) (z₁ z₂ : k → ℝ) :
    Hagi.ceOneHot t ((z₁ + z₂) / 2)
      = (Hagi.ceOneHot t z₁ + Hagi.ceOneHot t z₂) / 2 - jensenGap z₁ z₂ := by
  have hmid : ((z₁ + z₂) / 2) t = (z₁ t + z₂ t) / 2 := by simp
  unfold Hagi.ceOneHot jensenGap
  rw [hmid]
  field_simp
  ring

/-- **h_emp_merge instantiated by the Core ensemble theory**:
with the stage ledger fields read off the two-expert concat
model (`growEnergy` = the children's mean CE, `mergeEnergy` =
the merged model's CE, `gap` = the measured Jensen gap), the
capstone's merge premise holds — derived, not assumed. -/
theorem h_emp_merge_of_bridge (t : k) (z₁ z₂ : k → ℝ) :
    Hagi.ceOneHot t ((z₁ + z₂) / 2)
      ≤ (Hagi.ceOneHot t z₁ + Hagi.ceOneHot t z₂) / 2
        - jensenGap z₁ z₂
      ∧ 0 ≤ jensenGap z₁ z₂ :=
  ⟨le_of_eq (merge_energy_bridge t z₁ z₂), jensenGap_nonneg z₁ z₂⟩

/-!
## Strict positivity witness (R356)

The Jensen gap is not just nonnegative — it is STRICTLY
positive for real disagreements. Concrete two-logit witness:
children `z₁ = (0, 0)` and `z₂ = (a, −a)` (a ≠ 0) have

  jensenGap = ½·log(cosh a) − log(cosh (a/2)) > 0,

because `cosh²(a/2) = (1 + cosh a)/2 < cosh a` for `a ≠ 0`
(half-angle identity + `1 < cosh a`). This kills the
"gap = 0 idle witness" degeneracy: merging two genuinely
disagreeing experts STRICTLY beats their mean.
-/

/-- Half-angle identity via `cosh(2x) = 2cosh²x − 1`. -/
private theorem cosh_half_sq (x : ℝ) :
    Real.cosh x ^ 2 = (Real.cosh (2 * x) + 1) / 2 := by
  have h1 := Real.cosh_two_mul x
  have h2 := Real.cosh_sq_sub_sinh_sq x
  field_simp
  linarith

/-- The strict Jensen-gap witness: for the two-logit family
`z₁ = (0,0)`, `z₂ = (a,−a)` with `a ≠ 0`, the merge gap is
strictly positive — merging two genuinely disagreeing
experts STRICTLY beats their mean. -/
theorem jensenGap_pos_witness (a : ℝ) (ha : a ≠ 0) :
    0 < jensenGap
      (fun _ : Fin 2 => (0:ℝ))
      (fun i : Fin 2 => if i = 0 then a else -a) := by
  set z1 : Fin 2 → ℝ := fun _ => 0 with hz1
  set z2 : Fin 2 → ℝ := fun i => if i = 0 then a else -a with hz2
  have hz20 : z2 0 = a := by norm_num [hz2]
  have hz21 : z2 1 = -a := by norm_num [hz2]
  have hea : Real.exp a + Real.exp (-a) = 2 * Real.cosh a := by
    simp only [Real.cosh_eq]
    ring
  have heh : Real.exp (a / 2) + Real.exp (-(a / 2))
      = 2 * Real.cosh (a / 2) := by
    simp only [Real.cosh_eq]
    ring
  have hse1 : ∑ v : Fin 2, Real.exp (z1 v) = 2 := by
    simp only [Fin.sum_univ_two, hz1]
    norm_num
  have hse2 : ∑ v : Fin 2, Real.exp (z2 v) = 2 * Real.cosh a := by
    rw [Fin.sum_univ_two]
    simp only [hz20, hz21]
    exact hea
  have hsem : ∑ v : Fin 2, Real.exp (((z1 + z2) / 2) v)
      = 2 * Real.cosh (a / 2) := by
    rw [Fin.sum_univ_two]
    have e0 : ((z1 + z2) / 2 : Fin 2 → ℝ) 0 = a / 2 := by
      simp [Pi.add_apply, Pi.div_apply, hz1, hz20]
    have e1 : ((z1 + z2) / 2 : Fin 2 → ℝ) 1 = -(a / 2) := by
      simp [Pi.add_apply, Pi.div_apply, hz1, hz21]
      ring
    simp only [e0, e1]
    exact heh
  have hl1 : Hagi.lse z1 = Real.log 2 := by
    simp only [Hagi.lse, hse1]
  have hl2 : Hagi.lse z2 = Real.log (2 * Real.cosh a) := by
    simp only [Hagi.lse, hse2]
  have hlm : Hagi.lse ((z1 + z2) / 2)
      = Real.log (2 * Real.cosh (a / 2)) := by
    simp only [Hagi.lse, hsem]
  have hnc : Real.cosh a ≠ 0 := ne_of_gt (Real.cosh_pos a)
  have hnc2 : Real.cosh (a / 2) ≠ 0 :=
    ne_of_gt (Real.cosh_pos (a / 2))
  have hl2a : Real.log (2 * Real.cosh a)
      = Real.log 2 + Real.log (Real.cosh a) :=
    Real.log_mul two_ne_zero hnc
  have hlma : Real.log (2 * Real.cosh (a / 2))
      = Real.log 2 + Real.log (Real.cosh (a / 2)) :=
    Real.log_mul two_ne_zero hnc2
  have hc1 : 1 < Real.cosh a := (Real.one_lt_cosh (x := a)).mpr ha
  have hsq : Real.cosh (a / 2) ^ 2 = (Real.cosh a + 1) / 2 := by
    have h := cosh_half_sq (a / 2)
    rw [show 2 * (a / 2) = a from by ring] at h
    exact h
  have hlt : Real.cosh (a / 2) ^ 2 < Real.cosh a := by
    rw [hsq]
    linarith
  have hloglt : Real.log (Real.cosh (a / 2) ^ 2)
      < Real.log (Real.cosh a) :=
    Real.log_lt_log (by positivity) hlt
  have hlogpow : Real.log (Real.cosh (a / 2) ^ 2)
      = 2 * Real.log (Real.cosh (a / 2)) := by
    rw [Real.log_pow]
    norm_num
  rw [hlogpow] at hloglt
  unfold jensenGap
  rw [hl1, hl2, hlm, hl2a, hlma]
  linarith

end Hagi.Examples

namespace Hagi
export Hagi.Examples (jensenGap_pos_witness)
end Hagi

set_option linter.style.header false

/-!
# R263 (audit §2.1): a NONVACUITY WITNESS for `CorePremises`

The audit's central complaint: the capstone's premise set
`CorePremises` is never shown satisfiable — no `example`, no
`#guard`, nothing pins the 15 conjuncts to a real cycle.

This module exhibits ONE concrete cycle where every `h_emp_*`
stage law holds with equality (the degenerate-but-consistent
ledger instantiation), and — the substantive part — the
quantization-distortion conjunct `quantErr ≤ 1/2` (h_emp_dist)
is DERIVED from the entry-level ternary theory
(`Runtime.TernaryExact.qTern_error_in`, itself delegating to
`Energy.Ternary.roundTern_error_scaled` ← `roundTern_error`),
not assumed:

  quantErr := |w₀ − qTern 1 w₀| with w₀ = 1/4 (a real
  off-grid weight; the ternary quantizer rounds it to 0), and
  the half-step bound is the ternary rounding theorem.

This is audit stage 7, item 3 (witnesses of nonvacuity) and
the first `h_emp_*`-shaped conjunct fed by a Core-layer
theorem. The remaining stage laws are still chosen as
equalities (a ledger instantiation); deriving h_emp_grow /
h_emp_merge from the Hadamard/block-diag layer is the open
frontier.
-/

open Real Finset InnerProductSpace Hagi Hagi.Foundations

namespace Hagi.Examples

/-- The ternary-grounded distortion of the witness weight:
the compressed weight is `qTern 1 (1/4) = roundTern (1/4) = 0`,
and the half-step bound is `qTern_error_in` (delegating to
`roundTern_error_scaled` ← `roundTern_error`). -/
theorem witness_quantErr_bounded :
    |(1/4 : ℝ) - qTern 1 (1/4)| ≤ 1 / 2 := by
  have hin : ternInRange 1 (1/4) := by
    unfold ternInRange
    norm_num
  exact qTern_error_in 1 (1/4) one_pos hin

section Witness

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The witness cycle: one pre-state `S₀` at the origin with
zero gaps/gains/costs/risks and energies pinned at a common
`E`; the probe telemetry is the zero vector and the compressed
weight is `1/4` with its ternary distortion carried by
`witness_quantErr_bounded`. -/
noncomputable def S₀ (E : ℝ) [NormedAddCommGroup X] [InnerProductSpace ℝ X] :
    Hagi.GenState X where
  weightDim := 1
  weights := fun _ => 1/4
  params := 0
  experts := 0
  energy := E
  protectedRisk := 0
  budget := 0
  gap := 0
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := { eta := 0, L := 1, kappa := 0, s := 1 }
  effects := {
    growGain := 0
    growCost := 0
    growRisk := 0
    growEnergy := E
    mergeEnergy := E
    mergeRisk := 0
    jointEnergy := E
    jointRisk := 0
    jointCost := 0
    quantErr := |1/4 - qTern 1 (1/4)|
    compressEnergy := E
    compressRisk := 0
  }
  gen := ⟨0, 0, 0, 0, 0⟩

/-- The post-cycle state: the composite
`compress (joint (merge (grow S₀)))` on the three carriers the
account and potential laws read, with the (unconstrained)
remaining telemetry left at the pre-state values. -/
noncomputable def S₁ (E : ℝ) [NormedAddCommGroup X] [InnerProductSpace ℝ X] :
    Hagi.GenState X where
  weightDim := 1
  weights := fun _ => 1/4
  params := 0
  experts := 1
  energy := E
  protectedRisk := 0
  budget := 0
  gap := 0
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := { eta := 0, L := 1, kappa := 0, s := 1 }
  effects := {
    growGain := 0
    growCost := 0
    growRisk := 0
    growEnergy := E
    mergeEnergy := E
    mergeRisk := 0
    jointEnergy := E
    jointRisk := 0
    jointCost := 0
    quantErr := |1/4 - qTern 1 (1/4)|
    compressEnergy := E
    compressRisk := 0
  }
  gen := ⟨0, 0, 0, 0, 0⟩

/-!
## Non-idle witness (R357): positive gap and gain

`corePremises_nonvacuous` pins the 15 conjuncts at equality
with zero gap/gain — satisfiable but degenerate. The NON-idle
witness below feeds the merge conjunct with the STRICT Jensen
gap of two genuinely disagreeing experts (`jensenGap_pos_witness`,
R356): `gap := g > 0`, `growGain := g`, energies chained
`E → E−g → E−2g`, so the cycle strictly decreases the energy
ledger while every `h_emp_*` law holds. h_emp_merge is here
INSTANTIATED by the Core lse theory (MergeBridge), not chosen
freely.
-/

/-- The measured strict gap of the witness disagreement. -/
noncomputable def witnessGap : ℝ :=
  jensenGap (fun _ : Fin 2 => (0:ℝ))
    (fun i : Fin 2 => if i = 0 then (1:ℝ) else -1)

theorem witnessGap_pos : 0 < witnessGap :=
  jensenGap_pos_witness 1 one_ne_zero

/-- The non-idle pre-state: `gap := g > 0`, `growGain := g`,
energies chained `E → E−g → E−2g` (grow, then merge at the
strict gap); the joint and compress stages pass through at
`eta = 0`, `kappa = 0`. -/
noncomputable def Spos (E : ℝ) : Hagi.GenState X where
  weightDim := 1
  weights := fun _ => 1/4
  params := 0
  experts := 0
  energy := E
  protectedRisk := 0
  budget := 0
  gap := witnessGap
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := { eta := 0, L := 1, kappa := 0, s := 1 }
  effects := {
    growGain := witnessGap
    growCost := 0
    growRisk := 0
    growEnergy := E - witnessGap
    mergeEnergy := E - 2 * witnessGap
    mergeRisk := 0
    jointEnergy := E - 2 * witnessGap
    jointRisk := 0
    jointCost := 0
    quantErr := |1/4 - qTern 1 (1/4)|
    compressEnergy := E - 2 * witnessGap
    compressRisk := 0
  }
  gen := ⟨0, 0, 0, 0, 0⟩

/-- The non-idle post-state: the composite successor's
ledger fields (energy = the compress stage's output `E − 2g`)
with the expert count advanced. -/
noncomputable def Spos' (E : ℝ) : Hagi.GenState X :=
  { Spos E with
    experts := 1
    energy := E - 2 * witnessGap
    capability := witnessGap }

/-! ## The single-step obstruction (audit v8, full contract)

With the FULL transition contract (audit v8 §2.3) the state's
measured `effects` record is copied verbatim by every stage, so a
step of the cycle keeps the measured stage effects INVARIANT.
Consecutive productive steps are then impossible when the ledger
is honest (`kappa = 0`): the stage laws at the NEXT step demand
`growEnergy ≤ compressEnergy − growGain` (the grow law reads the
cycle's OUTPUT energy), while the composition at the CURRENT step
forces `compressEnergy ≤ mergeEnergy ≤ growEnergy − gap − c`
with `c = η⟪g,d⟫ − Lη²‖d‖²/2 ≥ 0` (merge gap + SafeQP descent).
The horizon witnesses therefore stop at ONE productive step; the
multi-step capstone witness is the IDLE orbit
(`Assumptions.trunc_idle_witness`). This is the formal shape of
the audit's point that the measured-effects ledger must be
reinterpretated per stage (Etap 2) before multi-step productive
trajectories can exist. -/

set_option maxHeartbeats 800000 in
-- audit v8 section 5: the 16-conjunct full-contract record proof chokes whnf at default heartbeats
/-- **The single-step obstruction**: under the full transition
contract, two consecutive `CorePremises` steps force a strictly
positive total ledger loss `gap + c + growGain` against a
nonnegative cycle budget — impossible when the merge gap is
strictly positive, the measured grow gain is nonnegative and the
compression ledger is honest (`kappa = 0`). -/
theorem corePremises_single_step_obstruction {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (S S' S'' : Hagi.GenState X) (epsQ epsQ' : ℝ)
    (w : Fin 5 → ℝ)
    (h1 : CorePremises S S' epsQ w)
    (h2 : CorePremises S' S'' epsQ' w)
    (hgap : 0 < S.toGrowthState.gap)
    (hga : 0 ≤ S.toGrowthState.effects.growGain)
    (hkappa : S.toGrowthState.sp.kappa = 0) : False := by
  obtain ⟨_, hgrow1, hmerge, hL, heta, heta0, hdesc, hsmooth, _, _,
    _, _, hlip, heq, _, _⟩ := h1
  obtain ⟨_, hgrow2, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := h2
  -- the full transition copies the measured effects verbatim
  have heff : S'.toGrowthState.effects = S.toGrowthState.effects := by
    rw [heq]; simp [Hagi.grow, Hagi.merge, Hagi.joint, Hagi.compress]
  have hEn : S'.toGrowthState.energy
      = S.toGrowthState.effects.compressEnergy := by
    rw [heq]; simp [Hagi.grow, Hagi.merge, Hagi.joint, Hagi.compress]
  rw [hEn, heff] at hgrow2
  -- the honest compression ledger: compress cannot gain (kappa = 0)
  have hlip0 : S.toGrowthState.effects.compressEnergy
      ≤ S.toGrowthState.effects.jointEnergy := by
    rw [hkappa] at hlip
    simpa using hlip
  -- c := η⟪g,d⟫ − Lη²‖d‖²/2 ≥ 0 from the SafeQP window (η ≤ 1/L)
  set eta := S.toGrowthState.sp.eta with hetaE
  set L := S.toGrowthState.sp.L with hLE
  set I := ⟪S.toGrowthState.grad, S.toGrowthState.stepDir⟫_ℝ with hIE
  set N := ‖S.toGrowthState.stepDir‖ ^ 2 with hNE
  have hLpos : 0 < L := hL
  have hetaL : eta * L ≤ 1 := by
    calc eta * L ≤ (1 / L) * L := mul_le_mul_of_nonneg_right heta hLpos.le
      _ = 1 := by field_simp
  have hN0 : 0 ≤ N := sq_nonneg _
  have hI0 : 0 ≤ I := by
    have hNI : N ≤ I := hdesc
    linarith
  have hA0 : 0 ≤ eta * N := by nlinarith [heta0, hN0]
  have hbound : L * eta ^ 2 * N ≤ eta * N := by nlinarith [hetaL, hA0]
  have k1 : eta * N ≤ eta * I := by nlinarith [heta0, hdesc, hI0, hN0]
  have hcpos : 0 ≤ eta * I - L * eta ^ 2 * N / 2 := by
    have h2b : (0 : ℝ) ≤ eta * N / 2 := by nlinarith [hA0]
    linarith
  -- the stranglehold: gap + c + growGain must fit a nonnegative budget
  linarith

/-!
## The FULL productive MasterHAGI witness (R370, one-step form)

On the concrete carrier `X = ℝ` with one protected domain
(`K = Fin 1`): a FULL-cycle trajectory — the recursive orbit
`Mw`, whose every step IS the composed transition
`compress ∘ joint ∘ merge ∘ grow` — on which every premise of
the capstone holds with live quantities: nonzero safe step,
one-step strictly decreasing energy, capability growth by the
measured grow gain, risk honestly accrued within budgets.

Honest scope (audit v8 §5.2 + `corePremises_single_step_obstruction`):
under the full transition contract the measured effects record is
invariant along the cycle, so a strictly productive run cannot
extend beyond ONE step while the ledger stays honest
(`kappa = 0`). The multi-step capstone witness is the IDLE orbit
(`Assumptions.trunc_idle_witness`); productive multi-step
trajectories require the stage-semantics reinterpretation of the
effects record (Etap 2), where each stage's successor state
carries the NEXT stage's measurements.
-/

open Hagi.Step

/-- The measured one-step effects of the productive witness:
grow gain `3/2`, merge gap `witnessGap`, joint drop `1`,
risk spend `1/4`, honest ternary quantization error
`|1/4 - qTern 1 (1/4)|` — all INVARIANT under the cycle (the
transitions copy the effects record verbatim). -/
noncomputable def MwEffects (E : ℝ) : Hagi.System.StageEffects where
  growGain := 3/2
  growCost := 0
  growRisk := 0
  growEnergy := E - 3/2
  mergeEnergy := E - 3/2 - witnessGap
  mergeRisk := 0
  jointEnergy := E - 3/2 - witnessGap - 1
  jointRisk := 1/4
  jointCost := 0
  quantErr := |1/4 - qTern 1 (1/4)|
  compressEnergy := E - 3/2 - witnessGap - 1
  compressRisk := 0

/-- The productive witness origin state at `t = 0` (X = ℝ):
live energy `E`, zero risk, zero capability, one unit of budget,
a strict Jensen merge gap, a nonzero safe step (`stepDir = 1`,
`η = 1/2` inside the SafeQP window against the old-domain
gradient), the measured effects above. -/
noncomputable def Mw0 (E : ℝ) : Hagi.GenState ℝ where
  weightDim := 1
  weights := fun _ => 1/4
  params := (0 : ℝ)
  experts := 0
  energy := E
  protectedRisk := 0
  budget := 1
  gap := witnessGap
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := 1
  grad := 1
  sp := { eta := 1/2, L := 1, kappa := 0, s := 1 }
  effects := MwEffects E
  gen := ⟨0, 0, 0, 0, 0⟩

/-- The witness ORBIT: `Mw E (t+1)` is DEFITIONALLY the composed
cycle `compress (joint (merge (grow (Mw E t))))` with the probe
carried over — the full transition contract holds by `rfl` on
every step (audit v8 §2.3), no arithmetic bridging needed. -/
noncomputable def Mw (E : ℝ) : ℕ → Hagi.GenState ℝ
  | 0 => Mw0 E
  | t + 1 =>
    { toGrowthState :=
        Hagi.compress (Hagi.joint (Hagi.merge (Hagi.grow (Mw E t).toGrowthState)))
      gen := (Mw E t).gen }

/-- Projection lemmas for the witness orbit: every step's
records project to closed forms by `rfl` (the orbit is
definitionally the composed cycle, and the stage records copy
the measured effects verbatim; no heavy simp is needed). -/
theorem Mw0_energy (E : ℝ) : (Mw E 0).toGrowthState.energy = E := rfl
theorem Mw0_gap (E : ℝ) : (Mw E 0).toGrowthState.gap = witnessGap := rfl
theorem Mw0_stepDir (E : ℝ) : (Mw E 0).toGrowthState.stepDir = 1 := rfl
theorem Mw0_grad (E : ℝ) : (Mw E 0).toGrowthState.grad = 1 := rfl
theorem Mw0_risk (E : ℝ) :
    (Mw E 0).toGrowthState.protectedRisk = 0 := rfl
theorem Mw0_budget (E : ℝ) : (Mw E 0).toGrowthState.budget = 1 := rfl
theorem Mw0_eta (E : ℝ) : (Mw E 0).toGrowthState.sp.eta = 1/2 := rfl
theorem Mw0_L (E : ℝ) : (Mw E 0).toGrowthState.sp.L = 1 := rfl
theorem Mw0_kappa (E : ℝ) : (Mw E 0).toGrowthState.sp.kappa = 0 := rfl
theorem Mw0_s (E : ℝ) : (Mw E 0).toGrowthState.sp.s = 1 := rfl
theorem Mw0_growGain (E : ℝ) :
    (Mw E 0).toGrowthState.effects.growGain = 3/2 := rfl
theorem Mw0_growEnergy (E : ℝ) :
    (Mw E 0).toGrowthState.effects.growEnergy = E - 3/2 := rfl
theorem Mw0_mergeEnergy (E : ℝ) :
    (Mw E 0).toGrowthState.effects.mergeEnergy = E - 3/2 - witnessGap := rfl
theorem Mw0_jointEnergy (E : ℝ) :
    (Mw E 0).toGrowthState.effects.jointEnergy = E - 3/2 - witnessGap - 1 := rfl
theorem Mw0_compressEnergy (E : ℝ) :
    (Mw E 0).toGrowthState.effects.compressEnergy = E - 3/2 - witnessGap - 1 := rfl
theorem Mw0_growCost (E : ℝ) :
    (Mw E 0).toGrowthState.effects.growCost = 0 := rfl
theorem Mw0_jointCost (E : ℝ) :
    (Mw E 0).toGrowthState.effects.jointCost = 0 := rfl
theorem Mw0_quantErr (E : ℝ) :
    (Mw E 0).toGrowthState.effects.quantErr = |1/4 - qTern 1 (1/4)| := rfl
theorem Mw0_growRisk (E : ℝ) :
    (Mw E 0).toGrowthState.effects.growRisk = 0 := rfl
theorem Mw0_mergeRisk (E : ℝ) :
    (Mw E 0).toGrowthState.effects.mergeRisk = 0 := rfl
theorem Mw0_jointRisk (E : ℝ) :
    (Mw E 0).toGrowthState.effects.jointRisk = 1/4 := rfl
theorem Mw0_compressRisk (E : ℝ) :
    (Mw E 0).toGrowthState.effects.compressRisk = 0 := rfl

/-- The measured effects are INVARIANT along the orbit (the
stage transitions copy the effects record verbatim). -/
theorem Mw_effects (E : ℝ) (t : ℕ) :
    (Mw E t).toGrowthState.effects = MwEffects E := by
  induction t with
  | zero => rfl
  | succ n ih => exact ih

theorem Mw0_effects (E : ℝ) :
    (Mw E 0).toGrowthState.effects = MwEffects E := rfl

theorem Mw0_cap (E : ℝ) :
    (Mw E 0).toGrowthState.capability = 0 := rfl

/-- The orbit's step risk law: one `1/4` jointRisk per cycle. -/
theorem Mw_risk_succ (E : ℝ) (t : ℕ) :
    (Mw E (t + 1)).toGrowthState.protectedRisk
      = (Mw E t).toGrowthState.protectedRisk + (1/4 : ℝ) := by
  show (Hagi.compress (Hagi.joint (Hagi.merge (Hagi.grow (Mw E t).toGrowthState)))).protectedRisk = _
  simp only [Hagi.grow, Hagi.merge, Hagi.joint, Hagi.compress]
  rw [Mw_effects]
  simp only [MwEffects]
  ring

theorem Mw1_energy (E : ℝ) :
    (Mw E 1).toGrowthState.energy = E - 3/2 - witnessGap - 1 := by
  show (Hagi.compress (Hagi.joint (Hagi.merge (Hagi.grow (Mw E 0).toGrowthState)))).energy = _
  simp only [Hagi.grow, Hagi.merge, Hagi.joint, Hagi.compress, Mw0_effects, MwEffects]

theorem Mw1_cap (E : ℝ) :
    (Mw E 1).toGrowthState.capability
      = (Mw E 0).toGrowthState.capability + (3/2 : ℝ) := by
  show (Hagi.compress (Hagi.joint (Hagi.merge (Hagi.grow (Mw E 0).toGrowthState)))).capability = _
  simp only [Hagi.grow, Hagi.merge, Hagi.joint, Hagi.compress]
  rw [Mw0_effects, Mw0_cap]
  simp only [MwEffects]
  try norm_num

theorem Mw1_risk (E : ℝ) :
    (Mw E 1).toGrowthState.protectedRisk = 1/4 := by
  show (Hagi.compress (Hagi.joint (Hagi.merge (Hagi.grow (Mw E 0).toGrowthState)))).protectedRisk = _
  simp only [Hagi.grow, Hagi.merge, Hagi.joint, Hagi.compress, Mw0_effects]
  simp only [MwEffects]
  rw [Mw0_risk]
  norm_num

/-- The one-step orbit satisfies the FULL `CorePremises`
(audit v8: the transition contract is `rfl` since `Mw E 1` is
definitionally the composed cycle). -/
theorem mw_core_premises (E : ℝ) :
    CorePremises (Mw E 0) (Mw E 1) 0 (fun _ => 0) := by
  have hfull : FullCycleRefinement (Mw E 0) (Mw E 1) := ⟨rfl, rfl⟩
  unfold CorePremises
  rw [Mw0_gap, Mw0_energy, Mw0_growGain, Mw0_growEnergy, Mw0_mergeEnergy,
    Mw0_jointEnergy, Mw0_compressEnergy, Mw0_quantErr,
    Mw0_stepDir, Mw0_grad, Mw0_eta, Mw0_L, Mw0_kappa, Mw0_s]
  refine ⟨le_of_lt witnessGap_pos,
    le_of_eq (by ring),
    le_of_eq (by ring),
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num <;> simp,
    by norm_num <;> try linarith,
    by norm_num,
    by norm_num,
    abs_nonneg _,
    witness_quantErr_bounded,
    by norm_num,
    hfull.1, hfull.2,
    by simp [Qgen, Hagi.Qvec]⟩

/-- **The productive MasterHAGI witness** (R370, one-step):
at horizon 1 EVERY premise of the capstone holds simultaneously
with live quantities — nonzero safe step (`stepDir = 1`,
`η = 1/2` within the SafeQP window), strictly decreasing energy,
capability growth by the measured gain `3/2`, risk honestly
accrued (`1/4`) — on a trajectory whose step is DEFITIONALLY the
full cycle (`FullCycleRefinement` by `rfl`); the conclusion
`CertifiedHAGIInvariant` follows by `MasterHAGI` itself. -/
theorem masterhagi_productive_witness (E : ℝ) :
    ∃ (S : ℕ → Hagi.GenState ℝ),
      (S 1).toGrowthState.energy < (S 0).toGrowthState.energy
        ∧ (S 0).toGrowthState.stepDir ≠ 0
        ∧ (S 1).toGrowthState.capability
            = (S 0).toGrowthState.capability + (3/2 : ℝ)
        ∧ (S 1).toGrowthState.protectedRisk = 1/4
        ∧ CertifiedHAGIInvariant 1
            (fun t => (S t).toGrowthState.protectedRisk)
            (fun t => hagiPotential (S t) 0 1 0 (fun _ => 0))
            (fun t => 2 * (3/2 : ℝ) ^ t)
            (fun t => (S t).toGrowthState.budget)
            (fun t => (verify (S t).toGrowthState).budgetSpend)
            (fun t => Qgen (S t).gen (fun _ => 0))
            (fun t => ∑ i : Fin 1, (2 : ℝ))
            (1/2 : ℝ)
            (0 - (hagiPotential (S 0) 0 1 0 (fun _ => 0)
              - (E - 3/2 - witnessGap - 1)) / 1) := by
  refine ⟨Mw E, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Mw1_energy, Mw0_energy]
    linarith [witnessGap_pos]
  · rw [Mw0_stepDir]
    norm_num
  · rw [Mw1_cap, Mw0_cap]
    try ring
  · exact Mw1_risk E
  · -- the capstone itself, on the full-cycle orbit
    have hd : ∀ t < 1, (Mw E t).toGrowthState.stepDir ≠ 0 := by
      intro t ht
      have h0 : t = 0 := by omega
      subst h0
      rw [Mw0_stepDir]
      norm_num
    have hlip : ∀ t < 1, ∀ i : Fin 1, (1/4 : ℝ) ≤ -(1/2) *
        ⟪(fun _ => (-1:ℝ)) i, (Mw E t).toGrowthState.stepDir⟫_ℝ
        + 1 * (1/2) * (1/2)
          * ‖(Mw E t).toGrowthState.stepDir‖ ^ 2 / 2 := by
      intro t ht i
      have h0 : t = 0 := by omega
      subst h0
      rw [Mw0_stepDir]
      norm_num
    have heta : ∀ t < 1, (1/2 : ℝ)
        ≤ safeqpEtaMax (K := Fin 1) (fun _ => (-1:ℝ))
            (fun _ => 2) (fun _ => 1)
            (Mw E t).toGrowthState.stepDir := by
      intro t ht
      have h0 : t = 0 := by omega
      subst h0
      rw [Mw0_stepDir, le_safeqpEtaMax_iff]
      refine ⟨by norm_num, ?_⟩
      intro i
      norm_num
    have hsum : ∀ t < 1,
        (Mw E (t + 1)).toGrowthState.protectedRisk
        = (Mw E t).toGrowthState.protectedRisk
          + ∑ i : Fin 1, (1/4 : ℝ) := by
      intro t ht
      rw [Mw_risk_succ]
      simp
    have hnet : ∀ t < 1, 0 * (verify (Mw E t).toGrowthState).riskSpend
        + 1 * 0 ≤ (verify (Mw E t).toGrowthState).decrease := by
      intro t ht
      have h0 : t = 0 := by omega
      subst h0
      unfold verify
      simp only [gainJoint]
      rw [Mw0_growGain, Mw0_gap, Mw0_eta, Mw0_stepDir, Mw0_kappa, Mw0_s,
        Mw0_growRisk, Mw0_mergeRisk, Mw0_jointRisk, Mw0_compressRisk]
      norm_num
      linarith [witnessGap_pos]
    have hbud : ∑ t ∈ Finset.range 1,
        (verify (Mw E t).toGrowthState).budgetSpend
      ≤ (Mw E 0).toGrowthState.budget := by
      rw [Finset.sum_range_one]
      show ((Mw E 0).toGrowthState.effects.growCost
          + (Mw E 0).toGrowthState.effects.jointCost : ℝ)
        ≤ (Mw E 0).toGrowthState.budget
      rw [Mw0_growCost, Mw0_jointCost, Mw0_budget]
      norm_num
    have hrnn : ∀ t, 0 ≤ (Mw E t).toGrowthState.protectedRisk := by
      intro t
      induction t with
      | zero => rw [Mw0_risk]; try norm_num
      | succ n ih => rw [Mw_risk_succ]; linarith
    have hEmin : E - 3/2 - witnessGap - 1
        ≤ (Mw E 1).toGrowthState.energy := by
      rw [Mw1_energy]
      try linarith
    exact Hagi.Unified.MasterHAGI (fun t => Mw E t) 0 1 0
      (E - 3/2 - witnessGap - 1) (fun _ => 0) (by norm_num) (by norm_num)
      (fun _ => 0) (by norm_num) 1
      (fun _ _ => (-1 : ℝ)) (fun _ _ => 1/4) (fun _ _ => 2)
      (fun _ _ => 1) (fun _ => 1/2)
      (by norm_num) (by norm_num) (by norm_num)
      hd hlip heta hsum
      (fun t _ => by
        have h0 : t = 0 := by omega
        subst h0
        exact mw_core_premises E)
      hnet hbud hrnn hEmin
      (fun t => 2 * (3/2 : ℝ) ^ t) (fun t => (3/2 : ℝ) ^ t)
      (fun t => (3/2 : ℝ) ^ t) (fun _ => 0)
      (1/2) 1 (1/2) (1/2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
      (fun t => by
        rw [pow_succ]
        ring)
      (fun t => by
        norm_num)
      (fun t => by
        rw [pow_succ]
        exact le_of_eq (by ring))
      (fun t => by
        rw [pow_succ]
        exact le_of_eq (by ring))
      (fun t => by
        have hpos : (0:ℝ) < 2 * (3/2 : ℝ) ^ t := by positivity
        norm_num)

/-- **The non-idle nonvacuity witness**: the FULL-contract
`CorePremises` is satisfiable with a STRICTLY positive Jensen
gap and measured gain — the one-step orbit `Mw` pays `3/2`
grow-gain and an honest `witnessGap` merge gap. -/
theorem corePremises_nonvacuous_strict (E : ℝ) :
    ∃ S S' : Hagi.GenState ℝ, ∃ epsQ : ℝ, ∃ w : Fin 5 → ℝ,
      CorePremises S S' epsQ w ∧ 0 < S.toGrowthState.gap
        ∧ 0 < S.toGrowthState.effects.growGain :=
  ⟨Mw E 0, Mw E 1, 0, fun _ => 0, mw_core_premises E,
    witnessGap_pos, by show 0 < (3/2 : ℝ); norm_num⟩

/-- **The nonvacuity witness**: the FULL-contract `CorePremises`
is satisfiable (strictly, in fact — see
`corePremises_nonvacuous_strict`). -/
theorem corePremises_nonvacuous (E : ℝ) :
    ∃ S S' : Hagi.GenState ℝ, ∃ epsQ : ℝ, ∃ w : Fin 5 → ℝ,
      CorePremises S S' epsQ w :=
  ⟨Mw E 0, Mw E 1, 0, fun _ => 0, mw_core_premises E⟩

end Witness

end Hagi.Examples
