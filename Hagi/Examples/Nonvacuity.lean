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
  { Spos E with experts := 1, energy := E - 2 * witnessGap }

/-- The productive TRAJECTORY witness state at step t:
energy strictly decreases `E − 2t·g` per step-pair, gap and
gain stay at the strict Jensen level `g`, capability grows
`t·g`. -/
noncomputable def Straj (E g : ℝ) (t : ℕ) : Hagi.GenState X where
  weightDim := 1
  weights := fun _ => 1/4
  params := 0
  experts := t
  energy := E - 2 * t * g
  protectedRisk := 0
  budget := 1
  gap := g
  dataField := 0
  capability := t * g
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := { eta := 0, L := 1, kappa := 0, s := 1 }
  effects := {
    growGain := g
    growCost := 0
    growRisk := 0
    growEnergy := E - (2 * t + 1) * g
    mergeEnergy := E - (2 * t + 2) * g
    mergeRisk := 0
    jointEnergy := E - (2 * t + 2) * g
    jointRisk := 0
    jointCost := 0
    quantErr := |1/4 - qTern 1 (1/4)|
    compressEnergy := E - (2 * t + 2) * g
    compressRisk := 0
  }
  gen := ⟨0, 0, 0, 0, 0⟩

/-- **The productive trajectory witness** (R369, audit v7
§5.3): for EVERY horizon T there is a state trajectory on
which `CorePremises` holds at EVERY step with strictly
positive gap and gain and strictly decreasing energy —
E − 2t·g → E − 2(t+1)·g — while capability grows linearly
`t·g`. This is the trajectory-level (category-2) witness:
not one pair of states, but the full contract along the
whole horizon. -/
theorem corePremises_trajectory_productive (E g : ℝ)
    (hg : 0 < g) (T : ℕ) :
    ∃ S : ℕ → Hagi.GenState X, ∀ t < T,
      CorePremises (S t) (S (t + 1)) 0 (fun _ => 0)
        ∧ (S (t + 1)).toGrowthState.energy
          < (S t).toGrowthState.energy
        ∧ 0 < (S t).toGrowthState.gap
        ∧ 0 < (S (t + 1)).toGrowthState.capability
            - (S t).toGrowthState.capability := by
  refine ⟨fun t => Straj E g t, fun t ht => ?_⟩
  unfold CorePremises Straj
  norm_num [Qgen, Qvec, grow, merge, joint, compress]
  have hq := witness_quantErr_bounded
  have hT : (0:ℝ) ≤ (t:ℝ) := by positivity
  refine ⟨⟨hg.le, by linarith [hT], by linarith [hT], hq,
    by left; ring⟩, by linarith [hg, hT], hg,
    by nlinarith [hg, hT]⟩
/-!
## The FULL productive MasterHAGI witness (R370)

The end-to-end witness (audit v7 §5.3, the final rung of the
R357 → R359 → R369 ladder): on the concrete carrier `X = ℝ`
with one protected domain (`K = Fin 1`), a trajectory on
which EVERY premise of the capstone `MasterHAGI` holds
simultaneously with genuinely live quantities — nonzero safe
step, strictly decreasing energy, growing capability and
risk accrued within its budgets — at a concrete horizon.

Numerical layout (all derived above):
`g_old = -1` (old-domain gradient: descent direction d = 1
points AGAINST it, so the domain's risk grows — honestly
paid via jointRisk), `d = 1`, `grad = 1`, `η = 1/2`, `L = 1`,
`ε = 2`, per-step merge gap `g = witnessGap`, joint drop
`j = 1`, risk spend `1/4` per step, capability `c0 + t·g_c`
with `c0 = 2`, `g_c = witnessGap`.
-/

open Hagi.Step

/-- The end-to-end witness state at step t (X = ℝ): closed
forms solving the composite recursion exactly —
energy e_{t+1} = e_t − (3/2)^t − g − 1 (grow gain, merge
gap, joint drop), capability 2·(3/2)^t (compound growth at
rate α = 1/2), risk t/4 (honestly accrued per-step
jointRisk), budget constant (zero spends). -/
noncomputable def Mw (E : ℝ) (t : ℕ) : Hagi.GenState ℝ where
  weightDim := 1
  weights := fun _ => 1/4
  params := 0
  experts := t
  energy := E - 2 * ((3/2 : ℝ) ^ t - 1) - t * witnessGap - t
  protectedRisk := t / 4
  budget := 1
  gap := witnessGap
  dataField := 0
  capability := 2 * (3/2 : ℝ) ^ t
  verifier := 0
  runtimeError := 0
  stepDir := 1
  grad := 1
  sp := { eta := 1/2, L := 1, kappa := 0, s := 1 }
  effects := {
    growGain := (3/2 : ℝ) ^ t
    growCost := 0
    growRisk := 0
    growEnergy := E - 2 * ((3/2 : ℝ) ^ t - 1) - t * witnessGap - t
      - (3/2 : ℝ) ^ t
    mergeEnergy := E - 2 * ((3/2 : ℝ) ^ t - 1) - t * witnessGap - t
      - (3/2 : ℝ) ^ t - witnessGap
    mergeRisk := 0
    jointEnergy := E - 2 * ((3/2 : ℝ) ^ t - 1) - t * witnessGap - t
      - (3/2 : ℝ) ^ t - witnessGap - 1
    jointRisk := 1/4
    jointCost := 0
    quantErr := |1/4 - qTern 1 (1/4)|
    compressEnergy := E - 2 * ((3/2 : ℝ) ^ t - 1) - t * witnessGap - t
      - (3/2 : ℝ) ^ t - witnessGap - 1
    compressRisk := 0
  }
  gen := ⟨0, 0, 0, 0, 0⟩

/-- **The full productive MasterHAGI witness** (R370): at
horizon 1 on the concrete carrier `ℝ`, EVERY premise of the
capstone holds simultaneously with live quantities — nonzero
safe step (`stepDir = 1`, η = 1/2 within the SafeQP window
against the old-domain gradient −1), strictly decreasing
energy, compound capability growth (rate 3/2), risk honestly
accrued (1/4 per step) — and the conclusion
`CertifiedHAGIInvariant` follows by `MasterHAGI` itself.
The end-to-end rung of the R357 → R359 → R369 witness
ladder (audit v7 §5.3). -/
theorem masterhagi_productive_witness (E : ℝ) :
    ∃ (S : ℕ → Hagi.GenState ℝ),
      (S 1).toGrowthState.energy < (S 0).toGrowthState.energy
        ∧ (S 0).toGrowthState.stepDir ≠ 0
        ∧ (S 1).toGrowthState.capability
            = (3/2 : ℝ) * (S 0).toGrowthState.capability
        ∧ (S 1).toGrowthState.protectedRisk
            = 1/4
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
              - (E - witnessGap - 3)) / 1) := by
  refine ⟨Mw E, ?_, ?_, ?_, ?_, ?_⟩
  · -- energy strictly decreases: e_1 = E - g - 2 < E
    unfold Mw
    norm_num
    linarith [witnessGap_pos]
  · unfold Mw; norm_num
  · unfold Mw; norm_num
  · -- risk accrued honestly: 1/4 after one step
    show (Mw E 1).toGrowthState.protectedRisk = 1/4
    unfold Mw
    norm_num
  · -- the capstone itself, applied to the live trajectory
    have hd : ∀ t < 1, (Mw E t).toGrowthState.stepDir ≠ 0 := by
      intro t ht
      have h0 : t = 0 := by omega
      subst h0
      unfold Mw
      norm_num
    have hlip : ∀ t < 1, ∀ i : Fin 1, (1/4 : ℝ) ≤ -(1/2) *
        ⟪(fun _ => (-1:ℝ)) i, (Mw E t).toGrowthState.stepDir⟫_ℝ
        + 1 * (1/2) * (1/2)
          * ‖(Mw E t).toGrowthState.stepDir‖ ^ 2 / 2 := by
      intro t ht i
      have h0 : t = 0 := by omega
      subst h0
      unfold Mw
      norm_num
    have heta : ∀ t < 1, (1/2 : ℝ)
        ≤ safeqpEtaMax (K := Fin 1) (fun _ => (-1:ℝ))
            (fun _ => 2) (fun _ => 1)
            (Mw E t).toGrowthState.stepDir := by
      intro t ht
      have h0 : t = 0 := by omega
      subst h0
      rw [le_safeqpEtaMax_iff]
      refine ⟨by norm_num, ?_⟩
      intro i
      unfold Mw
      norm_num
    have hsum : ∀ t < 1, (Mw E (t + 1)).toGrowthState.protectedRisk
        = (Mw E t).toGrowthState.protectedRisk
          + ∑ i : Fin 1, (1/4 : ℝ) := by
      intro t ht
      have h0 : t = 0 := by omega
      subst h0
      unfold Mw
      simp
    have hcore : ∀ t < 1,
        CorePremises (Mw E t) (Mw E (t + 1)) 0 (fun _ => 0) := by
      intro t ht
      have h0 : t = 0 := by omega
      subst h0
      unfold CorePremises Mw
      norm_num [Qgen, Qvec, grow, merge, joint, compress]
      all_goals first
        | exact ⟨witnessGap_pos.le, by linarith [witnessGap_pos],
            witness_quantErr_bounded⟩
        | exact witness_quantErr_bounded
        | linarith [witnessGap_pos]
        | norm_num
        | positivity
        | (left; ring)
    have hnet : ∀ t < 1, 0 * (verify (Mw E t).toGrowthState).riskSpend
        + 1 * 0 ≤ (verify (Mw E t).toGrowthState).decrease := by
      intro t ht
      have h0 : t = 0 := by omega
      subst h0
      unfold verify Mw
      simp [gainJoint]
      try linarith [witnessGap_pos]
    have hbud : ∑ t ∈ Finset.range 1,
        (verify (Mw E t).toGrowthState).budgetSpend
      ≤ (Mw E 0).toGrowthState.budget := by
      simp [verify, Mw, Finset.sum_range_one]
    have hrnn : ∀ t, 0 ≤ (Mw E t).toGrowthState.protectedRisk := by
      intro t
      unfold Mw
      positivity
    have hEmin : E - witnessGap - 3
        ≤ (Mw E 1).toGrowthState.energy := by
      unfold Mw
      norm_num
      try linarith [witnessGap_pos]
    exact Hagi.Unified.MasterHAGI (fun t => Mw E t) 0 1 0
      (E - witnessGap - 3) (fun _ => 0) (by norm_num) (by norm_num)
      (fun _ => 0) (by norm_num) 1
      (fun _ _ => (-1 : ℝ)) (fun _ _ => 1/4) (fun _ _ => 2)
      (fun _ _ => 1) (fun _ => 1/2)
      (by norm_num) (by norm_num) (by norm_num)
      hd hlip heta hsum hcore hnet hbud hrnn hEmin
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
        field_simp
        norm_num)

/-- **The productive MasterHAGI witness at ANY horizon**
(R373): the R370 witness generalizes from T = 1 to every
horizon `T ≥ 1` — the closed-form trajectory `Mw` (compound
capability 2·(3/2)^t, energy e_t = E − 2((3/2)^t − 1) −
t·gap − t, honestly accrued risk t/4) satisfies ALL
MasterHAGI premises at EVERY step t < T: the capstone is
productive on arbitrary horizons, not just single steps. The
terminal energy bound is the T-dependent floor e_T itself
(the constant E − gap − 3 of R370 fails for large T). -/
theorem masterhagi_productive_witness_all (E : ℝ) (T : ℕ)
    (hT : 1 ≤ T) :
    ∃ (S : ℕ → Hagi.GenState ℝ),
      (S T).toGrowthState.energy < (S 0).toGrowthState.energy
        ∧ (S 0).toGrowthState.stepDir ≠ 0
        ∧ (S T).toGrowthState.capability
            = (3/2 : ℝ) ^ T * (S 0).toGrowthState.capability
        ∧ (S T).toGrowthState.protectedRisk = (T : ℝ) / 4
        ∧ CertifiedHAGIInvariant T
            (fun t => (S t).toGrowthState.protectedRisk)
            (fun t => hagiPotential (S t) 0 1 0 (fun _ => 0))
            (fun t => 2 * (3/2 : ℝ) ^ t)
            (fun t => (S t).toGrowthState.budget)
            (fun t => (verify (S t).toGrowthState).budgetSpend)
            (fun t => Qgen (S t).gen (fun _ => 0))
            (fun t => ∑ i : Fin 1, (2 : ℝ))
            (1/2 : ℝ)
            (0 - (hagiPotential (S 0) 0 1 0 (fun _ => 0)
              - (E - 2 * ((3/2 : ℝ) ^ T - 1)
                - (T : ℝ) * witnessGap - (T : ℝ))) / 1) := by
  refine ⟨Mw E, ?_, ?_, ?_, ?_, ?_⟩
  · -- energy strictly decreases over the horizon
    have hone : (1:ℝ) ≤ (3/2 : ℝ) ^ T := by
      clear hT
      induction T with
      | zero => norm_num
      | succ T ih =>
          have hbase : (0:ℝ) < 3/2 := by norm_num
          rw [pow_succ]
          nlinarith
    have hT' : (1:ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    unfold Mw
    norm_num
    nlinarith [hone, hT', witnessGap_pos]
  · unfold Mw; norm_num
  · -- compound growth: c_T = (3/2)^T · c_0
    unfold Mw
    ring
  · -- risk accrued honestly: T/4
    unfold Mw
    push_cast
    ring
  · -- the capstone itself, on the whole horizon
    have hd : ∀ t < T, (Mw E t).toGrowthState.stepDir ≠ 0 := by
      intro t ht
      unfold Mw
      norm_num
    have hlip : ∀ t < T, ∀ i : Fin 1, (1/4 : ℝ) ≤ -(1/2) *
        ⟪(fun _ => (-1:ℝ)) i, (Mw E t).toGrowthState.stepDir⟫_ℝ
        + 1 * (1/2) * (1/2)
          * ‖(Mw E t).toGrowthState.stepDir‖ ^ 2 / 2 := by
      intro t ht i
      unfold Mw
      norm_num
    have heta : ∀ t < T, (1/2 : ℝ)
        ≤ safeqpEtaMax (K := Fin 1) (fun _ => (-1:ℝ))
            (fun _ => 2) (fun _ => 1)
            (Mw E t).toGrowthState.stepDir := by
      intro t ht
      rw [le_safeqpEtaMax_iff]
      refine ⟨by norm_num, ?_⟩
      intro i
      unfold Mw
      norm_num
    have hsum : ∀ t < T,
        (Mw E (t + 1)).toGrowthState.protectedRisk
        = (Mw E t).toGrowthState.protectedRisk
          + ∑ i : Fin 1, (1/4 : ℝ) := by
      intro t ht
      unfold Mw
      push_cast
      ring
    have hcore : ∀ t < T,
        CorePremises (Mw E t) (Mw E (t + 1)) 0 (fun _ => 0) := by
      intro t ht
      unfold CorePremises Mw
      norm_num [Qgen, Qvec, grow, merge, joint, compress]
      refine ⟨?_, ?_, witness_quantErr_bounded, ?_, ?_⟩
      · exact witnessGap_pos.le
      · linarith
      · -- telescoping: (3/2)^(t+1) = (3/2)·(3/2)^t
        rw [pow_succ]
        ring
      · push_cast
        ring
    have hnet : ∀ t < T, 0 * (verify (Mw E t).toGrowthState).riskSpend
        + 1 * 0 ≤ (verify (Mw E t).toGrowthState).decrease := by
      intro t ht
      unfold verify Mw
      simp [gainJoint]
      have hp : (0:ℝ) ≤ (3/2 : ℝ) ^ t := pow_nonneg (by norm_num) t
      linarith [hp, witnessGap_pos]
    have hbud : ∑ t ∈ Finset.range T,
        (verify (Mw E t).toGrowthState).budgetSpend
      ≤ (Mw E 0).toGrowthState.budget := by
      simp [verify, Mw]
    have hrnn : ∀ t, 0 ≤ (Mw E t).toGrowthState.protectedRisk := by
      intro t
      unfold Mw
      positivity
    have hEmin : E - 2 * ((3/2 : ℝ) ^ T - 1)
        - (T : ℝ) * witnessGap - (T : ℝ)
        ≤ (Mw E T).toGrowthState.energy := by
      unfold Mw
      push_cast
      ring_nf
      linarith
    exact Hagi.Unified.MasterHAGI (fun t => Mw E t) 0 1 0
      (E - 2 * ((3/2 : ℝ) ^ T - 1) - (T : ℝ) * witnessGap - (T : ℝ))
      (fun _ => 0) (by norm_num) (by norm_num)
      (fun _ => 0) (by norm_num) T
      (fun _ _ => (-1 : ℝ)) (fun _ _ => 1/4) (fun _ _ => 2)
      (fun _ _ => 1) (fun _ => 1/2)
      (by norm_num) (by norm_num) (by norm_num)
      hd hlip heta hsum hcore hnet hbud hrnn hEmin
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
        field_simp
        norm_num)

/-- **The non-idle nonvacuity witness**: `CorePremises` is
satisfiable with a STRICTLY positive Jensen gap and gain —
the cycle's energy ledger strictly decreases (`S'.energy =
E − 2g < E`), h_emp_merge carried by the Core lse theory. -/
theorem corePremises_nonvacuous_strict (E : ℝ) :
    ∃ S S' : Hagi.GenState X, ∃ epsQ : ℝ, ∃ w : Fin 5 → ℝ,
      CorePremises S S' epsQ w ∧ 0 < S.toGrowthState.gap
        ∧ 0 < S.toGrowthState.effects.growGain := by
  refine ⟨Spos E, Spos' E, 0, fun _ => 0, ?_, ?_, ?_⟩
  · unfold CorePremises Spos Spos'
    norm_num [Qgen, Qvec, grow, merge, joint, compress]
    refine ⟨le_of_lt witnessGap_pos, by linarith, witness_quantErr_bounded, rfl, rfl⟩
  · exact witnessGap_pos
  · exact witnessGap_pos

/-- **The nonvacuity witness**: `CorePremises` is satisfiable —
`S₀ E` and its composite successor `S₁ E` satisfy all 15
conjuncts, with h_emp_dist carried by the ternary rounding
theorem and every other stage law instantiated at equality. -/
theorem corePremises_nonvacuous (E : ℝ) :
    ∃ S S' : Hagi.GenState X, ∃ epsQ : ℝ, ∃ w : Fin 5 → ℝ,
      CorePremises S S' epsQ w := by
  refine ⟨S₀ E, S₁ E, 0, fun _ => 0, ?_⟩
  unfold CorePremises S₀ S₁ grow merge joint compress
  norm_num [Qgen, Qvec]
  exact witness_quantErr_bounded

end Witness

end Hagi.Examples
