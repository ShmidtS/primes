/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.System.GrowthState
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option linter.style.header false

/-!
# GrowthState effects recompute + capability tie-in (A16, C379)

The A16 mandatory fix #1, honesty half. Two pinned defects of
`Hagi.System.GrowthState` (statements Freeze-locked, so this module
ADDS the fix beside them, never edits them):

* **Stale effects.** The old ops `grow`/`merge`/`joint`/`compress`
  write the state-level channels from the measured record
  `S.effects` but carry the record itself unchanged
  (`effects := S.effects`). One generation is premise-covered (the
  h_emp_ chains of `growth_cycle_potential`); ACROSS generations
  nothing forces the post-cycle state's effects to be a re-measurement
  — see `stale_effects_gap_witness` for the formal gap.
* **Capability tie.** The master invariant's `cap` channel
  (`CertifiedHAGIInvariant.capability_growth`, R107) is an abstract
  `ℕ → ℝ` sequence; without the equality `cap t = (St t).capability`
  the growth theorem does not certify state capability growth. The
  missing premise is named here (`CapabilityTie`) and PROVEN for the
  new fresh ops (`capability_telescope_fresh`).

The fix (the C378 `EvalBinding` pattern — data carried with explicit
re-evaluation, no hidden convention): the fresh ops `growR`, `mergeR`,
`jointR`, `compressR` perform the SAME certified channel updates as
the old ops (measured at the pre-state `S`) but install the
caller-supplied RE-MEASURED record `e'` as the post-state's `effects`
field — freshness by construction. Honest pin: the re-evaluation
oracle is abstract (the caller re-measures, exactly as the caller
supplies `evalFn` in `EvalBinding`); when the oracle returns the same
record, the fresh ops COINCIDE with the old ones (`growR_eq_grow`,
`cycleR_eq_cycle`).

Nothing here changes the Legacy/Nonvacuity regression theorems.
-/

open Finset Real InnerProductSpace

namespace Hagi.System

noncomputable section Recompute

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-! ### The honesty pins (defect as theorems, not prose) -/

/-- The OLD ops carry the effects record through a full generation
UNCHANGED (definitional): after `compress (joint (merge (grow S)))`
the state's `effects` still holds the PRE-cycle measurement record.
This is the stale-effects defect of A16 mandatory fix #1, pinned. -/
theorem effects_carry_stale_cycle (S : GrowthState X) :
    (compress (joint (merge (grow S)))).effects = S.effects := by rfl

/-- The exact capability accounting of one OLD composed generation
(the fact the master `cap` channel was never tied to): capability
grows by exactly the measured `growGain`. -/
theorem capability_cycle_exact (S : GrowthState X) :
    (compress (joint (merge (grow S)))).capability
      = S.capability + S.effects.growGain := by rfl

/-- The witness carrier's stage constants: the degenerate zero-cost
window (η = 0, κ = 0, s = 0). -/
noncomputable def witParams : StageParams where
  eta := 0
  L := 1
  kappa := 0
  s := 0

/-- The witness effects: energy 10 → 9 at grow, constant through
merge/joint/compress, with growGain = 1. -/
noncomputable def witEffects : StageEffects where
  growGain := 1
  growCost := 0
  growRisk := 0
  growEnergy := 9
  mergeEnergy := 9
  mergeRisk := 0
  mergeCost := 0
  jointEnergy := 9
  jointRisk := 0
  jointCost := 0
  quantErr := 0
  compressEnergy := 9
  compressRisk := 0
  compressCost := 0

/-- The witness state: all stage chains hold at generation 1
(10 → 9 → 9 → 9 → 9 with gain 1), but the carried record makes the
generation-2 premise `9 ≤ 9 − 1` fail. -/
noncomputable def witState : GrowthState (EuclideanSpace ℝ (Fin 1)) where
  weightDim := 1
  weights := fun _ => 0
  params := 0
  experts := 0
  energy := 10
  protectedRisk := 0
  budget := 1
  gap := 0
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := witParams
  effects := witEffects

/-- **The formal stale-effects gap** (acceptance bar of this beat):
there is a state whose generation-1 certification premises ALL hold
  (gap sign plus the four h_emp_ stage chains, in the degenerate
  zero-cost window), yet at the post-cycle state the generation-2
  h_emp_grow premise FAILS — because the old ops carried the effects
record unchanged instead of re-measuring it. Effects freshness across
generations is NOT derivable from the old ops; it must be re-measured
(the `*R` ops below). -/
theorem stale_effects_gap_witness :
    ∃ S : GrowthState (EuclideanSpace ℝ (Fin 1)),
      (0 ≤ S.gap
        ∧ S.effects.growEnergy ≤ S.energy - S.effects.growGain
        ∧ S.effects.mergeEnergy ≤ S.effects.growEnergy - S.gap
        ∧ S.effects.jointEnergy ≤ S.effects.mergeEnergy)
      ∧ ¬ (S.effects.growEnergy
            ≤ (compress (joint (merge (grow S)))).energy
              - (compress (joint (merge (grow S)))).effects.growGain) := by
  refine ⟨witState, ⟨?_, ?_⟩⟩
  · norm_num [witState, witEffects, witParams]
  · intro h
    simp only [grow, merge, joint, compress, witState, witEffects, witParams] at h
    linarith

/-! ### The fresh ops (recomputed effects, C378 EvalBinding pattern) -/

/-- **growR**: the certified grow transition with a RE-MEASURED
effects record. The state-level channel updates are exactly `grow`'s
(measured at the pre-state `S`); the post-state's `effects` field is
the caller-supplied re-evaluation `e'` — the freshness the old carry
cannot guarantee, by construction. -/
def growR (S : GrowthState X) (e' : StageEffects) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts + 1
  energy := S.effects.growEnergy
  protectedRisk := S.protectedRisk + S.effects.growRisk
  budget := S.budget - S.effects.growCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability + S.effects.growGain
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := e'

/-- **mergeR**: the merge transition consuming the RE-MEASURED record
`e` at the post-grow state (`energy := e.mergeEnergy`), installing the
next re-evaluation `e'`. -/
def mergeR (S : GrowthState X) (e' : StageEffects) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts
  energy := S.effects.mergeEnergy
  protectedRisk := S.protectedRisk + S.effects.mergeRisk
  budget := S.budget - S.effects.mergeCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := e'

/-- **jointR**: the SafeQP refinement step consuming the re-measured
record, installing the next re-evaluation `e'`. -/
def jointR (S : GrowthState X) (e' : StageEffects) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params - S.sp.eta • S.stepDir
  experts := S.experts
  energy := S.effects.jointEnergy
  protectedRisk := S.protectedRisk + S.effects.jointRisk
  budget := S.budget - S.effects.jointCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := e'

/-- **compressR**: the compress transition consuming the re-measured
record, installing the generation's final re-evaluation `e'`. -/
def compressR (S : GrowthState X) (e' : StageEffects) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts
  energy := S.effects.compressEnergy
  protectedRisk := S.protectedRisk + S.effects.compressRisk
  budget := S.budget - S.effects.compressCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := e'

/-- The composed fresh generation: each stage consumes the record
re-measured at the previous stage's output. -/
def cycleR (S : GrowthState X) (e₁ e₂ e₃ e₄ : StageEffects) : GrowthState X :=
  compressR (jointR (mergeR (growR S e₁) e₂) e₃) e₄

/-! ### Freshness and carry-safety lemmas -/

/-- Freshness by construction: the post-state's effects ARE the
re-measured record. -/
theorem growR_effects (S : GrowthState X) (e' : StageEffects) :
    (growR S e').effects = e' := by rfl

theorem mergeR_effects (S : GrowthState X) (e' : StageEffects) :
    (mergeR S e').effects = e' := by rfl

theorem jointR_effects (S : GrowthState X) (e' : StageEffects) :
    (jointR S e').effects = e' := by rfl

theorem compressR_effects (S : GrowthState X) (e' : StageEffects) :
    (compressR S e').effects = e' := by rfl

/-- The composed fresh generation ends with the generation's final
re-evaluation as its effects record. -/
theorem cycleR_effects (S : GrowthState X) (e₁ e₂ e₃ e₄ : StageEffects) :
    (cycleR S e₁ e₂ e₃ e₄).effects = e₄ := by rfl

/-- Exact capability accounting of one fresh grow step. -/
theorem growR_capability (S : GrowthState X) (e' : StageEffects) :
    (growR S e').capability = S.capability + S.effects.growGain := by rfl

/-- Exact capability accounting of a full fresh generation (only the
grow stage moves the capability channel). -/
theorem cycleR_capability (S : GrowthState X) (e₁ e₂ e₃ e₄ : StageEffects) :
    (cycleR S e₁ e₂ e₃ e₄).capability
      = S.capability + S.effects.growGain := by rfl

/-- **Carry-safety**: when the re-evaluation oracle returns the SAME
record, the fresh op COINCIDES with the old one (full record
equality) — the fix degrades to the old behaviour exactly, no
divergence hidden anywhere. -/
theorem growR_eq_grow (S : GrowthState X) : growR S S.effects = grow S := by rfl

/-- Carry-safety for the composed generation: identity re-evaluation
at every stage reproduces the OLD composed cycle. -/
theorem cycleR_eq_cycle (S : GrowthState X) :
    cycleR S S.effects S.effects S.effects S.effects
      = compress (joint (merge (grow S))) := by rfl

/-! ### The capability tie-in (A16 honesty: channel vs state) -/

/-- **The missing premise of the master growth theorem**: the abstract
capability channel `cap` of `CertifiedHAGIInvariant` (and the C_t
renewal sequences) equals the `GrowthState.capability` projection of
the trajectory. WITHOUT this premise, the capability_growth conjunct
certifies an
abstract channel and must not be read as state-capability growth;
master consumers state it explicitly. -/
def CapabilityTie (St : ℕ → GrowthState X) (cap : ℕ → ℝ) : Prop :=
  ∀ t, cap t = (St t).capability

/-- The tie PROVEN for the fresh ops: along a `growR` trajectory the
capability channel evolves by EXACT additive growGain accounting —
the equality the master invariant would need, here a theorem instead
of a convention. -/
theorem capability_telescope_fresh {T : ℕ} (St : ℕ → GrowthState X)
    (e : ℕ → StageEffects)
    (hstep : ∀ t, t < T → St (t + 1) = growR (St t) (e t)) :
    (St T).capability = (St 0).capability
      + ∑ t ∈ Finset.range T, (St t).effects.growGain := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 : St (T + 1) = growR (St T) (e T) := hstep T (Nat.lt_succ_self T)
      rw [h1]
      have hgrow : (growR (St T) (e T)).capability
          = (St T).capability + (St T).effects.growGain := by rfl
      rw [hgrow, ih (fun t ht => hstep t (Nat.lt_trans ht (Nat.lt_succ_self T)))]
      rw [Finset.sum_range_succ]
      ring

/-- Under the tie premise, the abstract channel's endpoint IS the
state accounting: `capability_telescope_fresh` restated on `cap`. -/
theorem capability_channel_of_tie {T : ℕ} (St : ℕ → GrowthState X)
    (cap : ℕ → ℝ) (e : ℕ → StageEffects)
    (htie : CapabilityTie St cap)
    (hstep : ∀ t, t < T → St (t + 1) = growR (St t) (e t)) :
    cap T = cap 0 + ∑ t ∈ Finset.range T, (St t).effects.growGain := by
  rw [htie T, htie 0]
  exact capability_telescope_fresh St e hstep

end Recompute

end Hagi.System
