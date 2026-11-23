/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Semantics.Split
import Hagi.Training.Admission
import Hagi.Theory.MasterTheorem
import Hagi.Theory.SafeStep

/-!
# CR-MSM v2 — architecture skeleton: nonconvex extractor + controlled head

A16 track 1 (master plan v3 addendum A16 §CR-MSM v2): the
compositional SKELETON of the CR-MSM architecture, wiring PROVEN
blocks of the repo into one record with hypothesis-form bridges —
no new deep mathematics, every load-bearing statement is a bridge
to an existing theorem.

Layer decision: the skeleton must see Model(4)
transfer facts, Semantics(5) `ModelSpec`, Theory(7)
`UniversalSafeStep` (via `Hagi.Theory.CEChain`) and
`MasterStepCert`, and the layer-8 admission gate.
Only layer 8 (Training) sees all of them; `Hagi/Architecture`
(layer 2) cannot, so the module lives here (precedent).

## Composition (A16 components → repo pieces)

* **Multimodal encoder / nonconvex feature extractor** —
  `ExtractorSpec`: a feature map with hypothesis-form Lipschitz
  facts. The facts themselves are the transfer stack's business:
  residual backbone, attention, RoPE isometry
RMSNorm negative result, GDN bridge,
  FastArch3 end-to-end assembly. PIN: the extractor is
  NONCONVEX and NO joint update guarantee is claimed (A16:
  «доказательства для линейной головы при фиксированных признаках
  не распространяются на совместное обновление»).
* **SSM / GQA / memory branches** — `CRMSMBranch`: an OPTIONAL
  single-choice sum-type. The audit's directive: gated/SSM is a
  SEPARATE testable alternative, never a required per-block field
  (memory cycle KV-cache machinery).
* **Shared core (rare updates)** — `SharedCore`: the core moves
  only every K macro ticks; the macro book is `MacroStatCert`
  (Commit/Hold/Rollback via the Ville engine).
* **Residual low-rank expert bank** — `ExpertBank` carrying the
  correction-C premise record `CoherencePremise`: strict
  orthogonality of experts is NOT required; what IS required is
  the pairwise block-Gram Frobenius coherence ≤ μ TOGETHER with a
  per-block spectral lower bound (A16 correction C: pairwise
  coherence alone is insufficient; for orthogonal ranks Kr ≤ d).
  New experts enter ONLY through the admission rule.
* **Prediction head (controlled decision part)** — `ModelSpec`
  (Semantics split): the logit head whose updates are
  governed by the universal safe step at FIXED features.

## Wiring theorems

* `crmsm_head_step_safe` — head control at fixed extractor: a thin
  bridge over `Hagi.Theory.CEChain.universal_descent`.
* `crmsm_joint_separation` — the honesty pin: the head-control
  bridge carries the extractor-equality premise EXPLICITLY; no
  joint-update descent is claimed or derivable here.
* `CRMSMGrowth` + `crmsmGrowth_refuses` — growth is
  admission-gated: the decision is EXACTLY `Hagi.Training.admitRule`
  (no-drift pattern), and a non-positive margin always
  refuses.
* `CRMSMStep` + `crmsm_step_descent` — end-to-end pointer: at
  fixed extractor, a CR-MSM training step on the canonical state
  IS a master step (`MasterStepCert`), the descent included.

## Honest pins (no overclaiming)

- Extractor nonconvexity: no joint (extractor+head) guarantees.
- Quantization error reduction under orthogonal mixing: NOT
  claimed (A16 correction A — separate conditions, cf.).
- SSM branch optional; its testable-alternative status is a PIN.
- `CoherencePremise` is premise-form: μ-coherence AND the spectral
  lower bound are binders every instance must discharge.
-/

set_option relaxedAutoImplicit false

open Hagi.Semantics Hagi.Training Hagi.Theory

namespace Hagi.Training.CRMSM

/-! ## The nonconvex extractor (hypothesis-form) -/

/-- The feature-extractor side of CR-MSM: a feature map between
normed spaces together with its Lipschitz constant AS A HYPOTHESIS
(premise-form). The transfer stack (residual, attention,
 RoPE isometry, GDN, FastArch3 end-to-end) supplies
instances of this record; the skeleton does not re-prove them.
PIN: the extractor is nonconvex — nothing here claims a joint
extractor+head update guarantee. -/
structure ExtractorSpec (X F : Type) [NormedAddCommGroup X]
    [NormedAddCommGroup F] where
  /-- The feature (encoder) map. -/
  extract : X → F
  /-- The Lipschitz constant of the encoder (premise). -/
  lip : ℝ
  /-- The Lipschitz law: distances contract by `lip`. -/
  lipschitz : ∀ x x', ‖extract x - extract x'‖ ≤ lip * ‖x - x'‖

/-! ## Optional branches (SSM is a separate testable alternative) -/

/-- The OPTIONAL processing branch of a CR-MSM block: at most ONE
of the audit's alternatives is instantiated per block, and `noneB`
(no branch) is a legitimate choice — the gated/SSM route is a
separate testable alternative (A17 architecture directive), not a
required component. Memory points at the memory-cycle
semantics; `gqa` at the KV-cache machinery. -/
inductive CRMSMBranch where
  /-- No optional branch: the plain residual backbone. -/
  | noneB : CRMSMBranch
  /-- The SSM alternative (separate testable branch). -/
  | ssm : CRMSMBranch
  /-- Grouped-query attention branch (KV-cache machinery). -/
  | gqa : CRMSMBranch
  /-- Memory-cycle branch. -/
  | memory : CRMSMBranch

/-! ## The shared core (rare updates) -/

/-- The shared core of CR-MSM: core parameters move only on macro
ticks — every `K` steps — so the micro loop sees them
as constants. The macro book that certifies those rare updates is
 `MacroStatCert` (Commit/Hold/Rollback via the Ville
engine); this record carries the PERIOD and the premise-form rarity
law, not a new probability argument. -/
structure SharedCore where
  /-- The rarity period: core parameters update every K steps. -/
  K : ℕ
  /-- The core parameters are IDENTICAL between macro ticks
  (premise-form: the consumer's invariant, discharged
  macro controller's Hold semantics). -/
  core_frozen_between : Prop

/-! ## Correction C: the coherence premise record -/

/-- The Frobenius SQUARE of a matrix: the sum of squared
entries (the `frobSq` convention of `Hagi.Unified.MemoryCycle`). -/
def blockFrobSq {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, M i j ^ 2

/-- The block Gram of two experts `i ≠ j`: `(U i) * (U j)ᵀ` — the
object whose Frobenius square the coherence binder controls. -/
noncomputable def blockGram {m r d : ℕ} (U : Fin m → Matrix (Fin r) (Fin d) ℝ)
    (i j : Fin m) : Matrix (Fin r) (Fin r) ℝ :=
  (U i) * (U j).transpose

/-- The correction-C premise record for the residual low-rank
expert bank: strict orthogonality of experts is NOT required (A16
correction C). What the bank must carry is (a) the pairwise
block-Gram Frobenius coherence ≤ `μ`, AND (b) a per-block spectral
lower bound on the block Gram `G_ii = (U i)(U i)ᵀ`, stated as the
quadratic-form inequality `κ ‖v‖² ≤ vᵀG_ii v` (an equivalent
spectral binder, no eigenvector API). Docstring fact: for
orthogonal rank-r factors the total rank satisfies Kr ≤ d — that
is why coherence alone (which Kr ≤ d tolerates) is insufficient and
the spectral field exists. -/
structure CoherencePremise (m r d : ℕ) where
  /-- The low-rank expert factors: `U i` is r × d. -/
  U : Fin m → Matrix (Fin r) (Fin d) ℝ
  /-- The pairwise coherence level μ. -/
  mu : ℝ
  /-- Pairwise block-Gram Frobenius coherence ≤ μ for i ≠ j. -/
  coherence : ∀ i j : Fin m, i ≠ j → blockFrobSq (blockGram U i j) ≤ mu
  /-- The per-block spectral level κ. -/
  kappa : ℝ
  /-- The per-block spectral lower bound: every direction v has
  quadratic form ≥ κ‖v‖² on the diagonal block Gram. -/
  gramSpectral : ∀ i : Fin m, ∀ v : Fin r → ℝ,
    kappa * (∑ t, v t ^ 2) ≤ ∑ t, v t * Matrix.mulVec (blockGram U i i) v t
  /-- The spectral level is positive: the diagonal blocks are
  uniformly well-posed. -/
  kappa_pos : 0 < kappa

/-- The residual low-rank expert bank: rank-r experts over a
d-dimensional feature space, carrying their correction-C coherence
premise. -/
structure ExpertBank (m r d : ℕ) where
  /-- The coherence premise of the bank (correction C binder). -/
  coherencePremise : CoherencePremise m r d

/-! ## The block record -/

/-- The CR-MSM block: nonconvex extractor (hypothesis-form), one
OPTIONAL branch, the rarely-updated shared core, the residual
low-rank expert bank, and the CONTROLLED decision part
`ModelSpec` prediction head. This is the composition record; every
guarantee lives in the wiring theorems below, each a bridge to an
existing theorem of the repo. -/
structure CRMSMBlock (Θ X V F : Type) [NormedAddCommGroup X]
    [NormedAddCommGroup F] (m r d : ℕ) where
  /-- The nonconvex feature extractor (premise-form Lipschitz). -/
  extractor : ExtractorSpec X F
  /-- The optional processing branch (SSM separate alternative). -/
  branch : CRMSMBranch
  /-- The rarely-updated shared core (K + pointer). -/
  core : SharedCore
  /-- The residual low-rank expert bank (correction C premise). -/
  bank : ExpertBank m r d
  /-- The controlled prediction head (ModelSpec). -/
  head : ModelSpec Θ X V

/-! ## Wiring (i): head control at FIXED extractor -/

/-- The head-control statement between two blocks: the
fixed-extractor channel (left conjunct) TOGETHER
certified head descent (right conjunct). The conjunction is the
point: in this skeleton, head control EXISTS only in the
fixed-feature world. -/
def HeadControl {Θ X V F : Type} [NormedAddCommGroup X]
    [NormedAddCommGroup F] {m r d : ℕ}
    (b b' : CRMSMBlock Θ X V F m r d)
    (U : Hagi.Theory.CEChain.UniversalSafeStep Θ) (θ : Θ) : Prop :=
  b.extractor = b'.extractor ∧
    U.loss (U.step θ (Hagi.Theory.CEChain.universalStepSize U θ))
      ≤ U.loss θ - Hagi.Theory.CEChain.universalDrop U θ

/-- Head control: at FIXED extractor (the premise `b.extractor =
b'.extractor` is EXPLICIT), if the head-side loss admits
`UniversalSafeStep` carrier, the head step at the universal step
size descends by the certified drop. A thin bridge over
`Hagi.Theory.CEChain.universal_descent`: the CR-MSM skeleton adds
no mathematics, it pins WHERE the existing theorem applies. -/
theorem crmsm_head_step_safe {Θ X V F : Type} [NormedAddCommGroup X]
    [NormedAddCommGroup F] {m r d : ℕ}
    (b b' : CRMSMBlock Θ X V F m r d)
    -- The fixed-extractor premise: the extractor does not move.
    (hfix : b.extractor = b'.extractor)
    -- The head-side loss admits the carrier (premise).
    (U : Hagi.Theory.CEChain.UniversalSafeStep Θ) (θ : Θ)
    (hC : 0 < U.curvature θ) :
    HeadControl b b' U θ :=
  ⟨hfix, Hagi.Theory.CEChain.universal_descent U θ hC⟩

/-- The separation pin (A16, honesty): the head-control bridge of
`crmsm_head_step_safe` is stated for a pair of blocks whose
extractors are EQUAL — the guarantee governs the head at
fixed features and DOES NOT extend to the joint extractor+head
update («доказательства для линейной головы при фиксированных
признаках не распространяются на совместное обновление», A16
directive). Formally: any head-control fact between two blocks
FORCES the extractor-equality channel — the descent statement of
this skeleton lives entirely inside the fixed-feature world, and
no statement is offered for `b.extractor ≠ b'.extractor`. -/
theorem crmsm_joint_separation {Θ X V F : Type} [NormedAddCommGroup X]
    [NormedAddCommGroup F] {m r d : ℕ}
    (b b' : CRMSMBlock Θ X V F m r d)
    (U : Hagi.Theory.CEChain.UniversalSafeStep Θ) (θ : Θ)
    (h : HeadControl b b' U θ) :
    b.extractor = b'.extractor :=
  h.1

/-! ## Wiring (ii): expert growth is admission-gated -/

/-- A CR-MSM growth event: a proposal for a new expert (bank
growth) together with its decision. The decision is EXACTLY the
 `admitRule` output — no drift, the same no-free-floating-
decision pattern as `Hagi.Training.Admission.admit_ok`. New experts
enter the bank ONLY through this gate. -/
structure CRMSMGrowth where
  /-- The admission proposal of the candidate expert. -/
  proposal : AdmissionProposal
  /-- The recorded decision. -/
  decision : Bool
  /-- No drift: the decision is exactly `admitRule proposal`. -/
  admit_ok : decision = admitRule proposal

/-- Admission gating, refusal direction: a non-positive admission
margin always refuses the growth event. Direct bridge over
refusal law — the CR-MSM bank cannot grow against the gate. -/
theorem crmsmGrowth_refuses (g : CRMSMGrowth)
    (hm : admissionMargin g.proposal ≤ 0) :
    g.decision = false := by
  rw [g.admit_ok]
  exact noAdmitWithoutPositiveMargin g.proposal hm

/-! ## Wiring (iii): end-to-end descent = the master step -/

variable {n a e q r c k : ℕ}
variable {Θ X V F : Type} [NormedAddCommGroup X] [NormedAddCommGroup F]
variable {mE rE dE : ℕ}

/-- A CR-MSM training step on the canonical state, at FIXED
extractor: the step IS `MasterStepCert` step. The bridge
instance pattern: the CR-MSM skeleton does not re-prove descent —
it pins that the canonical CR-MSM step carries the master
certificate, with the fixed-extractor premise explicit (the joint
update is OUT of scope, see `crmsm_joint_separation`). -/
structure CRMSMStep (s s' : Hagi.State.CanonicalTrainState n a e q r c k) where
  /-- The block before the step. -/
  block : CRMSMBlock Θ X V F mE rE dE
  /-- The block after the step. -/
  block' : CRMSMBlock Θ X V F mE rE dE
  /-- Fixed extractor: the feature map did not move. -/
  extractor_fixed : block.extractor = block'.extractor
  /-- The step carries the master certificate. -/
  master : MasterStepCert s s'

/-- End-to-end descent pointer: at fixed extractor, a CR-MSM step
descends the full objective with controlled drop and penalty —
exactly the master descent, restated through the bridge. -/
theorem crmsm_step_descent (s s' : Hagi.State.CanonicalTrainState n a e q r c k)
    (h : CRMSMStep (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) s s') :
    Hagi.State.fullObjective s' ≤ Hagi.State.fullObjective s
      - h.master.drop + h.master.penalty :=
  h.master.descent

end Hagi.Training.CRMSM
