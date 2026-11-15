/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Model.GDNTransfer
import Hagi.Model.RoPETransfer
import Hagi.Model.SoftmaxHead

set_option linter.style.header false

/-!
# FastArch3 end-to-end transfer assembly (E4 final rung)

The FINAL rung of the E4 backbone ladder (TD E4-C300 remaining
rung: "chain all rungs into the full FastArch3 stack certificate"):
the end-to-end FastArch3-SHAPED certified-descent theorem — the
parametric SoftmaxHead (C283/C291) on top of the hybrid stack
(C307 attention + C308 RoPE wrap + C309 RMSNorm discharge + C310
GDN), assembled as COMPOSITION ONLY of the landed carriers, with
every remaining hypothesis exposed as an explicit PREMISE LEDGER
entry (`.tmp/C311/premise-ledger.md`, summarized in STATUS.md).

Structure (a thin config over existing carriers — KISS):

* `FA3Block n ι` — one hybrid backbone block: `att a R` (a C307
  `AttnBlock` on the Euclidean carrier, optionally wrapped in a
  RoPE-style pre-rotation `R`; C308 instantiates `R = rotEuc θ m`,
  an `Isometry`, at UNCHANGED damping; `R = id` when unwrapped) or
  `gdn g` (a C310 `GdnBlock`: μg-Lipschitz gate premise +
  doubly-stochastic mixing, C231).
* `FastArch3Spec n ι β` — the full FastArch3 shape: the hybrid
  blocks list plus the C283 `HeadConfig` (LogitMap / Reduction
  axes) of the parametric head.
* `fa3BlockList` / `fa3Stack` / `fa3Gain` — the C300 residual
  stack over the heterogeneous blocks list, per-block damping
  `μᵢ` (attention `μn·μatt`, GDN `μg`), gain `∏ (1 + μᵢ)`.
* `fa3BlockList_lipschitz` — the premise-ledger dispatch: each
  block's C300 block hypothesis from its carrier premises
  (C307 adapter composed with the C308 isometry pattern for
  attention; C310 adapter for GDN).
* `fa3Objective` — the END-TO-END objective: the loss evaluated at
  the stack output (the head loss composed through the backbone).
* `fastarch3_transfer_descent` (+ `_strict`) — THE assembly
  theorem: given each block's ledgered premise, the head's
  certified drop `δ` (C291 premise shape) and the head-loss
  Lipschitz premise `Lc`, the composed guard
  `Lc·(∏ (1 + μᵢ) − 1)·‖dx‖ < δ` makes the end-to-end objective
  STRICTLY decrease. Pure composition: the C300 stack theorem
  applied to the FastArch3 block list.

PREMISE LEDGER (every hypothesis of the final theorem):

| id | premise | source | state |
|----|---------|--------|-------|
| P1 | softmax weight map `p` is a fixed simplex | C307 | lived-with |
| P2 | value maps `v i` are `μatt`-Lipschitz | C307 | per-instance |
| P3 | pre-norm `μn`-Lipschitz | C307 premise | DISCHARGED by C309 (region `2√n/r`, ε-form `2/√ε`) |
| P4 | rope wrap `R` is an `Isometry` | C308 | DISCHARGED (`rotEuc`) |
| P5 | GDN gate `μg`-Lipschitz | C310 | lived-with (follow-up) |
| P6 | mixing matrix doubly stochastic | C231/C310 | lived-with |
| P7 | head loss `Lc`-Lipschitz (Euclidean carrier) | assembly | premise (sup-norm 2-Lipschitz: CEQuantized) |
| P8 | head certified drop `δ` | C291 | per-instance via `ceOneHot_next_le_param` |
| P9 | realized step `dx` on the identity path | C300 form | structural |

Honest scope: certified descent for the FastArch3-SHAPED model
UNDER THE LEDGERED PREMISES — NOT a claim about trained weights or
the Python runtime; no full forward/backward certificate; the
softmax weight map is not discharged (P1).
-/

namespace Hagi.Model.FastArch3Transfer

open Hagi.Model.Residual Hagi.Model.BackboneTransfer
  Hagi.Model.AttentionTransfer Hagi.Model.GDNTransfer
  Hagi.Model.RoPETransfer Hagi.Model.SoftmaxHead
  Hagi.Architecture.ManifoldHyperConn

variable {n : Type*} [Fintype n] [DecidableEq n]
  {ι : Type*} [Fintype ι] {β : Type} [Fintype β]

/-!
## The FastArch3 shape (thin config)
-/

/-- One FastArch3 backbone block: an attention block (C307) with an
optional RoPE-style pre-rotation `R` (C308: an `Isometry` premise,
instantiated by `rotEuc`; `id` when unwrapped), or a GDN block
(C310: gate + doubly-stochastic mixing). -/
inductive FA3Block (n : Type*) [Fintype n] [DecidableEq n]
    (ι : Type*) [Fintype ι] where
  /-- Attention block + rope wrap map (premise: `Isometry R`). -/
  | att (a : AttnBlock (EuclideanSpace ℝ n) ι)
      (R : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
  /-- GDN block (gate premise + doubly-stochastic mixing premise). -/
  | gdn (g : GdnBlock n)

/-- The full FastArch3 shape: the hybrid backbone blocks plus the
parametric head configuration (C283 `HeadConfig`: the LogitMap and
Reduction axes of the SoftmaxHead family). -/
structure FastArch3Spec (n : Type*) [Fintype n] [DecidableEq n]
    (ι : Type*) [Fintype ι] (β : Type) [Fintype β] where
  /-- Hybrid backbone: attention and GDN blocks, bottom-up order. -/
  blocks : List (FA3Block n ι)
  /-- Parametric SoftmaxHead configuration (C283). -/
  head : HeadConfig β

/-!
## The C300 stack instantiation
-/

/-- The C300 block list of a FastArch3 backbone: attention blocks
carry their composed damping `μn·μatt` (the rope wrap `R` changes
no constant — C308), GDN blocks their gate damping `μg`. -/
noncomputable def fa3BlockList (bs : List (FA3Block n ι)) :
    List ((EuclideanSpace ℝ n → EuclideanSpace ℝ n) × NNReal) :=
  bs.map fun b => match b with
    | .att a R => (fun x => attnBranch a.p a.v (a.n (R x)), a.μn * a.μatt)
    | .gdn g => (gdnBlockBranch g, g.μg)

/-- The FastArch3 backbone stack: the C300 residual stack over the
hybrid blocks list. -/
noncomputable def fa3Stack (bs : List (FA3Block n ι)) :
    EuclideanSpace ℝ n → EuclideanSpace ℝ n :=
  resStack (fa3BlockList bs)

/-- The FastArch3 stack gain: `∏ (1 + μᵢ)` over the per-block
composed dampings (attention `μn·μatt` — unchanged by the rope
wrap, C308 — and GDN `μg`). -/
noncomputable def fa3Gain (bs : List (FA3Block n ι)) : NNReal :=
  stackGain (fa3BlockList bs)

/-- Every block of a well-premised FastArch3 backbone satisfies the
C300 block hypothesis — the PREMISE-LEDGER dispatch: attention
blocks through the C307 adapter composed with the C308 isometry
pattern (`Isometry R` premise, constant unchanged), GDN blocks
through the C310 adapter. Each hypothesis below is a ledger row
(P1–P6). -/
theorem fa3BlockList_lipschitz (bs : List (FA3Block n ι))
    (hatt : ∀ (a : AttnBlock (EuclideanSpace ℝ n) ι)
        (R : EuclideanSpace ℝ n → EuclideanSpace ℝ n),
      FA3Block.att a R ∈ bs → LipschitzWith a.μn a.n
        ∧ (∀ i, 0 ≤ a.p i) ∧ (∑ i, a.p i = 1)
        ∧ (∀ i, LipschitzWith a.μatt (a.v i)) ∧ Isometry R)
    (hgdn : ∀ g : GdnBlock n, FA3Block.gdn g ∈ bs →
      LipschitzWith g.μg g.gate ∧ IsDoublyStochastic g.M) :
    ∀ c ∈ fa3BlockList bs, LipschitzWith c.2 c.1 := by
  intro c hc
  obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hc
  cases b₀ with
  | att a R =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hatt a R hb₀
      have hcomp : LipschitzWith (a.μn * a.μatt)
          (fun x => attnBranch a.p a.v (a.n (R x))) := by
        have h6 := (attn_norm_branch_lipschitz h1 h2 h3 h4).comp
          h5.lipschitzWith
        rw [mul_one] at h6
        exact h6
      exact hcomp
  | gdn g =>
      obtain ⟨h1, h2⟩ := hgdn g hb₀
      exact gdn_branch_lipschitz h1 h2

/-!
## The end-to-end assembly theorem
-/

/-- The END-TO-END objective: the loss evaluated at the stack
output — the head loss composed through the FastArch3 backbone
(the model's full-shape training objective at the stack input). -/
noncomputable def fa3Objective (bs : List (FA3Block n ι))
    (loss : EuclideanSpace ℝ n → ℝ) : EuclideanSpace ℝ n → ℝ :=
  fun x => loss (fa3Stack bs x)

/-- THE ASSEMBLY THEOREM: certified head descent through the whole
FastArch3 backbone. Given (a) each block's ledgered premises
(P1–P6), (b) the head's certified drop `δ` at the stack output
(C291 premise shape — `ceOneHot_next_le_param` instantiates it),
and (c) the head-loss Lipschitz premise `Lc` (P7), the composed
leak slack is `Lc·(∏ (1 + μᵢ) − 1)·‖dx‖` — the C300 stack theorem
instantiated over the FastArch3 block list, composition only. -/
theorem fastarch3_transfer_descent (bs : List (FA3Block n ι))
    {loss : EuclideanSpace ℝ n → ℝ} {Lc : NNReal} {δ : ℝ}
    (hatt : ∀ (a : AttnBlock (EuclideanSpace ℝ n) ι)
        (R : EuclideanSpace ℝ n → EuclideanSpace ℝ n),
      FA3Block.att a R ∈ bs → LipschitzWith a.μn a.n
        ∧ (∀ i, 0 ≤ a.p i) ∧ (∑ i, a.p i = 1)
        ∧ (∀ i, LipschitzWith a.μatt (a.v i)) ∧ Isometry R)
    (hgdn : ∀ g : GdnBlock n, FA3Block.gdn g ∈ bs →
      LipschitzWith g.μg g.gate ∧ IsDoublyStochastic g.M)
    (hloss : LipschitzWith Lc loss) (x dx : EuclideanSpace ℝ n)
    (hdrop : loss (fa3Stack bs x + dx) ≤ loss (fa3Stack bs x) - δ) :
    loss (fa3Stack bs (x + dx))
      ≤ loss (fa3Stack bs x) - δ
        + Lc * ((fa3Gain bs : ℝ) - 1) * ‖dx‖ :=
  resStack_transfer_descent _ (fa3BlockList_lipschitz bs hatt hgdn)
    hloss x dx hdrop

/-- STRICT end-to-end descent: if the certified head drop `δ`
beats the composed leak slack `Lc·(∏ (1 + μᵢ) − 1)·‖dx‖`, the
END-TO-END objective (the loss at the stack output, as a function
of the stack input) STRICTLY decreases. -/
theorem fastarch3_transfer_descent_strict (bs : List (FA3Block n ι))
    {loss : EuclideanSpace ℝ n → ℝ} {Lc : NNReal} {δ : ℝ}
    (hatt : ∀ (a : AttnBlock (EuclideanSpace ℝ n) ι)
        (R : EuclideanSpace ℝ n → EuclideanSpace ℝ n),
      FA3Block.att a R ∈ bs → LipschitzWith a.μn a.n
        ∧ (∀ i, 0 ≤ a.p i) ∧ (∑ i, a.p i = 1)
        ∧ (∀ i, LipschitzWith a.μatt (a.v i)) ∧ Isometry R)
    (hgdn : ∀ g : GdnBlock n, FA3Block.gdn g ∈ bs →
      LipschitzWith g.μg g.gate ∧ IsDoublyStochastic g.M)
    (hloss : LipschitzWith Lc loss) (x dx : EuclideanSpace ℝ n)
    (hdrop : loss (fa3Stack bs x + dx) ≤ loss (fa3Stack bs x) - δ)
    (hstrict : (Lc : ℝ) * ((fa3Gain bs : ℝ) - 1) * ‖dx‖ < δ) :
    fa3Objective bs loss (x + dx) < fa3Objective bs loss x :=
  resStack_transfer_descent_strict _
    (fa3BlockList_lipschitz bs hatt hgdn) hloss x dx hdrop hstrict

/-!
## Anchors (nonvacuity + numeric instance)
-/

/-- Rope-wrap premise nonvacuity (P4): the C308 rotation IS an
isometry, instantiating the `R` premise of an `att` block. -/
example : Isometry (rotEuc (fun _ : Fin 2 => Real.pi / 3) 1) :=
  rope_isometry _ _

/-- Spec nonvacuity: a FastArch3 shape exists — one attention
block (unwrapped, `R = id`), one GDN block, classical head. -/
example : FastArch3Spec (Fin 2) (Fin 1) (Fin 1) where
  blocks := [.att ⟨fun x => x, fun _ => 1, fun _ _ => 0, 0, 0⟩ id,
    .gdn ⟨fun x => x, 0, 1⟩]
  head := ⟨.ident, .uniform⟩

/-- Numeric anchor (2-block instance): attention composed damping
`μn·μatt = 1.4·0.4 = 0.56`, GDN gate `μg = 0.2` — composed leak
factor `(1 + 0.56)(1 + 0.2) − 1 = 0.872` per unit step. -/
example : (1 + ((1.4 : ℝ) * 0.4)) * (1 + 0.2) - 1 = 0.872 := by
  norm_num

/-- Numeric guard anchor: head drop `δ = 0.5` beats the composed
slack at `Lc = 0.5`, `‖dx‖ = 1` — `0.5·0.872·1 = 0.436 < 0.5`, so
`fastarch3_transfer_descent_strict` applies to the instance. -/
example : ((0.5 : ℝ)) * ((1 + 1.4 * 0.4) * (1 + 0.2) - 1) * 1 < 0.5 := by
  norm_num

end Hagi.Model.FastArch3Transfer
