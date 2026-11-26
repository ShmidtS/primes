/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Model.GDNTransfer
import Hagi.Model.RoPETransfer
import Hagi.Model.SoftmaxHead

set_option linter.style.header false

/-!
# FastArch3 end-to-end transfer assembly

The end-to-end FastArch3-SHAPED certified-descent theorem — the
parametric SoftmaxHead on top of the hybrid stack
(attention + RoPE wrap + RMSNorm discharge + GDN), assembled as
COMPOSITION ONLY of the existing carriers, with every remaining
hypothesis exposed as an explicit PREMISE LEDGER entry.

Structure (a thin config over existing carriers — KISS):

* `FA3Block n ι` — one hybrid backbone block: `att a R`
  `AttnBlock` on the Euclidean carrier, optionally wrapped in a
  RoPE-style pre-rotation `R`; instantiates `R = rotEuc θ m`,
  an `Isometry`, at UNCHANGED damping; `R = id` when unwrapped) or
  `gdn g` (`GdnBlock`: μg-Lipschitz gate premise +
  doubly-stochastic mixing).
* `FastArch3Spec n ι β` — the full FastArch3 shape: the hybrid
  blocks list plus `HeadConfig` (LogitMap / Reduction
  axes) of the parametric head.
* `fa3BlockList` / `fa3Stack` / `fa3Gain` — the residual
  stack over the heterogeneous blocks list, per-block damping
  `μᵢ` (attention `μn·μatt`, GDN `μg`), gain `∏ (1 + μᵢ)`.
* `fa3BlockList_lipschitz` — each
  block's block hypothesis from its carrier premises
  (adapter composed with the isometry pattern for
  attention; adapter for GDN).
* `fa3HeadLoss` / `fastarch3_head_Lc` — the ident-logit headCE at a fixed label is `2`-Lipschitz
  on the Euclidean carrier (`Lc = 2`, via `euclid_coord_abs_sub_le`
  `‖·‖∞ ≤ ‖·‖₂` and the sup-norm estimate).
* `fa3Objective` — the END-TO-END objective: the loss evaluated at
  the stack output (the head loss composed through the backbone).
* `fastarch3_transfer_descent` (+ `_strict`) — THE assembly
  theorem: given each block's premise, the head's
  certified drop `δ` (premise shape) and the head-loss
  Lipschitz premise `Lc`, the composed guard
  `Lc·(∏ (1 + μᵢ) − 1)·‖dx‖ < δ` makes the end-to-end objective
  STRICTLY decrease. Pure composition: the stack theorem
  applied to the FastArch3 block list.

PREMISE LEDGER (every hypothesis of the final theorem):

| id | premise | source | state |
|----|---------|--------|-------|
| P1 | softmax weight map `p` is a fixed simplex | | lived-with |
| P2 | value maps `v i` are `μatt`-Lipschitz | | per-instance |
| P3 | pre-norm `μn`-Lipschitz | premise | DISCHARGED (region `2√n/r`, ε-form `2/√ε`) |
| P4 | rope wrap `R` is an `Isometry` | | DISCHARGED (`rotEuc`) |
| P5 | GDN gate `μg`-Lipschitz | | DISCHARGED per-instance (`gdnGateTanh_lipschitz`, tanh family, μg = 1; other gate families remain per-instance) |
| P6 | mixing matrix doubly stochastic | | lived-with |
| P7 | head loss `Lc`-Lipschitz (Euclidean carrier) | assembly | DISCHARGED per-instance (`fastarch3_head_Lc`, ident-logit headCE at fixed label, Lc = 2) |
| P8 | head certified drop `δ` | | per-instance via `ceOneHot_next_le_param` |
| P9 | realized step `dx` on the identity path | form | structural |

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

/-- One FastArch3 backbone block: an attention block with an
optional RoPE-style pre-rotation `R` (an `Isometry` premise,
instantiated by `rotEuc`; `id` when unwrapped), or a GDN block
(gate + doubly-stochastic mixing). -/
inductive FA3Block (n : Type*) [Fintype n] [DecidableEq n]
    (ι : Type*) [Fintype ι] where
  /-- Attention block + rope wrap map (premise: `Isometry R`). -/
  | att (a : AttnBlock (EuclideanSpace ℝ n) ι)
      (R : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
  /-- GDN block (gate premise + doubly-stochastic mixing premise). -/
  | gdn (g : GdnBlock n)

/-- The full FastArch3 shape: the hybrid backbone blocks plus the
parametric head configuration (`HeadConfig`: the LogitMap and
Reduction axes of the SoftmaxHead family). -/
structure FastArch3Spec (n : Type*) [Fintype n] [DecidableEq n]
    (ι : Type*) [Fintype ι] (β : Type) [Fintype β] where
  /-- Hybrid backbone: attention and GDN blocks, bottom-up order. -/
  blocks : List (FA3Block n ι)
  /-- Parametric SoftmaxHead configuration. -/
  head : HeadConfig β

/-!
## The stack instantiation
-/

/-- The block list of a FastArch3 backbone: attention blocks
carry their composed damping `μn·μatt` (the rope wrap `R` changes
no constant), GDN blocks their gate damping `μg`. -/
noncomputable def fa3BlockList (bs : List (FA3Block n ι)) :
    List ((EuclideanSpace ℝ n → EuclideanSpace ℝ n) × NNReal) :=
  bs.map fun b => match b with
    | .att a R => (fun x => attnBranch a.p a.v (a.n (R x)), a.μn * a.μatt)
    | .gdn g => (gdnBlockBranch g, g.μg)

/-- The FastArch3 backbone stack: the residual stack over the
hybrid blocks list. -/
noncomputable def fa3Stack (bs : List (FA3Block n ι)) :
    EuclideanSpace ℝ n → EuclideanSpace ℝ n :=
  resStack (fa3BlockList bs)

/-- The FastArch3 stack gain: `∏ (1 + μᵢ)` over the per-block
composed dampings (attention `μn·μatt` — unchanged by the rope
wrap, — and GDN `μg`). -/
noncomputable def fa3Gain (bs : List (FA3Block n ι)) : NNReal :=
  stackGain (fa3BlockList bs)

/-- Every block of a well-premised FastArch3 backbone satisfies the
 block hypothesis — the PREMISE-LEDGER dispatch: attention
blocks through the adapter composed with the isometry
pattern (`Isometry R` premise, constant unchanged), GDN blocks
through the adapter. Each hypothesis below is one premise (P1–P6). -/
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
FastArch3 backbone. Given (a) each block's premises
(P1–P6), (b) the head's certified drop `δ` at the stack output
(premise shape — `ceOneHot_next_le_param` instantiates it),
and (c) the head-loss Lipschitz premise `Lc` (P7), the composed
leak slack is `Lc·(∏ (1 + μᵢ) − 1)·‖dx‖` — the stack theorem
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
## The head loss on the Euclidean
 carrier

The abstract head-loss premise `LipschitzWith Lc loss` is
discharged per-instance for the parametric head at the
identity logit map, fixed label: the sup-norm 2-Lipschitz
estimate `headCE_le_of_abs_sub_le` transported to the Euclidean
carrier through the coordinate bound `|x i − y i| ≤ ‖x − y‖`
(‖·‖∞ ≤ ‖·‖₂), giving the honest constant `Lc = 2`. Non-ident
logit maps would need the map's own constant — not claimed.
-/

/-- The head CE of the carrier readout at a fixed label `t`
(identity logit map). -/
noncomputable def fa3HeadLoss {n : Type} [Fintype n] [Nonempty n]
    (t : n) (x : EuclideanSpace ℝ n) : ℝ :=
  Hagi.Model.SoftmaxHead.headCE .ident t (WithLp.ofLp x)

/-- Coordinate bound on the Euclidean carrier: the sup-norm is
dominated by the Euclidean norm (`‖·‖∞ ≤ ‖·‖₂`). -/
theorem euclid_coord_abs_sub_le {n : Type} [Fintype n]
    (x y : EuclideanSpace ℝ n) (i : n) :
    |x i - y i| ≤ ‖x - y‖ := by
  have h : (x i - y i) ^ 2 ≤ ‖x - y‖ ^ 2 := by
    have hs := Finset.single_le_sum
      (f := fun j : n => (x j - y j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have heq : ‖(x - y : EuclideanSpace ℝ n)‖ ^ 2
        = ∑ j, ((x - y : EuclideanSpace ℝ n) : n → ℝ) j ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    rw [heq]
    simpa using hs
  have hb : 0 ≤ ‖(x - y : EuclideanSpace ℝ n)‖ := norm_nonneg _
  obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' h hb
  exact abs_le.2 ⟨h1, h2⟩

/-- The head CE at the identity
logit map and fixed label is `2`-Lipschitz on the Euclidean
carrier — the honest readout constant `Lc = 2` (the sup-norm
estimate at `r = ‖x − y‖`). -/
theorem fastarch3_head_Lc {n : Type} [Fintype n] [Nonempty n]
    (t : n) : LipschitzWith 2 (fa3HeadLoss t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hxy : ∀ i, |WithLp.ofLp x i - WithLp.ofLp y i| ≤ ‖x - y‖ :=
    fun i => euclid_coord_abs_sub_le x y i
  have hxy' : ∀ i, |Hagi.Model.SoftmaxHead.LogitMap.ident.apply
      (WithLp.ofLp x i) - Hagi.Model.SoftmaxHead.LogitMap.ident.apply
      (WithLp.ofLp y i)| ≤ ‖x - y‖ := fun i => hxy i
  have h1 := Hagi.Model.SoftmaxHead.headCE_le_of_abs_sub_le
    .ident t (WithLp.ofLp x) (WithLp.ofLp y) ‖x - y‖ hxy'
  have h2 := Hagi.Model.SoftmaxHead.headCE_le_of_abs_sub_le
    .ident t (WithLp.ofLp y) (WithLp.ofLp x) ‖x - y‖
    (fun i => by rw [abs_sub_comm]; exact hxy' i)
  have habs : |fa3HeadLoss t x - fa3HeadLoss t y| ≤ 2 * ‖x - y‖ := by
    simp only [fa3HeadLoss]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  simpa [dist_eq_norm, Real.dist_eq] using habs

/-!
## Anchors (nonvacuity + numeric instance)
-/

/-- Rope-wrap premise nonvacuity (P4): the rotation IS an
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
