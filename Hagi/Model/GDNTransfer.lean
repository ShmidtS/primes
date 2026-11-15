/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Model.AttentionTransfer
import Hagi.Model.GatedCEGradient
import Hagi.Architecture.ManifoldHyperConn

set_option linter.style.header false

/-!
# GDN block transfer composition (E4 GDN rung, hybrid payoff)

The GDN rung of the E4 backbone ladder (TD E4-C300/C309 remaining
rung 1: "GDN RAM read/write perturbation rung"): the GDN side of
the hybrid attention+GDN backbone is wired into the C300 residual
transfer stack (`Hagi.Model.BackboneTransfer`), and the HYBRID
payoff theorem lands — a stack mixing attention blocks and GDN
blocks descends with the product gain.

GDN-form verdict (the carrier survey pin): the repository carries
GDN in three distinct forms, and the C300 block form must be
matched honestly. (1) `Hagi.Model.GDNBridge` is one-hot RAM
addressing (C254 `gdn_lag1_alignment`, `gdn_ram_roundtrip`) —
read/write semantics, no state-space operator to wire; (2)
`Hagi.External.MemT.GDN2` is the Gated DeltaNet-2 MEMORY update
`M̃' = (I − UᵀU)·D·M̃ + Uᵀ(ω ⊙ V)` (arXiv:2610.26825), affine in
the memory matrix, bounded in `rowSumNorm` (`gdn2_step_bound`) —
matrix-space, not a state map; (3) `Hagi.Architecture.
ManifoldHyperConn` (C231) is the mHC STATE MIXING `x ↦ M *ᵥ x`
with `M` doubly stochastic. The GDN BLOCK wired here is form (3):
the doubly-stochastic state mixing branch, with the GDN nonlinear
gate (form (2) δ/β/σ gate structure) entering PREMISE-FORM as a
`μg`-Lipschitz pre-gate — exactly mirroring the C307 pre-norm
premise (discharged per-instance later, as C309 did for μn).

Carrier transport: `gdnMix M x = WithLp.toLp 2 (M *ᵥ ofLp x)` on
`EuclideanSpace ℝ n` (the transfer stack's abstract carrier),
through the same WithLp transport as C309.

* `gdnMix_lipschitz` — MAIN GDN lemma: `IsDoublyStochastic M ⇒
  LipschitzWith 1 (gdnMix M)` — the C231 `doublyStochastic_sq_le`
  contraction (Jensen/Cauchy per row + column redistribution)
  applied to the difference, lifted to the Euclidean norm through
  the `real_norm_sq_eq` bridge (`gdnMix_norm_sub_le`).
* `gdn_branch_lipschitz` — pre-gate μg ∘ mixing ⇒ `μg`-Lipschitz:
  the C300 block hypothesis shape with the gate honest premise.
* `gdnGateTanh` / `gdnGateTanh_lipschitz` — P5 PER-INSTANCE
  DISCHARGE (C313, the C309 pattern): the componentwise-saturating
  tanh gate family is `1`-Lipschitz on the Euclidean carrier
  (μg = 1 exact: per-coordinate |tanh x − tanh y| ≤ |x − y| via
  the Mathlib mean-value route, transported through the
  `real_norm_sq_eq` bridge).
* `gdn_branch_lipschitz_tanh` / `gdn_block_transfer_tanh` — the
  gate and block theorems instantiated at the tanh gate (μg = 1).
* `gdn_block_transfer` — one GDN block (gate + doubly-stochastic
  mixing + residual) satisfies the C300 leak bound `Lc·μg·‖dx‖`.
* `GdnBlock` / `gdnBlockList` / `gdnStack` / `gdnGain` /
  `gdn_stack_transfer_descent` (+ `_strict`) — the C307 attention
  stack pattern mirrored on the GDN side, gain `∏ (1 + μgᵢ)`.
* `HybBlock` / `hybBlockList` / `hybStack` / `hybGain` /
  `hybrid_stack_transfer_descent` (+ `_strict`) — the HYBRID
  stack: an inductive over attention blocks (`AttnBlock` on the
  same Euclidean carrier) and GDN blocks, each block carrying its
own composed μᵢ (attention `μn·μatt`, GDN `μg`); the C300 stack
instantiated over the heterogeneous blocks list with product
gain — both block-type adapters now exist.

Honest scope: the GDNBridge RAM read/write semantics and the GDN2
memory update (projection `I − UᵀU`, decay `D`, gated write
`ω ⊙ V`) are NOT claimed as state contractions — only the
mHC-style doubly-stochastic mixing branch is certified, and the
nonlinear gate stays premise-form (μg); Sinkhorn balancing is NOT
claimed (`IsDoublyStochastic M` is a premise — C231's honest
boundary); the softmax weight map stays premise-form (C307); the
full FastArch3 forward/backward certificate is NOT claimed here.
-/

namespace Hagi.Model.GDNTransfer

open Matrix Set Hagi.Model.Residual Hagi.Model.BackboneTransfer
  Hagi.Model.AttentionTransfer Hagi.Architecture.ManifoldHyperConn

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
## The mixing branch
-/

/-- Doubly-stochastic state mixing on the Euclidean carrier:
`gdnMix M x = M *ᵥ x` through the WithLp transport (the mHC
stream form; `M` premise-form doubly stochastic). -/
noncomputable def gdnMix (M : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n :=
  WithLp.toLp 2 (M *ᵥ WithLp.ofLp x)

theorem gdnMix_sub (M : Matrix n n ℝ) (x y : EuclideanSpace ℝ n) :
    gdnMix M x - gdnMix M y
      = WithLp.toLp 2 (M *ᵥ (WithLp.ofLp x - WithLp.ofLp y)) := by
  unfold gdnMix
  ext i
  rw [WithLp.ofLp_sub]
  simp only [WithLp.ofLp_toLp, Pi.sub_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_sub_distrib]
  congr 1 with j
  rw [Pi.sub_apply]
  ring

/-- The mixing difference bound: the C231 `doublyStochastic_sq_le`
contraction applied to the difference, lifted to the Euclidean
norm through the `real_norm_sq_eq` bridge. -/
theorem gdnMix_norm_sub_le {M : Matrix n n ℝ}
    (hM : IsDoublyStochastic M) (x y : EuclideanSpace ℝ n) :
    ‖gdnMix M x - gdnMix M y‖ ≤ ‖x - y‖ := by
  have h1 : ‖gdnMix M x - gdnMix M y‖ ^ 2
      = ∑ i, (M *ᵥ (WithLp.ofLp x - WithLp.ofLp y)) i ^ 2 := by
    rw [gdnMix_sub, EuclideanSpace.real_norm_sq_eq, WithLp.ofLp_toLp]
  have h2 := doublyStochastic_sq_le M hM (WithLp.ofLp x - WithLp.ofLp y)
  have h3 : ‖x - y‖ ^ 2
      = ∑ i, (WithLp.ofLp x - WithLp.ofLp y) i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, WithLp.ofLp_toLp,
      show (WithLp.ofLp x - WithLp.ofLp y) = WithLp.ofLp (x - y) from
        (WithLp.ofLp_sub 2 x y).symm]
  have h4 : ‖gdnMix M x - gdnMix M y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [h1, h3]; exact h2
  exact le_of_sq_le_sq h4 (norm_nonneg _)

/-- MAIN GDN lemma: a doubly-stochastic mixing matrix gives a
`1`-Lipschitz state mixing map on the Euclidean carrier — the C231
no-growth machinery (mHC `doublyStochastic_sq_le`) in the C300
block-hypothesis shape. -/
theorem gdnMix_lipschitz {M : Matrix n n ℝ} (hM : IsDoublyStochastic M) :
    LipschitzWith 1 (gdnMix M) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := gdnMix_norm_sub_le hM x y
  simpa [dist_eq_norm] using h

/-!
## The gated GDN block branch
-/

/-- Pre-gated mixing branch: a `μg`-Lipschitz gate (the GDN
nonlinear gate, premise-form — the honest scope of this rung)
composed with `1`-Lipschitz doubly-stochastic mixing is
`μg`-Lipschitz — the C300 block hypothesis shape. -/
theorem gdn_branch_lipschitz {gate : EuclideanSpace ℝ n → EuclideanSpace ℝ n}
    {μg : NNReal} (hg : LipschitzWith μg gate) {M : Matrix n n ℝ}
    (hM : IsDoublyStochastic M) :
    LipschitzWith μg (fun x => gdnMix M (gate x)) := by
  show LipschitzWith μg (gdnMix M ∘ gate)
  simpa [mul_one] using (gdnMix_lipschitz hM).comp hg

/-- One GDN block (gate + doubly-stochastic mixing + residual)
satisfies the C300 leak bound: the loss at the realized output
exceeds the intended head output loss by at most `Lc·μg·‖dx‖`. -/
theorem gdn_block_transfer {gate : EuclideanSpace ℝ n → EuclideanSpace ℝ n}
    {loss : EuclideanSpace ℝ n → ℝ} {μg Lc : NNReal}
    {M : Matrix n n ℝ} (hg : LipschitzWith μg gate)
    (hM : IsDoublyStochastic M)
    (hloss : LipschitzWith Lc loss) (x dx : EuclideanSpace ℝ n) :
    loss (resStep (fun y => gdnMix M (gate y)) (x + dx))
      ≤ loss (resStep (fun y => gdnMix M (gate y)) x + dx)
        + Lc * μg * ‖dx‖ :=
  residual_transfer_le (gdn_branch_lipschitz hg hM) hloss x dx

/-!
## P5 per-instance discharge: the tanh gate family (C313)

The abstract gate premise `LipschitzWith μg gate` is discharged
per-instance for the componentwise-saturating tanh family — the
scalar activation shape of the GDN2 δ/β/σ gate — with the honest
constant `μg = 1`. Multi-argument δ/β/σ gate compositions are NOT
claimed 1-Lipschitz (their constants remain per-instance data).

Dedup note (C319): the scalar fact `|tanh x - tanh y| ≤ |x - y|`
(formerly a private `tanh_abs_sub_le` twin here) lives as the
public `Hagi.Model.GatedCEGradient.abs_tanh_sub_le` — the private
twin was a statement duplicate exposed by the lock regeneration.
-/

/-- The componentwise-saturating tanh gate on the Euclidean
 carrier (the scalar activation shape of the GDN δ/β/σ gate). -/
noncomputable def gdnGateTanh (x : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n :=
  WithLp.toLp 2 (fun i => Real.tanh (WithLp.ofLp x i))

/-- P5 DISCHARGE (per-instance, C313): the componentwise tanh
gate is `1`-Lipschitz on the Euclidean carrier — the honest
constant `μg = 1` (each coordinate 1-Lipschitz, transported
through the `real_norm_sq_eq` bridge). -/
theorem gdnGateTanh_lipschitz :
    LipschitzWith 1 (gdnGateTanh (n := n)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h1 : ‖gdnGateTanh x - gdnGateTanh y‖ ^ 2
      = ∑ i, (Real.tanh (WithLp.ofLp x i)
        - Real.tanh (WithLp.ofLp y i)) ^ 2 := by
    have hsub : gdnGateTanh x - gdnGateTanh y
        = WithLp.toLp 2 (fun i => Real.tanh (WithLp.ofLp x i)
          - Real.tanh (WithLp.ofLp y i)) := by
      unfold gdnGateTanh
      ext i
      simp [WithLp.ofLp_sub]
    rw [hsub, EuclideanSpace.real_norm_sq_eq, WithLp.ofLp_toLp]
  have h2 : ‖x - y‖ ^ 2
      = ∑ i, (WithLp.ofLp x i - WithLp.ofLp y i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, WithLp.ofLp_sub]
    simp only [Pi.sub_apply]
  have h3 : ∀ i, (Real.tanh (WithLp.ofLp x i)
      - Real.tanh (WithLp.ofLp y i)) ^ 2
      ≤ (WithLp.ofLp x i - WithLp.ofLp y i) ^ 2 := fun i => by
    have h := GatedCEGradient.abs_tanh_sub_le (WithLp.ofLp x i) (WithLp.ofLp y i)
    have h1 : (Real.tanh (WithLp.ofLp x i) - Real.tanh (WithLp.ofLp y i)) ^ 2
        = |Real.tanh (WithLp.ofLp x i) - Real.tanh (WithLp.ofLp y i)|
          * |Real.tanh (WithLp.ofLp x i) - Real.tanh (WithLp.ofLp y i)| := by
      rw [abs_mul_abs_self]; ring_nf
    have h2 : (WithLp.ofLp x i - WithLp.ofLp y i) ^ 2
        = |WithLp.ofLp x i - WithLp.ofLp y i|
          * |WithLp.ofLp x i - WithLp.ofLp y i| := by
      rw [abs_mul_abs_self]; ring_nf
    rw [h1, h2]
    exact mul_le_mul h h (abs_nonneg _) (abs_nonneg _)
  have h4 : ‖gdnGateTanh x - gdnGateTanh y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [h1, h2]
    exact Finset.sum_le_sum fun i _ => h3 i
  rw [dist_eq_norm]
  have h5 := le_of_sq_le_sq h4 (norm_nonneg _)
  simpa [mul_one, dist_eq_norm] using h5

/-- The gated branch instantiated at the tanh gate: `1`-Lipschitz
(μg = 1 composed with the `1`-Lipschitz doubly-stochastic mix). -/
theorem gdn_branch_lipschitz_tanh {M : Matrix n n ℝ}
    (hM : IsDoublyStochastic M) :
    LipschitzWith 1 (fun x => gdnMix M (gdnGateTanh x)) :=
  gdn_branch_lipschitz gdnGateTanh_lipschitz hM

/-- One GDN block with the tanh gate satisfies the C300 leak bound
at the honest constant `Lc·1·‖dx‖`. -/
theorem gdn_block_transfer_tanh {loss : EuclideanSpace ℝ n → ℝ}
    {Lc : NNReal} {M : Matrix n n ℝ}
    (hM : IsDoublyStochastic M)
    (hloss : LipschitzWith Lc loss) (x dx : EuclideanSpace ℝ n) :
    loss (resStep (fun y => gdnMix M (gdnGateTanh y)) (x + dx))
      ≤ loss (resStep (fun y => gdnMix M (gdnGateTanh y)) x + dx)
        + Lc * 1 * ‖dx‖ :=
  gdn_block_transfer gdnGateTanh_lipschitz hM hloss x dx

/-!
## Stack of GDN blocks
-/

/-- One GDN block record: nonlinear gate (Lipschitz premise `μg`)
and doubly-stochastic mixing matrix `M` (premise). -/
structure GdnBlock (n : Type*) [Fintype n] [DecidableEq n] where
  /-- GDN nonlinear gate (`μg`-Lipschitz premise-form). -/
  gate : EuclideanSpace ℝ n → EuclideanSpace ℝ n
  /-- Gate Lipschitz premise. -/
  μg : NNReal
  /-- Doubly-stochastic mixing matrix (premise-form, C231). -/
  M : Matrix n n ℝ

/-- The pre-gated mixing branch of a block record. -/
noncomputable def gdnBlockBranch (b : GdnBlock n) :
    EuclideanSpace ℝ n → EuclideanSpace ℝ n :=
  fun x => gdnMix b.M (b.gate x)

/-- The C300 block list of GDN blocks: each block carries its gate
damping `μg` (the mixing contributes `1`). -/
noncomputable def gdnBlockList (bs : List (GdnBlock n)) :
    List ((EuclideanSpace ℝ n → EuclideanSpace ℝ n) × NNReal) :=
  bs.map fun b => (gdnBlockBranch b, b.μg)

/-- Every GDN block in a well-damped list satisfies the C300 block
hypothesis (Lipschitz through the gate damping). -/
theorem gdnBlockList_lipschitz (bs : List (GdnBlock n))
    (hg : ∀ b ∈ bs, LipschitzWith b.μg b.gate)
    (hM : ∀ b ∈ bs, IsDoublyStochastic b.M) :
    ∀ c ∈ gdnBlockList bs, LipschitzWith c.2 c.1 := by
  intro c hc
  obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hc
  exact gdn_branch_lipschitz (hg b₀ hb₀) (hM b₀ hb₀)

/-- Stack of GDN blocks: the C300 residual stack over the gate
dampings. -/
noncomputable def gdnStack (bs : List (GdnBlock n)) :
    EuclideanSpace ℝ n → EuclideanSpace ℝ n :=
  resStack (gdnBlockList bs)

/-- Multiplicative gain of a GDN stack: `∏ (1 + μgᵢ)` (the C300
`stackGain` on the gate dampings; the doubly-stochastic mixing is
`1`-Lipschitz and contributes no growth — C231 no-growth). -/
noncomputable def gdnGain (bs : List (GdnBlock n)) : NNReal :=
  stackGain (gdnBlockList bs)

/-- Certified head descent transfers through a stack of GDN
blocks: the C300 stack theorem with the gate damping per block —
leak slack `Lc·(∏ (1 + μgᵢ) − 1)·‖dx‖`. -/
theorem gdn_stack_transfer_descent (bs : List (GdnBlock n))
    {loss : EuclideanSpace ℝ n → ℝ} {Lc : NNReal} {δ : ℝ}
    (hg : ∀ b ∈ bs, LipschitzWith b.μg b.gate)
    (hM : ∀ b ∈ bs, IsDoublyStochastic b.M)
    (hloss : LipschitzWith Lc loss) (x dx : EuclideanSpace ℝ n)
    (hdrop : loss (gdnStack bs x + dx) ≤ loss (gdnStack bs x) - δ) :
    loss (gdnStack bs (x + dx))
      ≤ loss (gdnStack bs x) - δ
        + Lc * ((gdnGain bs : ℝ) - 1) * ‖dx‖ :=
  resStack_transfer_descent _ (gdnBlockList_lipschitz bs hg hM) hloss x dx hdrop

/-- Strict composed decrease through the GDN stack: the certified
drop `δ` beats the composed stack leak slack. -/
theorem gdn_stack_transfer_descent_strict (bs : List (GdnBlock n))
    {loss : EuclideanSpace ℝ n → ℝ} {Lc : NNReal} {δ : ℝ}
    (hg : ∀ b ∈ bs, LipschitzWith b.μg b.gate)
    (hM : ∀ b ∈ bs, IsDoublyStochastic b.M)
    (hloss : LipschitzWith Lc loss) (x dx : EuclideanSpace ℝ n)
    (hdrop : loss (gdnStack bs x + dx) ≤ loss (gdnStack bs x) - δ)
    (hstrict : (Lc : ℝ) * ((gdnGain bs : ℝ) - 1) * ‖dx‖ < δ) :
    loss (gdnStack bs (x + dx)) < loss (gdnStack bs x) := by
  have h := gdn_stack_transfer_descent bs hg hM hloss x dx hdrop
  linarith

/-!
## The hybrid stack (the rung payoff)
-/

variable {ι : Type*} [Fintype ι]

/-- A hybrid backbone block: either an attention block (C307, on
the same Euclidean carrier) or a GDN block (this rung) — each
constructor carries its own block premises. -/
inductive HybBlock (n : Type*) [Fintype n] [DecidableEq n]
    (ι : Type*) [Fintype ι] where
  /-- Attention block (pre-norm + softmax-weighted branch). -/
  | att : AttnBlock (EuclideanSpace ℝ n) ι → HybBlock n ι
  /-- GDN block (gate + doubly-stochastic mixing). -/
  | gdn : GdnBlock n → HybBlock n ι

/-- The C300 block list of a hybrid stack: attention blocks carry
their composed damping `μn·μatt`, GDN blocks their gate damping
`μg` — a heterogeneous blocks list where each block carries its
own `μᵢ`. -/
noncomputable def hybBlockList (bs : List (HybBlock n ι)) :
    List ((EuclideanSpace ℝ n → EuclideanSpace ℝ n) × NNReal) :=
  bs.map fun b => match b with
    | .att a => (attnBlockBranch a, a.μn * a.μatt)
    | .gdn g => (gdnBlockBranch g, g.μg)

/-- Hybrid stack: the C300 residual stack over the heterogeneous
blocks list. -/
noncomputable def hybStack (bs : List (HybBlock n ι)) :
    EuclideanSpace ℝ n → EuclideanSpace ℝ n :=
  resStack (hybBlockList bs)

/-- Multiplicative gain of a hybrid stack: `∏ (1 + μᵢ)` over the
per-block composed dampings (attention `μn·μatt`, GDN `μg`). -/
noncomputable def hybGain (bs : List (HybBlock n ι)) : NNReal :=
  stackGain (hybBlockList bs)

/-- Every block of a well-premised hybrid list satisfies the C300
block hypothesis: attention blocks through the C307 adapter, GDN
blocks through the C231-backed mixing adapter. -/
theorem hybBlockList_lipschitz (bs : List (HybBlock n ι))
    (hatt : ∀ a : AttnBlock (EuclideanSpace ℝ n) ι,
      HybBlock.att a ∈ bs → LipschitzWith a.μn a.n
        ∧ (∀ i, 0 ≤ a.p i) ∧ (∑ i, a.p i = 1)
        ∧ (∀ i, LipschitzWith a.μatt (a.v i)))
    (hgdn : ∀ g : GdnBlock n, HybBlock.gdn g ∈ bs →
      LipschitzWith g.μg g.gate ∧ IsDoublyStochastic g.M) :
    ∀ c ∈ hybBlockList bs, LipschitzWith c.2 c.1 := by
  intro c hc
  obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hc
  cases b₀ with
  | att a =>
      obtain ⟨h1, h2, h3, h4⟩ := hatt a hb₀
      exact attn_norm_branch_lipschitz h1 h2 h3 h4
  | gdn g =>
      obtain ⟨h1, h2⟩ := hgdn g hb₀
      exact gdn_branch_lipschitz h1 h2

/-- HYBRID payoff: certified head descent transfers through a
stack mixing attention blocks AND GDN blocks — the C300 stack
theorem instantiated over the heterogeneous blocks list, product
gain `∏ (1 + μᵢ)`, leak slack
`Lc·(∏ (1 + μᵢ) − 1)·‖dx‖`. -/
theorem hybrid_stack_transfer_descent (bs : List (HybBlock n ι))
    {loss : EuclideanSpace ℝ n → ℝ} {Lc : NNReal} {δ : ℝ}
    (hatt : ∀ a : AttnBlock (EuclideanSpace ℝ n) ι,
      HybBlock.att a ∈ bs → LipschitzWith a.μn a.n
        ∧ (∀ i, 0 ≤ a.p i) ∧ (∑ i, a.p i = 1)
        ∧ (∀ i, LipschitzWith a.μatt (a.v i)))
    (hgdn : ∀ g : GdnBlock n, HybBlock.gdn g ∈ bs →
      LipschitzWith g.μg g.gate ∧ IsDoublyStochastic g.M)
    (hloss : LipschitzWith Lc loss) (x dx : EuclideanSpace ℝ n)
    (hdrop : loss (hybStack bs x + dx) ≤ loss (hybStack bs x) - δ) :
    loss (hybStack bs (x + dx))
      ≤ loss (hybStack bs x) - δ
        + Lc * ((hybGain bs : ℝ) - 1) * ‖dx‖ :=
  resStack_transfer_descent _ (hybBlockList_lipschitz bs hatt hgdn)
    hloss x dx hdrop

/-- Strict composed decrease through the hybrid stack: the
certified drop `δ` beats the composed hybrid leak slack. -/
theorem hybrid_stack_transfer_descent_strict (bs : List (HybBlock n ι))
    {loss : EuclideanSpace ℝ n → ℝ} {Lc : NNReal} {δ : ℝ}
    (hatt : ∀ a : AttnBlock (EuclideanSpace ℝ n) ι,
      HybBlock.att a ∈ bs → LipschitzWith a.μn a.n
        ∧ (∀ i, 0 ≤ a.p i) ∧ (∑ i, a.p i = 1)
        ∧ (∀ i, LipschitzWith a.μatt (a.v i)))
    (hgdn : ∀ g : GdnBlock n, HybBlock.gdn g ∈ bs →
      LipschitzWith g.μg g.gate ∧ IsDoublyStochastic g.M)
    (hloss : LipschitzWith Lc loss) (x dx : EuclideanSpace ℝ n)
    (hdrop : loss (hybStack bs x + dx) ≤ loss (hybStack bs x) - δ)
    (hstrict : (Lc : ℝ) * ((hybGain bs : ℝ) - 1) * ‖dx‖ < δ) :
    loss (hybStack bs (x + dx)) < loss (hybStack bs x) := by
  have h := hybrid_stack_transfer_descent bs hatt hgdn hloss x dx hdrop
  linarith

/-!
## Nonvacuity anchors
-/

/-- Nonvacuity of the mixing premise: the identity matrix is
doubly stochastic (permutation matrices give the tight case —
C231's own boundary note). -/
example : IsDoublyStochastic (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  refine ⟨⟨fun i j => by simp [Matrix.one_apply]; split_ifs <;> norm_num,
      fun i => ?_⟩, fun j => ?_⟩
  · simp only [Matrix.one_apply, Finset.sum_ite_eq]; simp
  · simp only [Matrix.one_apply, Finset.sum_ite_eq']; simp

/-- Anchor: a hybrid stack with one attention block (composed
damping `3/10`) and one GDN block (gate damping `2/10`) has leak
factor `(1 + 3/10)(1 + 2/10) − 1 = 14/25` per unit step. -/
example : (1 + (3 / 10 : ℝ)) * (1 + 2 / 10) - 1 = 14 / 25 := by
  norm_num

/-- Anchor: the multiplicative hybrid composition `14/25`
dominates the additive damping sum `3/10 + 2/10` (the Σ form is
weaker). -/
example : (3 / 10 + 2 / 10 : ℝ)
    ≤ (1 + 3 / 10) * (1 + 2 / 10) - 1 := by
  norm_num

/-- ANCHOR (C313): numeric μg composition — a GDN block with the
tanh gate (μg = 1, `gdnGateTanh_lipschitz`) has per-unit leak
`(1 + 1) − 1 = 1`, and the multiplicative form dominates the
additive damping sum (Σ form weaker, as in the hybrid anchor). -/
example : (1 + (1:ℝ)) - 1 = 1 := by norm_num

example : ((1:ℝ)) ≤ (1 + 1) - 1 := by norm_num

end Hagi.Model.GDNTransfer
