/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Model.BackboneTransfer
import Hagi.Core.Attention

set_option linter.style.header false

/-!
# Attention block transfer composition (E4 attention rung)

The attention rung of the E4 backbone ladder (TD E4-C300,
`.omc/tech-debt.md`): the existing softmax error-damping
certificate `Hagi.Core.attention_error_damped` is wired into the
C300 residual-transfer stack (`Hagi.Model.BackboneTransfer`).

The attention branch is the softmax-weighted value composition
`attnBranch p v x = ∑ i, p i • v i x`. The damping interface: the
carrier bounds the deviation of the weighted output under value
perturbations `e i` by `max_i ‖e i‖`; instantiating `e i` with the
value-map response `v i (x + dx) − v i x` gives the branch
perturbation bound (`attn_branch_damped`), and a uniform
per-value Lipschitz premise (`LipschitzWith μatt`) converts it
into a branch Lipschitz constant (`attn_branch_lipschitz`).

A pre-norm `n` enters as a `LipschitzWith μn` premise, so the
pre-norm attention branch `fun x => attnBranch p v (n x)` is
`(μn·μatt)`-Lipschitz (`attn_norm_branch_lipschitz`) — exactly
the C300 block hypothesis shape — and one attention block
(pre-norm + softmax-weighted branch + residual) satisfies the
C300 leak bound (`attention_block_transfer`). Stacks of attention
blocks (`AttnBlock`, `attnStack`, `attnGain`) inherit the
multiplicative C300 descent bound
(`attention_stack_transfer_descent`, `_strict`).

Honest scope: the softmax weight map (p depending on x through
the QK^T scores) is encapsulated by the fixed-probability
premise — the softmax-map Lipschitz rung is follow-up; RMSNorm
Lipschitz is premise-form (`μn`; ladder rung 4); RoPE exactness
(`Hagi.Core.RoPEMoments.rot_norm` preserves the pairwise-block
inner product, not a normed-space norm) is a NEXT rung; the full
FastArch3 forward/backward certificate is NOT claimed here.
-/

namespace Hagi.Model.AttentionTransfer

open Hagi.Model.Residual Hagi.Model.BackboneTransfer Hagi.Core

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {ι : Type*} [Fintype ι]

/-!
## Attention branch
-/

/-- Attention branch: the softmax-weighted value composition
`∑ i, p i • v i x` (weights premise-form: `p` is a fixed
probability distribution encapsulating the softmax/QK^T
structure). -/
noncomputable def attnBranch (p : ι → ℝ) (v : ι → X → X) (x : X) : X :=
  ∑ i, p i • v i x

/-- Damping wire: the branch perturbation is bounded by the
largest value-map response — the C307 instance of
`Hagi.Core.attention_error_damped` with value errors
`e i = v i (x + dx) − v i x`. -/
theorem attn_branch_damped (p : ι → ℝ) (v : ι → X → X)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (x dx : X) :
    ‖attnBranch p v (x + dx) - attnBranch p v x‖
      ≤ Finset.univ.sup'
        (by
          by_contra h
          have h0 : ∑ i, p i = 0 :=
            Finset.sum_eq_zero fun i _ => (h ⟨i, Finset.mem_univ i⟩).elim
          rw [h0] at hp1
          exact zero_ne_one hp1)
        fun i => ‖v i (x + dx) - v i x‖ := by
  have hsplit : attnBranch p v (x + dx)
      = ∑ i, p i • (v i x + (v i (x + dx) - v i x)) := by
    unfold attnBranch
    simp only [add_sub_cancel]
  rw [hsplit]
  exact attention_error_damped p (fun i => v i x)
    (fun i => v i (x + dx) - v i x) hp hp1

/-- Uniform value damping gives a branch Lipschitz constant: if
every value map is `μatt`-Lipschitz, the softmax-weighted branch
is `μatt`-Lipschitz (the sup' of the damped bound is dominated by
`μatt·‖dx‖`). -/
theorem attn_branch_lipschitz {p : ι → ℝ} {v : ι → X → X} {μatt : NNReal}
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hv : ∀ i, LipschitzWith μatt (v i)) :
    LipschitzWith μatt (attnBranch p v) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hd : ‖attnBranch p v (x + (y - x)) - attnBranch p v x‖
      ≤ Finset.univ.sup'
        (by
          by_contra h
          have h0 : ∑ i, p i = 0 :=
            Finset.sum_eq_zero fun i _ => (h ⟨i, Finset.mem_univ i⟩).elim
          rw [h0] at hp1
          exact zero_ne_one hp1)
        fun i => ‖v i (x + (y - x)) - v i x‖ :=
    attn_branch_damped p v hp hp1 x (y - x)
  have hkey : ∀ i : ι, ‖v i y - v i x‖ ≤ (μatt : ℝ) * ‖y - x‖ :=
    fun i => (hv i).norm_sub_le y x
  have hsup : (Finset.univ.sup'
        (by
          by_contra h
          have h0 : ∑ i, p i = 0 :=
            Finset.sum_eq_zero fun i _ => (h ⟨i, Finset.mem_univ i⟩).elim
          rw [h0] at hp1
          exact zero_ne_one hp1)
        fun i => ‖v i y - v i x‖) ≤ (μatt : ℝ) * ‖y - x‖ :=
    Finset.sup'_le _ _ fun i _ => hkey i
  rw [show x + (y - x) = y from by abel] at hd
  simpa [dist_eq_norm, norm_sub_rev] using le_trans hd hsup

/-!
## Pre-norm attention block
-/

/-- Pre-norm composition: a `μn`-Lipschitz norm map (`μn`
premise-form — the RMSNorm Lipschitz rung instantiates it later)
composed with the `μatt`-Lipschitz attention branch gives the
`(μn·μatt)`-Lipschitz pre-norm branch — exactly the C300 block
hypothesis shape. -/
theorem attn_norm_branch_lipschitz {n : X → X} {p : ι → ℝ}
    {v : ι → X → X} {μn μatt : NNReal} (hn : LipschitzWith μn n)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hv : ∀ i, LipschitzWith μatt (v i)) :
    LipschitzWith (μn * μatt) (fun x => attnBranch p v (n x)) := by
  have hb := attn_branch_lipschitz hp hp1 hv
  rw [mul_comm]
  exact hb.comp hn

/-- One attention block (pre-norm + softmax-weighted branch +
residual) satisfies the C300 leak bound: the loss at the realized
output exceeds the intended head output loss by at most the leak
`Lc·(μn·μatt)·‖dx‖`. -/
theorem attention_block_transfer {n : X → X} {p : ι → ℝ} {v : ι → X → X}
    {loss : X → ℝ} {μn μatt Lc : NNReal} (hn : LipschitzWith μn n)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hv : ∀ i, LipschitzWith μatt (v i))
    (hloss : LipschitzWith Lc loss) (x dx : X) :
    loss (resStep (fun y => attnBranch p v (n y)) (x + dx))
      ≤ loss (resStep (fun y => attnBranch p v (n y)) x + dx)
        + Lc * (μn * μatt) * ‖dx‖ :=
  residual_transfer_le (attn_norm_branch_lipschitz hn hp hp1 hv) hloss x dx

/-!
## Stack of attention blocks
-/

/-- One attention block record: pre-norm `n` (Lipschitz premise
`μn`), softmax weights `p` (probability premise), value maps `v`
(Lipschitz premise `μatt`). -/
structure AttnBlock (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] (ι : Type*) [Fintype ι] where
  /-- Pre-norm map (RMSNorm rung instantiates; `μn`-Lipschitz premise). -/
  n : X → X
  /-- Softmax weights (fixed probability distribution premise). -/
  p : ι → ℝ
  /-- Value maps (`μatt`-Lipschitz premise). -/
  v : ι → X → X
  /-- Pre-norm Lipschitz premise. -/
  μn : NNReal
  /-- Value-map Lipschitz premise. -/
  μatt : NNReal

/-- The pre-norm attention branch of a block record. -/
noncomputable def attnBlockBranch (b : AttnBlock X ι) : X → X :=
  fun y => attnBranch b.p b.v (b.n y)

/-- The C300 block list of attention blocks: each block carries
its composed damping `μn·μatt`. -/
noncomputable def attnBlockList (bs : List (AttnBlock X ι)) : List ((X → X) × NNReal) :=
  bs.map fun b => (attnBlockBranch b, b.μn * b.μatt)

/-- Stack of attention blocks: the C300 residual stack over the
composed dampings. -/
noncomputable def attnStack (bs : List (AttnBlock X ι)) : X → X :=
  resStack (attnBlockList bs)

/-- Multiplicative gain of an attention stack: `∏ (1 + μnᵢ·μattᵢ)`
(the C300 `stackGain` on the composed dampings). -/
noncomputable def attnGain (bs : List (AttnBlock X ι)) : NNReal :=
  stackGain (attnBlockList bs)

/-- Every attention block in a well-damped list satisfies the C300
block hypothesis (Lipschitz through the composed damping). -/
theorem attnBlockList_lipschitz (bs : List (AttnBlock X ι))
    (hn : ∀ b ∈ bs, LipschitzWith b.μn b.n)
    (hp : ∀ b ∈ bs, ∀ i, 0 ≤ b.p i)
    (hp1 : ∀ b ∈ bs, ∑ i, b.p i = 1)
    (hv : ∀ b ∈ bs, ∀ i, LipschitzWith b.μatt (b.v i)) :
    ∀ c ∈ attnBlockList bs, LipschitzWith c.2 c.1 := by
  intro c hc
  obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hc
  exact attn_norm_branch_lipschitz (hn b₀ hb₀) (hp b₀ hb₀)
    (hp1 b₀ hb₀) (hv b₀ hb₀)

/-- Certified head descent transfers through a stack of attention
blocks: the C300 stack theorem applied with the composed damping
`μnᵢ·μattᵢ` per block — leak slack
`Lc·(∏ (1 + μnᵢ·μattᵢ) − 1)·‖dx‖`. -/
theorem attention_stack_transfer_descent (bs : List (AttnBlock X ι))
    {loss : X → ℝ} {Lc : NNReal} {δ : ℝ}
    (hn : ∀ b ∈ bs, LipschitzWith b.μn b.n)
    (hp : ∀ b ∈ bs, ∀ i, 0 ≤ b.p i)
    (hp1 : ∀ b ∈ bs, ∑ i, b.p i = 1)
    (hv : ∀ b ∈ bs, ∀ i, LipschitzWith b.μatt (b.v i))
    (hloss : LipschitzWith Lc loss) (x dx : X)
    (hdrop : loss (attnStack bs x + dx) ≤ loss (attnStack bs x) - δ) :
    loss (attnStack bs (x + dx))
      ≤ loss (attnStack bs x) - δ
        + Lc * ((attnGain bs : ℝ) - 1) * ‖dx‖ := by
  have hG : attnStack bs = resStack (attnBlockList bs) := rfl
  have hgain : (attnGain bs : ℝ)
      = (stackGain (attnBlockList bs) : ℝ) := rfl
  rw [hG, hgain]
  exact resStack_transfer_descent _ (attnBlockList_lipschitz bs hn hp hp1 hv)
    hloss x dx hdrop

/-- Strict composed decrease through the attention stack: the
certified drop `δ` beats the composed stack leak slack. -/
theorem attention_stack_transfer_descent_strict (bs : List (AttnBlock X ι))
    {loss : X → ℝ} {Lc : NNReal} {δ : ℝ}
    (hn : ∀ b ∈ bs, LipschitzWith b.μn b.n)
    (hp : ∀ b ∈ bs, ∀ i, 0 ≤ b.p i)
    (hp1 : ∀ b ∈ bs, ∑ i, b.p i = 1)
    (hv : ∀ b ∈ bs, ∀ i, LipschitzWith b.μatt (b.v i))
    (hloss : LipschitzWith Lc loss) (x dx : X)
    (hdrop : loss (attnStack bs x + dx) ≤ loss (attnStack bs x) - δ)
    (hstrict : (Lc : ℝ) * ((attnGain bs : ℝ) - 1) * ‖dx‖ < δ) :
    loss (attnStack bs (x + dx)) < loss (attnStack bs x) := by
  have h := attention_stack_transfer_descent bs hn hp hp1 hv hloss x dx hdrop
  linarith

/-!
## Scalar nonvacuity anchors (μ_att = 3/10, μ_res = 2/10)
-/

/-- Anchor: two blocks with composed dampings `μ_att = 3/10` and
`μ_res = 2/10` have stack leak factor
`(1 + 3/10)(1 + 2/10) − 1 = 28/50` per unit step. -/
example : (1 + (3 / 10 : ℝ)) * (1 + 2 / 10) - 1 = 28 / 50 := by
  norm_num

/-- Anchor: the multiplicative composition `28/50` dominates the
additive damping sum `3/10 + 2/10` (the Σ form is weaker). -/
example : (3 / 10 + 2 / 10 : ℝ)
    ≤ (1 + 3 / 10) * (1 + 2 / 10) - 1 := by
  norm_num

end Hagi.Model.AttentionTransfer
