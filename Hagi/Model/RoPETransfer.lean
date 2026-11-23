/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Hagi.Model.AttentionTransfer
import Hagi.Core.RoPEMoments

set_option linter.style.header false

/-!
# RoPE rotation isometry transfer composition (E4 rope rung)

The rope rung of the E4 backbone ladder (TD E4-C300/C307 notes):
the existing rotary fact `Hagi.Core.RoPEMoments.rot_norm` preserves
the pairwise-block inner product `pairInner x x` (same-vector form
only), and this rung upgrades it to a genuine NORMED-SPACE isometry
and wires it into the transfer stack.

The upgrade route (probe-verified):

* `rope_pair_inner` — the FULL bilinear preservation:
  `pairInner (rotVec θ m x) (rotVec θ m y) = pairInner x y` (the
  per-block 2×2 rotation is orthogonal; `rot_norm` is the diagonal
  specialization y = x). This is the exact bridge the carrier
  supports — `rot_norm` alone (same-vector) does NOT give a normed
  isometry; the bilinear form does.
* `toEuc`/`fromEuc` — the carrier transport: `Fin d → ℝ × ℝ` is
  carried to `EuclideanSpace ℝ (Fin d ⊕ Fin d)` (the norm the
  transfer stack quantifies over), with
  `‖toEuc x‖ ^ 2 = pairInner x x` (`toEuc_norm_sq`).
* `rotEuc` + `rope_isometry` — the transported rotation
  `toEuc ∘ rotVec θ m ∘ fromEuc` is an `Isometry` of the Euclidean
  carrier: bilinear preservation on the difference vector gives
  `‖R a − R b‖ = ‖a − b‖`.
* `rope_block_transfer` / `rope_block_post_transfer` — isometry
  pre/post-composition keeps a Lipschitz constant unchanged
  (`LipschitzWith μ (f ∘ R)` from `LipschitzWith μ f`).
* `attention_block_rope_transfer` — a RoPE-wrapped pre-norm
  attention block satisfies the SAME leak bound at the
  unchanged composed damping `μn·μatt`.
* `attnRopeBlockList`, `attnRopeStack`, `attnRopeGain` — stacks of
  rope-wrapped blocks: the gain is UNCHANGED (`attnRopeGain_eq`,
  `stackGain_wrap`), and the stack descent theorem applies
  verbatim (`attention_rope_stack_transfer_descent`, `_strict`).

Anchor: the concrete 4-dimensional rotation by π/3 (d = 2) is
norm-preserving on a specific vector.

Honest scope: the isometry is on the Euclidean carrier
`EuclideanSpace ℝ (Fin d ⊕ Fin d)` through the `toEuc` transport —
no operator-norm statement, no matrix-orthogonality claim
(`RᵀR = I` form), no softmax-map Lipschitz, no RMSNorm constant;
those stay premise-form / future rungs .
-/

namespace Hagi.Model.RoPETransfer

open Finset Hagi.Core Hagi.Model.Residual Hagi.Model.BackboneTransfer
  Hagi.Model.AttentionTransfer

variable {d : ℕ}
variable {ι : Type*} [Fintype ι]

/-!
## Full bilinear preservation
-/

/-- The RoPE rotation preserves the pairwise-block inner product in
the FULL bilinear form: per block the 2×2 rotation is orthogonal
(`cos² + sin² = 1`), so `pairInner` is preserved for any pair of
vectors. `Hagi.Core.RoPEMoments.rot_norm` is the diagonal
specialization `y = x`. -/
theorem rope_pair_inner (θ : Fin d → ℝ) (m : ℕ) (x y : Fin d → ℝ × ℝ) :
    pairInner (rotVec θ m x) (rotVec θ m y) = pairInner x y := by
  unfold pairInner rotVec
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (Real.cos (θ j * m)) ^ 2 + (Real.sin (θ j * m)) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  linear_combination (norm := ring_nf)
    h * ((x j).1 * (y j).1 + (x j).2 * (y j).2)

/-- The rotation is additive in the vector: `R (x − y) = R x − R y`
(the per-block rotation matrix is linear). -/
theorem rotVec_sub (θ : Fin d → ℝ) (m : ℕ) (x y : Fin d → ℝ × ℝ) :
    rotVec θ m (x - y) = rotVec θ m x - rotVec θ m y := by
  funext j
  unfold rotVec
  simp only [Pi.sub_apply]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-!
## Carrier transport to the Euclidean norm
-/

/-- Transport a pairwise-block vector to the Euclidean carrier
(first components on `Sum.inl`, second on `Sum.inr`). -/
def toEuc (x : Fin d → ℝ × ℝ) : EuclideanSpace ℝ (Fin d ⊕ Fin d) :=
  WithLp.toLp 2 (Sum.elim (fun j => (x j).1) (fun j => (x j).2))

/-- Transport back from the Euclidean carrier. -/
def fromEuc (z : EuclideanSpace ℝ (Fin d ⊕ Fin d)) : Fin d → ℝ × ℝ :=
  fun j => ((WithLp.ofLp z) (Sum.inl j), (WithLp.ofLp z) (Sum.inr j))

theorem fromEuc_toEuc (x : Fin d → ℝ × ℝ) : fromEuc (toEuc x) = x := by
  funext j
  unfold fromEuc toEuc
  simp

theorem toEuc_fromEuc (z : EuclideanSpace ℝ (Fin d ⊕ Fin d)) :
    toEuc (fromEuc z) = z := by
  unfold fromEuc toEuc
  ext i
  cases i <;> rfl

theorem toEuc_sub (u v : Fin d → ℝ × ℝ) :
    toEuc (u - v) = toEuc u - toEuc v := by
  unfold toEuc
  rw [← WithLp.toLp_sub]
  ext i
  cases i <;> simp

/-- The Euclidean norm of the transport is exactly the `pairInner`
norm: `‖toEuc x‖ ^ 2 = pairInner x x`. -/
theorem toEuc_norm_sq (x : Fin d → ℝ × ℝ) :
    ‖toEuc x‖ ^ 2 = pairInner x x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold toEuc pairInner
  rw [show (univ : Finset (Fin d ⊕ Fin d)) = univ.disjSum univ from
      Finset.univ_disjSum_univ.symm, Finset.sum_disjSum]
  simp only [Sum.elim_inl, Sum.elim_inr, sq]
  rw [← Finset.sum_add_distrib]

/-!
## The isometry
-/

/-- The RoPE rotation on the Euclidean carrier: transport, rotate,
transport back. -/
noncomputable def rotEuc (θ : Fin d → ℝ) (m : ℕ) :
    EuclideanSpace ℝ (Fin d ⊕ Fin d) → EuclideanSpace ℝ (Fin d ⊕ Fin d) :=
  fun z => toEuc (rotVec θ m (fromEuc z))

/-- The RoPE rotation is an isometry of the Euclidean carrier:
bilinear `pairInner` preservation on the difference vector gives
`‖R a − R b‖ = ‖a − b‖`. -/
theorem rope_isometry (θ : Fin d → ℝ) (m : ℕ) : Isometry (rotEuc θ m) := by
  refine Isometry.of_dist_eq fun a b => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : rotEuc θ m a - rotEuc θ m b
      = toEuc (rotVec θ m (fromEuc a - fromEuc b)) := by
    unfold rotEuc
    rw [rotVec_sub, ← toEuc_sub]
  have h1 : ‖toEuc (rotVec θ m (fromEuc a - fromEuc b))‖ ^ 2
      = ‖toEuc (fromEuc a - fromEuc b)‖ ^ 2 := by
    rw [toEuc_norm_sq, toEuc_norm_sq, rope_pair_inner]
  have h2 : toEuc (fromEuc a - fromEuc b) = a - b := by
    rw [toEuc_sub, toEuc_fromEuc, toEuc_fromEuc]
  rw [hsub, ← h2]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

/-!
## Isometry composition wiring
-/

/-- Pre-composition with the RoPE rotation keeps a Lipschitz
constant unchanged: a `μ`-Lipschitz map applied to rope-rotated
inputs stays `μ`-Lipschitz. -/
theorem rope_block_transfer {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X]
    {f : EuclideanSpace ℝ (Fin d ⊕ Fin d) → X} {μ : NNReal}
    (hf : LipschitzWith μ f) (θ : Fin d → ℝ) (m : ℕ) :
    LipschitzWith μ (fun x => f (rotEuc θ m x)) := by
  have h3 := hf.comp ((rope_isometry θ m).lipschitzWith)
  rw [mul_one] at h3
  exact h3

/-- Post-composition with the RoPE rotation keeps a Lipschitz
constant unchanged: rope-rotating the output of a `μ`-Lipschitz
map stays `μ`-Lipschitz. -/
theorem rope_block_post_transfer {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X]
    {f : X → EuclideanSpace ℝ (Fin d ⊕ Fin d)} {μ : NNReal}
    (hf : LipschitzWith μ f) (θ : Fin d → ℝ) (m : ℕ) :
    LipschitzWith μ (fun x => rotEuc θ m (f x)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  calc dist (rotEuc θ m (f x)) (rotEuc θ m (f y))
      = dist (f x) (f y) := (rope_isometry θ m).dist_eq _ _
    _ ≤ μ * dist x y := hf.dist_le_mul x y

/-!
## Attention wiring
-/

/-- A RoPE-wrapped pre-norm attention block (rotation applied to
the block input) satisfies the SAME leak bound at the
unchanged composed damping `μn·μatt`. -/
theorem attention_block_rope_transfer
    {n : EuclideanSpace ℝ (Fin d ⊕ Fin d) →
      EuclideanSpace ℝ (Fin d ⊕ Fin d)} {p : ι → ℝ}
    {v : ι → EuclideanSpace ℝ (Fin d ⊕ Fin d) →
      EuclideanSpace ℝ (Fin d ⊕ Fin d)}
    {loss : EuclideanSpace ℝ (Fin d ⊕ Fin d) → ℝ}
    {μn μatt Lc : NNReal} {θ : Fin d → ℝ} {m : ℕ}
    (hn : LipschitzWith μn n)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hv : ∀ i, LipschitzWith μatt (v i))
    (hloss : LipschitzWith Lc loss)
    (x dx : EuclideanSpace ℝ (Fin d ⊕ Fin d)) :
    loss (resStep (fun y => attnBranch p v (n (rotEuc θ m y))) (x + dx))
      ≤ loss (resStep (fun y => attnBranch p v (n (rotEuc θ m y))) x + dx)
        + Lc * (μn * μatt) * ‖dx‖ := by
  have hcomp : LipschitzWith (μn * μatt)
      (fun y => attnBranch p v (n (rotEuc θ m y))) := by
    have h1 := attn_norm_branch_lipschitz hn hp hp1 hv
    have h2 := (rope_isometry θ m).lipschitzWith
    have h3 := h1.comp h2
    rw [mul_one] at h3
    exact h3
  exact residual_transfer_le hcomp hloss x dx

/-!
## Stack of rope-wrapped attention blocks
-/

/-- Wrapping every branch of a block list with the same map does
not change the multiplicative stack gain. -/
theorem stackGain_wrap {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (l : List ((X → X) × NNReal)) (R : X → X) :
    stackGain (l.map fun p => (fun x => p.1 (R x), p.2)) = stackGain l := by
  induction l with
  | nil => rfl
  | cons p tl ih =>
    simp only [stackGain, List.map_cons, List.map_map, List.prod_cons] at ih ⊢
    rw [← ih]

/-- The rope-wrapped block list: every attention branch
pre-composed with the RoPE rotation, dampings UNCHANGED. -/
noncomputable def attnRopeBlockList (bs : List (AttnBlock
    (EuclideanSpace ℝ (Fin d ⊕ Fin d)) ι)) (θ : Fin d → ℝ) (m : ℕ) :
    List ((EuclideanSpace ℝ (Fin d ⊕ Fin d) →
      EuclideanSpace ℝ (Fin d ⊕ Fin d)) × NNReal) :=
  (attnBlockList bs).map fun c => (fun x => c.1 (rotEuc θ m x), c.2)

/-- The rope-wrapped stack: the residual stack over the
wrapped list. -/
noncomputable def attnRopeStack (bs : List (AttnBlock
    (EuclideanSpace ℝ (Fin d ⊕ Fin d)) ι)) (θ : Fin d → ℝ) (m : ℕ) :
    EuclideanSpace ℝ (Fin d ⊕ Fin d) →
      EuclideanSpace ℝ (Fin d ⊕ Fin d) :=
  resStack (attnRopeBlockList bs θ m)

/-- The gain of the rope-wrapped stack: UNCHANGED
(`stackGain` ignores the branch maps). -/
noncomputable def attnRopeGain (bs : List (AttnBlock
    (EuclideanSpace ℝ (Fin d ⊕ Fin d)) ι)) (θ : Fin d → ℝ) (m : ℕ) :
    NNReal :=
  stackGain (attnRopeBlockList bs θ m)

/-- The rope-wrapped gain equals the plain attention gain: RoPE
wrapping leaves every damping and hence the leak factor unchanged. -/
theorem attnRopeGain_eq (bs : List (AttnBlock
    (EuclideanSpace ℝ (Fin d ⊕ Fin d)) ι)) (θ : Fin d → ℝ) (m : ℕ) :
    attnRopeGain bs θ m = attnGain bs := by
  unfold attnRopeGain attnGain attnRopeBlockList attnBlockList
  exact stackGain_wrap _ _

/-- Every rope-wrapped block satisfies the block hypothesis at
the UNCHANGED composed damping. -/
theorem attnRopeBlockList_lipschitz (bs : List (AttnBlock
    (EuclideanSpace ℝ (Fin d ⊕ Fin d)) ι)) (θ : Fin d → ℝ) (m : ℕ)
    (hn : ∀ b ∈ bs, LipschitzWith b.μn b.n)
    (hp : ∀ b ∈ bs, ∀ i, 0 ≤ b.p i)
    (hp1 : ∀ b ∈ bs, ∑ i, b.p i = 1)
    (hv : ∀ b ∈ bs, ∀ i, LipschitzWith b.μatt (b.v i)) :
    ∀ c ∈ attnRopeBlockList bs θ m, LipschitzWith c.2 c.1 := by
  intro c hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
  have h0 := attnBlockList_lipschitz bs hn hp hp1 hv c₀ hc₀
  have h3 := h0.comp ((rope_isometry θ m).lipschitzWith)
  rw [mul_one] at h3
  exact h3

/-- Certified head descent transfers through a stack of
rope-wrapped attention blocks with the UNCHANGED leak factor
`Lc·(∏ (1 + μnᵢ·μattᵢ) − 1)·‖dx‖` — the stack theorem applied
verbatim. -/
theorem attention_rope_stack_transfer_descent (bs : List (AttnBlock
    (EuclideanSpace ℝ (Fin d ⊕ Fin d)) ι)) (θ : Fin d → ℝ) (m : ℕ)
    {loss : EuclideanSpace ℝ (Fin d ⊕ Fin d) → ℝ} {Lc : NNReal}
    {δ : ℝ}
    (hn : ∀ b ∈ bs, LipschitzWith b.μn b.n)
    (hp : ∀ b ∈ bs, ∀ i, 0 ≤ b.p i)
    (hp1 : ∀ b ∈ bs, ∑ i, b.p i = 1)
    (hv : ∀ b ∈ bs, ∀ i, LipschitzWith b.μatt (b.v i))
    (hloss : LipschitzWith Lc loss)
    (x dx : EuclideanSpace ℝ (Fin d ⊕ Fin d))
    (hdrop : loss (attnRopeStack bs θ m x + dx)
      ≤ loss (attnRopeStack bs θ m x) - δ) :
    loss (attnRopeStack bs θ m (x + dx))
      ≤ loss (attnRopeStack bs θ m x) - δ
        + Lc * ((attnRopeGain bs θ m : ℝ) - 1) * ‖dx‖ := by
  have hG : attnRopeStack bs θ m = resStack (attnRopeBlockList bs θ m) :=
    rfl
  have hgain : (attnRopeGain bs θ m : ℝ)
      = (stackGain (attnRopeBlockList bs θ m) : ℝ) := rfl
  rw [hG, hgain]
  exact resStack_transfer_descent _
    (attnRopeBlockList_lipschitz bs θ m hn hp hp1 hv) hloss x dx hdrop

/-- Strict composed decrease through the rope-wrapped stack: the
certified drop `δ` beats the UNCHANGED leak slack. -/
theorem attention_rope_stack_transfer_descent_strict (bs : List (AttnBlock
    (EuclideanSpace ℝ (Fin d ⊕ Fin d)) ι)) (θ : Fin d → ℝ) (m : ℕ)
    {loss : EuclideanSpace ℝ (Fin d ⊕ Fin d) → ℝ} {Lc : NNReal}
    {δ : ℝ}
    (hn : ∀ b ∈ bs, LipschitzWith b.μn b.n)
    (hp : ∀ b ∈ bs, ∀ i, 0 ≤ b.p i)
    (hp1 : ∀ b ∈ bs, ∑ i, b.p i = 1)
    (hv : ∀ b ∈ bs, ∀ i, LipschitzWith b.μatt (b.v i))
    (hloss : LipschitzWith Lc loss)
    (x dx : EuclideanSpace ℝ (Fin d ⊕ Fin d))
    (hdrop : loss (attnRopeStack bs θ m x + dx)
      ≤ loss (attnRopeStack bs θ m x) - δ)
    (hstrict : (Lc : ℝ) * ((attnRopeGain bs θ m : ℝ) - 1) * ‖dx‖ < δ) :
    loss (attnRopeStack bs θ m (x + dx))
      < loss (attnRopeStack bs θ m x) := by
  have h := attention_rope_stack_transfer_descent bs θ m hn hp hp1 hv
    hloss x dx hdrop
  linarith

/-!
## Scalar nonvacuity anchors
-/

/-- Anchor: the concrete 4-dimensional rotation by π/3 (d = 2,
θ ≡ π/3, m = 1) preserves the norm of the specific vector
`![(3, 4), (0, 0)]` (‖·‖ = 5). -/
example : ‖rotEuc (fun _ : Fin 2 => Real.pi / 3) 1
    (toEuc (![(3, 4), (0, 0)] : Fin 2 → ℝ × ℝ))‖
    = ‖toEuc (![(3, 4), (0, 0)] : Fin 2 → ℝ × ℝ)‖ := by
  have h0 : rotEuc (fun _ : Fin 2 => Real.pi / 3) 1
      (toEuc (![(3, 4), (0, 0)] : Fin 2 → ℝ × ℝ))
      = toEuc (rotVec (fun _ : Fin 2 => Real.pi / 3) 1
          (![(3, 4), (0, 0)] : Fin 2 → ℝ × ℝ)) := by
    unfold rotEuc
    rw [fromEuc_toEuc]
  have h : ‖toEuc (rotVec (fun _ : Fin 2 => Real.pi / 3) 1
      (![(3, 4), (0, 0)] : Fin 2 → ℝ × ℝ))‖ ^ 2
      = ‖toEuc (![(3, 4), (0, 0)] : Fin 2 → ℝ × ℝ)‖ ^ 2 := by
    rw [toEuc_norm_sq, toEuc_norm_sq, rope_pair_inner]
  rw [h0]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Anchor: the transported norm of the same vector is exactly 5
(the 3-4-5 triangle), so the rotated norm is 5 as well. -/
example : ‖toEuc (![(3, 4), (0, 0)] : Fin 2 → ℝ × ℝ)‖ = 5 := by
  have h : ‖toEuc (![(3, 4), (0, 0)] : Fin 2 → ℝ × ℝ)‖ ^ 2 = 25 := by
    rw [toEuc_norm_sq]
    unfold pairInner
    norm_num [Fin.sum_univ_two]
  exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
    (h.trans (by norm_num : (25 : ℝ) = (5 : ℝ) ^ 2))

end Hagi.Model.RoPETransfer
