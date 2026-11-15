/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Model.Residual

set_option linter.style.header false

/-!
# Residual transfer of certified descent (E4 first composition)

The first composition theorem of the nonlinear backbone certificate
(E4 seed, `.omc/analysis/period-c292-c297-analysis.md` rank 2): a
certified head descent transfers through residual blocks with an
explicit leak bound — the cascade-leak pattern of
`Hagi.Architecture.CascadeLeak` (C250) applied to the UPDATE path
instead of the adapter path.

Carrier is the abstract residual stream of `Hagi.Model.Residual`
(`resStep f x = x + f x`, source №22). No differentiability is
assumed anywhere: the residual-branch response `f (x + dx) − f x`
is bounded by a `LipschitzWith` premise-form, and the certified
head drop enters as a premise (`hdrop`) of the C291 shape
(`ceOneHot_next_le_param` instantiates it).

One block (`resStep_lipschitz`, `residual_transfer_le`,
`residual_transfer_descent`, `residual_transfer_descent_strict`):
if `f` is `μ`-Lipschitz and the loss is `Lc`-Lipschitz, then a head
descent `δ` realized by a parameter step `dx` through the identity
path survives the block:

`loss (resStep f (x + dx)) ≤ loss (resStep f x) − δ + Lc·μ·‖dx‖`,

with strict decrease whenever `Lc·μ·‖dx‖ < δ`. The leak term is
exactly the residual-branch response (`μ = 0` ⇒ zero leak).

Stack (`resStack`, `stackGain`, `stackGain_ge_one`,
`resStack_bounds`, `resStack_lipschitz`, `resStack_leak_le`,
`resStack_transfer_descent`, `resStack_transfer_descent_strict`):
a stack is a list of blocks `(f, μ)` with `f` `μ`-Lipschitz; for
`B` blocks the identity-passthrough leak composes MULTIPLICATIVELY
in the `cascadeGain` pattern (`Hagi.Core.ErrorProp`):

`‖G (x + dx) − G x − dx‖ ≤ (∏ (1 + μᵢ) − 1)·‖dx‖`,

so a head descent `δ` at the stack output transfers as
`loss (G (x + dx)) ≤ loss (G x) − δ + Lc·(∏ (1 + μᵢ) − 1)·‖dx‖`.
This is the induction step for stacking blocks: each block
multiplies the leak factor by `(1 + μᵢ)`.

Honest scope: the full FastArch3 forward/backward (attention
Jacobians, RoPE exactness, GDN RAM rung, RMSNorm constants) is NOT
claimed here; those internals are the documented follow-up ladder
(`.omc/tech-debt.md` E4 entry).
-/

namespace Hagi.Model.BackboneTransfer

open Hagi.Model.Residual

variable {X : Type*} [NormedAddCommGroup X]

/-!
## One residual block
-/

/-- The residual step `x ↦ x + f x` is `(1 + μ)`-Lipschitz whenever
`f` is `μ`-Lipschitz: identity path contributes `1`, residual branch
`μ` (additive Lipschitz constants). -/
theorem resStep_lipschitz {f : X → X} {μ : NNReal} (hf : LipschitzWith μ f) :
    LipschitzWith (1 + μ) (resStep f) :=
  LipschitzWith.add (LipschitzWith.id : LipschitzWith 1 (fun x : X => x)) hf

/-- Head-transfer through ONE residual block, leak form: the loss at
the realized output `resStep f (x + dx)` (step passed through the
identity path, plus the residual-branch response) exceeds the loss
at the intended head output `resStep f x + dx` by at most the leak
`Lc·μ·‖dx‖` — the cascade-leak entering-vector pattern applied to
the update path. `μ = 0` recovers the identity stack (zero leak). -/
theorem residual_transfer_le {f : X → X} {loss : X → ℝ}
    {μ Lc : NNReal} (hf : LipschitzWith μ f) (hloss : LipschitzWith Lc loss)
    (x dx : X) :
    loss (resStep f (x + dx))
      ≤ loss (resStep f x + dx) + Lc * μ * ‖dx‖ := by
  have hab : resStep f (x + dx) - (resStep f x + dx)
      = f (x + dx) - f x := by
    unfold resStep
    abel
  have h1 := hloss.norm_sub_le (resStep f (x + dx)) (resStep f x + dx)
  rw [hab] at h1
  have h2 := hf.norm_sub_le (x + dx) x
  rw [show (x + dx) - x = dx from by abel] at h2
  have h3 : loss (resStep f (x + dx)) - loss (resStep f x + dx)
      ≤ ‖loss (resStep f (x + dx)) - loss (resStep f x + dx)‖ :=
    le_abs_self _
  have key : ‖loss (resStep f (x + dx)) - loss (resStep f x + dx)‖
      ≤ (Lc * μ : NNReal) * ‖dx‖ := by
    have hcoe : ((Lc * μ : NNReal) : ℝ) = Lc * μ := NNReal.coe_mul Lc μ
    rw [hcoe]
    calc ‖loss (resStep f (x + dx)) - loss (resStep f x + dx)‖
        ≤ Lc * ‖f (x + dx) - f x‖ := h1
      _ ≤ Lc * (μ * ‖dx‖) :=
          mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg Lc)
      _ = Lc * μ * ‖dx‖ := by ring
  rw [NNReal.coe_mul] at key
  linarith

/-- Certified head descent transfers through ONE residual block: a
drop `δ` certified at the block output for the intended step (C291
premise-form) survives the block up to the leak slack `Lc·μ·‖dx‖`. -/
theorem residual_transfer_descent {f : X → X} {loss : X → ℝ}
    {μ Lc : NNReal} {δ : ℝ} (hf : LipschitzWith μ f)
    (hloss : LipschitzWith Lc loss) (x dx : X)
    (hdrop : loss (resStep f x + dx) ≤ loss (resStep f x) - δ) :
    loss (resStep f (x + dx))
      ≤ loss (resStep f x) - δ + Lc * μ * ‖dx‖ := by
  have h := residual_transfer_le hf hloss x dx
  linarith

/-- Strict composed decrease: if the certified head drop `δ` exceeds
the leak slack `Lc·μ·‖dx‖`, the composed objective (loss at the
realized block output) strictly decreases. -/
theorem residual_transfer_descent_strict {f : X → X} {loss : X → ℝ}
    {μ Lc : NNReal} {δ : ℝ} (hf : LipschitzWith μ f)
    (hloss : LipschitzWith Lc loss) (x dx : X)
    (hdrop : loss (resStep f x + dx) ≤ loss (resStep f x) - δ)
    (hstrict : (Lc : ℝ) * μ * ‖dx‖ < δ) :
    loss (resStep f (x + dx)) < loss (resStep f x) := by
  have h := residual_transfer_descent hf hloss x dx hdrop
  linarith

/-!
## Stack of residual blocks
-/

/-- A stack of residual blocks: list of `(f, μ)` pairs folded through
`resStep` (head block applied first, `foldl`). -/
def resStack (blocks : List ((X → X) × NNReal)) (x : X) : X :=
  blocks.foldl (fun acc b => resStep b.1 acc) x

/-- Multiplicative stack gain: `∏ (1 + μᵢ)` over the block dampings,
the `cascadeGain` pattern (`Hagi.Core.ErrorProp`) specialized to
residual blocks. -/
def stackGain (blocks : List ((X → X) × NNReal)) : NNReal :=
  (blocks.map (fun b => 1 + b.2)).prod

omit [NormedAddCommGroup X] in
/-- Every factor of the stack gain is at least `1`, hence so is the
gain itself (needed for nonnegative leak coefficients). -/
theorem stackGain_ge_one (blocks : List ((X → X) × NNReal)) :
    1 ≤ stackGain blocks := by
  induction blocks with
  | nil => unfold stackGain; simp
  | cons b bs ih =>
      unfold stackGain at *
      rw [List.map_cons, List.prod_cons]
      exact one_le_mul (by linarith) ih

/-- Triangle helper: `‖a‖ ≤ ‖a − b‖ + ‖b‖` (refold `a = (a − b) + b`). -/
private theorem norm_le_sub_add (a b : X) : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
  have he : a = (a - b) + b := by abel
  conv_lhs => rw [he]
  exact norm_add_le (a - b) b

/-- Combined stack induction: for a well-damped block list, the stack
is `stackGain`-Lipschitz in the step AND its identity-passthrough
leak is `(stackGain − 1)` per unit step (both bounds at every base
point — the mutual induction powering `resStack_lipschitz` and
`resStack_leak_le`). -/
theorem resStack_bounds (blocks : List ((X → X) × NNReal))
    (h : ∀ b ∈ blocks, LipschitzWith b.2 b.1) (x dx : X) :
    ‖resStack blocks (x + dx) - resStack blocks x‖
      ≤ (stackGain blocks : ℝ) * ‖dx‖
    ∧ ‖resStack blocks (x + dx) - resStack blocks x - dx‖
      ≤ ((stackGain blocks : ℝ) - 1) * ‖dx‖ := by
  induction blocks generalizing x dx with
  | nil =>
      constructor <;>
        · unfold resStack stackGain
          simp
  | cons b bs ih =>
      obtain ⟨f, μ⟩ := b
      have hfμ : LipschitzWith μ f := h (f, μ) (List.mem_cons_self ..)
      have htail : ∀ c ∈ bs, LipschitzWith c.2 c.1 := fun c hc =>
        h c (List.mem_cons_of_mem _ hc)
      have hstep : ∀ y : X,
          resStack ((f, μ) :: bs) y = resStack bs (resStep f y) :=
        fun _ => rfl
      set d : X := resStep f (x + dx) - resStep f x with hddef
      have hdy : ‖d‖ ≤ ((1 : ℝ) + μ) * ‖dx‖ := by
        have h0 := (resStep_lipschitz hfμ).norm_sub_le (x + dx) x
        rw [show (x + dx) - x = dx from by abel] at h0
        simpa [hddef, dist_eq_norm] using h0
      have hdyleak : ‖d - dx‖ ≤ μ * ‖dx‖ := by
        have h2 := hfμ.norm_sub_le (x + dx) x
        rw [show (x + dx) - x = dx from by abel] at h2
        have hsplit : d - dx = f (x + dx) - f x := by
          unfold d
          unfold resStep
          abel
        rw [hsplit]
        exact h2
      have e1 : resStep f (x + dx) = resStep f x + d := by
        unfold d
        abel
      obtain ⟨hlip', hleak'⟩ :=
        ih htail (resStep f x) d
      rw [hstep, hstep, e1]
      have gcons : ((stackGain ((f, μ) :: bs) : ℝ))
          = ((1 : ℝ) + μ) * (stackGain bs : ℝ) := by
        have hc : ((stackGain ((f, μ) :: bs) : NNReal))
            = (1 + μ) * stackGain bs := by
          unfold stackGain
          rw [List.map_cons, List.prod_cons]
        rw [hc]
        push_cast
        ring
      rw [gcons]
      have hge1 : (1 : ℝ) ≤ (stackGain bs : ℝ) :=
        by exact_mod_cast stackGain_ge_one bs
      have hP0 : (0 : ℝ) ≤ (stackGain bs : ℝ) := by positivity
      set A : X := resStack bs (resStep f x + d) with hA
      set B : X := resStack bs (resStep f x) with hB
      constructor
      · calc ‖A - B‖
            ≤ ‖A - B - d‖ + ‖d‖ := norm_le_sub_add (A - B) d
          _ ≤ ((stackGain bs : ℝ) - 1) * ‖d‖ + ‖d‖ :=
              add_le_add_left hleak' _
          _ = (stackGain bs : ℝ) * ‖d‖ := by ring
          _ ≤ (stackGain bs : ℝ) * (((1 : ℝ) + μ) * ‖dx‖) :=
              mul_le_mul_of_nonneg_left hdy hP0
          _ = ((1 : ℝ) + μ) * (stackGain bs : ℝ) * ‖dx‖ := by ring
      · calc ‖A - B - dx‖
            ≤ ‖A - B - dx - (d - dx)‖ + ‖d - dx‖ :=
              norm_le_sub_add (A - B - dx) (d - dx)
          _ = ‖A - B - d‖ + ‖d - dx‖ := by abel_nf
          _ ≤ ((stackGain bs : ℝ) - 1) * ‖d‖ + μ * ‖dx‖ :=
              add_le_add hleak' hdyleak
          _ ≤ ((stackGain bs : ℝ) - 1) * (((1 : ℝ) + μ) * ‖dx‖)
              + μ * ‖dx‖ :=
              add_le_add
                (mul_le_mul_of_nonneg_left hdy (sub_nonneg.mpr hge1))
                (le_refl _)
          _ = (((1 : ℝ) + μ) * (stackGain bs : ℝ) - 1) * ‖dx‖ := by
              ring

/-- The stack is `stackGain`-Lipschitz in the step: the composite of
`(1 + μᵢ)`-Lipschitz residual steps (the `cascade_exp_bound`
multiplicative pattern). -/
theorem resStack_lipschitz (blocks : List ((X → X) × NNReal))
    (h : ∀ b ∈ blocks, LipschitzWith b.2 b.1) (x dx : X) :
    ‖resStack blocks (x + dx) - resStack blocks x‖
      ≤ (stackGain blocks : ℝ) * ‖dx‖ :=
  (resStack_bounds blocks h x dx).1

/-- Identity-passthrough leak of the stack: the realized output step
`G (x + dx) − G x` deviates from the intended identity-path step
`dx` by at most `(∏ (1 + μᵢ) − 1)·‖dx‖`. The leak composes
MULTIPLICATIVELY (one block: `μ·‖dx‖`; each new block multiplies the
factor by `(1 + μᵢ)`) — the cascade-leak composition of C250 on the
update path. -/
theorem resStack_leak_le (blocks : List ((X → X) × NNReal))
    (h : ∀ b ∈ blocks, LipschitzWith b.2 b.1) (x dx : X) :
    ‖resStack blocks (x + dx) - resStack blocks x - dx‖
      ≤ ((stackGain blocks : ℝ) - 1) * ‖dx‖ :=
  (resStack_bounds blocks h x dx).2

/-- Certified head descent transfers through the WHOLE stack: drop
`δ` at the stack output, leak slack `Lc·(∏ (1 + μᵢ) − 1)·‖dx‖`. -/
theorem resStack_transfer_descent (blocks : List ((X → X) × NNReal))
    {loss : X → ℝ} {Lc : NNReal} {δ : ℝ}
    (h : ∀ b ∈ blocks, LipschitzWith b.2 b.1)
    (hloss : LipschitzWith Lc loss) (x dx : X)
    (hdrop : loss (resStack blocks x + dx)
      ≤ loss (resStack blocks x) - δ) :
    loss (resStack blocks (x + dx))
      ≤ loss (resStack blocks x) - δ
        + Lc * ((stackGain blocks : ℝ) - 1) * ‖dx‖ := by
  have h1 := hloss.norm_sub_le (resStack blocks (x + dx))
    (resStack blocks x + dx)
  have h2 := resStack_leak_le blocks h x dx
  have heq : resStack blocks (x + dx) - (resStack blocks x + dx)
      = resStack blocks (x + dx) - resStack blocks x - dx := by abel
  rw [heq] at h1
  have h3 : loss (resStack blocks (x + dx))
      - loss (resStack blocks x + dx)
      ≤ ‖loss (resStack blocks (x + dx))
        - loss (resStack blocks x + dx)‖ :=
    le_abs_self _
  have key : ‖loss (resStack blocks (x + dx))
      - loss (resStack blocks x + dx)‖
      ≤ Lc * (((stackGain blocks : ℝ) - 1) * ‖dx‖) := by
    calc ‖loss (resStack blocks (x + dx))
        - loss (resStack blocks x + dx)‖
        ≤ Lc * ‖resStack blocks (x + dx)
            - resStack blocks x - dx‖ := h1
      _ ≤ Lc * (((stackGain blocks : ℝ) - 1) * ‖dx‖) :=
          mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg Lc)
  linarith

/-- Strict composed decrease through the stack: certified drop `δ`
beats the stack leak slack. -/
theorem resStack_transfer_descent_strict (blocks : List ((X → X) × NNReal))
    {loss : X → ℝ} {Lc : NNReal} {δ : ℝ}
    (h : ∀ b ∈ blocks, LipschitzWith b.2 b.1)
    (hloss : LipschitzWith Lc loss) (x dx : X)
    (hdrop : loss (resStack blocks x + dx)
      ≤ loss (resStack blocks x) - δ)
    (hstrict : (Lc : ℝ) * ((stackGain blocks : ℝ) - 1) * ‖dx‖ < δ) :
    loss (resStack blocks (x + dx)) < loss (resStack blocks x) := by
  have h := resStack_transfer_descent blocks h hloss x dx hdrop
  linarith

/-!
## Scalar nonvacuity anchors (μ = 1/10)
-/

/-- Anchor: one block with `μ = 1/10` has leak factor
`1 + μ − 1 = 1/10` per unit step. -/
example : ((1 : ℝ) + 1 / 10) - 1 = 1 / 10 := by norm_num

/-- Anchor: two blocks compose multiplicatively:
`(1 + μ)² − 1 = 21/100 ≥ 2μ = 1/5` (the Σ form is weaker). -/
example : (1 / 5 : ℝ) ≤ (1 + 1 / 10) * (1 + 1 / 10) - 1 := by norm_num

end Hagi.Model.BackboneTransfer
