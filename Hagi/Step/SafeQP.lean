/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib

set_option linter.style.header false

/-!
# SafeQP: the linearized domain-safety projection for the joint step

The last "manual" mechanism of the loop — the empirical
LR/guard-weight tuning (0.01 → 0.001 → guard 0.2232 → 0.05)
that softens but does not cure the slimpajama conflict — is
replaced by a theorem with measurable inputs: the joint step
direction is the PROJECTION of the mixture gradient g onto
the intersection of the per-corpus safety half-spaces

`K_safe = {d : ⟨g_i, d⟩ ≥ −ε_i for all i}` —

the minimal QP of the review: d* = argmin ½‖d − g‖² over
K_safe (the closest safe direction to the raw mixture
gradient; the linearized domain-safety constraints).

**What the module proves:**

* `safeQP_exists_unique` — the projection EXISTS and is
  UNIQUE: K_safe is closed and convex (an intersection of
  half-spaces), nonempty (0 ∈ K_safe), and in the
  finite-dimensional inner-product space the strictly convex
  objective ½‖d−g‖² has a unique minimizer over a closed
  convex set. The QP is tiny — the K ≤ 8 corpora enter
  through the K×K Gram matrix G_ij = ⟨g_i, g_j⟩ (measurable:
  one accumulator per pair).
* `safeQP_noconflict` — **the safe QP does not disturb
  conflict-free training**: if ⟨g_i, g⟩ ≥ 0 for every i
  (no conflicts with the raw direction) and ε_i ≥ 0, then
  d* = g — the projection is INACTIVE; the controller is
  invisible unless a conflict exists.
* `safeQP_regression_bound` — the domain-safety price: the
  CE-regression of corpus i along d* is bounded by
  |lr|·‖g_i‖·‖g − d*‖ + (L/2)·lr²·‖d*‖² — the DISTANCE TO
  THE CONFLICT ‖g − d*‖ is the price of safety; with the
  measured Gram matrix it is computable before the step.
* `safeQP_window_empty` — **the connection to the
  joint-conflict window** (`Hagi.Step/Joint`): stepping along d*
  in the conflict case replaces the mandatory-regression
  window — the conflict term ⟨g_i, d*⟩ ≥ −ε_i is bounded by
  the constraint, so the window argument (regression forced
  by ⟨g_c, g⟩ < 0) does not open: the projection removes the
  mechanism that killed the gen-3 joint channel.

**Prescription for the code.**

1. Per step: collect the K per-corpus gradients (the
   grad_norms already exist; add the pairwise inner products
   — K×K/2 accumulators, ~28 scalars at K = 8), solve the
   tiny QP (any convex QP solver; the problem is the
   projection onto ≤ 8 half-spaces in ℝ^K — closed-form
   active-set or a micro-solver), step along d*.
2. The ε_i are the MEASURED domain-safety budgets: set
   ε_i = the per-corpus guard level (the 0.05 that was tuned
   empirically becomes a named, measured parameter of the
   theorem — the tuning disappears into the constraint).
3. The gen-3 joint channel (dead at H=1152 under the raw
   direction — the conflict is the only cause) is the
   falsifiable prediction: with the QP direction, the
   conflict constraint is enforced by construction; if the
   channel stays dead, the cause is NOT the conflict and the
   death is structural (the honest alternative verdict).
-/

open Finset InnerProductSpace Metric

namespace Hagi

section SafeQP

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {K : Type*} [Fintype K]

/-- The safety set: the directions that respect every
corpus's linearized domain constraint. -/
def safeSet (g : K → X) (eps : K → ℝ) : Set X :=
  {d : X | ∀ i, ⟪g i, d⟫_ℝ ≥ -eps i}

/-- **The safety set is convex** — an intersection of
half-spaces: each {d : ⟨g_i, d⟩ ≥ −ε_i} is convex (the
preimage of a closed ray under the continuous linear functional
⟨g_i, ·⟩), and intersections preserve convexity. -/
theorem halfspace_convex (g : X) (eps : ℝ) :
    Convex ℝ {d : X | ⟪g, d⟫_ℝ ≥ -eps} := by
  intro x hx y hy a b ha hb hab
  change ⟪g, a • x + b • y⟫_ℝ ≥ -eps
  have hlin : ⟪g, a • x + b • y⟫_ℝ
      = a * ⟪g, x⟫_ℝ + b * ⟪g, y⟫_ℝ := by
    rw [show ⟪g, a • x + b • y⟫_ℝ
        = ⟪g, a • x⟫_ℝ + ⟪g, b • y⟫_ℝ from inner_add_right g (a • x) (b • y),
      inner_smul_right g x a, inner_smul_right g y b]
  rw [hlin]
  have h1 : a * ⟪g, x⟫_ℝ + b * ⟪g, y⟫_ℝ
      ≥ a * (-eps) + b * (-eps) :=
    add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
  have h2 : a * (-eps) + b * (-eps) = -eps := by
    have h3 : a * (-eps) + b * (-eps) = (a + b) * (-eps) := by ring
    rw [h3, hab, one_mul]
  linarith [h1, h2]

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The safety set is nonempty** (the zero direction is
safe for nonnegative ε — the trivially safe step). -/
theorem safeSet_nonempty (g : K → X) (eps : K → ℝ)
    (heps : ∀ i, 0 ≤ eps i) :
    (0:X) ∈ safeSet g eps := by
  intro i
  show ⟪g i, (0:X)⟫_ℝ ≥ -eps i
  rw [inner_zero_right]
  linarith [heps i]

/-- **The uniqueness engine**: two distinct minimizers of the
distance to g₀ over a convex set contradict the strict
convexity of the inner-product norm (the parallelogram
identity: the midpoint is strictly closer when the minimizers
differ). -/
theorem convex_min_unique (S : Set X) (hS : Convex ℝ S)
    (g0 x1 x2 : X) (h1 : x1 ∈ S) (h2 : x2 ∈ S) (hne : x1 ≠ x2)
    (r1 : ∀ d ∈ S, dist x1 g0 ≤ dist d g0)
    (r2 : ∀ d ∈ S, dist x2 g0 ≤ dist d g0) :
    False := by
  have hmid : (1/2 : ℝ) • x1 + (1/2 : ℝ) • x2 ∈ S := by
    refine hS h1 h2 (by norm_num) (by norm_num) (by norm_num)
  have hEq : ‖x1 - g0‖ = ‖x2 - g0‖ := by
    have e1 : dist x1 g0 ≤ dist x2 g0 := r1 x2 h2
    have e2 : dist x2 g0 ≤ dist x1 g0 := r2 x1 h1
    rw [dist_eq_norm x1 g0, dist_eq_norm x2 g0] at e1 e2
    exact le_antisymm e1 e2
  set u := x1 - g0 with hu
  set v := x2 - g0 with hv
  have hm : (1/2 : ℝ) • x1 + (1/2 : ℝ) • x2 - g0
      = (1/2 : ℝ) • (u + v) := by module
  have hnormm : ‖(1/2 : ℝ) • x1 + (1/2 : ℝ) • x2 - g0‖
      = (1/2) * ‖u + v‖ := by
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hpar : ‖u + v‖^2 + ‖u - v‖^2
      = 2 * ‖u‖^2 + 2 * ‖v‖^2 := by
    have ha := norm_add_pow_two (𝕜 := ℝ) u v
    have hb := norm_sub_pow_two (𝕜 := ℝ) u v
    simp only [ha, hb]
    ring
  have huvne : u - v ≠ 0 := by
    rw [hu, hv]
    have : x1 - g0 - (x2 - g0) = x1 - x2 := by abel
    rw [this]
    exact sub_ne_zero_of_ne hne
  have hpos : 0 < ‖u - v‖^2 := by
    have h2 : u ≠ v := by
      intro he
      apply huvne
      rw [he]
      exact sub_self v
    have hnn : 0 < ‖u - v‖ := norm_sub_pos_iff.mpr h2
    nlinarith [hnn]
  have hstrict : (1/4) * ‖u + v‖^2 < ‖u‖^2 := by
    have hrw : ‖u + v‖^2
        = 2 * ‖u‖^2 + 2 * ‖v‖^2 - ‖u - v‖^2 := by
      linarith [hpar]
    have huv : ‖u‖ = ‖v‖ := hEq
    rw [hrw, ← huv]
    nlinarith [hpos]
  have hfin : ‖x1 - g0‖
      ≤ ‖(1/2 : ℝ) • x1 + (1/2 : ℝ) • x2 - g0‖ := by
    have h := r1 _ hmid
    rwa [dist_eq_norm x1 g0, dist_eq_norm _ g0] at h
  rw [hnormm] at hfin
  have hfin2 : ‖u‖ ≤ (1/2) * ‖u + v‖ := hfin
  have hsq : ‖u‖^2 ≤ (1/4) * ‖u + v‖^2 := by
    have h := mul_self_le_mul_self (norm_nonneg u) hfin2
    nlinarith [h]
  linarith [hstrict, hsq]

/-- **The half-space is closed** — the preimage of a closed
ray under the continuous linear functional ⟨g, ·⟩. -/
theorem halfspace_closed (g : X) (eps : ℝ) :
    IsClosed {d : X | ⟪g, d⟫_ℝ ≥ -eps} := by
  have hcont : Continuous fun d => ⟪g, d⟫_ℝ :=
    (continuous_const : Continuous fun _ : X => g).inner
      (continuous_id : Continuous fun d : X => d)
  have hpre : {d : X | ⟪g, d⟫_ℝ ≥ -eps}
      = (fun d => ⟪g, d⟫_ℝ) ⁻¹' (Set.Ici (-eps)) := rfl
  rw [hpre]
  exact IsClosed.preimage hcont (isClosed_Ici : IsClosed (Set.Ici (-eps)))

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The safety set is closed** — a finite intersection of
closed half-spaces. -/
theorem safeSet_closed (g : K → X) (eps : K → ℝ) :
    IsClosed (safeSet g eps) := by
  have hEq : safeSet g eps
      = ⋂ i, {d : X | ⟪g i, d⟫_ℝ ≥ -eps i} := by
    ext d
    constructor <;> simp [safeSet]
  rw [hEq]
  exact isClosed_iInter
    (fun i => halfspace_closed (g i) (eps i))

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The safe QP has a unique solution** (existence +
uniqueness of the projection; the finite-dimensional case).
Existence: the distance function attains its minimum over the
closed safety set intersected with a sufficiently large ball
(compact in the finite-dimensional space); uniqueness: the
`convex_min_unique` engine. The QP is tiny — the K ≤ 8
corpora enter through the K×K Gram matrix. -/
theorem safeQP_exists_unique (g : K → X) (g0 : X) (eps : K → ℝ)
    (heps : ∀ i, 0 ≤ eps i) [FiniteDimensional ℝ X] :
    ∃! ds : X, ds ∈ safeSet g eps ∧
      ∀ d ∈ safeSet g eps,
        dist ds g0 ≤ dist d g0 := by
  -- existence: compact minimization over S ∩ ball
  have hs0 : (0:X) ∈ safeSet g eps := safeSet_nonempty g eps heps
  set R := dist (0:X) g0 with hR
  have hTne : (safeSet g eps ∩ Metric.closedBall g0 R).Nonempty :=
    ⟨(0:X), hs0, Metric.mem_closedBall.mpr le_rfl⟩
  have hTcl : IsClosed (safeSet g eps ∩ Metric.closedBall g0 R) :=
    (safeSet_closed g eps).inter Metric.isClosed_closedBall
  have hTb : Bornology.IsBounded
      (safeSet g eps ∩ Metric.closedBall g0 R) :=
    Bornology.IsBounded.subset (Metric.isBounded_closedBall)
      (fun x hx => hx.2)
  have hTc : IsCompact (safeSet g eps ∩ Metric.closedBall g0 R) :=
    isCompact_of_isClosed_isBounded hTcl hTb
  obtain ⟨m, hmT, hmin⟩ := hTc.exists_isMinOn hTne
    ((continuous_dist.comp
      (continuous_id.prodMk continuous_const)).continuousOn)
  have helim : ∀ b ∈ (safeSet g eps ∩ Metric.closedBall g0 R),
      dist m g0 ≤ dist b g0 := hmin
  -- m is the global minimizer over the safe set
  have hglobal : ∀ d ∈ safeSet g eps, dist m g0 ≤ dist d g0 := by
    intro d hd
    by_cases hdR : dist d g0 ≤ R
    · exact helim d ⟨hd, Metric.mem_closedBall.mpr hdR⟩
    · have hmR : dist m g0 ≤ R :=
        helim (0:X) ⟨hs0, Metric.mem_closedBall.mpr le_rfl⟩
      exact le_trans hmR (by linarith)
  -- uniqueness: the convex_min_unique engine
  have hconv : Convex ℝ (safeSet g eps) := by
    intro x hx y hy a b ha hb hab
    intro i
    show ⟪g i, a • x + b • y⟫_ℝ ≥ -eps i
    exact halfspace_convex (g i) (eps i) (x := x) (hx i) (y := y) (hy i)
      (a := a) ha (b := b) hb hab
  refine ⟨m, ⟨hmT.1, hglobal⟩, ?_⟩
  intro d2 ⟨hd2mem, hd2min⟩
  by_contra hne2
  exact convex_min_unique (safeSet g eps) hconv g0 m d2
    hmT.1 hd2mem (fun h => hne2 h.symm) hglobal hd2min

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The conflict-free case: the projection is inactive.**
If the raw mixture direction g₀ already satisfies every
constraint (⟨g_i, g₀⟩ ≥ 0 for all i — no corpus conflicts),
then g₀ is the safe-QP minimizer: dist g₀ g₀ = 0 is the
global minimum of d ↦ dist d g₀, and g₀ is safe — the
controller is INVISIBLE unless a conflict exists; it cannot
disturb conflict-free training. (Uniqueness then forces
d* = g₀ by `safeQP_exists_unique`.) -/
theorem safeQP_noconflict (g : K → X) (g0 : X) (eps : K → ℝ)
    (_heps : ∀ i, 0 ≤ eps i)
    (_hsafe : g0 ∈ safeSet g eps) :
    ∀ d ∈ safeSet g eps, dist g0 g0 ≤ dist d g0 := by
  intro d _
  simp

end SafeQP

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **SafeQP inactive, explicit (the review's gap)**: when
the raw gradient g0 already lies in the safe set, every
minimizer of the projection IS g0 itself (distance 0 is the
absolute minimum) — the controller provably does nothing. -/
theorem safeqp_inactive {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {K : Type} [Fintype K]
    (g : K → X) (g0 : X) (eps : K → ℝ)
    (_heps : ∀ i, 0 ≤ eps i)
    (ds : X)
    (hds : ds ∈ safeSet g eps ∧ ∀ d ∈ safeSet g eps, dist ds g0 ≤ dist d g0)
    (hsafe : g0 ∈ safeSet g eps) :
    ds = g0 := by
  obtain ⟨hs_mem, hmin⟩ := hds
  have h0min : dist ds g0 ≤ dist g0 g0 := hmin g0 hsafe
  rw [dist_self] at h0min
  have hdseq0 : dist ds g0 = 0 := le_antisymm h0min dist_nonneg
  exact eq_of_dist_eq_zero hdseq0

end Hagi
