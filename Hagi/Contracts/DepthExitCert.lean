/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Model.BackboneTransfer
import Hagi.Contracts.SparseInferenceCert
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Certified early-exit depth routing (mixture-of-depths)

The rank-1 track (mixture-of-depths):
per-token depth routing with a certified early-exit error bound —
what the mixture-of-depths idea buys once the backbone certificate
is on the stack (`Hagi.Model.BackboneTransfer`).

The exit model: `G` is the full residual stack `resStack`, and
`G_k` runs only the FIRST k blocks, then identity (the rest
skipped). The leak theorem `resStack_leak_le` bounds the
UPDATE-path deviation `‖G(x+dx) − Gx − dx‖` — it does NOT bound
the skip distance `‖G x − G_k x‖`, and this module does not
misapply it. The honest skip composition is the premise-form the
ranking anticipated: with every tail block's residual branch
globally bounded `‖res z‖ ≤ bᵢ` (a PREMISE, no claim any trained
net satisfies it), the exit error obeys the tail-leak sum
`Σᵢ bᵢ·∏_{j>i}(1+μⱼ)` (`exitLeak`, recursive, plus the explicit
`exitLeak_eq_sum`). The μ weights enter through `stackGain` of the
blocks strictly after each position — the multiplicative
pattern as an amplification weight, with NO Lipschitz premise
needed for the skip distance itself.

The certificate is two-sided per token (`early_exit_certificate`):
IF a (premise, arbitrary — no optimality claim) depth router fires
at `k = route x`, THEN the token's exit-head output deviates from
the full-stack head output by at most `Lh · exitLeak (drop k)`
(head Lipschitz composed) AND its executed work is the
prefix share of the exact work ledger `early_exit_work` (per-block
counts in the entry-read model, `denseMatVecWork` the cited
form). A depth router for WHO exits is the sleeping-router
pattern (namespace `Hagi.Learning.SleepingRouter` in
`Hagi.Learning.SoftRouterMix`); connected by citation
only, no integration claimed.

Honest scope: the exit RULE's optimality is NOT claimed; batch-level
load balancing is NOT claimed; the b-premises are global bounds
(strong); all numbers live in the numeric `Anchor` lemmas only.
-/

namespace Hagi.Contracts.DepthExitCert

open Hagi.Model.Residual Hagi.Model.BackboneTransfer

variable {X : Type*} [NormedAddCommGroup X]

/-- A depth-routed residual block: the residual branch `res`, its
damping `mu` (`μᵢ`), the global residual-magnitude bound
`bres` (`‖res z‖ ≤ bres` for every z), and the per-block work count
`work` (entry-read model). -/
structure DepthBlock (X : Type*) [NormedAddCommGroup X] where
  /-- The residual branch of the block. -/
  res : X → X
  /-- The block damping `μᵢ`. -/
  mu : NNReal
  /-- The global residual-magnitude premise bound `bᵢ`. -/
  bres : NNReal
  /-- The per-block work count `Wᵢ` (count model). -/
  work : ℕ

def toBlocks (blocks : List (DepthBlock X)) : List ((X → X) × NNReal) :=
  blocks.map fun d => (d.res, d.mu)

/-- The per-layer exit-leak weight: `bᵢ·∏_{j>i}(1+μⱼ)` (recursive
form; `exitLeak_eq_sum` is the explicit Σ form). -/
def exitLeak : List (DepthBlock X) → ℝ
  | [] => 0
  | d :: bs => d.bres * (stackGain (toBlocks bs) : ℝ) + exitLeak bs

/-- The gains of the blocks strictly AFTER each position: the
`∏_{j>i}(1+μⱼ)` weights of the exit-leak sum. -/
def afterGain : List (DepthBlock X) → List ℝ
  | [] => []
  | _d :: bs => (stackGain (toBlocks bs) : ℝ) :: afterGain bs

/-- The Σ form: `exitLeak = Σᵢ bᵢ·∏_{j>i}(1+μⱼ)` — each block's
residual-magnitude premise weighted by the stack gain of the
blocks strictly after it. -/
theorem exitLeak_eq_sum (blocks : List (DepthBlock X)) :
    exitLeak blocks
      = ((blocks.zip (afterGain blocks)).map
          fun p => (p.1.bres : ℝ) * p.2).sum := by
  induction blocks with
  | nil => simp [exitLeak, afterGain]
  | cons d bs ih =>
      simp only [exitLeak, afterGain, List.zip_cons_cons, List.map_cons,
        List.sum_cons]
      rw [ih]

/-- foldl append identity: a stack splits into prefix ++ tail. -/
theorem resStack_append (l1 l2 : List ((X → X) × NNReal)) (x : X) :
    resStack (l1 ++ l2) x = resStack l2 (resStack l1 x) := by
  simp [resStack, List.foldl_append]

/-- THE SKIP BOUND: the distance between running the tail stack and
skipping it (identity), at ANY input y, is at most `exitLeak tail` —
only the residual-magnitude premises enter (the μ weights come in
through `stackGain` of the later blocks; NO Lipschitz premise is
needed for the skip distance itself). -/
theorem resStack_skip_le (blocks : List (DepthBlock X))
    (hb : ∀ d ∈ blocks, ∀ z : X, ‖d.res z‖ ≤ (d.bres : ℝ)) (y : X) :
    ‖resStack (toBlocks blocks) y - y‖ ≤ exitLeak blocks := by
  induction blocks generalizing y with
  | nil => simp [resStack, toBlocks, exitLeak]
  | cons d bs ih =>
      have hstep : resStack (toBlocks (d :: bs)) y
          = resStack (toBlocks bs) (y + d.res y) := rfl
      have hsplit : resStack (toBlocks bs) (y + d.res y) - y
          = (resStack (toBlocks bs) (y + d.res y) - (y + d.res y))
            + d.res y := by abel
      have hb' : ∀ d ∈ bs, ∀ z : X, ‖d.res z‖ ≤ (d.bres : ℝ) :=
        fun d hd z => hb d (List.mem_cons_of_mem _ hd) z
      have hbd : ‖d.res y‖ ≤ (d.bres : ℝ) := hb d List.mem_cons_self y
      have hge1 : (1 : ℝ) ≤ (stackGain (toBlocks bs) : ℝ) :=
        by exact_mod_cast stackGain_ge_one _
      have hm : (d.bres : ℝ)
          ≤ d.bres * (stackGain (toBlocks bs) : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hge1
          (NNReal.coe_nonneg d.bres)
        rw [mul_one] at hmul
        exact hmul
      rw [hstep, hsplit]
      simp only [exitLeak]
      calc ‖(resStack (toBlocks bs) (y + d.res y) - (y + d.res y))
              + d.res y‖
          ≤ ‖resStack (toBlocks bs) (y + d.res y) - (y + d.res y)‖
              + ‖d.res y‖ := norm_add_le _ _
      _ ≤ exitLeak bs + (d.bres : ℝ) := add_le_add (ih hb' _) hbd
      _ ≤ d.bres * (stackGain (toBlocks bs) : ℝ)
              + exitLeak bs := by linarith

/-- MAIN 1 (error side): exiting the stack at depth `k` (first k
blocks, then identity) perturbs the pre-head state by at most the
tail `exitLeak` — the early-exit error bound. Valid for EVERY k
(over-deep exit: tail empty, bound zero). -/
theorem early_exit_error (blocks : List (DepthBlock X)) (k : ℕ)
    (hb : ∀ d ∈ blocks, ∀ z : X, ‖d.res z‖ ≤ (d.bres : ℝ)) (x : X) :
    ‖resStack (toBlocks blocks) x - resStack (toBlocks (blocks.take k)) x‖
      ≤ exitLeak (blocks.drop k) := by
  have hsplit : toBlocks blocks
      = toBlocks (blocks.take k) ++ toBlocks (blocks.drop k) := by
    simp [toBlocks]
  have hbdrop : ∀ d ∈ blocks.drop k, ∀ z : X, ‖d.res z‖ ≤ (d.bres : ℝ) :=
    fun d hd z => hb d (List.mem_of_mem_drop hd) z
  rw [hsplit, resStack_append]
  exact resStack_skip_le _ hbdrop _

/-- MAIN 2 (head-composed bound): the exit head applied at depth k
vs the same head at the full output differs by at most `Lh` times
the tail `exitLeak` (transfer style: head Lipschitz composes
through the skip distance). -/
theorem early_exit_error_bound (blocks : List (DepthBlock X)) (k : ℕ)
    (hb : ∀ d ∈ blocks, ∀ z : X, ‖d.res z‖ ≤ (d.bres : ℝ)) (x : X)
    {head : X → X} {Lh : NNReal} (hLh : LipschitzWith Lh head) :
    ‖head (resStack (toBlocks (blocks.take k)) x)
        - head (resStack (toBlocks blocks) x)‖
      ≤ Lh * exitLeak (blocks.drop k) := by
  have h2 := early_exit_error blocks k hb x
  rw [norm_sub_rev] at h2
  have h1 : ‖head (resStack (toBlocks (blocks.take k)) x)
        - head (resStack (toBlocks blocks) x)‖
      ≤ Lh * ‖resStack (toBlocks (blocks.take k)) x
          - resStack (toBlocks blocks) x‖ := by
    simpa [dist_eq_norm] using hLh.norm_sub_le _ _
  calc ‖head (resStack (toBlocks (blocks.take k)) x)
          - head (resStack (toBlocks blocks) x)‖
        ≤ Lh * ‖resStack (toBlocks (blocks.take k)) x
            - resStack (toBlocks blocks) x‖ := h1
    _ ≤ Lh * exitLeak (blocks.drop k) :=
        mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg Lh)

/-- The per-block work sum (count model per layer). -/
def blockWork (blocks : List (DepthBlock X)) : ℕ :=
  (blocks.map DepthBlock.work).sum

/-- MAIN 3 (work side): the exact ledger split — the work of
exiting at k plus the skipped tail work equals the full work
(hence the exited work never exceeds the full work). -/
theorem early_exit_work (blocks : List (DepthBlock X)) (k : ℕ) :
    blockWork (blocks.take k) + blockWork (blocks.drop k)
      = blockWork blocks := by
  simp only [blockWork, ← List.map_append, ← List.sum_append,
    List.take_append_drop]

/-- MAIN 4 (the two-sided per-token certificate): IF the
(arbitrary, premise) depth router fires at `k = route x`, THEN the
token's head-output error is at most `Lh · exitLeak tail` AND its
executed work is at most the full work — one certificate, both
books. The exit RULE itself is a premise: no optimality claim. -/
theorem early_exit_certificate (blocks : List (DepthBlock X))
    {head : X → X} {Lh : NNReal}
    (route : X → ℕ) (hLh : LipschitzWith Lh head)
    (hb : ∀ d ∈ blocks, ∀ z : X, ‖d.res z‖ ≤ (d.bres : ℝ)) (x : X) :
    ‖head (resStack (toBlocks (blocks.take (route x))) x)
        - head (resStack (toBlocks blocks) x)‖
      ≤ Lh * exitLeak (blocks.drop (route x))
    ∧ blockWork (blocks.take (route x)) ≤ blockWork blocks := by
  refine ⟨early_exit_error_bound blocks (route x) hb x hLh, ?_⟩
  have h := early_exit_work blocks (route x)
  omega

/-! ## Numeric anchors (two-layer tail) -/

namespace Anchor

private noncomputable def d1 : DepthBlock X :=
  ⟨fun _ => 0, 1 / 5, 1 / 2, 1000⟩

private noncomputable def d2 : DepthBlock X :=
  ⟨fun _ => 0, 3 / 10, 1 / 2, 1000⟩

/-- The anchor exit-leak arithmetic: b·(1+μ₂) + b with μ = 1/5,
3/10 and b = 1/2 gives 23/20 — the tail bound with per-layer
residual magnitudes. -/
theorem anchor_exitLeak :
    exitLeak [(d1 : DepthBlock X), d2] = 23 / 20 := by
  norm_num [exitLeak, toBlocks, stackGain, d1, d2]

/-- The anchor work ledger: exiting after the first of two blocks
executes 1000 of the full 2000 work units (the tail 1000 skipped). -/
theorem anchor_work :
    blockWork [(d1 : DepthBlock X), d2]
      - blockWork (List.take 1 [(d1 : DepthBlock X), d2]) = 1000 := by
  have h := early_exit_work [(d1 : DepthBlock X), d2] 1
  simp only [blockWork, List.take, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, d1, d2] at h ⊢
  norm_num

end Anchor

end Hagi.Contracts.DepthExitCert
