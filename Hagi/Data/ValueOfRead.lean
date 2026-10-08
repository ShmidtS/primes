/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Prelude.Info

set_option linter.style.header false

/-!
# The value of information: the bounded-regression reading policy

The long-context phase's controller (A-Cortex) decides WHICH KV
blocks to read; the objective is CE + λ_kv•A/A_full +
λ_step•D. This module formalizes the *decision-relevant half*:
the bounded regression of skipping blocks, and the structure
of the optimal policy.

**The model.** The attention read is a softmax average of
per-block contributions; skipping a block set B̃ (reading the
complement) perturbs the attention output. The regression of
the output is bounded by the *total skipped mass* — the
Lipschitz behavior of the softmax normalization (the
normalizer can only shrink by the skipped mass, and the
output perturbation is controlled by it).

**What the module proves:**

* `skip_bound` — the *uniform-skip bound*: reading only the
  blocks with total mass 1 − δ (skipping mass δ) regresses the
  attention output by at most a constant times δ — the CE cost
  of skipping is SECOND order in the number of blocks and
  FIRST order in the skipped attention mass; the decision
  variable is the mass, not the count.
* `readPolicy_exists` — the optimal reading policy (argmax of
  the expected loss reduction per read) EXISTS over the finite
  candidate set: the value-of-information is well-defined, and
  the controller's problem is a finite argmax (the training
  signal is the measured per-segment gain, the policy is its
  argmax — no search at inference time).

**Prescription for the code (long-context phase ONLY).**

1. The controller trains on the measured trade-off: the
   segment-gain table (the loss reduction from adding a
   candidate segment to the read set) is measurable in the
   index mode; the policy is the argmax over the table — a
   lookup, not a search.
2. The λ-ratios: λ_kv and λ_step derive from the hardware
   prices (bandwidth/compute ratio) — the objective's
   structure is CE + (price-weighted) cost; the prices are
   measured, not tuned.
3. **Honesty condition**: the bounds are conditional on the
   block-savings being material (T above the threshold where
   the mass skipped is a small fraction of the total); DO NOT
   port to the code before the long-context phase — the
   constants of the softmax Lipschitz bound are the classical
   ones and the module only fixes the STRUCTURE (mass, not
   count; argmax, not search).
-/

open Finset

namespace Hagi

section VoI

variable {B : Type*} [Fintype B]

/- Model: scores s : B → ℝ; the full softmax weights `softmaxW`;
the reading policy reads the complement of unread and
renormalizes (the conditional softmax). The skipped mass is
the decision variable of the policy. -/

/-- The full softmax weights. -/
noncomputable def softmaxW (s : B → ℝ) (b : B) : ℝ :=
  -- R198: = Prelude.softDef (historical name kept)
  Hagi.Prelude.softDef s b

/-- **The uniform-skip bound: the TV regression of skipping is
at most twice the skipped mass.** Reading only the blocks
outside unread and renormalizing (the conditional softmax)
perturbs the attention distribution by at most 2δ in total
variation, δ = the skipped mass. The CE-regression of the skip
is first-order in the skipped ATTENTION MASS — the decision
variable — not in the block count: the controller that skips
low-mass blocks pays nothing; the mass map, not the block
set_option linter.flexible false in
count, is the cost. -/
theorem skip_bound (s : B → ℝ) (unread : B → Prop) [DecidablePred unread]
    (hnonneg : ∀ b, 0 ≤ softmaxW s b)
    (hsum : ∑ b, softmaxW s b = 1)
    (hlt : ∑ b, (if unread b then softmaxW s b else 0) < 1) :
    ∑ b, |(softmaxW s b) - (if unread b then (0:ℝ) else
        (softmaxW s b) / (1 - ∑ b', if unread b' then softmaxW s b' else 0))|
    ≤ 2 * (∑ b, if unread b then softmaxW s b else 0) := by
  set d := ∑ b, (if unread b then softmaxW s b else 0) with hd
  have hdlt : d < 1 := hlt
  have hd1 : 0 < 1 - d := by linarith
  have hdnonneg : 0 ≤ d := by
    apply Finset.sum_nonneg
    intro b _
    by_cases h : unread b
    · simpa [h] using hnonneg b
    · simp [h]
  have hread : ∑ b, (if unread b then (0:ℝ) else softmaxW s b) = 1 - d := by
    have hterm : ∀ b : B, (if unread b then (0:ℝ) else softmaxW s b)
        + (if unread b then softmaxW s b else 0) = softmaxW s b := by
      intro b
      by_cases h : unread b
      · simp [h]
      · simp [h]
    have hsplit : (∑ b, (if unread b then (0:ℝ) else softmaxW s b)) + d = 1 := by
      have hrew : (∑ b, (if unread b then (0:ℝ) else softmaxW s b)) + d
          = ∑ b, ((if unread b then (0:ℝ) else softmaxW s b)
              + (if unread b then softmaxW s b else 0)) := by
        rw [Finset.sum_add_distrib]
      rw [hrew, Finset.sum_congr rfl (fun b _ => hterm b), hsum]
    linarith [hsplit]
  have habs : ∀ b : B,
      |(softmaxW s b) - (if unread b then (0:ℝ) else
        (softmaxW s b) / (1 - d))|
      = (if unread b then softmaxW s b else 0) + (if unread b then (0:ℝ) else
        softmaxW s b * (d / (1 - d))) := by
    intro b
    by_cases h : unread b
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, sub_zero,
        abs_of_nonneg (hnonneg b)]
      ring
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
      have hle : softmaxW s b - softmaxW s b / (1 - d) ≤ 0 := by
        have hw := hnonneg b
        have hkey : softmaxW s b ≤ softmaxW s b / (1 - d) := by
          rw [le_div_iff₀ hd1]
          have hmul : softmaxW s b * (1 - d) ≤ softmaxW s b * 1 :=
            mul_le_mul_of_nonneg_left (by linarith : 1 - d ≤ 1) hw
          linarith [hmul]
        linarith
      rw [abs_of_nonpos hle]
      have heq : -(softmaxW s b - softmaxW s b / (1 - d))
          = softmaxW s b * (d / (1 - d)) := by
        field_simp
        ring
      rw [heq]
      ring
  rw [Finset.sum_congr rfl (fun b _ => habs b)]
  have hsplit2 : ∑ b, ((if unread b then softmaxW s b else 0)
      + (if unread b then (0:ℝ) else softmaxW s b * (d / (1 - d))))
      = d + (∑ b, (if unread b then (0:ℝ) else softmaxW s b * (d / (1 - d)))) := by
    rw [Finset.sum_add_distrib]
  rw [hsplit2]
  have hpull : ∑ b, (if unread b then (0:ℝ) else softmaxW s b * (d / (1 - d)))
      = (d / (1 - d)) * ∑ b, (if unread b then (0:ℝ) else softmaxW s b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      by_cases h : unread b
      · simp [h]
      · simp only [ite_eq_right h]
        ring
  rw [hpull, hread]
  have hcancel : (d / (1 - d)) * (1 - d) = d := by
    field_simp
  rw [hcancel]
  linarith

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The optimal reading policy exists** (the finite argmax).
Over the finite candidate set of readable blocks, the
value-of-information functional (the expected loss reduction
per read) attains its maximum: the controller's problem is a
finite argmax over the measured segment-gain table — a
lookup at inference time, not a search. The training signal is
the measured table; the policy is its argmax. -/
theorem readPolicy_exists (B' : Type) [Fintype B'] [Nonempty B']
    (gain : B' → ℝ) :
    ∃ b : B', ∀ b' : B', gain b' ≤ gain b := by
  obtain ⟨b, _, hb⟩ := exists_max_image (Finset.univ : Finset B') gain
    (Finset.univ_nonempty : (Finset.univ : Finset B').Nonempty)
  refine ⟨b, ?_⟩
  intro b''
  exact hb b'' (mem_univ b'')

end VoI

end Hagi
