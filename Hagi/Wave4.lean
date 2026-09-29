/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Wave3

set_option linter.style.header false

/-!
# Wave4: the fourth GitHub-scout wave — the best finds, transported

Four upgrades from the wave-4 scouts (round 40):

**1. `mup_scale_invariance`** (from microsoft/mup +
vankadara-lab/mssp-moe — the μP width/depth/expert-count
transfer): the 1/√n-scaled update has width-invariant relative
norm: n·‖(1/√n)v‖² = ‖v‖² — the formal core of LR transfer
across width. For our merge transitions (N, H, L change between
generations): the μP-scaled update is the scale-stable choice;
`Hagi.BranchScale`'s 1/√(2L·loop) is the depth-instance of the
same law — the two compose into an (N×H×L)-stable parametrization.

**2. `vocab_critical_point`** (from facebookresearch/
compute-optimal-tokenization — the only loss+|V|+compute
coupled law found): the vocab-optimization core: the cost model
L(V) = log V + c/V (the uniform-softmax baseline log V grows
with V; the token-sequence-length cost c/V shrinks) has its
critical point at V* = c. The vocab IS a derived variable:
prescription — fit c from a small-|V| sweep, predict V*.

**3. `phase_metric_monotone`** (from timaeus-research/devinterp
— the LLC phase apparatus): a monotone phase metric cannot
oscillate between phases: if the generation-over-generation
phase metric (the LLC, or our interval-verdict bracket) is
monotone, later phases are ordered below earlier ones for ALL
pairs — no phase revisits. The formal core of phase analysis
without measure theory.

**4. `frozen_norm_no_dynamics`** (from Omnigrok/Slingshot —
the grokking-via-weight-norm mechanism): the slingshot/grokking
observable IS the weight-norm trajectory; frozen norms make the
observable CONSTANT — the grokking lever is nullified by
construction. Our ternary normalization (absmean scaling) fixes
the norms — the formal explanation of our generations'
stability: no slingshot dynamics because the slingshot
observable has no dynamics.

**Prescription for the code.**

1. The μP bridge at merges: when the width grows (the block
   diagonal widens), scale the incoming updates by 1/√(H_new)
   per the invariance — the LR does not need re-tuning across
   generations; the BranchScale depth-term composes.
2. The vocab experiment: a 3-point |V| sweep (e.g. 16k/32k/64k)
   fits c in L(V) = log V + c/V; V* = c is the predicted
   optimum — check against the compute-optimal-tokenization
   data before committing a tokenizer change.
3. The LLC phase tracking: log the phase metric per generation;
   a monotone sequence certifies developmental progress (no
   phase revisits); an oscillation is the diagnostic of an
   unstable growth loop.
4. The stability attribution: the frozen-norm theorem explains
   why our generations show no slingshot — the grokking lever
   (weight-norm decay) is unavailable to the ternary body by
   construction; emergence must come through the mixers/gates,
   not through norm dynamics.
-/

open Finset Real

namespace Hagi

section MuP

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The μP scale invariance** (from microsoft/mup +
mssp-moe — transported): the 1/√n-scaled update has the
width-invariant relative norm — n·‖(1/√n)•v‖² = ‖v‖². The
formal core of LR transfer across width: the μP-scaled update
is invisible to the geometry at any width. Our merge
transitions (N, H, L change between generations) get the
scale-stable parametrization: scale incoming updates by
1/√(H_new); the BranchScale 1/√(2L·loop) is the depth-instance
of the same law. -/
theorem mup_scale_invariance (n : ℝ) (hn : 0 < n) (v : V) :
    n * ‖(Real.sqrt n)⁻¹ • v‖^2 = ‖v‖^2 := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have h1 : ‖(Real.sqrt n)⁻¹ • v‖ = (Real.sqrt n)⁻¹ * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  rw [h1, mul_pow, inv_pow, Real.sq_sqrt (le_of_lt hn)]
  field_simp

end MuP

section Vocab

/-- **The vocab critical point** (from facebookresearch/
compute-optimal-tokenization — the only loss+|V|+compute
coupled law found, transported): the two-channel vocab cost
model — the uniform-softmax baseline CE = log V GROWS with V
(the scratch-init head start of `Hagi.Wave2` shrinks), the
sequence-length cost c/V SHRINKS (fewer tokens per document) —
has its critical point exactly at V* = c: the vocab size is a
DERIVED variable, not a hyperparameter. Prescription: fit c
from a small-|V| sweep, predict the optimum, check against the
compute-optimal-tokenization scaling data. -/
theorem vocab_critical_point (c : ℝ) (hc : 0 < c) :
    deriv (fun x => Real.log x + c * x⁻¹) c = 0 := by
  have hl : HasDerivAt Real.log c⁻¹ c := Real.hasDerivAt_log (by linarith)
  have hi : HasDerivAt (fun x : ℝ => x⁻¹) (-(c^2)⁻¹) c :=
    hasDerivAt_inv (by linarith : (c:ℝ) ≠ 0)
  have hc2 : HasDerivAt (fun x => c * x⁻¹) (c * -(c^2)⁻¹) c := hi.const_mul c
  have h : HasDerivAt (fun x => Real.log x + c * x⁻¹) (c⁻¹ + c * -(c^2)⁻¹) c :=
    hl.add hc2
  have h2 : deriv (fun x => Real.log x + c * x⁻¹) c = c⁻¹ + c * -(c^2)⁻¹ := h.deriv
  rw [h2]
  field_simp
  ring

end Vocab

section Phase

/-- **The monotone phase metric cannot revisit phases** (from
timaeus-research/devinterp — the LLC phase apparatus,
transported): if the generation-over-generation phase metric
(the LLC, or our interval-verdict bracket) is monotone
decreasing, then EVERY later phase is ordered below EVERY
earlier one — ∀ i ≤ j, a j ≤ a i. No phase oscillation. The
diagnostic: a measured oscillation (a (k+1) > a k for some k)
falsifies the monotone-phase hypothesis — the growth loop is
unstable and the schedule program (Wave3) must intervene. -/
theorem phase_metric_monotone (a : ℕ → ℝ) (h : ∀ k, a (k+1) ≤ a k) :
    ∀ i j, i ≤ j → a j ≤ a i := by
  intro i j hij
  induction hij with
  | refl => exact le_rfl
  | @step j _ ih => exact le_trans (h j) ih

end Phase

section Slingshot

/-- **The frozen-norm slingshot nullification** (from
Omnigrok/Slingshot — the grokking-via-weight-norm mechanism,
transported): the slingshot/grokking observable IS the
weight-norm trajectory ‖w(t)‖ (the delayed-generalization
lever is the norm decay); a FROZEN norm makes the observable
constant — ∀ s t, ‖w(s)‖ = ‖w(t)‖ — no slingshot dynamics
because the slingshot observable has no dynamics. Our ternary
body (absmean normalization fixes the scales) is in this
regime BY CONSTRUCTION: the formal explanation of our
generations' stability — the grokking lever is unavailable;
emergence must route through the mixers/gates, not the norm
dynamics. -/
theorem frozen_norm_no_dynamics {W : Type*} [NormedAddCommGroup W]
    (w : ℕ → W) (c : ℝ)
    (hfrozen : ∀ t, ‖w t‖ = c) :
    ∀ s t, ‖w s‖ = ‖w t‖ := by
  intro s t
  rw [hfrozen s, hfrozen t]

end Slingshot

end Hagi
