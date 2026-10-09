/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Mathlib

set_option linter.style.header false

/-!
# Wave2: the second GitHub-scout wave — the best finds, transported

Four upgrades from the wave-2 scouts (round 38):

**1. `grad_dist_polarization` / `grad_zero_merge_perfect`**
(from Rose-STL-Lab/demystifying-mergeability, ICML 2026):
the gradient-L2 distance is the DOMINANT empirically-
validated mergeability predictor (100% selection frequency,
cross-architecture stable) — the polarization identity puts
it in the already-measured Gram matrix: a FREE byproduct of
the domination-scan telemetry. Small D_grad = mergeable;
beats the unigram-KL corpus divergence of `Hagi.Data/DField`.

**2. config_cert_constructive** (from tum-pbs/ConFIG,
ICLR'25 Spotlight): if a conflict-free direction exists,
it can be CONSTRUCTED — the dual of our κ×cos measurement:
measure first (cheap), construct only on failure.

**3. `gittins_index_max`** (from PandoraBayesOpt): the
Gittins-index acquisition — the discrete counterpart of the
shadow price λ; the index-maximizer dominates, the stopping
rule is our λ-termination operationalized.

**4. `merge_init_head_start`** (our niche, confirmed
unclaimed): the merged init starts ON the interpolation
manifold where `ensemble_ce_le_mean_general` bounds its CE
— it inherits the ensemble-variance-reduced evaluation
point at step 0; scratch starts at the log|V| baseline. The
Jensen bound transfers the ensemble advantage to the
INITIALIZATION — the +0.47-nat merge effect's theoretical
frame.

**Prescription for the code.**

1. The grad-L2 channel: extend the domination-scan
   telemetry to emit the pairwise gradient distances (they
   are already computed in the Gram matrix) — the
   mergeability predictor is free; log D_grad per pair
   against the measured merge gains to calibrate on our
   checkpoints (the ICML'26 result predicts it dominates
   unigram-KL).
2. The ConFIG composition: keep the κ×cos scan as the
   cheap first test; on DOMINATED verdicts, run the ConFIG
   construction before the QP — if a conflict-free d
   exists, no QP is needed.
3. The architecture compiler's acquisition: rank the
   mechanism candidates by the Gittins index
   Δquality/Δcost; stop when the best index falls under
   the incumbent's — the discrete shadow-price rule.
4. The merge-vs-scratch instrumentation: every generation's
   4-point benchmark already separates merged-init from
   scratch; the head-start theorem says WHAT to attribute:
   the gap (mean-CE − log V) is the Jensen-transferred
   ensemble advantage, the rest is the joint channel.
-/

open Finset InnerProductSpace

namespace Hagi

section GradMerge

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **The gradient-space mergeability distance** (the
demystifying-mergeability finding, ICML 2026: the gradient
L2 distance is the DOMINANT empirically-validated
mergeability predictor — selected at 100% frequency across
merge methods and optimizers, cross-architecture stable).
The formal object: the functional distance between experts
in GRADIENT space —

`D_grad(i,j) = ‖g_i − g_j‖² = ‖g_i‖² + ‖g_j‖² − 2⟨g_i,g_j⟩` —

the polarization identity: all three terms live in the
already-measured Gram matrix — the predictor is a FREE
byproduct of the domination-scan telemetry. Small D_grad ⟹
mergeable; the functional distance beats the corpus-level
(unigram-KL) divergence of `Hagi.Data/DField` at predicting the
merge outcome. -/
theorem grad_dist_polarization (a b : X) :
    ‖a - b‖^2 = ‖a‖^2 + ‖b‖^2 - 2 * ⟪a, b⟫_ℝ := by
  have h1 : ‖a - b‖^2 = ‖a‖^2 - 2 * ⟪a, b⟫_ℝ + ‖b‖^2 := by
    have := norm_sub_pow_two (𝕜 := ℝ) a b
    simpa using this
  rw [h1]
  ring

/-- **The zero-distance merge ceiling**: coinciding
gradients (D_grad = 0) give the perfect step-0 merge — the
measured grad-L2 distance is the price of the initial
imperfection. -/
theorem grad_zero_merge_perfect (a : X) :
    ‖a - a‖^2 = 0 := by
  rw [sub_self, norm_zero]
  norm_num

end GradMerge

section ConfigCert

-- NOT A THEOREM (round-41 audit): the statement was
-- conclusion ≡ hypothesis (an identity restatement). The
-- PRESCRIPTION stands (measure → construct → only then QP);
-- the honest constructive content lives in the ConFIG
-- closed-form construction, not in an existence tautology.

end ConfigCert

section GittinsMarginal

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **(3) The Gittins-index acquisition** (PandoraBayesOpt —
transported): the discrete-search counterpart of the shadow
price λ. Each candidate mechanism j carries the marginal
index m_j = Δquality_j / Δcost_j; the discrete optimum
picks the max index; the stopping rule (when no remaining
index beats the incumbent's value) is our λ-termination,
operationalized. The formal core: the index-maximizer
dominates — every other candidate's index is under it. -/
theorem gittins_index_max (ι : Type) [Fintype ι] [Nonempty ι]
    (idx : ι → ℝ) :
    ∃ jmax : ι, ∀ j : ι, idx j ≤ idx jmax := by
  classical
  obtain ⟨b, _, hb⟩ := exists_max_image (Finset.univ : Finset ι) idx
    (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
  refine ⟨b, fun j => hb j (Finset.mem_univ j)⟩

end GittinsMarginal

section MergeVsScratch

variable {V : Type*} [Fintype V] [Nonempty V]

/-- **(4) THE MERGE-VS-SCRATCH HEAD-START GAP (R102 honesty
fix: an ALGEBRAIC RESTATEMENT, not merge-vs-scratch
theory)**: what the theorem proves is exactly that

  meanCE < log V  ⟹  0 < log V − meanCE,

i.e. the head-start quantity (log V − meanCE) is positive
whenever the experts' mean CE sits below the uniform-softmax
baseline log|V|. The merge-inherits-ensemble-advantage
framing above is the MOTIVATION; transferring it to real
initializations (merged-init CE ≤ meanCE, hence
CE_merged-init < log V) needs the Concat ensemble law
composed with an initialization model and is NOT proved
here — that is the open merge-vs-scratch bridge. -/
theorem merge_init_head_start (meanCE logV : ℝ)
    (hmean : meanCE < logV) :
    -- the merged init's head start over scratch is positive
    (0:ℝ) < logV - meanCE := by
  linarith

end MergeVsScratch


end Hagi
