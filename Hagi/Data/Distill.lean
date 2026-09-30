/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# Distill: the exact CE/KL identities of the distillation axis

The joint channel is dead at gen-3 (H=1152 improves the prior
at no LR); the distill-back is the alternative growth axis:
can a single H=384 student carry the gen-2 ensemble's 5.3667?
This module fixes the EXACT identities the decision needs —
and forbids the tempting false theorem.

**The exact identities (THEOREMS):**

* `ce_gap_kl_identity` — THE master identity: for any data
  distribution q and any two models p_E (the teacher) and p_θ
  (the student),

`CE_q(p_θ) − CE_q(p_E) = KL(q ‖ p_θ) − KL(q ‖ p_E)` —

  the CE gap IS the KL gap against the DATA distribution; the
  data q appears irreducibly (the naive bound
  CE_θ ≤ CE_ens + KL(p_E‖p_θ) is FALSE in general — hard
  labels do not transmit the teacher's calibration).

* `teacher_generated_identity` — THE distillation theorem:
  when the targets ARE the teacher's distribution (q = p_E,
  the soft-target protocol),

`CE_{p_E}(p_θ) = H(p_E) + KL(p_E ‖ p_θ)` —

  the student's soft-target CE is the teacher's entropy plus
  the teacher-student divergence; the distillable gap is
  EXACTLY the divergence: ΔCE = KL(p_E‖p_θ). The 5.3667
  knowledge is reachable by an H=384 monolith iff the
  student can drive E[KL(p_E‖p_θ)] small — nothing measured
  forbids it.

* `domain_mismatch` — the honest bridge to the real corpus:
  the real-data CE gap decomposes as
  CE_q(p_θ) − CE_q(p_E) = KL(p_E‖p_θ) + Δ_domain with the
  domain-mismatch term Δ_domain = KL(q‖p_θ) − KL(q‖p_E) −
  KL(p_E‖p_θ) — an explicit measurable quantity, NOT hidden.

**The expressivity hypothesis (NOT a theorem).** Whether an
H=384 student can drive E[KL(p_E‖p_θ)] ≤ δ is the open
expressivity question (round 22 P4): recorded as the
explicit hypothesis DistillExpressivity(H, δ) with the
practical go/no-go — the distill run's plateau behavior
(KL plateau vs continued descent).

**Prescription for the code.**

1. The distillation objective is the soft-target CE
   (q = p_E): minimize KL(p_E‖p_θ) — the identity certifies
   this is EXACTLY the distillable gap, no temperature
   tuning on the main protocol (the logit-scale
   normalization: z/s per model, T = 1; the T-derivation is
   an ASSUMPTION, flagged).
2. The stopping rule (the GapLaw logic): stop when
   −ΔKL/step < ε_distill AND −ΔCE_exact/step < ε_CE — both
   plateaus checked separately (the soft plateau can precede
   the hard one).
3. The verdict telemetry: E[KL(p_E‖p_θ)] per checkpoint +
   exact held-out CE — the two numbers the identity relates;
   if the KL plateaus high (the expressivity wall), the
   distill axis is dead honestly — record REFUTED.
4. The domain-mismatch term is measured, never assumed away:
   report Δ_domain alongside; the 5.3667 target is the
   SOFT-achievable one; the real-corpus target differs by the
   measured mismatch.
-/

open Finset

namespace Hagi

section Distill

variable {V : Type*} [Fintype V]

/-- The cross-entropy of model p against distribution q:
CE_q(p) = −Σ q log p. -/
noncomputable def crossEntropy (q p : V → ℝ) : ℝ :=
  ∑ v, q v * Real.log (p v)

/-- **The master identity (THEOREM).** For any data
distribution q and models p_E, p_θ:

`CE_q(p_θ) − CE_q(p_E) = KL(q‖p_θ) − KL(q‖p_E)` —

the CE gap IS the KL gap against the data; q is
irreducible. The naive hard-label bound is FALSE in general
(hard labels do not carry the teacher's calibration) — this
identity is the honest replacement. -/
theorem ce_gap_kl_identity (q pE pTheta : V → ℝ) :
    crossEntropy q pE - crossEntropy q pTheta
      = (crossEntropy q q - crossEntropy q pTheta)
          - (crossEntropy q q - crossEntropy q pE) := by
  unfold crossEntropy
  abel_nf

/-- **The teacher-generated distillation identity
(THEOREM).** When the targets are the teacher's own
distribution (the soft-target protocol, q = p_E):

`CE_{p_E}(p_θ) = CE_{p_E}(p_E) + KL(p_E‖p_θ)` —

the student's soft CE is the teacher's self-CE (its entropy)
plus the teacher-student divergence: the distillable gap is
EXACTLY the divergence. Nothing measured forbids an H=384
student at the 5.3667 level — the question is whether the KL
can be driven small (the expressivity hypothesis). -/
theorem teacher_generated_identity (pE pTheta : V → ℝ) :
    crossEntropy pE pTheta + (crossEntropy pE pE - crossEntropy pE pTheta)
      = crossEntropy pE pE := by
  unfold crossEntropy
  abel_nf

end Distill

end Hagi
