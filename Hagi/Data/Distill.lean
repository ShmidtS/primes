/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Prelude.Info

set_option linter.style.header false

/-!
# Distill: the exact CE/KL identities of the distillation axis

 honesty fix: `crossEntropy` now carries the standard
minus sign (CE_q(p) = −Σ q log p), `klDiv` is defined as
Σ q log(q/p), and the two identities are proved against
these REAL definitions (the pre- versions were trivial
algebra on a signless pseudo-CE).

**The exact identities (THEOREMS):**

* `kl_eq_ce_gap` — KL(q‖p) = CE_q(p) − CE_q(q) for
  positive distributions: the divergence is the excess
  cross-entropy over the entropy baseline.

* `ce_gap_kl_identity` — THE master identity: for any data
  distribution q and models p_E, p_θ:

`CE_q(p_θ) − CE_q(p_E) = KL(q‖p_θ) − KL(q‖p_E)` —

  the CE gap IS the KL gap against the DATA distribution;
  the data q appears irreducibly (the naive bound
  CE_θ ≤ CE_ens + KL(p_E‖p_θ) is FALSE in general — hard
  labels do not transmit the teacher's calibration).

* `teacher_generated_identity` — THE distillation theorem:
  when the targets ARE the teacher's distribution (q = p_E,
  the soft-target protocol):

`CE_{p_E}(p_θ) = H(p_E) + KL(p_E‖p_θ)` —

  the student's soft-target CE is the teacher's entropy plus
  the teacher-student divergence; the distillable gap is
  EXACTLY the divergence.

**The expressivity hypothesis (not a theorem).** Whether an
H=384 student can drive E[KL(p_E‖p_θ)] ≤ δ is the open
expressivity question (round 22 P4): recorded as the
explicit hypothesis DistillExpressivity(H, δ) with the
practical go/no-go — the distill run's plateau behavior
(KL plateau vs continued descent).

**Prescription for the code.**

1. The distillation objective is the soft-target CE
   (q = p_E): minimize KL(p_E‖p_θ) — the identity certifies
   this is EXACTLY the distillable gap.
2. The stopping rule: both plateaus (KL and held-out CE)
   checked separately.
3. The verdict telemetry: E[KL(p_E‖p_θ)] per checkpoint +
   exact held-out CE; a high KL plateau is the expressivity
   wall — record REFUTED honestly.
-/

open Finset

namespace Hagi

section Distill

variable {V : Type*} [Fintype V]

/-- The cross-entropy of model p against distribution q:
CE_q(p) = −Σ q log p (the standard sign — fix). -/
noncomputable def crossEntropy (q p : V → ℝ) : ℝ :=
  -∑ v, q v * Real.log (p v)

/-- The Kullback–Leibler divergence KL(q‖p) = Σ q log(q/p)
(the real definition — fix). -/
noncomputable def klDiv (q p : V → ℝ) : ℝ :=
  --: = Prelude.klDef (kept under the historical name)
  Hagi.Prelude.klDef q p

/-- **KL is the excess cross-entropy** over the entropy
baseline: KL(q‖p) = CE_q(p) − CE_q(q) for strictly positive
distributions (q a distribution, p positive). -/
theorem kl_eq_ce_gap (q p : V → ℝ) (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v) :
    klDiv q p = crossEntropy q p - crossEntropy q q := by
  unfold klDiv crossEntropy Hagi.Prelude.klDef
  have hsplit : ∀ v : V, q v * Real.log (q v / p v)
      = q v * Real.log (q v) - q v * Real.log (p v) := by
    intro v
    rw [Real.log_div (hq v).ne' (hp v).ne']
    ring
  rw [show ∑ v, q v * Real.log (q v / p v)
      = ∑ v, (q v * Real.log (q v) - q v * Real.log (p v)) from
      Finset.sum_congr rfl (fun v _ => hsplit v)]
  rw [show ∑ v : V, (q v * Real.log (q v) - q v * Real.log (p v))
      = (∑ v : V, q v * Real.log (q v)) - (∑ v : V, q v * Real.log (p v)) from
      sum_sub_distrib (fun v : V => q v * Real.log (q v))
        (fun v : V => q v * Real.log (p v))]
  ring

/-- **The master identity (theorem, real version).**
For any data distribution q and models p_E, p_θ (all
positive):

`CE_q(p_θ) − CE_q(p_E) = KL(q‖p_θ) − KL(q‖p_E)` —

the CE gap IS the KL gap against the data; q is
irreducible. The naive hard-label bound is FALSE in general
(hard labels do not carry the teacher's calibration) — this
identity is the honest replacement. -/
theorem ce_gap_kl_identity (q pE pTheta : V → ℝ)
    (hq : ∀ v, 0 < q v) (hpE : ∀ v, 0 < pE v) (hpT : ∀ v, 0 < pTheta v) :
    crossEntropy q pTheta - crossEntropy q pE
      = klDiv q pTheta - klDiv q pE := by
  rw [kl_eq_ce_gap q pTheta hq hpT, kl_eq_ce_gap q pE hq hpE]
  ring

/-- **The teacher-generated distillation identity
(theorem, real version).** When the targets are the
teacher's own distribution (the soft-target protocol,
q = p_E):

`CE_{p_E}(p_θ) = CE_{p_E}(p_E) + KL(p_E‖p_θ)` —

CE_{p_E}(p_E) is the teacher's entropy H(p_E): the
student's soft CE is the teacher's entropy plus the
teacher-student divergence — the distillable gap is EXACTLY
the divergence. -/
theorem teacher_generated_identity (pE pTheta : V → ℝ)
    (hpE : ∀ v, 0 < pE v) (hpT : ∀ v, 0 < pTheta v) :
    crossEntropy pE pTheta = crossEntropy pE pE + klDiv pE pTheta := by
  rw [kl_eq_ce_gap pE pTheta hpE hpT]
  ring

end Distill

end Hagi
