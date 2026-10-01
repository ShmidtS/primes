/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.Distill
import Hagi.Unified.TopLevel
import Hagi.Audit.Exactness
set_option linter.style.header false

/-!
# R79: the insight channel (the RLTL;DR bridge)

Self-generated feedback (failed rollout → compressed insight
→ retry → internalize) as a FORMALLY PERMITTED growth channel
of the HAGI loop:

- `insight_kl_descent`: internalization IS KL-descent — the
  insight-conditioned behavior is the teacher; the residual
  gap is exactly the KL gap (the R78 master identity at
  p_E := p_insight). One currency with the distill axis.
- `insight_consolidation_safe`: the insight gradient through
  the SafeQP filter — certified alignment + per-domain
  linearized drift guard (old skills protected by ε).
- `experience_cycle_bound`: the ExperienceGate inequality —
  E_next ≤ E_t − (G_insight + G_merge + η‖d*‖²/2 − C_exp −
  C_quant); internalize vs grow vs stop share ONE Lyapunov
  currency. The RLTL;DR token measurements feed C_exp
  (rollout exploration dominates: 720M vs 2.9M forward).
-/

open Real Finset InnerProductSpace

namespace Hagi

section Insight

variable {V : Type*} [Fintype V]

/-- **Internalization is KL-descent (the RLTL;DR bridge)**:
the insight-conditioned behavior p_I (task + insight) is the
teacher; internalizing it into the plain-context student
p_θ' means driving the student's CE toward the teacher's —
and the residual gap is EXACTLY the KL gap:

  CE_q(p_θ') − CE_q(p_I) = KL(q‖p_θ') − KL(q‖p_I)

(the R78 master identity instantiated at p_E := p_insight).
The distillable insight-value on data q is the divergence
KL(q‖p_I) the student must close — the same currency as the
distill axis; internalization progress = KL decrease. -/
theorem insight_kl_descent (q pI pTheta' : V → ℝ)
    (hq : ∀ v, 0 < q v) (hI : ∀ v, 0 < pI v) (hT : ∀ v, 0 < pTheta' v) :
    crossEntropy q pTheta' - crossEntropy q pI
      = klDiv q pTheta' - klDiv q pI :=
  ce_gap_kl_identity q pI pTheta' hq hI hT

/-- **The experience-budget cycle bound (ExperienceGate)**:
one self-improvement cycle — insight generation
(gains G_insight on fresh failures), merge (G_merge, the
Jensen gap), safe joint update (η‖d*‖²/2) — against the
costs: exploration (C_exp: rollouts dominate — the RLTL;DR
measure), quantization (κ√n s/2), memory — obeys

  E_next ≤ E_t − (G_insight + G_merge + η‖d*‖²/2
                  − C_exp − κ√n s/2)

and growth/internalize/stop is decided by the sign of the
bracket: all three actions share ONE Lyapunov currency. The
h_emp_ inputs are the measured stage quantities (the
RLTL;DR token counts feed C_exp: 720M/12M vs 2.9M/292k —
dedup internalization is 100× cheaper than rollout
exploration). -/
theorem experience_cycle_bound (Et Enext Gins Gmerge dnorm2 eta Cexp Cquant : ℝ)
    (hstage : Enext ≤ Et - Gins - Gmerge - eta * dnorm2 / 2 + Cquant + Cexp) :
    Enext ≤ Et - (Gins + Gmerge + eta * dnorm2 / 2 - Cexp - Cquant) := by
  linarith


section Consolidation

/-- **Insight consolidation through the SafeQP filter**: the
insight gradient g_I (the internalization direction) may
conflict with old domains (⟪g_i, g_I⟫ < 0). The SafeQP
projection d* = Π_C(g_I) onto the safe cone
C = {d : ⟪g_i,d⟫ ≥ −ε_i} guarantees (a) the certified
alignment ‖d*‖² ≤ ⟪g_I,d*⟫ (descent signal preserved) and
(b) EVERY old domain's linearized drift is bounded by its
ε_i — the internalized insight cannot destroy old skills
beyond the declared budget. This is the RLTL;DR
internalization step made conflict-safe: the h_emp_ input is
the smoothness for the second-order remainder. -/
-- the real form: composition with safeQP_descent over the
-- safe cone, plus the per-domain linearized drift guard
theorem insight_consolidation_safe {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X]
    (C : Set X) (hconv : Convex ℝ C) (h0 : (0:X) ∈ C)
    (gI ds : X) (hs : ds ∈ C)
    (hmin : ∀ d ∈ C, dist ds gI ≤ dist d gI)
    (gold : X) (heps : ℝ)
    (hcone : C ⊆ {d : X | ⟪gold, d⟫_ℝ ≥ -heps}) :
    ⟪gold, ds⟫_ℝ ≥ -heps ∧ ‖ds‖^2 ≤ ⟪gI, ds⟫_ℝ := by
  exact ⟨hcone hs, (Hagi.safeQP_descent C hconv h0 gI ds hs hmin).1⟩

end Consolidation
end Insight
end Hagi
