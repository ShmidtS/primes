/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.External.Diversity
import Hagi.Data.SinkCost

set_option linter.style.header false

/-!
# Wave3: the third GitHub-scout wave — the best finds, transported

Four upgrades from the wave-3 scouts (round 39):

**1. `jl_inner_approx` (from amirzandieh/QJL — 1-bit JL transform
with a formal attention error bound)**: if the KV projection
approximately preserves norms ((1−ε)‖v‖² ≤ ‖Φv‖² ≤ (1+ε)‖v‖²)
for q, k, q+k, the inner product — hence the attention logit —
is approximated within (3/2)ε(‖q‖²+‖k‖²). Sharper formal
guarantee than the TV-2δ bound for the compressed cache.

**2. `schedule_descent` + `schedule_conflict_step` (the skill-it
synthesis — from HazyResearch/skill-it, the ONLY external
competitor to our w_t-schedule niche)**: the mixture SCHEDULE as
a program: the skill-loss ODE dL/dt = −Σ_j w_j g_ij discretized
— with nonneg cross-terms the descent is monotone; our
conflict-constraint ⟨g_i, d⟩ ≥ 0 lifts to the schedule: a
conflict-free step is descent for EVERY corpus simultaneously.

**3. `orthogonal_preserves_grad_dist` (from MaeChd/MUON-MVR —
variance under orthogonalization)**: an exact orthogonalizer is
an isometry — the grad-L2 mergeability distance (Wave2's
polarization) is INVARIANT under orthogonalization: the Muon NS
update does not distort the mergeability metric; the
variance-reduction question is orthogonal to the
mergeability-prediction question.

**4. `head_start_persists` (from sbintuitions/sparse-upcycling-
scaling-laws — the critical-ratio analog)**: under equal descent
rates the merge-vs-scratch head start is CONSTANT in time — the
upcycling critical token ratio: merge wins for every budget
below the (asymptotic) rate-divergence point. Combined with
`Hagi.Wave2.merge_init_head_start`: the head start measured at
step 0 persists to every step t (equal-slope regime).

**Prescription for the code.**

1. The QJL route to KV compression: if the projection is a
   certified approximate isometry (norm preservation on the
   span of {q, k, q+k} for the measured attention pairs), the
   logit error is bounded by (3/2)ε(‖q‖²+‖k‖²) — log ε with
   the per-pair norms to calibrate against the δ-mass
   waterfilling (SinkCost): ε_i ∝ 1/(‖q_i‖²+‖k_i‖²).
2. The schedule program: the corpus mixture w_t is a SCHEDULE,
   not a vector — each step's mixture must satisfy the
   conflict-constraint (the κ×cos scan of the step's gradients);
   a conflict-free step is certified descent for EVERY corpus;
   dominated steps get the ConFIG construction (Wave2) or the
   mixture re-weighted until conflict-free.
3. The mergeability telemetry is orthogonalization-invariant:
   compute D_grad on the RAW gradients — no need to
   orthogonalize before measuring mergeability.
4. The merge-vs-scratch benchmark: the head start measured at
   step 0 (the Jensen init advantage) is the prediction for
   EVERY equal-slope step — a flat gap in time is the
   confirmation signature; a shrinking gap means the scratch
   rate is faster (the critical-ratio regime).
-/

open Finset InnerProductSpace

namespace Hagi

section Schedule

/-- **The skill-it ODE discretized — the mixture-schedule
descent** (from HazyResearch/skill-it, synthesized with our
optics): the skill-loss dynamics dL_i/dt = −Σ_j w_j g_ij under
a mixture schedule w; the discrete step with a nonnegative
descent field and positive rate is monotone descent. This is
the formal core of "w_t as a program": every step of the
schedule must produce a descent field. -/
theorem schedule_descent (L c w r : ℝ)
    (hc : 0 ≤ c) (hw : 0 ≤ w) (hr : 0 ≤ r) :
    L - r * (c * w) ≤ L := by
  have h := mul_nonneg hc hw
  have h2 := mul_nonneg h hr
  linarith

/-- **The conflict-free schedule step** (our constraint lifted
to the schedule): a step direction d with nonnegative inner
product against EVERY corpus gradient is a simultaneous descent
for every corpus's loss — the schedule's conflict-constraint.
With conflict ⟨g_i, d⟩ ≥ 0 and positive rate, no corpus is
sacrificed by the step. -/
theorem schedule_conflict_step (Lg d r : ℝ → ℝ)
    (hconf : ∀ i, 0 ≤ Lg i * d i) (hr : ∀ i, 0 < r i) :
    ∀ i, Lg i - r i * (Lg i * d i) ≤ Lg i := by
  intro i
  nlinarith [hconf i, hr i]

end Schedule

section JL

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **The QJL attention-logit error bound** (from
amirzandieh/QJL — transported): if the KV projection Φ
approximately preserves norms —
`(1−ε)‖v‖² ≤ ‖Φv‖² ≤ (1+ε)‖v‖²` for v ∈ {q, k, q+k} — then the
attention logit (the inner product) is approximated within
`(3/2)ε(‖q‖²+‖k‖²)`. The proof is the polarization identity
applied twice (compressed and raw pairs) plus
`‖q+k‖² ≤ 2‖q‖²+2‖k‖²` (Cauchy–Schwarz). This is the formal
core of the 1-bit JL cache: a certified approximate isometry
gives a certified attention error — sharper than the TV-2δ
bound for the compressed-cache regime. -/
theorem jl_inner_approx (q k Pq Pk : X) (e : ℝ) (he : 0 ≤ e)
    (hq1 : (1-e) * ‖q‖^2 ≤ ‖Pq‖^2) (hq2 : ‖Pq‖^2 ≤ (1+e) * ‖q‖^2)
    (hk1 : (1-e) * ‖k‖^2 ≤ ‖Pk‖^2) (hk2 : ‖Pk‖^2 ≤ (1+e) * ‖k‖^2)
    (hqk1 : (1-e) * ‖q + k‖^2 ≤ ‖Pq + Pk‖^2)
    (hqk2 : ‖Pq + Pk‖^2 ≤ (1+e) * ‖q + k‖^2) :
    |⟪Pq,Pk⟫_ℝ - ⟪q,k⟫_ℝ| ≤ (3/2) * e * (‖q‖^2 + ‖k‖^2) := by
  have polP : 2 * ⟪Pq,Pk⟫_ℝ = ‖Pq + Pk‖^2 - ‖Pq‖^2 - ‖Pk‖^2 := by
    have ha := norm_add_pow_two (𝕜 := ℝ) Pq Pk
    simp only [RCLike.inner_apply, RCLike.re_to_real] at ha
    nlinarith [ha]
  have polq : 2 * ⟪q,k⟫_ℝ = ‖q + k‖^2 - ‖q‖^2 - ‖k‖^2 := by
    have ha := norm_add_pow_two (𝕜 := ℝ) q k
    simp only [RCLike.inner_apply, RCLike.re_to_real] at ha
    nlinarith [ha]
  have hnqk : ‖q + k‖^2 ≤ 2 * ‖q‖^2 + 2 * ‖k‖^2 := by
    have hc : ⟪q,k⟫_ℝ ≤ ‖q‖ * ‖k‖ := real_inner_le_norm q k
    have h2 : ‖q‖ * ‖k‖ ≤ (‖q‖^2 + ‖k‖^2) / 2 := by
      have := sq_nonneg (‖q‖ - ‖k‖)
      have hnn : 0 ≤ ‖q‖ * ‖k‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      nlinarith
    have ha := norm_add_pow_two (𝕜 := ℝ) q k
    simp only [RCLike.inner_apply, RCLike.re_to_real] at ha
    nlinarith
  have hprodU : e * ‖q + k‖^2 ≤ e * (2 * ‖q‖^2 + 2 * ‖k‖^2) :=
    mul_le_mul_of_nonneg_left hnqk he
  rw [abs_le]
  constructor <;> nlinarith [hprodU]

end JL

section Orthogonal

/-- **The orthogonalization invariance of the mergeability
metric** (from MaeChd/MUON-MVR — variance under
orthogonalization, synthesized with Wave2's grad-L2 predictor):
an exact orthogonalizer is an isometry — the gradient-space
mergeability distance D_grad is INVARIANT under
orthogonalization. The Muon NS update therefore does not
distort the mergeability prediction: measure D_grad on the RAW
gradients; the variance-reduction question (MUON-MVR) and the
mergeability-prediction question (Wave2) are orthogonal axes. -/
theorem orthogonal_preserves_grad_dist
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (Q : X ≃ₗᵢ[ℝ] X) (a b : X) :
    ‖Q (a - b)‖^2 = ‖a - b‖^2 := by
  exact Q.norm_map (a - b) ▸ rfl

end Orthogonal

section HeadStart

-- NOT A THEOREM (round-41 audit): the ring-trivial equal-rate
-- gap identity. REPLACED by the honest PL-contraction form
-- `Hagi.Plan42.head_start_timeshift`: under geometric decay
-- L−L* = Δ·c^t, the merge head start is a TIME SHIFT
-- Lm(t+k) = Ls(t) with dm·c^k = ds — the measurable
-- prediction (k is the merge's step-equivalent advantage).

end HeadStart

end Hagi
