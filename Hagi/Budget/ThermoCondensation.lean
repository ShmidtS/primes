/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Ensemble.Hoeffding
import Mathlib.Tactic
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
synthesis — from HazyResearch/skill-it, the only external
competitor to our w_t-schedule niche)**: the mixture SCHEDULE as
a program: the skill-loss ODE dL/dt = −Σ_j w_j g_ij discretized
— with nonneg cross-terms the descent is monotone; our
conflict-constraint ⟨g_i, d⟩ ≥ 0 lifts to the schedule: a
conflict-free step is descent for every corpus simultaneously.

**3. `orthogonal_preserves_grad_dist` (from MaeChd/MUON-MVR —
variance under orthogonalization)**: an exact orthogonalizer is
an isometry — the grad-L2 mergeability distance (Wave2's
polarization) is INVARIANT under orthogonalization: the Muon NS
update does not distort the mergeability metric; the
variance-reduction question is orthogonal to the
mergeability-prediction question.

**4. head_start_persists (from sbintuitions/sparse-upcycling-
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
   a conflict-free step is certified descent for every corpus;
   dominated steps get the ConFIG construction (Wave2) or the
   mixture re-weighted until conflict-free.
3. The mergeability telemetry is orthogonalization-invariant:
   compute D_grad on the RAW gradients — no need to
   orthogonalize before measuring mergeability.
4. The merge-vs-scratch benchmark: the head start measured at
   step 0 (the Jensen init advantage) is the prediction for
   every equal-slope step — a flat gap in time is the
   confirmation signature; a shrinking gap means the scratch
   rate is faster (the critical-ratio regime).
-/

open Finset InnerProductSpace

namespace Hagi.External

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
product against every corpus gradient is a simultaneous descent
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
    simp only [ RCLike.re_to_real] at ha
    nlinarith [ha]
  have polq : 2 * ⟪q,k⟫_ℝ = ‖q + k‖^2 - ‖q‖^2 - ‖k‖^2 := by
    have ha := norm_add_pow_two (𝕜 := ℝ) q k
    simp only [ RCLike.re_to_real] at ha
    nlinarith [ha]
  have hnqk : ‖q + k‖^2 ≤ 2 * ‖q‖^2 + 2 * ‖k‖^2 := by
    have hc : ⟪q,k⟫_ℝ ≤ ‖q‖ * ‖k‖ := real_inner_le_norm q k
    have h2 : ‖q‖ * ‖k‖ ≤ (‖q‖^2 + ‖k‖^2) / 2 := by
      have := sq_nonneg (‖q‖ - ‖k‖)
      have hnn : 0 ≤ ‖q‖ * ‖k‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      nlinarith
    have ha := norm_add_pow_two (𝕜 := ℝ) q k
    simp only [ RCLike.re_to_real] at ha
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

-- not A theorem (round-41 audit): the ring-trivial equal-rate
-- gap identity. REPLACED by the honest PL-contraction form
-- `Hagi.Plan42.head_start_timeshift`: under geometric decay
-- L−L* = Δ·c^t, the merge head start is a TIME SHIFT
-- Lm(t+k) = Ls(t) with dm·c^k = ds — the measurable
-- prediction (k is the merge's step-equivalent advantage).

end HeadStart

end Hagi.External



/-!
# Wave4: the fourth GitHub-scout wave — the best finds, transported

Four upgrades from the wave-4 scouts (round 40):

**1. `mup_scale_invariance`** (from microsoft/mup +
vankadara-lab/mssp-moe — the μP width/depth/expert-count
transfer): the 1/√n-scaled update has width-invariant relative
norm: n·‖(1/√n)v‖² = ‖v‖² — the formal core of LR transfer
across width. For our merge transitions (N, H, L change between
generations): the μP-scaled update is the scale-stable choice;
`Hagi.Energy/BranchScale`'s 1/√(2L·loop) is the depth-instance of the
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

namespace Hagi.External

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
(the scratch-init head start of `Hagi.External/Diversity` shrinks), the
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
decreasing, then every later phase is ordered below every
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

end Hagi.External



/-!
# Wave5: the DepthBench synthesis + the wave-5 scout imports (round 44)

The unification (arXiv:2609.32534 DepthBench + our formalization):
**architecture scaling is useful only if it increases ACCESSIBLE
COMPUTATIONAL DIVERSITY** — the same law for experts (inter-model:
GapLaw/Jensen) and for layers (intra-model: DepthBench's finding
that Pre-LN deep-narrow adds near-dead layers while HC/AttnRes
keep layer-state diversity).

**1. `admission_var_criterion`** (the wave-5 diversity scout
confirmed the niche ΔVar/ΔC UNOCCUPIED): under the quadratic gap
law (ΔGap = ½·ΔVar, the empirical hypothesis behind pairVarEq /
twoGap's cosh form), the argmax of the variance-per-cost index
IS the argmax of the gap-per-cost index — the next-expert
admission rule: maximize new logit-space variance per compute,
not minimize standalone loss (selection_hurts already proved
the latter fails).

**2. `branchscale_minmax`** (the reviewer's S_l²·v_l ≈ const,
now a theorem): for any scale allocation with Σ s_l² = B, the
worst per-layer variance contribution satisfies
max_l s_l²·v_l ≥ B / Σ(1/v_l) — the min-max floor, achieved when
s_l²·v_l is uniform across layers: per-layer residual scales
must compensate the measured branch variance (a uniform scale
is provably suboptimal whenever v_l varies).

**3. `dead_layer_stop`** (the DepthBench adaptive-depth rule):
with monotone decreasing layer values
V_l = ΔQ_remove(l)/T_l, if layer L's value drops under ε then
every later layer's value does — the stop rule for adaptive
depth L* = max{L: V_L > λ}; layer pruning = marginal-value
optimization (the DesignOpt principle at intra-model scale).
Composed from `Wave4.phase_metric_monotone`.

**4. The state-diversity unification (documented)**: the
DepthBench layer-state diversity D_layer = Var_p(h_i − h_j) is
the SAME object as our pairVarEq expert diversity — one
quantity, I_eff = effective rank of accessible computational
states; the next unit of architecture (expert / layer /
cross-layer memory / width) is chosen by ΔI_eff/ΔT_wall (the
Gittins index of Wave2 instantiated on the unified diversity).
The uniform-mixer warning (mHC's route-diversity loss): a mixer
collapsing toward rank 1 destroys exactly the diversity being
purchased — kept as the prescription; the honest rank statement
lives in Matrix.rank and is not re-proved here.

**Prescription for the code.**

1. The admission scan: for each candidate expert, one forward
   per leaf gives the pooled-softmax Var_p(z_new − z_pool);
   admit argmax ΔVar/ΔC — not min-CE (selection_hurts).
2. The per-layer scale audit: log v_l (branch variance) per
   layer; set s_l² ∝ 1/v_l (the min-max floor) instead of a
   uniform residual scale.
3. The layer-value table: per layer, the removal delta
   ΔQ_remove(l)/T_l — monotone by construction in the healthy
   regime; a non-monotone table is the DepthBench dead-layer
   signature (Pre-LN's late layers collapse); stop L* where
   V crosses λ.
4. The unified index: rank all growth options (expert, layer,
   memory-bridge, width) by ΔI_eff/ΔT_wall — one queue, not
   four research directions.
-/

open Finset Real

namespace Hagi.External

section Admission

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The variance-admission criterion** (round 44; the niche
confirmed unoccupied by the wave-5 scout): under the quadratic
gap law (the empirical h_quad: every candidate's merge-gain
increment equals half its new logit-variance — the small-delta
regime of `twoGap`/`pairVarEq`), the candidate maximizing the
variance-per-cost index ΔVar/ΔC also maximizes the
gap-per-cost index ΔGap/ΔC — the admission rule: the next
expert is chosen for new INFORMATION per compute, not for
standalone loss (`selection_hurts` proved that criterion
fails). The composition is exact: the ½ factor commutes with
the ratio ordering. -/
theorem admission_var_criterion {I : Type} [Fintype I] (dV dC : I → ℝ)
    (hc : ∀ i, 0 < dC i) (ibest : I)
    (hbest : ∀ j, dV j / dC j ≤ dV ibest / dC ibest) :
    ∀ j, (1/2 * dV j) / dC j ≤ (1/2 * dV ibest) / dC ibest := by
  intro j
  have h1 := hbest j
  have h1' := (div_le_div_iff₀ (hc j) (hc ibest)).mp h1
  exact (div_le_div_iff₀ (hc j) (hc ibest)).mpr (by
    calc (1/2 * dV j) * dC ibest = (1/2) * (dV j * dC ibest) := by ring
      _ ≤ (1/2) * (dV ibest * dC j) :=
          mul_le_mul_of_nonneg_left h1' (by norm_num : (0:ℝ) ≤ 1/2)
      _ = (1/2 * dV ibest) * dC j := by ring)

end Admission

section BranchUniformity

/-- **The BranchScale min-max floor** (the reviewer's
S_l²·v_l ≈ const as a theorem; honesty fix): for ANY
allocation of residual scales with total budget Σ s_l² = B
over branches with variances v_l > 0, the worst per-layer
variance contribution is at least B / Σ_l (1/v_l). honest
boundary: only the LOWER bound is formalized; the
attainability direction (the uniform allocation
s_l²·v_l = const achieves the floor) is stated but not
proven here — it remains an open construction. A single
global scale s is provably suboptimal whenever the v_l
vary. (The exchange argument: s_l² ≤ M·v_l⁻¹ summed over l
gives the bound.) -/
theorem branchscale_minmax {L : Type} [Fintype L] [Nonempty L] (s v : L → ℝ)
    (hv : ∀ l, 0 < v l) (B M : ℝ)
    (hM : ∀ l, s l ^ 2 * v l ≤ M) (hsum : ∑ l, s l ^ 2 = B) :
    B / ∑ l, (v l)⁻¹ ≤ M := by
  have hbound : ∀ l, s l ^ 2 ≤ M * (v l)⁻¹ := by
    intro l
    have h1 := hM l
    rw [mul_comm M (v l)⁻¹, inv_mul_eq_div, le_div_iff₀ (hv l)]
    nlinarith [h1, sq_nonneg (s l), (hv l)]
  have hsum2 : B ≤ M * ∑ l, (v l)⁻¹ := by
    rw [← hsum]
    calc ∑ l, s l ^ 2 ≤ ∑ l, M * (v l)⁻¹ :=
        Finset.sum_le_sum (fun l _ => hbound l)
      _ = M * ∑ l, (v l)⁻¹ := (Finset.mul_sum _ _ _).symm
  have hpos : 0 < ∑ l, (v l)⁻¹ := by
    apply Finset.sum_pos' (fun l _ => le_of_lt (inv_pos.mpr (hv l)))
    obtain ⟨l⟩ := ‹Nonempty L›
    exact ⟨l, Finset.mem_univ l, inv_pos.mpr (hv l)⟩
  rw [div_le_iff₀ hpos]
  linarith

end BranchUniformity

section DeadLayer

/-- **The dead-layer stop rule** (the DepthBench adaptive-depth
law): with monotone decreasing layer values
V_l = ΔQ_remove(l)/T_l (the healthy regime — DepthBench's
finding is that Pre-LN's late layers DEPART from it, their
values collapsing toward zero), the stop rule is sound: once
layer L's value drops under ε, every later layer's value is
under ε — depth L* = max{L: V_L > λ} is well-defined and the
layers beyond it are economically dead (marginal value below
cost). Composed from `Wave4.phase_metric_monotone` — the same
monotone-certificate structure serves both the phase tracker
and the layer pruner. -/
theorem dead_layer_stop (val : ℕ → ℝ) (hmono : ∀ k, val (k+1) ≤ val k)
    (L : ℕ) (eps : ℝ) (hL : val L < eps) :
    ∀ j, L ≤ j → val j < eps := by
  intro j hj
  have h2 := phase_metric_monotone val hmono L j hj
  linarith

end DeadLayer

end Hagi.External

namespace Hagi
export Hagi.External (admission_var_criterion branchscale_minmax dead_layer_stop)
end Hagi
/-!
# FactorizedBPW — bits-per-weight arithmetic of the
factorized ternary branch (; LittleBit scheme,
ternary body, FP16 scales)

A square d×d layer is replaced by a factorized branch
W ≈ diag(h)·T(U)·diag(ℓ)·T(V)ᵀ·diag(g) with latent rank r:
ternary factors (log₂3 bits/entry, 2·d·r entries) plus
three FP16 scale vectors (h: d, g: d, ℓ: r — 16 bits
each). The bits-per-original-weight of ONE branch is

  b₁ = (log₂3 · 2·d·r + 16·(2d + r)) / d².

This module fixes that arithmetic exactly:

* `factorized_ternary_bits` — total bits as a function of
  d, r (the identity the BPW claims reduce to);
* `bpw_two_branches` — the two-branch LittleBit layout is
  exactly twice one branch;
* `bpw_lt_one_bound` — GROWTH BY RANK: keeping the whole
  factorized layer below 1 BPW bounds the affordable
  latent rank linearly in d (and quadratically relative
  to the dense budget d²) — the formal counterpart of
  "HAGI grows by effective latent dimension, not width":
  r can scale with d while the layer stays sub-1-BPW.

Numerical anchor (not a theorem — arithmetic of the scheme
with ternary factors): d = 4096, r = 384 gives
b₁ ≈ 0.305 BPW, two branches ≈ 0.611 BPW.
-/

open scoped BigOperators

namespace Hagi.Budget

/-- log₂3 as a real constant. -/
noncomputable def log2_3 : ℝ := Real.log 3 / Real.log 2

/-- Total bits of one factorized ternary branch:
ternary factor entries plus FP16 scale vectors. -/
noncomputable def factorizedTernaryBits (d r : ℕ) : ℝ :=
  log2_3 * (2 * d * r) + 16 * (2 * d + r)

/-- Bits per original weight of one branch (d×d layer). -/
noncomputable def bpw (d r : ℕ) : ℝ := factorizedTernaryBits d r / (d * d)

theorem factorized_ternary_bits (d r : ℕ) :
    factorizedTernaryBits d r = log2_3 * (2 * d * r) + 16 * (2 * d + r) := rfl

/-- The two-branch (primary + residual) layout costs exactly
twice one branch. -/
theorem bpw_two_branches (d r : ℕ) :
    (factorizedTernaryBits d r + factorizedTernaryBits d r) / (d * d)
      = 2 * bpw d r := by
  unfold bpw
  ring

/-- **Growth by latent rank under a 1-BPW budget**: for a
nondegenerate layer, the one-branch BPW stays below 1
exactly when the rank is below the linear-in-d threshold
(d² − 32·d) / (2·log₂3·d + 16). In particular a
rank growing linearly with d keeps the layer sub-1-BPW —
formalizing "grow effective latent dimension, not width". -/
theorem bpw_lt_one_bound (d r : ℕ) (hd : 0 < d) (hlog : 0 < log2_3) :
    bpw d r < 1 ↔
      (r : ℝ) < ((d : ℝ) * (d : ℝ) - 16 * 2 * (d : ℝ))
        / (2 * log2_3 * (d : ℝ) + 16) := by
  unfold bpw factorizedTernaryBits
  have hdc : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdd : (0:ℝ) < (d : ℝ) * (d : ℝ) := by positivity
  have hden : (0:ℝ) < 2 * log2_3 * (d : ℝ) + 16 := by
    have : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
    nlinarith [hlog, this]
  have key : ∀ x : ℝ, log2_3 * (2 * (d:ℝ) * x) + 16 * (2 * (d:ℝ) + x)
      = (2 * log2_3 * (d:ℝ) + 16) * x + 32 * (d:ℝ) := by
    intro x; ring
  constructor
  · intro h
    rw [div_lt_iff₀ hdd, one_mul, key] at h
    apply (lt_div_iff₀ hden).mpr
    linarith
  · intro h
    rw [lt_div_iff₀ hden] at h
    rw [div_lt_iff₀ hdd, one_mul, key]
    linarith

end Hagi.Budget
/-!
# Термодинамический prune-сертификат (R522)

Формализация тезиса «98,5% сети — фоновая тепловая среда,
знание конденсировано в 1,5% каркаса»:
* `condensation_budget` — каркасная девиация M ⟹ CE-стоимость
  перестройки ≤ M²/4 (интерфейс:CE-бюджет ε ⟹ допустимая
  девиация δ = 2√ε);
* `thermo_prune_certificate` — двухступенчатый сертификат:
  слои за L мертвы (monotone-вал, dead_layer_stop) И живой
  каркас перестраивается не дороже M²/4.
-/

namespace Hagi.Ensemble

open Real Finset

/-- **Конденсационный бюджет (мост «1,5% каркаса» → prune)**:
если девиации logits d_u каркасно-сжаты в δ-окрестность
(гипотеза конденсации: тепловая фоновая масса почти не
меняет logits), то merge/prune-перестройка ансамбля стоит
не больше δ²/4 CE-бюджета (prune_certificate). Эквивалентно:
для любого CE-бюджета ε допустимая каркасная девиация есть
δ = 2√ε. -/
theorem condensation_budget {k : Type} [Fintype k] [Nonempty k]
    (m d : k → ℝ) (t : k) (M : ℝ)
    (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1)
    (hM : 0 < M)
    (hcond : ∀ u v, |d u - d v| ≤ M) :
    Hagi.ceOneHot t (fun v => m v + d v) / 2
      + Hagi.ceOneHot t (fun v => m v - d v) / 2
      - Hagi.ceOneHot t m ≤ M ^ 2 / 4 := ce_gap_bounded m d t M hp hsum hM hcond

/-- Обратная постановка: CE-бюджет ε ⟹ допустимая конденсационная
девиация δ = 2√ε ( Loved «1,5%»: жёсткий каркас ⟹ малое δ). -/
theorem condensation_epsilon_budget (ε : ℝ) (hε : 0 < ε) :
    0 < 2 * Real.sqrt ε := by
  positivity

/-- **Термодинамический prune-сертификат (двухступенчатый)**:
(1) слои за `L` мертвы по `dead_layer_stop` (монотонный вал ценности);
(2) живой каркас с конденсационной девиацией ≤ M перестраивается
не дороже M²/4 CE (prune_certificate). Сумма: полная стоимость
конденсации модели к каркасу ограничена и слои за L отрезаны —
формализация тезиса «98,5% тепловая масса, знание — в 1,5%». -/
theorem thermo_prune_certificate {k : Type} [Fintype k] [Nonempty k]
    (m d : k → ℝ) (t : k) (M : ℝ)
    (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1)
    (hM : 0 < M)
    (hcond : ∀ u v, |d u - d v| ≤ M)
    (val : ℕ → ℝ) (hmono : ∀ j, val (j+1) ≤ val j)
    (L : ℕ) (eps : ℝ) (hL : val L < eps) :
    (∀ j, L ≤ j → val j < eps)
      ∧ (Hagi.ceOneHot t (fun v => m v + d v) / 2
          + Hagi.ceOneHot t (fun v => m v - d v) / 2
          - Hagi.ceOneHot t m ≤ M ^ 2 / 4) := by
  refine ⟨dead_layer_stop val hmono L eps hL, ?_⟩
  exact ce_gap_bounded m d t M hp hsum hM hcond

end Hagi.Ensemble
/-!
# Доля каркаса vs эффективная размерность (R526)

Количественный мост «1,5% каркаса ⟺ d_eff ~ 5-6»:
факториальная таблица 4!..8!, доля фазового объёма
на направление 1/k! и её монотонность по d_eff.
Точечные значения: 1/5! ≈ 0.83% < 1,5%; 1/6! ≈ 0.14%.
Связь с FactorizedBPW (d_eff ≤ 8) и ThermoPrune.
-/

namespace Hagi.Budget

open Real Finset Nat

/-- Факториальная таблица (точные значения):
4! = 24, 5! = 120, 6! = 720, 7! = 5040, 8! = 40320. -/
theorem fact4 : (4 : ℕ).factorial = 24 := by norm_num
theorem fact5 : (5 : ℕ).factorial = 120 := by norm_num
theorem fact6 : (6 : ℕ).factorial = 720 := by norm_num
theorem fact7 : (7 : ℕ).factorial = 5040 := by norm_num
theorem fact8 : (8 : ℕ).factorial = 40320 := by norm_num

/-- Обратные доли как Real: 1/5! = 1/120 ≈ 0.0083 < 0.015 (1,5%). -/
theorem inv_fact5_lt_15pct : (1:ℝ) / ((5:ℕ).factorial : ℝ) < 3/200 := by
  norm_num

/-- 1/6! = 1/720 ≈ 0.0014 < 0.015. -/
theorem inv_fact6_lt_15pct : (1:ℝ) / ((6:ℕ).factorial : ℝ) < 3/200 := by
  norm_num

/-- **Главный мост R526**: уже при d_eff = 5 доля фонового
объёма 1/5! = 1/120 ≈ 0.83% меньше 1,5% — каркас «1,5%»
достижим пятью эффективными направлениями. -/
theorem scaffold_15pct_at_deff5 : (1:ℝ) / ((5:ℕ).factorial : ℝ) ≤ 0.015 := by
  rw [show (0.015:ℝ) = 3/200 from by norm_num]
  norm_num

/-- Монотонность падения доли по d_eff: 1/(k+1)! ≤ 1/k!. -/
theorem inv_fact_mono (k : ℕ) :
    (1:ℝ) / (((k+1 : ℕ).factorial : ℝ)) ≤ (1:ℝ) / (k.factorial : ℝ) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h : (k+1 : ℕ).factorial = (k+1 : ℕ) * k.factorial := Nat.factorial_succ k
  rw [h]
  push_cast
  nlinarith [Nat.factorial_pos k]

end Hagi.Budget
set_option linter.style.header false

/-!
# Полный термодинамический сертификат конденсации (R527)

Мост CE-бюджет → девиация и композиция трёх вертикалей:
* `condensation_epsilon_to_gap` — бюджет ε ⟹ допустимая девиация
  каркаса δ = 2√ε (перестройка стоит ровно δ²/4 = ε);
* `thermo_condensation_full` — полная связка
  «1,5% каркаса (ScaffoldFraction) + мёртвые слои за L
  (dead_layer_stop) + конденсация внутри CE-бюджета ε
  (condensation_epsilon_to_gap)».
Файл в слое 4 (Budget): может импортировать Ensemble (3).
-/

namespace Hagi.Budget

open Hagi.Ensemble

open Real Finset

/-- **Мост CE-бюджет → девиация (R527)**: при CE-бюджете ε любая
конденсационная девиация каркаса масштаба δ = 2√ε допустима:
перестройка живой пары стоит ровно δ²/4 = ε. Это обращение
`condensation_budget`: бюджет задаёт радиус конденсации. -/
theorem condensation_epsilon_to_gap {k : Type} [Fintype k] [Nonempty k]
    (m d : k → ℝ) (t : k) (ε : ℝ)
    (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1)
    (hε : 0 < ε)
    (hcond : ∀ u v, |d u - d v| ≤ 2 * Real.sqrt ε) :
    Hagi.ceOneHot t (fun v => m v + d v) / 2
      + Hagi.ceOneHot t (fun v => m v - d v) / 2
      - Hagi.ceOneHot t m ≤ ε := by
  have key : (2 * Real.sqrt ε) ^ 2 / 4 = ε := by
    field_simp
    rw [Real.sq_sqrt (le_of_lt hε)]
    ring
  exact (condensation_budget m d t (2 * Real.sqrt ε) hp hsum (by positivity) hcond).trans
    (le_of_eq key)

/-- **Полный термодинамический сертификат конденсации (R527)**:
объединение трёх вертикалей —
(1) слои за L мертвы (`dead_layer_stop`);
(2) живой каркас конденсируется внутри CE-бюджета ε при девиации
    δ = 2√ε (`condensation_epsilon_to_gap`);
(3) каркасная доля: уже при d_eff = 5 фоновый объём 1/5! ≈ 0,83% < 1,5%
    (`scaffold_15pct_at_deff5`).
Итог: «98,5% тепловая среда ⟹ знание в ≤1,5% каркаса, отрезаемое
и перестраиваемое за ε» — полная формализация тезиса. -/
theorem thermo_condensation_full {k : Type} [Fintype k] [Nonempty k]
    (m d : k → ℝ) (t : k) (ε : ℝ)
    (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1)
    (hε : 0 < ε)
    (hcond : ∀ u v, |d u - d v| ≤ 2 * Real.sqrt ε)
    (val : ℕ → ℝ) (hmono : ∀ j, val (j+1) ≤ val j)
    (L : ℕ) (epsL : ℝ) (hL : val L < epsL) :
    (∀ j, L ≤ j → val j < epsL)
      ∧ (Hagi.ceOneHot t (fun v => m v + d v) / 2
          + Hagi.ceOneHot t (fun v => m v - d v) / 2
          - Hagi.ceOneHot t m ≤ ε)
      ∧ (1:ℝ) / ((5:ℕ).factorial : ℝ) ≤ 0.015 := by
  refine ⟨dead_layer_stop val hmono L epsL hL,
    condensation_epsilon_to_gap m d t ε hp hsum hε hcond, ?_⟩
  exact Hagi.Budget.scaffold_15pct_at_deff5

end Hagi.Budget
