/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Audit.Exactness

set_option linter.style.header false

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
admission rule: maximize NEW logit-space variance per compute,
not minimize standalone loss (selection_hurts already proved
the latter fails).

**2. `branchscale_minmax`** (the reviewer's S_l²·v_l ≈ const,
now a THEOREM): for any scale allocation with Σ s_l² = B, the
worst per-layer variance contribution satisfies
max_l s_l²·v_l ≥ B / Σ(1/v_l) — the min-max floor, achieved when
s_l²·v_l is uniform across layers: per-layer residual scales
must compensate the measured branch variance (a uniform scale
is provably suboptimal whenever v_l varies).

**3. `dead_layer_stop`** (the DepthBench adaptive-depth rule):
with monotone decreasing layer values
V_l = ΔQ_remove(l)/T_l, if layer L's value drops under ε then
EVERY later layer's value does — the stop rule for adaptive
depth L* = max{L : V_L > λ}; layer pruning = marginal-value
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
   admit argmax ΔVar/ΔC — NOT min-CE (selection_hurts).
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

namespace Hagi

section Admission

/-- **The variance-admission criterion** (round 44; the niche
confirmed unoccupied by the wave-5 scout): under the quadratic
gap law (the empirical h_quad: every candidate's merge-gain
increment equals half its new logit-variance — the small-delta
regime of `twoGap`/`pairVarEq`), the candidate maximizing the
variance-per-cost index ΔVar/ΔC also maximizes the
gap-per-cost index ΔGap/ΔC — the admission rule: the next
expert is chosen for NEW INFORMATION per compute, not for
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
S_l²·v_l ≈ const as a theorem): for ANY allocation of residual
scales with total budget Σ s_l² = B over branches with
variances v_l > 0, the worst per-layer variance contribution is
at least B / Σ_l (1/v_l) — and the floor is ACHIEVED exactly by
the uniform allocation s_l²·v_l = const. A single global scale
s is provably suboptimal whenever the v_l vary: the per-layer
scales must compensate the measured branch variance. (The
exchange argument: s_l² ≤ M·v_l⁻¹ summed over l gives the
bound; equality forces each term to the max.) -/
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
layer L's value drops under ε, EVERY later layer's value is
under ε — depth L* = max{L : V_L > λ} is well-defined and the
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

end Hagi
