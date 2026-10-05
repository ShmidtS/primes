/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# MacroCycleV2: the engineering upgrades, licensed by kernels (R175)

The MacroCycle v2.0 proposal (2026-10-05): five engineering
upgrades that bridge the Lean corpus to GPU practice. This
module formalizes the MATHEMATICAL KERNELS that license each
upgrade; the runtime engineering itself lives in E:\HAGI_v2
and carries no Lean claim here.

* **Variance-gated merging (`SmartMerge`)** —
  `logitRange_scale` + `variance_gate_contract`: the logit
  range of an expert scales LINEARLY under temperature
  division (`R(d/τ) = R(d)/τ`), so the PoE second-order bound
  `R²/8` contracts QUADRATICLY: a range overshoot `R > R̄` is
  repaired exactly to `R̄²/8` by `τ = R/R̄`. The hybrid
  linear/geometric split inherits both the proven linear
  bound (in-range experts) and exactness (out-of-range
  experts pooled geometrically) — no new math needed.

* **Trust-region safety (`FastSafeStep`)** —
  `trust_region_proj_norm` + `trust_region_nearest`: for an
  AdamW step `x` overshooting the safety radius `R`, the
  rescaled step `(R/‖x‖)•x` has norm EXACTLY `R` and is the
  NEAREST point of the safety ball to `x` (the metric
  projection onto the ball — reverse triangle inequality, no
  QP). Replacing the exact SafeQP solve by this scaling for
  the 99% non-critical weights LOSES NOTHING relative to the
  ball-constraint semantics; the 1% critical-weight QP split
  is an engineering heuristic with no formal claim.

* **Dynamic routing scale (`DynamicRoutingScale`)** —
  `dynamic_branch_variance`: with per-branch scale
  `s = 1/√(2·L_eff)`, the TOTAL variance injected over the
  token's effective path is `v/2` INDEPENDENT of `L_eff` —
  the BranchScale variance recursion stays O(1) on short and
  long paths alike. No gradient-clipping folklore needed.

**Honest boundary (what is NOT claimed).** The FreeEnergy
loss upgrade reuses the existing variational core
(`Hagi.Energy.Variational.gibbs_variational`:
the minimizer of `F[q] = E_q[U] − τH(q)` is the tilted
measure, existence/uniqueness included) — the
anti-hallucination READING is runtime interpretation, not a
theorem here. The heterogeneous quantization budget
(`HeteroQuant`) is additivity of the per-layer bounds — the
already-proven telescopic budgets (R143/R155 style) — plus a
knapsack choice with no closed-form theorem claimed. Numbers
like "1% weights", "10× memory", "99% abilities" are
engineering targets, not Lean content.
-/

namespace Hagi.Unified

open Finset Real

/-! ## 1. Variance-gated merging: temperature contracts R²/8 -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- The canonical nonemptiness proof for `Finset.univ`:
a FIXED proof term, so `sup'` expressions across the module
share syntax (essential for `linarith`). -/
theorem univNE : (Finset.univ : Finset V).Nonempty :=
  Finset.univ_nonempty_iff.mpr ‹_›

/-- The logit range functional: sup − inf of a real logit
map over the (finite) token support, written as sup + sup(−·)
to stay inside `Finset.sup'`. -/
def logitRange (f : V → ℝ) : ℝ :=
  Finset.sup' Finset.univ univNE f + Finset.sup' Finset.univ univNE (fun v => -f v)

theorem sup_div (f : V → ℝ) {tau : ℝ} (htau : 0 < tau) :
    Finset.sup' Finset.univ univNE (fun v => f v / tau)
      = Finset.sup' Finset.univ univNE f / tau := by
  apply le_antisymm
  · refine (Finset.sup'_le_iff univNE _).mpr fun v _ => ?_
    have hle := Finset.le_sup' f (Finset.mem_univ v)
    exact div_le_div_of_nonneg_right hle htau.le
  · rw [div_le_iff₀ htau]
    refine (Finset.sup'_le_iff univNE _).mpr fun v _ => ?_
    have hle' : f v / tau ≤ Finset.sup' Finset.univ univNE
        (fun v => f v / tau) :=
      Finset.le_sup' (fun v => f v / tau) (Finset.mem_univ v)
    have h1 : f v ≤ tau * Finset.sup' Finset.univ univNE (fun v => f v / tau) :=
      calc f v = tau * (f v / tau) := by field_simp
        _ ≤ tau * Finset.sup' Finset.univ univNE (fun v => f v / tau) :=
            mul_le_mul_of_nonneg_left hle' htau.le
    calc f v ≤ tau * Finset.sup' Finset.univ univNE (fun v => f v / tau) := h1
      _ = Finset.sup' Finset.univ univNE (fun v => f v / tau) * tau := by ring

/-- **The range scales linearly under temperature division**:
`R(d/τ) = R(d)/τ` for `τ > 0` — temperature scaling of an
overconfident expert shrinks its logit range exactly by the
temperature factor. -/
theorem logitRange_scale (f : V → ℝ) {tau : ℝ} (htau : 0 < tau) :
    logitRange (fun v => f v / tau) = logitRange f / tau := by
  have hneg : Finset.sup' Finset.univ univNE (fun v => -(f v / tau))
      = Finset.sup' Finset.univ univNE (fun v => -f v) / tau := by
    apply le_antisymm
    · refine (Finset.sup'_le_iff univNE _).mpr fun v _ => ?_
      have hle := Finset.le_sup' (fun v => -f v) (Finset.mem_univ v)
      have hre : -(f v / tau) = (-f v) / tau := by ring
      rw [hre]
      exact div_le_div_of_nonneg_right hle htau.le
    · rw [div_le_iff₀ htau]
      refine (Finset.sup'_le_iff univNE _).mpr fun v _ => ?_
      have hle' : -(f v / tau) ≤ Finset.sup' Finset.univ univNE
          (fun v => -(f v / tau)) :=
        Finset.le_sup' (fun v => -(f v / tau)) (Finset.mem_univ v)
      have h1 : -f v ≤ tau * Finset.sup' Finset.univ univNE
          (fun v => -(f v / tau)) :=
        calc -f v = tau * (-(f v / tau)) := by field_simp
          _ ≤ tau * Finset.sup' Finset.univ univNE (fun v => -(f v / tau)) :=
              mul_le_mul_of_nonneg_left hle' htau.le
      calc -f v ≤ tau * Finset.sup' Finset.univ univNE (fun v => -(f v / tau)) := h1
        _ = Finset.sup' Finset.univ univNE (fun v => -(f v / tau)) * tau := by ring
  rw [logitRange, logitRange, sup_div f htau, hneg]
  ring

/-- **The variance gate contracts the PoE bound
quadratically**: with the second-order PoE slack `R²/8` in
the expert's range, temperature division by `τ ≥ 1` shrinks
the bound by the factor `1/τ²`. -/
theorem variance_gate_contract (f : V → ℝ) {tau : ℝ}
    (htau : 1 ≤ tau) :
    (logitRange (fun v => f v / tau)) ^ 2 / 8
      ≤ (logitRange f) ^ 2 / 8 := by
  have htau0 : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  obtain ⟨v0⟩ := ‹Nonempty V›
  have hR : 0 ≤ logitRange f := by
    have h1 : f v0 ≤ Finset.sup' Finset.univ univNE f :=
      Finset.le_sup' f (Finset.mem_univ v0)
    have h2 : -f v0 ≤ Finset.sup' Finset.univ univNE (fun v => -f v) :=
      Finset.le_sup' (fun v => -f v) (Finset.mem_univ v0)
    unfold logitRange
    have hzero : (0:ℝ) = f v0 + -f v0 := by ring
    rw [hzero]
    exact add_le_add h1 h2
  rw [logitRange_scale f htau0, div_pow]
  have htau2 : (1:ℝ) ≤ tau ^ 2 := by nlinarith [htau]
  have hsq : (logitRange f) ^ 2 / tau ^ 2 ≤ (logitRange f) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < tau ^ 2)]
    nlinarith [htau2, sq_nonneg (logitRange f)]
  have h8 : (0:ℝ) < 8 := by norm_num
  exact (div_le_div_iff_of_pos_right h8).mpr hsq

/-- **The variance gate normalizes an overshoot exactly**: an
expert whose range `R` overshoots the certified admission
threshold `R̄` is repaired by `τ = R/R̄`: its range becomes
exactly `R̄` and its PoE slack exactly `R̄²/8` — the boundary
of the certified merge admission. -/
theorem variance_gate_normalize (f : V → ℝ) {Rbar : ℝ}
    (hRbar : 0 < Rbar) (hover : Rbar ≤ logitRange f) :
    1 ≤ logitRange f / Rbar ∧
      logitRange (fun v => f v / (logitRange f / Rbar)) = Rbar := by
  have hRpos : 0 < logitRange f := lt_of_lt_of_le hRbar hover
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hRbar]
    linarith
  · rw [logitRange_scale f (div_pos hRpos hRbar)]
    rw [div_div_eq_mul_div]
    field_simp


/-! ## 2. Trust-region safety: ball projection replaces the QP -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The rescaled step has norm exactly the safety radius**:
for an AdamW step `x` overshooting the safety ball (`‖x‖ ≥
R > 0`), the trust-region scaling `(R/‖x‖) • x` lands EXACTLY
on the boundary of the ball. -/
theorem trust_region_proj_norm (x : E) {R : ℝ} (hR : 0 < R) (hxR : R ≤ ‖x‖) :
    ‖(R / ‖x‖) • x‖ = R := by
  have hx0 : (0:ℝ) < ‖x‖ := lt_of_lt_of_le hR hxR
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    div_mul_cancel₀ _ (ne_of_gt hx0)]

/-- **The ball projection is the NEAREST safe point**: for
any step `x` outside the safety ball and ANY safe direction
`y` (‖y‖ ≤ R), the rescaled step `(R/‖x‖)•x` is at least as
close to `x` as `y`. Replacing the exact SafeQP solve on the
non-critical weights by this one-line scaling LOSES NOTHING
relative to the ball-constraint semantics — the projection
IS the metric projection onto the ball (reverse triangle
inequality; no QP solver, no inner products). -/
theorem trust_region_nearest (x y : E) {R : ℝ} (hR : 0 < R)
    (hxR : R ≤ ‖x‖) (hy : ‖y‖ ≤ R) :
    ‖x - (R / ‖x‖) • x‖ ≤ ‖x - y‖ := by
  have hx0 : (0:ℝ) < ‖x‖ := lt_of_lt_of_le hR hxR
  -- the projection distance is exactly ‖x‖ - R
  have hcoef : (1:ℝ) - R / ‖x‖ = (‖x‖ - R) / ‖x‖ := by
    field_simp
  have hsplit : x - (R / ‖x‖) • x = ((‖x‖ - R) / ‖x‖) • x := by
    have e1 : ((‖x‖ - R)/‖x‖) • x = (‖x‖/‖x‖ - R/‖x‖) • x := by
      congr 1
      field_simp
    have e2 : (‖x‖/‖x‖ - R/‖x‖) • x = (1 - R/‖x‖) • x := by
      congr 1
      field_simp
    have e3 : x - (R/‖x‖) • x = (1 - R/‖x‖) • x := by
      nth_rewrite 1 [show x = (1:ℝ) • x from (one_smul ℝ x).symm]
      rw [sub_smul]
    rw [e3, ← e2, ← e1]
  have hc : (0:ℝ) ≤ (‖x‖ - R) / ‖x‖ := by
    apply div_nonneg <;> linarith
  have hdist : ‖x - (R / ‖x‖) • x‖ = ‖x‖ - R := by
    rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
      div_mul_cancel₀ _ (ne_of_gt hx0)]
  -- the reverse triangle inequality finishes
  rw [hdist]
  have hrev := norm_sub_norm_le x y
  have hle : ‖x‖ - ‖y‖ ≥ ‖x‖ - R := by
    have : ‖y‖ ≤ R := hy
    linarith
  linarith

/-! ## 3. Dynamic routing scale: path-invariant variance -/

/-- **The dynamic-branch scale makes the injected variance
path-invariant**: with per-branch scale `s = 1/√(2·L_eff)`,
the total variance injected over the token's effective path
of depth `L_eff` is `v/2` — INDEPENDENT of `L_eff`. Early
exit and short paths keep exactly the same O(1) variance
recursion as the full-depth path; no clipping folklore. -/
theorem dynamic_branch_variance (L : ℕ) (v : ℝ)
    (hL : 0 < L) (hv : 0 ≤ v) :
    (∑ _l ∈ Finset.range L, ((Real.sqrt (2 * (L : ℝ))) ⁻¹) ^ 2 * v) = v / 2 := by
  have hpos : 0 < 2 * (L : ℝ) := by positivity
  have hsq : ((Real.sqrt (2 * (L : ℝ))) ⁻¹) ^ 2 = (2 * (L : ℝ)) ⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (le_of_lt hpos)]
  rw [hsq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

end Hagi.Unified
