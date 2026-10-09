/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# MacroCycleV2 — mathematical kernels for engineering upgrades

* Variance gating: the logit range scales linearly under
  temperature division (`logitRange_scale`), so the `R²/8`
  bound contracts quadratically (`variance_gate_contract`)
  and an overshoot `R ≥ R̄` is repaired exactly by
  `τ = R/R̄` (`variance_gate_normalize`).
* Trust region: for `‖x‖ ≥ R > 0`, the rescaled step
  `(R/‖x‖) • x` has norm exactly `R`
  (`trust_region_proj_norm`) and is the nearest point of the
  R-ball to `x` (`trust_region_nearest`).
* Dynamic routing: with per-branch scale `1/√(2L)`, the
  total injected variance is `v/2`, independent of the path
  depth (`dynamic_branch_variance`).
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

/-- For `tau > 0`:
`logitRange (fun v => f v / tau) = logitRange f / tau`. -/
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

/-- For `tau ≥ 1`:
`(logitRange (· / tau)) ^ 2 / 8 ≤ (logitRange f) ^ 2 / 8`. -/
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

/-- If `0 < Rbar ≤ logitRange f`, then `τ := logitRange f / Rbar`
satisfies `1 ≤ τ` and
`logitRange (fun v => f v / τ) = Rbar`. -/
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

/-- If `0 < R ≤ ‖x‖` then `‖(R / ‖x‖) • x‖ = R`. -/
theorem trust_region_proj_norm (x : E) {R : ℝ} (hR : 0 < R) (hxR : R ≤ ‖x‖) :
    ‖(R / ‖x‖) • x‖ = R := by
  have hx0 : (0:ℝ) < ‖x‖ := lt_of_lt_of_le hR hxR
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    div_mul_cancel₀ _ (ne_of_gt hx0)]

/-- If `0 < R ≤ ‖x‖` and `‖y‖ ≤ R`, then
`‖x − (R/‖x‖) • x‖ ≤ ‖x − y‖`: the rescaled step is the
nearest point of the closed R-ball to `x`. -/
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

/-- For `0 < L` and `0 ≤ v`:
`∑ _l < L, ((√(2L))⁻¹)² * v = v / 2`, independent of the
path depth `L`. -/
theorem dynamic_branch_variance (L : ℕ) (v : ℝ)
    (hL : 0 < L) (hv : 0 ≤ v) :
    (∑ _l ∈ Finset.range L, ((Real.sqrt (2 * (L : ℝ))) ⁻¹) ^ 2 * v) = v / 2 := by
  have hpos : 0 < 2 * (L : ℝ) := by positivity
  have hsq : ((Real.sqrt (2 * (L : ℝ))) ⁻¹) ^ 2 = (2 * (L : ℝ)) ⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (le_of_lt hpos)]
  rw [hsq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

end Hagi.Unified
