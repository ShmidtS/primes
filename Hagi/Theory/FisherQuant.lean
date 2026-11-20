/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
-/
import Hagi.Budget.WeightedExpAlloc
import Mathlib.Tactic

set_option linter.style.header false

/-!
# FisherQuant — curvature-based quantization bounds (C472, audit P2/G3)

The existing quantization bridges are first-order and dimension-blind:
`compressed_safe_step` (C389) pays `2·L_lip·ε_q` per step (linear in the
error budget), and `quant_loss_bridge_derived` (C426) pays
`2·D·√(m·n)·‖x‖` (isotropic uniform rounding D, growing with √(V·n)).
This module adds the second-order, per-coordinate counterpart:

* `quadLoss_second_order` — the EXACT second-order expansion of the
  least-squares loss (coordinate twin of
  `Hagi.System.DerivedState.energyOf_quad_ident`, C428): no inequality,
  the residual algebra of a fixed dataset;
* `hess_le_colCurv` — the honest per-coordinate (Gershgorin) curvature
  domination `δᵀ(AᵀA)δ ≤ Σ_j c_j δ_j²` with `c_j = Σ_k |⟨col j, col k⟩|`
  (the naive diagonal `H_jj` claim is FALSE — off-diagonal mass is
  honestly priced in);
* `fisher_quant_loss_bound` — the abstract bound: with a
  coordinatewise curvature premise (the Fisher/empirical premise
  class) and per-coordinate quantization `|δ_j| ≤ ε_j`, the loss
  increment is `Σ|g_j|ε_j + ½Σ c_j ε_j²` — QUADRATIC, not linear, in
  the error; at a stationary point (`g = 0`) purely `½Σ c_j ε_j²`;
* `quadLoss_curv_le` — the curvature premise is DERIVED (discharged)
  for the quadratic carrier;
* `fisher_beats_lipschitz` / `fisher_tolerance_mono` — the anisotropy
  comparison: under the per-coordinate tolerance `ε_j ≤ 2L/c_j` the
  curvature penalty beats the Lipschitz transport `L·Σε_j`; flat
  coordinates (small `c`) tolerate a `c_max/c_min` factor more error
  (in squared-energy space: √). Isotropic `c` gives NO gain;
* `fisher_alloc_mono` — the BRIDGE to `Hagi.Budget.weightedExpAllocation`
  (`weightedExpAllocation_optimal`, C428 cycle): the closed-form
  optimal allocation is MONOTONE in the Fisher weight — coordinates
  with larger curvature receive MORE bits; `fisher_alloc_isotropic_uniform`
  pins the isotropic case (uniform allocation, no gain).

## Honest pins

* The general-loss bound keeps the first-order term `Σ|g_j|ε_j`; the
  pure quadratic form holds only at a stationary point (`g = 0`).
* Exactness claims attach to the identity `quadLoss_second_order`
  (full Hessian); the diagonal bound `hess_le_colCurv` is an
  inequality by construction (Gershgorin).
* The `√(c_max/c_min)` anisotropy factor is a docstring reading of
  `fisher_tolerance_mono` (tolerance ratio `c_max/c_min` in
  ε-space), not a separate formal theorem (KISS down-scope).
* Bit allocation: optimality itself is consumed from
  `weightedExpAllocation_optimal`, not restated (STMDUP hygiene);
  the monotonicity bridge is the new formal content.
-/

namespace Hagi.Theory.FisherQuant

open Finset Real
open scoped BigOperators

variable {d : ℕ} {I : Type} [Fintype I]

variable {d : ℕ} {I : Type} [Fintype I]

/-! ## Quadratic carrier: exact second-order identity (C428 pattern) -/

/-- Least-squares loss on a fixed dataset, coordinate form:
`quadLoss a y θ = Σᵢ (⟪a i, θ⟫ − y i)²/2`. -/
noncomputable def quadLoss (a : I → Fin d → ℝ) (y : I → ℝ) (θ : Fin d → ℝ) : ℝ :=
  ∑ i, (∑ j, a i j * θ j - y i) ^ 2 / 2

/-- Gradient of `quadLoss` at `θ`, coordinate `j`. -/
def quadGrad (a : I → Fin d → ℝ) (y : I → ℝ) (θ : Fin d → ℝ) (j : Fin d) : ℝ :=
  ∑ i, (∑ l, a i l * θ l - y i) * a i j

/-- Cross curvature: the Hessian entry `(AᵀA)_{jk} = ⟨col j, col k⟩`
of the quadratic carrier. -/
def crossCurv (a : I → Fin d → ℝ) (j k : Fin d) : ℝ := ∑ i, a i j * a i k

/-- Gershgorin diagonal curvature `c_j = Σ_k |H_{jk}| ≥ 0`: the
honest per-coordinate curvature bound (the naive diagonal `H_{jj}`
does NOT dominate the quadratic form — off-diagonal mass is priced
in here). -/
def colCurv (a : I → Fin d → ℝ) (j : Fin d) : ℝ := ∑ _k, |crossCurv a j _k|

/-- Symmetry of the cross curvature (Hessian of the quadratic). -/
theorem crossCurv_symm (a : I → Fin d → ℝ) (j k : Fin d) :
    crossCurv a j k = crossCurv a k j := by
  unfold crossCurv
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The Gershgorin curvature is nonnegative. -/
theorem colCurv_nonneg (a : I → Fin d → ℝ) (j : Fin d) : 0 ≤ colCurv a j :=
  Finset.sum_nonneg fun k _ => abs_nonneg (crossCurv a j k)

/-- The EXACT second-order expansion of the quadratic loss: no
inequality, no measurement — coordinate twin of
`Hagi.System.DerivedState.energyOf_quad_ident`. -/
theorem quadLoss_second_order (a : I → Fin d → ℝ) (y : I → ℝ)
    (θ δ : Fin d → ℝ) :
    quadLoss a y (θ + δ) = quadLoss a y θ
      + ∑ j, quadGrad a y θ j * δ j
      + ∑ j, ∑ k, crossCurv a j k * δ j * δ k / 2 := by
  have hsplit : ∀ i : I, ∑ j, a i j * (θ j + δ j)
      = ∑ j, a i j * θ j + ∑ j, a i j * δ j := by
    intro i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => mul_add _ _ _
  have hper : ∀ i : I,
      (∑ j, a i j * (θ j + δ j) - y i) ^ 2 / 2
        = (∑ j, a i j * θ j - y i) ^ 2 / 2
          + ∑ j, (∑ l, a i l * θ l - y i) * a i j * δ j
          + ∑ j, ∑ k, a i j * a i k * δ j * δ k / 2 := by
    intro i
    have h1 : (∑ j, a i j * θ j - y i) * ∑ j, a i j * δ j
        = ∑ j, (∑ l, a i l * θ l - y i) * a i j * δ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : (∑ j, a i j * δ j) ^ 2
        = ∑ j, ∑ k, a i j * a i k * δ j * δ k := by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => by ring
    have key : (∑ j, a i j * θ j + ∑ j, a i j * δ j - y i) ^ 2 / 2
        = (∑ j, a i j * θ j - y i) ^ 2 / 2
          + (∑ j, a i j * θ j - y i) * ∑ j, a i j * δ j
          + (∑ j, a i j * δ j) ^ 2 / 2 := by ring
    rw [hsplit i, key, h1, h2]
    rw [Finset.sum_div]
    simp only [Finset.sum_div]
  have hB : ∑ i, ∑ j, (∑ l, a i l * θ l - y i) * a i j * δ j
      = ∑ j, ∑ i, (∑ l, a i l * θ l - y i) * a i j * δ j := Finset.sum_comm
  have hC : ∑ i, ∑ j, ∑ k, a i j * a i k * δ j * δ k / 2
      = ∑ j, ∑ k, ∑ i, a i j * a i k * δ j * δ k / 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  unfold quadLoss quadGrad crossCurv
  simp only [Pi.add_apply]
  rw [Finset.sum_congr rfl fun i _ => hper i]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hB' : ∑ i, ∑ j, (∑ l, a i l * θ l - y i) * a i j * δ j
      = ∑ j, (∑ i, (∑ l, a i l * θ l - y i) * a i j) * δ j := by
    rw [hB]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hm : (∑ i, (∑ l, a i l * θ l - y i) * a i j) * δ j
        = ∑ i, (∑ l, a i l * θ l - y i) * a i j * δ j := by
      rw [Finset.sum_mul]
    exact hm.symm
  have hC' : ∑ i, ∑ j, ∑ k, a i j * a i k * δ j * δ k / 2
      = ∑ j, ∑ k, (∑ i, a i j * a i k) * δ j * δ k / 2 := by
    rw [hC]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    have hm : (∑ i, a i j * a i k) * δ j * δ k / 2
        = ∑ i, a i j * a i k * δ j * δ k / 2 := by
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
    exact hm.symm
  linarith


/-! ## Diagonal curvature domination (Gershgorin form) -/

/-- The Hessian quadratic form is dominated by the Gershgorin diagonal:
δᵀ(AᵀA)δ ≤ Σ_j c_j δ_j² with c_j = Σ_k |⟨col j, col k⟩|, via
2|x·y| ≤ x²+y² and symmetry of the Hessian. -/
theorem hess_le_colCurv (a : I → Fin d → ℝ) (δ : Fin d → ℝ) :
    ∑ j, ∑ k, crossCurv a j k * δ j * δ k
      ≤ ∑ j, colCurv a j * δ j ^ 2 := by
  have hsymm : ∀ j k : Fin d, |crossCurv a j k| = |crossCurv a k j| :=
    fun j k => by rw [crossCurv_symm]
  have h1 : ∀ j k : Fin d, crossCurv a j k * δ j * δ k
      ≤ |crossCurv a j k| * |δ j| * |δ k| := by
    intro j k
    have h := le_abs_self (crossCurv a j k * δ j * δ k)
    rw [abs_mul, abs_mul] at h
    exact h
  have h2 : ∀ j k : Fin d, |crossCurv a j k| * |δ j| * |δ k|
      ≤ |crossCurv a j k| * (δ j ^ 2 + δ k ^ 2) / 2 := by
    intro j k
    have hsq : 2 * (|δ j| * |δ k|) ≤ δ j ^ 2 + δ k ^ 2 := by
      have hnn : 0 ≤ |δ j| * |δ k| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      nlinarith [sq_nonneg (|δ j| - |δ k|), sq_abs (δ j), sq_abs (δ k)]
    have hnn : 0 ≤ |crossCurv a j k| := abs_nonneg _
    nlinarith
  have hper2 : ∀ j : Fin d,
      ∑ k, |crossCurv a j k| * (δ j ^ 2 + δ k ^ 2) / 2
        = ∑ k, |crossCurv a j k| * δ j ^ 2 / 2
          + ∑ k, |crossCurv a j k| * δ k ^ 2 / 2 := by
    intro j
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hA : ∑ j, ∑ k, |crossCurv a j k| * (δ j ^ 2 + δ k ^ 2) / 2
      = ∑ j, ∑ k, |crossCurv a j k| * δ j ^ 2 / 2
        + ∑ j, ∑ k, |crossCurv a j k| * δ k ^ 2 / 2 := by
    rw [Finset.sum_congr rfl fun j _ => hper2 j, Finset.sum_add_distrib]
  have hB : ∑ j, ∑ k, |crossCurv a j k| * δ k ^ 2 / 2
      = ∑ j, ∑ k, |crossCurv a j k| * δ j ^ 2 / 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun j _ => by rw [hsymm k j]
  have hC : ∑ j, ∑ k, |crossCurv a j k| * δ j ^ 2 / 2
      = ∑ j, colCurv a j * δ j ^ 2 / 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold colCurv
    rw [Finset.sum_mul, Finset.sum_div]
  calc ∑ j, ∑ k, crossCurv a j k * δ j * δ k
      ≤ ∑ j, ∑ k, |crossCurv a j k| * |δ j| * |δ k| :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h1 j k
    _ ≤ ∑ j, ∑ k, |crossCurv a j k| * (δ j ^ 2 + δ k ^ 2) / 2 :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h2 j k
    _ = ∑ j, ∑ k, |crossCurv a j k| * δ j ^ 2 / 2
          + ∑ j, ∑ k, |crossCurv a j k| * δ k ^ 2 / 2 := hA
    _ = ∑ j, ∑ k, |crossCurv a j k| * δ j ^ 2 / 2
          + ∑ j, ∑ k, |crossCurv a j k| * δ j ^ 2 / 2 := by rw [hB]
    _ = ∑ j, colCurv a j * δ j ^ 2 / 2
          + ∑ j, colCurv a j * δ j ^ 2 / 2 := by rw [hC]
    _ = ∑ j, (colCurv a j * δ j ^ 2 / 2 + colCurv a j * δ j ^ 2 / 2) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ j, colCurv a j * δ j ^ 2 :=
        Finset.sum_congr rfl fun j _ => by ring

/-! ## The abstract Fisher quantization bound (general loss) -/

/-- MAIN (general loss): if the loss has coordinatewise-bounded second
order curvature (premise `hcurv`, the honest generalization of the
Fisher/empirical premise class) and quantization is per-coordinate
(|δ_j| ≤ ε_j), then the loss increment is bounded by the FIRST-order
transport plus the CURVATURE penalty ½Σ c_j ε_j² — quadratic, not
linear, in the quantization error. -/
theorem fisher_quant_loss_bound (L : (Fin d → ℝ) → ℝ) (θ0 δ0 : Fin d → ℝ)
    (g c ε : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hcurv : ∀ e : Fin d → ℝ,
      L (θ0 + e) ≤ L θ0 + ∑ j, g j * e j + ∑ j, c j * e j ^ 2 / 2)
    (hε : ∀ j, |δ0 j| ≤ ε j) :
    L (θ0 + δ0) - L θ0
      ≤ ∑ j, |g j| * ε j + ∑ j, c j * ε j ^ 2 / 2 := by
  have h := hcurv δ0
  have hg : ∑ j, g j * δ0 j ≤ ∑ j, |g j| * ε j := by
    refine le_trans (Finset.sum_le_sum fun j _ => le_abs_self _) ?_
    exact Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hε j) (abs_nonneg _)
  have hq : ∑ j, c j * δ0 j ^ 2 / 2 ≤ ∑ j, c j * ε j ^ 2 / 2 := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hsq : δ0 j ^ 2 ≤ ε j ^ 2 :=
      (sq_le_sq.mpr (le_trans (hε j) (le_abs_self (ε j))))
    nlinarith [hc j, hsq]
  linarith

/-- The pure curvature form: at a stationary point (g = 0) the
quantization price is ONLY the second-order term. -/
theorem fisher_quant_loss_bound_opt (L : (Fin d → ℝ) → ℝ) (θ0 δ0 : Fin d → ℝ)
    (g c ε : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hcurv : ∀ e : Fin d → ℝ,
      L (θ0 + e) ≤ L θ0 + ∑ j, g j * e j + ∑ j, c j * e j ^ 2 / 2)
    (hg : ∀ j, g j = 0) (hε : ∀ j, |δ0 j| ≤ ε j) :
    L (θ0 + δ0) - L θ0 ≤ ∑ j, c j * ε j ^ 2 / 2 := by
  have h := fisher_quant_loss_bound L θ0 δ0 g c ε hc hcurv hε
  have hz : ∑ j, |g j| * ε j = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hg j, abs_zero, zero_mul]
  linarith

/-! ## Quadratic instantiation: premise DISCHARGED -/

/-- The curvature premise is DERIVED (not assumed) for the quadratic
loss: exact identity + Gershgorin domination. -/
theorem quadLoss_curv_le (a : I → Fin d → ℝ) (y : I → ℝ)
    (θ e : Fin d → ℝ) :
    quadLoss a y (θ + e) ≤ quadLoss a y θ
      + ∑ j, quadGrad a y θ j * e j
      + ∑ j, colCurv a j * e j ^ 2 / 2 := by
  have hident := quadLoss_second_order a y θ e
  have hdom := hess_le_colCurv a e
  have hhalfL : ∑ j, ∑ k, crossCurv a j k * e j * e k / 2
      = (∑ j, ∑ k, crossCurv a j k * e j * e k) / 2 := by
    rw [Finset.sum_div]
    simp only [Finset.sum_div]
  have hhalfR : ∑ j, colCurv a j * e j ^ 2 / 2
      = (∑ j, colCurv a j * e j ^ 2) / 2 := by
    rw [Finset.sum_div]
  have hdiv : (∑ j, ∑ k, crossCurv a j k * e j * e k) / 2
      ≤ (∑ j, colCurv a j * e j ^ 2) / 2 := by
    exact div_le_div_of_nonneg_right hdom (by norm_num)
  linarith

/-- The quadratic Fisher quantization bridge: quantizing the weights of
the least-squares loss with per-coordinate error ε costs at most the
first-order transport plus ½Σ c_j ε_j². -/
theorem quad_fisher_quant_bound (a : I → Fin d → ℝ) (y : I → ℝ)
    (θ θq ε : Fin d → ℝ) (hε : ∀ j, |θq j - θ j| ≤ ε j) :
    quadLoss a y θq - quadLoss a y θ
      ≤ ∑ j, |quadGrad a y θ j| * ε j
        + ∑ j, colCurv a j * ε j ^ 2 / 2 := by
  have hkey : θ + (fun j => θq j - θ j) = θq := by
    funext j
    simp [Pi.add_apply]
  have hcurv : ∀ e : Fin d → ℝ,
      quadLoss a y (θ + e) ≤ quadLoss a y θ
        + ∑ j, quadGrad a y θ j * e j
        + ∑ j, colCurv a j * e j ^ 2 / 2 :=
    fun e => quadLoss_curv_le a y θ e
  have h := fisher_quant_loss_bound (quadLoss a y) θ
    (fun j => θq j - θ j) (quadGrad a y θ) (colCurv a) ε
    (fun j => colCurv_nonneg a j) hcurv (fun j => by
      have := hε j
      simpa using this)
  rw [hkey] at h
  linarith

/-- At a stationary point of the quadratic loss the price is purely
curvature: ½Σ c_j ε_j² — the C472 headline. -/
theorem quad_fisher_quant_bound_opt (a : I → Fin d → ℝ) (y : I → ℝ)
    (θ θq ε : Fin d → ℝ)
    (hgrad : ∀ j, quadGrad a y θ j = 0) (hε : ∀ j, |θq j - θ j| ≤ ε j) :
    quadLoss a y θq - quadLoss a y θ ≤ ∑ j, colCurv a j * ε j ^ 2 / 2 := by
  have hcurv : ∀ e : Fin d → ℝ,
      quadLoss a y (θ + e) ≤ quadLoss a y θ
        + ∑ j, quadGrad a y θ j * e j
        + ∑ j, colCurv a j * e j ^ 2 / 2 :=
    fun e => quadLoss_curv_le a y θ e
  have hkey : θ + (fun j => θq j - θ j) = θq := by
    funext j
    simp [Pi.add_apply]
  have h := fisher_quant_loss_bound_opt (quadLoss a y) θ
    (fun j => θq j - θ j) (quadGrad a y θ) (colCurv a) ε
    (fun j => colCurv_nonneg a j) hcurv hgrad (fun j => by
      have := hε j
      simpa using this)
  rw [hkey] at h
  linarith

/-! ## Fisher beats Lipschitz (anisotropy comparison) -/

/-- Pointwise comparison: under the per-coordinate tolerance premise
ε_j ≤ 2L/c_j (the c_min-flavored hypothesis: a UNIFORM ε must satisfy
ε ≤ 2L/c_max everywhere, while the Fisher form allows coordinate-wise
ε_j = 2L/c_j), the curvature penalty ½Σ c_j ε_j² is bounded by the
Lipschitz transport L·Σ ε_j. Isotropic c gives NO gain (both sides
collapse to the same form); the gain is strictly anisotropic — flat
coordinates (small c) tolerate a c_max/c_min factor more error. -/
theorem fisher_beats_lipschitz (c ε : Fin d → ℝ) (L : ℝ)
    (hc : ∀ j, 0 < c j) (hε0 : ∀ j, 0 ≤ ε j)
    (hε : ∀ j, ε j ≤ 2 * L / c j) :
    ∑ j, c j * ε j ^ 2 / 2 ≤ L * ∑ j, ε j := by
  have hcε : ∀ j, c j * ε j ≤ 2 * L := by
    intro j
    have h := mul_le_mul_of_nonneg_left (hε j) (le_of_lt (hc j))
    rw [show c j * (2 * L / c j) = 2 * L from by
      field_simp [(hc j).ne']] at h
    exact h
  have hterm : ∀ j, c j * ε j ^ 2 / 2 ≤ L * ε j := by
    intro j
    nlinarith [hc j, hε0 j, hcε j]
  calc ∑ j, c j * ε j ^ 2 / 2 ≤ ∑ j, L * ε j :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = L * ∑ j, ε j := (Finset.mul_sum _ _ _).symm

/-- Monotone tolerance: the Fisher admissible per-coordinate budget
2L/c_j is LARGER on flatter coordinates (smaller curvature). -/
theorem fisher_tolerance_mono (L : ℝ) (c : Fin d → ℝ) (hL : 0 ≤ L)
    (i j : Fin d) (hi : 0 < c i) (hj : 0 < c j) (hij : c i ≤ c j) :
    2 * L / c j ≤ 2 * L / c i := by
  exact (div_le_div_iff₀ hj hi).mpr
    (mul_le_mul_of_nonneg_left hij (mul_nonneg zero_le_two hL))

/-! ## Bridge to weightedExpAllocation: Fisher-weighted bit allocation -/

open Hagi.Budget in
/-- BRIDGE (C472): the closed-form optimal allocation of
`weightedExpAllocation` (with uniform decay κ and weights w) is
MONOTONE in the cost coefficient c: coordinates with larger Fisher
curvature c receive MORE budget r*. Reading r as bits and c as the
per-coordinate curvature weight, the optimal exponential-budget
allocation spends more bits exactly where quantization hurts most. -/
theorem fisher_alloc_mono (c κ w : Fin d → ℝ) (B : ℝ)
    (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    (i j : Fin d) (hκij : κ i = κ j) (hwij : w i = w j)
    (hcc : c i ≤ c j) :
    Hagi.Budget.weightedExpAllocation c κ w B i
      ≤ Hagi.Budget.weightedExpAllocation c κ w B j := by
  unfold Hagi.Budget.weightedExpAllocation
  have hle : c i * κ j / w i ≤ c j * κ j / w j := by
    rw [hwij]
    rw [div_le_div_iff_of_pos_right (hw j)]
    exact mul_le_mul_of_nonneg_right hcc (le_of_lt (hκ j))
  rw [hκij]
  rw [div_le_div_iff_of_pos_right (hκ j)]
  apply sub_le_sub_right
  exact Real.log_le_log (div_pos (mul_pos (hc i) (hκ j)) (hw i)) hle

open Hagi.Budget in
/-- Isotropic pin: when the curvature is the same everywhere (uniform
κ, w), the optimal allocation is UNIFORM — no Fisher gain in the
isotropic case, exactly as the lip-form predicts. -/
theorem fisher_alloc_isotropic_uniform (c κ w : Fin d → ℝ) (B : ℝ)
    (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    (i j : Fin d) (hci : c i = c j) (hκij : κ i = κ j)
    (hwij : w i = w j) :
    Hagi.Budget.weightedExpAllocation c κ w B i
      = Hagi.Budget.weightedExpAllocation c κ w B j :=
  le_antisymm
    (fisher_alloc_mono c κ w B hκ hw hc i j hκij hwij (le_of_eq hci))
    (fisher_alloc_mono c κ w B hκ hw hc j i hκij.symm hwij.symm
      (le_of_eq hci.symm))

end Hagi.Theory.FisherQuant
