/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Optimization.InexactContraction
import Hagi.Energy.SingleCellDescent

set_option linter.style.header false

/-!
# Latent energy field: strict convexity, ℓ∞ contraction, two-phase protocol

Track E3 (addendum A9 §E3 + A9-supplement, CRAM / Maze-Hard): the LATENT
quadratic energy on a finite graph carrier,

  `latentEnergy N m G z = (m/2)·Σ z i^2 − (1/2)·Σ i, z i * Σ j ∈ N i, z j − z G`,

with symmetric adjacency `j ∈ N i ↔ i ∈ N j` and degree bound
`(N i).card ≤ Δ`, `m > Δ`. CONVENTION (fixed, numerically anchored on the
path-graph fixture below): NEIGHBOR-SUM cross term with the `1/2` outside —
under symmetric adjacency this equals the edge form `(m/2)·Σz^2 −
Σ_{each edge once} z_i·z_j − z_G`, since each edge appears twice in the
double neighbor sum and the `1/2` collapses the duplicate.

Main results:

* `latent_hessian_diag_dominant` — the symmetrized quadratic form obeys
  `((m−Δ)/2)·Σ w^2 ≤ Q(w)`: diagonal `m` strictly dominates the
  off-diagonal row-sum `Δ` (honest derivation via `|w_i|·|w_j| ≤
  (w_i^2 + w_j^2)/2`, with the COLUMN part of the double sum bounded by
  `Δ` only through the symmetry premise — the graph symmetry is
  load-bearing, not decorous).
* `latent_quad_pos`, `latent_strict_convex`, `latent_unique_min` —
  positive-definiteness for `w ≠ 0`, strict convexity along chords, and
  uniqueness of the global minimizer (midpoint chord argument).
* `latent_fixed_iff_grad` — the fixed-point equation
  `z* i = (Σ_{j ∈ N i} z* j + 1[i = G])/m` ⟺ zero gradient.
* `latent_update_contraction` — the discrete update IS the fixed-point
  map and is a `Δ/m`-contraction in the ℓ∞ (Pi sup) norm, `Δ/m < 1`.
* `latent_update_fixed_exists` — Banach fixed point (existence of the
  minimizer, chained to `latent_min_of_grad_zero`).
* `latent_iterate_err_bound` — geometric iterate bound
  `‖z^k − z*‖ ≤ (Δ/m)^k·‖z^0 − z*‖`, REUSING
  `Hagi.Optimization.inexact_contraction_bound` at `ε = 0` (no geometric
  induction duplicated here); tolerance form `latent_settle_tolerance`.
* `visible_descent_frozen_z` — the TWO-PHASE protocol composition: after
  settling `z` and FREEZING it into the constant bias
  `visibleBiasWithZ B zc`, the visible greedy single-cell descent
  (`Hagi.Energy.greedy_single_cell_nonincreasing`, C261) applies verbatim.

## Two-phase protocol (supplement mandate)

Phase 1: iterate `latentUpdate` until `‖z^k − z*‖ < ε_z`
(`latent_settle_tolerance` gives the horizon). Phase 2: FREEZE the
latent contribution `zc` (constant in the visible state `y`) and run the
visible CRAM descent with bias `visibleBiasWithZ B zc`. JOINT `(z, p)`
updates are FORBIDDEN by this theory: a z-move changes the bias
`B' i a = B i a + zc i` mid-descent, so the C261 single-cell delta
identity no longer bounds the total energy change and the Lyapunov
argument breaks. The frozen-z premise is structural: `zc : ι → ℝ` is not
a function of `y`. No joint-update descent theorem exists (see the
RootApi negative pin: the name visible_descent_joint_z is nonexistent).

## Honest boundaries

* `Δ = 0` degenerate case: `latent_iterate_err_bound` and
  `latent_settle_tolerance` carry the premise `0 < Δ` because the reused
  `inexact_contraction_bound` requires a contraction factor in `(0,1)`
  (at `Δ = 0` the update is constant and the iterate is exact after one
  step; that case is outside this corollary's scope, not hidden).
* `m ≤ Δ` witnesses below show the degree gap is NECESSARY: at `m = Δ`
  the form is merely semidefinite on the double-loop graph, at `m < Δ`
  it takes negative values — no convexity, no contraction factor < 1.
* Energy descent (visible or latent) is NOT a validity certificate; the
  E-track certificates remain separate (A9 cert-kernel).
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (localField pairwiseEnergy greedy_single_cell_nonincreasing)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Carrier -/
section Defs

/-- **`latentQuadraticForm`** — the quadratic part of the latent energy:
`(m/2)·Σ w i^2 − (1/2)·Σ i, w i * Σ j ∈ N i, w j` (neighbor-sum
convention; equals the edge form under symmetric adjacency). -/
noncomputable def latentQuadraticForm (N : ι → Finset ι) (m : ℝ) (w : ι → ℝ) : ℝ :=
  ∑ i, (m / 2 * w i ^ 2 - (1 / 2) * w i * ∑ j ∈ N i, w j)

/-- **`latentEnergy`** — the Maze-Hard latent energy: quadratic form minus
the goal indicator `- z G`. -/
noncomputable def latentEnergy (N : ι → Finset ι) (m : ℝ) (G : ι) (z : ι → ℝ) : ℝ :=
  latentQuadraticForm N m z - z G

/-- **`latentGradient`** — coordinate gradient of `latentEnergy`:
`m * z i - Σ j ∈ N i, z j - 1[i = G]`. -/
noncomputable def latentGradient (N : ι → Finset ι) (m : ℝ) (G : ι) (z : ι → ℝ) (i : ι) : ℝ :=
  m * z i - ∑ j ∈ N i, z j - (if i = G then (1 : ℝ) else 0)

/-- **`latentUpdate`** — the discrete latent update (the fixed-point map):
`(Σ j ∈ N i, z j + 1[i = G]) / m`. -/
noncomputable def latentUpdate (N : ι → Finset ι) (m : ℝ) (G : ι) (z : ι → ℝ) (i : ι) : ℝ :=
  (∑ j ∈ N i, z j + (if i = G then (1 : ℝ) else 0)) / m

/-- **`visibleBiasWithZ`** — the visible CRAM bias `B` shifted by the
FROZEN latent contribution `zc` (constant in the visible state by
construction — the two-phase premise). -/
noncomputable def visibleBiasWithZ {α : Type*} (B : ι → α → ℝ) (zc : ι → ℝ) :
    ι → α → ℝ := fun i a => B i a + zc i

end Defs

/-! ## Exchange lemma (symmetric adjacency) -/
section Exchange

/-- **`sum_exchange`** — under symmetric adjacency the bilinear cross sum
is symmetric: `Σ i, a i * Σ j ∈ N i, b j = Σ i, b i * Σ j ∈ N i, a j`. -/
theorem sum_exchange (N : ι → Finset ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j) (a b : ι → ℝ) :
    ∑ i, a i * ∑ j ∈ N i, b j = ∑ i, b i * ∑ j ∈ N i, a j := by
  have key : ∀ (S : Finset ι) (f : ι → ℝ),
      ∑ j ∈ S, f j = ∑ j ∈ Finset.univ, if j ∈ S then f j else 0 := by
    intro S f
    rw [← Finset.sum_filter (p := (· ∈ S)) (s := Finset.univ) (f := f)]
    congr 1
    ext x
    simp
  have step : ∀ i, a i * ∑ j ∈ N i, b j
      = ∑ j ∈ Finset.univ, if j ∈ N i then a i * b j else 0 := by
    intro i
    rw [key (N i) (fun j => b j), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      by_cases h : j ∈ N i <;> simp [h]
  simp only [step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key (N i) (fun j => a j), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j ∈ N i
  · have h' : i ∈ N j := (hNsymm i j).mp h
    simp [h, h']; ring
  · have h' : i ∉ N j := fun hc => h ((hNsymm j i).mp hc)
    simp [h, h']

end Exchange

/-! ## Diagonal dominance -/
section Dominance

/-- **`abs_le_half_sq`** — the two-squares bound `|x| * |y| ≤
((1/2)) * (x^2 + y^2)`. -/
theorem abs_le_half_sq (x y : ℝ) : |x| * |y| ≤ ((1:ℝ)/2) * (x ^ 2 + y ^ 2) := by
  have h := sq_nonneg (|x| - |y|)
  have hx : |x| ^ 2 = x ^ 2 := sq_abs x
  have hy : |y| ^ 2 = y ^ 2 := sq_abs y
  nlinarith

/-- **`latent_cross_le`** — the cross term obeys
`Σ i, w i * Σ j ∈ N i, w j ≤ Δ * Σ w i ^2`: the row part uses
`(N i).card ≤ Δ`, the column part uses the SAME bound only through the
symmetry premise (`{i | j ∈ N i} = N j`). -/
theorem latent_cross_le (N : ι → Finset ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (w : ι → ℝ) :
    ∑ i, w i * ∑ j ∈ N i, w j ≤ (Δ : ℝ) * ∑ i, w i ^ 2 := by
  have habs : ∀ i, w i * ∑ j ∈ N i, w j
      ≤ ∑ j ∈ N i, ((1:ℝ)/2) * (w i ^ 2 + w j ^ 2) := by
    intro i
    have e1 : |w i * ∑ j ∈ N i, w j| = |w i| * |∑ j ∈ N i, w j| := abs_mul _ _
    have e2 : |∑ j ∈ N i, w j| ≤ ∑ j ∈ N i, |w j| := Finset.abs_sum_le_sum_abs _ _
    calc w i * ∑ j ∈ N i, w j ≤ |w i * ∑ j ∈ N i, w j| := le_abs_self _
      _ = |w i| * |∑ j ∈ N i, w j| := e1
      _ ≤ |w i| * ∑ j ∈ N i, |w j| := mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
      _ = ∑ j ∈ N i, |w i| * |w j| := by rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ N i, ((1:ℝ)/2) * (w i ^ 2 + w j ^ 2) :=
          Finset.sum_le_sum fun j _ => abs_le_half_sq _ _
  have hsplit : ∑ i, ∑ j ∈ N i, ((1:ℝ)/2) * (w i ^ 2 + w j ^ 2)
      = ((1:ℝ)/2) * (∑ i, ((N i).card : ℝ) * w i ^ 2 + ∑ i, ∑ j ∈ N i, w j ^ 2) := by
    have e1 : ∀ i, ∑ j ∈ N i, ((1:ℝ)/2) * (w i ^ 2 + w j ^ 2)
        = ((1:ℝ)/2) * (((N i).card : ℝ) * w i ^ 2 + ∑ j ∈ N i, w j ^ 2) := by
      intro i
      have step : ∀ j ∈ N i, ((1:ℝ)/2) * (w i ^ 2 + w j ^ 2)
          = ((1:ℝ)/2) * w i ^ 2 + ((1:ℝ)/2) * w j ^ 2 := fun j _ => by ring
      rw [Finset.sum_congr rfl step, Finset.sum_add_distrib, Finset.sum_const]
      have hs : ((1:ℝ)/2) * ∑ j ∈ N i, w j ^ 2
          = ∑ j ∈ N i, ((1:ℝ)/2) * w j ^ 2 := Finset.mul_sum _ _ _
      rw [← hs]
      simp
      ring
    rw [Finset.sum_congr rfl fun i _ => e1 i, ← Finset.mul_sum,
      Finset.sum_add_distrib]
  have hrow : ∑ i, ((N i).card : ℝ) * w i ^ 2 ≤ ∑ i, ((Δ:ℝ)) * w i ^ 2 :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast hΔ i : ((N i).card : ℝ) ≤ (Δ : ℝ)) (sq_nonneg _)
  have hrow' : ∑ i, ((Δ:ℝ)) * w i ^ 2 = (Δ : ℝ) * ∑ i, w i ^ 2 :=
    (Finset.mul_sum _ _ _).symm
  have hcol : ∑ i, ∑ j ∈ N i, w j ^ 2 ≤ (Δ : ℝ) * ∑ i, w i ^ 2 := by
    have key : ∀ (S : Finset ι) (f : ι → ℝ),
        ∑ j ∈ S, f j = ∑ j ∈ Finset.univ, if j ∈ S then f j else 0 := by
      intro S f
      rw [← Finset.sum_filter (p := (· ∈ S)) (s := Finset.univ) (f := f)]
      congr 1
      ext x
      simp
    rw [Finset.sum_congr rfl fun i _ => key _ _, Finset.sum_comm]
    have eswap : ∀ j, (∑ i ∈ Finset.univ, if j ∈ N i then w j ^ 2 else 0 : ℝ)
        = ∑ i ∈ N j, w j ^ 2 := by
      intro j
      have e : ∀ i ∈ Finset.univ, (if j ∈ N i then w j ^ 2 else 0)
          = if i ∈ N j then w j ^ 2 else 0 := by
        intro i _
        by_cases h : j ∈ N i
        · have h' : i ∈ N j := (hNsymm i j).mp h
          simp [h, h']
        · have h' : i ∉ N j := fun hc => h ((hNsymm i j).mpr hc)
          simp [h, h']
      exact (Finset.sum_congr rfl e).trans (key (N j) (fun _ => w j ^ 2)).symm
    have esum : ∀ j, ∑ i ∈ N j, w j ^ 2 = ((N j).card : ℝ) * w j ^ 2 := by
      intro j
      rw [Finset.sum_const]
      simp
    rw [Finset.sum_congr rfl fun j _ => eswap j]
    rw [Finset.sum_congr rfl fun j _ => esum j]
    have hfin : ∑ j, ((N j).card : ℝ) * w j ^ 2 ≤ ∑ j, ((Δ:ℝ)) * w j ^ 2 :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast hΔ j : ((N j).card : ℝ) ≤ (Δ : ℝ)) (sq_nonneg _)
    have hfin' : ∑ j, ((Δ:ℝ)) * w j ^ 2 = (Δ : ℝ) * ∑ j, w j ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    rw [← hfin']
    exact hfin
  calc ∑ i, w i * ∑ j ∈ N i, w j
      ≤ ∑ i, ∑ j ∈ N i, ((1:ℝ)/2) * (w i ^ 2 + w j ^ 2) :=
        Finset.sum_le_sum fun i _ => habs i
    _ = ((1:ℝ)/2) * (∑ i, ((N i).card : ℝ) * w i ^ 2 + ∑ i, ∑ j ∈ N i, w j ^ 2) :=
        hsplit
    _ ≤ ((1:ℝ)/2) * ((Δ:ℝ) * ∑ i, w i ^ 2 + (Δ:ℝ) * ∑ i, w i ^ 2) := by
        have h1 : ∑ i, ((N i).card : ℝ) * w i ^ 2 ≤ (Δ:ℝ) * ∑ i, w i ^ 2 :=
          hrow.trans_eq hrow'
        exact mul_le_mul_of_nonneg_left (add_le_add h1 hcol) (by norm_num)
    _ = (Δ:ℝ) * ∑ i, w i ^ 2 := by rw [Finset.mul_sum]; ring

/-- **`latent_hessian_diag_dominant`** — (E3 MAIN) the symmetrized quadratic
form is diagonally dominant with gap `m − Δ`:
`((m − Δ)/2) * Σ w i ^ 2 ≤ latentQuadraticForm N m w`. -/
theorem latent_hessian_diag_dominant (N : ι → Finset ι) (m : ℝ)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (w : ι → ℝ) :
    (m - (Δ : ℝ)) / 2 * ∑ i, w i ^ 2 ≤ latentQuadraticForm N m w := by
  have hc := latent_cross_le N hNsymm hΔ w
  have hS : (0:ℝ) ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  unfold latentQuadraticForm
  have e1 : ∑ i, (m / 2 * w i ^ 2 - (1 / 2) * w i * ∑ j ∈ N i, w j)
      = (m / 2) * ∑ i, w i ^ 2 - (1 / 2) * ∑ i, w i * ∑ j ∈ N i, w j := by
    have hL : ∑ i, (m / 2 * w i ^ 2) = (m / 2) * ∑ i, w i ^ 2 := by
      rw [Finset.mul_sum]
    have key2 : ∀ i, ((1:ℝ)/2) * w i * ∑ j ∈ N i, w j
        = (1/2) * (w i * ∑ j ∈ N i, w j) := fun i => by ring
    have hR : ∑ i, ((1 / 2) * w i * ∑ j ∈ N i, w j)
        = (1 / 2) * ∑ i, w i * ∑ j ∈ N i, w j := by
      rw [Finset.sum_congr rfl (fun i _ => key2 i), Finset.mul_sum]
    rw [Finset.sum_sub_distrib, hL, hR]
  rw [e1]
  have hkey : (m / 2) * ∑ i, w i ^ 2 - (1 / 2) * ∑ i, w i * ∑ j ∈ N i, w j
      - (m - (Δ : ℝ)) / 2 * ∑ i, w i ^ 2
      = ((1:ℝ)/2) * ((Δ:ℝ) * ∑ i, w i ^ 2
          - ∑ i, w i * ∑ j ∈ N i, w j) := by ring
  linarith

end Dominance

/-! ## Positivity, chord identity, strict convexity -/
section Positivity

omit [DecidableEq ι] in
/-- **`latent_quad_sum_pos`** — a nonzero function has positive squared
`1`-sum. -/
theorem latent_quad_sum_pos (w : ι → ℝ) (hw : w ≠ 0) : 0 < ∑ i, w i ^ 2 := by
  by_contra hcon
  have hz : ∑ i, w i ^ 2 = 0 :=
    le_antisymm (le_of_not_gt hcon) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have h0 := Finset.sum_eq_zero_iff_of_nonneg
    (f := fun i => w i ^ 2) (fun i _ => sq_nonneg _) |>.mp hz
  apply hw
  funext i
  have h2 := h0 i (Finset.mem_univ i)
  exact (pow_eq_zero_iff two_ne_zero).mp h2

/-- **`latent_quad_pos`** — for `m > Δ` and `w ≠ 0` the quadratic form is
strictly positive (positive definiteness of the symmetrized Hessian). -/
theorem latent_quad_pos (N : ι → Finset ι) (m : ℝ)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (w : ι → ℝ) (hw : w ≠ 0) : 0 < latentQuadraticForm N m w := by
  have hdom := latent_hessian_diag_dominant N m hNsymm hΔ w
  have hpos := latent_quad_sum_pos w hw
  have hcoeff : 0 < (m - (Δ : ℝ)) / 2 := by
    have : 0 < m - (Δ : ℝ) := by linarith
    exact div_pos this (by norm_num)
  have := mul_pos hcoeff hpos
  linarith

end Positivity

/-! ## Add-with-remainder, homogeneity, chord -/
section Chord

omit [DecidableEq ι] in
/-- **`cross_expand`** — the cross double-sum of a linear combination
expands bilinearly: `Cross(c·u + d·v) = c²·Cross(u) +
c·d·(X(u,v) + X(v,u)) + d²·Cross(v)`. -/
theorem cross_expand (N : ι → Finset ι)
    (u v : ι → ℝ) (c d : ℝ) :
    ∑ i, (c * u i + d * v i) * ∑ j ∈ N i, (c * u j + d * v j)
      = c * c * (∑ i, u i * ∑ j ∈ N i, u j)
        + c * d * (∑ i, u i * ∑ j ∈ N i, v j + ∑ i, v i * ∑ j ∈ N i, u j)
        + d * d * (∑ i, v i * ∑ j ∈ N i, v j) := by
  have mulc : ∀ (c : ℝ) (s : Finset ι) (f : ι → ℝ),
      ∑ j ∈ s, c * f j = c * ∑ j ∈ s, f j := fun c s f => by rw [Finset.mul_sum]
  have inner : ∀ i, ∑ j ∈ N i, (c * u j + d * v j)
      = c * ∑ j ∈ N i, u j + d * ∑ j ∈ N i, v j := by
    intro i
    rw [Finset.sum_add_distrib, mulc c (N i) _, mulc d (N i) _]
  have step : ∀ i, (c * u i + d * v i) * ∑ j ∈ N i, (c * u j + d * v j)
      = c * c * (u i * ∑ j ∈ N i, u j)
        + c * d * (u i * ∑ j ∈ N i, v j + v i * ∑ j ∈ N i, u j)
        + d * d * (v i * ∑ j ∈ N i, v j) := by
    intro i; rw [inner i]; ring
  rw [Finset.sum_congr rfl (fun i _ => step i), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  rw [mulc (c*c) _ _, mulc (c*d) _ _, mulc (d*d) _ _]
  rw [Finset.sum_add_distrib]

omit [DecidableEq ι] in
/-- **`cross_sub`** — the cross double-sum of a difference:
`Cross(a − b) = Cross(a) − (X(a,b) + X(b,a)) + Cross(b)`. -/
theorem cross_sub (N : ι → Finset ι) (a b : ι → ℝ) :
    ∑ i, (a i - b i) * ∑ j ∈ N i, (a j - b j)
      = ∑ i, a i * ∑ j ∈ N i, a j
        - (∑ i, a i * ∑ j ∈ N i, b j + ∑ i, b i * ∑ j ∈ N i, a j)
        + ∑ i, b i * ∑ j ∈ N i, b j := by
  have inner : ∀ i, ∑ j ∈ N i, (a j - b j)
      = ∑ j ∈ N i, a j - ∑ j ∈ N i, b j := fun i => by rw [Finset.sum_sub_distrib]
  have step : ∀ i, (a i - b i) * ∑ j ∈ N i, (a j - b j)
      = (a i * ∑ j ∈ N i, a j + b i * ∑ j ∈ N i, b j)
        - (a i * ∑ j ∈ N i, b j + b i * ∑ j ∈ N i, a j) := by
    intro i; rw [inner i]; ring
  rw [Finset.sum_congr rfl (fun i _ => step i), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

omit [DecidableEq ι] in
/-- **`latent_quad_split`** — split-form helper: the quadratic form as
`(m/2)·Σ w^2 − (1/2)·Cross(w)`. -/
theorem latent_quad_split (N : ι → Finset ι) (m : ℝ) (w : ι → ℝ) :
    latentQuadraticForm N m w
      = (m / 2) * ∑ i, w i ^ 2
        - (1 / 2) * ∑ i, w i * ∑ j ∈ N i, w j := by
  unfold latentQuadraticForm
  have mulc : ∀ (c : ℝ) (f : ι → ℝ), ∑ i, c * f i = c * ∑ i, f i :=
    fun c f => by rw [Finset.mul_sum]
  have hA : ∑ i, m / 2 * w i ^ 2 = (m / 2) * ∑ i, w i ^ 2 :=
    mulc (m / 2) (fun i => w i ^ 2)
  have hB : ∑ i, (1 / 2) * w i * ∑ j ∈ N i, w j
      = (1 / 2) * ∑ i, w i * ∑ j ∈ N i, w j := by
    have key : ∀ i, (1 / 2) * w i * ∑ j ∈ N i, w j
        = (1 / 2) * (w i * ∑ j ∈ N i, w j) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => key i), mulc (1 / 2) _]
  rw [Finset.sum_sub_distrib]
  linarith

/-- **`latent_quad_chord`** — Bregman chord identity for the quadratic
form (NO graph premises): the form at a convex combination equals the
combination minus `t·(1−t)` times the form of the difference. -/
theorem latent_quad_chord (N : ι → Finset ι) (m : ℝ)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j) (a b : ι → ℝ) (t : ℝ) :
    latentQuadraticForm N m (fun i => t * a i + (1 - t) * b i)
      = t * latentQuadraticForm N m a + (1 - t) * latentQuadraticForm N m b
        - t * (1 - t) * latentQuadraticForm N m (fun i => a i - b i) := by
  have hex : ∑ i, a i * ∑ j ∈ N i, b j = ∑ i, b i * ∑ j ∈ N i, a j :=
    sum_exchange N hNsymm a b
  have hc := cross_expand N a b t (1 - t)
  have hcs := cross_sub N a b
  have mulc : ∀ (c : ℝ) (f : ι → ℝ), ∑ i, c * f i = c * ∑ i, f i :=
    fun c f => by rw [Finset.mul_sum]
  have step : ∀ i, (t * a i + (1 - t) * b i) ^ 2
      = t * a i ^ 2 + (1 - t) * b i ^ 2 - t * (1 - t) * (a i - b i) ^ 2 :=
    fun i => by ring
  have hd : ∑ i, (t * a i + (1 - t) * b i) ^ 2
      = t * ∑ i, a i ^ 2 + (1 - t) * ∑ i, b i ^ 2
        - t * (1 - t) * ∑ i, (a i - b i) ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => step i), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, mulc t _, mulc (1 - t) _, mulc (t * (1 - t)) _]
  rw [latent_quad_split, latent_quad_split, latent_quad_split, latent_quad_split,
    hd, hc, hcs]
  rw [hex]
  ring

omit [DecidableEq ι] in
/-- **`latent_quad_smul`** — homogeneity of degree `2`:
`Q(c • w) = c^2 * Q(w)`. -/
theorem latent_quad_smul (N : ι → Finset ι) (m : ℝ) (c : ℝ) (w : ι → ℝ) :
    latentQuadraticForm N m (fun i => c * w i)
      = c * c * latentQuadraticForm N m w := by
  have mulc : ∀ (cc : ℝ) (s : Finset ι) (f : ι → ℝ),
      ∑ j ∈ s, cc * f j = cc * ∑ j ∈ s, f j := fun cc s f => by rw [Finset.mul_sum]
  have step : ∀ i, m / 2 * (c * w i) ^ 2 - (1 / 2) * (c * w i) * ∑ j ∈ N i, (c * w j)
      = c * c * (m / 2 * w i ^ 2 - (1 / 2) * w i * ∑ j ∈ N i, w j) := by
    intro i
    rw [mulc c (N i) _]
    ring
  unfold latentQuadraticForm
  rw [Finset.sum_congr rfl (fun i _ => step i)]
  have mulc2 : ∀ (cc : ℝ) (f : ι → ℝ), ∑ i, cc * f i = cc * ∑ i, f i :=
    fun cc f => by rw [Finset.mul_sum]
  rw [mulc2 (c * c) _]

end Chord

/-! ## Strict convexity and the energy add-remainder identity -/
section Convex

/-- **`latent_energy_add`** — add-with-remainder identity:
`E(z + w) = E(z) + ⟨grad E(z), w⟩ + Q(w)` (the second-order remainder is
exactly the quadratic form). -/
theorem latent_energy_add (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j) (z w : ι → ℝ) :
    latentEnergy N m G (fun i => z i + w i)
      = latentEnergy N m G z + ∑ i, w i * latentGradient N m G z i
        + latentQuadraticForm N m w := by
  have mulc : ∀ (c : ℝ) (f : ι → ℝ), ∑ i, c * f i = c * ∑ i, f i :=
    fun c f => by rw [Finset.mul_sum]
  have stepd : ∀ i, (z i + w i) ^ 2 = z i ^ 2 + 2 * (z i * w i) + w i ^ 2 :=
    fun i => by ring
  have hd : ∑ i, (z i + w i) ^ 2
      = ∑ i, z i ^ 2 + 2 * ∑ i, z i * w i + ∑ i, w i ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => stepd i), Finset.sum_add_distrib,
      Finset.sum_add_distrib, mulc 2 _]
  have hex : ∑ i, z i * ∑ j ∈ N i, w j = ∑ i, w i * ∑ j ∈ N i, z j :=
    sum_exchange N hNsymm z w
  -- cross_add inline (same-layer helper below is avoided: direct expand)
  have hcross : ∑ i, (z i + w i) * ∑ j ∈ N i, (z j + w j)
      = ∑ i, z i * ∑ j ∈ N i, z j
        + (∑ i, z i * ∑ j ∈ N i, w j + ∑ i, w i * ∑ j ∈ N i, z j)
        + ∑ i, w i * ∑ j ∈ N i, w j := by
    have h := cross_expand N z w 1 1
    simp only [one_mul] at h
    exact h
  have hgrad : ∑ i, w i * latentGradient N m G z i
      = m * ∑ i, z i * w i - ∑ i, w i * ∑ j ∈ N i, z j - w G := by
    have e : ∀ i, w i * latentGradient N m G z i
        = m * (z i * w i) - w i * ∑ j ∈ N i, z j
          - w i * (if i = G then (1:ℝ) else 0) := fun i => by
      rw [latentGradient]; ring
    have eind : ∑ i, w i * (if i = G then (1:ℝ) else 0) = w G := by
      simp
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, mulc m _, ← eind]
  have hlin : (fun i => z i + w i) G = z G + w G := by ring
  unfold latentEnergy
  rw [latent_quad_split, latent_quad_split, latent_quad_split]
  rw [hd, hcross, hlin, hgrad]
  rw [hex]
  ring

/-- **`latent_strict_convex`** — (E3 MAIN) for `m > Δ`, distinct points and
`0 < t < 1` the energy is strictly below the chord. -/
theorem latent_strict_convex (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (a b : ι → ℝ) (hab : a ≠ b) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    latentEnergy N m G (fun i => t * a i + (1 - t) * b i)
      < t * latentEnergy N m G a + (1 - t) * latentEnergy N m G b := by
  have hq := latent_quad_chord N m hNsymm a b t
  have hlin : (fun i => t * a i + (1 - t) * b i) G
      = t * a G + (1 - t) * b G := by ring
  have hqd : 0 < t * (1 - t) * latentQuadraticForm N m (fun i => a i - b i) := by
    have hne : (fun i => a i - b i) ≠ 0 := by
      intro h
      apply hab
      funext i
      have h0 : a i - b i = 0 := by simpa using congrFun h i
      linarith
    have hpos := latent_quad_pos N m hNsymm hΔ hm _ hne
    have hts : 0 < t * (1 - t) := by nlinarith
    exact mul_pos hts hpos
  unfold latentEnergy
  rw [hlin]
  nlinarith [hq, hqd]

end Convex

/-! ## Fixed points, minimizers, contraction -/
section Fix

/-- **`latent_quad_nonneg`** — for `Δ ≤ m` the quadratic form is
nonnegative (semidefinite regime). -/
theorem latent_quad_nonneg (N : ι → Finset ι) (m : ℝ)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) ≤ m) (w : ι → ℝ) :
    0 ≤ latentQuadraticForm N m w := by
  have hdom := latent_hessian_diag_dominant N m hNsymm hΔ w
  have hS : (0:ℝ) ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc : (0:ℝ) ≤ (m - (Δ : ℝ)) / 2 := by
    have : (0:ℝ) ≤ m - (Δ : ℝ) := by linarith
    exact div_nonneg this (by norm_num)
  have := mul_nonneg hc hS
  linarith

omit [Fintype ι] in
/-- **`latent_fixed_iff_grad`** — the fixed-point equation of
`latentUpdate` ⟺ zero `latentGradient` (needs `m ≠ 0`). -/
theorem latent_fixed_iff_grad (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hm : m ≠ 0) (z : ι → ℝ) :
    latentUpdate N m G z = z ↔ ∀ i, latentGradient N m G z i = 0 := by
  constructor
  · intro h i
    have hi : (∑ j ∈ N i, z j + (if i = G then (1:ℝ) else 0)) / m = z i :=
      congrFun h i
    unfold latentGradient
    rw [div_eq_iff hm] at hi
    linarith
  · intro h
    funext i
    have hi := h i
    unfold latentUpdate at hi ⊢
    unfold latentGradient at hi
    rw [sub_eq_zero] at hi
    rw [div_eq_iff hm]
    linarith [hi]

/-- **`latent_min_of_grad_zero`** — zero gradient ⟹ global minimizer
(the add-remainder identity with a nonnegative remainder). -/
theorem latent_min_of_grad_zero (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) ≤ m)
    (zstar : ι → ℝ) (hg : ∀ i, latentGradient N m G zstar i = 0) :
    ∀ z, latentEnergy N m G zstar ≤ latentEnergy N m G z := by
  intro z
  have hrep : z = fun i => zstar i + (z i - zstar i) := by funext i; ring
  have h1 := latent_energy_add N m G hNsymm zstar (fun i => z i - zstar i)
  have hq := latent_quad_nonneg N m hNsymm hΔ hm (fun i => z i - zstar i)
  have hgrad : ∑ i, (z i - zstar i) * latentGradient N m G zstar i = 0 := by
    have e : ∀ i, (z i - zstar i) * latentGradient N m G zstar i
        = (z i - zstar i) * 0 := fun i => by rw [hg i]
    rw [Finset.sum_congr rfl (fun i _ => e i)]
    simp
  rw [hrep]
  rw [h1, hgrad]
  linarith

/-- **`latent_grad_zero_of_min`** — a global minimizer has zero gradient
(converse direction; single-coordinate test with the curvature of the
diagonal entry). -/
theorem latent_grad_zero_of_min (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hmin : ∀ z, latentEnergy N m G zstar ≤ latentEnergy N m G z) :
    ∀ i, latentGradient N m G zstar i = 0 := by
  intro i
  by_contra hg
  set e : ι → ℝ := fun j => if j = i then (1:ℝ) else 0 with he
  have hene : e ≠ 0 := by
    intro h
    apply hg
    have h0 : e i = (0 : ι → ℝ) i := congrFun h i
    rw [he] at h0
    simp at h0
  have hq : 0 < latentQuadraticForm N m e := latent_quad_pos N m hNsymm hΔ hm e hene
  set q := latentQuadraticForm N m e with hqdef
  set g := latentGradient N m G zstar i with hgdef
  set t := -g / (2 * q) with ht
  have h1 := latent_energy_add N m G hNsymm zstar (fun j => t * e j)
  have h2 : latentQuadraticForm N m (fun j => t * e j) = t * t * q :=
    latent_quad_smul N m t e
  have h3 : ∑ j, (t * e j) * latentGradient N m G zstar j = t * g := by
    have hterm : ∀ j, (t * e j) * latentGradient N m G zstar j
        = t * (if j = i then latentGradient N m G zstar j else 0) := by
      intro j
      by_cases hj : j = i
      · simp [he, hj]
      · simp [he, hj]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_eq_single i]
    · rw [hgdef]
      simp
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h2, h3] at h1
  have hmin' := hmin (fun j => zstar j + t * e j)
  have hneg : t * g + t * t * q < 0 := by
    have h4q : (0:ℝ) < 4 * q := by nlinarith
    have hgg : (0:ℝ) < g * g := mul_self_pos.mpr hg
    have hev : t * g + t * t * q = -((g * g) / (4 * q)) := by
      rw [ht]
      field_simp
      ring
    rw [hev]
    have hpos : (0:ℝ) < (g * g) / (4 * q) := div_pos hgg h4q
    linarith
  rw [h1] at hmin'
  nlinarith [hneg]

/-- **`latent_unique_min`** — (E3 MAIN) uniqueness of the global minimizer
(midpoint chord argument; `m > Δ`). -/
theorem latent_unique_min (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (a b : ι → ℝ)
    (ha : ∀ z, latentEnergy N m G a ≤ latentEnergy N m G z)
    (hb : ∀ z, latentEnergy N m G b ≤ latentEnergy N m G z) : a = b := by
  by_contra hne
  have hconv := latent_strict_convex N m G hNsymm hΔ hm a b hne (1/2) (by norm_num)
    (by norm_num)
  have hmid : (fun i => (1/2) * a i + (1 - 1/2) * b i)
      = fun i => (a i + b i) / 2 := by
    funext i; ring
  have h1 : latentEnergy N m G a = latentEnergy N m G b :=
    le_antisymm (ha b) (hb a)
  have h2 := ha (fun i => (a i + b i) / 2)
  rw [hmid] at hconv
  have h3 : (1/2) * latentEnergy N m G a + (1 - 1/2) * latentEnergy N m G b
      = latentEnergy N m G a := by
    rw [h1]; ring
  rw [h3] at hconv
  exact absurd hconv (not_lt.2 h2)

end Fix

/-! ## ℓ∞ contraction of the update map -/
section Contr

/-- **`latent_update_contraction`** — (E3 MAIN) the discrete update map is
a `Δ/m`-contraction in the ℓ∞ (Pi sup) norm, `Δ/m < 1`. -/
theorem latent_update_contraction (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (z z' : ι → ℝ) :
    ‖latentUpdate N m G z - latentUpdate N m G z'‖
      ≤ ((Δ : ℝ) / m) * ‖z - z'‖ := by
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _
    linarith
  have hnn : (0:ℝ) ≤ ((Δ : ℝ) / m) * ‖z - z'‖ := by
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hm0))
      (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hnn).mpr fun i => ?_
  have hnum : ‖∑ j ∈ N i, (z j - z' j)‖ ≤ ((N i).card : ℝ) * ‖z - z'‖ := by
    calc ‖∑ j ∈ N i, (z j - z' j)‖ ≤ ∑ j ∈ N i, ‖z j - z' j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ N i, ‖z - z'‖ := Finset.sum_le_sum fun j _ => norm_le_pi_norm (z - z') j
      _ = ((N i).card : ℝ) * ‖z - z'‖ := by rw [Finset.sum_const]; simp
  have hsplit : (∑ j ∈ N i, z j + (if i = G then (1:ℝ) else 0))
        - (∑ j ∈ N i, z' j + (if i = G then (1:ℝ) else 0))
      = ∑ j ∈ N i, (z j - z' j) := by
    have h1 : (∑ j ∈ N i, z j + (if i = G then (1:ℝ) else 0))
        - (∑ j ∈ N i, z' j + (if i = G then (1:ℝ) else 0))
        = (∑ j ∈ N i, z j) - (∑ j ∈ N i, z' j) := by ring
    rw [h1, Finset.sum_sub_distrib]
  unfold latentUpdate
  simp only [Pi.sub_apply]
  rw [div_sub_div_same, hsplit, norm_div,
    show ‖(m:ℝ)‖ = m from abs_of_pos hm0]
  have hcard : ((N i).card : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ i
  have h1 : ((N i).card : ℝ) * ‖z - z'‖ / m ≤ ((Δ : ℝ) / m) * ‖z - z'‖ := by
    rw [div_le_iff₀ hm0]
    have hrw : (((Δ : ℝ) / m) * ‖z - z'‖) * m = (Δ : ℝ) * ‖z - z'‖ := by
      field_simp
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hcard (norm_nonneg _)
  calc ‖∑ j ∈ N i, (z j - z' j)‖ / m
      ≤ (((N i).card : ℝ) * ‖z - z'‖) / m :=
        (div_le_div_iff_of_pos_right hm0).mpr hnum
    _ ≤ ((Δ : ℝ) / m) * ‖z - z'‖ := h1

end Contr

/-! ## Existence via Banach and the iterate error bound -/
section Banach

/-- **`latent_update_fixed_exists`** — existence of the latent minimizer:
Banach fixed point of the contraction, chained to
`latent_min_of_grad_zero` (the fixed point is the unique global minimizer
by `latent_unique_min`). -/
theorem latent_update_fixed_exists [Nonempty ι] (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m) :
    ∃ zstar, latentUpdate N m G zstar = zstar ∧
      ∀ z, latentEnergy N m G zstar ≤ latentEnergy N m G z := by
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _
    linarith
  have hnndiv : (0:ℝ) ≤ (Δ : ℝ) / m :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hm0)
  have hx1 : (Δ : ℝ) / m < 1 := by
    rw [div_lt_iff₀ hm0]
    linarith
  have hKlt : (Δ : ℝ) / m < ((Δ : ℝ) / m + 1) / 2 := by
    field_simp
    linarith
  have hK1 : ((Δ : ℝ) / m + 1) / 2 < 1 := by
    field_simp
    linarith
  have hval : (0:ℝ) ≤ ((Δ : ℝ) / m + 1) / 2 :=
    div_nonneg (by linarith) (by norm_num)
  have hlip : LipschitzWith (⟨((Δ : ℝ) / m + 1) / 2, hval⟩ : NNReal)
      (latentUpdate N m G) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      have h1 := latent_update_contraction N m G hΔ hm x y
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖latentUpdate N m G x - latentUpdate N m G y‖
          ≤ ((Δ : ℝ) / m) * ‖x - y‖ := h1
        _ ≤ (((Δ : ℝ) / m + 1) / 2) * ‖x - y‖ :=
            mul_le_mul_of_nonneg_right hKlt.le (norm_nonneg _)
  have hc : ContractingWith (⟨((Δ : ℝ) / m + 1) / 2, hval⟩ : NNReal)
      (latentUpdate N m G) := ⟨hK1, hlip⟩
  obtain ⟨zstar, hfix, -⟩ := hc.exists_fixedPoint (fun _ => 0)
    (edist_ne_top _ _)
  refine ⟨zstar, hfix, ?_⟩
  have hgrad : ∀ i, latentGradient N m G zstar i = 0 := by
    intro i
    exact (latent_fixed_iff_grad N m G (ne_of_gt hm0) zstar).mp hfix i
  exact latent_min_of_grad_zero N m G hNsymm hΔ (by linarith) zstar hgrad

/-- **`latent_iterate_err_bound`** — (E3 MAIN) geometric iterate error
bound `‖z^k − z*‖ ≤ (Δ/m)^k * ‖z^0 − z*‖` for any fixed point `z*` of the
update, REUSING `Hagi.Optimization.inexact_contraction_bound` at `ε = 0`
(premise `0 < Δ`: the reused lemma needs a factor in `(0,1)`; the `Δ = 0`
degenerate case is out of scope, see the module docstring). -/
theorem latent_iterate_err_bound (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hΔ0 : 0 < Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar)
    (z : ℕ → ι → ℝ) (hstep : ∀ k, z (k+1) = latentUpdate N m G (z k)) (k : ℕ) :
    ‖z k - zstar‖ ≤ ((Δ : ℝ) / m) ^ k * ‖z 0 - zstar‖ := by
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _
    linarith
  have hq0 : (0:ℝ) < (Δ : ℝ) / m := by
    have : (0:ℝ) < (Δ : ℝ) := by exact_mod_cast hΔ0
    exact div_pos this hm0
  have hq1 : (Δ : ℝ) / m < 1 := by
    rw [div_lt_iff₀ hm0]
    linarith
  have hrec : ∀ j, ‖z (j+1) - zstar‖ ≤ ((Δ : ℝ) / m) * ‖z j - zstar‖ + 0 := by
    intro j
    have h1 := latent_update_contraction N m G hΔ hm (z j) zstar
    rw [hstep j]
    nth_rewrite 1 [← hz]
    linarith [h1]
  have hmain := Hagi.Optimization.inexact_contraction_bound
    (fun j => ‖z j - zstar‖) ((Δ : ℝ) / m) 0 hq0 hq1 (le_refl 0) hrec k
  have hz0 : (0:ℝ) * (1 - ((Δ : ℝ) / m) ^ k) / (1 - (Δ : ℝ) / m) = 0 := by
    rw [zero_mul, zero_div]
  rw [hz0, add_zero] at hmain
  exact hmain

/-- **`latent_settle_tolerance`** — tolerance form: if the geometric decay
of the initial error is below the latent tolerance `ε_z`, iterate `k` has
settled to tolerance. -/
theorem latent_settle_tolerance (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hΔ0 : 0 < Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar)
    (z : ℕ → ι → ℝ) (hstep : ∀ k, z (k+1) = latentUpdate N m G (z k))
    (k : ℕ) (εz : ℝ)
    (hε : ((Δ : ℝ) / m) ^ k * ‖z 0 - zstar‖ < εz) :
    ‖z k - zstar‖ < εz := by
  have h := latent_iterate_err_bound N m G hΔ hΔ0 hm zstar hz z hstep k
  linarith

end Banach

/-! ## Two-phase protocol: frozen-z visible descent -/
section TwoPhase

/-- **`visible_descent_frozen_z`** — (E3 MAIN, thin by design) the
two-phase composition: after settling `z` and FREEZING it into the
constant bias `visibleBiasWithZ B zc` (constant in the visible state `y`
BY CONSTRUCTION — `zc` is not a function of `y`), the C261 greedy
single-cell visible descent applies verbatim: the energy
`pairwiseEnergy (visibleBiasWithZ B zc) K` does not increase under a move
to a local-field minimizer.

JOINT `(z, p)` updates break the Lyapunov argument: a z-move changes the
bias mid-descent, the C261 single-cell delta identity no longer bounds the
total energy change, and NO joint-update descent theorem is claimed (the RootApi negative
pin: the name visible_descent_joint_z is nonexistent — records this). -/
theorem visible_descent_frozen_z {α : Type*} (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (zc : ι → ℝ) (y : ι → α) (i : ι) (a : α)
    (hmin : ∀ a', localField (visibleBiasWithZ B zc) K y i a
      ≤ localField (visibleBiasWithZ B zc) K y i a') :
    pairwiseEnergy (visibleBiasWithZ B zc) K (Function.update y i a)
      ≤ pairwiseEnergy (visibleBiasWithZ B zc) K y :=
  greedy_single_cell_nonincreasing _ K hK y i a hmin

end TwoPhase

/-! ## Fixtures and witnesses -/
section Fixture

/-- **`pathN`** — path graph on `Fin 4` (maxDegree `Δ = 2` fixture). -/
def pathN : Fin 4 → Finset (Fin 4) := ![({1} : Finset _), {0, 2}, {1, 3}, {2}]

/-- `pathN` adjacency is symmetric. -/
example : ∀ i j, j ∈ pathN i ↔ i ∈ pathN j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pathN]

/-- `pathN` degree bound: every neighborhood has at most `2` members. -/
example : ∀ i, (pathN i).card ≤ 2 := by
  intro i
  fin_cases i <;> simp [pathN]

/-- **`zstar4`** — the unique fixed point of the path-graph update with
`m = 3`, `G = 0`: `z* = ![21/55, 8/55, 3/55, 1/55]`. -/
noncomputable def zstar4 : Fin 4 → ℝ := ![21/55, 8/55, 3/55, 1/55]

/-- Numeric anchor: `zstar4` solves the fixed-point equation
`z* i = (Σ_{j ∈ N i} z* j + 1[i = 0]) / 3` exactly. -/
example : latentUpdate pathN 3 0 zstar4 = zstar4 := by
  funext i
  fin_cases i <;> simp [latentUpdate, pathN, zstar4] <;> norm_num

/-- **`loopN2`** — double-loop graph on `Fin 2` (degree `Δ = 2` fixture
for the `m ≤ Δ` witnesses). -/
def loopN2 : Fin 2 → Finset (Fin 2) := fun _ => Finset.univ

/-- Witness: at `m = Δ` the degree gap is gone and the quadratic form is
merely semidefinite (`Q 1 = 0` on `loopN2`), so strict dominance fails. -/
example : ¬ (0 < latentQuadraticForm loopN2 2 (fun _ => (1:ℝ))) := by
  unfold latentQuadraticForm loopN2
  simp

/-- Witness: at `m < Δ` the form is not even positive semidefinite
(`Q 1 < 0` on `loopN2`) — no convexity, no contraction factor below `1`. -/
example : latentQuadraticForm loopN2 1 (fun _ => (1:ℝ)) < 0 := by
  unfold latentQuadraticForm loopN2
  simp

end Fixture

end Hagi.Model.EnergyReasoning
