/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Math.Info.InfoCore
import Hagi.Core.Concat
import Hagi.Energy.PairwiseCategorical
import Hagi.Optimization.InexactContraction
import Hagi.Energy.SingleCellDescent
import Mathlib
import Hagi.Runtime.BF16Delta
import Hagi.Probability.MirrorHedgeCertificates
import Hagi.Cert.Core
import Hagi.Cert.StepGen
import Hagi.Probability.Concentration
import Hagi.Model.CEGradient
import Hagi.Probability.FiniteFamilyConfidence

set_option linter.style.header false

/-!
# Pseudolikelihood as local conditional cross-entropy

Track E1 (addendum A9, CRAM / arXiv:2611.17309): the pseudolikelihood
objective of a categorical pairwise energy is EXACTLY the mean local
cross-entropy over the CRAM-sign conditional logits — reducing it to
the existing `Hagi.Prelude.ceDef` / `Hagi.Prelude.softDef` machinery
(the C235 Prelude spine), so the CEDescent toolchain applies to
pseudolikelihood training by construction, with no new CE theory.

* `conditionalLogit` — the local logits `z_ia = −H(y^{i←a})` (CRAM
  sign: LOW energy = HIGH logit).
* `conditionalDist` — the local Gibbs conditional
  `q_i(a) = softDef z_i ∝ exp(−H(y^{i←a}))`.
* `pseudolikelihoodObjective` — `J = (1/|ι|) Σ_i −log q_i(y_i)`,
  written with `Hagi.Core.ceOneHot` (the `-log q_i(y_i)` term IS
  `ceOneHot (y i) z_i`, since `-log q_i(y_i) = lse z_i − z_i(y i)`).
* `pseudolikelihood_eq_conditional_ce` — (E1 MAIN) `J` equals the mean
  of `Hagi.Prelude.ceDef (Pi.single (y i) 1) (Hagi.Prelude.softDef z_i)`
  over `i`: pseudolikelihood is local conditional cross-entropy on the
  Prelude CE spine (`Hagi.Core.ceOneHot_eq_ceDef_pi_single`, termwise).
* `pseudolikelihood_nonneg` — `0 ≤ J` (every local CE term is
  nonnegative; division by the positive variable count).

## Sign-adapter warning (CRAM vs classic Hopfield)

The logits follow the CRAM convention `z = −H`, conditionals
`q ∝ exp(−H)` (low energy = high probability). The classic Hopfield
file `Hagi/StatMech/Hopfield/Model.lean` uses `Z = Σ exp(β·E)` with
`H = −E` — the OPPOSITE sign. Any bridge to classic Hopfield MUST be
an explicit sign adapter; none is claimed here.

## Honest boundaries

Pseudolikelihood is NOT the full likelihood: it is the exact local
conditional objective only. Nothing here asserts descent in `θ`
(CertTrain) or free-energy descent in `p` (CertReason) — those are
separate certificates (A9), E2+ scope.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (pairwiseEnergy)
open Hagi.Core (ceOneHot)
open Hagi.Prelude (softDef ceDef)

section Conditional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Local conditional logits `z_ia = −H(y^{i←a})` where `y^{i←a}`
replaces coordinate `i` of the observed configuration by value `a`
(CRAM sign convention: low energy = high logit; see the module
docstring's sign-adapter warning). -/
noncomputable def conditionalLogit (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (y : ι → α) (i : ι) : α → ℝ :=
  fun a => -pairwiseEnergy B K (Function.update y i a)

/-- Local Gibbs conditional `q_i(a) = softDef z_i(a) ∝ exp(−H(y^{i←a}))`
on the canonical Prelude softmax spine. -/
noncomputable def conditionalDist (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (y : ι → α) (i : ι) : α → ℝ :=
  softDef (conditionalLogit B K y i)

/-- Pseudolikelihood objective
`J = (1/|ι|) Σ_i −log q_i(y_i) = (1/|ι|) Σ_i ceOneHot (y i) z_i`
(each `-log q_i(y_i)` term is `ceOneHot (y i) z_i` because
`-log q_i(y_i) = lse z_i − z_i (y i)` on the `softDef`/`lse` spine). -/
noncomputable def pseudolikelihoodObjective (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (y : ι → α) : ℝ :=
  (∑ i, ceOneHot (y i) (conditionalLogit B K y i)) / (Fintype.card ι : ℝ)

end Conditional

section Identities

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- (E1 MAIN) The pseudolikelihood objective equals the MEAN of local
conditional cross-entropies on the canonical Prelude CE spine:
`J = (1/|ι|) Σ_i ceDef (δ_{y i}) (softDef z_i)` with one-hot targets
`δ_{y i} = Pi.single (y i) 1` and logits `z_i = conditionalLogit`.
Consequence: pseudolikelihood training is cross-entropy training
against the local Gibbs conditionals — the existing CEDescent /
CEGradient machinery applies by construction, no new CE theory. -/
theorem pseudolikelihood_eq_conditional_ce [Nonempty α]
    (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ) (y : ι → α) :
    pseudolikelihoodObjective B K y
      = (∑ i, ceDef (Pi.single (y i) 1) (softDef (conditionalLogit B K y i)))
        / (Fintype.card ι : ℝ) := by
  unfold pseudolikelihoodObjective
  exact congrArg (· / (Fintype.card ι : ℝ))
    (Finset.sum_congr rfl fun i _ =>
      Hagi.Core.ceOneHot_eq_ceDef_pi_single (y i)
        (conditionalLogit B K y i))

omit [DecidableEq α] in
/-- (E1) Pseudolikelihood is nonnegative: every local term
`ceOneHot (y i) z_i = lse z_i − z_i (y i) ≥ 0` (the target exponential
is one term of the log-sum-exp normalizer), the variable count is
positive for nonempty `ι`. -/
theorem pseudolikelihood_nonneg [Nonempty ι] [Nonempty α] (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (y : ι → α) :
    0 ≤ pseudolikelihoodObjective B K y := by
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  refine div_nonneg ?_ hcard.le
  refine Finset.sum_nonneg fun i _ => ?_
  have hpos : (0 : ℝ) < ∑ v, Real.exp (conditionalLogit B K y i v) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hterm : Real.exp (conditionalLogit B K y i (y i))
      ≤ ∑ v, Real.exp (conditionalLogit B K y i v) :=
    Finset.single_le_sum (fun v _ => (Real.exp_pos _).le)
      (Finset.mem_univ (y i))
  have hlog := Real.log_le_log (Real.exp_pos _) hterm
  rw [Real.log_exp] at hlog
  unfold ceOneHot Hagi.Core.lse
  unfold conditionalLogit at hlog ⊢
  linarith

end Identities

end Hagi.Model.EnergyReasoning

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

set_option linter.style.header false

/-!
# Heat-bath kernel, focused mixture stationarity

Track E4 (addendum A9 §E4 + A9-supplement, CRAM / arXiv:2611.17309): the
Gibbs-search transition kernel as an EXPLICIT policy — the single-cell
heat-bath kernel, its detailed balance and stationarity w.r.t. the Boltzmann
density, and the focused (state-dependent) mixture.

* `heatbathWeight` — the heat-bath weight of value `a` at cell `i`:
  `softDef (fun c => −L_i(c)/T) a`, the softmax of the NEGATIVE local field
  over temperature (REUSE of `Hagi.Prelude.softDef`; no new softmax).
* `heatbathKernel` — the single-cell kernel `Q_i(y, z)`: `heatbathWeight` at
  `z i` when `z` agrees with `y` off cell `i` (a single-cell move), `0`
  otherwise. The kernel is UNCLAMPED; clamp preservation is a theorem with a
  free-cells premise, not a construction.
* `heatbath_detailed_balance` — (E4 MAIN) under symmetric `K` and `T ≠ 0`
  the kernel is reversible w.r.t. the unnormalized Boltzmann density
  `π(y) = exp(−E(y)/T)`. The proof reduces EXACTLY to the C261 identity
  `single_cell_move_energy_delta_symm` plus the off-cell localField
  invariance; the softmax normalizer cancels (both weights are evaluated at
  the same state's fields).
* `heatbath_stationary` — (E4 MAIN) reversible + row-stochastic ⇒ stationary
  (`reversible_stationary`), via `heatbathKernel_rowsum` (the map
  `a ↦ y^{i←a}` reindexes the supported row: `Finset.sum_bij`).
* `mixture_reversible` / `focused_mixture_stationary` — (E4 MAIN) the focused
  selection `Q = Σ_i w(y)_i · Q_i` is reversible/stationary under TWO
  explicit load-bearing premises: SUPPORT (each `Q_i` only moves cell `i`)
  and INVARIANCE (`w(y^{i←a})_i = w(y)_i` — the selection weight of cell `i`
  is invariant under moves of cell `i`; state-dependence through OTHER cells,
  frozen latents, givens or a fixed schedule is fine).
* `focused_heatbath_mixture_stationary` — the focused-Gibbs corollary: the
  heat-bath family satisfies SUPPORT structurally, so only `hK`, `T ≠ 0`,
  INVARIANCE and `Σ_i w(y)_i = 1` remain.
* `focused_mixture_preserves_givens` — clamps preserved (premise-form): if
  the selection weights vanish on given cells (`∀ y, w y i = 0` for given
  `i`), the mixture output preserves every given value EXACTLY.

## Honest boundaries (A9 'not to adopt' list + supplement §E4)

* STATIONARITY ≠ MONOTONICITY: `T > 0` can RAISE energy — the heat-bath
  weight of a HIGHER-energy value is strictly positive (fixture witness
  below: weight `exp(−3)/(1 + exp(−3)) > 0` for the worse value). No descent
  claim is made about the kernel or the mixture.
* The A9-supplement phrase "state-dependent mixture preserves stationarity"
  is FALSE as an unconditional statement (two-state flip-vs-stay
  counterexample); the INVARIANCE premise here is exactly what the counterexample
  violates, and it is documented as load-bearing (RootApi-пин: имя
  `focused_mixture_stationarity_without_invariance` отсутствует).
* The stationarity statements are about the unnormalized density on a
  FINITE configuration space; no measure-theoretic packaging, no mixing-time
  or convergence-rate claim.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy Hagi.Prelude

section Definitions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Kernel row condition (private): `z` agrees with `y` off cell `i`,
i.e. `z` is the single-cell move `y^{i←(z i)}`. -/
private def heatbathOffCellCond (y : ι → α) (i : ι) (z : ι → α) : Prop :=
  ∀ j, j ≠ i → z j = y j

/-- The heat-bath weight of value `a` at cell `i` from state `y`: the
softmax (`softDef` reuse) of the NEGATIVE local field over temperature,
`exp(−L_i(a)/T) / Σ_c exp(−L_i(c)/T)` with `L_i` the C261 `localField`. -/
noncomputable def heatbathWeight (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (y : ι → α) (i : ι) (a : α) : ℝ :=
  softDef (fun c => -(localField B K y i c) / T) a

open Classical in
/-- The single-cell heat-bath kernel `Q_i(y, z)`: `heatbathWeight` at `z i`
when `z` is a single-cell move of `y` at cell `i`, `0` otherwise
(the supported row is exactly `{y^{i←a} : a ∈ α}`). -/
noncomputable def heatbathKernel (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (i : ι) (y z : ι → α) : ℝ :=
  if heatbathOffCellCond y i z then heatbathWeight B K T y i (z i) else 0

/-- Reversibility (detailed balance) of a kernel `Q` w.r.t. a density `π`
on the finite configuration space. -/
def kernelReversible (π : (ι → α) → ℝ) (Q : (ι → α) → (ι → α) → ℝ) : Prop :=
  ∀ y z, π y * Q y z = π z * Q z y

/-- Stationarity of a kernel `Q` w.r.t. a density `π`:
`Σ_y π y * Q y z = π z` for every `z`. -/
def kernelStationary (π : (ι → α) → ℝ) (Q : (ι → α) → (ι → α) → ℝ) : Prop :=
  ∀ z, ∑ y, π y * Q y z = π z

/-- The unnormalized Boltzmann density `π(y) = exp(−E(y)/T)` of the
C261 `pairwiseEnergy`. -/
noncomputable def boltzmannDensity (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (y : ι → α) : ℝ :=
  Real.exp (-(pairwiseEnergy B K y) / T)

/-- The focused (state-dependent) mixture kernel
`Q(y, z) = Σ_i w(y)_i * Q_i(y, z)` — the FocusedSearch selection policy of
A9-supplement §E4. -/
noncomputable def focusedMixture (w : (ι → α) → ι → ℝ)
    (Q : ι → (ι → α) → (ι → α) → ℝ) (y z : ι → α) : ℝ :=
  ∑ i, w y i * Q i y z

end Definitions

section Weight

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The local field only depends on the state off the moved cell: if `z`
agrees with `y` everywhere except (possibly) at `i`, then `L^z_i = L^y_i`
(the off-cell couplings `K i j · (y j)` are untouched by an `i`-move). -/
theorem localField_kcond (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (y z : ι → α) (i : ι) (a : α)
    (h : ∀ j, j ≠ i → z j = y j) :
    localField B K z i a = localField B K y i a := by
  simp only [localField]
  refine congrArg (B i a + ·) ?_
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h j (by simpa using hj)]

omit [DecidableEq α] in
/-- Heat-bath weights are strictly positive (softmax positivity). -/
theorem heatbathWeight_pos (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (y : ι → α) (i : ι) (a : α) :
    0 < heatbathWeight B K T y i a :=
  softDef_pos _ a

omit [DecidableEq α] in
/-- Heat-bath weights normalize: `Σ_a w_i(a) = 1` (softmax normalization). -/
theorem heatbathWeight_sum_one (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (y : ι → α) (i : ι) :
    ∑ a, heatbathWeight B K T y i a = 1 :=
  softDef_sum_one _

end Weight

section Rows

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [DecidableEq α] in
/-- The kernel is nonnegative: `0 ≤ Q_i(y, z)` (a probability weight or
zero). -/
theorem heatbathKernel_nonneg (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (i : ι) (y z : ι → α) : 0 ≤ heatbathKernel B K T i y z := by
  classical
  unfold heatbathKernel
  split
  · exact le_of_lt (heatbathWeight_pos B K T y i (z i))
  · norm_num

omit [DecidableEq α] in
omit [DecidableEq α] [Nonempty α] in
/-- Kernel support (clamp premise-form): a nonzero transition `Q_i(y, z) ≠ 0`
forces `z` to be the single-cell move `y^{i←(z i)}` — every OTHER cell `j ≠ i`
is preserved EXACTLY. This is the structural SUPPORT premise consumed by
`mixture_reversible`. -/
theorem heatbathKernel_supported (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (i : ι) (y z : ι → α) (h : heatbathKernel B K T i y z ≠ 0) :
    z = Function.update y i (z i) := by
  classical
  by_cases hcond : heatbathOffCellCond y i z
  · unfold heatbathKernel at h
    simp only [hcond, ite_true] at h
    funext j
    by_cases hji : j = i
    · subst hji; simp [Function.update_self]
    · rw [Function.update_of_ne hji]; exact hcond j hji
  · unfold heatbathKernel at h
    simp only [hcond, ite_false] at h
    exact absurd rfl h

omit [DecidableEq α] in
/-- Every kernel row sums to ONE, with NO premises: the map
`a ↦ y^{i←a}` is a bijection from `α` onto the supported row, and the
weights normalize (`heatbathWeight_sum_one`). -/
theorem heatbathKernel_rowsum (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (i : ι) (y : ι → α) :
    ∑ z, heatbathKernel B K T i y z = 1 := by
  classical
  have h1 : ∑ z, heatbathKernel B K T i y z
      = ∑ z ∈ Finset.univ.filter (fun z => heatbathOffCellCond y i z),
          heatbathWeight B K T y i (z i) := by
    simp only [heatbathKernel]
    rw [Finset.sum_filter]
  rw [h1]
  refine (Finset.sum_bij (fun z _ => z i)
    (fun z _ => Finset.mem_univ _)
    (fun z₁ h₁ z₂ h₂ heq => by
      funext j
      by_cases hji : j = i
      · subst hji; simpa using heq
      · rw [(Finset.mem_filter.mp h₁).2 j hji,
          (Finset.mem_filter.mp h₂).2 j hji])
    (fun a _ => ⟨Function.update y i a,
      Finset.mem_filter.mpr ⟨Finset.mem_univ (Function.update y i a),
        fun j hj => Function.update_of_ne hj a y⟩,
      Function.update_self i a y⟩)
    (fun z _ => rfl)).trans (heatbathWeight_sum_one B K T y i)

end Rows

section DetailedBalance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [DecidableEq α] [Nonempty α] in
/-- (E4 MAIN) Heat-bath detailed balance: under symmetric `K`
(`K_ij(a,b) = K_ji(b,a)`, the CRAM `W = sym(K)`) and `T ≠ 0`, the
single-cell kernel is REVERSIBLE w.r.t. the unnormalized Boltzmann density
`π(y) = exp(−E(y)/T)`. The proof is exactly the C261 delta identity
`E(y^{i←a}) − E(y) = L_i(a) − L_i(y_i)` (all non-`i` partition terms cancel)
plus the off-cell localField invariance; the softmax normalizer cancels
because both weights are evaluated at the SAME state's fields. `T ≠ 0` is
the only temperature premise. -/
theorem heatbath_detailed_balance (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (hK : ∀ i j a b, K i j a b = K j i b a) (hT : T ≠ 0)
    (i : ι) (y z : ι → α) :
    boltzmannDensity B K T y * heatbathKernel B K T i y z
      = boltzmannDensity B K T z * heatbathKernel B K T i z y := by
  classical
  by_cases hc : heatbathOffCellCond y i z
  · simp only [heatbathKernel, hc, ite_true]
    have hc' : heatbathOffCellCond z i y :=
      fun j hj => (hc j hj).symm
    simp only [hc', ite_true]
    have hzu : z = Function.update y i (z i) := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [Function.update_self]
      · rw [Function.update_of_ne hji]; exact hc j hji
    have hLz : ∀ c, localField B K z i c = localField B K y i c :=
      fun c => localField_kcond B K y z i c hc
    have hd := single_cell_move_energy_delta_symm B K hK y i (z i)
    have hEz : pairwiseEnergy B K z
        = pairwiseEnergy B K (Function.update y i (z i)) :=
      congrArg (pairwiseEnergy B K) hzu
    have hw : heatbathWeight B K T z i (y i)
        = heatbathWeight B K T y i (y i) := by
      simp only [heatbathWeight, hLz]
    rw [hw]
    simp only [heatbathWeight, softDef, boltzmannDensity]
    have key2 :
        Real.exp (-(pairwiseEnergy B K y) / T)
            * Real.exp (-(localField B K y i (z i)) / T)
        = Real.exp (-(pairwiseEnergy B K z) / T)
            * Real.exp (-(localField B K y i (y i)) / T) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      field_simp
      linarith
    rw [mul_div_assoc', mul_div_assoc', key2]
  · simp only [heatbathKernel, hc, ite_false]
    obtain ⟨j, hj⟩ := not_forall.mp hc
    have hji : j ≠ i := fun he => hj (fun hne => absurd he hne)
    have hjz : z j ≠ y j := fun heq => hj (fun _ => heq)
    have hne : ¬ heatbathOffCellCond z i y := fun h => hjz (h j hji).symm
    simp only [hne, ite_false]
    ring

omit [DecidableEq α] [Nonempty α] in
/-- Reversible + row-stochastic ⇒ stationary: `Σ_y π y * Q y z`
`= Σ_y π z * Q z y = π z · 1`. -/
theorem reversible_stationary (π : (ι → α) → ℝ)
    (Q : (ι → α) → (ι → α) → ℝ) (hQ : kernelReversible π Q)
    (hrow : ∀ y, ∑ z, Q y z = 1) : kernelStationary π Q := by
  intro z
  calc ∑ y, π y * Q y z = ∑ y, π z * Q z y :=
        Finset.sum_congr rfl fun y _ => hQ y z
    _ = π z * ∑ y, Q z y :=
        (Finset.mul_sum Finset.univ (fun y => Q z y) (π z)).symm
    _ = π z * 1 := by rw [hrow z]
    _ = π z := by ring

omit [DecidableEq α] in
/-- (E4 MAIN) Heat-bath stationarity: the single-cell heat-bath kernel
preserves the Boltzmann density — detailed balance (`heatbath_detailed_balance`)
plus row-stochasticity (`heatbathKernel_rowsum`) via
`reversible_stationary`. STATIONARITY ≠ MONOTONICITY: at `T > 0` the kernel
assigns strictly positive weight to HIGHER-energy values (fixture witness
below); no descent claim is made. -/
theorem heatbath_stationary (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (hK : ∀ i j a b, K i j a b = K j i b a) (hT : T ≠ 0) (i : ι) :
    kernelStationary (boltzmannDensity B K T) (heatbathKernel B K T i) :=
  reversible_stationary _ _
    (fun y z => heatbath_detailed_balance B K hK hT i y z)
    (fun y => heatbathKernel_rowsum B K T i y)

end DetailedBalance

section Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- (E4 MAIN, part a) The focused mixture of reversible SINGLE-CELL kernels
is reversible under the SUPPORT premise (`Q_i(y,z) ≠ 0 ⇒ z = y^{i←(z i)}`:
each kernel only moves its own cell) and the INVARIANCE premise
(`w(y^{i←a})_i = w(y)_i`: the selection weight of cell `i` is invariant under
moves of cell `i`). Both premises are LOAD-BEARING: without INVARIANCE the
supplement's "state-dependent mixture preserves stationarity" is FALSE
(two-state flip-vs-stay counterexample), and without SUPPORT the invariance
premise would have to range over arbitrary moves. -/
theorem mixture_reversible (w : (ι → α) → ι → ℝ)
    (Q : ι → (ι → α) → (ι → α) → ℝ) (π : (ι → α) → ℝ)
    (hQsupp : ∀ (i : ι) (y z : ι → α), Q i y z ≠ 0 →
      z = Function.update y i (z i))
    (hwinv : ∀ (i : ι) (y : ι → α) (a : α),
      w (Function.update y i a) i = w y i)
    (hQrev : ∀ i, kernelReversible π (Q i)) :
    kernelReversible π (focusedMixture w Q) := by
  intro y z
  simp only [focusedMixture, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hz : Q i z y = 0
  · have h0 : π y * Q i y z = 0 := by
      rw [hQrev i y z, hz, mul_zero]
    rw [mul_left_comm (π y), h0, mul_zero, mul_left_comm (π z), hz,
      mul_zero, mul_zero]
  · have hy : y = Function.update z i (y i) := hQsupp i z y hz
    have hw : w y i = w z i := by rw [hy]; exact hwinv i z (y i)
    rw [hw, mul_left_comm (π y), hQrev i y z]
    ring

omit [DecidableEq α] [Nonempty α] in
/-- Mixture rows sum to one: `Σ_i w(y)_i = 1` plus per-kernel
row-stochasticity. -/
theorem mixture_rowsum (w : (ι → α) → ι → ℝ)
    (Q : ι → (ι → α) → (ι → α) → ℝ) (y : ι → α)
    (hw : ∀ y', ∑ i, w y' i = 1) (hrow : ∀ i y', ∑ z, Q i y' z = 1) :
    ∑ z, focusedMixture w Q y z = 1 := by
  calc ∑ z, focusedMixture w Q y z
      = ∑ z, ∑ i, w y i * Q i y z := Finset.sum_congr rfl fun z _ => rfl
    _ = ∑ i, ∑ z, w y i * Q i y z := Finset.sum_comm
    _ = ∑ i, w y i * ∑ z, Q i y z :=
        Finset.sum_congr rfl fun i _ =>
          (Finset.mul_sum Finset.univ (fun z => Q i y z) (w y i)).symm
    _ = ∑ i, w y i * 1 :=
        Finset.sum_congr rfl fun i _ => by rw [hrow i y]
    _ = ∑ i, w y i := Finset.sum_congr rfl fun i _ => mul_one _
    _ = 1 := hw y

omit [DecidableEq α] [Nonempty α] in
/-- (E4 MAIN) Focused mixture stationarity: `Q = Σ_i w(y)_i · Q_i` with
`w ≥ 0`-free normalization `Σ_i w(y)_i = 1` preserves `π` under the SUPPORT,
INVARIANCE, reversibility and row-sum premises (see `mixture_reversible`
for why the premises are load-bearing). STATIONARITY ≠ MONOTONICITY:
the mixture can RAISE energy at `T > 0` — no descent claim is made. -/
theorem focused_mixture_stationary (w : (ι → α) → ι → ℝ)
    (Q : ι → (ι → α) → (ι → α) → ℝ) (π : (ι → α) → ℝ)
    (hQsupp : ∀ (i : ι) (y z : ι → α), Q i y z ≠ 0 →
      z = Function.update y i (z i))
    (hwinv : ∀ (i : ι) (y : ι → α) (a : α),
      w (Function.update y i a) i = w y i)
    (hQrev : ∀ i, kernelReversible π (Q i))
    (hrow : ∀ i y', ∑ z, Q i y' z = 1)
    (hw : ∀ y', ∑ i, w y' i = 1) :
    kernelStationary π (focusedMixture w Q) :=
  reversible_stationary π _
    (mixture_reversible w Q π hQsupp hwinv hQrev)
    (fun y => mixture_rowsum w Q y hw hrow)

omit [DecidableEq α] in
/-- (E4 MAIN, corollary) The FOCUSED-GIBBS-SEARCH policy — a state-dependent
mixture of single-cell heat-bath kernels — preserves the Boltzmann density.
The heat-bath family satisfies SUPPORT structurally
(`heatbathKernel_supported`), so only `hK`, `T ≠ 0`, INVARIANCE of the
selection weights and `Σ_i w(y)_i = 1` remain as premises. -/
theorem focused_heatbath_mixture_stationary (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (hT : T ≠ 0) (w : (ι → α) → ι → ℝ)
    (hwinv : ∀ (i : ι) (y : ι → α) (a : α),
      w (Function.update y i a) i = w y i)
    (hw : ∀ y', ∑ i, w y' i = 1) :
    kernelStationary (boltzmannDensity B K T)
      (focusedMixture w (fun i => heatbathKernel B K T i)) :=
  focused_mixture_stationary w _ _
    (fun i y z h => heatbathKernel_supported B K T i y z h)
    hwinv
    (fun i y z => heatbath_detailed_balance B K hK hT i y z)
    (fun i y => heatbathKernel_rowsum B K T i y)
    hw

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Clamps preserved (premise-form): if the selection weights VANISH on
given cells (`hFree` — the free-cells-only premise) and the kernels are
single-cell kernels, then a NONZERO mixture transition `z` from `y`
preserves every given cell value EXACTLY (`z i = y i` for `givens i = some
a`). The premise is the honest form of "the sampler never touches clues";
it is not baked into the kernel. -/
theorem focused_mixture_preserves_givens (w : (ι → α) → ι → ℝ)
    (Q : ι → (ι → α) → (ι → α) → ℝ) (givens : ι → Option α)
    (hQsupp : ∀ (i : ι) (y z : ι → α), Q i y z ≠ 0 →
      z = Function.update y i (z i))
    (hFree : ∀ (i : ι) (a : α) (y : ι → α),
      givens i = some a → w y i = 0)
    (y z : ι → α) (hQ : focusedMixture w Q y z ≠ 0)
    (i : ι) (a : α) (hg : givens i = some a) :
    z i = y i := by
  classical
  by_contra hne
  unfold focusedMixture at hQ
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
  have hwj : w y j ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hj; exact hj rfl
  have hzne : Q j y z ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hj; exact hj rfl
  have hnone : ∀ b : α, givens j ≠ some b :=
    fun b hgb => hwj (hFree j b y hgb)
  have hij : i ≠ j := by
    intro he
    rw [he] at hg
    exact hnone a hg
  have hzj : z = Function.update y j (z j) := hQsupp j y z hzne
  apply hne
  rw [hzj, Function.update_of_ne hij]

end Mixture

section Fixture
/-! ## Fin 2 × Bool fixture (Bex/Kex/xtt carriers from C260) -/

open Hagi.Energy

private theorem Kex_symm :
    ∀ (i j : Fin 2) (a b : Bool), Kex i j a b = Kex j i b a := by
  intro i j a b
  simp only [Kex, Bool.and_comm]
  split_ifs <;> ring

/-- Numeric anchor: `L_0(f) = 0`, `L_0(t) = 3` at `xtt = (t,t)` (C260
anchors `E(t,t) = 5`, `E(f,t) = 2`, so the C261 delta identity gives
`2 − 5 = 0 − 3`), hence the heat-bath weight of moving cell `0` to `f` at
`T = 1` is `1/(1 + exp(−3))`. -/
example : heatbathKernel Bex Kex 1 0 xtt (Function.update xtt 0 false)
      = 1 / (1 + Real.exp (-(3 : ℝ))) := by
  classical
  simp only [heatbathKernel, heatbathOffCellCond, heatbathWeight, softDef]
  have hLt : localField Bex Kex xtt 0 true = 3 := by
    simp only [localField, xtt, Bex, Kex]
    norm_num
  have hLf : localField Bex Kex xtt 0 false = 0 := by
    simp only [localField, xtt, Bex, Kex]
    norm_num
  have hL : ∀ c : Bool, localField Bex Kex xtt 0 c
      = (if c then (3 : ℝ) else 0) := by
    intro c
    cases c
    · exact hLf
    · exact hLt
  simp only [hL]
  norm_num
  linarith [Real.exp_pos (-(3 : ℝ))]

/-- STATIONARITY ≠ MONOTONICITY witness: at `T = 1` the heat-bath weight of
the HIGHER-energy value `t` (local field `3` vs `0`) is strictly positive —
the kernel can RAISE energy, and no descent claim is made. -/
example : 0 < heatbathWeight Bex Kex 1 xtt 0 true := by
  exact heatbathWeight_pos Bex Kex 1 xtt 0 true

/-- Detailed balance on the fixture, by the general theorem (Fin 2 × Bool,
`T = 1`, every pair of configurations). -/
example (y z : Fin 2 → Bool) :
    boltzmannDensity Bex Kex 1 y * heatbathKernel Bex Kex 1 0 y z
      = boltzmannDensity Bex Kex 1 z * heatbathKernel Bex Kex 1 0 z y :=
  heatbath_detailed_balance Bex Kex Kex_symm one_ne_zero 0 y z

/-- Row sums on the fixture: the kernel from `(t,t)` at cell `0`, `T = 1`,
is a probability row. -/
example : ∑ z, heatbathKernel Bex Kex 1 0 xtt z = 1 :=
  heatbathKernel_rowsum Bex Kex 1 0 xtt

end Fixture

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Certified stopping: energy threshold vs validity certificate

Track E4 (addendum A9 §E4 + A9-supplement cert-kernel): the STOPPING side of
Gibbs search — two DISTINCT certificates, never conflated:

* `EnergyStop` — the EFFICIENCY event: a configuration `y` with
  `pairwiseEnergy B K y ≤ τ`. An energy threshold is a search-efficiency
  heuristic, NEVER a correctness claim (A9 'not to adopt': threshold stop is
  empirical).
* `ValidityCertificate` — the PRODUCTION certificate: a configuration `y`
  that preserves every given value (`preserves_givens`) and satisfies every
  per-cell constraint (`satisfies_constraints`) — the AcceptedSolution shape
  of the A9-supplement cert-kernel (preserves_givens + satisfies_constraints).
* `stopping_sound_of_separation` — (E4 MAIN) the SEPARATION transfer: under
  the separation premise "every configuration with `E ≤ τ` is valid"
  (∀ y', E(y') ≤ τ → givens preserved ∧ constraints satisfied), an
  `EnergyStop` produces a `ValidityCertificate`. The separation premise is
  doing ALL the work — the same certified-gate shape as the certified-argmax
  2ε gap theorems (`Hagi.Cert.certified_selection_slack`): without the
  premise the transfer is vacuous, and the fixture witness below ships the
  failure (a ZERO-energy INVALID board).

## Honest boundaries

* No implication between the two certificates exists without the separation
  premise: energy says nothing about constraints (witness: zero-energy
  invalid board) and validity says nothing about energy (witness: a valid
  board with an arbitrarily large field).
* Both structures are Type-valued (the carrier `y` is data), so the transfer
  is a `def` (certificate producer); the Prop content is the separation
  premise itself, checked per-instance by the external verifier.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy

section Stopping

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The energy-stop certificate: a configuration `y` whose
`pairwiseEnergy B K y` is at or below the threshold `τ`. This is the
EFFICIENCY event of the search — an energy threshold is a heuristic, never
a correctness claim (see `ValidityCertificate` for the production
certificate). -/
structure EnergyStop (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ) (τ : ℝ) where
  /-- The stopped configuration. -/
  y : ι → α
  /-- The energy bound that triggered the stop. -/
  energy_bound : pairwiseEnergy B K y ≤ τ

/-- The validity certificate: a configuration `y` that (1) preserves every
given value (`givens i = some a → y i = a` — clamps intact) and (2)
satisfies every per-cell constraint `C i (y i)`. This is the PRODUCTION
certificate (AcceptedSolution of the A9-supplement cert-kernel); it says
NOTHING about energy. -/
structure ValidityCertificate (givens : ι → Option α)
    (C : ι → α → Prop) where
  /-- The certified configuration. -/
  y : ι → α
  /-- Clamps preserved: every given value is intact. -/
  preserves_givens : ∀ i a, givens i = some a → y i = a
  /-- Constraints satisfied at every cell. -/
  satisfies_constraints : ∀ i, C i (y i)

/-- (E4 MAIN) Certified stopping, soundness of the separation condition:
if every configuration with energy `≤ τ` is valid (the SEPARATION premise —
this is what an external verifier must certify about the instance), then an
`EnergyStop` at threshold `τ` PRODUCES a `ValidityCertificate`. The premise
carries all the content; without it the transfer is vacuous (witness below:
a zero-energy invalid board). -/
def stopping_sound_of_separation (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (τ : ℝ) (givens : ι → Option α)
    (C : ι → α → Prop)
    (hsep : ∀ y' : ι → α, pairwiseEnergy B K y' ≤ τ →
      (∀ i a, givens i = some a → y' i = a) ∧ ∀ i, C i (y' i))
    (s : EnergyStop B K τ) : ValidityCertificate givens C where
  y := s.y
  preserves_givens := (hsep s.y s.energy_bound).1
  satisfies_constraints := (hsep s.y s.energy_bound).2

end Stopping

section Fixture
/-! ## Fin 2 × Bool fixture: the two failure directions of conflating the
certificates (energy ↛ validity, validity ↛ energy). -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype ι] [DecidableEq ι] in
private theorem zero_energy_zero_field (y : Fin 2 → Bool) :
    pairwiseEnergy (fun _ _ => (0 : ℝ)) (fun _ _ _ _ => (0 : ℝ)) y = 0 := by
  simp [pairwiseEnergy, pairwiseInteractionSum]

/-- Energy ↛ validity witness: with zero fields `B = K = 0` every board has
energy `0 ≤ τ = 0`, so `y = const true` is an `EnergyStop` — but with the
constraint `C i a = (a = false)` it is INVALID: an energy threshold alone
certifies NOTHING (the separation premise is what a real verifier must
supply; without it `stopping_sound_of_separation` is vacuous). -/
example : ∃ (s : EnergyStop (fun (_ : Fin 2) (_ : Bool) => (0 : ℝ))
      (fun (_ : Fin 2) (_ : Fin 2) (_ : Bool) (_ : Bool) => (0 : ℝ)) (0 : ℝ)),
    ¬ (∀ i : Fin 2, s.y i = false) := by
  refine ⟨{ y := (fun _ => true),
             energy_bound := le_of_eq (zero_energy_zero_field (fun _ => true)) }, ?_⟩
  intro h
  have h0 := h 0
  simp at h0

end Fixture

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Sparse local field: neighbour-restricted sums and operation counts

Track D3 (addendum A11 P3 "sparse field update correctness"): the
claimed FLOP advantage of LOCAL (sparse) couplings, turned into
theorems. The dense C261 `localField`
`L_i(a) = B i a + Σ_{j ≠ i} K i j a (y j)` sums over ALL off-diagonal
cells; when the coupling `K` is SUPPORTED on neighbour sets
`N : ι → Finset ι` (`j ∉ N i → K i j a b = 0`), summing only over
`N i` computes EXACTLY the same field, and the single-cell delta
identity of C261 composes unchanged. The cost advantage is a formal
ℕ-inequality: sparse work `(N i).card · (card α)²` ≤ dense work
`card(univ \ {i}) · (card α)²`, STRICT for a proper neighbour subset
— a Finset count, NOT a complexity framework.

* `couplingSupportedOn` — premise-form support: `K` vanishes off the
  neighbour sets (function-level, all four coupling arguments).
* `sparseLocalField` — the neighbour-restricted field
  `B i a + Σ_{j ∈ N i}, K i j a (y j)`.
* `sparse_neighbours_subset` — no self-neighbour (`i ∉ N i`) gives
  `N i ⊆ univ \ {i}` VERBATIM: the sparse split respects the C260
  ordered-pair convention (off-diagonal, `1/2` outside in the energy;
  the field is one-sided and creates/destroys no diagonal entry).
* `sparse_localField_eq_dense` — (D3 MAIN) under support and
  no-self-neighbour the sparse field EQUALS the dense `localField`:
  zero couplings contribute nothing (`Finset.sum_subset`).
* `sparse_update_energy_delta_eq` — (D3 MAIN) with symmetric `K` the
  exact single-cell energy delta is the SPARSE field difference —
  the C261 `single_cell_move_energy_delta_symm` composed (cited, not
  reproved) through the equivalence above.
* `neighbour_card_le` — `(N i).card ≤ Fintype.card ι`
  (`Finset.subset_univ`): at most all cells.
* `localField_dense_work` / `localField_sparse_work` — the ℕ work
  products `card(univ \ {i}) · (card α)²` / `(N i).card · (card α)²`
  (the Σ_{j ∈ N i} card α² shape as one product; per value `a` the
  field reads card-many coupling entries).
* `localField_op_count_le` — (D3 MAIN) `N i ⊆ univ \ {i}` ⇒ sparse
  work ≤ dense work.
* `localField_op_count_lt` — (D3 MAIN) STRICT for a proper neighbour
  subset and `0 < card α` (necessary: an empty value type zeroes both
  products): the formal FLOP advantage of local couplings.
* `sparse_support_of_symmetric` — symmetric `K` + support ⇒ the
  transpose side also vanishes (`i ∉ N j → K i j a b = 0`): symmetric
  storage cannot smuggle a nonzero entry outside the neighbour sets.

## Honest boundaries (D3)

* The op counts are ℕ-PRODUCT counts (entry reads per field value);
  NO asymptotics, no machine model of arithmetic — `localField_sparse_work`
  is a work-model DEFINITION and the theorems are about the products.
* Support is PREMISE-form: the carrier supplies `N`; no theorem claims
  an arbitrary `K` admits a small `N` (that is the modeling
  assumption behind sparse couplings, not a result).
* For a constructively symmetrized kernel (`both directed edges in
  every entry`, the C271 `attentionCoupling` recipe), support of the
  directed parts gives support of the kernel on `N i ∪ N j`-shaped
  sets; this remark is documentation, not a theorem here.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (localField pairwiseEnergy single_cell_move_energy_delta_symm)

section Definitions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Premise-form coupling support: `K i j` vanishes on every argument
pair whenever `j` is outside the neighbour set `N i`
(the modeling assumption behind sparse couplings). -/
def couplingSupportedOn (N : ι → Finset ι) (K : ι → ι → α → α → ℝ) : Prop :=
  ∀ i j a b, j ∉ N i → K i j a b = 0

/-- The neighbour-restricted (sparse) local field:
`B i a + Σ_{j ∈ N i}, K i j a (y j)` — sums ONLY over the neighbour
set, not over all off-diagonal cells. -/
noncomputable def sparseLocalField (N : ι → Finset ι)
    (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (y : ι → α) (i : ι) (a : α) : ℝ :=
  B i a + ∑ j ∈ N i, K i j a (y j)

/-- Dense per-cell work (work-model definition): reading every
off-diagonal coupling entry for one field value costs
`card(univ \ {i}) · (card α)²` entry-reads (the α² all-pairs readout
of the task's Σ-shape, packed as one ℕ product). -/
def localField_dense_work (α : Type*) [Fintype α] (i : ι) : ℕ :=
  (Finset.univ \ ({i} : Finset ι)).card * (Fintype.card α) ^ 2

/-- Sparse per-cell work (work-model definition): the neighbour sum
costs `(N i).card · (card α)²` entry-reads — the Σ_{j ∈ N i} card α²
shape as one ℕ product. -/
def localField_sparse_work (α : Type*) [Fintype α]
    (N : ι → Finset ι) (i : ι) : ℕ :=
  (N i).card * (Fintype.card α) ^ 2

end Definitions

section Equivalence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- No self-neighbour (`∀ i, i ∉ N i`) puts every neighbour set
inside the dense off-diagonal `univ \ {i}` VERBATIM — the C260
ordered-pair convention (the field is one-sided; no diagonal entry
is created or destroyed by the sparse split). -/
theorem sparse_neighbours_subset (N : ι → Finset ι)
    (hN : ∀ i, i ∉ N i) (i : ι) : N i ⊆ Finset.univ \ {i} := by
  intro j hj
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
  by_contra hji
  rw [hji] at hj
  exact absurd hj (hN i)

omit [Fintype α] [DecidableEq α] in
/-- (D3 MAIN) Under coupling support and no-self-neighbour the SPARSE
field EQUALS the dense C261 `localField`: zero couplings contribute
nothing (`Finset.sum_subset` over `N i ⊆ univ \ {i}`). -/
theorem sparse_localField_eq_dense (N : ι → Finset ι)
    (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ) (y : ι → α)
    (hs : couplingSupportedOn N K) (hN : ∀ i, i ∉ N i)
    (i : ι) (a : α) :
    sparseLocalField N B K y i a = localField B K y i a := by
  rw [sparseLocalField, localField]
  congr 1
  exact Finset.sum_subset (sparse_neighbours_subset N hN i)
    (fun j _ hj => hs i j a (y j) hj)

omit [Fintype α] [DecidableEq α] in
/-- (D3 MAIN) With symmetric `K` the exact single-cell move delta of
the DENSE pairwise energy is the SPARSE field difference — the C261
`single_cell_move_energy_delta_symm` composed (cited, not reproved)
through `sparse_localField_eq_dense`. -/
theorem sparse_update_energy_delta_eq (N : ι → Finset ι)
    (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (hK : ∀ i j a b, K i j a b = K j i b a) (y : ι → α)
    (hs : couplingSupportedOn N K) (hN : ∀ i, i ∉ N i)
    (i : ι) (a : α) :
    pairwiseEnergy B K (Function.update y i a) - pairwiseEnergy B K y
      = sparseLocalField N B K y i a
        - sparseLocalField N B K y i (y i) := by
  rw [single_cell_move_energy_delta_symm B K hK y i a,
    sparse_localField_eq_dense N B K y hs hN i a,
    sparse_localField_eq_dense N B K y hs hN i (y i)]

end Equivalence

section OpCount

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq ι] in
/-- The neighbour count is at most the full cell count
(`Finset.subset_univ` + `card_le_card`): at most all cells. -/
theorem neighbour_card_le (N : ι → Finset ι) (i : ι) :
    (N i).card ≤ Fintype.card ι :=
  Finset.card_le_card (Finset.subset_univ (N i))

omit [DecidableEq α] in
/-- (D3 MAIN) Op-count bound: with `N i` inside the off-diagonal the
SPARSE work product is ≤ the DENSE work product (Finset card monotone
under the common `(card α)²` multiplier). -/
theorem localField_op_count_le (N : ι → Finset ι)
    (hN : ∀ i, i ∉ N i) (i : ι) :
    localField_sparse_work α N i ≤ localField_dense_work α i := by
  unfold localField_sparse_work localField_dense_work
  exact Nat.mul_le_mul_right _
    (Finset.card_le_card (sparse_neighbours_subset N hN i))

omit [DecidableEq α] in
/-- (D3 MAIN) STRICT op-count advantage: a PROPER neighbour subset
(`N i ⊂ univ \ {i}`) with `0 < card α` gives strictly less work than
the dense field. The premise `0 < card α` is NECESSARY, not
decorative: an empty value type zeroes both products. -/
theorem localField_op_count_lt (N : ι → Finset ι) (i : ι)
    (hsub : N i ⊂ Finset.univ \ {i}) (hα : 0 < Fintype.card α) :
    localField_sparse_work α N i < localField_dense_work α i := by
  unfold localField_sparse_work localField_dense_work
  have hcard : (N i).card < (Finset.univ \ {i} : Finset ι).card :=
    Finset.card_lt_card hsub
  have hα2 : 0 < (Fintype.card α) ^ 2 := by positivity
  exact (Nat.mul_lt_mul_right hα2).mpr hcard

end OpCount

section SymmetricStorage

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] in
/-- Symmetric `K` + support propagate to the TRANSPOSE side:
`i ∉ N j → K i j a b = 0` (via `K i j a b = K j i b a` and support at
`(j, i)`). Symmetric storage cannot smuggle a nonzero coupling entry
outside the neighbour sets. -/
theorem sparse_support_of_symmetric (N : ι → Finset ι)
    (K : ι → ι → α → α → ℝ)
    (hK : ∀ i j a b, K i j a b = K j i b a)
    (hs : couplingSupportedOn N K)
    (i j : ι) (a b : α) (h : i ∉ N j) : K i j a b = 0 := by
  rw [hK i j a b]
  exact hs j i b a h

end SymmetricStorage

/-! ## Fin 4 anchor (2 of 3 neighbours; sparse = dense; 8 < 12) -/

section Carrier

open Hagi.Energy

-- Cell 0 has exactly 2 of its 3 possible neighbours.
private def Nex : Fin 4 → Finset (Fin 4) :=
  fun i => if i = 0 then {1, 3} else ∅

-- Coupling supported on N (off-support entries are 0).
private noncomputable def Kex4 : Fin 4 → Fin 4 → Bool → Bool → ℝ :=
  fun i j a b => if j ∈ Nex i && a && b then (i : ℝ) + (j : ℝ) + 1 else 0

private def Bex4 : Fin 4 → Bool → ℝ := fun i a => if a then (i : ℝ) + 1 else 0
private def yex4 : Fin 4 → Bool := fun i => i % 2 == 0

private theorem carrier_supported : couplingSupportedOn Nex Kex4 := by
  intro i j a b hj
  by_cases h0 : i = 0
  · subst h0
    simp [Nex] at hj
    simp [Nex, Kex4, hj]
  · simp [Nex, h0, Kex4]

private theorem carrier_no_self : ∀ i, i ∉ Nex i := by
  intro i
  by_cases h0 : i = 0
  · subst h0; decide
  · simp [Nex, h0]

/-- Vacuity/equivalence check: on the carrier the sparse field equals
the dense C261 field for every cell and value. -/
example (i : Fin 4) (c : Bool) :
    sparseLocalField Nex Bex4 Kex4 yex4 i c
      = localField Bex4 Kex4 yex4 i c :=
  sparse_localField_eq_dense Nex Bex4 Kex4 yex4 carrier_supported
    carrier_no_self i c

/-- Vacuity check: cell 0 has 2 neighbours, 3 off-diagonal cells;
per-value Bool work `(card α)² = 4`: sparse `2·4 = 8 < 12 = 3·4`
dense (decide). -/
example : localField_sparse_work Bool Nex 0
    < localField_dense_work Bool (0 : Fin 4) := by
  decide

end Carrier

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Numerical error bridges: guarded energy descent under local-field noise

Track P3 (addendum A11, first item): the CRAM solver's computed local
fields `L̂_i` (e.g. BF16-rounded evaluations) carry a per-value error
`|L̂_i(a) − L_i(a)| ≤ ε`. This file bridges that numerical premise to
the exact-arithmetic descent of `Hagi.Energy.SingleCellDescent` (C261):

* `guarded_energy_delta_error` — the energy-delta error is at most
  `2ε`: the single-cell delta `Δ = E(y^{i←a}) − E(y)` equals
  `L_i(a) − L_i(y_i)` (symmetric `K`) and involves TWO field
  evaluations, each ±ε; the constant `2ε` is TIGHT (both perturbations
  in the same direction give exactly `2ε` — an `ε`-only bound would be
  the single-evaluation fallacy).
* `guarded_energy_delta` — the guard is SOUND: computed improvement
  margin `2ε < L̂_i(y_i) − L̂_i(a)` ⇒ the TRUE energy strictly
  decreases (noise-robust strict descent; acceptance only when the
  margin clears the full `2ε` slack).
* `localField_visibleBiasWithZ` — the frozen-z bias shift adds the
  constant `zc i` to every local-field value (composition seam).
* `guarded_greedy_strict_drop` — composition of the guarded acceptance
  with `Hagi.Energy.strict_drop_of_positive_margin` at the two-phase
  frozen-z setting (`visibleBiasWithZ`): upgrades C261's
  exact-arithmetic descent to noise-robust descent. Joint `(z, y)`
  updates remain FORBIDDEN by the E3 two-phase protocol.
* `latent_update_degree_zero_exact_after_one` /
  `latent_update_degree_zero_one_step_is_fixed` — the `Δ = 0`
  degenerate case (all neighborhoods empty): the latent update is a
  constant map, hence EXACT after one step; every start reaches the
  fixed point in one step. `LatentEnergy.latent_iterate_err_bound`
  requires `0 < Δ` (its reused `inexact_contraction_bound` needs a
  factor in `(0,1)`), so the degenerate case is a SEPARATE theorem —
  not hidden, not conflated with the asymptotic floor
  `ε_round/(1−q)` which only exists for a genuine contraction.

## Honest boundaries (both directions of the guard)

Acceptance is sound (proved). REJECTION carries no information: a
computed margin `≤ 2ε` can occur while the true margin is strictly
positive — the guard conservatively rejects a TRUE drop (witness
below: `ε = 1`, true margin `2`, computed margin `0`). The solver may
therefore stall below the `2ε` noise floor; this is the price of
soundness, stated rather than hidden.

## BF16 instantiation of the ε premise (mapping, not re-proven)

The ε premise instantiates against the EXISTING BF16 nearest-rounding
model of `Hagi.Runtime.BF16Delta`: for a value `x` in the normal range
`2⁻¹²⁶ ≤ |x| ≤ 2¹²⁷` and a nearest code `c`,
`abs_sub_le_of_isNearest_normal` gives `|decode c − x| ≤ 2⁻⁸ · |x|`
over the exact rational carrier. Instantiation recipe: take
`L̂ i a = (decode c(i,a) : ℝ)` with each `c(i,a)` nearest-selected in
the normal range and set the ABSOLUTE premise bound
`ε = 2⁻⁸ · max_b |L i b|` (cast the per-value relative bound through
`Rat.cast_le`); the guard then accepts exactly when the computed
margin exceeds `2⁻⁷ · max_b |L i b|`. The relative-to-absolute cast is
recorded as a recipe (reuse, not redefine); below the normal range the
relative bound genuinely fails (see the BF16 anchor round-trip witness)
and no ε premise is claimed there.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (localField pairwiseEnergy strict_drop_of_positive_margin)

/-! ## Guarded local-field margins -/
section Guard

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- **`guarded_energy_delta_error`** — (P3 MAIN) the computed
single-cell energy delta `Δ̂ = L̂_i(a) − L̂_i(y_i)` approximates the TRUE
delta `Δ = E(y^{i←a}) − E(y)` within `2ε`: the delta involves TWO field
evaluations (`L̂ i a` and `L̂ i (y i)`), each within `ε` of the exact
local field (symmetric `K` — the exact delta is the one-sided
`localField` difference; WITHOUT symmetry the delta uses the
symmetrized field and a premise on `localField` alone would NOT bound
it). The constant `2ε` is tight. -/
theorem guarded_energy_delta_error (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (y : ι → α) (i : ι) (a : α) (Lhat : ι → α → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ b, |Lhat i b - localField B K y i b| ≤ ε) :
    |(Lhat i a - Lhat i (y i))
      - (pairwiseEnergy B K (Function.update y i a) - pairwiseEnergy B K y)|
      ≤ 2 * ε := by
  have hd := Hagi.Energy.single_cell_move_energy_delta_symm B K hK y i a
  have h1 := abs_le.mp (herr a)
  have h2 := abs_le.mp (herr (y i))
  rw [hd]
  have key : (Lhat i a - Lhat i (y i))
      - (localField B K y i a - localField B K y i (y i))
      = (Lhat i a - localField B K y i a)
        - (Lhat i (y i) - localField B K y i (y i)) := by ring
  rw [key, abs_le]
  constructor <;> linarith

/-- **`guarded_energy_delta`** — (P3 MAIN) the guard is SOUND: if the
COMPUTED improvement margin clears the full noise slack,
`2ε < L̂_i(y_i) − L̂_i(a)`, then the TRUE energy strictly decreases.
Rejection (`margin ≤ 2ε`) carries no information — see the witness
below: the guard can conservatively reject a true drop. -/
theorem guarded_energy_delta (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (y : ι → α) (i : ι) (a : α) (Lhat : ι → α → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ b, |Lhat i b - localField B K y i b| ≤ ε)
    (hguard : 2 * ε < Lhat i (y i) - Lhat i a) :
    pairwiseEnergy B K (Function.update y i a) < pairwiseEnergy B K y := by
  have hb := abs_le.mp
    (guarded_energy_delta_error B K hK y i a Lhat ε hε herr)
  have hd := Hagi.Energy.single_cell_move_energy_delta_symm B K hK y i a
  linarith

/-- Honest rejection witness (BOTH directions stated): a computed
margin `≤ 2ε` can coexist with a strictly positive TRUE margin — the
sound guard conservatively rejects a genuine drop (here: true margin
`2`, computed margin `0`, `ε = 1`). Stalling below the `2ε` noise
floor is possible; this is the price of soundness. -/
example : ∃ lhatHi lhatLo lHi lLo ε : ℝ, 0 ≤ ε ∧ 0 < lHi - lLo ∧
    |lhatHi - lHi| ≤ ε ∧ |lhatLo - lLo| ≤ ε ∧ lhatHi - lhatLo ≤ 2 * ε := by
  refine ⟨1, 1, 2, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

end Guard

/-! ## Frozen-z composition (two-phase protocol) -/
section FrozenZ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- **`localField_visibleBiasWithZ`** — the frozen-z bias shift adds
the CONSTANT `zc i` to every local-field value of cell `i` (independent
of the candidate `a`): the composition seam between the two-phase
protocol and the local-field machinery. -/
theorem localField_visibleBiasWithZ (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (zc : ι → ℝ) (y : ι → α) (i : ι) (a : α) :
    localField (visibleBiasWithZ B zc) K y i a
      = localField B K y i a + zc i := by
  unfold localField visibleBiasWithZ
  ring

/-- **`guarded_greedy_strict_drop`** — (P3 MAIN, composition with C261
`strict_drop_of_positive_margin`) guarded acceptance under the
two-phase frozen-z setting: computed fields of the frozen-bias energy
`pairwiseEnergy (visibleBiasWithZ B zc) K` with margin clearing `2ε`
give a STRICT drop of that TRUE energy. This upgrades C261's
exact-arithmetic descent to noise-robust descent. The frozen-`z`
premise is structural (E3): joint `(z, y)` updates remain forbidden —
a mid-descent z-move changes the bias and voids the delta identity. -/
theorem guarded_greedy_strict_drop (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (zc : ι → ℝ) (y : ι → α) (i : ι) (a : α) (Lhat : ι → α → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ b, |Lhat i b - localField (visibleBiasWithZ B zc) K y i b| ≤ ε)
    (hguard : 2 * ε < Lhat i (y i) - Lhat i a) :
    pairwiseEnergy (visibleBiasWithZ B zc) K (Function.update y i a)
      < pairwiseEnergy (visibleBiasWithZ B zc) K y :=
  guarded_energy_delta (visibleBiasWithZ B zc) K hK y i a Lhat ε hε herr hguard

end FrozenZ

/-! ## Latent Δ = 0 degenerate case (B1-low) -/
section LatentZero

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`latent_update_degree_zero_exact_after_one`** — (B1-low) at
`Δ = 0` (all neighborhoods empty) the latent update is the CONSTANT
map `1[i = G]/m`, hence exact after ONE step — no contraction factor,
no asymptotic floor `ε_round/(1−q)` (that floor belongs to a genuine
contraction with `0 < Δ`; see `LatentEnergy.latent_iterate_err_bound`
and `Hagi.Optimization.inexact_contraction_bound`, which REQUIRE
`0 < Δ`). Separate theorem, not a special case smuggled in. -/
theorem latent_update_degree_zero_exact_after_one (N : ι → Finset ι)
    (m : ℝ) (G : ι) (hN : ∀ i, N i = ∅) (z : ι → ℝ) :
    latentUpdate N m G (latentUpdate N m G z) = latentUpdate N m G z := by
  funext i
  simp [latentUpdate, hN i]

/-- **`latent_update_degree_zero_one_step_is_fixed`** — every start
reaches THE fixed point in one step (the constant map's value): the
`Δ = 0` iterate error is exactly zero after one step, for any fixed
point `zstar`. -/
theorem latent_update_degree_zero_one_step_is_fixed (N : ι → Finset ι)
    (m : ℝ) (G : ι) (hN : ∀ i, N i = ∅) (zstar z : ι → ℝ)
    (hz : latentUpdate N m G zstar = zstar) :
    latentUpdate N m G z = zstar := by
  funext i
  simpa [latentUpdate, hN i] using congrFun hz i

end LatentZero

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Latent fixed point support and reachability

Track B2 (addendum A11 B-level): support/connectivity properties of the
LATENT fixed point `z*` of `latentUpdate` (C272's `LatentEnergy.lean`
carrier, fixed-point equation `z* i = (Σ_{j ∈ N i} z* j + 1[i = G])/m`
with symmetric adjacency, degree bound `(N i).card ≤ Δ`, `m > Δ`).

Main results:

* `latent_fixed_unique` — uniqueness of the fixed point (directly from
  `latent_update_contraction`: `‖z − z'‖ ≤ (Δ/m)·‖z − z'‖` with
  `Δ/m < 1` forces equality), reused by `latent_fixed_zero_off_closed`.
* `latent_fixed_nonneg` — (B2 MAIN) the unique fixed point is
  nonnegative: at the argmin index the goal injection `1[i = G] ≥ 0`
  and the neighbour terms give `m·z i ≥ card(N i)·z i`, so
  `(m − card(N i))·z i ≥ 0` with `m > Δ ≥ card` forces `z i ≥ 0`.
* `latent_fixed_goal_pos` — the goal source term: `1/m ≤ z* G`.
* `latent_fixed_ge_of_neighbour` — propagation across an edge:
  `i ∈ N j → z* j / m ≤ z* i` (symmetry is load-bearing: it puts `j`
  into `N i`; nonnegativity handles the remaining neighbour terms).
* `LatentPath` — inductive reachability from the goal over the
  neighbour relation (path length = number of edges).
* `latent_fixed_pos_of_reachable` — (B2 MAIN) if `LatentPath N G i k`
  then `(1/m)^(k+1) ≤ z* i`, in particular `0 < z* i`: positivity
  propagates from the goal along every path.
* `latent_fixed_upper_bound` — global sup bound `z* i ≤ 1/(m − Δ)`
  (argmax mirror of the nonneg argument).
* `latent_fixed_zero_off_closed` — (B2 MAIN) on a set `C'` closed
  under neighbours (`∀ i ∈ C', N i ⊆ C'`) with no goal
  (`∀ i ∈ C', i ≠ G`), the fixed point vanishes: the 0-on-C' patch of
  `z*` is again a fixed point (closedness for `i ∈ C'`; SYMMETRY for
  `i ∉ C'` — a neighbour in `C'` would pull `i` into `C'`), and
  `latent_fixed_unique` forces it back onto `z*`.

## Honest boundaries

* NO per-distance DECAY upper bound (`z* i ≤ z_G/m^k · const`) is
  claimed: it needs graph structure beyond degree boundedness (`z i`
  receives contributions from ALL its neighbours, so off-path edges
  break a pure path-decay bound). The provable general statement is
  the global sup bound `1/(m − Δ)` (see `latent_fixed_upper_bound`);
  the name `latent_fixed_decay_upper` is nonexistent (RootApi negative
  pin). Honesty over completeness.
* All theorems are about the FIXED POINT of `latentUpdate` (which
  exists uniquely by C272's Banach theorem); no iterate statements are
  duplicated here (see `latent_iterate_err_bound` there).

Numeric anchor (consumed from `LatentEnergy.lean`'s frozen fixture):
`zstar4 = ![21/55, 8/55, 3/55, 1/55]` on the `Fin 4` path with
`m = 3`, `G = 0`: all entries positive, `(1/3)^4 = 1/81 ≤ 1/55`
(reachability at distance 3), `21/55 ≤ 1 = 1/(3 − 2)` (upper bound).
-/

namespace Hagi.Model.EnergyReasoning

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Uniqueness and nonnegativity -/
section Support

/-- **`latent_fixed_unique`** — two fixed points of the latent update
coincide (direct consequence of the C272 ℓ∞ contraction
`latent_update_contraction` with factor `Δ/m < 1`). -/
theorem latent_fixed_unique (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (z z' : ι → ℝ)
    (hz : latentUpdate N m G z = z) (hz' : latentUpdate N m G z' = z') : z = z' := by
  by_contra hne
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  have h := latent_update_contraction N m G hΔ hm z z'
  rw [hz, hz'] at h
  have h0 : 0 < ‖z - z'‖ := norm_pos_iff.mpr (fun h0 => hne (sub_eq_zero.mp h0))
  have hlt : ((Δ : ℝ) / m) * ‖z - z'‖ < ‖z - z'‖ := by
    have e : ((Δ : ℝ) / m) * ‖z - z'‖ < (m / m) * ‖z - z'‖ :=
      mul_lt_mul_of_pos_right (div_lt_div_iff_of_pos_right hm0 |>.mpr (by linarith)) h0
    rw [div_self (ne_of_gt hm0), one_mul] at e
    exact e
  linarith

/-- **`latent_fixed_nonneg`** — (B2 MAIN) with `m > Δ`, any fixed point
of the latent update is nonnegative (minimum argument: at the argmin
index `m·z i = Σ_{N i} z j + 1[i = G] ≥ card(N i)·z i`, and
`m − card(N i) > 0` since `card ≤ Δ < m`). -/
theorem latent_fixed_nonneg (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    ∀ i, 0 ≤ zstar i := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  obtain ⟨i, -, hile⟩ := Finset.exists_min_image Finset.univ zstar ⟨i₀, by simp⟩
  have hmin : ∀ j, zstar i ≤ zstar j := fun j => hile j (Finset.mem_univ j)
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  have hfix : zstar i = (∑ j ∈ N i, zstar j + (if i = G then (1:ℝ) else 0)) / m :=
    (congrFun hz i).symm
  have hsumge : ((N i).card : ℝ) * zstar i ≤ ∑ j ∈ N i, zstar j := by
    have e1 : ∑ j ∈ N i, zstar i = ((N i).card : ℝ) * zstar i := by
      rw [Finset.sum_const]; simp
    calc ((N i).card : ℝ) * zstar i = ∑ j ∈ N i, zstar i := e1.symm
      _ ≤ ∑ j ∈ N i, zstar j := Finset.sum_le_sum fun j _ => hmin j
  have hind : (0:ℝ) ≤ (if i = G then (1:ℝ) else 0) := by split <;> norm_num
  have hkey : ((N i).card : ℝ) * zstar i ≤ m * zstar i := by
    have e : m * zstar i = ∑ j ∈ N i, zstar j + (if i = G then (1:ℝ) else 0) := by
      rw [hfix]; exact mul_div_cancel₀ _ (ne_of_gt hm0)
    linarith
  have hzineg : zstar i < 0 := lt_of_le_of_lt (hmin i₀) hi₀
  have hpos : (0:ℝ) < m - (N i).card := by
    have hcard : ((N i).card : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ i
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  have hfinal : (0:ℝ) ≤ m * zstar i - ((N i).card : ℝ) * zstar i := by linarith
  have hznn : (0:ℝ) ≤ zstar i := by
    have e : m * zstar i - ((N i).card : ℝ) * zstar i
        = (m - ((N i).card : ℝ)) * zstar i := by ring
    rw [e] at hfinal
    exact (mul_nonneg_iff_of_pos_left hpos).mp hfinal
  exact absurd hzineg (not_lt.mpr hznn)

/-- **`latent_fixed_goal_pos`** — the goal source term: `1/m ≤ z* G`
(the fixed-point equation at `G` reads `m·z* G = Σ_{N G} z* j + 1`). -/
theorem latent_fixed_goal_pos (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    1 / m ≤ zstar G := by
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  have hfix : zstar G = (∑ j ∈ N G, zstar j + (if G = G then (1:ℝ) else 0)) / m :=
    (congrFun hz G).symm
  have e : zstar G = (∑ j ∈ N G, zstar j + 1) / m := by
    rw [hfix]; congr 1; simp
  rw [e, le_div_iff₀ hm0]
  have hsum : (0:ℝ) ≤ ∑ j ∈ N G, zstar j :=
    Finset.sum_nonneg fun j _ => latent_fixed_nonneg N m G hΔ hm zstar hz j
  have hone : (1:ℝ) / m * m = 1 := by field_simp
  linarith

end Support

/-! ## Neighbour propagation and reachability -/
section Reach

/-- **`latent_fixed_ge_of_neighbour`** — propagation across an edge:
`i ∈ N j → z* j / m ≤ z* i`. Symmetry is load-bearing (it puts `j`
into `N i`); nonnegativity handles the remaining neighbour terms. -/
theorem latent_fixed_ge_of_neighbour (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar)
    {i j : ι} (hn : i ∈ N j) : zstar j / m ≤ zstar i := by
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  have hfix : zstar i = (∑ j' ∈ N i, zstar j' + (if i = G then (1:ℝ) else 0)) / m :=
    (congrFun hz i).symm
  have hn' : j ∈ N i := (hNsymm j i).mp hn
  have hnn : ∀ j', (0:ℝ) ≤ zstar j' := latent_fixed_nonneg N m G hΔ hm zstar hz
  have hge : zstar j ≤ ∑ j' ∈ N i, zstar j' :=
    Finset.single_le_sum (f := zstar) (fun j' _ => hnn j') hn'
  have hind : (0:ℝ) ≤ (if i = G then (1:ℝ) else 0) := by split <;> norm_num
  rw [hfix, le_div_iff₀ hm0]
  have hjm : zstar j / m * m = zstar j := by field_simp
  linarith

/-- **`LatentPath`** — inductive reachability from the goal `G` over
the neighbour relation; the ℕ index is the path length (number of
edges). -/
inductive LatentPath (N : ι → Finset ι) (G : ι) : ι → ℕ → Prop
  | goal : LatentPath N G G 0
  | step {j i : ι} {k : ℕ} (h : LatentPath N G j k) (hn : i ∈ N j) :
      LatentPath N G i (k + 1)

/-- **`latent_fixed_pos_of_reachable`** — (B2 MAIN) if `i` is reachable
from the goal by a path of length `k`, then `(1/m)^(k+1) ≤ z* i`; in
particular `0 < z* i`: positivity propagates from the goal source term
along every path. -/
theorem latent_fixed_pos_of_reachable (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    ∀ {i k}, LatentPath N G i k → (1 / m) ^ (k + 1) ≤ zstar i := by
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  intro i k hp
  induction hp with
  | goal =>
      simpa using latent_fixed_goal_pos N m G hΔ hm zstar hz
  | @step j i k h hn ih =>
      have h1 := latent_fixed_ge_of_neighbour N m G hNsymm hΔ hm zstar hz hn
      have hexp : (1 / m) ^ (k + 1 + 1) = (1 / m) ^ (k + 1) / m := by
        rw [pow_succ]; field_simp
      rw [hexp, div_le_iff₀ hm0]
      have h2 : m * (zstar j / m) = zstar j := by field_simp
      calc (1 / m) ^ (k + 1) ≤ zstar j := ih
        _ = m * (zstar j / m) := h2.symm
        _ ≤ m * zstar i := mul_le_mul_of_nonneg_left h1 (le_of_lt hm0)
        _ = zstar i * m := by ring

/-- **`latent_fixed_upper_bound`** — global sup bound: every entry of
the fixed point obeys `z* i ≤ 1/(m − Δ)` (argmax mirror of the
nonneg argument: `m·z_max = Σ + 1[i = G] ≤ Δ·z_max + 1`). This is the
provable general upper statement; a per-distance decay bound needs
graph structure beyond degree boundedness and is NOT claimed. -/
theorem latent_fixed_upper_bound (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    ∀ i, zstar i ≤ 1 / (m - (Δ : ℝ)) := by
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  obtain ⟨i, -, hile⟩ := Finset.exists_max_image Finset.univ zstar ⟨i₀, by simp⟩
  have hmax : ∀ j, zstar j ≤ zstar i := fun j => hile j (Finset.mem_univ j)
  have hfix : zstar i = (∑ j ∈ N i, zstar j + (if i = G then (1:ℝ) else 0)) / m :=
    (congrFun hz i).symm
  have hcard : ((N i).card : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ i
  have hsumle : ∑ j ∈ N i, zstar j ≤ ((N i).card : ℝ) * zstar i := by
    have e1 : ∑ j ∈ N i, zstar i = ((N i).card : ℝ) * zstar i := by
      rw [Finset.sum_const]; simp
    calc ∑ j ∈ N i, zstar j ≤ ∑ j ∈ N i, zstar i :=
          Finset.sum_le_sum fun j _ => hmax j
      _ = ((N i).card : ℝ) * zstar i := e1
  have hind : (if i = G then (1:ℝ) else 0) ≤ 1 := by split <;> norm_num
  have e : m * zstar i = ∑ j ∈ N i, zstar j + (if i = G then (1:ℝ) else 0) := by
    rw [hfix]; exact mul_div_cancel₀ _ (ne_of_gt hm0)
  have hviol : 1 / (m - (Δ:ℝ)) < zstar i := lt_of_lt_of_le hi₀ (hmax i₀)
  have hgap : (0:ℝ) < m - (Δ : ℝ) := by linarith
  have hnnz : (0:ℝ) ≤ zstar i := latent_fixed_nonneg N m G hΔ hm zstar hz i
  have hcz : ((N i).card : ℝ) * zstar i ≤ ((Δ:ℝ)) * zstar i :=
    mul_le_mul_of_nonneg_right hcard hnnz
  have h1 : ∑ j ∈ N i, zstar j + (if i = G then (1:ℝ) else 0)
      ≤ ((Δ:ℝ)) * zstar i + 1 := by linarith
  have hle : (m - (Δ:ℝ)) * zstar i ≤ 1 := by nlinarith [e, h1]
  have hone : (m - (Δ:ℝ)) * (1 / (m - (Δ:ℝ))) = 1 := by field_simp
  have hlt : (m - (Δ:ℝ)) * (1 / (m - (Δ:ℝ))) < (m - (Δ:ℝ)) * zstar i :=
    mul_lt_mul_of_pos_left hviol hgap
  rw [hone] at hlt
  linarith

end Reach

/-! ## Zero on neighbour-closed goal-free regions -/
section Closed

/-- **`latent_fixed_zero_off_closed`** — (B2 MAIN) if `C'` is closed
under neighbours (`∀ i ∈ C', N i ⊆ C'`) and carries no goal
(`∀ i ∈ C', i ≠ G`), then the fixed point vanishes on `C'`: the
0-on-`C'` patch of `z*` is again a fixed point (closedness for
`i ∈ C'`; SYMMETRY for `i ∉ C'` — a neighbour in `C'` would pull `i`
into `C'`), and `latent_fixed_unique` forces it back onto `z*`. -/
theorem latent_fixed_zero_off_closed (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (C' : Finset ι)
    (hC : ∀ i ∈ C', N i ⊆ C') (hG : ∀ i ∈ C', i ≠ G)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    ∀ i ∈ C', zstar i = 0 := by
  set z' : ι → ℝ := fun i => if i ∈ C' then 0 else zstar i with hz'def
  have hfixz' : latentUpdate N m G z' = z' := by
    funext i
    by_cases hmem : i ∈ C'
    · have hsub : ∀ j ∈ N i, z' j = 0 := by
        intro j hj
        simp [hz'def, hC i hmem hj]
      have hsum : ∑ j ∈ N i, z' j = 0 := Finset.sum_eq_zero hsub
      have hind : (if i = G then (1:ℝ) else 0) = 0 := by simp [hG i hmem]
      show (∑ j ∈ N i, z' j + (if i = G then (1:ℝ) else 0)) / m = z' i
      rw [hsum, hind]
      simp [hz'def, hmem]
    · have hnot : ∀ j ∈ N i, z' j = zstar j := by
        intro j hj
        have hnc : j ∉ C' := by
          intro hc
          exact hmem ((hC j hc) ((hNsymm i j).mp hj))
        simp [hz'def, hnc]
      show (∑ j ∈ N i, z' j + (if i = G then (1:ℝ) else 0)) / m = z' i
      have hsum' : ∑ j ∈ N i, z' j = ∑ j ∈ N i, zstar j :=
        Finset.sum_congr rfl hnot
      have hzi : z' i = zstar i := by rw [hz'def]; simp [hmem]
      rw [hsum', hzi]
      exact congrFun hz i
  have heq : z' = zstar := latent_fixed_unique N m G hΔ hm z' zstar hfixz' hz
  intro i hi
  have hz'i : z' i = 0 := by simp [hz'def, hi]
  rw [← heq]
  exact hz'i

end Closed

/-! ## Fixtures and numeric anchors -/
section Fixture

/-- Numeric anchor: every entry of the frozen path-graph fixed point
`zstar4 = ![21/55, 8/55, 3/55, 1/55]` is strictly positive. -/
example : ∀ i, (0:ℝ) < zstar4 i := by
  intro i; fin_cases i <;> norm_num [zstar4]

/-- Numeric anchor (reachability): cell `3` at path distance `3` from
the goal `0` obeys `(1/3)^(3+1) = 1/81 ≤ 1/55 = zstar4 3`. -/
example : (1:ℝ) / 3 ^ (3+1) ≤ zstar4 3 := by norm_num [zstar4]

/-- Numeric anchor (upper bound): `zstar4 0 = 21/55 ≤ 1 = 1/(3 − 2)`
(`m = 3`, `Δ = 2`). -/
example : zstar4 0 ≤ 1 / (3 - (2:ℝ)) := by norm_num [zstar4]

/-- **`emptyN2`** — empty-adjacency `Fin 2` fixture (zero-off-closed
anchor). -/
def emptyN2 : Fin 2 → Finset (Fin 2) := fun _ => ∅

/-- **`zstar2`** — the unique fixed point of the empty-adjacency update
with `m = 3`, `G = 0`: `![1/3, 0]` (cell `1` is unreachable and lies in
the closed goal-free region `{1}`). -/
noncomputable def zstar2 : Fin 2 → ℝ := fun i => if i = 0 then (1:ℝ)/3 else 0

/-- Numeric anchor: `zstar2` solves the fixed-point equation. -/
example : latentUpdate emptyN2 3 0 zstar2 = zstar2 := by
  funext i; fin_cases i <;> simp [latentUpdate, emptyN2, zstar2]

/-- Numeric anchor (zero-off-closed): on the closed goal-free region
`C' = {1}` the fixed point vanishes. -/
example : ∀ i ∈ ({1} : Finset (Fin 2)), zstar2 i = 0 := by
  have hsymm : ∀ i j, j ∈ emptyN2 i ↔ i ∈ emptyN2 j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [emptyN2]
  have hΔ : ∀ i, (emptyN2 i).card ≤ 0 := by
    intro i; fin_cases i <;> simp [emptyN2]
  have hC : ∀ i ∈ ({1} : Finset (Fin 2)), emptyN2 i ⊆ {1} := by
    intro i hi
    have hi1 : i = 1 := by simpa [Finset.mem_singleton] using hi
    rw [hi1]; simp [emptyN2]
  have hG : ∀ i ∈ ({1} : Finset (Fin 2)), i ≠ 0 := by
    intro i hi
    have hi1 : i = 1 := by simpa [Finset.mem_singleton] using hi
    rw [hi1]; simp
  have hfix : latentUpdate emptyN2 3 0 zstar2 = zstar2 := by
    funext i; fin_cases i <;> simp [latentUpdate, emptyN2, zstar2]
  intro i hi
  exact latent_fixed_zero_off_closed emptyN2 3 0 hsymm hΔ (by norm_num) {1}
    hC hG zstar2 hfix i hi

end Fixture

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Attention coupling: the latent-to-visible field link L_ij(z)

Track B3 (addendum A11 B-level): the REAL CRAM+Z link — the latent
state `z` couples into the VISIBLE pairwise energy through an
ATTENTION-weighted coupling kernel K(z), not just an additive bias
(the additive route is `LatentEnergy.visibleBiasWithZ`, the E3
two-phase seam — both exist, this file adds the multiplicative
attention link).

Construction: at FROZEN `z` (E3 two-phase protocol; `z` is
discrete/frozen — no differentiability-in-`z` is claimed), scores
`s : ι → ι → ℝ` induce softmax attention weights
`attentionWeights s i j = exp(s i j) / ∑_k exp(s i k)`, and the
coupling carries BOTH directed edges in every entry:

  `L_ij(a,b) = κ_ij · w_ij · f(a,b) + κ_ji · w_ji · f(b,a)`.

* `attentionWeights_nonneg` / `attentionWeights_le_one` /
  `attentionWeights_sum` — the softmax simplex facts (weights in
  `[0,1]`, row sums `1`; premise `[Nonempty ι]`: an empty index type
  has no softmax).
* `attention_coupling_symmetric` — (B3 MAIN) `L_ij(a,b) = L_ji(b,a)`
  BY CONSTRUCTION: the two directed contributions swap exactly. This
  is the A9 upper-triangle trick — both directed edges are built into
  every `L_ij`, so the kernel satisfies the C261 `hK` premise with NO
  symmetry hypothesis on `κ` or `w`. Fin 3 numeric anchor below uses
  a deliberately ASYMMETRIC `κ` to catch any index-role slip.
* `attention_coupling_bounded` — `|L_ij(a,b)| ≤ 2·κmax·fmax` when
  `0 ≤ κ ≤ κmax`, `w ∈ [0,1]`, `|f| ≤ fmax`. The constant `2` is
  TIGHT: two directed contributions, each `≤ κmax·fmax` (witness: `f`
  constant `±fmax` attains both simultaneously).
* `attentionK` — the kernel `K(z)` at frozen `z` (`w = α(·; z)`),
  `attention_K_symmetric` — the C261 premise verbatim.
* `frozen_z_field_with_attention` — the local field for `K(z)` is
  well-defined and the C261 machinery applies at frozen `z`: a
  local-field minimizer move does not increase
  `pairwiseEnergy B (attentionK κ (attentionWeights s) f)`.
* `attention_coupling_field_diff` — weight drift `|w1 − w2| ≤ δ`
  (premise) ⇒ local-field perturbation
  `≤ |S_i| · 2κmax·fmax·δ`, `S_i = univ \ {i}`.
* `latent_error_couples_field` — the composed latent-error contract
  (PREMISE-FORM, honest): `‖z − z*‖ ≤ η` plus a softmax-Lipschitz
  PREMISE `|w(z) − w(z*)| ≤ L_sm·η` (no such lemma is claimed for
  this carrier; `z` is frozen) bounds the field perturbation by
  `|S_i|·2κmax·fmax·L_sm·η`.
* `latent_attention_guarded_drop` — the C270 guard ABSORBS the latent
  error: with `ε := |S_i|·2κmax·fmax·L_sm·η`, a computed margin
  `2ε < L̂(y_i) − L̂(a)` on the `K(z)`-fields gives a STRICT drop of
  the TRUE energy `pairwiseEnergy B (attentionK κ w(z*) f)` — the
  2ε-guard recipe of `guarded_energy_delta` instantiated at the
  coupling bound.

## Honest boundaries (B3)

This is the STRUCTURAL CRAM+Z bridge only. Full Maze-Hard semantics —
support of `z*`, reachability, and JOINT `(z, y)` updates — remain
OPEN: joint updates are still forbidden by the E3 two-phase protocol
(a mid-descent z-move changes the kernel and voids the C261 delta
identity; no joint theorem exists or is claimed). The softmax
Lipschitz-in-z step is a premise, not a theorem.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (localField pairwiseEnergy greedy_single_cell_nonincreasing)

/-! ## Softmax attention weights (z frozen in the scores s) -/
section Weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **`attentionWeights`** — the softmax attention weight
`α_ij = exp(s i j) / ∑_k exp(s i k)`; the latent state `z` is FROZEN
inside the scores `s` (premise-form scores: `z` discrete/frozen, no
differentiability-in-`z` claimed). -/
noncomputable def attentionWeights (s : ι → ι → ℝ) (i j : ι) : ℝ :=
  Real.exp (s i j) / ∑ k, Real.exp (s i k)

/-- **`attentionWeights_nonneg`** — softmax weights are nonnegative
(the denominator is a sum of positive exponentials). -/
theorem attentionWeights_nonneg (s : ι → ι → ℝ) (i j : ι) :
    0 ≤ attentionWeights s i j := by
  have hZ : (0:ℝ) < ∑ k, Real.exp (s i k) :=
    Finset.sum_pos' (fun k _ => (Real.exp_pos (s i k)).le)
      ⟨i, Finset.mem_univ i, Real.exp_pos (s i i)⟩
  exact div_nonneg (Real.exp_nonneg _) (le_of_lt hZ)

/-- **`attentionWeights_le_one`** — each softmax weight is at most
`1` (the numerator is one summand of the denominator). -/
theorem attentionWeights_le_one (s : ι → ι → ℝ) (i j : ι) :
    attentionWeights s i j ≤ 1 := by
  have hZ : (0:ℝ) < ∑ k, Real.exp (s i k) :=
    Finset.sum_pos' (fun k _ => (Real.exp_pos (s i k)).le)
      ⟨i, Finset.mem_univ i, Real.exp_pos (s i i)⟩
  have hle : Real.exp (s i j) ≤ ∑ k, Real.exp (s i k) :=
    Finset.single_le_sum (fun k _ => (Real.exp_pos (s i k)).le)
      (Finset.mem_univ j)
  unfold attentionWeights
  rw [div_le_iff₀ hZ]
  exact hle.trans_eq (one_mul _).symm

/-- **`attentionWeights_sum`** — the softmax row sums to `1`
(premise `[Nonempty ι]`: on an empty index type the denominator is
`0` and there is no softmax). -/
theorem attentionWeights_sum (s : ι → ι → ℝ) (i : ι) :
    ∑ j, attentionWeights s i j = 1 := by
  have hZ : (0:ℝ) < ∑ k, Real.exp (s i k) :=
    Finset.sum_pos' (fun k _ => (Real.exp_pos (s i k)).le)
      ⟨i, Finset.mem_univ i, Real.exp_pos (s i i)⟩
  unfold attentionWeights
  rw [← Finset.sum_div, div_self hZ.ne']

end Weights

/-! ## The attention coupling and its constructive symmetry -/
section Coupling

variable {ι : Type*}
variable {α : Type*}

/-- **`attentionCoupling`** — the attention coupling
`L_ij(a,b) = κ_ij·w_ij·f(a,b) + κ_ji·w_ji·f(b,a)`: BOTH directed
edges are built into every entry (the A9 upper-triangle
construction); `w` is the attention weight function (e.g.
`attentionWeights s` at frozen `z`). -/
noncomputable def attentionCoupling (κ w : ι → ι → ℝ) (f : α → α → ℝ)
    (i j : ι) (a b : α) : ℝ :=
  κ i j * w i j * f a b + κ j i * w j i * f b a

/-- **`attention_coupling_symmetric`** — (B3 MAIN) symmetry BY
CONSTRUCTION: `L_ij(a,b) = L_ji(b,a)` — the two directed
contributions swap exactly (add_comm; NO symmetry premise on `κ` or
`w`). This is why the kernel `attentionK` satisfies the C261 `hK`
premise verbatim. -/
theorem attention_coupling_symmetric (κ w : ι → ι → ℝ) (f : α → α → ℝ)
    (i j : ι) (a b : α) :
    attentionCoupling κ w f i j a b = attentionCoupling κ w f j i b a := by
  unfold attentionCoupling
  ring

/-- **`attention_coupling_bounded`** — with `0 ≤ κ ≤ κmax`, weights
in `[0,1]` (softmax facts) and `|f| ≤ fmax`:
`|L_ij(a,b)| ≤ 2·κmax·fmax`. The constant `2` is TIGHT — two
directed contributions, each `≤ κmax·fmax`. -/
theorem attention_coupling_bounded (κ w : ι → ι → ℝ) (f : α → α → ℝ)
    {κmax fmax : ℝ} (hκ : ∀ i j, 0 ≤ κ i j ∧ κ i j ≤ κmax)
    (hw : ∀ i j, 0 ≤ w i j ∧ w i j ≤ 1)
    (hf : ∀ a b, |f a b| ≤ fmax) (i j : ι) (a b : α) :
    |attentionCoupling κ w f i j a b| ≤ 2 * κmax * fmax := by
  have hκmax : (0:ℝ) ≤ κmax := le_trans (hκ i i).1 (hκ i i).2
  have hterm : ∀ (p q : ι) (a b : α), |κ p q * w p q * f a b| ≤ κmax * fmax := by
    intro p q a b
    have h1 := (hκ p q).1
    have h2 := (hκ p q).2
    have h3 := (hw p q).1
    have h4 := (hw p q).2
    have habs : |κ p q * w p q * f a b| = κ p q * w p q * |f a b| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg h1 h3)]
    rw [habs]
    have hkw : κ p q * w p q ≤ κmax := by
      nlinarith [mul_le_mul_of_nonneg_left h4 h1]
    exact mul_le_mul hkw (hf a b) (abs_nonneg _) hκmax
  have h1 := hterm i j a b
  have h2 := hterm j i b a
  calc |attentionCoupling κ w f i j a b|
      = |κ i j * w i j * f a b + κ j i * w j i * f b a| := rfl
    _ ≤ |κ i j * w i j * f a b| + |κ j i * w j i * f b a| := abs_add_le _ _
    _ ≤ 2 * κmax * fmax := by linarith

end Coupling

/-! ## The kernel K(z) and the frozen-z visible field -/
section Kernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- **`attentionK`** — the attention coupling KERNEL `K(z)` at frozen
`z`: `K(z) i j a b = attentionCoupling κ w f i j a b` with `w = α(·;z)`
the frozen attention weights. -/
noncomputable def attentionK (κ w : ι → ι → ℝ) (f : α → α → ℝ) :
    ι → ι → α → α → ℝ :=
  fun i j a b => attentionCoupling κ w f i j a b

/-- **`attention_K_symmetric`** — `K(z)` satisfies the C261 `hK`
premise verbatim, for ANY `κ` and `w` (constructive symmetry). -/
theorem attention_K_symmetric (κ w : ι → ι → ℝ) (f : α → α → ℝ) :
    ∀ i j a b, attentionK κ w f i j a b = attentionK κ w f j i b a :=
  fun i j a b => attention_coupling_symmetric κ w f i j a b

/-- **`frozen_z_field_with_attention`** — (B3 MAIN, thin by design)
the local field for `K(z)` is well-defined and the C261 machinery
applies AT FROZEN `z`: moving cell `i` to a local-field minimizer of
`pairwiseEnergy B (attentionK κ (attentionWeights s) f)` does not
increase the energy. PREMISE-FORM for the descent — NO joint
`(z, y)` theorem exists or is claimed (E3 two-phase protocol: a
mid-descent z-move changes the kernel and voids the C261 delta
identity). -/
theorem frozen_z_field_with_attention (B : ι → α → ℝ)
    (κ : ι → ι → ℝ) (s : ι → ι → ℝ) (f : α → α → ℝ)
    (y : ι → α) (i : ι) (a : α)
    (hmin : ∀ a', localField B (attentionK κ (attentionWeights s) f) y i a
      ≤ localField B (attentionK κ (attentionWeights s) f) y i a') :
    pairwiseEnergy B (attentionK κ (attentionWeights s) f)
        (Function.update y i a)
      ≤ pairwiseEnergy B (attentionK κ (attentionWeights s) f) y :=
  greedy_single_cell_nonincreasing B _ (attention_K_symmetric _ _ _) y i a hmin

end Kernel

/-! ## Weight drift ⇒ local-field perturbation -/
section FieldDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- **`attention_coupling_field_diff`** — weight drift
`|w1 − w2| ≤ δ` (premise; the softmax-Lipschitz step is NOT claimed
here) perturbs the local field by at most
`|S_i| · 2κmax·fmax·δ`, `S_i = Finset.univ \ {i}`: each coupling
difference is `κ·|Δw|·|f|` in each of the two directed summands
(triangle + `Finset.abs_sum_le_sum_abs` + `Finset.sum_const`). -/
theorem attention_coupling_field_diff (B : ι → α → ℝ) (κ w1 w2 : ι → ι → ℝ)
    (f : α → α → ℝ)
    {κmax fmax δ : ℝ} (hκ : ∀ i j, 0 ≤ κ i j ∧ κ i j ≤ κmax)
    (hf : ∀ a b, |f a b| ≤ fmax)
    (hw : ∀ i j, |w1 i j - w2 i j| ≤ δ) (y : ι → α) (i : ι) (a : α) :
    |localField B (attentionK κ w1 f) y i a
      - localField B (attentionK κ w2 f) y i a|
      ≤ ((Finset.univ \ {i}).card : ℝ) * (2 * κmax * fmax * δ) := by
  have hκmax : (0:ℝ) ≤ κmax := le_trans (hκ i i).1 (hκ i i).2
  have hone : ∀ (p q : ι) (c d : α),
      |κ p q * (w1 p q - w2 p q) * f c d| ≤ κmax * fmax * δ := by
    intro p q c d
    have habs : |κ p q * (w1 p q - w2 p q) * f c d|
        = κ p q * |w1 p q - w2 p q| * |f c d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hκ p q).1]
    rw [habs]
    have hδ0 : (0:ℝ) ≤ δ := le_trans (abs_nonneg _) (hw p q)
    have hinner : |w1 p q - w2 p q| * |f c d| ≤ δ * fmax :=
      mul_le_mul (hw p q) (hf c d) (abs_nonneg _) hδ0
    have hstep : κ p q * (|w1 p q - w2 p q| * |f c d|) ≤ κmax * (δ * fmax) :=
      mul_le_mul (hκ p q).2 hinner
        (mul_nonneg (abs_nonneg (w1 p q - w2 p q)) (abs_nonneg (f c d))) hκmax
    have hlhs : κ p q * |w1 p q - w2 p q| * |f c d|
        = κ p q * (|w1 p q - w2 p q| * |f c d|) := by ring
    have hrhs : κmax * (δ * fmax) = κmax * fmax * δ := by ring
    rw [hlhs]
    exact le_trans hstep (le_of_eq hrhs)
  have hterm : ∀ j ∈ Finset.univ \ {i},
      |attentionCoupling κ w1 f i j a (y j)
        - attentionCoupling κ w2 f i j a (y j)| ≤ 2 * κmax * fmax * δ := by
    intro j _
    have h1 := hone i j a (y j)
    have h2 := hone j i (y j) a
    have heq : κ i j * w1 i j * f a (y j) + κ j i * w1 j i * f (y j) a
          - (κ i j * w2 i j * f a (y j) + κ j i * w2 j i * f (y j) a)
        = κ i j * (w1 i j - w2 i j) * f a (y j)
          + κ j i * (w1 j i - w2 j i) * f (y j) a := by ring
    unfold attentionCoupling
    rw [heq]
    calc |κ i j * (w1 i j - w2 i j) * f a (y j)
          + κ j i * (w1 j i - w2 j i) * f (y j) a|
        ≤ |κ i j * (w1 i j - w2 i j) * f a (y j)|
          + |κ j i * (w1 j i - w2 j i) * f (y j) a| := abs_add_le _ _
      _ ≤ 2 * κmax * fmax * δ := by linarith
  have hfield : localField B (attentionK κ w1 f) y i a
      - localField B (attentionK κ w2 f) y i a
      = ∑ j ∈ Finset.univ \ {i},
        (attentionCoupling κ w1 f i j a (y j)
          - attentionCoupling κ w2 f i j a (y j)) := by
    unfold localField attentionK
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  rw [hfield]
  have hsum : |∑ j ∈ Finset.univ \ {i},
      (attentionCoupling κ w1 f i j a (y j)
        - attentionCoupling κ w2 f i j a (y j))|
      ≤ ∑ j ∈ Finset.univ \ {i}, 2 * κmax * fmax * δ :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j hj => hterm j hj)
  have hconst : ∑ j ∈ Finset.univ \ {i}, 2 * κmax * fmax * δ
      = ((Finset.univ \ {i}).card : ℝ) * (2 * κmax * fmax * δ) := by
    rw [Finset.sum_const]; simp
  linarith [hsum.trans_eq hconst]

end FieldDiff

/-! ## The composed latent-error contract and the guarded drop -/
section LatentLink

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- **`latent_error_couples_field`** — (B3 MAIN, PREMISE-FORM chain,
honest) the composed latent-error contract: if the latent settling
tolerance gives `‖z − z*‖ ≤ η` and the softmax attention is
Lipschitz-in-`z` with constant `L_sm` (PREMISE — no such lemma is
claimed for this carrier; `z` is frozen), then the `K(z)` local field
is within `|S_i|·2κmax·fmax·L_sm·η` of the `K(z*)` local field. The
value is the explicit composed contract `η → δ_w → field
perturbation`; each arrow is auditable. -/
theorem latent_error_couples_field (B : ι → α → ℝ) (κ : ι → ι → ℝ)
    (w1 w2 : ι → ι → ℝ) (f : α → α → ℝ)
    {κmax fmax Lsm η : ℝ} (hκ : ∀ i j, 0 ≤ κ i j ∧ κ i j ≤ κmax)
    (hf : ∀ a b, |f a b| ≤ fmax)
    (hsoft : ∀ i j, |w1 i j - w2 i j| ≤ Lsm * η)
    (y : ι → α) (i : ι) (a : α) :
    |localField B (attentionK κ w1 f) y i a
      - localField B (attentionK κ w2 f) y i a|
      ≤ ((Finset.univ \ {i}).card : ℝ) * (2 * κmax * fmax * (Lsm * η)) :=
  attention_coupling_field_diff B κ w1 w2 f hκ hf hsoft y i a

/-- **`latent_attention_guarded_drop`** — (B3 MAIN) the C270 guard
ABSORBS the latent error: with
`ε := |S_i|·2κmax·fmax·L_sm·η` (the coupling bound), a computed
improvement margin `2ε < L̂(y_i) − L̂(a)` on the `K(z)`-fields gives a
STRICT drop of the TRUE energy
`pairwiseEnergy B (attentionK κ w2 f)` — the `2ε`-guard recipe of
`guarded_energy_delta` instantiated at the attention coupling bound.
Rejection still carries no information (C270 honesty). Joint
`(z, y)` updates remain FORBIDDEN (E3). -/
theorem latent_attention_guarded_drop [Nonempty α] (B : ι → α → ℝ)
    (κ : ι → ι → ℝ) (w1 w2 : ι → ι → ℝ) (f : α → α → ℝ)
    {κmax fmax Lsm η : ℝ} (hκ : ∀ i j, 0 ≤ κ i j ∧ κ i j ≤ κmax)
    (hf : ∀ a b, |f a b| ≤ fmax)
    (hsoft : ∀ i j, |w1 i j - w2 i j| ≤ Lsm * η)
    (y : ι → α) (i : ι) (a : α)
    (hguard : 2 * (((Finset.univ \ {i}).card : ℝ)
        * (2 * κmax * fmax * (Lsm * η)))
      < localField B (attentionK κ w1 f) y i (y i)
        - localField B (attentionK κ w1 f) y i a) :
    pairwiseEnergy B (attentionK κ w2 f) (Function.update y i a)
      < pairwiseEnergy B (attentionK κ w2 f) y := by
  refine guarded_energy_delta B (attentionK κ w2 f)
    (attention_K_symmetric κ w2 f) y i a
    (fun _ b => localField B (attentionK κ w1 f) y i b)
    (((Finset.univ \ {i}).card : ℝ) * (2 * κmax * fmax * (Lsm * η)))
    (by
      have a0 := Classical.arbitrary α
      have hf0 : (0:ℝ) ≤ fmax :=
        le_trans (abs_nonneg (f a0 a0)) (hf a0 a0)
      have hκ0 : (0:ℝ) ≤ κmax := le_trans (hκ i i).1 (hκ i i).2
      have hδ0 : (0:ℝ) ≤ Lsm * η :=
        le_trans (abs_nonneg _) (hsoft i i)
      exact mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hκ0) hf0) hδ0)) ?_ hguard
  intro b
  exact latent_error_couples_field B κ w1 w2 f hκ hf hsoft y i b

end LatentLink

/-! ## Fixtures and witnesses -/
section Fixture

/-- **`κa3`** — deliberately ASYMMETRIC distance kernel on `Fin 3`
(anchor: the constructive symmetry must survive asymmetric `κ`). -/
noncomputable def κa3 : Fin 3 → Fin 3 → ℝ := fun i j => (i.val + 2 * j.val : ℝ) / 4 + 1

/-- **`wa3`** — nonconstant weight fixture on `Fin 3`. -/
noncomputable def wa3 : Fin 3 → Fin 3 → ℝ := fun i j => (i.val * j.val : ℝ) / 8 + 1 / 8

/-- **`fa3`** — value-coupling fixture on `Bool`. -/
def fa3 : Bool → Bool → ℝ := fun a b => if a then (if b then 3 else 1) else -2

/-- Numeric anchor (Fin 3): `L_02(tt, ff) = L_20(ff, tt)` on an
ASYMMETRIC `κ` — the index roles swap exactly. -/
example : attentionCoupling κa3 wa3 fa3 0 2 true false
    = attentionCoupling κa3 wa3 fa3 2 0 false true := by
  unfold attentionCoupling κa3 wa3 fa3
  norm_num

end Fixture

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Doeblin mixing bound for the heat-bath kernel

Track A8 (E-track audit, addendum A11 context): the Doeblin contraction
route — re-derived in main from first principles (the quarantined
`Hagi.Research.PPT` module carries the same math for a toy `Seq`
carrier behind the quarantine boundary; it is NOT imported here).

* `doeblinMinorized` — the Doeblin minorization predicate: `0 < c` and
  every kernel entry `≥ c`.
* `vecMul` / `hbChain` — one-step pushforward and the n-step chain of a
  finite kernel.
* `tv_pair_contraction` — (A8 MAIN, first principles) any two mass
  vectors of EQUAL total mass contract under a row-stochastic kernel
  with entry floor `c`: `TV(μK, νK) ≤ (1 − |S|·c)·TV(μ, ν)`. Elementary
  splitting of the signed difference `μ − ν` into positive/negative
  parts; the pair form needs NO stationarity (stationarity enters only
  through the corollaries `tv_contraction_stationary_sharp` /
  `tv_contraction_stationary` — the audit-text `(1 − c)` weak form).
* `heatbathWeight_floor` — field-spread premise: if all local-field
  differences at a cell are within `M`, then every heat-bath weight is
  `≥ exp(−M/T)/card α` (each softmax exponent is within `M/T` of the
  best one).
* `heatbath_doeblin_floor` — (A8 MAIN, premise-form) under the
  field-spread bound and the SUPPORT premise (every target `z` is a
  single-cell move — unconditionally true when `ι` is a subsingleton,
  see `heatbath_doeblin_floor_subsingleton`), the heat-bath kernel is
  `doeblinMinorized` with `c = exp(−M/T)/card α`.
* `stationaryDensity` — the normalized Boltzmann density; stationary
  for the heat-bath kernel (from `heatbath_stationary` by linearity).
* `heatbath_tv_contraction` — (A8 MAIN) Doeblin premise on the
  heat-bath kernel ⇒ `TV(μK, π̂) ≤ (1 − c)·TV(μ, π̂)` (sharp constant
  `(1 − |ι→α|·c)` in `heatbath_tv_contraction_sharp`).
* `heatbath_mixing` / `heatbath_mixing_time` — (A8 MAIN) geometric
  mixing `TV(μKⁿ, π̂) ≤ (1 − c)ⁿ`, and the explicit mixing-time
  corollary: `n ≥ log e / log(1 − c)` steps suffice for `TV ≤ e`.

## Honest boundaries (A8 scope)

* The entrywise floor is a PREMISE for the unconditional single-cell
  kernel: for `card ι ≥ 2` the off-support entries are exactly ZERO,
  so the Doeblin premise FAILS unless supplied by the consumer (e.g. a
  scan mixture, or `card ι ≤ 1`). The floor premise subsumes
  irreducibility and aperiodicity — those are NOT claimed for the
  unconditional kernel (names `heatbath_irreducible` /
  `heatbath_aperiodic` are RootApi negative pins).
* The focused (state-dependent) mixture is OUT of scope: C268 showed
  the INVARIANCE premise can fail; only the plain single-cell
  heat-bath kernel is treated.
* No spectral-gap or cutoff claim; only the Doeblin geometric rate.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy Hagi.Prelude

section Generic

variable {S : Type*} [Fintype S] [Nonempty S]

/-- Doeblin minorization: strictly positive floor `c` under EVERY
kernel entry (row-stochasticity is carried separately by the theorems
that consume this predicate). -/
def doeblinMinorized (K : S → S → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ ∀ x y, c ≤ K x y

/-- One kernel step applied to a mass vector: `(μK)(y) = Σ_x μ(x)·K(x,y)`. -/
noncomputable def vecMul (mu : S → ℝ) (K : S → S → ℝ) : S → ℝ :=
  fun y => ∑ x, mu x * K x y

/-- The n-step chain `μKⁿ`, by iterating the one-step pushforward. -/
noncomputable def hbChain (mu : S → ℝ) (K : S → S → ℝ) : ℕ → S → ℝ
  | 0 => mu
  | n + 1 => vecMul (hbChain mu K n) K

omit [Nonempty S] in
/-- Total variation is nonnegative (half of a sum of absolute values;
  the division constant is positive). -/
theorem tvDef_nonneg (mu nu : S → ℝ) : 0 ≤ Hagi.Prelude.tvDef mu nu := by
  unfold Hagi.Prelude.tvDef
  exact div_nonneg (Finset.sum_nonneg fun y _ => abs_nonneg _) (by norm_num)

omit [Nonempty S] in
/-- The pushforward preserves the total mass under row-stochastic
  kernels. -/
theorem vecMul_sum (K : S → S → ℝ) (hrow : ∀ x, ∑ y, K x y = 1)
    (mu : S → ℝ) : ∑ y, vecMul mu K y = ∑ x, mu x := by
  calc ∑ y, vecMul mu K y = ∑ y, ∑ x, mu x * K x y := Finset.sum_congr rfl fun y _ => rfl
    _ = ∑ x, ∑ y, mu x * K x y := Finset.sum_comm
    _ = ∑ x, mu x * ∑ y, K x y := by
        refine Finset.sum_congr rfl fun x _ => (Finset.mul_sum Finset.univ (fun y => K x y) (mu x)).symm
    _ = ∑ x, mu x * 1 := Finset.sum_congr rfl fun x _ => by rw [hrow x]
    _ = ∑ x, mu x := Finset.sum_congr rfl fun x _ => mul_one _

omit [Nonempty S] in
/-- The pushforward of a nonnegative vector is nonnegative under a
  nonnegative kernel. -/
theorem vecMul_nonneg (K : S → S → ℝ) (hnn : ∀ x y, 0 ≤ K x y)
    (mu : S → ℝ) (hmunn : ∀ x, 0 ≤ mu x) (y : S) :
    0 ≤ vecMul mu K y :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hmunn x) (hnn x y)

omit [Nonempty S] in
/-- Chain step equation (`hbChain` on `n + 1` pushes the n-th iterate
  through the kernel). -/
theorem hbChain_succ (mu : S → ℝ) (K : S → S → ℝ) (n : ℕ) :
    hbChain mu K (n + 1) = vecMul (hbChain mu K n) K := rfl

omit [Nonempty S] in
/-- The chain preserves unit mass under a row-stochastic kernel. -/
theorem hbChain_sum (K : S → S → ℝ) (hrow : ∀ x, ∑ y, K x y = 1)
    (mu : S → ℝ) (hmass : ∑ x, mu x = 1) (n : ℕ) :
    ∑ y, hbChain mu K n y = 1 := by
  induction n with
  | zero => exact hmass
  | succ n ih =>
      rw [hbChain_succ, vecMul_sum K hrow, ih]

omit [Nonempty S] in
/-- The chain preserves nonnegativity under a nonnegative kernel. -/
theorem hbChain_nonneg (K : S → S → ℝ) (hnn : ∀ x y, 0 ≤ K x y)
    (mu : S → ℝ) (hmunn : ∀ x, 0 ≤ mu x) (n : ℕ) (y : S) :
    0 ≤ hbChain mu K n y := by
  have key : ∀ (n : ℕ) (y : S), 0 ≤ hbChain mu K n y := by
    intro n
    induction n with
    | zero => intro y; exact hmunn y
    | succ n ih =>
        intro y
        rw [hbChain_succ]
        exact vecMul_nonneg K hnn _ ih y
  exact key n y

/-- (A8 MAIN, first principles) One-step Doeblin PAIR contraction: for
any row-stochastic kernel with entry floor `c` and any two mass
vectors of EQUAL total mass, `TV(μK, νK) ≤ (1 − |S|·c)·TV(μ, ν)`.
Elementary proof: split the signed difference `μ − ν` into its
positive part (on `A`) and negative part (on `B`); each pushed through
the kernel stays `≥ c·δ` pointwise (`δ = Σ_A (μ − ν)` is the TV
value); the identity `|P − Q| = P + Q − 2·min(P, Q)` then shrinks the
total mass `2δ` by `2·|S|·c·δ`. No stationarity and no nonnegativity
of `μ`, `ν` is needed — only equal total mass. The constant
`1 − |S|·c` is sharp; the audit-text `1 − c` is the weak corollary
below. -/
theorem tv_pair_contraction (K : S → S → ℝ) (hrow : ∀ x, ∑ y, K x y = 1)
    (c : ℝ) (hc : ∀ x y, c ≤ K x y) (mu nu : S → ℝ)
    (hmass : ∑ x, mu x = ∑ x, nu x) :
    Hagi.Prelude.tvDef (vecMul mu K) (vecMul nu K)
      ≤ (1 - (Fintype.card S : ℝ) * c) * Hagi.Prelude.tvDef mu nu := by
  classical
  set A : Finset S := Finset.univ.filter (fun x => 0 ≤ mu x - nu x) with hAdef
  set B : Finset S := Finset.univ.filter (fun x => ¬ 0 ≤ mu x - nu x) with hBdef
  have hAnn : ∀ x ∈ A, 0 ≤ mu x - nu x := by
    intro x hx
    rw [hAdef] at hx
    exact (Finset.mem_filter.mp hx).2
  have hBnn : ∀ x ∈ B, mu x - nu x ≤ 0 := by
    intro x hx
    rw [hBdef] at hx
    exact (not_le.mp (Finset.mem_filter.mp hx).2).le
  have hAB : (∑ x ∈ A, (mu x - nu x)) + (∑ x ∈ B, (mu x - nu x))
      = ∑ x : S, (mu x - nu x) := by
    rw [hAdef, hBdef]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x => 0 ≤ mu x - nu x) (fun x => mu x - nu x)
  have hdsum : ∑ x : S, (mu x - nu x) = 0 := by
    rw [Finset.sum_sub_distrib, hmass, sub_self]
  set delta : ℝ := ∑ x ∈ A, (mu x - nu x) with hdeltadef
  have hBdelta : ∑ x ∈ B, (mu x - nu x) = -delta := by linarith
  have hdeltann : 0 ≤ delta := Finset.sum_nonneg fun x hx => hAnn x hx
  set P : S → ℝ := fun y => ∑ x ∈ A, (mu x - nu x) * K x y with hPdef
  set Q : S → ℝ := fun y => -∑ x ∈ B, (mu x - nu x) * K x y with hQdef
  have hPy : ∀ y, P y = ∑ x ∈ A, (mu x - nu x) * K x y := fun _ => rfl
  have hQy : ∀ y, Q y = -∑ x ∈ B, (mu x - nu x) * K x y := fun _ => rfl
  -- the pushed-through signed difference (pair form: no stationarity)
  have hdiff : ∀ y, vecMul mu K y - vecMul nu K y = P y - Q y := by
    intro y
    have hsplitA : (∑ x ∈ A, (mu x - nu x) * K x y)
        + (∑ x ∈ B, (mu x - nu x) * K x y)
        = ∑ x : S, (mu x - nu x) * K x y := by
      rw [hAdef, hBdef]
      exact Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => 0 ≤ mu x - nu x) (fun x => (mu x - nu x) * K x y)
    calc vecMul mu K y - vecMul nu K y
        = (∑ x, mu x * K x y) - (∑ x, nu x * K x y) := rfl
      _ = ∑ x, (mu x - nu x) * K x y := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun x _ => (sub_mul _ _ _).symm
      _ = (∑ x ∈ A, (mu x - nu x) * K x y)
          + (∑ x ∈ B, (mu x - nu x) * K x y) := hsplitA.symm
      _ = P y - Q y := by rw [hPy y, hQy y]; ring
  -- both halves stay above the Doeblin floor
  have hPge : ∀ y, c * delta ≤ P y := by
    intro y
    rw [hPy y]
    calc c * delta = ∑ x ∈ A, c * (mu x - nu x) := by
          rw [hdeltadef, ← Finset.mul_sum]
      _ = ∑ x ∈ A, (mu x - nu x) * c :=
          Finset.sum_congr rfl fun x _ => mul_comm _ _
      _ ≤ ∑ x ∈ A, (mu x - nu x) * K x y :=
          Finset.sum_le_sum fun x hx =>
            mul_le_mul_of_nonneg_left (hc x y) (hAnn x hx)
  have hQge : ∀ y, c * delta ≤ Q y := by
    intro y
    rw [hQy y]
    have h1 : ∑ x ∈ B, (mu x - nu x) * K x y
        ≤ c * (∑ x ∈ B, (mu x - nu x)) := by
      calc ∑ x ∈ B, (mu x - nu x) * K x y
          ≤ ∑ x ∈ B, (mu x - nu x) * c :=
            Finset.sum_le_sum fun x hx =>
              mul_le_mul_of_nonpos_left (hc x y) (hBnn x hx)
        _ = c * (∑ x ∈ B, (mu x - nu x)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
    rw [hBdelta] at h1
    calc -∑ x ∈ B, (mu x - nu x) * K x y ≥ -(c * -delta) := neg_le_neg h1
      _ = c * delta := by ring
  -- totals
  have hinner : ∀ x : S, ∑ y : S, (mu x - nu x) * K x y = (mu x - nu x) := by
    intro x
    calc ∑ y : S, (mu x - nu x) * K x y
        = ∑ y : S, K x y * (mu x - nu x) :=
            Finset.sum_congr rfl fun y _ => mul_comm _ _
      _ = (∑ y : S, K x y) * (mu x - nu x) :=
            (Finset.sum_mul Finset.univ (fun y => K x y) (mu x - nu x)).symm
      _ = 1 * (mu x - nu x) := by rw [hrow x]
      _ = mu x - nu x := one_mul _
  have hPsum : ∑ y, P y = delta := by
    have hswap : ∑ y, P y = ∑ y, ∑ x ∈ A, (mu x - nu x) * K x y :=
      Finset.sum_congr rfl fun y _ => hPy y
    rw [hswap, Finset.sum_comm, Finset.sum_congr rfl fun x hx => hinner x]
  have hQsum : ∑ y, Q y = delta := by
    have hstep : ∑ y, ∑ x ∈ B, (mu x - nu x) * K x y = ∑ x ∈ B, (mu x - nu x) := by
      rw [Finset.sum_comm, Finset.sum_congr rfl fun x hx => hinner x]
    calc ∑ y, Q y = -∑ y, ∑ x ∈ B, (mu x - nu x) * K x y := by
          rw [← Finset.sum_neg_distrib]
      _ = -∑ x ∈ B, (mu x - nu x) := by rw [hstep]
      _ = delta := by rw [hBdelta]; ring
  -- the L1 mass of the signed difference
  have hL1d : ∑ x : S, |mu x - nu x| = 2 * delta := by
    have hAabs : ∑ x ∈ A, |mu x - nu x| = ∑ x ∈ A, (mu x - nu x) :=
      Finset.sum_congr rfl fun x hx => abs_of_nonneg (hAnn x hx)
    have hBabs : ∑ x ∈ B, |mu x - nu x| = ∑ x ∈ B, -(mu x - nu x) :=
      Finset.sum_congr rfl fun x hx => abs_of_nonpos (hBnn x hx)
    have hsplit : (∑ x ∈ A, |mu x - nu x|) + (∑ x ∈ B, |mu x - nu x|)
        = ∑ x : S, |mu x - nu x| := by
      rw [hAdef, hBdef]
      exact Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => 0 ≤ mu x - nu x) (fun x => |mu x - nu x|)
    have hneg : ∑ x ∈ B, -(mu x - nu x) = -∑ x ∈ B, (mu x - nu x) := by
      simp
    rw [← hsplit, hAabs, hBabs, hneg, hBdelta]
    ring
  -- the min-overlap floor
  have hsummin : (Fintype.card S : ℝ) * (c * delta) ≤ ∑ y, min (P y) (Q y) := by
    calc (Fintype.card S : ℝ) * (c * delta)
        = ∑ y : S, c * delta := by simp
      _ ≤ ∑ y, min (P y) (Q y) :=
          Finset.sum_le_sum fun y _ => le_min (hPge y) (hQge y)
  -- the L1 identity behind the coupling bound
  have habs : ∀ y, |vecMul mu K y - vecMul nu K y|
      = P y + Q y - 2 * min (P y) (Q y) := by
    intro y
    rw [hdiff y]
    rcases le_total (P y) (Q y) with h | h
    · rw [abs_of_nonpos (by linarith : P y - Q y ≤ 0), min_eq_left h]
      ring
    · rw [abs_of_nonneg (by linarith : 0 ≤ P y - Q y), min_eq_right h]
      ring
  -- assemble
  change (∑ y, |vecMul mu K y - vecMul nu K y|) / 2
      ≤ (1 - (Fintype.card S : ℝ) * c) * ((∑ y, |mu y - nu y|) / 2)
  calc (∑ y, |vecMul mu K y - vecMul nu K y|) / 2
      = (∑ y, (P y + Q y - 2 * min (P y) (Q y))) / 2 := by
        refine congrArg (fun t => t / 2) (Finset.sum_congr rfl fun y _ => habs y)
    _ = ((∑ y, P y) + (∑ y, Q y) - 2 * ∑ y, min (P y) (Q y)) / 2 := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ ((2 * delta) - 2 * ((Fintype.card S : ℝ) * (c * delta))) / 2 := by
        nlinarith [hPsum, hQsum]
    _ = (1 - (Fintype.card S : ℝ) * c) * ((∑ y, |mu y - nu y|) / 2) := by
        rw [hL1d]; ring

/-- (A8 MAIN) One-step contraction TO A STATIONARY measure (sharp
constant): if `π` is stationary for a row-stochastic kernel with
entry floor `c`, then `TV(μK, π) ≤ (1 − |S|·c)·TV(μ, π)` for any `μ`
with the same total mass as `π`. -/
theorem tv_contraction_stationary_sharp (K : S → S → ℝ)
    (hrow : ∀ x, ∑ y, K x y = 1) (c : ℝ) (hc : ∀ x y, c ≤ K x y)
    (pi : S → ℝ) (hstat : ∀ y, vecMul pi K y = pi y) (mu : S → ℝ)
    (hmass : ∑ x, mu x = ∑ x, pi x) :
    Hagi.Prelude.tvDef (vecMul mu K) pi
      ≤ (1 - (Fintype.card S : ℝ) * c) * Hagi.Prelude.tvDef mu pi := by
  have hpi : vecMul pi K = pi := funext hstat
  have halign : Hagi.Prelude.tvDef (vecMul mu K) pi
      = Hagi.Prelude.tvDef (vecMul mu K) (vecMul pi K) := by rw [hpi]
  rw [halign]
  exact tv_pair_contraction K hrow c hc mu pi hmass

omit [Nonempty S] in
/-- `(1 : ℝ) ≤ |S|` for a nonempty finite type. -/
theorem one_le_card_fin (S : Type*) [Fintype S] [Nonempty S] :
    (1 : ℝ) ≤ (Fintype.card S : ℝ) := by
  obtain ⟨a⟩ := ‹Nonempty S›
  rw [← Nat.cast_one, Nat.cast_le]
  exact Finset.one_le_card.2 ⟨a, Finset.mem_univ a⟩

/-- One-step contraction to a stationary measure, audit-text weak
constant: `TV(μK, π) ≤ (1 − c)·TV(μ, π)` (the sharp constant is
`(1 − |S|·c)`, see `tv_contraction_stationary_sharp`; `0 ≤ c` and
nonemptiness make the weak form a corollary). -/
theorem tv_contraction_stationary (K : S → S → ℝ)
    (hrow : ∀ x, ∑ y, K x y = 1) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ x y, c ≤ K x y)
    (pi : S → ℝ) (hstat : ∀ y, vecMul pi K y = pi y) (mu : S → ℝ)
    (hmass : ∑ x, mu x = ∑ x, pi x) :
    Hagi.Prelude.tvDef (vecMul mu K) pi
      ≤ (1 - c) * Hagi.Prelude.tvDef mu pi := by
  refine le_trans (tv_contraction_stationary_sharp K hrow c hc pi hstat mu hmass) ?_
  have h1 : (1 : ℝ) ≤ (Fintype.card S : ℝ) := one_le_card_fin S
  have hnn : 0 ≤ Hagi.Prelude.tvDef mu pi := tvDef_nonneg mu pi
  have key : (1 - (Fintype.card S : ℝ) * c) * Hagi.Prelude.tvDef mu pi
      ≤ (1 - c) * Hagi.Prelude.tvDef mu pi := by
    have hnnn : 0 ≤ ((Fintype.card S : ℝ) - 1) * c * Hagi.Prelude.tvDef mu pi :=
      mul_nonneg (mul_nonneg (by linarith) hc0) hnn
    have hident : (1 - c) * Hagi.Prelude.tvDef mu pi
        - (1 - (Fintype.card S : ℝ) * c) * Hagi.Prelude.tvDef mu pi
        = ((Fintype.card S : ℝ) - 1) * c * Hagi.Prelude.tvDef mu pi := by ring
    linarith
  linarith

omit [Nonempty S] in
/-- TV between two probability vectors is at most one. -/
theorem tvDef_le_one_of_prob (mu nu : S → ℝ)
    (hnn1 : ∀ x, 0 ≤ mu x) (hnn2 : ∀ x, 0 ≤ nu x)
    (hs1 : ∑ x, mu x = 1) (hs2 : ∑ x, nu x = 1) :
    Hagi.Prelude.tvDef mu nu ≤ 1 := by
  have h1 : ∑ y, |mu y - nu y| ≤ ∑ y, (mu y + nu y) :=
    Finset.sum_le_sum fun y _ => abs_le.2 ⟨by linarith [hnn1 y, hnn2 y],
      by linarith [hnn1 y, hnn2 y]⟩
  rw [Finset.sum_add_distrib, hs1, hs2] at h1
  unfold Hagi.Prelude.tvDef
  linarith

end Generic

section WeightFloor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Field-spread weight floor: if all local-field differences at cell
`i` are bounded by `M` in absolute value and `T > 0`, then EVERY
heat-bath weight is at least `exp(−M/T) / card α` — each softmax
exponent is within `M/T` of the largest one, so the normalizer is at
most `card α · exp(M/T)` times the numerator. -/
theorem heatbathWeight_floor (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (y : ι → α) (i : ι) (M : ℝ)
    (hM : ∀ a b, |localField B K y i a - localField B K y i b| ≤ M)
    (hT : 0 < T) (a : α) :
    Real.exp (-(M / T)) / (Fintype.card α : ℝ)
      ≤ heatbathWeight B K T y i a := by
  have hcardpos : 0 < (Fintype.card α : ℝ) :=
    Nat.cast_pos.2 (Fintype.card_pos)
  unfold heatbathWeight softDef
  set La : ℝ := -(localField B K y i a) / T with hLa
  set Z : ℝ := ∑ b : α, Real.exp (-(localField B K y i b) / T) with hZ
  have hZpos : 0 < Z :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hmem : ∀ b : α, Real.exp (-(localField B K y i b) / T)
      ≤ Real.exp La * Real.exp (M / T) := by
    intro b
    have hL : localField B K y i a - localField B K y i b ≤ M :=
      (abs_le.mp (hM a b)).2
    have hexp : -(localField B K y i b) / T ≤ La + M / T := by
      have key : -localField B K y i b / T
          ≤ (-localField B K y i a + M) / T := by
        rw [div_le_div_iff₀ hT hT]
        nlinarith [hT]
      have hsplit : (-localField B K y i a + M) / T
          = -localField B K y i a / T + M / T := by
        rw [add_div]
      linarith
    calc Real.exp (-(localField B K y i b) / T)
        ≤ Real.exp (La + M / T) := Real.exp_le_exp.2 hexp
      _ = Real.exp La * Real.exp (M / T) := Real.exp_add _ _
  have hZle : Z ≤ (Fintype.card α : ℝ) * (Real.exp La * Real.exp (M / T)) := by
    calc Z = ∑ b, Real.exp (-(localField B K y i b) / T) := rfl
      _ ≤ ∑ b : α, Real.exp La * Real.exp (M / T) :=
          Finset.sum_le_sum fun b _ => hmem b
      _ = (Fintype.card α : ℝ) * (Real.exp La * Real.exp (M / T)) := by
          have hsc : ∑ b : α, Real.exp (M / T)
              = (Fintype.card α : ℝ) * Real.exp (M / T) := by simp
          rw [← Finset.mul_sum, hsc]
          ring
  have hexp1 : Real.exp (-(M / T)) * Real.exp (M / T) = 1 := by
    have h0 : (-(M / T)) + M / T = 0 := by ring
    rw [← Real.exp_add, h0, Real.exp_zero]
  have h1 : Real.exp (-(M / T)) * Z
      ≤ Real.exp La * (Fintype.card α : ℝ) := by
    have h2 : Real.exp (-(M / T)) * Z
        ≤ Real.exp (-(M / T))
            * ((Fintype.card α : ℝ) * (Real.exp La * Real.exp (M / T))) :=
      mul_le_mul_of_nonneg_left hZle (Real.exp_nonneg _)
    have h3 : Real.exp (-(M / T))
        * ((Fintype.card α : ℝ) * (Real.exp La * Real.exp (M / T)))
        = Real.exp La * (Fintype.card α : ℝ) := by
      linear_combination (Real.exp La * (Fintype.card α : ℝ)) * hexp1
    linarith
  rw [div_le_div_iff₀ hcardpos hZpos]
  linarith

/-- (A8 MAIN, premise-form) Doeblin floor for the heat-bath kernel:
under the field-spread bound `hM` at cell `i`, temperature `T > 0`,
and the SUPPORT premise `hsupp` (every target `z` agrees with the
source `y` off cell `i` — i.e. every transition is a single-cell
move), the heat-bath kernel is `doeblinMinorized` with floor
`exp(−M/T)/card α`. HONEST: for `card ι ≥ 2` the unconditional
single-cell kernel does NOT satisfy `hsupp` (off-support entries are
zero) — the floor is a premise the consumer must discharge (see
`heatbath_doeblin_floor_subsingleton` for the case where it holds
unconditionally). -/
theorem heatbath_doeblin_floor (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (i : ι) (M : ℝ)
    (hM : ∀ y a b, |localField B K y i a - localField B K y i b| ≤ M)
    (hT : 0 < T)
    (hsupp : ∀ (y z : ι → α), ∀ j, j ≠ i → z j = y j) :
    doeblinMinorized (heatbathKernel B K T i)
      (Real.exp (-(M / T)) / (Fintype.card α : ℝ)) := by
  have hcardpos : 0 < (Fintype.card α : ℝ) :=
    Nat.cast_pos.2 (Fintype.card_pos)
  refine ⟨div_pos (Real.exp_pos _) hcardpos, ?_⟩
  intro y z
  classical
  simp only [heatbathKernel]
  split
  · exact heatbathWeight_floor B K T y i M (hM y) hT (z i)
  · next h => exact absurd (fun j hj => hsupp y z j hj) h

/-- The support premise of `heatbath_doeblin_floor` holds
unconditionally when the cell index type is a subsingleton (a
single-cell configuration space: every target trivially agrees with
the source off the only cell). -/
theorem heatbath_doeblin_floor_subsingleton (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) (i : ι) (M : ℝ)
    (hM : ∀ y a b, |localField B K y i a - localField B K y i b| ≤ M)
    (hT : 0 < T) [Subsingleton ι] :
    doeblinMinorized (heatbathKernel B K T i)
      (Real.exp (-(M / T)) / (Fintype.card α : ℝ)) :=
  heatbath_doeblin_floor B K T i M hM hT
    (fun y z j hj => absurd (Subsingleton.elim j i) hj)

end WeightFloor

section Stationary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The NORMALIZED Boltzmann density: `boltzmannDensity` divided by
its total mass (a genuine probability vector on the finite
configuration space). -/
noncomputable def stationaryDensity (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) : (ι → α) → ℝ :=
  fun y => boltzmannDensity B K T y / (∑ z, boltzmannDensity B K T z)

/-- The normalizer is strictly positive (an exponential sum over a
  nonempty space). -/
theorem stationaryDensity_norm_pos (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) :
    0 < ∑ z, boltzmannDensity B K T z :=
  Finset.sum_pos (fun z _ => Real.exp_pos _) Finset.univ_nonempty

/-- The stationary density is strictly positive everywhere. -/
theorem stationaryDensity_pos (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) (y : ι → α) :
    0 < stationaryDensity B K T y := by
  unfold stationaryDensity
  exact div_pos (Real.exp_pos _) (stationaryDensity_norm_pos B K T)

/-- The stationary density sums to one. -/
theorem stationaryDensity_sum_one (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) :
    ∑ y, stationaryDensity B K T y = 1 := by
  have hZ : 0 < ∑ z, boltzmannDensity B K T z := stationaryDensity_norm_pos B K T
  unfold stationaryDensity
  rw [← Finset.sum_div, div_self (ne_of_gt hZ)]

/-- The normalized Boltzmann density is stationary for the heat-bath
kernel (the unnormalized `heatbath_stationary` divided through by the
constant normalizer). -/
theorem stationaryDensity_stationary (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (hT : T ≠ 0) (i : ι) (z : ι → α) :
    vecMul (stationaryDensity B K T) (heatbathKernel B K T i) z
      = stationaryDensity B K T z := by
  have hZ : 0 < ∑ w, boltzmannDensity B K T w := stationaryDensity_norm_pos B K T
  have hstat := heatbath_stationary B K hK hT i z
  unfold kernelStationary at hstat
  unfold stationaryDensity vecMul
  have hsplit : ∀ y : ι → α,
      (boltzmannDensity B K T y / ∑ w, boltzmannDensity B K T w)
          * heatbathKernel B K T i y z
      = (boltzmannDensity B K T y * heatbathKernel B K T i y z)
          / ∑ w, boltzmannDensity B K T w := by
    intro y
    rw [div_mul_eq_mul_div]
  rw [Finset.sum_congr rfl fun y _ => hsplit y, ← Finset.sum_div, hstat]

/-- (A8 MAIN) One-step TV contraction for the heat-bath kernel,
audit-text weak constant: IF the kernel is Doeblin-minorized with
floor `c` (a PREMISE — see `heatbath_doeblin_floor` for when it
holds), THEN `TV(μK, π̂) ≤ (1 − c)·TV(μ, π̂)` for every probability
vector `μ`, with `π̂` the normalized Boltzmann density. -/
theorem heatbath_tv_contraction (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) (i : ι) (c : ℝ)
    (hD : doeblinMinorized (heatbathKernel B K T i) c)
    (hK : ∀ i j a b, K i j a b = K j i b a) (hT : T ≠ 0)
    (mu : (ι → α) → ℝ) (hmu : ∑ x, mu x = 1) :
    Hagi.Prelude.tvDef (vecMul mu (heatbathKernel B K T i))
        (stationaryDensity B K T)
      ≤ (1 - c) * Hagi.Prelude.tvDef mu (stationaryDensity B K T) :=
  tv_contraction_stationary (heatbathKernel B K T i)
    (fun y => heatbathKernel_rowsum B K T i y) c (le_of_lt hD.1) hD.2 _
    (stationaryDensity_stationary B K hK hT i) mu
    (by rw [hmu, stationaryDensity_sum_one])

/-- (A8 MAIN) One-step TV contraction for the heat-bath kernel, SHARP
constant `1 − |ι→α|·c` (the audit-text `1 − c` form is
`heatbath_tv_contraction`; the row sums force `c ≤ 1/|ι→α|`, so the
sharp constant is the larger contraction rate). -/
theorem heatbath_tv_contraction_sharp (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) (i : ι) (c : ℝ)
    (hD : doeblinMinorized (heatbathKernel B K T i) c)
    (hK : ∀ i j a b, K i j a b = K j i b a) (hT : T ≠ 0)
    (mu : (ι → α) → ℝ) (hmu : ∑ x, mu x = 1) :
    Hagi.Prelude.tvDef (vecMul mu (heatbathKernel B K T i))
        (stationaryDensity B K T)
      ≤ (1 - (Fintype.card (ι → α) : ℝ) * c)
          * Hagi.Prelude.tvDef mu (stationaryDensity B K T) :=
  tv_contraction_stationary_sharp (heatbathKernel B K T i)
    (fun y => heatbathKernel_rowsum B K T i y) c hD.2 _
    (stationaryDensity_stationary B K hK hT i) mu
    (by rw [hmu, stationaryDensity_sum_one])

/-- (A8 MAIN) Geometric mixing: under the Doeblin premise, the n-step
heat-bath chain from ANY start distribution `μ` satisfies
`TV(μKⁿ, π̂) ≤ (1 − c)ⁿ`. The chain stays a probability vector
(`hbChain_sum` / `hbChain_nonneg`) and `TV(μ, π̂) ≤ 1`
(`tvDef_le_one_of_prob`). -/
theorem heatbath_mixing (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) (i : ι) (c : ℝ)
    (hD : doeblinMinorized (heatbathKernel B K T i) c)
    (hK : ∀ i j a b, K i j a b = K j i b a) (hT : T ≠ 0)
    (mu : (ι → α) → ℝ) (hmu : ∑ x, mu x = 1)
    (hnn : ∀ x, 0 ≤ mu x) (n : ℕ) :
    Hagi.Prelude.tvDef (hbChain mu (heatbathKernel B K T i) n)
        (stationaryDensity B K T)
      ≤ (1 - c) ^ n := by
  have hrow : ∀ x, ∑ y, heatbathKernel B K T i x y = 1 :=
    fun x => heatbathKernel_rowsum B K T i x
  have hnnK : ∀ x y, 0 ≤ heatbathKernel B K T i x y :=
    fun x y => heatbathKernel_nonneg B K T i x y
  -- c ≤ 1: the row sums force card · c ≤ 1
  obtain ⟨x0⟩ : Nonempty (ι → α) := inferInstance
  have hcard1 : (1 : ℝ) ≤ (Fintype.card (ι → α) : ℝ) := one_le_card_fin _
  have hcardc : (Fintype.card (ι → α) : ℝ) * c ≤ 1 := by
    have h1 : ∑ y : ι → α, c ≤ ∑ y : ι → α, heatbathKernel B K T i x0 y :=
      Finset.sum_le_sum fun y _ => hD.2 x0 y
    have h2 : ∑ y : ι → α, c = (Fintype.card (ι → α) : ℝ) * c := by simp
    rw [h2, hrow x0] at h1
    exact h1
  have hc1 : 0 ≤ 1 - c := by nlinarith
  have hstep : ∀ m : (ι → α) → ℝ, ∑ x, m x = 1 →
      Hagi.Prelude.tvDef (vecMul m (heatbathKernel B K T i))
          (stationaryDensity B K T)
        ≤ (1 - c) * Hagi.Prelude.tvDef m (stationaryDensity B K T) :=
    fun m hm =>
      heatbath_tv_contraction B K T i c hD hK hT m hm
  induction n with
  | zero =>
      show Hagi.Prelude.tvDef mu (stationaryDensity B K T) ≤ 1
      have hpi : ∀ x, 0 ≤ stationaryDensity B K T x :=
        fun x => le_of_lt (stationaryDensity_pos B K T x)
      exact tvDef_le_one_of_prob mu (stationaryDensity B K T) hnn hpi hmu
        (stationaryDensity_sum_one B K T)
  | succ n ih =>
      have hsumn : ∑ x, hbChain mu (heatbathKernel B K T i) n x = 1 :=
        hbChain_sum (heatbathKernel B K T i) hrow mu hmu n
      show Hagi.Prelude.tvDef
          (vecMul (hbChain mu (heatbathKernel B K T i) n)
            (heatbathKernel B K T i)) (stationaryDensity B K T)
        ≤ (1 - c) ^ (n + 1)
      calc Hagi.Prelude.tvDef
            (vecMul (hbChain mu (heatbathKernel B K T i) n)
              (heatbathKernel B K T i)) (stationaryDensity B K T)
          ≤ (1 - c) * Hagi.Prelude.tvDef
              (hbChain mu (heatbathKernel B K T i) n)
              (stationaryDensity B K T) := hstep _ hsumn
        _ ≤ (1 - c) * ((1 - c) ^ n) :=
            mul_le_mul_of_nonneg_left ih hc1
        _ = (1 - c) ^ (n + 1) := by rw [pow_succ]; ring

/-- (A8 MAIN) Mixing-time corollary: under the Doeblin premise with
`c < 1`, after `n ≥ log e / log (1 − c)` steps the chain is within
`e` (any `e > 0`) of the stationary density in TV. Route: the
geometric bound `heatbath_mixing` plus `exp (n · log (1 − c)) ≤ e`
(the base `1 − c` lies in `(0, 1)`, so `log (1 − c) < 0` and the
division flips). -/
theorem heatbath_mixing_time (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) (i : ι) (c : ℝ)
    (hD : doeblinMinorized (heatbathKernel B K T i) c)
    (hK : ∀ i j a b, K i j a b = K j i b a) (hT : T ≠ 0)
    (mu : (ι → α) → ℝ) (hmu : ∑ x, mu x = 1)
    (hnn : ∀ x, 0 ≤ mu x)
    (e : ℝ) (he : 0 < e) (hc1 : c < 1) (n : ℕ)
    (hn : Real.log e / Real.log (1 - c) ≤ n) :
    Hagi.Prelude.tvDef (hbChain mu (heatbathKernel B K T i) n)
        (stationaryDensity B K T)
      ≤ e := by
  have hmix := heatbath_mixing B K T i c hD hK hT mu hmu hnn n
  have h01 : 0 < 1 - c := by linarith [hD.1]
  have hc0 : 0 < c := hD.1
  have hlogneg : Real.log (1 - c) < 0 := by
    have hlt : 1 - c < (1 : ℝ) := by linarith
    have h := Real.log_lt_log h01 hlt
    rw [Real.log_one] at h
    linarith
  have hnpow : (1 - c) ^ n ≤ e := by
    have hkey : (n : ℝ) * Real.log (1 - c) ≤ Real.log e := by
      have hLne : Real.log (1 - c) ≠ 0 := by
        intro h0
        rw [h0] at hlogneg
        exact absurd hlogneg (by norm_num : ¬(0 : ℝ) < 0)
      have hdiv : Real.log e / Real.log (1 - c) * Real.log (1 - c)
          = Real.log e := by
        field_simp
      calc (n : ℝ) * Real.log (1 - c)
          ≤ (Real.log e / Real.log (1 - c)) * Real.log (1 - c) :=
            mul_le_mul_of_nonpos_right hn (by linarith)
        _ = Real.log e := hdiv
    calc (1 - c) ^ n
        = Real.exp ((n : ℝ) * Real.log (1 - c)) := by
            rw [Real.exp_nat_mul, Real.exp_log h01]
      _ ≤ Real.exp (Real.log e) := Real.exp_le_exp.2 hkey
      _ = e := Real.exp_log he
  linarith

end Stationary

section Fixture
/-! ## Fin 2 × Bool fixture (Bex/Kex/xtt carriers from C260) -/

open Hagi.Energy

/-- Numeric anchor for `heatbathWeight_floor` (no theorem, bare
numbers): with local fields `0` and `3` at the fixture state, the
spread is `3`, and the floor `exp(−3)/2` is below the exact weight
`1/(1 + exp(−3))` of the better value. -/
example : Real.exp (-(3 : ℝ)) / (Fintype.card Bool : ℝ)
    ≤ 1 / (1 + Real.exp (-(3 : ℝ))) := by
  have hpos : 0 < Real.exp (-(3 : ℝ)) := Real.exp_pos _
  have hle : Real.exp (-(3 : ℝ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by norm_num : -(3 : ℝ) ≤ 0)
  have hcard : (Fintype.card Bool : ℝ) = 2 := by norm_num
  have hden : 0 < 1 + Real.exp (-(3 : ℝ)) := by positivity
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [hcard, div_le_div_iff₀ h2 hden]
  nlinarith [hpos, hle, mul_le_mul_of_nonneg_left hle (le_of_lt hpos)]

/-- The same anchor THROUGH `heatbathWeight_floor`: the fixture fields
`L_0(f) = 0`, `L_0(t) = 3` (spread `3` at `T = 1`) give the weight of
the better value `f` the floor `exp(−3)/2`. -/
example : Real.exp (-(3 : ℝ)) / (Fintype.card Bool : ℝ)
    ≤ heatbathWeight Bex Kex 1 xtt 0 false := by
  have hM : ∀ a b : Bool,
      |localField Bex Kex xtt 0 a - localField Bex Kex xtt 0 b| ≤ (3 : ℝ) := by
    intro a b
    have hLt : localField Bex Kex xtt 0 true = 3 := by
      simp only [localField, xtt, Bex, Kex]
      norm_num
    have hLf : localField Bex Kex xtt 0 false = 0 := by
      simp only [localField, xtt, Bex, Kex]
      norm_num
    cases a <;> cases b <;> simp only [hLt, hLf] <;> norm_num
  have hf := heatbathWeight_floor Bex Kex 1 xtt 0 3 hM (by norm_num) false
  simpa using hf

end Fixture

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Greedy finite termination and the focused-policy invariance audit

Track P1-remainder (addendum A11): the two honest closures of the
greedy single-cell search story on a FINITE configuration space.

* `greedy_strict_search_terminates` — (A6 MAIN) on a finite space a
  strictly-improving trajectory cannot be long: a list of
  configurations along which the energy `H` strictly decreases at
  every pair has length at most the number of DISTINCT energy values
  `Fintype.card (Set.image H univ)` (the ranking bound: an infinite
  strictly-descending chain would produce arbitrarily long such
  lists). No rate or complexity claim is made.
* `greedy_search_terminal_is_coordinate_minimum` — (A6 MAIN) a
  terminal state of strict-improvement greedy search — one where NO
  single-cell move has a positive C261 local-field margin — is a
  COORDINATE minimum (`IsCoordinateMinimum` reused verbatim).
* `focusedDisagreementWeight` — the PRACTICAL focused selection rule
  of A9-supplement §E4: cell `i` is weighted by its OWN disagreement
  `Σ_a max 0 (L_i(y_i) − L_i(a))` (state-dependent through y_i itself).
* `concrete_focus_policy_violates_invariance` — (A7 MAIN, NEGATIVE
  witness) the disagreement weight CHANGES under a move of its own
  cell (fixture: `3 → 0`), so the INVARIANCE premise
  `w(y^{i←a})_i = w(y)_i` of `focused_mixture_stationary` FAILS for
  this policy: stationarity of the practical focused sampler is NOT
  certified — premise-form only.

## Honest boundaries (A11 'not to adopt')

* COORDINATE MINIMUM ≠ GLOBAL MINIMUM ≠ VALID SOLUTION: the terminal
  state of greedy search is only a coordinate minimum (ties allowed;
  witness in `Hagi.Energy.SingleCellDescent`: coordinate-min state
  that is not global); energy says nothing about constraints (E4
  separation in `Hagi.Model.EnergyReasoning.EnergyStopping`).
* The termination bound is a LIST bound on a finite type; no
  measure-theoretic packaging, no mixing-time, no convergence rate.
* A7 is a NEGATIVE result by design: it closes the audit question of
  A11 ("focused-policy invariance check — likely VIOLATES") with a
  concrete witness; it does NOT define an alternative invariant
  policy (a y-minus-i-measurable rule would satisfy the premise —
  that is policy design, out of scope).
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy

section Termination

variable {γ : Type*} [Fintype γ]

omit [Fintype γ] in
/-- The energy values along a pairwise strictly-improving trajectory
are pairwise DISTINCT (strictly decreasing), so the mapped list is
`Nodup`. -/
private theorem nodup_map_energy_of_pairwise {H : γ → ℝ} {l : List γ}
    (h : l.Pairwise (fun a b => H b < H a)) : (List.map H l).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rcases List.pairwise_cons.1 h with ⟨hhead, hchain⟩
    have hnod : (List.map H xs).Nodup := ih hchain
    have hlt : ∀ v ∈ (List.map H xs), v < H x := by
      intro v hv
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
      exact hhead b hb
    rw [List.map_cons, List.nodup_cons]
    exact ⟨fun hmem => absurd (hlt (H x) hmem) (lt_irrefl (H x)), hnod⟩

/-- (A6 MAIN) Greedy finite termination: on a FINITE configuration
space, a strictly-improving trajectory (a list of configurations
whose energy `H` strictly decreases along every pair — the
transitive closure of the per-step strict drop) has length at most
the number of DISTINCT energy values `Fintype.card (Set.image H
univ)`. An infinite strictly-descending chain would produce
arbitrarily long such lists, so none exists. The bound is the honest
ranking statement; NO rate, complexity or mixing-time claim is made,
and the terminal state claim is `greedy_search_terminal_is_
coordinate_minimum` below. -/
theorem greedy_strict_search_terminates (H : γ → ℝ) (l : List γ)
    (h : l.Pairwise (fun a b => H b < H a)) :
    l.length ≤ Fintype.card (Set.image H (Set.univ : Set γ)) := by
  have himage : ∀ v ∈ (List.map H l), v ∈ Set.image H (Set.univ : Set γ) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ⟨x, Set.mem_univ _, rfl⟩
  have hnodup : (List.map H l).Nodup := nodup_map_energy_of_pairwise h
  let m : List {x // x ∈ Set.image H (Set.univ : Set γ)} :=
    (List.map H l).attach.map (fun p => ⟨p.1, himage p.1 p.2⟩)
  have hml : m.length = l.length := by simp [m, List.length_attach]
  have hmn : m.Nodup :=
    List.Nodup.map
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
      (List.nodup_attach.mpr hnodup)
  calc l.length = m.length := hml.symm
    _ ≤ Fintype.card {x // x ∈ Set.image H (Set.univ : Set γ)} :=
        hmn.length_le_card

end Termination

section Terminal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- (A6 MAIN) The terminal state of strict-improvement greedy search
is a COORDINATE minimum: if at `y` NO single-cell move has a strictly
positive C261 local-field margin (`0 < L_i(y_i) − L_i(a)` fails for
every cell `i` and value `a` — strict improvement is unavailable),
then `y` is an `IsCoordinateMinimum` (no single-cell move decreases
the energy; ties allowed). HONEST SCOPE: a coordinate minimum is NOT
the global minimum (witness in `Hagi.Energy.SingleCellDescent`) and
NOT a validity certificate (E4 separation in
`Hagi.Model.EnergyReasoning.EnergyStopping`). -/
theorem greedy_search_terminal_is_coordinate_minimum (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (y : ι → α)
    (h : ∀ (i : ι) (a : α),
      ¬ 0 < localField B K y i (y i) - localField B K y i a) :
    IsCoordinateMinimum B K y := by
  intro i a
  have hd := single_cell_move_energy_delta_symm B K hK y i a
  have hle : localField B K y i (y i) ≤ localField B K y i a := by
    linarith [h i a]
  linarith

end Terminal

section FocusAudit

/-! ## A7: the practical focused selection rule vs the C263
INVARIANCE premise. The rule weights cell `i` by its OWN
disagreement — state-dependent through y_i ITSELF, which is
exactly what the invariance premise forbids. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The PRACTICAL focused selection weight of A9-supplement §E4:
cell `i` is weighted by its own disagreement
`Σ_a max 0 (L_i(y_i) − L_i(a))` with `L` the C261 `localField`.
State-dependent through y_i itself (and through the other cells via the
field). This is the rule the CRAM focused sampler actually uses;
against the C263 `focused_mixture_stationary` premises it satisfies
SUPPORT structurally (heat-bath kernels) but INVARIANCE only as an
UNVERIFIED premise — see the witness below. -/
noncomputable def focusedDisagreementWeight (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (y : ι → α) (i : ι) : ℝ :=
  ∑ a, max 0 (localField B K y i (y i) - localField B K y i a)

/-- Local-field anchor on the Fin 2 × Bool fixture (C260 `Bex`/
`Kex`/`xtt`): at cell `0`, whenever `y 1 = true`, the field is
`L_0(c) = if c then 3 else 0` — it depends ONLY on `y 1`, never on
`y 0`. -/
private theorem localField_cell0_fixture (y : Fin 2 → Bool)
    (hy1 : y 1 = true) (c : Bool) :
    localField Bex Kex y 0 c = if c then (3 : ℝ) else 0 := by
  simp only [localField, Bex, Kex]
  fin_cases c <;> norm_num [hy1]

/-- Numeric anchor: at `xtt = (t, t)` the disagreement weight of
cell `0` is `max 0 (3 − 3) + max 0 (3 − 0) = 3`. -/
example : focusedDisagreementWeight Bex Kex xtt 0 = 3 := by
  have hL : ∀ c, localField Bex Kex xtt 0 c = if c then (3 : ℝ) else 0 := by
    intro c
    simp only [localField, Bex, Kex]
    fin_cases c <;> norm_num [xtt]
  simp only [focusedDisagreementWeight, hL, xtt]
  norm_num

/-- (A7 MAIN, NEGATIVE WITNESS) The practical focused selection rule
VIOLATES the INVARIANCE premise of `focused_mixture_stationary`
(C263): after the greedy move of cell `0` from `t` to `f` (its local
field minimizer on the fixture), the weight of cell `0` DROPS from
`3` to `0` — `w(y^{0←f})_0 ≠ w(y)_0`. The weight depends on y_0
itself through `L_i(y_i)`, which is exactly what the premise
forbids. Consequence, stated honestly: the C263 stationarity
theorem applies to the practical focused sampler ONLY in
premise-form — the INVARIANCE premise is FALSE for this policy, so
NO stationarity claim for the practical focused sampler is certified
here. -/
theorem concrete_focus_policy_violates_invariance :
    focusedDisagreementWeight Bex Kex (Function.update xtt 0 false) 0
      ≠ focusedDisagreementWeight Bex Kex xtt 0 := by
  have hy0 : Function.update xtt 0 false 0 = false :=
    Function.update_self 0 false xtt
  have hL : ∀ c, localField Bex Kex (Function.update xtt 0 false) 0 c
      = if c then (3 : ℝ) else 0 := by
    intro c
    simp only [localField, Bex, Kex]
    fin_cases c <;> norm_num [xtt]
  have hw0 : focusedDisagreementWeight Bex Kex
      (Function.update xtt 0 false) 0 = 0 := by
    simp only [focusedDisagreementWeight, hL, hy0]
    norm_num
  have hw1 : focusedDisagreementWeight Bex Kex xtt 0 = 3 := by
    have hL' : ∀ c, localField Bex Kex xtt 0 c = if c then (3 : ℝ) else 0 := by
      intro c
      simp only [localField, Bex, Kex]
      fin_cases c <;> norm_num [xtt]
    simp only [focusedDisagreementWeight, hL', xtt]
    norm_num
  rw [hw0, hw1]
  norm_num

end FocusAudit

section Fixture
/-! ## Fin 2 × Bool fixture: the termination bound closes on a
concrete two-state trajectory (C260 carriers). -/

/-- Bound fixture: the two-state strictly-decreasing trajectory
`[true, false]` under `H = fun b => if b then 1 else 0` has length
`2` at most the cardinality of the two-element energy image. -/
example :
    ([true, false] : List Bool).length ≤
    Fintype.card (Set.image (fun b => if b then (1 : ℝ) else 0)
      (Set.univ : Set Bool)) := by
  refine greedy_strict_search_terminates _ _ ?_
  simp [List.pairwise_cons]

end Fixture

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Concrete validity separation for penalty energies

Track P1-remainder (addendum A11, item A5): the E4 separation premise
"H(y) ≤ τ ⇒ valid(y)" INSTANTIATED for concrete penalty energies —
proved, not postulated. Primary instance: graph coloring with a
conflict-count energy realized as the pairwise energy
`Hagi.Energy.pairwiseEnergy`.

* `energy_threshold_lt_min_penalty_implies_valid` — (A5 CORE,
  premise-form) if the energy is a finite sum of nonnegative
  penalties, every nonzero penalty is at least `pmin > 0`, and zero
  penalties imply validity, then energy `< pmin` gives validity.
  This is the reusable core covering integer-penalty families
  (sudoku cell/duplicate penalties, nqueens attack pairs) in
  premise-form: each family supplies its own `hviol`/`hvalid`.
* `graph_coloring_zero_energy_iff_valid` — the conflict-count energy
  `pairwiseEnergy 0 (coloringCoupling edges) y` is ZERO exactly when
  `y` is a proper coloring of `edges` (adjacency-agnostic: `edges`
  is a Finset of ordered pairs; off-diagonal premise `hnodiag`).
* `graph_coloring_separation` — the SEPARATION PREMISE PROVED for
  the coloring family at any `τ < 1`: a configuration with energy
  `≤ τ` preserves the givens (unary penalty part, via the core
  lemma) and is a proper coloring (pairwise part: each violated
  undirected edge costs exactly 1 — both ordered indicators under
  the E1 `½`-ordered-pair convention — so any violation forces
  energy ≥ 1 > τ; family-optimal threshold, `τ < 1`).
* `graph_coloring_stop_sep_valid` — an `EnergyStop` at `τ < 1`
  PRODUCES a `ValidityCertificate` through
  `stopping_sound_of_separation` with the separation premise proved
  above (an instance, not an axiom).
* `graph_coloring_stop_proper` — the companion theorem carrying the
  FULL proper-coloring content of the same stop.

## Honest boundaries (A11 'not to adopt')

* The E4 cert-kernel's unary constraint slot `C : ι → α → Prop`
  cannot express the binary edge constraint "colors differ along
  every edge"; the `ValidityCertificate` below therefore records the
  unary part (`preserves_givens` + differ from every GIVEN-colored
  neighbor), while the full proper-coloring content ships as
  `graph_coloring_stop_proper`. No overclaim is made that the
  certificate alone encodes proper coloring.
* LEARNED energies have NO such separation: a low learned energy
  does NOT imply validity (the E4 zero-field witness in
  `Hagi.Model.EnergyReasoning.EnergyStopping`: zero energy, invalid
  board). Acceptance of learned-sampler output is only via an
  independent validator — the `CRAMAcceptedSolution` route of the
  A9-supplement cert-kernel.
* `τ < 1` needs the symmetry premise `hsym` on the ordered edge set
  (one violated undirected edge contributes two ordered indicators;
  without symmetry a single directed conflict costs only `½`). The
  zero-energy iff needs only `hnodiag`.
* Sudoku/nqueens are NOT separately instantiated here; the general
  core covers them abstractly in premise-form.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- (A5 CORE, premise-form) Energy-separation for integer penalty
sums: if the energy is the finite sum of nonnegative penalties
(`hpen`), every nonzero penalty is at least `pmin > 0` (`hviol`),
and zero penalties imply validity (`hvalid`), then an energy below
`pmin` yields `Valid y`. The premise `hvalid` is one-directional by
design: only "zero penalties ⇒ valid" is needed; the converse is not
smuggled in. Reusable across integer-penalty families (coloring
conflicts here; sudoku/nqueens penalties in premise-form). -/
theorem energy_threshold_lt_min_penalty_implies_valid
    {κ : Type*} [Fintype κ] {Valid : (ι → α) → Prop}
    (penalty : (ι → α) → κ → ℝ) {pmin : ℝ} (_hpmin : 0 < pmin)
    (hpen : ∀ y' k, 0 ≤ penalty y' k)
    (hviol : ∀ y' k, penalty y' k ≠ 0 → pmin ≤ penalty y' k)
    (hvalid : ∀ y' : ι → α, (∀ k, penalty y' k = 0) → Valid y')
    {y : ι → α} (h : ∑ k, penalty y k < pmin) : Valid y := by
  refine hvalid y (fun k => ?_)
  by_contra h0
  have hne : penalty y k ≠ 0 := fun hc => h0 hc
  have hle : penalty y k ≤ ∑ k', penalty y k' :=
    Finset.single_le_sum (fun k' _ => hpen y k') (Finset.mem_univ k)
  have := hviol y k hne
  linarith

end General

section Coloring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Proper coloring, adjacency-agnostic: `y` is proper for the graph
given by the ordered-pair edge set `edges` when colors differ along
every edge. `edges` is the ordered representation (the graph is its
symmetric hull; `hsym` premises make this explicit where needed). -/
def isProperColoring (edges : Finset (ι × ι)) (y : ι → α) : Prop :=
  ∀ p ∈ edges, y p.1 ≠ y p.2

/-- The coloring coupling: the pairwise kernel realizing the
conflict-count energy — `K i j a b = 1` exactly on ordered edges with
equal endpoint colors, `0` otherwise. With the E1 convention
(`pairwiseEnergy B K y = Σᵢ B i (y i) + ½·Σ_{i≠j} K i j (y i) (y j)`)
this energy IS the (half-ordered) conflict count: no separate count
function is asserted equal to H — H is the conflict count by
construction. -/
def coloringCoupling (edges : Finset (ι × ι)) : ι → ι → α → α → ℝ :=
  fun i j a b => if (i, j) ∈ edges ∧ a = b then (1 : ℝ) else 0

/-- The unary given-violation penalty: `B i a = 1` when cell `i` has
a given color and `a` differs from it, `0` otherwise (precoloring
penalty for the `givens` of the certificate). -/
def coloringField (givens : ι → Option α) : ι → α → ℝ :=
  fun i a => if ∃ b, givens i = some b ∧ a ≠ b then (1 : ℝ) else 0

/-- Zero-energy iff validity for the pure coloring family (no unary
field): the conflict-count energy vanishes exactly on proper
colorings. Off-diagonal premise `hnodiag` (a diagonal "edge"
`(i, i)` never has differing endpoint colors, so zero energy cannot
imply properness there; diagonal pairs contribute nothing to the
ordered sum). -/
theorem graph_coloring_zero_energy_iff_valid (edges : Finset (ι × ι))
    (y : ι → α) (hnodiag : ∀ i, (i, i) ∉ edges) :
    pairwiseEnergy (fun _ _ => (0 : ℝ)) (coloringCoupling edges) y = 0
      ↔ isProperColoring edges y := by
  have hnn : ∀ i j, (0 : ℝ) ≤ coloringCoupling edges i j (y i) (y j) := by
    intro i j; unfold coloringCoupling; split <;> norm_num
  have hinn : ∀ i, (0 : ℝ) ≤ ∑ j ∈ Finset.univ \ {i},
      coloringCoupling edges i j (y i) (y j) :=
    fun i => Finset.sum_nonneg fun j _ => hnn i j
  constructor
  · rintro h ⟨a, b⟩ hab hcon
    -- hab : (a, b) ∈ edges, hcon : y a = y b; derive energy > 0
    have hoff : a ≠ b := by
      intro he
      rw [he] at hab
      exact hnodiag b hab
    have h1 : coloringCoupling edges a b (y a) (y b) = 1 := by
      unfold coloringCoupling; rw [if_pos ⟨hab, hcon⟩]
    have hinner1 : (1 : ℝ) ≤ ∑ j ∈ Finset.univ \ {a},
        coloringCoupling edges a j (y a) (y j) := by
      rw [← h1]
      exact Finset.single_le_sum (fun j _ => hnn a j)
        (Finset.mem_sdiff.2 ⟨Finset.mem_univ b,
          fun hb => hoff (Finset.mem_singleton.1 hb).symm⟩)
    have hge : (1 : ℝ) ≤ pairwiseInteractionSum (coloringCoupling edges) y := by
      rw [pairwiseInteractionSum]
      calc (1:ℝ) ≤ ∑ j ∈ Finset.univ \ {a},
          coloringCoupling edges a j (y a) (y j) := hinner1
        _ ≤ ∑ i, ∑ j ∈ Finset.univ \ {i},
            coloringCoupling edges i j (y i) (y j) :=
          Finset.single_le_sum (fun i _ => hinn i) (Finset.mem_univ a)
    rw [pairwiseEnergy, Finset.sum_const_zero, zero_add] at h
    linarith
  · intro h
    have hzero : pairwiseInteractionSum (coloringCoupling edges) y = 0 := by
      rw [pairwiseInteractionSum]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_
      have hne : i ≠ j := by
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
        obtain ⟨_, hj'⟩ := hj
        exact fun he => hj' he.symm
      unfold coloringCoupling
      by_cases hc : (i, j) ∈ edges ∧ y i = y j
      · exact (h (i, j) hc.1 hc.2).elim
      · rw [if_neg hc]
    rw [pairwiseEnergy, Finset.sum_const_zero, zero_add, hzero, mul_zero]

/-- The separation premise PROVED for the coloring family at any
`τ < 1`: a configuration `y` with conflict-plus-given energy `≤ τ`
preserves every given value and is a proper coloring. Unary part via
the A5 core lemma (each given violation costs `1`); pairwise part by
symmetric doubling — a violated undirected edge contributes BOTH
ordered indicators under the E1 `½` convention, so any violation
forces energy `≥ 1 > τ` (family-optimal: one violated undirected
edge costs exactly `1`). -/
theorem graph_coloring_separation (givens : ι → Option α)
    (edges : Finset (ι × ι)) (τ : ℝ)
    (hsym : ∀ i j, (i, j) ∈ edges → (j, i) ∈ edges)
    (hnodiag : ∀ i, (i, i) ∉ edges) (hτ : τ < 1)
    (y : ι → α)
    (h : pairwiseEnergy (coloringField givens) (coloringCoupling edges) y ≤ τ) :
    (∀ i a, givens i = some a → y i = a) ∧ isProperColoring edges y := by
  have hBnn : ∀ i, (0 : ℝ) ≤ coloringField givens i (y i) := by
    intro i; unfold coloringField; split <;> norm_num
  have hBsum : (0 : ℝ) ≤ ∑ i, coloringField givens i (y i) :=
    Finset.sum_nonneg fun i _ => hBnn i
  have hKnn : ∀ i j, (0 : ℝ) ≤ coloringCoupling edges i j (y i) (y j) := by
    intro i j; unfold coloringCoupling; split <;> norm_num
  have hintnn : ∀ i, (0 : ℝ) ≤ ∑ j ∈ Finset.univ \ {i},
      coloringCoupling edges i j (y i) (y j) :=
    fun i => Finset.sum_nonneg fun j _ => hKnn i j
  rw [pairwiseEnergy] at h
  constructor
  · -- unary given penalties via the A5 core, pmin = 1
    have hBlt : ∑ i, coloringField givens i (y i) < 1 := by
      have hnn' : (0 : ℝ) ≤ pairwiseInteractionSum (coloringCoupling edges) y :=
        Finset.sum_nonneg fun i _ => hintnn i
      linarith
    exact energy_threshold_lt_min_penalty_implies_valid
      (ι := ι) (α := α) (κ := ι)
      (Valid := fun y' => ∀ i a, givens i = some a → y' i = a)
      (penalty := fun y' i => coloringField givens i (y' i))
      (pmin := 1) (by norm_num)
      (fun y' i => by unfold coloringField; split <;> norm_num)
      (fun y' i _hne => by
        rcases Classical.em (∃ b, givens i = some b ∧ y' i ≠ b) with hc | hc
        · unfold coloringField; rw [if_pos hc]
        · unfold coloringField at _hne ⊢
          rw [if_neg hc] at _hne; exact absurd rfl _hne)
      (fun y' hz i a hg => by
        by_contra hcon
        have h1 : coloringField givens i (y' i) = 1 := by
          unfold coloringField
          rw [if_pos ⟨a, hg, hcon⟩]
        rw [hz i] at h1
        norm_num at h1)
      hBlt
  · -- pairwise conflicts: each violated (symmetric) edge costs ≥ 1
    by_contra hpr
    obtain ⟨p, hp0⟩ := not_forall.mp hpr
    obtain ⟨hp, hpne⟩ := not_imp.mp hp0
    have hconf : y p.1 = y p.2 := by
      by_contra hc
      exact hpne hc
    have hpe : (p.1, p.2) ∈ edges := by rw [Prod.mk.eta]; exact hp
    have hoff : p.1 ≠ p.2 := by
      intro he
      rw [he] at hpe
      exact hnodiag p.2 hpe
    have hin1 : coloringCoupling edges p.1 p.2 (y p.1) (y p.2) = 1 := by
      unfold coloringCoupling; rw [if_pos ⟨hpe, hconf⟩]
    have hin2 : coloringCoupling edges p.2 p.1 (y p.2) (y p.1) = 1 := by
      unfold coloringCoupling; rw [if_pos ⟨hsym p.1 p.2 hpe, hconf.symm⟩]
    have hinner1 : (1 : ℝ) ≤ ∑ j ∈ Finset.univ \ {p.1},
        coloringCoupling edges p.1 j (y p.1) (y j) := by
      rw [← hin1]
      exact Finset.single_le_sum (fun j _ => hKnn p.1 j)
        (Finset.mem_sdiff.2 ⟨Finset.mem_univ p.2,
          fun hb => hoff (Finset.mem_singleton.1 hb).symm⟩)
    have hinner2 : (1 : ℝ) ≤ ∑ j ∈ Finset.univ \ {p.2},
        coloringCoupling edges p.2 j (y p.2) (y j) := by
      rw [← hin2]
      exact Finset.single_le_sum (fun j _ => hKnn p.2 j)
        (Finset.mem_sdiff.2 ⟨Finset.mem_univ p.1,
          fun hb => hoff (Finset.mem_singleton.1 hb)⟩)
    have hpair : ∑ i ∈ ({p.1, p.2} : Finset ι), ∑ j ∈ Finset.univ \ {i},
        coloringCoupling edges i j (y i) (y j)
        = (∑ j ∈ Finset.univ \ {p.1}, coloringCoupling edges p.1 j (y p.1) (y j))
          + ∑ j ∈ Finset.univ \ {p.2}, coloringCoupling edges p.2 j (y p.2) (y j) :=
      Finset.sum_pair hoff
    have hrest : (0 : ℝ) ≤ ∑ i ∈ Finset.univ \ ({p.1, p.2} : Finset ι),
        ∑ j ∈ Finset.univ \ {i}, coloringCoupling edges i j (y i) (y j) :=
      Finset.sum_nonneg fun i _ => hintnn i
    have hsplit := Finset.sum_sdiff
      (s₁ := ({p.1, p.2} : Finset ι)) (s₂ := (Finset.univ : Finset ι))
      (f := fun i => ∑ j ∈ Finset.univ \ {i},
        coloringCoupling edges i j (y i) (y j))
      (Finset.subset_univ _)
    have hintge : (2 : ℝ) ≤ pairwiseInteractionSum (coloringCoupling edges) y := by
      rw [pairwiseInteractionSum]
      linarith
    linarith

/-- An `EnergyStop` for the coloring family at `τ < 1` PRODUCES a
`ValidityCertificate` — the E4 separation transfer with the premise
PROVED (this instance, not an axiom): the unary constraint slot
records "differ from every GIVEN-colored neighbor" plus
`preserves_givens`. HONEST BOUNDARY: the unary slot cannot express
the binary edge constraint; the FULL proper-coloring content ships
as the companion `graph_coloring_stop_proper`. -/
def graph_coloring_stop_sep_valid (givens : ι → Option α)
    (edges : Finset (ι × ι)) (τ : ℝ)
    (hsym : ∀ i j, (i, j) ∈ edges → (j, i) ∈ edges)
    (hnodiag : ∀ i, (i, i) ∉ edges) (hτ : τ < 1)
    (s : EnergyStop (coloringField givens) (coloringCoupling edges) τ) :
    ValidityCertificate givens
      (fun i a => ∀ j b, (i, j) ∈ edges ∧ givens j = some b → a ≠ b) :=
  stopping_sound_of_separation _ _ _ _ _
    (fun y' hy' => by
      obtain ⟨hgiv, hprop⟩ :=
        graph_coloring_separation givens edges τ hsym hnodiag hτ y' hy'
      refine ⟨hgiv, fun i j b hj => ?_⟩
      obtain ⟨hmem, hgb⟩ := hj
      have h1 : y' j = b := hgiv j b hgb
      have h2 : y' i ≠ y' j := hprop (i, j) hmem
      exact fun hc => h2 (hc.trans h1.symm))
    s

/-- The companion theorem carrying the FULL proper-coloring content
of the same energy stop: the stopped configuration is a proper
coloring of `edges` (binary constraints — beyond the unary slot of
`ValidityCertificate`, see `graph_coloring_stop_sep_valid`). -/
theorem graph_coloring_stop_proper (givens : ι → Option α)
    (edges : Finset (ι × ι)) (τ : ℝ)
    (hsym : ∀ i j, (i, j) ∈ edges → (j, i) ∈ edges)
    (hnodiag : ∀ i, (i, i) ∉ edges) (hτ : τ < 1)
    (s : EnergyStop (coloringField givens) (coloringCoupling edges) τ) :
    isProperColoring edges s.y :=
  (graph_coloring_separation givens edges τ hsym hnodiag hτ s.y
    s.energy_bound).2

end Coloring

/-! ## Triangle fixture (Fin 3): anchors of the separation -/

section Fixture

/-- The triangle K₃ as a symmetric ordered edge set (Fin 3). -/
private def tri : Finset (Fin 3 × Fin 3) :=
  {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}

private theorem tri_nodiag : ∀ i : Fin 3, (i, i) ∉ tri := by
  intro i hi
  simp only [tri, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hi
  rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at h2 <;> exact absurd h2 (by decide)

/-- Anchor: 2 colors do NOT suffice — no proper 2-coloring of the
triangle exists (the separation family is non-vacuous: zero-energy
configurations exist only with ≥ 3 colors). -/
example : ¬ ∃ y : Fin 3 → Bool, isProperColoring tri y := by
  rintro ⟨y, hy⟩
  have h01 := hy (0, 1) (by simp [tri])
  have h02 := hy (0, 2) (by simp [tri])
  have h12 := hy (1, 2) (by simp [tri])
  revert h01 h02 h12
  cases h0 : y 0 <;> cases h1 : y 1 <;> cases h2 : y 2 <;>
    simp_all [h0, h1, h2]

/-- Anchor: 3 colors suffice — the identity coloring of the triangle
has ZERO energy (the `iff` in the zero-separation direction). -/
example : pairwiseEnergy (fun _ _ => (0 : ℝ)) (coloringCoupling tri)
    (fun i => i) = 0 := by
  have hprop : isProperColoring tri (fun i : Fin 3 => i) := by
    intro p hp
    simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  exact (graph_coloring_zero_energy_iff_valid tri _ tri_nodiag).2 hprop

/-- Anchor: the monochrome coloring has conflicts, hence NONZERO
energy (the `iff` in the converse direction). -/
example : pairwiseEnergy (fun _ _ => (0 : ℝ)) (coloringCoupling tri)
    (fun _ => (0 : Fin 3)) ≠ 0 := by
  intro hc
  have := (graph_coloring_zero_energy_iff_valid tri _ tri_nodiag).1 hc
    (0, 1) (by simp [tri])
  simp at this

end Fixture

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Alternating (z, y) round: strict descent with an inexact latent

Track B4 (master-plan-v3 addendum A11 B4: "alternating minimization
with summable errors ... важно не выдавать текущий frozen-z result
за joint convergence"). DESIGN-FIRST beat: the joint latent-visible
descent is organized as ALTERNATING ROUNDS with per-round
tolerances (route R1 of `.tmp/C293/design.md`):

  round t = z-phase (settle `z` toward `z*` to tolerance η_t) +
            y-phase (one guarded visible move on computed
            `K(z_t)`-fields with the COMPOSED guard).

Structural fact driving the design: `latentUpdate N m G` and
`latentEnergy N m G` do NOT depend on the visible state `y`, so the
latent fixed point `z*` is STATIC across rounds — the coupling is
one-way (z → visible through `attentionK`). Route R2 (small-gain
floor `ε_round/(1−q)`) degenerates to R1's slack inequality in this
regime (no moving latent target ⇒ no nonzero asymptotic floor);
route R3 (joint Lyapunov `E_vis + c·‖z−z*‖²`) would need the
z-differentiability that the E3 protocol forbids claiming.

Main results:

* `alternating_round_nonincreasing` — (B4 MAIN, ROUND THEOREM,
  strict form) one full z-then-y round with an INEXACT latent: if
  the z-phase delivers `‖z_t − z*‖ ≤ η` (premise-form: contracted
  through the declared softmax-Lipschitz premise
  `hsoft : |w(z_t) − w(z*)| ≤ Lsm·η`, delivery lemma
  `LatentEnergy.latent_settle_tolerance`), the computed fields
  `L̂` of the `K(z_t)`-energy carry numerical error ≤ ε (C270
  premise), and the computed margin clears the COMPOSED slack
  `2·(ε + |S_i|·2κmax·fmax·L_sm·η)` (C270's 2ε plus C271's coupling
  bound), then the visible energy at the TRUE frozen-z* kernel
  `pairwiseEnergy B (attentionK κ w(z*) f)` STRICTLY decreases
  across the round. Composition of `guarded_energy_delta` with
  `latent_error_couples_field` via the triangle inequality — the
  frozen statements are used, not restated. Additive over C271's
  `latent_attention_guarded_drop`: the SEPARATE numerical ε on top
  of the coupling η and the round packaging.
* `alternating_zphase_one_step_error` — (B4 η-bookkeeping brick)
  one z-phase step from ANY state contracts the latent error:
  `‖latentUpdate N m G z − z*‖ ≤ (Δ/m)·‖z − z*‖` for a fixed point
  `z*` — per-round tolerances satisfy η_t ≤ q·η_{t−1}, q = Δ/m,
  WITHOUT restarting (the summability input of the R1 design).
* `alternating_round_slack_summable` — (B4 N1, C294) ROUND-ERROR
  SUMMABILITY: a round-guard slack sequence with premise-form
  geometric decay `slack (t+1) ≤ (Δ/m)·slack t` (delivered for
  the coupling part by `alternating_zphase_one_step_error`) has
  ALL partial sums bounded by the geometric budget
  `slack 0 · m/(m−Δ)`.
* `alternating_trajectory_bound` / `alternating_trajectory_
descent_budget` — (B4 N2, C294) TRAJECTORY TELESCOPING: rounds
  each dropping `d t` (premise-form) telescope to
  `E (y N) ≤ E (y 0) − Σ d t`; with a bounded-below PREMISE
  `Emin ≤ E (y t)` the total descent is budgeted by
  `E (y 0) − Emin` (the floor is a hypothesis, not a conclusion).
* `alternating_rounds_converge` — (B4 N3, C294) TERMINAL FINITE
  FORM: on a finite configuration space, strictly-decreasing
  alternating rounds terminate (length ≤ card of the energy
  image) — the C268 ranking bound reused; the unconditional
  analytic convergence stays OPEN (pinned negative).

## Honest boundaries (B4)

* PREMISE-FORM throughout: the z-phase inexactness (η, `hsoft`) and
  the numerical field error (ε) are HYPOTHESES, not conclusions;
  the softmax-Lipschitz step remains a declared premise (C271
  honesty inherited), and rejection below the slack carries no
  information (C270 honesty inherited).
* NO UNCONDITIONAL joint `(z, y)` convergence theorem exists or is
  claimed: the names `alternating_round_converges` and
  `visible_descent_joint_z` are NONEXISTENT (RootApi negative
  pins). What is proven: ONE round, strictly, under premises. The
  chain/summability follow-ups are the recorded next statements
  (N1 round chain nonincrease, N2 η_t summability, N3 bounded-below
  round decreases) — none of them claimed here.
* The latent block of a round is inexact but STATIC-TARGETED: the
  y-independence of `z*` is why no `ε_round/(1−q)` floor appears;
  if the latent energy ever becomes y-dependent, R2's small-gain
  machinery becomes necessary and this file's design must be
  revisited (design doc records the dispositions).
* C294 convergence lift (N1–N3) stays PREMISE-FORM and FINITE:
  the geometric slack decay and the per-round drops are HYPOTHESES;
  the energy floor `Emin` is a PREMISE; the terminal statement is
  the FINITE/STRICT form only (length bound via the C268 ranking
  argument). The UNCONDITIONAL analytic convergence statement
  `alternating_round_converges` STILL does not exist and stays
  OPEN (RootApi negative pin unchanged); the near-name
  `alternating_rounds_converge` (plural) is the finite terminal
  form and states termination, NOT convergence to a minimizer.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (localField pairwiseEnergy)

/-! ## The round theorem -/
section Round

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- **`alternating_round_nonincreasing`** — (B4 MAIN, ROUND THEOREM,
strict form) one full z-then-y round with an inexact latent: with
the z-phase settled-state weights `w1 = w(z_t)` within `Lsm·η` of
the fixed-point weights `w2 = w(z*)` (premise-form delivery: η is
the settle tolerance of `latent_settle_tolerance`, composed through
the declared softmax-Lipschitz premise), computed fields `L̂` of the
`K(z_t)`-energy within ε of the exact ones (C270 numerical
premise), and the computed margin clearing the COMPOSED slack
`2·(ε + |S_i|·2κmax·fmax·(Lsm·η))`, the visible energy at the TRUE
frozen-z* kernel STRICTLY decreases across the round. -/
theorem alternating_round_nonincreasing [Nonempty α]
    (B : ι → α → ℝ) (κ : ι → ι → ℝ) (w1 w2 : ι → ι → ℝ) (f : α → α → ℝ)
    {κmax fmax Lsm η ε : ℝ} (hκ : ∀ i j, 0 ≤ κ i j ∧ κ i j ≤ κmax)
    (hf : ∀ a b, |f a b| ≤ fmax)
    (hε : 0 ≤ ε)
    (hsoft : ∀ i j, |w1 i j - w2 i j| ≤ Lsm * η)
    (y : ι → α) (i : ι) (a : α) (Lhat : ι → α → ℝ)
    (herr : ∀ b, |Lhat i b - localField B (attentionK κ w1 f) y i b| ≤ ε)
    (hguard : 2 * (ε + ((Finset.univ \ {i}).card : ℝ)
        * (2 * κmax * fmax * (Lsm * η)))
      < Lhat i (y i) - Lhat i a) :
    pairwiseEnergy B (attentionK κ w2 f) (Function.update y i a)
      < pairwiseEnergy B (attentionK κ w2 f) y := by
  have hfmax : (0:ℝ) ≤ fmax := le_trans (abs_nonneg (f (Classical.arbitrary α)
    (Classical.arbitrary α))) (hf _ _)
  have hκmax : (0:ℝ) ≤ κmax := le_trans (hκ i i).1 (hκ i i).2
  have hLη : (0:ℝ) ≤ Lsm * η := le_trans (abs_nonneg _) (hsoft i i)
  set C : ℝ := ((Finset.univ \ {i}).card : ℝ) * (2 * κmax * fmax * (Lsm * η))
    with hC
  have hC0 : (0:ℝ) ≤ C :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hκmax) hfmax) hLη)
  have htot : ∀ b, |Lhat i b - localField B (attentionK κ w2 f) y i b| ≤ ε + C := by
    intro b
    have h1 := herr b
    have h2 := latent_error_couples_field B κ w1 w2 f hκ hf hsoft y i b
    calc |Lhat i b - localField B (attentionK κ w2 f) y i b|
        = |(Lhat i b - localField B (attentionK κ w1 f) y i b)
            + (localField B (attentionK κ w1 f) y i b
                - localField B (attentionK κ w2 f) y i b)| := by ring_nf
      _ ≤ |Lhat i b - localField B (attentionK κ w1 f) y i b|
          + |localField B (attentionK κ w1 f) y i b
              - localField B (attentionK κ w2 f) y i b| := abs_add_le _ _
      _ ≤ ε + C := by linarith
  exact guarded_energy_delta B (attentionK κ w2 f)
    (attention_K_symmetric κ w2 f) y i a Lhat (ε + C)
    (by linarith) htot hguard

end Round

/-! ## The η-bookkeeping brick -/
section ZPhase

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`alternating_zphase_one_step_error`** — (B4 η-bookkeeping
brick) one z-phase step contracts the latent error toward the
(y-independent, static) fixed point: for `latentUpdate N m G zstar =
zstar`, `‖latentUpdate N m G z − zstar‖ ≤ (Δ/m)·‖z − zstar‖`. This
is the summability input of the R1 design (per-round tolerance
η_t ≤ q·η_{t−1}, q = Δ/m, without restarting the settle loop); the
summable-series statement itself is NOT claimed here. -/
theorem alternating_zphase_one_step_error (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar z : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    ‖latentUpdate N m G z - zstar‖ ≤ ((Δ : ℝ) / m) * ‖z - zstar‖ := by
  have h := latent_update_contraction N m G hΔ hm z zstar
  rw [hz] at h
  exact h

end ZPhase

/-! ## N1: round-error summability (geometric slack budget) -/
section SlackSummable

private theorem slack_partial_sum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (slack : ℕ → ℝ) (hs0 : 0 ≤ slack 0)
    (hslack : ∀ t, slack (t + 1) ≤ q * slack t) (N : ℕ) :
    ∑ t ∈ Finset.range N, slack t
      ≤ slack 0 * (1 - q ^ N) / (1 - q) := by
  have hdec : ∀ t, slack t ≤ q ^ t * slack 0 := fun t =>
    Hagi.Probability.compounding_bound q hq0 slack hslack t
  induction N with
  | zero => simp
  | succ n ih =>
    have hqn : 0 ≤ q ^ n := pow_nonneg hq0 n
    have h1 : (0:ℝ) < 1 - q := by linarith
    have h2 := hdec n
    have h3 : (1 - q) * slack n ≤ (1 - q) * (q ^ n * slack 0) :=
      mul_le_mul_of_nonneg_left h2 h1.le
    have h5 : (0:ℝ) ≤ q ^ n * slack 0 := mul_nonneg hqn hs0
    rw [Finset.sum_range_succ]
    calc ∑ t ∈ Finset.range n, slack t + slack n
        ≤ slack 0 * (1 - q ^ n) / (1 - q) + slack n :=
            add_le_add ih (le_refl _)
      _ ≤ slack 0 * (1 - q ^ (n + 1)) / (1 - q) := by
          have h4 : q ^ (n + 1) = q ^ n * q := pow_succ q n
          rw [h4]
          field_simp
          nlinarith [hqn, h5, h3]

/-- **`alternating_round_slack_summable`** — (B4 N1, C294,
ROUND-ERROR SUMMABILITY) the composed round-guard slack with
geometric decay (premise-form `slack (t+1) ≤ (Δ/m)·slack t`; the
delivery for the C·η_t part is `alternating_zphase_one_step_error`)
has ALL partial sums bounded by the geometric-series budget
`slack 0 * m/(m−Δ)`. Premise-form: the decay is a HYPOTHESIS; the
chain from latent-error contraction to slack decay is documented,
not claimed here. -/
theorem alternating_round_slack_summable {Δ : ℕ} {m : ℝ}
    (hm : 0 < m) (hΔm : (Δ : ℝ) < m)
    (slack : ℕ → ℝ) (hs0 : 0 ≤ slack 0)
    (hslack : ∀ t, slack (t + 1) ≤ ((Δ : ℝ) / m) * slack t)
    (N : ℕ) :
    ∑ t ∈ Finset.range N, slack t ≤ slack 0 * m / (m - Δ) := by
  set q : ℝ := (Δ : ℝ) / m with hq
  have hq0 : 0 ≤ q := by rw [hq]; exact div_nonneg (Nat.cast_nonneg _) hm.le
  have hq1 : q < 1 := by
    rw [hq]
    exact (div_lt_one hm).2 hΔm
  have hbound := slack_partial_sum hq0 hq1 slack hs0 hslack N
  have hqN : 0 ≤ q ^ N := pow_nonneg hq0 N
  have hp : (0:ℝ) < 1 - q := by linarith
  have hinner : slack 0 * (1 - q ^ N) ≤ slack 0 * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) hs0
  have hle1 : slack 0 * (1 - q ^ N) / (1 - q)
      ≤ slack 0 * 1 / (1 - q) :=
    (div_le_div_iff₀ hp hp).2 (mul_le_mul_of_nonneg_right hinner hp.le)
  have hfinal : slack 0 * 1 / (1 - q) = slack 0 * m / (m - Δ) := by
    rw [hq]
    field_simp
  linarith [hbound, hle1, hfinal.ge]

end SlackSummable

/-! ## N2: trajectory telescoping and the descent budget -/
section Trajectory

variable {γ : Type*}

/-- **`alternating_trajectory_bound`** — (B4 N2, C294, TRAJECTORY
TELESCOPING) a trajectory of rounds `y 0, y 1, …` each satisfying
the strict-drop premise with per-round drop `d t` (premise-form)
telescopes: the final visible energy is at most the initial minus
the total drop. -/
theorem alternating_trajectory_bound {E : γ → ℝ} (y : ℕ → γ)
    (d : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ t < N, E (y (t + 1)) ≤ E (y t) - d t) :
    E (y N) ≤ E (y 0) - ∑ t ∈ Finset.range N, d t := by
  have hkey : ∀ (n : ℕ), (∀ t < n, E (y (t + 1)) ≤ E (y t) - d t) →
      E (y n) ≤ E (y 0) - ∑ t ∈ Finset.range n, d t := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : ∀ t < k, E (y (t + 1)) ≤ E (y t) - d t :=
        fun t ht => hk t (by omega)
      have hstep' := hk k (by omega)
      have hrec := ih hk'
      rw [Finset.sum_range_succ]
      have : E (y 0) - (∑ t ∈ Finset.range k, d t + d k)
          = E (y 0) - ∑ t ∈ Finset.range k, d t - d k := by ring
      rw [this]
      linarith
  exact hkey N hstep

/-- **`alternating_trajectory_descent_budget`** — (B4 N2, C294,
floor corollary) with the visible energy BOUNDED BELOW by `Emin`
(the honest floor premise — nonneg or bounded-below by
construction; a HYPOTHESIS, not a conclusion), the total descent
of a strictly-dropping trajectory is bounded: Σ drops ≤
`E (y 0) − Emin`. Combined with `alternating_round_slack_
summable`: a per-round drop `d t = c − slack t` with geometric
slack gives the cumulative descent budget `c·N − slack 0·m/(m−Δ)
≤ E (y 0) − Emin`, bounding the achievable number of guarded
rounds (remark, not a theorem — packaging the per-round premises
as a chain is the recorded next statement). -/
theorem alternating_trajectory_descent_budget {E : γ → ℝ} (y : ℕ → γ)
    (d : ℕ → ℝ) (N : ℕ) (Emin : ℝ)
    (hfloor : ∀ t, Emin ≤ E (y t))
    (hstep : ∀ t < N, E (y (t + 1)) ≤ E (y t) - d t) :
    ∑ t ∈ Finset.range N, d t ≤ E (y 0) - Emin := by
  have hb := alternating_trajectory_bound (E := E) y d N hstep
  have hf := hfloor N
  linarith

end Trajectory

/-! ## N3: terminal statement, finite form -/
section TerminalFinite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- **`alternating_rounds_converge`** — (B4 N3, C294, TERMINAL
FINITE FORM) on a finite configuration space, a trajectory of
alternating rounds along which the visible energy at the TRUE
frozen-z* kernel `pairwiseEnergy B (attentionK κ w f)` strictly
decreases at every pair has length at most the number of DISTINCT
energy values — the C268 ranking bound reused
(`greedy_strict_search_terminates` cited, not restated). Hence an
infinite strictly-improving alternating run CANNOT exist: the
process reaches a round where the composed guard fails (a STALL —
the honest terminal outcome; NOT a global-minimum claim).
Relation to the pinned negative: the UNCONDITIONAL analytic
convergence statement alternating_round_converges does NOT
exist and stays OPEN; this finite/strict version claims
TERMINATION only. -/
theorem alternating_rounds_converge (B : ι → α → ℝ) (κ : ι → ι → ℝ)
    (w : ι → ι → ℝ) (f : α → α → ℝ) (l : List (ι → α))
    (h : l.Pairwise (fun a b =>
      pairwiseEnergy B (attentionK κ w f) b
        < pairwiseEnergy B (attentionK κ w f) a)) :
    l.length ≤ Fintype.card (Set.image
      (pairwiseEnergy B (attentionK κ w f))
      (Set.univ : Set (ι → α))) :=
  greedy_strict_search_terminates _ l h

end TerminalFinite

/-! ## Numeric anchors (C294) -/
section Anchors

/-- ANCHOR (geometric slack sum numeric check): slack t = (1/2)^t
(q = Δ/m = 1/2, Δ = 1, m = 2): the budget is slack 0 * m/(m−Δ) = 2,
and the partial sum Σ_{t<5} (1/2)^t = 31/16 ≤ 2 through the
theorem itself. -/
example : ∑ t ∈ Finset.range 5, (1 / 2 : ℝ) ^ t ≤ 2 := by
  have h := alternating_round_slack_summable (Δ := 1) (m := 2)
    (by norm_num) (by norm_num) (fun t => (1 / 2 : ℝ) ^ t) (by norm_num)
    (fun t => by simp [pow_succ, mul_comm]) 5
  simp at h
  linarith

/-- ANCHOR (trajectory telescoping numeric check): E = 10 − t,
d = 1, N = 3: final 7 ≤ 10 − 3 through the theorem itself. -/
example : (fun t => (10 : ℝ) - t) 3
    ≤ (fun t => (10 : ℝ) - t) 0 - ∑ _t ∈ Finset.range 3, (1 : ℝ) := by
  have h := alternating_trajectory_bound (E := fun t => (10 : ℝ) - t)
    (fun t => t) (fun _ => 1) 3
    (by intro _t _; simp only [Nat.cast_succ]; linarith)
  show (10:ℝ) - 3 ≤ 10 - 0 - ∑ _t ∈ Finset.range 3, (1:ℝ)
  exact_mod_cast h

end Anchors

/-! ## Fixtures and witnesses -/
section Fixture

/-- **`fan2`** — agreement value-coupling on `Bool`
(`f a b = −1` iff `a = b`). -/
noncomputable def fan2 : Bool → Bool → ℝ := fun a b => if a = b then -1 else 0

/-- **`yan2`** — disagreeing fixture on `Fin 2` (cell 0 ≠ cell 1). -/
noncomputable def yan2 : Fin 2 → Bool := ![true, false]

/-- Numeric anchor (Fin 2 / Bool, APPLIED through the round theorem):
with constant weights (`w1 = w2`, so the latent slack `Lsm·η = 0`),
exact fields (ε = 0) and the agreement kernel, moving cell 0 of
`![true, false]` to `false` AGREES with cell 1 and STRICTLY drops
the energy `0 → −2` — the round theorem fires on a concrete
instance, not just a norm_num identity. -/
example : pairwiseEnergy (fun _ _ => (0:ℝ))
    (attentionK (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) fan2)
    (Function.update yan2 0 false)
    < pairwiseEnergy (fun _ _ => (0:ℝ))
    (attentionK (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) fan2) yan2 := by
  refine alternating_round_nonincreasing (κmax := 1) (fmax := 1)
    (Lsm := 0) (η := 0) (ε := 0)
    (fun _ _ => (0:ℝ))
    (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) fan2
    (fun i j => ⟨by norm_num, le_refl _⟩)
    (fun a b => by unfold fan2; split <;> simp) (by norm_num)
    (fun i j => by simp) yan2 0 false
    (fun _ b => localField (fun _ _ => (0:ℝ))
      (attentionK (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) fan2) yan2 0 b)
    (fun b => by
      unfold localField attentionK attentionCoupling fan2 yan2
      simp)
    (by
      unfold localField attentionK attentionCoupling fan2 yan2
      simp)

end Fixture

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Pseudolikelihood as free-cell local-field cross-entropy with β

Track E1 (addendum A11 bridge B2, CRAM / arXiv:2611.17309): the
pseudolikelihood of a categorical pairwise energy reduces EXACTLY
to cross-entropy on the LOCAL FIELD — the off-`i` energy is
independent of the candidate value and cancels as a constant
(C261's delta machinery viewed as a constant), for every
inverse temperature β, over the FREE cells of a CRAM problem.

* `CRAMProblem` — the concrete constraint carrier: per-cell
  allowed sets, optional givens (givens live inside the allowed
  sets), nonempty allowed sets; `CRAMProblem.freeCells` is the
  free-cell mask `{i : given i = none}`.
* `symmetrizeCoupling` / `symmetric_parameterization_preserves_hK`
  — the constructive symmetrizer `(Kt + Ktᵀ)/2` satisfies the
  symmetric-K premise of the main identities by construction.
* `conditionalLogit_eq_neg_localField_add_const` — (B2 MAIN)
  under symmetric `K`, `−H(y^{i←a}) = −L_i(a) + C_i(y)` with
  `C_i(y) = L_i(y_i) − H(y)` a constant in `a` — the C261
  single-cell delta identity (reused verbatim) read as a
  constant offset.
* `conditionalDist_eq_localField_softmax` — the local Gibbs
  conditional satisfies `softDef(−β·H(y^{i←a})) =
  softDef(−β·L_i)` for EVERY β: the constant `β·C_i(y)` cancels
  in softmax (shift-invariance — NOT in the Prelude, added here
  as minimal private lemmas; audit note in the C266 plan).
* `localFieldLogit` — the −β-scaled local-field logit vector
  `z_i(a) = −β·L_i(a)` (the local training logits).
* `freeCellPseudolikelihood` — the free-cell PL objective
  (mean over free cells of the CE of the −β-scaled energy
  logits).
* `pseudolikelihood_eq_local_CE_beta` — the free-cell
  pseudolikelihood equals the mean over free cells of
  `ceOneHot (y i) (−β·L_i)` — constants cancel in CE too.
* `pseudolikelihood_local_field_gradient` — premise-form
  gradient: for any differentiable local-field family
  (premise HasFDerivAt Lmap Lmap' θ), the derivative of the local
  CE is Σ_v (q_v − 1[v = t]) · (−β · Lmap' h v) — the EXISTING
  `Hagi.Model.CEGradient.fderiv_ceOneHot_comp_apply`
  instantiated at the scaled local-field logit map.
* `pseudolikelihood_freeCell_B_gradient` — chain-rule
  corollary: `B` enters `L_i` affinely (derivative `proj i`),
  so the free-cell PL gradient at `B` in direction `h` is
  `(1/|F|) Σ_{i∈F} Σ_a (q_i(a) − 1[a = y_i]) · (−β · h i a)`.

## Honest boundaries

* The K-gradient is NOT claimed: `K` enters `L_i` through the
  neighbor literals `y_j`; its derivative is a rank-one
  operator per parameter — deferred (premise-form only).
* No descent/convergence claim: these are exact identities and
  a gradient FORMULA, not a training certificate.
* The free-cell identities are premise-free algebra (valid for
  any `y`, any `β`, even an empty free-cell set); `hK`
  (symmetric `K`) is a real premise of the cancellation, not
  decoration.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (pairwiseEnergy localField)
open Hagi.Core (ceOneHot lse)
open Hagi.Prelude (softDef)

section Carrier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The concrete CRAM constraint carrier: per-cell allowed value
sets, optional givens with `hgiven` (every given lives inside its
allowed set) and `hnonempty` (every allowed set nonempty). The
free cells of the problem are those WITHOUT a given — the cells
pseudolikelihood trains on. -/
structure CRAMProblem (ι : Type*) [Fintype ι] [DecidableEq ι]
    (α : Type*) [Fintype α] [DecidableEq α] where
  /-- Per-cell allowed values (the constraint sets). -/
  allowed : ι → Finset α
  /-- Optional per-cell givens (puzzle clues). -/
  givens : ι → Option α
  /-- Every given is admissible: `given i = some a → a ∈ allowed i`. -/
  hgiven : ∀ i a, givens i = some a → a ∈ allowed i
  /-- Every allowed set is nonempty (each cell has a candidate). -/
  hnonempty : ∀ i, (allowed i).Nonempty

/-- The free-cell mask `{i : P.given i = none}` — cells without
a given; the pseudolikelihood objective averages over exactly
these cells. -/
def CRAMProblem.freeCells (P : CRAMProblem ι α) : Finset ι :=
  Finset.univ.filter (fun i => P.givens i = none)

end Carrier

section Symmetrizer

variable {ι : Type*} {α : Type*}

/-- The constructive symmetrizer `(Kt + Ktᵀ)/2`:
`symmetrizeCoupling K̃ i j a b = (Kt i j a b + Kt j i b a) / 2` —
upper-triangle storage lifted to a symmetric coupling. -/
noncomputable def symmetrizeCoupling (Kt : ι → ι → α → α → ℝ) :
    ι → ι → α → α → ℝ :=
  fun i j a b => (Kt i j a b + Kt j i b a) / 2

/-- The constructive symmetrizer satisfies the symmetric-K
premise `hK` of the local-field identities BY CONSTRUCTION
(cheap isSymm lemma: exchange `i↔j`, `a↔b` and use ring). -/
theorem symmetric_parameterization_preserves_hK (Kt : ι → ι → α → α → ℝ)
    (i j : ι) (a b : α) :
    symmetrizeCoupling Kt i j a b = symmetrizeCoupling Kt j i b a := by
  unfold symmetrizeCoupling
  ring

end Symmetrizer

section Shift

/-! ## Minimal shift-invariance lemmas (private)

Audit note (C266 plan, challenge 1): NO softmax/CE const-shift
lemma exists in the Prelude (`InfoCore`), `Core.Concat`, or
`Numerics.SoftmaxFix` — only `softDef_pos`, `softDef_sum_one`,
`softDef_eq_exp_sub_lse`, `temperature_*`. These two minimal
companions are PRIVATE to this file to keep the addition
additive (no existing module touched). -/

variable {k : Type*} [Fintype k]

/-- Softmax is invariant under adding a constant to all logits:
`softDef (z + const c) = softDef z` (the `e^c` factor cancels
between numerator and normalizer). -/
private theorem softDef_add_const [Nonempty k] (z : k → ℝ) (c : ℝ) :
    (fun a => softDef (fun a => z a + c) a) = softDef z := by
  have hsum : ∑ b, Real.exp (z b + c) = Real.exp c * ∑ b, Real.exp (z b) := by
    rw [Finset.sum_congr rfl (fun b _ => Real.exp_add (z b) c), Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hpos : 0 < ∑ b, Real.exp (z b) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  funext a
  unfold softDef
  rw [hsum, Real.exp_add]
  field_simp

/-- One-hot cross-entropy is invariant under adding a constant to
all logits: `ceOneHot t (z + const c) = ceOneHot t z` (the lse
normalizer shifts by exactly `c`, cancelling the target shift). -/
private theorem ceOneHot_add_const [Nonempty k] (t : k) (z : k → ℝ) (c : ℝ) :
    ceOneHot t (fun a => z a + c) = ceOneHot t z := by
  have hsum : ∑ b, Real.exp (z b + c) = Real.exp c * ∑ b, Real.exp (z b) := by
    rw [Finset.sum_congr rfl (fun b _ => Real.exp_add (z b) c), Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hpos : 0 < ∑ b, Real.exp (z b) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hlse : lse (fun a => z a + c) = c + lse z := by
    unfold lse
    rw [hsum, Real.log_mul (Real.exp_pos _).ne' (ne_of_gt hpos), Real.log_exp]
  unfold ceOneHot
  rw [hlse]
  ring

end Shift

section LocalFieldBridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- (B2 MAIN) Under symmetric `K`, the local conditional logit
splits as `−H(y^{i←a}) = −L_i(a) + C_i(y)` with the constant
`C_i(y) = L_i(y_i) − H(y)` INDEPENDENT of `a`: the off-`i`
energy is a constant of the candidate value — this is C261's
single-cell delta identity (`single_cell_move_energy_delta_symm`,
reused verbatim) read as a constant offset. -/
theorem conditionalLogit_eq_neg_localField_add_const
    (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (hK : ∀ i j a b, K i j a b = K j i b a)
    (y : ι → α) (i : ι) (a : α) :
    conditionalLogit B K y i a
      = -localField B K y i a
        + (localField B K y i (y i) - pairwiseEnergy B K y) := by
  have hd := Hagi.Energy.single_cell_move_energy_delta_symm B K hK y i a
  unfold conditionalLogit
  linarith

omit [DecidableEq α] in
/-- The local Gibbs conditional on the −β-scaled energy logits
equals the softmax of the −β-scaled LOCAL FIELD, for EVERY β
(no sign or positivity premise on β: the constant `β·C_i(y)`
cancels in softmax unconditionally). -/
theorem conditionalDist_eq_localField_softmax [Nonempty α]
    (β : ℝ) (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (hK : ∀ i j a b, K i j a b = K j i b a)
    (y : ι → α) (i : ι) :
    (fun a => softDef (fun a => -β * pairwiseEnergy B K (Function.update y i a)) a)
      = softDef (fun a => -β * localField B K y i a) := by
  have key : (fun a => -β * pairwiseEnergy B K (Function.update y i a))
      = fun a => -β * localField B K y i a
        + β * (localField B K y i (y i) - pairwiseEnergy B K y) := by
    funext a
    have h := conditionalLogit_eq_neg_localField_add_const B K hK y i a
    unfold conditionalLogit at h
    have hPE : pairwiseEnergy B K (Function.update y i a)
        = pairwiseEnergy B K y + localField B K y i a
          - localField B K y i (y i) := by linarith
    rw [hPE]
    ring
  conv_lhs => rw [key]
  exact softDef_add_const _ _

end LocalFieldBridge

section FreeCells

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The −β-scaled local-field logit vector of cell `i`
(`z_i(a) = −β·L_i(a)` — the local training logits after the
cancellation of the off-`i` constant). -/
noncomputable def localFieldLogit (β : ℝ) (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (y : ι → α) (i : ι) : α → ℝ :=
  fun a => -β * localField B K y i a

/-- Free-cell pseudolikelihood objective (energy form):
`J = (1/|F|) Σ_{i∈F} ceOneHot (y i) (a ↦ −β·H(y^{i←a}))` over
the free cells `F = P.freeCells` — the mean local cross-entropy
against the −β-scaled Gibbs conditionals, restricted to the
cells without givens. -/
noncomputable def freeCellPseudolikelihood (β : ℝ) (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (P : CRAMProblem ι α) (y : ι → α) : ℝ :=
  (∑ i ∈ P.freeCells,
      ceOneHot (y i) (fun a => -β * pairwiseEnergy B K (Function.update y i a)))
    / (P.freeCells.card : ℝ)

/-- (B2) The free-cell pseudolikelihood equals the mean over
FREE cells of the local cross-entropy on the LOCAL-FIELD logits
`−β·L_i`: the per-cell constant `β·C_i(y)` cancels in
`ceOneHot` exactly as it cancels in softmax. Premise-free in
`y` and in the free-cell set (an empty `F` gives the same
`0/0`-mean on both sides) — `hK` is the real cancellation
premise. -/
theorem pseudolikelihood_eq_local_CE_beta [Nonempty α]
    (β : ℝ) (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (hK : ∀ i j a b, K i j a b = K j i b a)
    (P : CRAMProblem ι α) (y : ι → α) :
    freeCellPseudolikelihood β B K P y
      = (∑ i ∈ P.freeCells, ceOneHot (y i) (localFieldLogit β B K y i))
        / (P.freeCells.card : ℝ) := by
  have hterm : ∀ (i : ι),
      (fun a => -β * pairwiseEnergy B K (Function.update y i a) : α → ℝ)
        = fun a => -β * localField B K y i a
          + β * (localField B K y i (y i) - pairwiseEnergy B K y) := by
    intro i
    funext a
    have h := conditionalLogit_eq_neg_localField_add_const B K hK y i a
    unfold conditionalLogit at h
    have hPE : pairwiseEnergy B K (Function.update y i a)
        = pairwiseEnergy B K y + localField B K y i a
          - localField B K y i (y i) := by linarith
    rw [hPE]
    ring
  unfold freeCellPseudolikelihood
  refine congrArg (· / (P.freeCells.card : ℝ)) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hterm i]
  exact ceOneHot_add_const (y i) (fun a => -β * localField B K y i a) _

end FreeCells

section Gradient

variable {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- (B2, premise-form) The local CE gradient on a differentiable
local-field family: if `θ ↦ Lmap θ` has derivative Lmap' at
`θ`, then the derivative of `a ↦ ceOneHot t (−β · Lmap θ a)` at
`θ` in direction `h` is
Σ_v (q_v − 1[v = t]) · (−β · Lmap' h v) with
`q = softDef (−β · Lmap θ)` — the EXISTING
`Hagi.Model.CEGradient.fderiv_ceOneHot_comp_apply`
instantiated at the scaled local-field logit map (no new CE
calculus; the differentiability of `Lmap` is an honest
premise). -/
theorem pseudolikelihood_local_field_gradient (β : ℝ)
    (Lmap : E → (V → ℝ)) (Lmap' : E →L[ℝ] (V → ℝ)) (θ h : E) (t : V)
    (hg : HasFDerivAt Lmap Lmap' θ) :
    fderiv ℝ (fun w => ceOneHot t (fun a => -β * Lmap w a)) θ h
      = ∑ v, (softDef (fun a => -β * Lmap θ a) v
          - if v = t then 1 else 0) * (-β * Lmap' h v) :=
  Hagi.Model.CEGradient.fderiv_ceOneHot_comp_apply
    ((-β : ℝ) • Lmap) ((-β : ℝ) • Lmap') θ h t (hg.const_smul (-β))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

omit [Nonempty ι] in
/-- (B2 chain rule) The `B`-gradient of the free-cell
pseudolikelihood: `B` enters the local field AFFINELY
(derivative `proj i`), so the derivative of the objective at
`B` in direction `h` is
`(1/|F|) Σ_{i∈F} Σ_a (q_i(a) − 1[a = y_i]) · (−β · h i a)` with
`q_i = softDef (−β · L_i)` — the residual form of
`pseudolikelihood_local_field_gradient` summed over the free
cells. The value carrier is fixed at `α : Type` because the
CEGradient spine is `Type`-level (universe-0); the K-gradient
is NOT claimed (see module honest boundaries). -/
theorem pseudolikelihood_freeCell_B_gradient {α : Type} [Fintype α]
    [DecidableEq α] [Nonempty α] (β : ℝ) (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ)
    (hK : ∀ i j a b, K i j a b = K j i b a)
    (P : CRAMProblem ι α) (y : ι → α)
    (h : ι → α → ℝ) :
    fderiv ℝ (fun B' => freeCellPseudolikelihood β B' K P y) B h
      = (∑ i ∈ P.freeCells, ∑ a,
          (softDef (localFieldLogit β B K y i) a
            - if a = y i then 1 else 0) * (-β * h i a))
        / (P.freeCells.card : ℝ) := by
  -- reduce to the local-field form (constants cancel, termwise)
  have hfun : (fun B' => freeCellPseudolikelihood β B' K P y)
      = fun B' => (∑ i ∈ P.freeCells,
          ceOneHot (y i) (localFieldLogit β B' K y i))
          / (P.freeCells.card : ℝ) :=
    funext fun B' => pseudolikelihood_eq_local_CE_beta β B' K hK P y
  rw [hfun]
  -- the local-field map of cell i is affine in B: deriv = proj i
  have hL : ∀ i : ι,
      HasFDerivAt (fun B' : ι → α → ℝ => localField B' K y i)
        (ContinuousLinearMap.proj i :
          (ι → α → ℝ) →L[ℝ] (α → ℝ)) B := by
    intro i
    have h1 : HasFDerivAt (fun B' : ι → α → ℝ => (fun a => B' i a : α → ℝ))
        (ContinuousLinearMap.proj i :
          (ι → α → ℝ) →L[ℝ] (α → ℝ)) B :=
      ContinuousLinearMap.hasFDerivAt
        (ContinuousLinearMap.proj i :
          (ι → α → ℝ) →L[ℝ] (α → ℝ))
    have h2 : HasFDerivAt
        (fun _ : ι → α → ℝ =>
          (fun a => ∑ j ∈ Finset.univ \ {i}, K i j a (y j) : α → ℝ))
        (0 : (ι → α → ℝ) →L[ℝ] (α → ℝ)) B :=
      hasFDerivAt_const _ B
    have h3 := h1.add h2
    rw [add_zero] at h3
    convert h3 using 1
    rfl
  -- per-cell derivative applied to a direction (residual · proj pairs)
  have hLcell : ∀ (i : ι) (u : ι → α → ℝ),
      (∑ a, (softDef (localFieldLogit β B K y i) a
            - if a = y i then 1 else 0)
          • (-β • ((ContinuousLinearMap.proj a :
                (α → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.proj i :
                (ι → α → ℝ) →L[ℝ] (α → ℝ))))
        : (ι → α → ℝ) →L[ℝ] ℝ) u
      = ∑ a, (softDef (localFieldLogit β B K y i) a
          - if a = y i then 1 else 0) * (-β * u i a) := by
    intro i u
    simp only [sum_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul]
  have hcell : ∀ i ∈ P.freeCells,
      HasFDerivAt (fun B' : ι → α → ℝ =>
          ceOneHot (y i) (localFieldLogit β B' K y i))
        (∑ a, (softDef (localFieldLogit β B K y i) a
            - if a = y i then 1 else 0)
          • (-β • ((ContinuousLinearMap.proj a :
                (α → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.proj i :
                (ι → α → ℝ) →L[ℝ] (α → ℝ))))) B := by
    intro i _
    have hg' : HasFDerivAt
        ((-β : ℝ) • (fun B' : ι → α → ℝ => localField B' K y i))
        ((-β : ℝ) • (ContinuousLinearMap.proj i :
          (ι → α → ℝ) →L[ℝ] (α → ℝ))) B :=
      (hL i).const_smul (-β)
    have hdiff : DifferentiableAt ℝ
        (fun B' : ι → α → ℝ => ceOneHot (y i) (localFieldLogit β B' K y i)) B :=
      Hagi.Model.CEGradient.differentiableAt_ceOneHot_comp
        ((-β : ℝ) • (fun B' : ι → α → ℝ => localField B' K y i)) B (y i)
        hg'.differentiableAt
    refine hdiff.hasFDerivAt.congr_fderiv
      (ContinuousLinearMap.ext fun u => ?_)
    have hval := pseudolikelihood_local_field_gradient β
      (fun B' : ι → α → ℝ => localField B' K y i)
      (ContinuousLinearMap.proj i :
        (ι → α → ℝ) →L[ℝ] (α → ℝ)) B u (y i) (hL i)
    change (fderiv ℝ (fun B' : ι → α → ℝ =>
      ceOneHot (y i) (fun a => -β * localField B' K y i a)) B) u = _
    rw [hval, hLcell i]
    rfl
  -- sum over free cells, then scale by the constant cardinality
  have hsum : HasFDerivAt
      (fun B' => ∑ i ∈ P.freeCells,
        ceOneHot (y i) (localFieldLogit β B' K y i))
      (∑ i ∈ P.freeCells,
        ∑ a, (softDef (localFieldLogit β B K y i) a
            - if a = y i then 1 else 0)
          • (-β • ((ContinuousLinearMap.proj a :
                (α → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.proj i :
                (ι → α → ℝ) →L[ℝ] (α → ℝ))))) B := by
    convert HasFDerivAt.sum hcell using 1
    funext B'
    simp
  have hEq3 :
      (fun B' => (∑ i ∈ P.freeCells,
          ceOneHot (y i) (localFieldLogit β B' K y i))
          / ((P.freeCells.card : ℝ)))
      = fun B' => (∑ i ∈ P.freeCells,
          ceOneHot (y i) (localFieldLogit β B' K y i))
          * ((P.freeCells.card : ℝ)⁻¹) := by
    funext B'
    field_simp
  have hdiv := hsum.mul_const ((P.freeCells.card : ℝ)⁻¹)
  rw [hEq3, hdiv.fderiv]
  simp only [smul_apply, smul_eq_mul, sum_apply, hLcell,
    div_eq_inv_mul, mul_comm]

end Gradient

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Typed CRAM transition contracts with Cert-kernel bridge

Track E-bridge B3 (addendum A11 bridge B3): CRAM transitions
become TYPED premise-form contracts over a `CRAMState` carrier
with exact resource laws (budget' = budget − cost, nonnegative
remainder), bridged into the canonical certification kernel
`Hagi.Cert` so the certified telescope applies.

* `MetricDirection` — the typed metric polarity: `UtilityFloor`
  (higher is better; obligations are lower floors) vs
  `LossCeiling` (lower is better — energy/loss descent;
  obligations are upper ceilings).  `MetricDirection.kept` and
  `MetricDirection.improves` are the direction-indexed
  obligation/improvement predicates; the negation bridge
  `MetricDirection.kept_lossCeiling_neg` is THE polarity fix for
  the kernel's floor-form `FloorsKept`: a loss is read by
  negating the objective, typed and explicit instead of confused.
* `CRAMState` — the transition carrier: problem, board, optional
  latent, budgets (search with natural numbers, compute real),
  remaining risk and delta, with componentwise extensionality.
* `CRAMTrainStep` — parameter-training contract on the free-cell
  pseudolikelihood objective: MEASURED-drop premise (no gradient
  proof, no convergence claim) plus exact budget laws;
  `CRAMTrainStep.measured_of_majorizer` is the majorizer entry
  (surrogate anchored at the old parameters).
* `CRAMEnergyDescentStep` — single-cell energy descent from the
  C261 strict-drop margin, with MarginBudget accounting (the
  certified margin is deducted from the risk remainder);
  `strictDrop` reuses `strict_drop_of_positive_margin` verbatim;
  `toLossCeilingDrop` wires the LossCeiling polarity.
* `CRAMExplorationStep` — legal exploration transition: positive
  kernel mass, row-stochastic kernel premise (the C263
  `mixture_rowsum` premise shape), clamps (givens) preserved,
  search budget consumed.  NO DESCENT CLAIM: exploration may
  RAISE the energy (stationarity is not monotonicity).
* `CRAMAcceptedSolution` — production certificate: a
  `ValidityCertificate` (givens preserved + constraints
  satisfied, C263 `EnergyStopping`) agreeing with the board,
  with an OPTIONAL energy bound.
* `CRAMEnergyDescentStep.toKernelCertStep` — the canonical-kernel
  bridge (pattern: `HonestTransition.toKernelCertStep`, C254):
  under explicit metric-readout premises the descent step is a
  `Hagi.Cert.CertStep`, so the kernel telescope applies.
* `HoldStep.cram_state_components` — a kernel hold on the CRAM
  carrier fixes the FULL state (problem, board, latent, budgets,
  risk, delta): Hold = full state equality, documented.

## Honest boundaries

* Train step: the measured drop and the majorizer properties are
  PREMISES; the gradient formula exists
  (`pseudolikelihood_freeCell_B_gradient`) but no descent is
  proven from it here.
* Exploration makes NO descent claim and carries no energy field.
* Accepted solution: validity says nothing about energy (E4
  separation) — the energy bound is optional data.
* The kernel adapter's metric readouts are explicit premises; no
  ambient `SystemMetrics` is postulated for `CRAMState`.
* `MetricDirection.kept_floor_iff` (the reverse direction) needs
  `[Nonempty TaskId]`: with an empty task space the kernel's
  `FloorsKept` is vacuous — the premise is load-bearing, not
  decoration.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (pairwiseEnergy localField)

/-! ## Typed metric polarity -/

/-- The typed metric polarity.  `UtilityFloor`: higher objective
is better, obligations are LOWER floors (`floor ≤ objective`).
`LossCeiling`: lower objective is better — energy/loss descent —
obligations are UPPER ceilings (`objective ≤ ceiling`). -/
inductive MetricDirection where
  /-- Utility polarity: obligations are floors. -/
  | UtilityFloor
  /-- Loss/energy polarity: obligations are ceilings. -/
  | LossCeiling

/-- Direction-indexed kept-obligation predicate: at level `lvl`,
the state `s` keeps its obligation w.r.t. the readout `obj`. -/
def MetricDirection.kept {S : Type*} (dir : MetricDirection)
    (obj : S → ℝ) (lvl : ℝ) (s : S) : Prop :=
  match dir with
  | UtilityFloor => lvl ≤ obj s
  | LossCeiling => obj s ≤ lvl

/-- Direction-indexed improvement: the readout improves from `s`
to `s'` by at least `δ` in the direction's polarity. -/
def MetricDirection.improves {S : Type*} (dir : MetricDirection)
    (obj : S → ℝ) (s s' : S) (δ : ℝ) : Prop :=
  match dir with
  | UtilityFloor => obj s + δ ≤ obj s'
  | LossCeiling => obj s' ≤ obj s - δ

/-- Forward bridge to the kernel floor contract: a kept
UtilityFloor obligation implies the kernel's `FloorsKept` at the
constant floor `lvl` (always, without any premise on the task
space). -/
theorem MetricDirection.kept_floor_forwards {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId) (lvl : ℝ) (s : S)
    (h : MetricDirection.kept MetricDirection.UtilityFloor
        M.objective lvl s) :
    Hagi.Cert.FloorsKept M { floor := fun _ => lvl } s :=
  fun _ => h

/-- Reverse bridge: the kernel's `FloorsKept` at a constant floor
implies the kept UtilityFloor obligation, PROVIDED a task tag
exists — with an empty task space `FloorsKept` is vacuous, so the
`[Nonempty TaskId]` premise is honest and load-bearing. -/
theorem MetricDirection.kept_floor_iff {S TaskId : Type*}
    [Nonempty TaskId] (M : Hagi.Cert.SystemMetrics S TaskId)
    (lvl : ℝ) (s : S)
    (h : Hagi.Cert.FloorsKept M { floor := fun _ => lvl } s) :
    MetricDirection.kept MetricDirection.UtilityFloor M.objective
        lvl s :=
  h (Classical.arbitrary TaskId)

/-- THE polarity fix, typed: a LossCeiling obligation at ceiling
`c` is exactly a UtilityFloor obligation at floor `−c` for the
NEGATED objective — the canonical kernel's floor-form
`FloorsKept` reads losses by negation, and this Iff makes the
translation explicit instead of confused. -/
theorem MetricDirection.kept_lossCeiling_neg {S : Type*}
    (obj : S → ℝ) (c : ℝ) (s : S) :
    MetricDirection.kept MetricDirection.LossCeiling obj c s
      ↔ MetricDirection.kept MetricDirection.UtilityFloor
          (fun t => -obj t) (-c) s := by
  simp only [MetricDirection.kept]
  exact ⟨fun h => by linarith, fun h => by linarith⟩

/-- Drop-form descent is a typed LossCeiling improvement. -/
theorem MetricDirection.improves_lossCeiling_intro {S : Type*}
    (obj : S → ℝ) (s s' : S) (δ : ℝ)
    (h : obj s' ≤ obj s - δ) :
    MetricDirection.improves MetricDirection.LossCeiling obj s s'
        δ := h

/-! ## CRAM state carrier -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The CRAM transition-state carrier: the problem, the current
board, an optional latent configuration, the search budget
(natural — one exploration step costs units), the compute budget
(real), the remaining risk-margin budget and the remaining delta
(false-commit probability) budget. -/
structure CRAMState (ι : Type*) [Fintype ι] [DecidableEq ι]
    (α : Type*) [Fintype α] [DecidableEq α] where
  /-- The CRAM problem (constraint carrier, C266). -/
  problem : CRAMProblem ι α
  /-- The current board configuration. -/
  board : ι → α
  /-- An optional latent configuration (two-phase protocol). -/
  latent : Option (ι → α)
  /-- Search-step budget (consumed by exploration). -/
  searchBudget : ℕ
  /-- Compute budget (consumed by training and descent). -/
  computeBudget : ℝ
  /-- Remaining risk-margin budget (consumed by descent margins). -/
  riskRem : ℝ
  /-- Remaining delta (false-commit) budget. -/
  deltaRem : ℝ

/-- Componentwise equality of CRAM states iff equality. -/
theorem CRAMState.ext_iff (s s' : CRAMState ι α) :
    s = s' ↔ s.problem = s'.problem ∧ s.board = s'.board
      ∧ s.latent = s'.latent ∧ s.searchBudget = s'.searchBudget
      ∧ s.computeBudget = s'.computeBudget ∧ s.riskRem = s'.riskRem
      ∧ s.deltaRem = s'.deltaRem := by
  constructor
  · intro h
    exact ⟨by rw [h], by rw [h], by rw [h], by rw [h], by rw [h],
      by rw [h], by rw [h]⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    cases s
    cases s'
    simp_all

/-! ## CRAMTrainStep: measured-drop / majorizer premise-form -/

/-- Parameter-training contract on the free-cell
pseudolikelihood objective (C266): a MEASURED drop premise — the
new parameters achieve at most the old objective minus the drop —
plus exact resource laws.  Premise-form: no gradient proof and no
convergence claim is made (the gradient FORMULA exists in
`pseudolikelihood_freeCell_B_gradient`; deriving a certified drop
from it is deliberately NOT attempted here). -/
structure CRAMTrainStep (β : ℝ) (K : ι → ι → α → α → ℝ)
    (P : CRAMProblem ι α) (y : ι → α)
    (oldB newB : ι → α → ℝ) (s s' : CRAMState ι α) where
  /-- Certified (measured) drop of the free-cell PL objective. -/
  drop : ℝ
  /-- The drop is nonnegative (a zero drop — a wasted step — is
  allowed; this contract does not claim progress). -/
  drop_nonneg : 0 ≤ drop
  /-- MEASURED drop premise: the new parameters achieve at most
  the old objective minus the drop. -/
  measured : freeCellPseudolikelihood β newB K P y
    ≤ freeCellPseudolikelihood β oldB K P y - drop
  /-- Training does not move the board. -/
  board_next : s'.board = s.board
  /-- Training does not change the problem. -/
  problem_next : s'.problem = s.problem
  /-- Training does not change the latent. -/
  latent_next : s'.latent = s.latent
  /-- Search budget spent by the training step. -/
  searchCost : ℕ
  /-- Exact search-budget law (additive form: no truncated natural
  subtraction). -/
  search_next : s'.searchBudget + searchCost = s.searchBudget
  /-- Compute budget spent by the training step. -/
  computeCost : ℝ
  /-- Exact compute-budget law. -/
  compute_next : s'.computeBudget = s.computeBudget - computeCost
  /-- Nonnegative compute remainder. -/
  compute_nonneg : 0 ≤ s'.computeBudget
  /-- Training consumes no risk margin. -/
  risk_next : s'.riskRem = s.riskRem
  /-- Training consumes no delta. -/
  delta_next : s'.deltaRem = s.deltaRem

/-- Majorizer entry into the measured-drop premise
(majorize-minimize, premise-form): if a surrogate is ANCHORED at
the old parameters (equal to the old objective there) and the new
objective beats the surrogate by `drop`, then the measured drop
holds.  The surrogate properties are premises, not derived. -/
theorem CRAMTrainStep.measured_of_majorizer (β : ℝ)
    (K : ι → ι → α → α → ℝ) (P : CRAMProblem ι α) (y : ι → α)
    (oldB newB : ι → α → ℝ) (maj : ℝ) (drop : ℝ)
    (hAnchor : freeCellPseudolikelihood β oldB K P y = maj)
    (hNew : freeCellPseudolikelihood β newB K P y ≤ maj - drop) :
    freeCellPseudolikelihood β newB K P y
      ≤ freeCellPseudolikelihood β oldB K P y - drop := by
  rw [hAnchor]
  exact hNew

/-! ## CRAMEnergyDescentStep: C261 strict drop + MarginBudget -/

/-- Single-cell energy-descent contract: a strictly positive
local-field margin (the C261 form) certifies a strict energy drop
`E(y^{i←a}) < E(y)`; the certified margin is DEDUCTED from the
risk remainder (MarginBudget accounting), the compute budget is
spent exactly, and the board moves by the single-cell update. -/
structure CRAMEnergyDescentStep (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (s s' : CRAMState ι α) where
  /-- Symmetric coupling premise (load-bearing for the C261
  strict-drop theorem; satisfied by the constructive symmetrizer
  `symmetrizeCoupling` of C266). -/
  hK : ∀ i j a b, K i j a b = K j i b a
  /-- The moved cell. -/
  cell : ι
  /-- The new value at the moved cell. -/
  move : α
  /-- The certified local-field margin. -/
  margin : ℝ
  /-- Strictly positive margin, C261 form:
  `L_i(y_i) − L_i(move) > 0`. -/
  margin_pos : 0 < localField B K s.board cell (s.board cell)
    - localField B K s.board cell move
  /-- The board moves by the single-cell update. -/
  board_next : s'.board = Function.update s.board cell move
  /-- The problem is unchanged. -/
  problem_next : s'.problem = s.problem
  /-- The latent is unchanged. -/
  latent_next : s'.latent = s.latent
  /-- Search budget spent by the descent step. -/
  searchCost : ℕ
  /-- Exact search-budget law. -/
  search_next : s'.searchBudget + searchCost = s.searchBudget
  /-- Compute budget spent by the descent step. -/
  computeCost : ℝ
  /-- Exact compute-budget law. -/
  compute_next : s'.computeBudget = s.computeBudget - computeCost
  /-- Nonnegative compute remainder. -/
  compute_nonneg : 0 ≤ s'.computeBudget
  /-- MarginBudget accounting: the certified margin is deducted
  from the risk remainder. -/
  risk_next : s'.riskRem = s.riskRem - margin
  /-- Nonnegative risk remainder. -/
  risk_nonneg : 0 ≤ s'.riskRem
  /-- Descent consumes no delta. -/
  delta_next : s'.deltaRem = s.deltaRem

/-- The C261 strict drop, verbatim: a positive local-field margin
gives `E(s'.board) < E(s.board)` — the existing
`strict_drop_of_positive_margin` applied at the board update. -/
theorem CRAMEnergyDescentStep.strictDrop (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) {s s' : CRAMState ι α}
    (h : CRAMEnergyDescentStep B K s s') :
    pairwiseEnergy B K s'.board < pairwiseEnergy B K s.board := by
  rw [h.board_next]
  exact Hagi.Energy.strict_drop_of_positive_margin B K h.hK
    s.board h.cell h.move h.margin_pos

/-- The strict drop packaged as a typed LossCeiling certificate:
the drop `E(s.board) − E(s'.board)` is positive, exact
(energy_next is an equality), and is a `MetricDirection.improves`
LossCeiling improvement — the polarity is wired by typing, not by
convention. -/
noncomputable def CRAMEnergyDescentStep.toLossCeilingDrop (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) {s s' : CRAMState ι α}
    (h : CRAMEnergyDescentStep B K s s') :
    { drop : ℝ // 0 < drop
        ∧ pairwiseEnergy B K s'.board
            = pairwiseEnergy B K s.board - drop
        ∧ MetricDirection.improves MetricDirection.LossCeiling
            (fun t : CRAMState ι α => pairwiseEnergy B K t.board)
            s s' drop } where
  val := pairwiseEnergy B K s.board - pairwiseEnergy B K s'.board
  property :=
    ⟨by linarith [h.strictDrop], by linarith,
      MetricDirection.improves_lossCeiling_intro _ _ _ _ (by linarith)⟩

/-- The canonical-kernel bridge (pattern:
`HonestTransition.toKernelCertStep`, C254): under EXPLICIT
metric-readout premises — the kernel metrics read the board
energy, the compute budget and the risk remainder — a
`CRAMEnergyDescentStep` IS a canonical `Hagi.Cert.CertStep`:
positive drop, real descent, exact budget/risk consumption laws
with nonnegative remainders, floors kept at the post-state.  The
kernel telescope therefore applies to certified CRAM descent
trajectories. -/
noncomputable def CRAMEnergyDescentStep.toKernelCertStep {TaskId : Type*}
    (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    {s s' : CRAMState ι α} (h : CRAMEnergyDescentStep B K s s')
    (M : Hagi.Cert.SystemMetrics (CRAMState ι α) TaskId)
    (hobj : M.objective = fun t => pairwiseEnergy B K t.board)
    (hbud : M.budget = fun t => t.computeBudget)
    (hrisk : M.risk = fun t => t.riskRem)
    (obl : Hagi.Cert.StepObligations TaskId)
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    Hagi.Cert.CertStep M obl s s' where
  drop := pairwiseEnergy B K s.board - pairwiseEnergy B K s'.board
  drop_pos := by linarith [h.strictDrop]
  descent := by
    simp only [hobj]
    linarith [h.strictDrop]
  budgetSpend := h.computeCost
  budget_next := by simp only [hbud]; exact h.compute_next
  budget_nonneg := by simp only [hbud]; exact h.compute_nonneg
  riskSpend := h.margin
  risk_next := by simp only [hrisk]; exact h.risk_next
  risk_nonneg := by simp only [hrisk]; exact h.risk_nonneg
  floorsKept := hfloors

/-! ## CRAMExplorationStep: legal move, NO descent claim -/

/-- Legal exploration transition: the new board has POSITIVE
kernel mass under a ROW-STOCHASTIC kernel (the C263
`mixture_rowsum` premise shape — the kernel is a premise, e.g.
the focused heat-bath mixture), every given (clamp) is preserved
exactly, and the search budget is CONSUMED (strictly positive
cost).

NO DESCENT CLAIM: this contract deliberately carries no energy
field and proves no decrease — exploration under a stationary
kernel may RAISE the energy (stationarity is not monotonicity;
see `focused_mixture_stationary`).  Descent is claimed ONLY by
`CRAMEnergyDescentStep`. -/
structure CRAMExplorationStep (s s' : CRAMState ι α) where
  /-- The transition kernel (premise-form data; e.g. a focused
  heat-bath mixture of C263). -/
  kernel : (ι → α) → (ι → α) → ℝ
  /-- Legality: the new board has positive transition mass. -/
  legality : 0 < kernel s.board s'.board
  /-- Row-stochasticity premise (C263 `mixture_rowsum` shape):
  every row of the kernel sums to one. -/
  rowStochastic : ∀ y, ∑ z, kernel y z = 1
  /-- Clamps preserved: every given value is intact. -/
  clampsPreserved : ∀ i a, s.problem.givens i = some a →
    s'.board i = a
  /-- The problem is unchanged. -/
  problem_next : s'.problem = s.problem
  /-- The latent is unchanged. -/
  latent_next : s'.latent = s.latent
  /-- Search budget spent by the exploration step. -/
  searchCost : ℕ
  /-- Exploration CONSUMES search budget (strictly). -/
  searchCost_pos : 0 < searchCost
  /-- Exact search-budget law. -/
  search_next : s'.searchBudget + searchCost = s.searchBudget
  /-- Compute budget spent by the exploration step. -/
  computeCost : ℝ
  /-- Exact compute-budget law. -/
  compute_next : s'.computeBudget = s.computeBudget - computeCost
  /-- Nonnegative compute remainder. -/
  compute_nonneg : 0 ≤ s'.computeBudget
  /-- Exploration consumes no risk margin. -/
  risk_next : s'.riskRem = s.riskRem
  /-- Exploration consumes no delta. -/
  delta_next : s'.deltaRem = s.deltaRem

/-! ## CRAMAcceptedSolution: production certificate -/

/-- The production certificate: a `ValidityCertificate` (givens
preserved + constraints satisfied — C263 `EnergyStopping`)
agreeing with the current board, with an OPTIONAL energy bound.
Validity says NOTHING about energy (E4 separation: the bound is
optional data, and an energy threshold alone certifies nothing). -/
structure CRAMAcceptedSolution (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (C : ι → α → Prop)
    (s : CRAMState ι α) where
  /-- The validity certificate (C263). -/
  cert : ValidityCertificate s.problem.givens C
  /-- The certified configuration IS the current board. -/
  board_agrees : ∀ i, cert.y i = s.board i
  /-- An optional certified energy bound (`none` = no claim). -/
  energyBound : Option ℝ
  /-- The energy bound, when present, holds for the certified
  configuration. -/
  energy_ok : ∀ τ, energyBound = some τ →
    pairwiseEnergy B K cert.y ≤ τ

/-! ## Hold: full state equality on the CRAM carrier -/

/-- A kernel hold on the CRAM carrier fixes the FULL state —
problem, board, latent, both budgets, risk and delta remainders
(Hold = full state equality; the kernel `HoldStep` is reused
as-is, `CRAMState.ext_iff` gives the componentwise reading). -/
theorem _root_.Hagi.Cert.HoldStep.cram_state_components {TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics (CRAMState ι α) TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (s s' : CRAMState ι α)
    (h : Hagi.Cert.HoldStep M obl s s') :
    s'.problem = s.problem ∧ s'.board = s.board
      ∧ s'.latent = s.latent ∧ s'.searchBudget = s.searchBudget
      ∧ s'.computeBudget = s.computeBudget ∧ s'.riskRem = s.riskRem
      ∧ s'.deltaRem = s.deltaRem := by
  have e : s' = s := h.hold
  subst e
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### C278-адаптер: CRAMEnergyDescentStep → общее ядро CertStepGen

A10 item 2 (третий адаптер): спускной шаг CRAM как шаг общего ядра
`Hagi.Cert.CertStepGen`. Отличия от C267-моста `toKernelCertStep`:
остаток риска — НЕ пиннинг, а чтение носителя `s'.riskRem`
(ненулевой остаток допустим по построению), и δ-канал ядра
живёт на носителе `deltaRem` (нулевой расход у спускового шага —
запись явная, свёрнутый C245-канал). -/

/-- C278: спускной шаг CRAM — шаг общего ядра (premise-form:
метрики читают энергию доски, вычислительный бюджет и остаток
риска; δ-канал — на носителе `deltaRem`, спуск δ не тратит;
неотрицательность δ-остатка — явная посылка `hdelta` — в самом
`CRAMState` ограничения на `deltaRem` нет). -/
noncomputable def CRAMEnergyDescentStep.toCertStepGen {TaskId : Type*}
    (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    {s s' : CRAMState ι α} (h : CRAMEnergyDescentStep B K s s')
    (M : Hagi.Cert.SystemMetrics (CRAMState ι α) TaskId)
    (hobj : M.objective = fun t => pairwiseEnergy B K t.board)
    (hbud : M.budget = fun t => t.computeBudget)
    (hrisk : M.risk = fun t => t.riskRem)
    (obl : Hagi.Cert.StepObligations TaskId)
    (hfloors : Hagi.Cert.FloorsKept M obl s')
    (hdelta : 0 ≤ s.deltaRem) :
    Hagi.Cert.CertStepGen M obl (fun t => t.deltaRem) s s' where
  drop := pairwiseEnergy B K s.board - pairwiseEnergy B K s'.board
  drop_pos := by linarith [h.strictDrop]
  descent := by
    simp only [hobj]
    linarith [h.strictDrop]
  budgetSpend := h.computeCost
  budget_next := by simp only [hbud]; exact h.compute_next
  budget_nonneg := by simp only [hbud]; exact h.compute_nonneg
  riskSpend := h.margin
  riskRem := s'.riskRem
  risk_next := by simp only [hrisk]
  risk_split := by
    simp only [hrisk]
    have e := h.risk_next
    linarith
  risk_nonneg := h.risk_nonneg
  delta := 0
  delta_next := by simp; exact h.delta_next
  delta_nonneg := by
    have e := h.delta_next
    simp
    linarith
  floorsKept := hfloors

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Finite-class generalization for learned energy models (C315)

P4 frontier item (ranked #3 in `.omc/analysis/period-c298-c312-analysis.md`):
what generalization claim is TRUE and cheaply provable for a learned-energy
solver.  The honest two-tier structure (research: `.tmp/C315/research.md`):

* TIER 1 (correctness, EXACT): accepted outputs are validated by the
  independent `CRAMAcceptedSolution` certificate (givens preserved +
  constraints satisfied, C267/C263).  Correctness does NOT depend on any
  generalization bound — the learned energy is quarantined to efficiency.
* TIER 2 (efficiency, LEARNED): over a FINITE hypothesis class of energy
  tables indexed by a `Fintype ι`, uniform convergence of the [0,1]-bounded
  PL loss holds via the C264 finite-family union composed with the C287
  concentration API (`concRadius`, `concRadius_valid`) — no new
  concentration mathematics.

What is NOT claimed (honesty ledger, research.md §2): no continuous
classes, no Rademacher/VC machinery, no stability, no claim that low PL
loss implies validity (that is exactly the C269 non-separation), no
distributional assumption beyond the explicit independent finite product.

The `[0,1]` bound on the loss `X k` is a PREMISE (the `[0,L]` scale route
exists via `FiniteFamilyConfidence.populationMean_le_empiricalMean_of_scale`).
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Probability Hagi.Probability.FiniteFamilyConfidence

/-! ## Tier 2: uniform convergence over a finite energy class -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- C315 MAIN (uniform convergence, finite class): for a FINITE class of
energy tables indexed by `ι` with `[0,1]`-normalized PL losses `X k`, with
probability ≥ `1 − δ` EVERY hypothesis's population PL-loss is within
`concRadius (δ/|ι|) n` of its empirical loss.  This is the C264 finite
family union bound (`finite_family_upper_confidence`) at the C287 radius
`concRadius (δ/|class|) n` (`concRadius_valid`): the class-size penalty
is the standard `log |class|` structural-risk term on a finite class. -/
theorem finite_class_pl_uniform {n : ℕ} {ι : Type} [Fintype ι]
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : ι → Fin n → V → ℝ) (hX : ∀ k i v, 0 ≤ X k i v ∧ X k i v ≤ 1)
    (hn : 0 < n) {delta : ℝ} (hd1 : 0 < delta) (hd2 : delta < 1)
    (hcard : 0 < Fintype.card ι) :
    1 - delta ≤ prodPq p (fun ω => ∀ k,
      populationMean p (X k) ≤ empiricalMean (X k) ω +
        concRadius (delta / (Fintype.card ι : ℝ)) n) := by
  have hc : 0 < (Fintype.card ι : ℝ) := by positivity
  have hc1 : (1:ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hcard
  have hlt : delta / (Fintype.card ι : ℝ) < 1 :=
    (div_lt_one₀ hc).mpr (lt_of_lt_of_le hd2 hc1)
  have hdv : concConfidence
        (concRadius (delta / (Fintype.card ι : ℝ)) n) n ≤
      delta / (Fintype.card ι : ℝ) :=
    concRadius_valid (div_pos hd1 hc) hlt hn
  have hrpos : 0 < concRadius (delta / (Fintype.card ι : ℝ)) n := by
    unfold concRadius
    refine Real.sqrt_pos.mpr (div_pos ?_ (by positivity))
    exact Real.log_pos (by
      rw [lt_div_iff₀ (div_pos hd1 hc), one_mul]
      exact hlt)
  have hconf := finite_family_upper_confidence p hp X hX hn _ hrpos
  have hbudget : (Fintype.card ι : ℝ) * concConfidence
      (concRadius (delta / (Fintype.card ι : ℝ)) n) n ≤ delta := by
    have h2 := mul_le_mul_of_nonneg_left hdv hc.le
    rw [mul_div_cancel₀ _ hc.ne'] at h2
    exact h2
  calc 1 - delta ≤ 1 - (Fintype.card ι : ℝ) * concConfidence
        (concRadius (delta / (Fintype.card ι : ℝ)) n) n := by
          refine le_of_eq_of_le rfl ?_
          rw [sub_le_sub_iff_left]
          exact hbudget
    _ ≤ prodPq p (fun ω => ∀ k,
        populationMean p (X k) ≤ empiricalMean (X k) ω +
          concRadius (delta / (Fintype.card ι : ℝ)) n) := by
          exact hconf

/-- C315 margin corollary (finite-class argmax identification): on the
simultaneous two-sided event of `finite_family_abs_error_confidence`
(C264), if the empirical winner `best`'s margin over every other
hypothesis is at least `2 * eps`, then `best` is the TRUE population-best
hypothesis: population loss of `best` ≤ population loss of every `k`.
Standard finite-class identification (the informal "gap > 2·radius"
condition; the non-strict `≤` form here covers it). -/
theorem finite_class_pl_margin_argmax {n : ℕ} {ι : Type} [Fintype ι]
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : ι → Fin n → V → ℝ) (hX : ∀ k i v, 0 ≤ X k i v ∧ X k i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) (best : ι)
    (hmargin : ∀ ω k,
      2 * eps ≤ empiricalMean (X k) ω - empiricalMean (X best) ω) :
    1 - 2 * (Fintype.card ι : ℝ) * Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤
      prodPq p (fun ω => ∀ k,
        populationMean p (X best) ≤ populationMean p (X k)) := by
  refine le_trans (finite_family_abs_error_confidence p hp X hX hn eps heps) ?_
  apply prodPq_mono p hp
  intro ω hω k
  by_cases hk : k = best
  · subst hk
    exact le_refl _
  · have hb := abs_le.mp (hω best)
    have hkk := abs_le.mp (hω k)
    have hm := hmargin ω k
    have h1 : populationMean p (X best) - empiricalMean (X best) ω ≤ eps := hb.2
    have h2 : empiricalMean (X k) ω - populationMean p (X k) ≤ eps := by
      have := hkk.1
      linarith
    linarith

/-! ## Tier 1: exact correctness through the independent validator -/

section Solver

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- C315 TIER-1 MAIN (exact correctness, energy-free): any ACCEPTED
solution of the learned-energy solver — acceptance goes through the
independent `CRAMAcceptedSolution` certificate (C267), never through the
energy — preserves every given cell BOTH in the certificate and ON THE
BOARD, and satisfies every constraint on the board.  Correctness does not
depend on any generalization bound: the statement mentions neither sample
nor energy, by construction. -/
theorem learned_solver_correctness_exact {B : ι → α → ℝ}
    {K : ι → ι → α → α → ℝ} {C : ι → α → Prop} {s : CRAMState ι α}
    (sol : CRAMAcceptedSolution B K C s) :
    (∀ i a, s.problem.givens i = some a →
        sol.cert.y i = a ∧ s.board i = a) ∧
      ∀ i, C i (s.board i) := by
  constructor
  · intro i a h
    exact ⟨sol.cert.preserves_givens i a h,
      (sol.board_agrees i).symm.trans (sol.cert.preserves_givens i a h)⟩
  · intro i
    have hci := sol.cert.satisfies_constraints i
    exact sol.board_agrees i ▸ hci

/-- C315 QUARANTINE (two-tier separation, failure side): even on the
COMPLEMENT of the uniform-convergence event of `finite_class_pl_uniform`,
every accepted solution is STILL valid.  Generalization debt is confined
to efficiency (how often search succeeds, how tight the optional energy
bound is), never to correctness. -/
theorem accepted_solution_valid_of_generalization_failure
    {n : ℕ} {V : Type} [Fintype V] [Nonempty V] {ι : Type}
    [Fintype ι] [DecidableEq ι] {α : Type} [Fintype α] [DecidableEq α]
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : ι → Fin n → V → ℝ) (hX : ∀ k i v, 0 ≤ X k i v ∧ X k i v ≤ 1)
    (hn : 0 < n) {delta : ℝ} (hd1 : 0 < delta) (hd2 : delta < 1)
    (hcard : 0 < Fintype.card ι)
    (hfail : ¬ (1 - delta ≤ prodPq p (fun ω => ∀ k,
      populationMean p (X k) ≤ empiricalMean (X k) ω +
        concRadius (delta / (Fintype.card ι : ℝ)) n)))
    {B : ι → α → ℝ} {K : ι → ι → α → α → ℝ} {C : ι → α → Prop}
    {s : CRAMState ι α}
    (sol : CRAMAcceptedSolution B K C s) :
    (∀ i a, s.problem.givens i = some a →
        sol.cert.y i = a ∧ s.board i = a) ∧
      ∀ i, C i (s.board i) :=
  learned_solver_correctness_exact sol

end Solver

/-! ## Numeric anchor -/

/-- C315 numeric anchor: at `m = 1000` samples, class size `|ι| = 10`,
`δ = 0.05`, the per-class budget is `δ/|ι| = 0.005` and the radius is
`concRadius 0.005 1000 = sqrt (log 200 / 2000) ≈ 0.0515` (float, for
orientation only).  The PROVED bound is the honest loose form
`≤ 1/15 ≈ 0.0667` via `log 200 ≤ 8` (since `200 ≤ 2 ^ 8 ≤ e ^ 8`,
using `2 = 1 + 1 ≤ exp 1`). -/
theorem concRadius_anchor_315 :
    concRadius (0.05 / 10) 1000 ≤ 1 / 15 := by
  have h200 : (1:ℝ) / (0.05 / 10) = 200 := by norm_num
  have hlog : Real.log 200 ≤ 8 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc 200 ≤ (2:ℝ) ^ 8 := by norm_num
      _ ≤ (Real.exp 1) ^ 8 :=
          pow_le_pow_left₀ (by norm_num)
            (le_trans (by rw [add_comm]; norm_num) (Real.add_one_le_exp 1)) 8
      _ = Real.exp 8 := by rw [← Real.exp_nat_mul]; norm_num
  have hnum : Real.log (1 / (0.05 / 10)) / (2 * (1000 : ℝ)) ≤ (1 / 15) ^ 2 := by
    have hdiv : Real.log 200 / (2 * (1000 : ℝ)) ≤ (1 / 15) ^ 2 := by
      have h8 : (8:ℝ) / (2 * 1000) ≤ (1 / 15) ^ 2 := by norm_num
      calc Real.log 200 / (2 * (1000 : ℝ))
          ≤ 8 / (2 * (1000 : ℝ)) :=
            div_le_div_of_nonneg_right hlog (by norm_num)
        _ ≤ (1 / 15) ^ 2 := h8
    rw [h200]
    exact hdiv
  unfold concRadius
  rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 15)]
  exact Real.sqrt_le_sqrt hnum

end Hagi.Model.EnergyReasoning
