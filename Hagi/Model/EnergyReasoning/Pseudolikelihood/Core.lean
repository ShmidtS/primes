/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Math.Info.InfoCore
import Hagi.Core.Concat
import Hagi.Energy.PairwiseCategorical
import Hagi.Optimization.InexactContraction
import Hagi.Energy.SingleCellDescent
import Mathlib.Tactic
import Hagi.Runtime.BF16Delta
import Hagi.Probability.MirrorHedgeMWU
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
(the Prelude spine), so the CEDescent toolchain applies to
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
  (`Hagi.Energy.greedy_single_cell_nonincreasing`) applies verbatim.

## Two-phase protocol (supplement mandate)

Phase 1: iterate `latentUpdate` until `‖z^k − z*‖ < ε_z`
(`latent_settle_tolerance` gives the horizon). Phase 2: FREEZE the
latent contribution `zc` (constant in the visible state `y`) and run the
visible CRAM descent with bias `visibleBiasWithZ B zc`. JOINT `(z, p)`
updates are FORBIDDEN by this theory: a z-move changes the bias
`B' i a = B i a + zc i` mid-descent, so the single-cell delta
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
BY CONSTRUCTION — `zc` is not a function of `y`), the greedy
single-cell visible descent applies verbatim: the energy
`pairwiseEnergy (visibleBiasWithZ B zc) K` does not increase under a move
to a local-field minimizer.

JOINT `(z, p)` updates break the Lyapunov argument: a z-move changes the
bias mid-descent, the single-cell delta identity no longer bounds the
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
  `π(y) = exp(−E(y)/T)`. The proof reduces EXACTLY to the identity
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
`exp(−L_i(a)/T) / Σ_c exp(−L_i(c)/T)` with `L_i` `localField`. -/
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
 `pairwiseEnergy`. -/
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
`π(y) = exp(−E(y)/T)`. The proof is exactly the delta identity
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
/-! ## Fin 2 × Bool fixture (Bex/Kex/xtt carriers) -/

open Hagi.Energy

private theorem Kex_symm :
    ∀ (i j : Fin 2) (a b : Bool), Kex i j a b = Kex j i b a := by
  intro i j a b
  simp only [Kex, Bool.and_comm]
  split_ifs <;> ring

/-- Numeric anchor: `L_0(f) = 0`, `L_0(t) = 3` at `xtt = (t,t)` (
anchors `E(t,t) = 5`, `E(f,t) = 2`, so the delta identity gives
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

