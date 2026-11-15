/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Contracts.GradientBottleneckIdentification
import Hagi.Cert.StepGen
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Sparsity-certified inference: the spectral mask and the compute ratio

Audit §8 («Ранг и биты — по water-filling») — the INFERENCE side of
sparsity: formal guarantees that restricting a weight to its rank-k
singular subspace (the premise-form spectral mask) preserves the
function within the spectral-tail budget while the matvec cost drops
to the rank fraction of dense. Every ingredient is cited from its own
carrier; only the PACKAGING is new:

* the mask error law is Eckart-Young — cited EXACTLY as
  `Hagi.Contracts.GradientBottleneckIdentification.
  eckart_young_lower_bound_rect_true_tail` (C281, true rectangular
  tail): NO rank-`k` approximant beats the tail
  (`sparse_mask_minimal`); NOT re-proven here;
* the function-level transfer is the C300/C322 Lipschitz-readout
  route (`Hagi.Budget.rd_step_error_bound` pattern): weight-space
  error becomes function error through a sensitivity-`sens`
  premise (`sparse_inference_error`);
* the op-count family is the C272 work-model discipline
  (`Hagi.Model.EnergyReasoning.localField_dense_work` et al.):
  ℕ product definitions, theorems only ABOUT the products
  (`denseMatVecWork`, `lowRankMatVecWork`, `lowrank_op_count_le/lt`,
  `lowrank_op_ratio`);
* the certified transition is the C322 packaging
  (`Hagi.Budget.rd_step_certified` pattern) over the C278 kernel
  (`Hagi.Cert.CertStepGen`): `sparse_step_certified` spends the
  low-rank matvec work in the budget channel (compute accounting)
  and the certified function error in the risk channel, explicit
  nonnegative remainders (the C254 no-zero-pinning lesson).

Honest scope:

* SPECTRAL (low-rank) sparsity only. The mask is "B lives in the
  top-k singular subspace" — premise-form `hE` in
  `sparse_inference_error` (the mask ACHIEVES the tail bound; exact
  equality holds for the truncated spectral mask in the square
  case, `frobenius_error_truncatedSVD` in Flywheel; the
  rectangular exact-equality bridge is deferred with the C232/C281
  root-sorting gap).
* UNSTRUCTURED (entrywise) sparsity is NOT claimed: the optimal
  entrywise mask under an error budget is NP-hard (Natarajan 1995,
  sparse-approximation hardness lineage) — acknowledged here, not
  formalized.
* Work model: entry-reads; the honest two-pass factorized matvec
  costs `2·k·n` reads against `n²` dense; the per-pass ratio `k/n`
  appears in docstrings, the exact identity in `lowrank_op_ratio`.
* No probability; no empirical constants in theorem statements.
-/

open Matrix Finset
open Hagi.External.Flywheel
open Hagi.Contracts.GradientBottleneckIdentification (rectangularTail
  eckart_young_lower_bound_rect_true_tail)
open scoped BigOperators

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

namespace Hagi.Contracts.SparseInferenceCert

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ## The certified-sparsity error bound -/

set_option linter.unusedSectionVars false in
/-- **MAIN — sparsity-certified inference, function level**: if the
rank-`k` spectral mask `B` achieves the spectral-tail error bound
(premise-form `hE : ‖A − B‖ ≤ (∑ i, (rectangularTail A k i)²)^{1/2}`;
true with equality for the truncated spectral mask — square case
`frobenius_error_truncatedSVD`, and unimprovable by
`sparse_mask_minimal`), then every `sens`-Lipschitz readout `phi`
(C300 pattern: the head-input perturbation through the backbone
sensitivity) changes by at most `sens` times the tail root:
`|phi B − phi A| ≤ sens · (∑ tail²)^{1/2}`. The mask structure is
the premise; the tail theorem is C281's, cited — the composition is
the only new content. -/
theorem sparse_inference_error
    (A B : Matrix m n ℂ) (k : ℕ)
    (hE : ‖A - B‖ ≤ (∑ i, (rectangularTail A k i)^2).sqrt)
    (phi : Matrix m n ℂ → ℝ) (sens : ℝ) (hsens : 0 ≤ sens)
    (hlip : ∀ X Y : Matrix m n ℂ,
      |phi X - phi Y| ≤ sens * ‖X - Y‖) :
    |phi B - phi A| ≤ sens * (∑ i, (rectangularTail A k i)^2).sqrt := by
  calc |phi B - phi A| ≤ sens * ‖B - A‖ := hlip B A
    _ = sens * ‖A - B‖ := by rw [norm_sub_rev]
    _ ≤ sens * (∑ i, (rectangularTail A k i)^2).sqrt :=
      mul_le_mul_of_nonneg_left hE hsens

/-- **Mask minimality** — Eckart-Young cited EXACTLY (C281
`eckart_young_lower_bound_rect_true_tail`, not re-proven): no
rank-`k` mask beats the spectral tail. This certificates that the
premise `hE` of `sparse_inference_error` is the best possible
error budget for any rank-`k` restriction of `A`. -/
theorem sparse_mask_minimal (inj : m → n) (hinj : Function.Injective inj)
    (A B : Matrix m n ℂ) (k : ℕ) (hB : B.rank ≤ k) :
    ∑ i, (rectangularTail A k i)^2 ≤ ‖A - B‖^2 :=
  eckart_young_lower_bound_rect_true_tail inj hinj A B k hB

/-! ## The op-count family (C272 work-model discipline) -/

/-- Dense matvec work (work-model definition, C272
`localField_dense_work` style): applying an `n×n` weight reads all
`n²` entries. -/
def denseMatVecWork (n : ℕ) : ℕ := n * n

/-- Low-rank matvec work (work-model definition): applying an
explicit rank-`k` factorization `A_k = ∑_{i<k} σᵢ uᵢ vᵢ*` costs,
per retained direction, ONE `n`-entry inner product (`vᵢᵀ x`) and
ONE `n`-entry scaled accumulation — the honest TWO-pass total
`2·k·n` entry-reads. Each single pass costs `k·n = (k/n)·n²` —
the per-pass `k/n` fraction of dense. -/
def lowRankMatVecWork (k n : ℕ) : ℕ := 2 * k * n

/-- Op-count bound: `2k ≤ n` makes the two-pass low-rank matvec
cheaper than dense (plain ℕ arithmetic on the work-model
products). -/
theorem lowrank_op_count_le (k n : ℕ) (h : 2 * k ≤ n) :
    lowRankMatVecWork k n ≤ denseMatVecWork n := by
  unfold lowRankMatVecWork denseMatVecWork
  nlinarith

/-- STRICT op-count advantage: `2k < n` is strictly cheaper
(the premise is necessary: `2k = n` equalizes the products). -/
theorem lowrank_op_count_lt (k n : ℕ) (h : 2 * k < n) :
    lowRankMatVecWork k n < denseMatVecWork n := by
  unfold lowRankMatVecWork denseMatVecWork
  nlinarith

/-- Exact compute ratio: the low-rank work IS `(2k/n)` times the
dense work (`0 < n`); per pass the factor is `k/n` — the
compute-minimization account of audit §8 (the same `k` that
water-filling chose for the bits buys the FLOPs fraction). -/
theorem lowrank_op_ratio (k n : ℕ) (hn : 0 < n) :
    (lowRankMatVecWork k n : ℝ) = (2 * (k : ℝ) / n) * (denseMatVecWork n : ℝ) := by
  unfold lowRankMatVecWork denseMatVecWork
  push_cast
  field_simp

/-! ## The certified transition (C322 packaging over the C278 kernel) -/

/-- **The sparsification step IS a certified transition**: the
spectral-mask step packaged as a `Hagi.Cert.CertStepGen` (the C322
`rd_step_certified` pattern): the budget channel spends
`workSpend` (instantiate at `lowRankMatVecWork k n` — the compute
accounting), the risk channel spends `errSpend` (instantiate at
`sens * (∑ tail²)^{1/2}` — the certified bound of
`sparse_inference_error`) with an EXPLICIT nonnegative remainder
(the C254 no-zero-pinning lesson), the false-commit delta channel
in premise form, descent in drop form `obj s' ≤ obj s − drop`
(the C267 LossCeiling polarity). -/
noncomputable def sparse_step_certified {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ)
    (workSpend errSpend : ℝ) (s s' : S)
    (drop : ℝ) (hdrop : 0 < drop)
    (hdesc : M.objective s' ≤ M.objective s - drop)
    (hbud : M.budget s' = M.budget s - workSpend)
    (hbudnn : 0 ≤ M.budget s')
    (riskRem : ℝ)
    (hrisk : M.risk s = errSpend + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (delta : ℝ)
    (hdelta : deltaLevel s' = deltaLevel s - delta)
    (hdeltaNN : 0 ≤ deltaLevel s')
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    Hagi.Cert.CertStepGen M obl deltaLevel s s' where
  drop := drop
  drop_pos := hdrop
  descent := hdesc
  budgetSpend := workSpend
  budget_next := hbud
  budget_nonneg := hbudnn
  riskSpend := errSpend
  riskRem := riskRem
  risk_next := hrisk'
  risk_split := hrisk
  risk_nonneg := hrem
  delta := delta
  delta_next := hdelta
  delta_nonneg := hdeltaNN
  floorsKept := hfloors

/-- The compute spend of the packaged step is the work argument. -/
theorem sparse_step_certified_budgetSpend {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ)
    (workSpend errSpend : ℝ) {s s' : S}
    (drop : ℝ) (hdrop : 0 < drop)
    (hdesc : M.objective s' ≤ M.objective s - drop)
    (hbud : M.budget s' = M.budget s - workSpend)
    (hbudnn : 0 ≤ M.budget s')
    (riskRem : ℝ)
    (hrisk : M.risk s = errSpend + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (delta : ℝ)
    (hdelta : deltaLevel s' = deltaLevel s - delta)
    (hdeltaNN : 0 ≤ deltaLevel s')
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    (sparse_step_certified M obl deltaLevel workSpend errSpend s s' drop hdrop
      hdesc hbud hbudnn riskRem hrisk hrisk' hrem delta hdelta hdeltaNN
      hfloors).budgetSpend = workSpend := rfl

/-- The risk spend of the packaged step is the certified error
argument. -/
theorem sparse_step_certified_errorSpend {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ)
    (workSpend errSpend : ℝ) {s s' : S}
    (drop : ℝ) (hdrop : 0 < drop)
    (hdesc : M.objective s' ≤ M.objective s - drop)
    (hbud : M.budget s' = M.budget s - workSpend)
    (hbudnn : 0 ≤ M.budget s')
    (riskRem : ℝ)
    (hrisk : M.risk s = errSpend + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (delta : ℝ)
    (hdelta : deltaLevel s' = deltaLevel s - delta)
    (hdeltaNN : 0 ≤ deltaLevel s')
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    (sparse_step_certified M obl deltaLevel workSpend errSpend s s' drop hdrop
      hdesc hbud hbudnn riskRem hrisk hrisk' hrem delta hdelta hdeltaNN
      hfloors).riskSpend = errSpend := rfl

/-! ## Numeric anchors: the 2×3 rank-1 instance -/

namespace Anchor

/-- The rank-one factor `U` of the anchor matrix (2×1). -/
private def Uex : Matrix (Fin 2) (Fin 1) ℂ :=
  Matrix.of fun i _ => if i = 0 then (1 : ℂ) else 0

/-- The rank-one factor `V` of the anchor matrix (1×3). -/
private def Vex : Matrix (Fin 1) (Fin 3) ℂ :=
  Matrix.of fun _ j => if j = 0 then (1 : ℂ) else 0

/-- The anchor matrix: 2×3, `Aex = Uex * Vex` — a single retained
direction (a scaled `e₀ ⊗ e₀`). -/
private def Aex : Matrix (Fin 2) (Fin 3) ℂ := Uex * Vex

/-- The anchor matrix has rank at most one: the factor-product rank
bound (`rank_mul_le_left` + `rank_le_card_width` — the
`factor_update_rank_le` twin, ℂ form). -/
private theorem Aex_rank_le : Aex.rank ≤ 1 := by
  have h1 : (Uex * Vex).rank ≤ Uex.rank := rank_mul_le_left Uex Vex
  have h2 : Uex.rank ≤ 1 := by simpa using rank_le_card_width Uex
  unfold Aex
  exact le_trans h1 h2

private theorem hmin_eq :
    min (Fintype.card (Fin 2)) (Fintype.card (Fin 3)) = 2 := by simp

private def idx0 : Fin (min (Fintype.card (Fin 2)) (Fintype.card (Fin 3))) :=
  ⟨0, by simp [hmin_eq]⟩

private def idx1 : Fin (min (Fintype.card (Fin 2)) (Fintype.card (Fin 3))) :=
  ⟨1, by simp [hmin_eq]⟩

private theorem idx0_le_idx1 : idx0 ≤ idx1 := by
  simp [idx1, idx0, Fin.mk_le_mk]

/-- **Tail numeric at k = 1**: the 2×3 rank-1 anchor has spectral
tail `∑ i ≥ 1 σᵢ² = 0` — the rank-1 mask is EXACT. (The spectrum
head beyond the rank vanishes: antitone +
`rank_eq_card_nonzero_singularValues_rect`; two nonzero singulars
would force rank ≥ 2 > 1. A NONZERO numeric tail is not yet
mechanizable — charpoly root-sorting, the C232/C281 deferral.) -/
private theorem tail_zero :
    ∑ i, (rectangularTail Aex 1 i)^2 = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  unfold rectangularTail
  split
  · rename_i h
    have hσ1 : Matrix.SVD.Rectangular.singularValues Aex idx1 = 0 := by
      by_contra hne
      have hanti := Matrix.SVD.Rectangular.singularValues_antitone Aex
      have hle : Matrix.SVD.Rectangular.singularValues Aex idx1 ≤
          Matrix.SVD.Rectangular.singularValues Aex idx0 := hanti idx0_le_idx1
      have hnn0 : Matrix.SVD.Rectangular.singularValues Aex idx0 ≠ 0 := by
        intro h0
        rw [h0] at hle
        have hp := Matrix.SVD.Rectangular.singularValues_nonneg Aex idx1
        exact hne (le_antisymm hle hp)
      have hcard := Matrix.SVD.Rectangular.rank_eq_card_nonzero_singularValues_rect Aex
      have hge : (2 : ℕ) ≤ Fintype.card
          {i : Fin (min (Fintype.card (Fin 2)) (Fintype.card (Fin 3))) //
            Matrix.SVD.Rectangular.singularValues Aex i ≠ 0} := by
        have h2min : (2 : ℕ) ≤ min
            (Fintype.card (Fin 2)) (Fintype.card (Fin 3)) := by simp
        have hinj : Function.Injective
            (fun (b : Fin 2) => (⟨Fin.castLE h2min b, by
              fin_cases b <;> first | exact hnn0 | exact hne⟩ :
              {i : Fin (min (Fintype.card (Fin 2)) (Fintype.card (Fin 3))) //
                Matrix.SVD.Rectangular.singularValues Aex i ≠ 0})) := by
          intro a b hab
          have h1 : (Fin.castLE h2min a : Fin (min
              (Fintype.card (Fin 2)) (Fintype.card (Fin 3)))) =
              (Fin.castLE h2min b) := congrArg Subtype.val hab
          have h2 : (a : ℕ) = (b : ℕ) := by
            simpa [Fin.val_castLE] using congrArg Fin.val h1
          exact Fin.ext h2
        simpa using Fintype.card_le_of_injective _ hinj
      rw [← hcard] at hge
      have := Aex_rank_le
      omega
    have hanti := Matrix.SVD.Rectangular.singularValues_antitone Aex
    have hpos := Matrix.SVD.Rectangular.singularValues_nonneg Aex i
    have h1i : idx1 ≤ i := by
      have hv : idx1.val = 1 := by simp [idx1]
      exact Fin.le_def.mpr (by rw [hv]; exact h)
    have hle := hanti h1i
    rw [hσ1] at hle
    rw [le_antisymm hle hpos]
    simp
  · simp

/-- **Inference-error anchor**: at `k = 1` the exact (rank-1) mask
makes the certified function bound `sens · 0` — the main theorem
instantiated, not a bare computation. -/
theorem anchor_error (phi : Matrix (Fin 2) (Fin 3) ℂ → ℝ) (sens : ℝ)
    (hsens : 0 ≤ sens)
    (hlip : ∀ X Y : Matrix (Fin 2) (Fin 3) ℂ,
      |phi X - phi Y| ≤ sens * ‖X - Y‖) :
    |phi Aex - phi Aex| ≤ sens * 0 := by
  have h := sparse_inference_error Aex Aex 1 (by
    rw [tail_zero, Real.sqrt_zero]; simp) phi sens hsens hlip
  simpa using h

/-- **Compute anchor**: the rank-1 matvec on the 3-wide side costs
`2·1·3 = 6` reads against the dense `3² = 9` (`decide`). -/
theorem anchor_count : lowRankMatVecWork 1 3 ≤ denseMatVecWork 3 := by
  decide

/-- **Ratio anchor**: `6 = (2/3)·9` — the exact ratio identity
instantiated at the anchor (`k/n = 1/3` per pass). -/
theorem anchor_ratio :
    (lowRankMatVecWork 1 3 : ℝ) = (2 / 3 : ℝ) * (denseMatVecWork 3 : ℝ) := by
  norm_num [lowrank_op_ratio]

end Anchor

end Hagi.Contracts.SparseInferenceCert
