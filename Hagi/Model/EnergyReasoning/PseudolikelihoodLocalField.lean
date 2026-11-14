/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.InfoCore
import Hagi.Core.Concat
import Hagi.Energy.PairwiseCategorical
import Hagi.Energy.SingleCellDescent
import Hagi.Model.CEGradient
import Hagi.Model.EnergyReasoning.Pseudolikelihood

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
