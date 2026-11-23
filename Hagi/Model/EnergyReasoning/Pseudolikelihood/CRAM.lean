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
import Hagi.Probability.MirrorHedgeMWU
import Hagi.Cert.Core
import Hagi.Cert.StepGen
import Hagi.Probability.Concentration
import Hagi.Model.CEGradient
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Model.EnergyReasoning.Pseudolikelihood.Mixing

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
  `C_i(y) = L_i(y_i) − H(y)` a constant in `a`
  single-cell delta identity (reused verbatim) read as a
  constant offset.
* `conditionalDist_eq_localField_softmax` — the local Gibbs
  conditional satisfies `softDef(−β·H(y^{i←a})) =
  softDef(−β·L_i)` for EVERY β: the constant `β·C_i(y)` cancels
  in softmax (shift-invariance — NOT in the Prelude, added here
  as minimal private lemmas; audit note in the plan).
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

/-! ## Словарь перегрузок: `MetricDirection`
Канон-носитель направления метрики в CRAM-псевдоправдоподобии —
этот файл; одноимённые объявления внутри него различают
нормировки. Полное переименование — вне v5.
-/

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

Audit note (plan, challenge 1): NO softmax/CE const-shift
lemma exists in the Prelude (`InfoCore`), `Core.Concat`, or
`Numerics.Numerics` — only `softDef_pos`, `softDef_sum_one`,
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
 strict-drop margin, with MarginBudget accounting (the
  certified margin is deducted from the risk remainder);
  `strictDrop` reuses `strict_drop_of_positive_margin` verbatim;
  `toLossCeilingDrop` wires the LossCeiling polarity.
* `CRAMExplorationStep` — legal exploration transition: positive
  kernel mass, row-stochastic kernel premise (
  `mixture_rowsum` premise shape), clamps (givens) preserved,
  search budget consumed.  NO DESCENT CLAIM: exploration may
  RAISE the energy (stationarity is not monotonicity).
* `CRAMAcceptedSolution` — production certificate: a
  `ValidityCertificate` (givens preserved + constraints
  satisfied `EnergyStop`) agreeing with the board,
  with an OPTIONAL energy bound.
* `CRAMEnergyDescentStep.toKernelCertStep` — the canonical-kernel
  bridge (pattern: `HonestTransition.toKernelCertStep`):
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
  /-- The CRAM problem (constraint carrier). -/
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
pseudolikelihood objective: a MEASURED drop premise — the
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

/-! ## CRAMEnergyDescentStep: strict drop + MarginBudget -/

/-- Single-cell energy-descent contract: a strictly positive
local-field margin (the form) certifies a strict energy drop
`E(y^{i←a}) < E(y)`; the certified margin is DEDUCTED from the
risk remainder (MarginBudget accounting), the compute budget is
spent exactly, and the board moves by the single-cell update. -/
structure CRAMEnergyDescentStep (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (s s' : CRAMState ι α) where
  /-- Symmetric coupling premise (load-bearing for
  strict-drop theorem; satisfied by the constructive symmetrizer
  `symmetrizeCoupling`). -/
  hK : ∀ i j a b, K i j a b = K j i b a
  /-- The moved cell. -/
  cell : ι
  /-- The new value at the moved cell. -/
  move : α
  /-- The certified local-field margin. -/
  margin : ℝ
  /-- Strictly positive margin, form:
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

/-- The strict drop, verbatim: a positive local-field margin
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
`HonestTransition.toKernelCertStep`): under EXPLICIT
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
kernel mass under a ROW-STOCHASTIC kernel (
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
  heat-bath mixture). -/
  kernel : (ι → α) → (ι → α) → ℝ
  /-- Legality: the new board has positive transition mass. -/
  legality : 0 < kernel s.board s'.board
  /-- Row-stochasticity premise (`mixture_rowsum` shape):
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
preserved + constraints satisfied `EnergyStop`)
agreeing with the current board, with an OPTIONAL energy bound.
Validity says NOTHING about energy (E4 separation: the bound is
optional data, and an energy threshold alone certifies nothing). -/
structure CRAMAcceptedSolution (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (C : ι → α → Prop)
    (s : CRAMState ι α) where
  /-- The validity certificate. -/
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

/-- спускной шаг CRAM — шаг общего ядра (premise-form:
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
# Finite-class generalization for learned energy models

P4 frontier item:
what generalization claim is TRUE and cheaply provable for a learned-energy
solver.  The honest two-tier structure:

* TIER 1 (correctness, EXACT): accepted outputs are validated by the
  independent `CRAMAcceptedSolution` certificate (givens preserved +
  constraints satisfied).  Correctness does NOT depend on any
  generalization bound — the learned energy is quarantined to efficiency.
* TIER 2 (efficiency, LEARNED): over a FINITE hypothesis class of energy
  tables indexed by a `Fintype ι`, uniform convergence of the [0,1]-bounded
  PL loss holds via the finite-family union composed
  concentration API (`concRadius`, `concRadius_valid`) — no new
  concentration mathematics.

What is NOT claimed (honesty ledger, research.md §2): no continuous
classes, no Rademacher/VC machinery, no stability, no claim that low PL
loss implies validity (that is exactly the non-separation), no
distributional assumption beyond the explicit independent finite product.

The `[0,1]` bound on the loss `X k` is a PREMISE (the `[0,L]` scale route
exists via `FiniteFamilyConfidence.populationMean_le_empiricalMean_of_scale`).
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Probability Hagi.Probability.FiniteFamilyConfidence

/-! ## Tier 2: uniform convergence over a finite energy class -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- MAIN (uniform convergence, finite class): for a FINITE class of
energy tables indexed by `ι` with `[0,1]`-normalized PL losses `X k`, with
probability ≥ `1 − δ` EVERY hypothesis's population PL-loss is within
`concRadius (δ/|ι|) n` of its empirical loss.  This is the finite
family union bound (`finite_family_upper_confidence`) at the radius
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

/-- margin corollary (finite-class argmax identification): on the
simultaneous two-sided event of `finite_family_abs_error_confidence`
if the empirical winner `best`'s margin over every other
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

/-- TIER-1 MAIN (exact correctness, energy-free): any ACCEPTED
solution of the learned-energy solver — acceptance goes through the
independent `CRAMAcceptedSolution` certificate, never through the
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

/-- QUARANTINE (two-tier separation, failure side): even on the
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

/-- numeric anchor: at `m = 1000` samples, class size `|ι| = 10`,
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

