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
import Hagi.Model.EnergyReasoning.Pseudolikelihood.Core

set_option linter.style.header false
/-!
# Sparse local field: neighbour-restricted sums and operation counts

Track D3 (addendum A11 P3 "sparse field update correctness"): the
claimed FLOP advantage of LOCAL (sparse) couplings, turned into
theorems. The dense `localField`
`L_i(a) = B i a + Σ_{j ≠ i} K i j a (y j)` sums over ALL off-diagonal
cells; when the coupling `K` is SUPPORTED on neighbour sets
`N : ι → Finset ι` (`j ∉ N i → K i j a b = 0`), summing only over
`N i` computes EXACTLY the same field, and the single-cell delta
identity composes unchanged. The cost advantage is a formal
ℕ-inequality: sparse work `(N i).card · (card α)²` ≤ dense work
`card(univ \ {i}) · (card α)²`, STRICT for a proper neighbour subset
— a Finset count, NOT a complexity framework.

* `couplingSupportedOn` — premise-form support: `K` vanishes off the
  neighbour sets (function-level, all four coupling arguments).
* `sparseLocalField` — the neighbour-restricted field
  `B i a + Σ_{j ∈ N i}, K i j a (y j)`.
* `sparse_neighbours_subset` — no self-neighbour (`i ∉ N i`) gives
  `N i ⊆ univ \ {i}` VERBATIM: the sparse split respects
  ordered-pair convention (off-diagonal, `1/2` outside in the energy;
  the field is one-sided and creates/destroys no diagonal entry).
* `sparse_localField_eq_dense` — (D3 MAIN) under support and
  no-self-neighbour the sparse field EQUALS the dense `localField`:
  zero couplings contribute nothing (`Finset.sum_subset`).
* `sparse_update_energy_delta_eq` — (D3 MAIN) with symmetric `K` the
  exact single-cell energy delta is the SPARSE field difference —
 `single_cell_move_energy_delta_symm` composed (cited, not
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
  every entry` `attentionCoupling` recipe), support of the
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
inside the dense off-diagonal `univ \ {i}` VERBATIM
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
field EQUALS the dense `localField`: zero couplings contribute
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
the DENSE pairwise energy is the SPARSE field difference
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
the dense field for every cell and value. -/
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
the exact-arithmetic descent of `Hagi.Energy.SingleCellDescent`:

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

/-- **`guarded_greedy_strict_drop`** — (P3 MAIN, composition
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
coincide (direct consequence of the ℓ∞ contraction
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
  every `L_ij`, so the kernel satisfies `hK` premise with NO
  symmetry hypothesis on `κ` or `w`. Fin 3 numeric anchor below uses
  a deliberately ASYMMETRIC `κ` to catch any index-role slip.
* `attention_coupling_bounded` — `|L_ij(a,b)| ≤ 2·κmax·fmax` when
  `0 ≤ κ ≤ κmax`, `w ∈ [0,1]`, `|f| ≤ fmax`. The constant `2` is
  TIGHT: two directed contributions, each `≤ κmax·fmax` (witness: `f`
  constant `±fmax` attains both simultaneously).
* `attentionK` — the kernel `K(z)` at frozen `z` (`w = α(·; z)`),
  `attention_K_symmetric` — the premise verbatim.
* `frozen_z_field_with_attention` — the local field for `K(z)` is
  well-defined and the machinery applies at frozen `z`: a
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
* `latent_attention_guarded_drop` — the guard ABSORBS the latent
  error: with `ε := |S_i|·2κmax·fmax·L_sm·η`, a computed margin
  `2ε < L̂(y_i) − L̂(a)` on the `K(z)`-fields gives a STRICT drop of
  the TRUE energy `pairwiseEnergy B (attentionK κ w(z*) f)` — the
  2ε-guard recipe of `guarded_energy_delta` instantiated at the
  coupling bound.

## Honest boundaries (B3)

This is the STRUCTURAL CRAM+Z bridge only. Full Maze-Hard semantics —
support of `z*`, reachability, and JOINT `(z, y)` updates — remain
OPEN: joint updates are still forbidden by the E3 two-phase protocol
(a mid-descent z-move changes the kernel and voids the delta
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
`w`). This is why the kernel `attentionK` satisfies `hK`
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

/-- **`attention_K_symmetric`** — `K(z)` satisfies `hK`
premise verbatim, for ANY `κ` and `w` (constructive symmetry). -/
theorem attention_K_symmetric (κ w : ι → ι → ℝ) (f : α → α → ℝ) :
    ∀ i j a b, attentionK κ w f i j a b = attentionK κ w f j i b a :=
  fun i j a b => attention_coupling_symmetric κ w f i j a b

/-- **`frozen_z_field_with_attention`** — (B3 MAIN, thin by design)
the local field for `K(z)` is well-defined and the machinery
applies AT FROZEN `z`: moving cell `i` to a local-field minimizer of
`pairwiseEnergy B (attentionK κ (attentionWeights s) f)` does not
increase the energy. PREMISE-FORM for the descent — NO joint
`(z, y)` theorem exists or is claimed (E3 two-phase protocol: a
mid-descent z-move changes the kernel and voids the delta
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

/-- **`latent_attention_guarded_drop`** — (B3 MAIN) the guard
ABSORBS the latent error: with
`ε := |S_i|·2κmax·fmax·L_sm·η` (the coupling bound), a computed
improvement margin `2ε < L̂(y_i) − L̂(a)` on the `K(z)`-fields gives a
STRICT drop of the TRUE energy
`pairwiseEnergy B (attentionK κ w2 f)` — the `2ε`-guard recipe of
`guarded_energy_delta` instantiated at the attention coupling bound.
Rejection still carries no information (honesty). Joint
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

