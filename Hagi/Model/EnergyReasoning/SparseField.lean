/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Energy.SingleCellDescent

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
