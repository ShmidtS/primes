/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Energy.PairwiseCategorical

set_option linter.style.header false

/-!
# Single-cell descent on the categorical pairwise energy

Track E2 (addendum A9 + A9-supplement, CRAM / arXiv:2611.17309): the discrete
single-cell core — the exact energy delta of moving ONE cell, the greedy
nonincrease certificate, and the three DISTINCT stationarity/validity notions
(never conflated).

* `localField` — the supplement's local field
  `L_i(a) = B_i(a) + Σ_{j ≠ i} K_ij(a, y_j)`.
* `transposeLocalField` — the transpose companion
  `Σ_{j ≠ i} K_ji(y_j, a)`; without K-symmetry the exact delta is the
  SYMMETRIZED-field difference, with symmetry it collapses to `localField`.
* `single_cell_move_energy_delta` — (E2a MAIN, general, NO symmetry
  assumed): `E(y^{i←a}) − E(y) = (1/2)·((Ld a + Lt a) − (Ld b + Lt b)) +
  (B_i(a) − B_i(b))`, `b = y_i`. Every partition term not involving cell `i`
  cancels EXACTLY — this is the clean cancellation the C260 ordered-pair
  convention (factor `1/2` outside) buys.
* `single_cell_move_energy_delta_symm` — under symmetric `K`
  (`K_ij(a,b) = K_ji(b,a)`, the CRAM `W = sym(K)`): the delta is EXACTLY
  `L_i(a) − L_i(b)`.
* `greedy_single_cell_nonincreasing` — moving cell `i` to a minimizer of its
  local field never increases the energy (under `hK`).
* `strict_drop_of_positive_margin` — a positive local-field margin gives a
  strict energy drop (under `hK`).
* `IsCoordinateMinimum` / `IsGlobalMinimum` / `IsValidSolution` — three
  distinct predicates with documented implication gaps: coordinate-min ↛
  global-min (witness below), global-min ↛ valid, valid ↛ anything. The only
  implication that holds is `global_minimum_is_coordinate_minimum`.

## Honest boundaries (A9 'not to adopt' list)

Energy descent is NOT correctness: no minimum notion implies
`IsValidSolution`, and validity says nothing about energy. The greedy
nonincrease is a property of SINGLE-CELL moves on the supplement local field
under symmetric `K`; it implies nothing about multi-cell moves, Euler steps
of the continuous flow (the paper's own caveat — the safe discrete
certificate is the coordinate-KL identity of
`Hagi.Energy.EnergyCoordinateStep`), or convergence.
-/

namespace Hagi.Energy

section Definitions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- Local field `L_i(a) = B_i(a) + Σ_{j ≠ i} K_ij(a, y_j)`
(A9-supplement form: the computable one-sided field). -/
noncomputable def localField (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (y : ι → α) (i : ι) (a : α) : ℝ :=
  B i a + ∑ j ∈ Finset.univ \ {i}, K i j a (y j)

/-- Transpose field `Σ_{j ≠ i} K_ji(y_j, a)` — the honest no-symmetry
companion of `localField`; the two coincide under symmetric `K`. -/
noncomputable def transposeLocalField (K : ι → ι → α → α → ℝ)
    (y : ι → α) (i : ι) (a : α) : ℝ :=
  ∑ j ∈ Finset.univ \ {i}, K j i (y j) a

end Definitions

section Delta

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- Split of a full-`univ` sum at one index (helper for the delta proof). -/
theorem sum_univ_split (f : ι → ℝ) (i : ι) :
    (∑ i' ∈ Finset.univ, f i') = f i + (∑ i' ∈ Finset.univ.erase i, f i') := by
  have h : (∑ i' ∈ Finset.univ, f i')
      = (∑ i' ∈ insert i (Finset.univ.erase i), f i') := by
    rw [Finset.insert_erase (Finset.mem_univ i)]
  rw [h, Finset.sum_insert (by simp [Finset.mem_erase])]

/-- (E2a MAIN, general, NO symmetry): the exact single-cell move delta is
the SYMMETRIZED-field difference. All interaction terms not involving the
moved cell `i` cancel exactly (the C260 ordered-pair convention with the
factor `1/2` outside). -/
theorem single_cell_move_energy_delta (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (y : ι → α) (i : ι) (a : α) :
    pairwiseEnergy B K (Function.update y i a) - pairwiseEnergy B K y
      = (1 / 2) * (((∑ j ∈ Finset.univ \ {i}, K i j a (y j))
            + (∑ j ∈ Finset.univ \ {i}, K j i (y j) a))
          - ((∑ j ∈ Finset.univ \ {i}, K i j (y i) (y j))
            + (∑ j ∈ Finset.univ \ {i}, K j i (y j) (y i))))
        + (B i a - B i (y i)) := by
  classical
  have hun : ((∑ i', B i' (Function.update y i a i')) - (∑ i', B i' (y i')))
      = B i a - B i (y i) := by
    rw [← Finset.sum_sub_distrib,
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
        (fun i' _ hi' => by rw [Function.update_of_ne hi' a y]; ring),
      Function.update_self]
  set g : ι → ℝ := fun i' => (∑ j ∈ Finset.univ \ {i'},
      (K i' j (Function.update y i a i') (Function.update y i a j)
        - K i' j (y i') (y j))) with hg
  have hsplit : pairwiseInteractionSum K (Function.update y i a)
      - pairwiseInteractionSum K y = ∑ i', g i' := by
    rw [pairwiseInteractionSum, pairwiseInteractionSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i' _ => (Finset.sum_sub_distrib _ _).symm
  have hpair : pairwiseEnergy B K (Function.update y i a) - pairwiseEnergy B K y
      = ((∑ i', B i' (Function.update y i a i')) - (∑ i', B i' (y i')))
        + (1 / 2) * (∑ i', g i') := by
    rw [pairwiseEnergy, pairwiseEnergy]
    have hEq : ((∑ i', B i' (Function.update y i a i'))
          + (1 / 2) * pairwiseInteractionSum K (Function.update y i a))
        - ((∑ i', B i' (y i')) + (1 / 2) * pairwiseInteractionSum K y)
        = ((∑ i', B i' (Function.update y i a i')) - (∑ i', B i' (y i')))
          + (1 / 2) * (pairwiseInteractionSum K (Function.update y i a)
            - pairwiseInteractionSum K y) := by ring
    rw [hEq, hsplit]
  have hun' : ∀ j ∈ Finset.univ \ {i}, Function.update y i a j = y j := by
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
    exact Function.update_of_ne hj.2 a y
  have hi : g i = ((∑ j ∈ Finset.univ \ {i}, K i j a (y j))
      - (∑ j ∈ Finset.univ \ {i}, K i j (y i) (y j))) := by
    have hb : (∑ j ∈ Finset.univ \ {i},
        (K i j (Function.update y i a i) (Function.update y i a j)
          - K i j (y i) (y j)))
        = (∑ j ∈ Finset.univ \ {i},
            (K i j a (y j) - K i j (y i) (y j))) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hun' j hj, Function.update_self]
    show (∑ j ∈ Finset.univ \ {i},
        (K i j (Function.update y i a i) (Function.update y i a j)
          - K i j (y i) (y j))) = _
    rw [hb]
    exact Finset.sum_sub_distrib _ _
  have hneE : ∀ i', i' ∈ Finset.univ.erase i → i' ≠ i := by
    intro i' hi'
    rw [Finset.mem_erase] at hi'
    exact hi'.1
  have hmem : ∀ i', i' ∈ Finset.univ.erase i → i' ∈ Finset.univ \ {i} := fun i' hi' =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ i', by
      simp only [Finset.mem_singleton]
      exact hneE i' hi'⟩
  have hne : ∀ i' ∈ Finset.univ.erase i,
      g i' = K i' i (y i') a - K i' i (y i') (y i) := by
    intro i' hi'
    have h1 : Function.update y i a i' = y i' :=
      Function.update_of_ne (hneE i' hi') a y
    have h2 : i ∈ Finset.univ \ {i'} := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, by
      simp only [Finset.mem_singleton]
      exact (hneE i' hi').symm⟩
    have hzero : ∀ j ∈ Finset.univ \ {i'}, j ≠ i →
        (K i' j (Function.update y i a i') (Function.update y i a j)
          - K i' j (y i') (y j)) = 0 := by
      intro j hj hij
      rw [Function.update_of_ne hij a y, h1]
      ring
    have E : (∑ j ∈ Finset.univ \ {i'},
        (K i' j (Function.update y i a i') (Function.update y i a j)
          - K i' j (y i') (y j)))
        = K i' i (y i') a - K i' i (y i') (y i) := by
      rw [Finset.sum_eq_single_of_mem i h2 hzero, h1, Function.update_self]
    show (∑ j ∈ Finset.univ \ {i'},
        (K i' j (Function.update y i a i') (Function.update y i a j)
          - K i' j (y i') (y j))) = _
    exact E
  have hrest : (∑ i' ∈ Finset.univ.erase i, g i')
      = ((∑ i' ∈ Finset.univ.erase i, K i' i (y i') a)
        - (∑ i' ∈ Finset.univ.erase i, K i' i (y i') (y i))) := by
    rw [Finset.sum_congr rfl (fun i' hi' => hne i' hi'),
      ← Finset.sum_sub_distrib]
  rw [hpair, hun, sum_univ_split g i, hi, hrest,
    Finset.sdiff_singleton_eq_erase]
  ring

/-- Under symmetric `K` (`K_ij(a,b) = K_ji(b,a)`, the CRAM `W = sym(K)`):
the transpose field equals the direct field, so the exact delta collapses
to the supplement's one-sided `localField` difference. -/
theorem transposeLocalField_eq_localField_part
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (y : ι → α) (i : ι) (c : α) :
    transposeLocalField K y i c
      = ∑ j ∈ Finset.univ \ {i}, K i j c (y j) :=
  Finset.sum_congr rfl fun j _ => hK j i (y j) c

/-- (E2a, symmetric form): under symmetric `K` the single-cell move delta
is EXACTLY the `localField` difference `L_i(a) − L_i(y_i)`
(the supplement's practical form). -/
theorem single_cell_move_energy_delta_symm (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (y : ι → α) (i : ι) (a : α) :
    pairwiseEnergy B K (Function.update y i a) - pairwiseEnergy B K y
      = localField B K y i a - localField B K y i (y i) := by
  rw [single_cell_move_energy_delta B K y i a, localField, localField,
    show (∑ j ∈ Finset.univ \ {i}, K j i (y j) a)
      = transposeLocalField K y i a from rfl,
    show (∑ j ∈ Finset.univ \ {i}, K j i (y j) (y i))
      = transposeLocalField K y i (y i) from rfl,
    transposeLocalField_eq_localField_part K hK y i a,
    transposeLocalField_eq_localField_part K hK y i (y i)]
  have key : ∀ x y : ℝ, (1 / 2) * ((x + x) - (y + y)) = x - y := by
    intro x y; field_simp; ring
  rw [key]
  ring

end Delta

section Greedy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- Greedy single-cell move to a LOCAL-FIELD minimizer never increases the
energy (under symmetric `K`): the move `y_i → a` with
`∀ a', localField B K y i a ≤ localField B K y i a'` has
`E(y^{i←a}) ≤ E(y)`. -/
theorem greedy_single_cell_nonincreasing (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (y : ι → α) (i : ι) (a : α)
    (hmin : ∀ a' : α, localField B K y i a ≤ localField B K y i a') :
    pairwiseEnergy B K (Function.update y i a) ≤ pairwiseEnergy B K y := by
  have hd := single_cell_move_energy_delta_symm B K hK y i a
  have hle := hmin (y i)
  linarith

/-- A strictly positive local-field margin gives a strictly positive energy
drop (under symmetric `K`): `L_i(y_i) − L_i(a) > 0 ⟹
E(y^{i←a}) < E(y)`. -/
theorem strict_drop_of_positive_margin (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (y : ι → α) (i : ι) (a : α)
    (hmargin : 0 < localField B K y i (y i) - localField B K y i a) :
    pairwiseEnergy B K (Function.update y i a) < pairwiseEnergy B K y := by
  have hd := single_cell_move_energy_delta_symm B K hK y i a
  linarith

end Greedy

section Minima

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- Coordinate minimum: no SINGLE-CELL move decreases the energy (weak:
ties allowed). This is the stationarity notion greedy descent reaches;
it is NOT the global minimum and NOT a validity certificate — see the
witnesses below and the module docstring. -/
def IsCoordinateMinimum (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (y : ι → α) : Prop :=
  ∀ (i : ι) (a : α),
    pairwiseEnergy B K y ≤ pairwiseEnergy B K (Function.update y i a)

/-- Global minimum over ALL configurations `y'` — a strictly stronger
notion than `IsCoordinateMinimum` (implication one-way, proven below),
and STILL not a validity certificate. -/
def IsGlobalMinimum (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (y : ι → α) : Prop :=
  ∀ y' : ι → α, pairwiseEnergy B K y ≤ pairwiseEnergy B K y'

/-- Validity certificate: per-cell constraint satisfaction (the
A9 'AcceptedSolution = preserves_givens + satisfies_constraints' spirit at
the abstract carrier level; givens are per-cell constraints `C i`).
NEVER implied by any energy-minimum notion: energy is efficiency of search,
the constraint certificate is correctness. -/
def IsValidSolution (C : ι → α → Prop) (y : ι → α) : Prop :=
  ∀ i, C i (y i)

/-- The one implication that holds: a global minimum is a coordinate
minimum (single-cell moves are a subset of all configurations). -/
theorem global_minimum_is_coordinate_minimum (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (y : ι → α) (h : IsGlobalMinimum B K y) :
    IsCoordinateMinimum B K y :=
  fun i a => h (Function.update y i a)

end Minima

section Fixture
/-! ## Fin 2 × Bool fixture (vacuity audit; C260 carrier Bex/Kex/xex/xtt) -/

open Hagi.Energy

/-- Kex is symmetric: the delta collapses to the localField form. -/
example (a : Bool) :
    pairwiseEnergy Bex Kex (Function.update xtt 0 a) - pairwiseEnergy Bex Kex xtt
      = localField Bex Kex xtt 0 a - localField Bex Kex xtt 0 (xtt 0) := by
  refine single_cell_move_energy_delta_symm Bex Kex ?_ xtt 0 a
  intro i j a b
  simp only [Kex, Bool.and_comm]
  split_ifs <;> ring

/-- Numeric anchor: `E(f, t) = B_0(f) + B_1(t) + (1/2)·(0 + 0) = 2` while
`E(t,t) = 5` — moving cell 0 from `t` to `f` drops the energy by exactly
the local-field margin `3`. -/
example : pairwiseEnergy Bex Kex (Function.update xtt 0 false) = 2 := by
  simp [pairwiseEnergy, pairwiseInteractionSum, Fin.sum_univ_two, xtt, Bex,
    Kex, Finset.sum_singleton, Function.update]
  norm_num

/-- Coordinate-min ↛ global-min witness (separate fixture):
with `B' i a = if a then 0 else (i + 1)` and the symmetric `Kex`, the state
`(t, f)` is a coordinate minimum with energy `2`, while the global minimum
is `(f, t)` with energy `1`. -/
noncomputable def Bc : Fin 2 → Bool → ℝ := fun i a => if a then 0 else (i : ℝ) + 1

/-- `E(t,t) = (1/2)·(2 + 2) = 2` (B-part zero at `t`). -/
private theorem Ectt : pairwiseEnergy Bc Kex xtt = 2 := by
  simp [pairwiseEnergy, pairwiseInteractionSum, Fin.sum_univ_two, Bc, Kex,
    Finset.sum_singleton, xtt]
  norm_num

/-- The witness state `xex = (t, f)`: `E = B_0(t) + B_1(f) = 0 + 2 = 2`. -/
private theorem Ecxex : pairwiseEnergy Bc Kex xex = 2 := by
  simp [pairwiseEnergy, pairwiseInteractionSum, Fin.sum_univ_two, Bc, Kex,
    Finset.sum_singleton, xex]
  norm_num

/-- The global minimum `(f, t)`: `E = B_0(f) + B_1(t) = 1 + 0 = 1 < 2`. -/
private theorem Ecft : pairwiseEnergy Bc Kex (fun i => i == 1) = 1 := by
  simp [pairwiseEnergy, pairwiseInteractionSum, Fin.sum_univ_two, Bc, Kex,
    Finset.sum_singleton]

/-- Coordinate-min ↛ global-min WITNESS: `xex = (t, f)` is a coordinate
minimum (both single-cell moves land at energy `≥ 2`: `(f,f) = 3`,
`(t,t) = 2 — ties allowed by the weak def), yet it is NOT a global minimum
(`(f,t) = 1 < 2`). -/
example : IsCoordinateMinimum Bc Kex xex := by
  intro i a
  fin_cases i <;> fin_cases a <;>
    simp [pairwiseEnergy, pairwiseInteractionSum, Fin.sum_univ_two, Bc, Kex,
      Finset.sum_singleton, Function.update, xex]; norm_num

example : ¬ IsGlobalMinimum Bc Kex xex := by
  intro h
  have h1 := h (fun i => i == 1)
  rw [Ecft] at h1
  rw [Ecxex] at h1
  simp at h1

end Fixture

end Hagi.Energy
