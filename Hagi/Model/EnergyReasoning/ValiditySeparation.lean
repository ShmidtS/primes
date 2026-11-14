/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Energy.PairwiseCategorical
import Hagi.Model.EnergyReasoning.EnergyStopping

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
