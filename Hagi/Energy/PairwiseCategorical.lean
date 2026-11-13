/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Prelude.InfoCore

set_option linter.style.header false

/-!
# Categorical pairwise energy and its mean-field free energy

Track E1 (addendum A9, CRAM / arXiv:2611.17309): the discrete pairwise
energy over finite variable configurations and the mean-field free
energy over product-marginal states, unified by two exact identities.

* `pairwise_energy_onehot` — (E1a) the mean-field free energy at the
  one-hot marginal state `δ_x` EQUALS the discrete energy `H(x)`,
  exactly, for every `β` (the entropy term `1 · log 1` vanishes):
  the vertex of the product simplex is the configuration.
* `meanfield_decomposition` — (E1b) the mean-field free energy splits
  exactly as `F(p) = E_{∏p_i}[H] + (1/β) Σ_i Σ_a p i a · log (p i a)`;
  in Shannon-entropy form `F(p) = E_{∏p_i}[H] − (1/β) Σ_i H(p_i)` with
  `H(p_i) = −Σ_a p i a · log (p i a)`.

## Convention (challenge-pinned, E1)

The interaction term is the ORDERED-pair sum
`pairwiseInteractionSum K x = Σ_i Σ_{j ≠ i} K i j (x i) (x j)` and the
energy carries the factor `1/2` outside it:
`pairwiseEnergy B K x = Σ_i B i (x i) + (1/2) * pairwiseInteractionSum K x`.
This is verbatim the CRAM shape `E_θ(p) = (1/β)Σ p log p + Σ Bᵀp +
(1/2)Σ_{i≠j} pᵢᵀ K_{ij} p_j`. NO symmetry of `K` is assumed; with
symmetric `K` the `1/2` compensates the ordered double count, without
symmetry it is a fixed convention — one convention everywhere in H and F,
so `pairwise_energy_onehot` carries no hidden diagonal correction.

## Sign-adapter warning (CRAM vs classic Hopfield)

CRAM/EBR uses `exp(−E/T)`: LOW energy = HIGH conditional logit (the
conditional logits of `Hagi.Model.EnergyReasoning.Pseudolikelihood` are
`z_ia = −H(y^{i←a})`). The classic Hopfield file
`Hagi/StatMech/Hopfield/Model.lean` uses the OPPOSITE convention
`Z = Σ_σ exp(β·E(σ))` with Hamiltonian `H = −E`. Any bridge between
this module and classic Hopfield MUST pass through an explicit sign
adapter; no such bridge is claimed here (E2+ scope).

## Honest boundaries

* `expectedPairwiseEnergy` packages the product-marginal expectation at
  the level of marginals (`P(X_i = a, X_j = b) = p i a * p j b` under
  independence); no measure-theory packaging is claimed.
* Nothing here asserts descent, convergence, or correctness of any
  update rule — those are E2+ certificates, not E1 identities.
-/

namespace Hagi.Energy

section Definitions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Ordered-pair interaction sum
`Σ_i Σ_{j ≠ i} K i j (x i) (x j)` (E1 convention: the `1/2` of the
energy compensates the ordered double count; no symmetry of `K`
assumed). -/
noncomputable def pairwiseInteractionSum (K : ι → ι → α → α → ℝ)
    (x : ι → α) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ \ {i}, K i j (x i) (x j)

/-- Discrete pairwise energy over configurations
`H(x) = Σ_i B i (x i) + (1/2) * pairwiseInteractionSum K x`
(unary fields `B`, pairwise couplings `K`). -/
noncomputable def pairwiseEnergy (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (x : ι → α) : ℝ :=
  ∑ i, B i (x i) + (1 / 2) * pairwiseInteractionSum K x

/-- The one-hot marginal state at configuration `x`
(the vertex `δ_x` of the product simplex). -/
noncomputable def oneHotState (x : ι → α) : ι → (α → ℝ) :=
  fun i => Pi.single (x i) 1

/-- Mean-field free energy over product-marginal states `p`, raw CRAM
form: `F(p) = (1/β) Σ_i Σ_a p i a · log (p i a)
+ Σ_i Σ_a B i a * p i a + (1/2) Σ_i Σ_{j≠i} Σ_a Σ_b K i j a b *
(p i a * p j b)`. -/
noncomputable def meanFieldFreeEnergy (β : ℝ) (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (p : ι → (α → ℝ)) : ℝ :=
  (1 / β) * ∑ i, ∑ a, p i a * Real.log (p i a)
  + ∑ i, ∑ a, B i a * p i a
  + (1 / 2) * ∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b, K i j a b * (p i a * p j b)

/-- Expectation of the discrete energy `pairwiseEnergy` under the
product measure of marginals `p` (independent coordinates:
`P(X_i = a, X_j = b) = p i a * p j b`):
`E_{∏p_i}[H] = Σ_i Σ_a B i a * p i a + (1/2) Σ_{i≠j} Σ_a Σ_b
K i j a b * (p i a * p j b)`. -/
noncomputable def expectedPairwiseEnergy (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (p : ι → (α → ℝ)) : ℝ :=
  ∑ i, ∑ a, B i a * p i a
  + (1 / 2) * ∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b, K i j a b * (p i a * p j b)

end Definitions

/-! ## Concrete 2×2 carrier (vacuity audit: Fin 2 variables, Bool values) -/

section Carrier

noncomputable def Bex : Fin 2 → Bool → ℝ := fun i a => if a then (i : ℝ) + 1 else 0
noncomputable def Kex : Fin 2 → Fin 2 → Bool → Bool → ℝ :=
  fun i j a b => if a && b then (i : ℝ) + (j : ℝ) + 1 else 0
noncomputable def xex : Fin 2 → Bool := fun i => i == 0
noncomputable def xtt : Fin 2 → Bool := fun _ => true

/-- Vacuity check: `x = (true, false)` — off-diagonal ordered pairs
`(0,1)`, `(1,0)` each hit a false literal, interaction `0`. -/
example : pairwiseInteractionSum Kex xex = 0 := by
  simp [pairwiseInteractionSum, Fin.sum_univ_two, xex, Kex, Finset.sum_singleton]

/-- Vacuity check: `x = (true, true)` — ordered pairs `(0,1)` and
`(1,0)` contribute `2` each, interaction sum `4` (NOT `8`: the ordered
sum counts both directions once, the `1/2` in the energy restores the
edge weight). -/
example : pairwiseInteractionSum Kex xtt = 4 := by
  simp [pairwiseInteractionSum, Fin.sum_univ_two, xtt, Kex, Finset.sum_singleton]
  norm_num

/-- Vacuity check: `H(xtt) = Σ B (1 + 2) + (1/2) * 4 = 5`. -/
example : pairwiseEnergy Bex Kex xtt = 5 := by
  have h : pairwiseInteractionSum Kex xtt = 4 := by
    simp [pairwiseInteractionSum, Fin.sum_univ_two, xtt, Kex,
      Finset.sum_singleton]
    norm_num
  simp [pairwiseEnergy, h, Fin.sum_univ_two, Bex, xtt]
  norm_num

end Carrier

section Identities

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- (E1a) The mean-field free energy at the one-hot state `δ_x` is
EXACTLY the discrete energy `H(x)` — for every `β` (also `β = 0`: the
entropy term `1 · log 1 = 0` kills the `(1/β)` factor). The vertex of
the product simplex is the configuration itself: nothing is smoothed
away at `δ_x`. -/
theorem pairwise_energy_onehot (β : ℝ) (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (x : ι → α) :
    meanFieldFreeEnergy β B K (oneHotState x) = pairwiseEnergy B K x := by
  rw [meanFieldFreeEnergy]
  have hent : ∑ i, ∑ a, oneHotState x i a * Real.log (oneHotState x i a) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases h : a = x i
    · subst h; simp [oneHotState]
    · simp [oneHotState, Pi.single_apply, h]
  rw [hent, mul_zero, zero_add, pairwiseEnergy]
  have hB : ∑ i, ∑ a, B i a * oneHotState x i a = ∑ i, B i (x i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [oneHotState, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.mem_univ]
  have hK : ∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b,
      K i j a b * (oneHotState x i a * oneHotState x j b)
      = pairwiseInteractionSum K x := by
    rw [pairwiseInteractionSum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
    simp [oneHotState, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.mem_univ]
  rw [hB, hK]

omit [DecidableEq α] in
/-- (E1b) Exact mean-field decomposition:
`F(p) = E_{∏p_i}[H] + (1/β) Σ_i Σ_a p i a · log (p i a)` — the free
energy is the product-marginal expected energy plus the (negative)
entropy surcharge. In Shannon form
`F(p) = E_{∏p_i}[H] − (1/β) Σ_i H(p_i)`, `H(p_i) = −Σ_a p i a · log (p i a)`.
The product-measure content sits in `expectedPairwiseEnergy`
(`P(X_i = a, X_j = b) = p i a * p j b`); the identity itself is the
exact rearrangement of the raw CRAM form. -/
theorem meanfield_decomposition (β : ℝ) (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (p : ι → (α → ℝ)) :
    meanFieldFreeEnergy β B K p
      = expectedPairwiseEnergy B K p
        + (1 / β) * ∑ i, ∑ a, p i a * Real.log (p i a) := by
  rw [meanFieldFreeEnergy, expectedPairwiseEnergy]
  ring

end Identities

end Hagi.Energy
