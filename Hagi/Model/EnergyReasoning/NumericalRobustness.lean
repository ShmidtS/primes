/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Energy.SingleCellDescent
import Hagi.Model.EnergyReasoning.LatentEnergy
import Hagi.Runtime.BF16Delta

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
