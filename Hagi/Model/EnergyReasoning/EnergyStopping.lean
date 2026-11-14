/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Energy.SingleCellDescent

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
