/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# Heterarchy — control as a spectrum, not a chain of command

Model: a context-dependent influence relation `R : C → M → M → ℝ`
(`dominatesIn`: `0 < R c i j` means module `i` constrains module
`j` in context `c`) and the "chain of command" hypothesis
`RankingConsistent`. (source: arXiv:2610.04643)

* `no_global_ranking` — if dominance reverses across two
  contexts (`a → b` in `c₁`, `b → a` in `c₂`), no linear
  ranking is consistent with all dominance relations.
* `cycle_breaks_ranking` — a 3-cycle of dominance (in possibly
  different contexts) breaks every ranking.
* `disagreement_survives_configs` — for `d ≠ 0`, the pair
  `(d, -d)` sums to exactly zero while `‖d‖ * ‖d‖ + ‖-d‖ * ‖-d‖`
  is strictly positive.
-/

namespace Hagi

open Finset

/-! ## The context-dependent dominance relation -/

variable {C M : Type}

/-- `dominatesIn R c i j`: in context c, module i constrains
module j (positive influence). -/
def dominatesIn (R : C → M → M → ℝ) (c : C) (i j : M) : Prop :=
  0 < R c i j

/-- A linear ranking r is consistent with the dominance
relation if every positive dominance forces a strict rank
drop: the "chain of command" hypothesis. -/
def RankingConsistent (R : C → M → M → ℝ) (r : M → ℝ) : Prop :=
  ∀ c i j, dominatesIn R c i j → r i > r j

/-- Reversed dominance across two contexts (`hab`, `hba`)
kills every linear ranking: `¬ RankingConsistent R r`. -/
theorem no_global_ranking (R : C → M → M → ℝ) (c₁ c₂ : C) (a b : M)
    (hab : dominatesIn R c₁ a b) (hba : dominatesIn R c₂ b a)
    (r : M → ℝ) : ¬ RankingConsistent R r := by
  intro hcons
  have h1 : r a > r b := hcons c₁ a b hab
  have h2 : r b > r a := hcons c₂ b a hba
  exact absurd h1 (not_lt.2 (le_of_lt h2))

/-- A 3-cycle of dominance (in possibly different contexts)
breaks every ranking. -/
theorem cycle_breaks_ranking (R : C → M → M → ℝ)
    (c₁ c₂ c₃ : C) (a b c : M)
    (hab : dominatesIn R c₁ a b)
    (hbc : dominatesIn R c₂ b c)
    (hca : dominatesIn R c₃ c a)
    (r : M → ℝ) : ¬ RankingConsistent R r := by
  intro hcons
  have h1 : r a > r b := hcons c₁ a b hab
  have h2 : r b > r c := hcons c₂ b c hbc
  have h3 : r c > r a := hcons c₃ c a hca
  linarith

/-! ## Merge answer: disagreement as a switchable resource -/

variable {X : Type} [NormedAddCommGroup X]

/-- For `d ≠ 0`: `d + -d = 0` while
`0 < ‖d‖ * ‖d‖ + ‖-d‖ * ‖-d‖` — the pair cancels in the mean
but retains positive energy. -/
theorem disagreement_survives_configs (d : X) (hd : d ≠ 0) :
    (d + -d = 0)
      ∧ 0 < ‖d‖ * ‖d‖ + ‖-d‖ * ‖-d‖ := by
  constructor
  · simp
  · have h1 : (0:ℝ) < ‖d‖ * ‖d‖ := by
      have h0 : (0:ℝ) < ‖d‖ := norm_pos_iff.mpr hd
      exact mul_pos h0 h0
    have h2 : ‖-d‖ * ‖-d‖ = ‖d‖ * ‖d‖ := by
      rw [norm_neg]
    rw [h2]
    linarith

end Hagi
