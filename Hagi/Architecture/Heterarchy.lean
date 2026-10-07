/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Ensemble.MergeCancellation
import Hagi.Ensemble.PolicyCompatibility

/-!
# Heterarchy — control as a spectrum, not a chain of command

The HAGI reading of the heterarchy paper (arXiv:2610.04643):
functional control relations are CONTEXT-DEPENDENT and may
form CYCLES; a global ranking of modules ("who is the boss")
need not exist. Development hierarchy (experts → student) is
NOT a runtime command hierarchy.

This module adds the heterarchical layer WITHOUT touching the
certified controller (the slow outer loop stands; this is the
fast inner layer):

* `Dominance` — the context-dependent influence relation
  R(c, i, j) > 0: module i constrains module j in context c;
* `no_global_ranking` — THE CONFIGURATION PROOF: if dominance
  reverses across two contexts (A→B in c₁, B→A in c₂), then NO
  linear ranking of modules is consistent with all dominance
  relations — "who is the boss" does not exist as a global
  fact; it exists only per context;
* `cycle_breaks_ranking` — the 3-cycle form (A→B→C→A in any
  contexts): the paper's cycle criterion, formalized;
* `disagreement_survives_configs` — THE MERGE ANSWER: the
  cancellation pair (d, −d) has ZERO mean (MergeCancellation:
  averaging destroys it) but NONZERO retained configuration
  energy — the answer to the γ 9x deficit is not better
  averaging but NOT averaging: Integrate = (cortex, fibers,
  context graph), the disagreement becomes a switchable
  resource.
-/

namespace Hagi

open Finset

/-! ## The context-dependent dominance relation -/

variable {C M : Type}

/-- `dominates R c i j`: in context c, module i constrains
module j (positive influence). -/
def dominates (R : C → M → M → ℝ) (c : C) (i j : M) : Prop :=
  0 < R c i j

/-- A linear ranking r is consistent with the dominance
relation if every positive dominance forces a strict rank
drop: the "chain of command" hypothesis. -/
def RankingConsistent (R : C → M → M → ℝ) (r : M → ℝ) : Prop :=
  ∀ c i j, dominates R c i j → r i > r j

/-- **The configuration proof**: reversed dominance across two
contexts kills EVERY linear ranking — control is a spectrum
per context, not a global chain of command. -/
theorem no_global_ranking (R : C → M → M → ℝ) (c₁ c₂ : C) (a b : M)
    (hab : dominates R c₁ a b) (hba : dominates R c₂ b a)
    (r : M → ℝ) : ¬ RankingConsistent R r := by
  intro hcons
  have h1 : r a > r b := hcons c₁ a b hab
  have h2 : r b > r a := hcons c₂ b a hba
  exact absurd h1 (not_lt.2 (le_of_lt h2))

/-- **The cycle criterion (the paper's formal test)**: a
3-cycle of dominance (in possibly different contexts) breaks
every ranking — local chains of command do not compose into a
global order. -/
theorem cycle_breaks_ranking (R : C → M → M → ℝ)
    (c₁ c₂ c₃ : C) (a b c : M)
    (hab : dominates R c₁ a b)
    (hbc : dominates R c₂ b c)
    (hca : dominates R c₃ c a)
    (r : M → ℝ) : ¬ RankingConsistent R r := by
  intro hcons
  have h1 : r a > r b := hcons c₁ a b hab
  have h2 : r b > r c := hcons c₂ b c hbc
  have h3 : r c > r a := hcons c₃ c a hca
  linarith

/-! ## Merge answer: disagreement as a switchable resource -/

variable {X : Type} [NormedAddCommGroup X]

/-- **The γ-deficit answer**: a cancellation pair (d, −d) has
exactly ZERO mean — averaging destroys the disagreement
(MergeCancellation, restated as the failure mode) — while the
CONFIGURATION view (keep both) retains the full signal energy
2·‖d‖²: disagreement is not noise to average away but a
switchable resource to index. -/
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
