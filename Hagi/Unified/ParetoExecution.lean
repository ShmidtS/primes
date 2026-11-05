/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.SelfDevelopment
import Hagi.Model.StageSemantics
set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Cycle 70 — finite constrained Pareto execution controller

A well-specified FINITE policy over an explicitly supplied family of
candidate actions: maximize an objective subject to a model-safety
predicate and separate memory / operation-count budget caps, using the
ACTUAL successor function `step : A → S → S` of the mathematical model
(no synthesized "desired effects" records are executed).

Design (plan `cycle70-controller.md`, alternative 3):

* `feasible` reuses `Hagi.Growth.safeCandidates` on
  `safe a ∧ memory a ≤ M ∧ operations a ≤ C`.
* `score` is a nested Mathlib `Prod.Lex` maximum
  `(value (step a s), −memory, −operations)`: quality has lexicographic
  priority, and smaller resources win quality ties WITHOUT arbitrary
  scalarization weights.
* `selection` is a `Classical.choose` witness of `Finset.exists_max_image`
  over the nonempty feasible set; `selectedNext` is its actual successor.

Exact domain limits:

* Non-domination (`selection_pareto`) holds WITHIN the finite supplied
  feasible family only — not over all possible architectures, and not as
  automatic optimality on actual tasks.
* `value`, `memory`, `operations` are declared MODEL objectives and
  model units supplied with the problem, not physical measurements
  (no hardware/IEEE/total-size/universal-training claims).
* The selector uses `Classical.choice` and `ℝ`, so it is exact finite
  mathematical selection; no native executable optimizer is certified.
-/

namespace Hagi.Unified.ParetoExecution

open Prod.Lex

variable {A S : Type*}

/-- A finite feasible controller problem over an explicit candidate
family `A` and state space `S`. All fields are model-level data
declared with the problem (objectives/units), not measurements. -/
structure ControllerProblem (A S : Type*) where
  /-- Model objective to maximize (higher is better). -/
  value : S → ℝ
  /-- Actual successor function of the model: action, state, next state. -/
  step : A → S → S
  /-- Memory cost of an action, in model units. -/
  memory : A → ℕ
  /-- Operation-count cost of an action, in model units. -/
  operations : A → ℕ
  /-- Model-safety predicate (conditional on its model, not physical
  safety). -/
  safe : A → Prop

section Finite

variable {A : Type} {S : Type*} [Fintype A] {s : S}

@[reducible]
private def feasPred (p : ControllerProblem A S) (M C : ℕ) : A → Prop :=
  fun a => p.safe a ∧ p.memory a ≤ M ∧ p.operations a ≤ C

instance {p : ControllerProblem A S} [DecidablePred p.safe] (M C : ℕ) :
    DecidablePred (feasPred p M C) :=
  fun _ => inferInstance

/-- The finite feasible set: `Hagi.Growth.safeCandidates` on safety plus
memory/operation caps. -/
def feasible (p : ControllerProblem A S) (memoryLimit operationLimit : ℕ)
    [DecidablePred p.safe] : Finset A :=
  Hagi.Growth.safeCandidates (feasPred p memoryLimit operationLimit)

@[simp] theorem mem_feasible {p : ControllerProblem A S} [DecidablePred p.safe]
    {M C : ℕ} {a : A} :
    a ∈ feasible p M C ↔ p.safe a ∧ p.memory a ≤ M ∧ p.operations a ≤ C := by
  simp [feasible, feasPred, Hagi.Growth.safeCandidates]

/-- Lexicographic score: quality first, then SMALLER memory, then
smaller operations. Nonnegative integer resource costs are negated so
that `≤` in the max-lex order prefers cheaper actions, without any
arbitrary scalar weights. -/
def score (p : ControllerProblem A S) (s : S) (a : A) : ℝ ×ₗ (ℤ ×ₗ ℤ) :=
  toLex (p.value (p.step a s), toLex (-(p.memory a : ℤ), -(p.operations a : ℤ)))

/-- Selected action: a `Classical.choose` max-`score` witness over the
nonempty feasible set (exact finite selection via
`Finset.exists_max_image`; noncomputable because `ℝ` scores are not
decidable in general). -/
noncomputable def selection (p : ControllerProblem A S) [DecidablePred p.safe] (s : S) (M C : ℕ)
    (stay : A) (h_stay : stay ∈ feasible p M C) : A :=
  Classical.choose
    (Finset.exists_max_image (feasible p M C) (score p s) ⟨stay, h_stay⟩)

/-- Master specification of the selection: feasibility of the selected
action plus the feasible-set lex maximum property. -/
theorem selection_spec (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) :
    selection p s M C stay h_stay ∈ feasible p M C
      ∧ ∀ a ∈ feasible p M C, score p s a ≤ score p s (selection p s M C stay h_stay) :=
  by
  have h := Classical.choose_spec
    (Finset.exists_max_image (feasible p M C) (score p s) ⟨stay, h_stay⟩)
  exact h

/-- The selected action is feasible (safe and within both resource
caps). -/
theorem selection_admissible (p : ControllerProblem A S) [DecidablePred p.safe] (s : S) (M C : ℕ)
    (stay : A) (h_stay : stay ∈ feasible p M C) :
    selection p s M C stay h_stay ∈ feasible p M C :=
  (selection_spec p s M C stay h_stay).1

/-- The selected action maximizes the lex score over the feasible set. -/
theorem selection_optimal (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) :
    ∀ a ∈ feasible p M C, score p s a ≤ score p s (selection p s M C stay h_stay) :=
  (selection_spec p s M C stay h_stay).2

/-- The actual successor state produced by the selected action. -/
noncomputable def selectedNext (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) : S :=
  p.step (selection p s M C stay h_stay) s

/-- Quality optimality within the feasible family: no feasible action's
actual next state has higher objective than the selected next state. -/
theorem selection_quality_optimal (p : ControllerProblem A S)
    [DecidablePred p.safe] (s : S) (M C : ℕ)
    (stay : A) (h_stay : stay ∈ feasible p M C) :
    ∀ a ∈ feasible p M C,
      p.value (p.step a s) ≤ p.value (selectedNext p s M C stay h_stay) := by
  intro a ha
  exact Prod.Lex.monotone_fst _ _ (selection_optimal p s M C stay h_stay a ha)

/-- If the baseline keeps the state fixed, its quality is met by the
selection. -/
theorem selection_quality_ge_stay (p : ControllerProblem A S)
    [DecidablePred p.safe] (s : S) (M C : ℕ)
    (stay : A) (h_stay : stay ∈ feasible p M C) (hid : p.step stay s = s) :
    p.value s ≤ p.value (selectedNext p s M C stay h_stay) := by
  have h := selection_quality_optimal p s M C stay h_stay stay h_stay
  rwa [hid] at h

/-- Resource caps hold for the selected action (from feasibility). -/
theorem selection_memory_le (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) : p.memory (selection p s M C stay h_stay) ≤ M :=
  (mem_feasible.mp (selection_admissible p s M C stay h_stay)).2.1

/-- Resource caps hold for the selected action (from feasibility). -/
theorem selection_operations_le (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) : p.operations (selection p s M C stay h_stay) ≤ C :=
  (mem_feasible.mp (selection_admissible p s M C stay h_stay)).2.2

/-- **Pareto non-domination within the exact finite feasible set.**
If a feasible competitor matches the selected quality while using no
more memory and no more operations, then all three coordinates are
EQUAL: no feasible action strictly dominates the selection. This is
not a claim about all possible architectures, not a scalarization,
and not automatic optimality on actual tasks. -/
theorem selection_pareto (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) {a : A} (ha : a ∈ feasible p M C)
    (hq : p.value (selectedNext p s M C stay h_stay) ≤ p.value (p.step a s))
    (hm : p.memory a ≤ p.memory (selection p s M C stay h_stay))
    (ho : p.operations a ≤ p.operations (selection p s M C stay h_stay)) :
    p.value (p.step a s) = p.value (selectedNext p s M C stay h_stay)
      ∧ p.memory a = p.memory (selection p s M C stay h_stay)
      ∧ p.operations a = p.operations (selection p s M C stay h_stay) := by
  have hsa : score p s a ≤ score p s (selection p s M C stay h_stay) :=
    selection_optimal p s M C stay h_stay a ha
  have hle1 : p.value (p.step a s) ≤
      p.value (p.step (selection p s M C stay h_stay) s) :=
    Prod.Lex.monotone_fst _ _ hsa
  have hveq : p.value (p.step a s) =
      p.value (p.step (selection p s M C stay h_stay) s) :=
    le_antisymm hle1 hq
  have hlex : p.value (p.step a s) <
      p.value (p.step (selection p s M C stay h_stay) s)
      ∨ (p.value (p.step a s) =
          p.value (p.step (selection p s M C stay h_stay) s)
          ∧ toLex (-(p.memory a : ℤ), -(p.operations a : ℤ))
              ≤ toLex (-(p.memory (selection p s M C stay h_stay) : ℤ),
                  -(p.operations (selection p s M C stay h_stay) : ℤ))) :=
    Prod.Lex.toLex_le_toLex.mp hsa
  rcases hlex with hlt | hval
  · linarith
  · obtain ⟨hval, hinner⟩ := hval
    rcases Prod.Lex.toLex_le_toLex.mp hinner with hlt2 | ⟨heq2, hle2⟩
    · exact absurd hlt2 (by omega)
    · have hmeq : p.memory a = p.memory (selection p s M C stay h_stay) := by
        have hz : (p.memory a : ℤ) = p.memory (selection p s M C stay h_stay) := by
          linarith
        omega
      have hoeq : p.operations a = p.operations (selection p s M C stay h_stay) := by
        have hz : (p.operations a : ℤ) = p.operations (selection p s M C stay h_stay) := by
          have h2 : (p.operations (selection p s M C stay h_stay) : ℤ) ≤ p.operations a := by
            linarith
          have h1 : (p.operations a : ℤ) ≤ p.operations (selection p s M C stay h_stay) := by
            exact_mod_cast ho
          linarith
        omega
      exact ⟨hveq, hmeq, hoeq⟩

/-- **Identity fallback.** If the baseline `stay` is the only feasible
action, the selection is exactly `stay`. -/
theorem selection_fallback (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C)
    (honly : ∀ a, a ≠ stay → a ∉ feasible p M C) :
    selection p s M C stay h_stay = stay := by
  by_contra hne
  exact honly _ hne (selection_admissible p s M C stay h_stay)

/-- On fallback with a state-fixing baseline, the executed successor is
exactly the current state: no alternate effect is executed. -/
theorem next_fallback (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C)
    (honly : ∀ a, a ≠ stay → a ∉ feasible p M C) (hid : p.step stay s = s) :
    selectedNext p s M C stay h_stay = s := by
  rw [selectedNext, selection_fallback p s M C stay h_stay honly, hid]

end Finite

section Stage

variable {A : Type*} {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **Model adapter from fresh stage inputs to actual successors**:
each action's successor is the existing `Hagi.Model.advance` applied to
a per-action fresh `StageInput`. This maps measured per-cycle inputs to
the actual successor function of the model — it is a mathematical
adapter, not hardware execution. -/
def stageFamily (inputs : A → Hagi.Model.StageInput X) :
    A → Hagi.System.GrowthState X → Hagi.System.GrowthState X :=
  fun a S => Hagi.Model.advance S (inputs a)

/-- The adapter's capability ledger comes verbatim from the cycle input:
fresh per-cycle gains, not a copied effects record. -/
theorem stageFamily_capability (inputs : A → Hagi.Model.StageInput X) (a : A)
    (S : Hagi.System.GrowthState X) :
    (stageFamily inputs a S).capability = S.capability + (inputs a).eff.growGain :=
  Hagi.Model.advance_capability S (inputs a)

end Stage

end Hagi.Unified.ParetoExecution
