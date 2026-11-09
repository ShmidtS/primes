/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Optimization.SchellingPercolation
import Hagi.Unified.GuardedRobustResourceMin

/-!
# Bounded structural admission for finite candidate controllers

A constrained view retains the supplied controller's quality, successor,
declared resources, and model safety, and additionally requires local graph
compatibility and a route from every top vertex to some bottom vertex.
Feasibility and guarded resource selection remain those of the existing
finite providers. The graph predicates are finite structural conditions,
not physical-safety, task-quality, or percolation-probability claims.
-/

namespace Hagi.Contracts.SchellingCandidateSelection

open Hagi.Optimization.Schelling Hagi.Unified.ParetoExecution

universe u

open Classical in
/-- Every vertex meets its local compatible-neighbor quota, and every top
vertex can reach some bottom vertex in the same supplied finite graph. -/
def structuralConstraint {V : Type u} [Fintype V] (G : SimpleGraph V)
    (compatibility : V → V → ℝ) (k : ℕ) (top bottom : V → Prop) : Prop :=
  (∀ v, locallySatisfied G compatibility k v) ∧
    ∀ s, top s → ∃ t, bottom t ∧ G.Reachable s t

open Classical in
/-- Constrain an existing controller by an action-dependent graph while
preserving its value, step, memory, operations, and original model safety. -/
def withStructuralConstraint {A : Type} {Γ V : Type*} [Fintype V]
    (p : ControllerProblem A Γ) (graphOf : A → SimpleGraph V)
    (compatibility : V → V → ℝ) (k : ℕ) (top bottom : V → Prop) :
    ControllerProblem A Γ where
  value := p.value
  step := p.step
  memory := p.memory
  operations := p.operations
  safe := fun a => p.safe a ∧
    structuralConstraint (graphOf a) compatibility k top bottom

open Classical in
/-- Structural admission is exactly original feasibility together with the
candidate's own graph constraint; neither original safety nor either cap is
weakened or hidden by the structural predicate. -/
theorem mem_feasible_withStructuralConstraint
    {A : Type} {Γ V : Type*} [Fintype V] [Fintype A]
    (p : ControllerProblem A Γ) [DecidablePred p.safe]
    (graphOf : A → SimpleGraph V) (compatibility : V → V → ℝ) (k : ℕ)
    (top bottom : V → Prop) (M C : ℕ) (a : A) :
    a ∈ feasible (withStructuralConstraint p graphOf compatibility k top bottom) M C ↔
      a ∈ feasible p M C ∧
        structuralConstraint (graphOf a) compatibility k top bottom := by
  rw [mem_feasible, mem_feasible]
  constructor
  · rintro ⟨⟨hsafe, hstructural⟩, hmemory, hoperations⟩
    exact ⟨⟨hsafe, hmemory, hoperations⟩, hstructural⟩
  · rintro ⟨⟨hsafe, hmemory, hoperations⟩, hstructural⟩
    exact ⟨⟨hsafe, hstructural⟩, hmemory, hoperations⟩

end Hagi.Contracts.SchellingCandidateSelection
