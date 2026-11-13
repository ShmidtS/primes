/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Research.SchellingCandidateSelection
import Hagi.Research.MarkovPercolation

/-! Structural admission to exact Markov history support, with independent walk
horizons and no endpoint-marginal, common-hitting-time, or quality claim. -/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.SchellingMarkovRouting

open Hagi.Contracts.SchellingCandidateSelection Hagi.Optimization.MarkovPercolation
open Hagi.Probability Hagi.Unified.ParetoExecution

open Classical in
/-- A selected decorated-feasible candidate needs only one-way support for
its kernel; structural admission and reachability remain unchanged. -/
theorem walkHistory_support_of_mem_feasible_withStructuralConstraint_of_adjSupported
    {A : Type} {Γ V : Type*} [Fintype A] [Fintype V]
    (p : ControllerProblem A Γ)
    (graphOf : A → SimpleGraph V) (compatibility : V → V → ℝ)
    (k : ℕ) (top bottom : V → Prop) (K : V → PMF V)
    {M C : ℕ} {a : A}
    (hK : adjSupportedRoutingKernel (graphOf a) K)
    (ha : a ∈ feasible
      (withStructuralConstraint p graphOf compatibility k top bottom) M C) :
    ∀ s, top s → ∃ (t : V) (w : (graphOf a).Walk s t), bottom t ∧
      walkHistory w ∈ (historyLaw (PMF.pure s) (fun _ => K)
        w.length w.length).support := by
  have hstructural := (mem_feasible_withStructuralConstraint p graphOf compatibility
    k top bottom M C a).mp ha |>.2
  intro s hs
  obtain ⟨t, ht, ⟨w⟩⟩ := hstructural.2 s hs
  exact ⟨t, w, ht,
    historyLaw_walk_support_of_adjSupported (graphOf a) K hK w (by simp)⟩

open Classical in
/-- Decorated-feasible diagonal routing gives an exact supported bottom-walk history. -/
theorem walkHistory_support_of_mem_feasible_withStructuralConstraint
    {A : Type} {Γ V : Type*} [Fintype A] [Fintype V]
    (p : ControllerProblem A Γ)
    (graphOf : A → SimpleGraph V) (compatibility : V → V → ℝ)
    (k : ℕ) (top bottom : V → Prop) (K : A → V → PMF V)
    {M C : ℕ}
    (hK : ∀ a, a ∈ feasible
      (withStructuralConstraint p graphOf compatibility k top bottom) M C →
      supportedRoutingKernel (graphOf a) (K a))
    {a : A}
    (ha : a ∈ feasible
      (withStructuralConstraint p graphOf compatibility k top bottom) M C) :
    ∀ s, top s → ∃ (t : V) (w : (graphOf a).Walk s t), bottom t ∧
      walkHistory w ∈ (historyLaw (PMF.pure s) (fun _ => K a)
        w.length w.length).support := by
  exact walkHistory_support_of_mem_feasible_withStructuralConstraint_of_adjSupported
    p graphOf compatibility k top bottom (K a)
    (adjSupportedRoutingKernel_of_supportedRoutingKernel (graphOf a) (K a) (hK a ha)) ha

end Hagi.Contracts.SchellingMarkovRouting
