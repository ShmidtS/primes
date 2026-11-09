/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Optimization.SchellingPercolation
import Hagi.Probability.MarkovPathSupport

/-!
# Positive support of graph walks under Markov routing

This isolated candidate adapts Mathlib `SimpleGraph.Walk.getVert` to the
existing finite `historyLaw`.  A supplied walk gives a positive-mass exact
vertex history, not an endpoint-hitting or common-horizon statement.  The
existential `Hagi.Percolation.crossing` is consumed only at its supplied pair;
universal top starts require a separate explicit reachability premise.

The normalized neighbor kernel uses Hagi's PMF-valued `uniformOfFinset`, not
Mathlib's same-named measure-valued construction.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Optimization.MarkovPercolation

open Hagi.Percolation Hagi.Probability
open Hagi.Probability.MarkovPathSupport

universe u

variable {V : Type u}

/-- A normalized routing kernel has support exactly on actual graph edges. -/
def supportedRoutingKernel (G : SimpleGraph V) (K : V → PMF V) : Prop :=
  ∀ a b, b ∈ (K a).support ↔ G.Adj a b

/-- The finite vertex history of a supplied graph walk. -/
def walkHistory {G : SimpleGraph V} {u v : V} (w : G.Walk u v) :
    History V w.length := fun i => w.getVert i.val

@[simp] theorem walkHistory_zero {G : SimpleGraph V} {u v : V} (w : G.Walk u v) :
    walkHistory w (historyIndex w.length 0) = u := by
  simp [walkHistory, historyIndex]

@[simp] theorem walkHistory_last {G : SimpleGraph V} {u v : V} (w : G.Walk u v) :
    walkHistory w (historyIndex w.length w.length) = v := by
  simp [walkHistory, historyIndex]

/-- Any graph walk is a supported full history for the homogeneous supported
routing kernel and any initial law supporting its first vertex. -/
theorem historyLaw_walk_support (G : SimpleGraph V) (K : V → PMF V)
    (hK : supportedRoutingKernel G K) {u v : V} (w : G.Walk u v)
    {initial : PMF V} (hu : u ∈ initial.support) :
    walkHistory w ∈
      (historyLaw initial (fun _ => K) w.length w.length).support := by
  apply historyLaw_full_support
  · simpa [walkHistory, historyIndex] using hu
  · intro j hj
    simp only [walkHistory, historyIndex_val, Nat.min_eq_left hj.le,
      Nat.min_eq_left (by omega : j + 1 ≤ w.length)]
    exact (hK _ _).mpr (w.adj_getVert_succ hj)

/-- Positive point-mass form of `historyLaw_walk_support`. -/
theorem historyLaw_walk_apply_pos (G : SimpleGraph V) (K : V → PMF V)
    (hK : supportedRoutingKernel G K) {u v : V} (w : G.Walk u v)
    {initial : PMF V} (hu : u ∈ initial.support) :
    0 < historyLaw initial (fun _ => K) w.length w.length (walkHistory w) :=
  (PMF.apply_pos_iff _ _).mpr (historyLaw_walk_support G K hK w hu)

/-- The existing existential crossing supplies a pair and a walk whose exact
history is supported from a pure start. -/
theorem exists_walk_history_support_of_crossing {L M : ℕ}
    {top bottom : Hagi.Percolation.V L → Prop} {qv : ℕ} {ω : Hagi.Percolation.V L → Fin M}
    {K : Hagi.Percolation.V L → PMF (Hagi.Percolation.V L)}
    (hK : supportedRoutingKernel (openGraph (openAt qv ω)) K)
    (hcross : crossing top bottom qv ω) :
    ∃ (a b : Hagi.Percolation.V L) (w : (openGraph (openAt qv ω)).Walk a b),
      top a ∧ bottom b ∧
        walkHistory w ∈
          (historyLaw (PMF.pure a) (fun _ => K) w.length w.length).support := by
  obtain ⟨a, b, ha, hb, ⟨w⟩⟩ := hcross
  exact ⟨a, b, w, ha, hb, historyLaw_walk_support _ _ hK w (by simp)⟩

/-- Universal top starts are available only from an explicit universal
reachability premise.  Different walks retain their independent horizons. -/
theorem exists_walk_history_support_of_forall_top {L M : ℕ}
    {top bottom : Hagi.Percolation.V L → Prop} {qv : ℕ} {ω : Hagi.Percolation.V L → Fin M}
    {K : Hagi.Percolation.V L → PMF (Hagi.Percolation.V L)}
    (hK : supportedRoutingKernel (openGraph (openAt qv ω)) K)
    (hreach : ∀ a, top a →
      ∃ b, bottom b ∧ (openGraph (openAt qv ω)).Reachable a b) :
    ∀ a, top a →
      ∃ (b : Hagi.Percolation.V L) (w : (openGraph (openAt qv ω)).Walk a b), bottom b ∧
        walkHistory w ∈
          (historyLaw (PMF.pure a) (fun _ => K) w.length w.length).support := by
  intro a ha
  obtain ⟨b, hb, ⟨w⟩⟩ := hreach a ha
  exact ⟨b, w, hb, historyLaw_walk_support _ _ hK w (by simp)⟩

open Classical in
/-- Uniform normalized routing on a supplied nonempty neighbor finset. -/
noncomputable def uniformNeighborKernel [Fintype V] (G : SimpleGraph V)
    [SimpleGraph.LocallyFinite G]
    (hne : ∀ v, (G.neighborFinset v).Nonempty) : V → PMF V := by
  classical
  exact fun v => Hagi.Probability.PMF.uniformOfFinset (G.neighborFinset v) (hne v)

/-- Uniform nonempty-neighbor routing has exactly the graph edges as support;
in particular, self-pairs and other nonedges are excluded. -/
theorem uniformNeighborKernel_support [Fintype V] (G : SimpleGraph V)
    [SimpleGraph.LocallyFinite G]
    (hne : ∀ v, (G.neighborFinset v).Nonempty) :
    supportedRoutingKernel G (uniformNeighborKernel G hne) := by
  classical
  intro a b
  constructor
  · intro hb
    have hmem : b ∈ G.neighborFinset a := by
      by_contra hnot
      rw [PMF.mem_support_iff, uniformNeighborKernel,
        Hagi.Probability.PMF.uniformOfFinset_apply, ite_eq_right hnot] at hb
      exact hb rfl
    exact (G.mem_neighborFinset a b).mp hmem
  · intro hab
    have hmem : b ∈ G.neighborFinset a := (G.mem_neighborFinset a b).mpr hab
    rw [PMF.mem_support_iff, uniformNeighborKernel,
      Hagi.Probability.PMF.uniformOfFinset_apply, ite_eq_left hmem]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

end Hagi.Optimization.MarkovPercolation
