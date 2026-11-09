/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.FinCases

set_option linter.style.header false
set_option relaxedAutoImplicit false

@[expose] public section
/-!
# Local compatibility on a finite simple graph

Only actual graph neighbors are inspected. Satisfaction requires at least
`min k degree` neighbors whose supplied real compatibility is at least `k`.
This is local graph semantics only: no dynamics, convergence, or model-quality
claim is made.
-/

namespace Hagi.Optimization.Schelling

open Finset

universe u

variable {V : Type u}

open Classical in
/-- The number of actual neighbors whose real compatibility reaches the threshold. -/
noncomputable def localCompatibleDegree (G : SimpleGraph V)
    (compatibility : V → V → ℝ) (k : ℕ) (v : V)
    [Fintype (G.neighborSet v)] : ENNReal :=
  (((G.neighborFinset v).filter fun w => (k : ℝ) ≤ compatibility v w).card : ENNReal)

open Classical in
/-- At least `min k degree` actual neighbors reach the real compatibility threshold `k`. -/
noncomputable def locallySatisfied (G : SimpleGraph V) (compatibility : V → V → ℝ)
    (k : ℕ) (v : V) [Fintype (G.neighborSet v)] : Prop :=
  ((min k (G.degree v) : ℕ) : ENNReal) ≤ localCompatibleDegree G compatibility k v

open Classical in
/-- Filtering actual neighbors cannot increase their finite cardinal. -/
theorem localCompatibleDegree_le_degree (G : SimpleGraph V) (compatibility : V → V → ℝ)
    (k : ℕ) (v : V) [Fintype (G.neighborSet v)] :
    localCompatibleDegree G compatibility k v ≤ (G.degree v : ENNReal) := by
  change (((G.neighborFinset v).filter fun w => (k : ℝ) ≤ compatibility v w).card : ENNReal) ≤
    ((G.neighborFinset v).card : ENNReal)
  exact Nat.cast_le.mpr (card_filter_le _ _)

open Classical in
/-- When the degree is below the requested count, every actual neighbor must qualify. -/
theorem locallySatisfied_iff_forall_of_degree_le (G : SimpleGraph V)
    (compatibility : V → V → ℝ) (k : ℕ) (v : V) [Fintype (G.neighborSet v)]
    (hkv : G.degree v ≤ k) :
    locallySatisfied G compatibility k v ↔
      ∀ w ∈ G.neighborFinset v, (k : ℝ) ≤ compatibility v w := by
  have hmin : min k (G.degree v) = (G.neighborFinset v).card := by
    rw [Nat.min_eq_right hkv, SimpleGraph.card_neighborFinset_eq_degree]
  simp only [locallySatisfied, localCompatibleDegree, hmin]
  rw [Nat.cast_le]
  constructor
  · intro hs
    have heq : ((G.neighborFinset v).filter fun w => (k : ℝ) ≤ compatibility v w).card =
        (G.neighborFinset v).card := Nat.le_antisymm (card_filter_le _ _) hs
    exact card_filter_eq_iff.mp heq
  · intro hall
    rw [card_filter_eq_iff.mpr hall]

open Classical in
/-- A zero requested compatible-neighbor count imposes no local requirement. -/
theorem locallySatisfied_zero (G : SimpleGraph V) (compatibility : V → V → ℝ)
    (v : V) [Fintype (G.neighborSet v)] : locallySatisfied G compatibility 0 v := by
  simp [locallySatisfied]

open Classical in
/-- An isolated vertex is satisfied for every compatibility and threshold. -/
theorem locallySatisfied_isolated (G : SimpleGraph V) (compatibility : V → V → ℝ)
    (k : ℕ) (v : V) [Fintype (G.neighborSet v)] (hv : G.IsIsolated v) :
    locallySatisfied G compatibility k v := by
  have hd : G.degree v = 0 := (G.degree_eq_zero v).mpr hv
  simp [locallySatisfied, hd]

open Classical in
/-- Nonvacuous empty-neighborhood fixture: compatibility is everywhere negative. -/
example : locallySatisfied (⊥ : SimpleGraph (Fin 1)) (fun _ _ => (-1 : ℝ)) 3 0 := by
  apply locallySatisfied_isolated
  simp [SimpleGraph.IsIsolated]

open Classical in
/-- One of two neighbors may miss the cutoff when only one compatible neighbor is required. -/
example :
    locallySatisfied (SimpleGraph.edge (0 : Fin 3) 1 ⊔ SimpleGraph.edge 0 2)
      (fun _ w => if w = 1 then 2 else 0) 1 0 := by
  have hn : (SimpleGraph.edge (0 : Fin 3) 1 ⊔ SimpleGraph.edge 0 2).neighborFinset 0 =
      {1, 2} := by
    ext w
    fin_cases w <;> norm_num [SimpleGraph.mem_neighborFinset,
      SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  norm_num [locallySatisfied, localCompatibleDegree, SimpleGraph.degree, hn,
    Finset.filter_insert, Finset.filter_singleton]

open Classical in
/-- Requiring two qualifying neighbors fails when exactly one of two qualifies. -/
example :
    ¬ locallySatisfied (SimpleGraph.edge (0 : Fin 3) 1 ⊔ SimpleGraph.edge 0 2)
      (fun _ w => if w = 1 then 2 else 0) 2 0 := by
  have hn : (SimpleGraph.edge (0 : Fin 3) 1 ⊔ SimpleGraph.edge 0 2).neighborFinset 0 =
      {1, 2} := by
    ext w
    fin_cases w <;> norm_num [SimpleGraph.mem_neighborFinset,
      SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  norm_num [locallySatisfied, localCompatibleDegree, SimpleGraph.degree, hn,
    Finset.filter_insert, Finset.filter_singleton]

open Classical in
/-- The two disjoint edges used only by the negative semantic witness. -/
def disconnectedGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.edge 0 1 ⊔ SimpleGraph.edge 2 3

open Classical in
/-- Local satisfaction everywhere does not imply reachability or preconnectedness. -/
theorem locallySatisfied_disconnected :
    let compatibility : Fin 4 → Fin 4 → ℝ := fun v w =>
      if v.val % 2 = w.val % 2 then 0 else 1
    (∀ v, locallySatisfied disconnectedGraph compatibility 1 v) ∧
      ¬ disconnectedGraph.Reachable 0 2 ∧ ¬ disconnectedGraph.Preconnected := by
  dsimp only
  have hn {v : Fin 4} : disconnectedGraph.neighborFinset v =
      {if v = 0 then 1 else if v = 1 then 0 else if v = 2 then 3 else 2} := by
    ext w
    fin_cases v <;> fin_cases w <;> norm_num [disconnectedGraph,
      SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  constructor
  · intro v
    fin_cases v <;> norm_num [locallySatisfied, localCompatibleDegree,
      SimpleGraph.degree, hn, Finset.filter_insert, Finset.filter_singleton]
  · have component_invariant {u v : Fin 4} (walk : disconnectedGraph.Walk u v) :
        u.val / 2 = v.val / 2 := by
      induction walk with
      | nil => rfl
      | @cons u x v hadj walk ih =>
          have hux : u.val / 2 = x.val / 2 := by
            simp only [disconnectedGraph, SimpleGraph.sup_adj,
              SimpleGraph.edge_adj] at hadj
            rcases hadj with h | h
            · rcases h with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _hne⟩ <;> norm_num
            · rcases h with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _hne⟩ <;> norm_num
          exact hux.trans ih
    have hnot : ¬ disconnectedGraph.Reachable 0 2 := by
      rintro ⟨walk⟩
      have h := component_invariant walk
      norm_num at h
    exact ⟨hnot, fun hpreconnected => hnot (hpreconnected 0 2)⟩

end Hagi.Optimization.Schelling
