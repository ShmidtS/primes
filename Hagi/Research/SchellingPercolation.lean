/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Research.Schelling
import Hagi.Research.Site

/-!
# Exact finite bridge between local compatibility and site percolation

Edge addition preserves the filtered compatible-neighbor cardinal, but local
satisfaction is preserved only with the explicit old non-vacuous-count premise
`k ≤ G.degree v`: the quota `min k degree` can grow with the graph.

On `paritySeed`, threshold 1 has exactly two diagonal open cells. Direct finite
computation shows that the open graph is edgeless, every cell is locally
satisfied at `k = 1`, and the existing no-crossing theorem applies. At
threshold 2 the existing crossing witness applies, while constant negative
compatibility makes every cell unsatisfied. Constant positive compatibility is
a separate chosen local datum under which every cell is satisfied. Nothing here
is a critical-point, asymptotic-component, learning, or model-quality result.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Optimization.SchellingPercolation

open Hagi.Optimization.Schelling Hagi.Percolation

universe u

variable {Vertex : Type u}

open Classical in
/-- Adding edges preserves every old compatible actual neighbor. -/
theorem localCompatibleDegree_mono (G G' : SimpleGraph Vertex)
    (compatibility : Vertex → Vertex → ℝ) (k : ℕ) (v : Vertex)
    [Fintype (G.neighborSet v)] [Fintype (G'.neighborSet v)] (hGG' : G ≤ G') :
    localCompatibleDegree G compatibility k v ≤
      localCompatibleDegree G' compatibility k v := by
  change (((G.neighborFinset v).filter fun w =>
    (k : ℝ) ≤ compatibility v w).card : ENNReal) ≤
      (((G'.neighborFinset v).filter fun w =>
        (k : ℝ) ≤ compatibility v w).card : ENNReal)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro w hw
  rw [SimpleGraph.mem_neighborFinset] at hw ⊢
  exact hGG' hw

open Classical in
/-- With a non-vacuous old quota, local satisfaction survives edge addition.
Both minima equal `k`; this is not an unconditional monotonicity theorem. -/
theorem locallySatisfied_mono_of_le (G G' : SimpleGraph Vertex)
    (compatibility : Vertex → Vertex → ℝ) (k : ℕ) (v : Vertex)
    [Fintype (G.neighborSet v)] [Fintype (G'.neighborSet v)]
    (hGG' : G ≤ G') (hk : k ≤ G.degree v)
    (hs : locallySatisfied G compatibility k v) :
    locallySatisfied G' compatibility k v := by
  have hk' : k ≤ G'.degree v :=
    hk.trans (SimpleGraph.degree_le_of_le hGG')
  have hmin : min k (G.degree v) = k := Nat.min_eq_left hk
  have hmin' : min k (G'.degree v) = k := Nat.min_eq_left hk'
  simp only [locallySatisfied, hmin] at hs
  simp only [locallySatisfied, hmin']
  exact hs.trans (localCompatibleDegree_mono G G' compatibility k v hGG')

open Classical in
/-- At threshold 1 exactly the two diagonal cells are open. -/
private theorem parity_open1 (c : Hagi.Percolation.V 2) :
    openAt 1 paritySeed c ↔ c = (0, 0) ∨ c = (1, 1) := by
  fin_cases c <;> norm_num [openAt, paritySeed, seedParity]

open Classical in
/-- At threshold 1 every cell is isolated: the only open cells are diagonal. -/
private theorem parity_isolated1 (c : Hagi.Percolation.V 2) :
    (openGraph (openAt 1 paritySeed)).IsIsolated c := by
  intro w hAdj
  fin_cases c <;> fin_cases w <;>
    norm_num [openGraph, openAt, paritySeed, seedParity, cellAdj, step] at hAdj

open Classical in
/-- At threshold 2 every cell has a horizontal neighbor in the open graph. -/
private theorem parity_degree_pos2 (c : Hagi.Percolation.V 2) :
    0 < (openGraph (openAt 2 paritySeed)).degree c := by
  rw [SimpleGraph.degree_pos_iff_exists_adj]
  fin_cases c
  · exact ⟨(0, 1), by
      norm_num [openGraph, cellAdj, step, openAt, paritySeed, seedParity]⟩
  · exact ⟨(0, 0), by
      norm_num [openGraph, cellAdj, step, openAt, paritySeed, seedParity]⟩
  · exact ⟨(1, 1), by
      norm_num [openGraph, cellAdj, step, openAt, paritySeed, seedParity]⟩
  · exact ⟨(1, 0), by
      norm_num [openGraph, cellAdj, step, openAt, paritySeed, seedParity]⟩

open Classical in
/-- The `k = 1` compatible-neighbor cardinal vanishes for constant `-1`. -/
private theorem parity_negative2 (c : Hagi.Percolation.V 2) :
    ¬ locallySatisfied (openGraph (openAt 2 paritySeed))
      (fun _ _ => (-1 : ℝ)) 1 c := by
  have hdegree := parity_degree_pos2 c
  have hmin : min 1 ((openGraph (openAt 2 paritySeed)).degree c) = 1 :=
    Nat.min_eq_left hdegree
  have hcount : localCompatibleDegree (openGraph (openAt 2 paritySeed))
      (fun _ _ => (-1 : ℝ)) 1 c = 0 := by
    norm_num [localCompatibleDegree]
  intro hs
  simp only [locallySatisfied, hmin, hcount] at hs
  norm_num at hs

open Classical in
/-- The chosen constant `+1` compatibility admits every actual q2 neighbor. -/
private theorem parity_positive2 (c : Hagi.Percolation.V 2) :
    locallySatisfied (openGraph (openAt 2 paritySeed))
      (fun _ _ => (1 : ℝ)) 1 c := by
  have hcount : localCompatibleDegree (openGraph (openAt 2 paritySeed))
      (fun _ _ => (1 : ℝ)) 1 c =
        ((openGraph (openAt 2 paritySeed)).degree c : ENNReal) := by
    norm_num [localCompatibleDegree]
  simp only [locallySatisfied, hcount]
  exact Nat.cast_le.mpr (Nat.min_le_right _ _)

open Classical in
/-- Exact q1 boundary: isolation approves every cell locally but gives no
crossing. The local statement is computed from isolation, not the other way. -/
theorem parity_boundary1 :
    (∀ c, openAt 1 paritySeed c ↔ c = (0, 0) ∨ c = (1, 1)) ∧
      (∀ c, (openGraph (openAt 1 paritySeed)).IsIsolated c) ∧
      (∀ c, locallySatisfied (openGraph (openAt 1 paritySeed))
        (fun _ _ => (-1 : ℝ)) 1 c) ∧
      ¬ crossing rowTop rowBot 1 paritySeed := by
  refine ⟨parity_open1, parity_isolated1, ?_, parity_not_crossing1⟩
  intro c
  exact locallySatisfied_isolated _ _ _ _ (parity_isolated1 c)

open Classical in
/-- Exact q2 positive connectivity and local sign fixtures. Together with the
q1 local-satisfaction component of `parity_boundary1`, the negative q2 component,
refute unconditional local-satisfaction preservation under graph inclusion. -/
theorem parity_threshold2 :
    openGraph (openAt 1 paritySeed) ≤ openGraph (openAt 2 paritySeed) ∧
      crossing rowTop rowBot 2 paritySeed ∧
      (∀ c, ¬ locallySatisfied (openGraph (openAt 2 paritySeed))
        (fun _ _ => (-1 : ℝ)) 1 c) ∧
      (∀ c, locallySatisfied (openGraph (openAt 2 paritySeed))
        (fun _ _ => (1 : ℝ)) 1 c) := by
  refine ⟨?_, parity_crossing2, parity_negative2, parity_positive2⟩
  intro x y hxy
  have hle : (1 : ℕ) ≤ 2 := by omega
  exact ⟨hxy.1, Nat.lt_of_lt_of_le hxy.2.1 hle,
    Nat.lt_of_lt_of_le hxy.2.2 hle⟩

end Hagi.Optimization.SchellingPercolation
