/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.RankedStopRouting

/-!
# Shortest-distance normalized ranked-stop routing

For a finite graph in which every vertex has a walk to a fixed target, uniform
normalized routing over strictly shorter-distance neighbors gives strict rank
progress.  The canonical ranked-stop theorem then gives mass one for target
hitting by the common vertex-cardinal cutoff.  Every supported nonterminal
step decrements the exact graph distance by one.

The target row is a pure temporal stop, not a graph self-edge.  Unreachable
non-target vertices have no default routing row; universal reachability is an
explicit premise of the total kernel.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Optimization.GraphDistanceRouting

open Hagi.Probability
open Hagi.Probability.RankedStopRouting

universe u

variable {V : Type u}

open Classical in
noncomputable def shorterNeighborFinset [Fintype V] (G : SimpleGraph V)
    (target v : V) : Finset V :=
  (G.neighborFinset v).filter fun b => G.dist b target < G.dist v target

@[simp] theorem mem_shorterNeighborFinset [Fintype V]
    (G : SimpleGraph V) (target v b : V) :
    b ∈ shorterNeighborFinset G target v ↔
      G.Adj v b ∧ G.dist b target < G.dist v target := by
  classical
  simp [shorterNeighborFinset, SimpleGraph.mem_neighborFinset]

theorem exists_adj_dist_add_one_le {G : SimpleGraph V} {v target : V}
    (hr : G.Reachable v target) (hv : v ≠ target) :
    ∃ b, G.Adj v b ∧ G.dist b target + 1 ≤ G.dist v target := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  cases p with
  | nil => exact (hv rfl).elim
  | cons hadj q =>
      refine ⟨_, hadj, ?_⟩
      have hq := G.dist_le q
      simp only [SimpleGraph.Walk.length_cons] at hp
      omega

theorem dist_lt_card [Fintype V] (G : SimpleGraph V)
    {v target : V} (hr : G.Reachable v target) :
    G.dist v target < Fintype.card V := by
  obtain ⟨p, hp, hlen⟩ := hr.exists_path_of_dist
  rw [← hlen]
  exact hp.length_lt

open Classical in
theorem shorterNeighborFinset_nonempty [Fintype V]
    (G : SimpleGraph V) (target : V)
    (hreach : ∀ v, G.Reachable v target) {v : V} (hv : v ≠ target) :
    (shorterNeighborFinset G target v).Nonempty := by
  obtain ⟨b, hadj, hd⟩ := exists_adj_dist_add_one_le (hreach v) hv
  exact ⟨b, (mem_shorterNeighborFinset G target v b).mpr ⟨hadj, by omega⟩⟩

open Classical in
theorem shorterNeighborFinset_eq_empty_of_not_reachable [Fintype V]
    (G : SimpleGraph V) {target v : V} (hr : ¬ G.Reachable v target) :
    shorterNeighborFinset G target v = ∅ := by
  simp [shorterNeighborFinset, SimpleGraph.dist_eq_zero_of_not_reachable hr]

noncomputable def targetRank [Fintype V] (G : SimpleGraph V)
    (target v : V) : ℕ :=
  Fintype.card V - G.dist v target

open Classical in
noncomputable def shortestToTargetKernel [Fintype V]
    (G : SimpleGraph V) (target : V)
    (hreach : ∀ v, G.Reachable v target) : ℕ → V → PMF V :=
  fun _ v => if hv : v = target then PMF.pure target else
    Hagi.Probability.PMF.uniformOfFinset (shorterNeighborFinset G target v)
      (shorterNeighborFinset_nonempty G target hreach hv)

@[simp] theorem shortestToTargetKernel_target [Fintype V]
    (G : SimpleGraph V) (target : V)
    (hreach : ∀ v, G.Reachable v target) (t : ℕ) :
    shortestToTargetKernel G target hreach t target = PMF.pure target := by
  simp [shortestToTargetKernel]

theorem mem_shortestToTargetKernel_support [Fintype V]
    (G : SimpleGraph V) (target : V)
    (hreach : ∀ v, G.Reachable v target) {v : V} (hv : v ≠ target)
    (t : ℕ) (b : V) :
    b ∈ (shortestToTargetKernel G target hreach t v).support ↔
      b ∈ shorterNeighborFinset G target v := by
  classical
  rw [shortestToTargetKernel, dite_eq_right hv]
  constructor
  · intro hb
    by_contra hnot
    rw [PMF.mem_support_iff, Hagi.Probability.PMF.uniformOfFinset_apply,
      ite_eq_right hnot] at hb
    exact hb rfl
  · intro hb
    rw [PMF.mem_support_iff, Hagi.Probability.PMF.uniformOfFinset_apply,
      ite_eq_left hb]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem targetRank_strictMono [Fintype V] (G : SimpleGraph V)
    {target v b : V} (hr : G.Reachable v target)
    (hd : G.dist b target < G.dist v target) :
    targetRank G target v < targetRank G target b := by
  have hcard := dist_lt_card G hr
  simp only [targetRank]
  omega

@[simp] theorem targetRank_target [Fintype V] (G : SimpleGraph V) (target : V) :
    targetRank G target target = Fintype.card V := by
  simp [targetRank]

theorem eq_target_of_targetRank_eq_card [Fintype V]
    (G : SimpleGraph V) (target : V)
    (hreach : ∀ v, G.Reachable v target) {v : V}
    (hv : targetRank G target v = Fintype.card V) : v = target := by
  by_contra hne
  have hpos := (hreach v).pos_dist_of_ne hne
  have hcard := dist_lt_card G (hreach v)
  simp only [targetRank] at hv
  omega

theorem dist_add_one_eq_of_mem_support [Fintype V]
    (G : SimpleGraph V) (target : V)
    (hreach : ∀ v, G.Reachable v target) {v : V} (hv : v ≠ target)
    {t : ℕ} {b : V}
    (hb : b ∈ (shortestToTargetKernel G target hreach t v).support) :
    G.dist b target + 1 = G.dist v target := by
  have hmem := (mem_shortestToTargetKernel_support G target hreach hv t b).mp hb
  obtain ⟨hadj, hd⟩ := (mem_shorterNeighborFinset G target v b).mp hmem
  have htri := hadj.reachable.dist_triangle_left target
  have hone : G.dist v b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  omega

theorem historyLaw_shortestToTarget_hitBy_card_eq_one [Fintype V]
    (G : SimpleGraph V) (target : V)
    (hreach : ∀ v, G.Reachable v target) (initial : PMF V)
    {T : ℕ} (hT : Fintype.card V ≤ T) :
    (historyLaw initial (shortestToTargetKernel G target hreach) T T).toOuterMeasure
      {ω | ∃ j ≤ Fintype.card V, ω (historyIndex T j) = target} = 1 := by
  apply historyLaw_ranked_hitBy_eq_one initial
    (shortestToTargetKernel G target hreach) G.Adj (fun v => v = target)
    (targetRank G target) (Fintype.card V) T hT
  · intro v
    exact Nat.sub_le _ _
  · intro t v hv
    subst v
    exact shortestToTargetKernel_target G target hreach t
  · intro t v hv b hb
    have hmem := (mem_shortestToTargetKernel_support G target hreach hv t b).mp hb
    obtain ⟨hadj, hd⟩ := (mem_shorterNeighborFinset G target v b).mp hmem
    exact ⟨hadj, targetRank_strictMono G (hreach v) hd⟩

/-- Every supported full history first reaches the target after exactly its
initial shortest-path distance, provided the horizon covers that distance. -/
theorem first_target_at_initial_dist_of_historyLaw_support
    [Fintype V] (G : SimpleGraph V) (target : V)
    (hreach : ∀ v, G.Reachable v target) (initial : PMF V)
    {T : ℕ} (hT : ∀ v ∈ initial.support, G.dist v target ≤ T)
    (ω : History V T)
    (hω : ω ∈ (historyLaw initial
      (shortestToTargetKernel G target hreach) T T).support) :
    let D := G.dist (ω (historyIndex T 0)) target
    ω (historyIndex T D) = target ∧
      ∀ j < D, ω (historyIndex T j) ≠ target := by
  dsimp only
  obtain ⟨hstart, hsteps⟩ := start_and_steps_of_historyLaw_support
    initial (shortestToTargetKernel G target hreach) le_rfl ω hω
  have hDT : G.dist (ω (historyIndex T 0)) target ≤ T := hT _ hstart
  have hclock : ∀ j ≤ G.dist (ω (historyIndex T 0)) target,
      G.dist (ω (historyIndex T j)) target + j =
          G.dist (ω (historyIndex T 0)) target ∧
        (j < G.dist (ω (historyIndex T 0)) target →
          ω (historyIndex T j) ≠ target) := by
    intro j
    induction j with
    | zero =>
        intro _
        constructor
        · simp
        · intro hD htarget
          simp [htarget] at hD
    | succ j ih =>
        intro hjD
        have hjlt : j < G.dist (ω (historyIndex T 0)) target := by omega
        have hjT : j < T := by omega
        obtain ⟨hprev, hnone⟩ := ih (by omega)
        have hcur : ω (historyIndex T j) ≠ target := hnone hjlt
        have hnext := hsteps j hjT
        have hdist := dist_add_one_eq_of_mem_support G target hreach hcur hnext
        constructor
        · omega
        · intro _ htarget
          simp only [htarget, SimpleGraph.dist_self] at hdist
          omega
  have hDclock := (hclock _ le_rfl).1
  have hzero : G.dist
      (ω (historyIndex T (G.dist (ω (historyIndex T 0)) target))) target = 0 := by
    omega
  exact ⟨(hreach _).dist_eq_zero_iff.mp hzero,
    fun j hj => (hclock j (by omega)).2 hj⟩

/-- The pure-start exact first-hit event has outer mass one under any
horizon covering that start's shortest-path distance. -/
theorem historyLaw_shortestToTarget_firstHit_dist_eq_one
    [Fintype V] (G : SimpleGraph V) (target : V)
    (hreach : ∀ v, G.Reachable v target) (s : V)
    {T : ℕ} (hT : G.dist s target ≤ T) :
    (historyLaw (PMF.pure s)
      (shortestToTargetKernel G target hreach) T T).toOuterMeasure
      {ω | ω (historyIndex T (G.dist s target)) = target ∧
        ∀ j < G.dist s target,
          ω (historyIndex T j) ≠ target} = 1 := by
  apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
  intro ω hω
  obtain ⟨hstart, _⟩ := start_and_steps_of_historyLaw_support
    (PMF.pure s) (shortestToTargetKernel G target hreach) le_rfl ω hω
  rw [PMF.mem_support_pure_iff] at hstart
  have hT' : ∀ v ∈ (PMF.pure s).support, G.dist v target ≤ T := by
    intro v hv
    rw [PMF.mem_support_pure_iff] at hv
    subst v
    exact hT
  have hfirst := first_target_at_initial_dist_of_historyLaw_support
    G target hreach (PMF.pure s) hT' ω hω
  dsimp only at hfirst
  change ω (historyIndex T (G.dist s target)) = target ∧
    ∀ j < G.dist s target, ω (historyIndex T j) ≠ target
  simpa only [hstart] using hfirst

end Hagi.Optimization.GraphDistanceRouting
