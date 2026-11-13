/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Research.SchellingPercolation
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

/-- Every actual edge is a supported kernel transition.  The converse is
deliberately not asserted: a one-way kernel may put mass on nonedges. -/
def adjSupportedRoutingKernel (G : SimpleGraph V) (K : V → PMF V) : Prop :=
  ∀ a b, G.Adj a b → b ∈ (K a).support

/-- Equality-support supplies the forward direction needed by one-way support. -/
theorem adjSupportedRoutingKernel_of_supportedRoutingKernel
    (G : SimpleGraph V) (K : V → PMF V)
    (hK : supportedRoutingKernel G K) : adjSupportedRoutingKernel G K :=
  fun a b hab => (hK a b).mpr hab

/-- Only transitions actually occurring before the walk endpoint are required.
This is an adapter to the existing full-history theorem, not another induction. -/
theorem historyLaw_walk_support_of_steps (G : SimpleGraph V) (K : ℕ → V → PMF V)
    {u v : V} (w : G.Walk u v) {initial : PMF V}
    (hu : u ∈ initial.support)
    (hsteps : ∀ j < w.length,
      w.getVert (j + 1) ∈ (K j (w.getVert j)).support) :
    walkHistory w ∈
      (historyLaw initial K w.length w.length).support := by
  apply historyLaw_full_support
  · simpa [walkHistory, historyIndex] using hu
  · intro j hj
    simpa only [walkHistory, historyIndex_val, Nat.min_eq_left hj.le,
      Nat.min_eq_left (by omega : j + 1 ≤ w.length)] using hsteps j hj

/-- Any supplied graph walk is supported by a homogeneous one-way kernel. -/
theorem historyLaw_walk_support_of_adjSupported
    (G : SimpleGraph V) (K : V → PMF V)
    (hK : adjSupportedRoutingKernel G K) {u v : V} (w : G.Walk u v)
    {initial : PMF V} (hu : u ∈ initial.support) :
    walkHistory w ∈
      (historyLaw initial (fun _ => K) w.length w.length).support := by
  apply historyLaw_walk_support_of_steps G (fun _ => K) w hu
  intro j hj
  exact hK _ _ (w.adj_getVert_succ hj)

/-- Any graph walk is a supported full history for the homogeneous supported
routing kernel and any initial law supporting its first vertex. -/
theorem historyLaw_walk_support (G : SimpleGraph V) (K : V → PMF V)
    (hK : supportedRoutingKernel G K) {u v : V} (w : G.Walk u v)
    {initial : PMF V} (hu : u ∈ initial.support) :
    walkHistory w ∈
      (historyLaw initial (fun _ => K) w.length w.length).support := by
  exact historyLaw_walk_support_of_adjSupported G K
    (adjSupportedRoutingKernel_of_supportedRoutingKernel G K hK) w hu

/-- Positive point-mass form of `historyLaw_walk_support`. -/
theorem historyLaw_walk_apply_pos (G : SimpleGraph V) (K : V → PMF V)
    (hK : supportedRoutingKernel G K) {u v : V} (w : G.Walk u v)
    {initial : PMF V} (hu : u ∈ initial.support) :
    0 < historyLaw initial (fun _ => K) w.length w.length (walkHistory w) :=
  (PMF.apply_pos_iff _ _).mpr (historyLaw_walk_support G K hK w hu)

/-- The existing existential crossing supplies a pair and a walk whose exact
history is supported from a pure start under the weaker one-way premise. -/
theorem exists_walk_history_support_of_crossing_of_adjSupported {L M : ℕ}
    {top bottom : Hagi.Percolation.V L → Prop} {qv : ℕ} {ω : Hagi.Percolation.V L → Fin M}
    {K : Hagi.Percolation.V L → PMF (Hagi.Percolation.V L)}
    (hK : adjSupportedRoutingKernel (openGraph (openAt qv ω)) K)
    (hcross : crossing top bottom qv ω) :
    ∃ (a b : Hagi.Percolation.V L) (w : (openGraph (openAt qv ω)).Walk a b),
      top a ∧ bottom b ∧
        walkHistory w ∈
          (historyLaw (PMF.pure a) (fun _ => K) w.length w.length).support := by
  obtain ⟨a, b, ha, hb, ⟨w⟩⟩ := hcross
  exact ⟨a, b, w, ha, hb, historyLaw_walk_support_of_adjSupported _ _ hK w (by simp)⟩

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
  exact exists_walk_history_support_of_crossing_of_adjSupported
    (adjSupportedRoutingKernel_of_supportedRoutingKernel _ _ hK) hcross

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

/-- Uniform routing at non-isolated vertices, with a pure row at isolated
vertices.  The latter is row totalization, not a graph self-edge, temporal
terminal stop, or `Option.none` fallback. -/
noncomputable def neighborOrStayKernel [Fintype V] (G : SimpleGraph V)
    [SimpleGraph.LocallyFinite G] : V → PMF V := by
  classical
  exact fun v => if hv : (G.neighborFinset v).Nonempty then
    Hagi.Probability.PMF.uniformOfFinset (G.neighborFinset v) hv
  else PMF.pure v

/-- Adjacency is sufficient for support in the total neighbor-or-stay kernel. -/
theorem neighborOrStayKernel_adjSupported [Fintype V]
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] :
    adjSupportedRoutingKernel G (neighborOrStayKernel G) := by
  classical
  intro a b hab
  have hmem : b ∈ G.neighborFinset a := (G.mem_neighborFinset a b).mpr hab
  have hne : (G.neighborFinset a).Nonempty := ⟨b, hmem⟩
  rw [PMF.mem_support_iff, neighborOrStayKernel, dite_eq_left hne,
    Hagi.Probability.PMF.uniformOfFinset_apply, ite_eq_left hmem]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

/-- At an isolated vertex the actual PMF row is the pure PMF. -/
theorem neighborOrStayKernel_isolated [Fintype V]
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] {a : V}
    (ha : G.IsIsolated a) : neighborOrStayKernel G a = PMF.pure a := by
  classical
  have hne : ¬ (G.neighborFinset a).Nonempty := by
    rintro ⟨b, hb⟩
    exact ha b ((G.mem_neighborFinset a b).mp hb)
  simp [neighborOrStayKernel, hne]

open Hagi.Optimization.Schelling

open Classical in
/-- qv=1: equality-support is impossible at the isolated closed cell, while
the total one-way kernel, its actual pure row and a nil history are available.
The last conjunct separately consumes not-crossing evidence. -/
example :
    ¬ (∃ K, supportedRoutingKernel (openGraph (openAt 1 paritySeed)) K) ∧
    adjSupportedRoutingKernel (openGraph (openAt 1 paritySeed))
      (neighborOrStayKernel (openGraph (openAt 1 paritySeed))) ∧
    neighborOrStayKernel (openGraph (openAt 1 paritySeed)) ((0, 1) : Hagi.Percolation.V 2) =
      PMF.pure ((0, 1) : Hagi.Percolation.V 2) ∧
    (∃ w : (openGraph (openAt 1 paritySeed)).Walk ((0, 1) : Hagi.Percolation.V 2)
        ((0, 1) : Hagi.Percolation.V 2),
      walkHistory w ∈
        (historyLaw (PMF.pure ((0, 1) : Hagi.Percolation.V 2))
          (fun _ => neighborOrStayKernel (openGraph (openAt 1 paritySeed)))
          w.length w.length).support) ∧
    ¬ crossing rowTop rowBot 1 paritySeed := by
  have hclosed : ¬ openAt 1 paritySeed ((0, 1) : Hagi.Percolation.V 2) := by
    norm_num [openAt, paritySeed, Percolation.seedParity]
  have hisolated :
      (openGraph (openAt 1 paritySeed)).IsIsolated ((0, 1) : Hagi.Percolation.V 2) := by
    intro b hab
    exact hclosed hab.2.1
  refine ⟨?_, neighborOrStayKernel_adjSupported _,
    neighborOrStayKernel_isolated _ hisolated, ?_, parity_not_crossing1⟩
  · rintro ⟨K, hK⟩
    obtain ⟨b, hb⟩ := (K ((0, 1) : Hagi.Percolation.V 2)).support_nonempty
    exact hisolated b ((hK _ b).mp hb)
  · refine ⟨SimpleGraph.Walk.nil, ?_⟩
    exact historyLaw_walk_support_of_adjSupported _ _
      (neighborOrStayKernel_adjSupported _) SimpleGraph.Walk.nil (by simp)

open Classical in
/-- qv=2: the explicit finite all-open 2×2 graph has nonempty neighbor
finsets, an equality-support kernel and a supported crossing history. -/
example : ∃ K : Hagi.Percolation.V 2 → PMF (Hagi.Percolation.V 2),
    supportedRoutingKernel (openGraph (openAt 2 paritySeed)) K ∧
    ∃ (a b : Hagi.Percolation.V 2) (w : (openGraph (openAt 2 paritySeed)).Walk a b),
      rowTop a ∧ rowBot b ∧
        walkHistory w ∈
          (historyLaw (PMF.pure a) (fun _ => K) w.length w.length).support := by
  have hne : ∀ c, ((openGraph (openAt 2 paritySeed)).neighborFinset c).Nonempty := by
    intro c
    fin_cases c
    · exact ⟨(0, 1), by
        norm_num [SimpleGraph.mem_neighborFinset, openGraph, openAt,
          paritySeed, seedParity, cellAdj, step]⟩
    · exact ⟨(0, 0), by
        norm_num [SimpleGraph.mem_neighborFinset, openGraph, openAt,
          paritySeed, seedParity, cellAdj, step]⟩
    · exact ⟨(1, 1), by
        norm_num [SimpleGraph.mem_neighborFinset, openGraph, openAt,
          paritySeed, seedParity, cellAdj, step]⟩
    · exact ⟨(1, 0), by
        norm_num [SimpleGraph.mem_neighborFinset, openGraph, openAt,
          paritySeed, seedParity, cellAdj, step]⟩
  let K := uniformNeighborKernel (openGraph (openAt 2 paritySeed)) hne
  have hK : supportedRoutingKernel (openGraph (openAt 2 paritySeed)) K :=
    uniformNeighborKernel_support _ _
  exact ⟨K, hK, exists_walk_history_support_of_crossing hK parity_crossing2⟩

open scoped BigOperators

universe v

variable {W : Type v}

/-- Zero a weight field outside the actual graph-neighbor relation. -/
noncomputable def maskedNeighborWeights (G : SimpleGraph W) (w : W → W → ENNReal) :
    W → W → ENNReal := fun a => (G.neighborSet a).indicator (w a)

/-- Normalize a masked weight field only where every row has nonzero
finite mass; no pure/default row is supplied when these premises fail. -/
noncomputable def weightedNeighborKernel (G : SimpleGraph W) (w : W → W → ENNReal)
    (h0 : ∀ a, (∑' b, maskedNeighborWeights G w a b) ≠ 0)
    (htop : ∀ a, (∑' b, maskedNeighborWeights G w a b) ≠ ⊤) : W → PMF W :=
  fun a => PMF.normalize (maskedNeighborWeights G w a) (h0 a) (htop a)

/-- Point mass under explicit masked normalization. -/
theorem weightedNeighborKernel_apply (G : SimpleGraph W) (w : W → W → ENNReal)
    (h0 : ∀ a, (∑' b, maskedNeighborWeights G w a b) ≠ 0)
    (htop : ∀ a, (∑' b, maskedNeighborWeights G w a b) ≠ ⊤) (a b : W) :
    weightedNeighborKernel G w h0 htop a b =
      maskedNeighborWeights G w a b * (∑' c, maskedNeighborWeights G w a c)⁻¹ := by
  exact PMF.normalize_apply (h0 a) (htop a) b

/-- Support is graph adjacency with nonzero original weight. -/
theorem mem_weightedNeighborKernel_support_iff (G : SimpleGraph W)
    (w : W → W → ENNReal)
    (h0 : ∀ a, (∑' b, maskedNeighborWeights G w a b) ≠ 0)
    (htop : ∀ a, (∑' b, maskedNeighborWeights G w a b) ≠ ⊤) (a b : W) :
    b ∈ (weightedNeighborKernel G w h0 htop a).support ↔
      G.Adj a b ∧ w a b ≠ 0 := by
  classical
  rw [weightedNeighborKernel, PMF.mem_support_normalize_iff]
  by_cases hab : G.Adj a b <;> simp [maskedNeighborWeights, hab]

/-- Exact support requires positivity on every actual graph edge. -/
theorem weightedNeighborKernel_support (G : SimpleGraph W)
    (w : W → W → ENNReal)
    (h0 : ∀ a, (∑' b, maskedNeighborWeights G w a b) ≠ 0)
    (htop : ∀ a, (∑' b, maskedNeighborWeights G w a b) ≠ ⊤)
    (hpos : ∀ a b, G.Adj a b → w a b ≠ 0) :
    supportedRoutingKernel G (weightedNeighborKernel G w h0 htop) := by
  intro a b
  rw [mem_weightedNeighborKernel_support_iff G w h0 htop]
  exact ⟨fun h => h.1, fun hab => ⟨hab, hpos a b hab⟩⟩

end Hagi.Optimization.MarkovPercolation
