/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.MarkovPathSupport

/-!
# Percolation path: supported routing, open-site crossing and descent paths

A routing kernel whose support is exactly the edge set of a graph puts positive
mass on the exact vertex history of every supplied walk.  For a finite grid with
vacant (open) sites this turns an open-site crossing into a positive-probability
trajectory.  The same statement read on the landscape gives the bridge to
optimization: a kernel whose support percolates the strictly decreasing pairs is
a stochastic optimizer, a descent path is a percolation of the landscape, and
any supplied descent path through the kernel has positive mass, with a strict
total drop.  On a finite state space such a kernel cannot be total with exact
strict support (no infinite descent), so support is stated one-way.

Only supplied trajectories are addressed: no endpoint-hitting probability, no
common-horizon or critical-threshold statement is made.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Optimization.PercolationPath

open Hagi.Probability
open Hagi.Probability.MarkovPathSupport

universe u

variable {V : Type u}

/-! ### Supported routing kernels -/

/-- A normalized routing kernel has support exactly on the actual graph edges. -/
def routingKernelSupported (G : SimpleGraph V) (K : V → PMF V) : Prop :=
  ∀ a b, b ∈ (K a).support ↔ G.Adj a b

/-- Every actual edge is a supported kernel transition (one-way support). -/
def routingKernelSupportedOfAdj (G : SimpleGraph V) (K : V → PMF V) : Prop :=
  ∀ a b, G.Adj a b → b ∈ (K a).support

theorem routingKernelSupportedOfAdj_of_routingKernelSupported (G : SimpleGraph V)
    (K : V → PMF V) (hK : routingKernelSupported G K) :
    routingKernelSupportedOfAdj G K := fun _ _ hab => (hK _ _).mpr hab

/-- The finite vertex history of a supplied graph walk. -/
def walkVertex {G : SimpleGraph V} {a b : V} (w : G.Walk a b) :
    History V w.length := fun i => w.getVert i.val

/-- The walk history is supported once its start and every transition are. -/
theorem historyLaw_walk_support_of_steps (G : SimpleGraph V) (K : ℕ → V → PMF V)
    {a b : V} (w : G.Walk a b) {initial : PMF V}
    (ha : a ∈ initial.support)
    (hsteps : ∀ j < w.length, w.getVert (j + 1) ∈ (K j (w.getVert j)).support) :
    walkVertex w ∈ (historyLaw initial K w.length w.length).support := by
  apply historyLaw_full_support
  · simpa [walkVertex, historyIndex] using ha
  · intro j hj
    simpa only [walkVertex, historyIndex_val, Nat.min_eq_left hj.le,
      Nat.min_eq_left (by omega : j + 1 ≤ w.length)] using hsteps j hj

/-- Any graph walk is a supported history for a homogeneous one-way kernel. -/
theorem historyLaw_walk_support (G : SimpleGraph V) (K : V → PMF V)
    (hK : routingKernelSupportedOfAdj G K) {a b : V} (w : G.Walk a b)
    {initial : PMF V} (ha : a ∈ initial.support) :
    walkVertex w ∈ (historyLaw initial (fun _ => K) w.length w.length).support :=
  historyLaw_walk_support_of_steps G _ w ha
    (fun _ hj => hK _ _ (w.adj_getVert_succ hj))

/-- Any graph walk has positive mass under a homogeneous supported kernel. -/
theorem historyLaw_walk_pos (G : SimpleGraph V) (K : V → PMF V)
    (hK : routingKernelSupported G K) {a b : V} (w : G.Walk a b)
    {initial : PMF V} (ha : a ∈ initial.support) :
    0 < historyLaw initial (fun _ => K) w.length w.length (walkVertex w) :=
  (PMF.apply_pos_iff _ _).mpr
    (historyLaw_walk_support G K (routingKernelSupportedOfAdj_of_routingKernelSupported G K hK)
      w ha)

/-! ### Vacant-site percolation on a finite grid -/

/-- The `L × L` vertex grid (coordinates `0, …, L`). -/
abbrev grid (L : ℕ) := Fin (L + 1) × Fin (L + 1)

/-- Manhattan adjacency of grid sites. -/
def gridAdj {L : ℕ} (a b : grid L) : Prop :=
  (a.1 = b.1 ∧ (a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val)) ∨
    (a.2 = b.2 ∧ (a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val))

theorem gridAdj_symm {L : ℕ} {a b : grid L} (h : gridAdj a b) : gridAdj b a := by
  rcases h with ⟨h, s⟩ | ⟨h, s⟩
  · exact Or.inl ⟨h.symm, s.symm⟩
  · exact Or.inr ⟨h.symm, s.symm⟩

theorem gridAdj_loopless {L : ℕ} (a : grid L) : ¬ gridAdj a a := by
  rintro (⟨_, h⟩ | ⟨_, h⟩) <;> omega

/-- A site is vacant when its seed differs from the blocked value `q`. -/
def vacantSite {L M : ℕ} (ω : grid L → Fin M) (q : Fin M) (c : grid L) : Prop :=
  ω c ≠ q

/-- The graph of vacant sites: Manhattan neighbors, both vacant. -/
def vacantGraph {L M : ℕ} (ω : grid L → Fin M) (q : Fin M) : SimpleGraph (grid L) where
  Adj a b := gridAdj a b ∧ vacantSite ω q a ∧ vacantSite ω q b
  symm := ⟨fun _ _ h => ⟨gridAdj_symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => gridAdj_loopless a h.1⟩

/-- An open crossing: a `top` site connected to a `bottom` site through
vacant sites. -/
def crosses {V : Type u} (top bottom : V → Prop) (G : SimpleGraph V) : Prop :=
  ∃ a b, top a ∧ bottom b ∧ G.Reachable a b

/-- The vacant graph only grows when fewer sites are blocked. -/
theorem vacantGraph_mono {L M : ℕ} {ω : grid L → Fin M} {q q' : Fin M}
    (h : ∀ c, vacantSite ω q' c → vacantSite ω q c) :
    vacantGraph ω q' ≤ vacantGraph ω q := by
  intro a b hab
  exact ⟨hab.1, h a hab.2.1, h b hab.2.2⟩

/-- A crossing under a homogeneous supported routing kernel yields a supplied
walk whose exact history has positive mass from the pure start. -/
theorem crosses_pos {L M : ℕ} {top bottom : grid L → Prop} {ω : grid L → Fin M}
    {q : Fin M} {K : grid L → PMF (grid L)}
    (hK : routingKernelSupported (vacantGraph ω q) K)
    (hc : crosses top bottom (vacantGraph ω q)) :
    ∃ (a b : grid L) (w : (vacantGraph ω q).Walk a b), top a ∧ bottom b ∧
      0 < historyLaw (PMF.pure a) (fun _ => K) w.length w.length (walkVertex w) := by
  obtain ⟨a, b, ha, hb, hr⟩ := hc
  obtain ⟨w⟩ := hr
  exact ⟨a, b, w, ha, hb, historyLaw_walk_pos _ _ hK w (by simp)⟩

/-- One-way form of `crosses_pos`: adjacency alone suffices. -/
theorem crosses_pos_of_adj {L M : ℕ} {top bottom : grid L → Prop} {ω : grid L → Fin M}
    {q : Fin M} {K : grid L → PMF (grid L)}
    (hK : routingKernelSupportedOfAdj (vacantGraph ω q) K)
    (hc : crosses top bottom (vacantGraph ω q)) :
    ∃ (a b : grid L) (w : (vacantGraph ω q).Walk a b), top a ∧ bottom b ∧
      walkVertex w ∈ (historyLaw (PMF.pure a) (fun _ => K) w.length w.length).support := by
  obtain ⟨a, b, ha, hb, hr⟩ := hc
  obtain ⟨w⟩ := hr
  exact ⟨a, b, w, ha, hb, historyLaw_walk_support _ _ hK w (by simp)⟩

/-! ### Descent paths: percolation of the landscape -/

/-- A descent path of length `T`: a trajectory along which `f` strictly
decreases at every step. -/
def descentPath (f : V → ℝ) (T : ℕ) (a b : V) : Prop :=
  ∃ ω : ℕ → V, ω 0 = a ∧ ω T = b ∧ ∀ j < T, f (ω (j + 1)) < f (ω j)

/-- Along a descending trajectory every positive time not exceeding the horizon
lies strictly below the start. -/
theorem descent_value_lt_of_pos {f : V → ℝ} {T k : ℕ} {ω : ℕ → V}
    (hk : k ≤ T) (hk0 : k ≠ 0) (hω : ∀ j < T, f (ω (j + 1)) < f (ω j)) :
    f (ω k) < f (ω 0) := by
  induction T generalizing ω k hk0 with
  | zero => exact absurd (Nat.eq_zero_of_le_zero hk) hk0
  | succ T ih =>
      rcases Nat.lt_or_ge k (T + 1) with hk1 | hk1
      · exact ih (by omega) (by omega) (fun j hj => hω j (by omega))
      · have hkT : k = T + 1 := le_antisymm hk hk1
        subst k
        by_cases hT0 : T = 0
        · subst T
          exact hω 0 (by omega)
        · have hsucc : f ((fun i => ω (i + 1)) T) < f ((fun i => ω (i + 1)) 0) :=
            ih (by omega) (by omega) (fun j hj => hω (j + 1) (by omega))
          exact lt_trans (by simpa using hsucc) (hω 0 (by omega))

/-- Along a nonconstant descent trajectory the endpoint is below the start. -/
theorem descent_value_drop {f : V → ℝ} {T : ℕ} {ω : ℕ → V} (hT : 0 < T)
    (hω : ∀ j < T, f (ω (j + 1)) < f (ω j)) : f (ω T) < f (ω 0) := by
  exact descent_value_lt_of_pos le_rfl (Nat.pos_iff_ne_zero.mp hT) hω

/-- A nonempty descent path strictly decreases the objective. -/
theorem descentPath_drop {f : V → ℝ} {T : ℕ} {a b : V} (hT : 0 < T)
    (hp : descentPath f T a b) : f b < f a := by
  obtain ⟨ω, h0, hT', hω⟩ := hp
  rw [← hT', ← h0]
  exact descent_value_drop hT hω

/-- A kernel supported on decreasing edges never leads uphill: every supported
transition strictly decreases the objective. -/
def supportedDescentKernel (f : V → ℝ) (K : V → PMF V) : Prop :=
  ∀ a b, b ∈ (K a).support → f b < f a

/-- Every strictly decreasing pair is a supported transition: the kernel
percolates the whole landscape of descents. -/
def descentKernelFullSupport (f : V → ℝ) (K : V → PMF V) : Prop :=
  ∀ a b, f b < f a → b ∈ (K a).support

/-- A kernel that never leads uphill and either strictly decreases or stays. -/
def descentOrStayKernel (f : V → ℝ) (K : V → PMF V) : Prop :=
  ∀ a b, b ∈ (K a).support → f b < f a ∨ b = a

theorem descentOrStayKernel_of_supportedDescentKernel (f : V → ℝ) (K : V → PMF V)
    (hK : supportedDescentKernel f K) : descentOrStayKernel f K :=
  fun _ _ hb => Or.inl (hK _ _ hb)

/-- A descent path through the kernel: a trajectory whose every step is a
supported, strictly decreasing transition. -/
def kernelDescentPath (f : V → ℝ) (K : V → PMF V) (T : ℕ) (a b : V) : Prop :=
  ∃ ω : ℕ → V, ω 0 = a ∧ ω T = b ∧
    ∀ j < T, ω (j + 1) ∈ (K (ω j)).support ∧ f (ω (j + 1)) < f (ω j)

/-- Under full descent support every descent path is a path through the kernel. -/
theorem kernelDescentPath_of_descentPath (f : V → ℝ) (K : V → PMF V)
    (hK : descentKernelFullSupport f K) {T : ℕ} {a b : V}
    (hp : descentPath f T a b) : kernelDescentPath f K T a b := by
  obtain ⟨ω, h0, hT, hω⟩ := hp
  exact ⟨ω, h0, hT, fun j hj => ⟨hK _ _ (hω j hj), hω j hj⟩⟩

/-- The unordered graph of step edges whose endpoints have unequal values; a
strictly decreasing step is one of its edges. -/
def descentGraph (f : V → ℝ) (step : V → V) : SimpleGraph V where
  Adj a b := (b = step a ∨ a = step b) ∧ (f b < f a ∨ f a < f b)
  symm := ⟨fun a b ⟨h, h'⟩ => ⟨h.symm, h'.symm⟩⟩
  loopless := ⟨fun a ⟨_, h⟩ => by rcases h with h | h; exact lt_irrefl _ h; exact lt_irrefl _ h⟩

/-- A strictly decreasing step is an edge of the descent graph. -/
theorem descentGraph_adj_of_step_lt {f : V → ℝ} {step : V → V} {a : V}
    (h : f (step a) < f a) : (descentGraph f step).Adj a (step a) :=
  ⟨Or.inl rfl, Or.inl h⟩

/-- A certified first step (hypothesis form of a useful-step theorem: some
`η` with a strict decrease of `f` along `d`) is an edge of the descent graph
of its own step map. -/
theorem exists_descentGraph_edge_of_useful_step {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → ℝ) (a d : E) (η : ℝ) (h : f (a + η • d) < f a) :
    ∃ b : E, (descentGraph f (fun x => x + η • d)).Adj a b ∧ f b < f a :=
  ⟨a + η • d, descentGraph_adj_of_step_lt h, h⟩

/-- Main bridge: a descent path of positive length `T` through a homogeneous
kernel is realized by an exact history of strictly positive probability,
decreasing at every step and ending below the start value. -/
theorem descentPath_apply_pos (f : V → ℝ) (K : V → PMF V)
    {T : ℕ} {a b : V} (hT : 0 < T) (hp : kernelDescentPath f K T a b) :
    ∃ ω : History V T,
      0 < historyLaw (PMF.pure a) (fun _ => K) T T ω ∧
      (∀ j < T, f (ω (historyIndex T (j + 1))) < f (ω (historyIndex T j))) ∧
      f b < f a := by
  obtain ⟨ω, h0, hTb, hω⟩ := hp
  have hstart : ω 0 ∈ (PMF.pure a).support := by rw [h0]; simp
  have hsteps : ∀ j < T, (fun i : Fin (T + 1) => ω i.val) (historyIndex T (j + 1)) ∈
      (K ((fun i : Fin (T + 1) => ω i.val) (historyIndex T j))).support := by
    intro j hj
    simpa only [historyIndex_val, Nat.min_eq_left hj.le,
      Nat.min_eq_left (by omega : j + 1 ≤ T)] using (hω j hj).1
  have hdec : ∀ j < T, f (ω (j + 1)) < f (ω j) := fun j hj => (hω j hj).2
  refine ⟨fun i => ω i.val, historyLaw_full_apply_pos _ _ _ hstart hsteps, fun j hj => by
    simpa only [historyIndex_val, Nat.min_eq_left hj.le,
      Nat.min_eq_left (by omega : j + 1 ≤ T)] using hdec j hj, ?_⟩
  simpa [h0, hTb] using descent_value_drop hT hdec

/-- Corollary with full descent support: every landscape descent path has
positive mass. -/
theorem descentPath_apply_pos_of_full_support (f : V → ℝ) (K : V → PMF V)
    (hK : descentKernelFullSupport f K) {T : ℕ} {a b : V} (hT : 0 < T)
    (hp : descentPath f T a b) :
    ∃ ω : History V T,
      0 < historyLaw (PMF.pure a) (fun _ => K) T T ω ∧
      (∀ j < T, f (ω (historyIndex T (j + 1))) < f (ω (historyIndex T j))) ∧
      f b < f a :=
  descentPath_apply_pos f K hT (kernelDescentPath_of_descentPath f K hK hp)

/-- A supplied trajectory of supported non-staying steps under a
descent-or-stay kernel strictly decreases and has positive mass. -/
theorem descentOrStay_apply_pos (f : V → ℝ) (K : V → PMF V) (hK : descentOrStayKernel f K)
    (initial : PMF V) {T : ℕ} (ω : History V T)
    (hstart : ω (historyIndex T 0) ∈ initial.support)
    (hsteps : ∀ j < T, ω (historyIndex T (j + 1)) ∈ (K (ω (historyIndex T j))).support)
    (hmove : ∀ j < T, ω (historyIndex T (j + 1)) ≠ ω (historyIndex T j)) :
    0 < historyLaw initial (fun _ => K) T T ω ∧
      ∀ j < T, f (ω (historyIndex T (j + 1))) < f (ω (historyIndex T j)) :=
  ⟨historyLaw_full_apply_pos initial (fun _ => K) ω hstart hsteps,
    fun j hj => ((hK _ _ (hsteps j hj)).resolve_right (hmove j hj))⟩

/-- The descent path statement for a trajectory that decreases for `T` steps. -/
theorem descentPath_of_iterate (f : V → ℝ) (step : V → V) (a : V) {T : ℕ}
    (h : ∀ j < T, f ((step^[j + 1]) a) < f ((step^[j]) a)) :
    descentPath f T a ((step^[T]) a) :=
  ⟨fun j => (step^[j]) a, rfl, rfl, h⟩

end Hagi.Optimization.PercolationPath
