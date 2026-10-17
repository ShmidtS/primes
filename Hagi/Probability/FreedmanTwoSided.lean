/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.MarkovFreedman
/-!
# HistoryPath — the path-space lift of a Markov chain


Ported verbatim from openai/math,
OAI.Combinatorics.TriangleRemoval.Process.History (the
E:/math audit, Fam 188): History (path type), historyIndex,
historyInitial/historyKernel/historyLaw (the lifted chain on
paths), the marginal/invariant lemmas and the support
transport — the infrastructure for path-level additive
functionals (HistoryAdditive next).
-/

namespace Hagi.Probability

section
open scoped BigOperators Topology
open Filter

abbrev History (α : Type*) (T : ℕ) := Fin (T + 1) → α

def historyIndex (T k : ℕ) : Fin (T + 1) := ⟨min k T,by omega⟩

@[simp] theorem historyIndex_val (T k : ℕ) : (historyIndex T k).val = min k T := rfl

noncomputable def historyInitial {α : Type*} (initial : PMF α) (T : ℕ) : PMF (History α T) :=
  initial.map (fun a => fun _ => a)

noncomputable def historyKernel {α : Type*} (K : ℕ → α → PMF α) (T k : ℕ)
    (ω : History α T) : PMF (History α T) :=
  if k < T then (K k (ω (historyIndex T k))).map
    (fun b => Function.update ω (historyIndex T (k + 1)) b) else PMF.pure ω

noncomputable def historyLaw {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α)
    (T k : ℕ) : PMF (History α T) :=
  markovLaw (historyInitial initial T) (historyKernel K T) k

theorem historyIndex_ne_succ {T j k : ℕ} (hjk : j ≤ k) (hk : k < T) :
    historyIndex T j ≠ historyIndex T (k + 1) := by
  intro h
  have he := congrArg Fin.val h
  simp only [historyIndex_val] at he
  omega

theorem historyLaw_marginal {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α)
    (T k : ℕ) (hk : k ≤ T) :
    (historyLaw initial K T k).map (fun ω => ω (historyIndex T k)) =
      markovLaw initial K k := by
  induction k with
  | zero =>
    simp only [historyLaw,markovLaw,historyInitial,PMF.map_comp]
    change initial.map id = initial
    exact PMF.map_id initial
  | succ k ih =>
    have hkt : k < T := by omega
    have hkm : k ≤ T := by omega
    simp only [historyLaw,markovLaw,PMF.map_bind]
    have ih' := ih hkm
    change (historyLaw initial K T k).bind _ = (markovLaw initial K k).bind (K k)
    rw [← ih',PMF.bind_map]
    congr 1
    funext ω
    simp only [historyKernel,ite_eq_left hkt,PMF.map_comp,Function.comp_def,
      Function.update_self]
    exact PMF.map_id _

theorem historyLaw_invariant {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α)
    (P : α → Prop) (hinit : ∀ a ∈ initial.support, P a)
    (hstep : ∀ k a, P a → ∀ b ∈ (K k a).support, P b)
    (T k : ℕ) (ω : History α T) (hω : ω ∈ (historyLaw initial K T k).support) :
    ∀ j, P (ω j) := by
  induction k generalizing ω with
  | zero =>
    obtain ⟨a,ha,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
    exact fun _ => hinit a ha
  | succ k ih =>
    obtain ⟨π,hπ,hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
    have hp := ih π hπ
    by_cases hk : k < T
    · rw [historyKernel,ite_eq_left hk] at hω
      obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
      intro j
      by_cases hj : j = historyIndex T (k + 1)
      · subst j
        rw [Function.update_self]
        exact hstep k _ (hp _) b hb
      · rw [Function.update_of_ne hj]
        exact hp j
    · rw [historyKernel,ite_eq_right hk,PMF.mem_support_pure_iff] at hω
      subst ω
      exact hp

noncomputable def historyIncrement {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T j : ℕ) (ω : History α T) : ℝ :=
  f (j + 1) (ω (historyIndex T (j + 1))) -
    pmfMean (K j (ω (historyIndex T j))) (f (j + 1))

noncomputable def historyNoise {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T k : ℕ) (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), historyIncrement K f T j ω

noncomputable def historyCounter {α : Type*} (v : ℕ → α → ℝ)
    (T k : ℕ) (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), v j (ω (historyIndex T j))

noncomputable def historyCounterRate {α : Type*} (v : ℕ → α → ℝ)
    (T k : ℕ) (ω : History α T) : ℝ :=
  if k < T then v k (ω (historyIndex T k)) else 0

theorem historyNoise_update {α : Type*} [Fintype α] (K : ℕ → α → PMF α)
    (f : ℕ → α → ℝ) (T k : ℕ) (hk : k < T) (ω : History α T) (b : α) :
    historyNoise K f T (k + 1) (Function.update ω (historyIndex T (k + 1)) b) =
      historyNoise K f T k ω + f (k + 1) b -
        pmfMean (K k (ω (historyIndex T k))) (f (k + 1)) := by
  unfold historyNoise
  rw [Nat.min_eq_left (by omega : k + 1 ≤ T),Nat.min_eq_left hk.le,Finset.sum_range_succ]
  have hp : (∑ j ∈ Finset.range k,
      historyIncrement K f T j (Function.update ω (historyIndex T (k + 1)) b)) =
      ∑ j ∈ Finset.range k, historyIncrement K f T j ω := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjk := Finset.mem_range.mp hj
    simp only [historyIncrement,Function.update_of_ne (historyIndex_ne_succ (by omega : j + 1 ≤ k) hk),
      Function.update_of_ne (historyIndex_ne_succ hjk.le hk)]
  rw [hp]
  simp only [historyIncrement,Function.update_self,
    Function.update_of_ne (historyIndex_ne_succ le_rfl hk)]
  ring

theorem historyCounter_update {α : Type*} (v : ℕ → α → ℝ)
    (T k : ℕ) (hk : k < T) (ω : History α T) (b : α) :
    historyCounter v T (k + 1) (Function.update ω (historyIndex T (k + 1)) b) =
      historyCounter v T k ω + v k (ω (historyIndex T k)) := by
  unfold historyCounter
  rw [Nat.min_eq_left (by omega : k + 1 ≤ T),Nat.min_eq_left hk.le,Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (historyIndex_ne_succ (Finset.mem_range.mp hj).le hk)]
  · rw [Function.update_of_ne (historyIndex_ne_succ le_rfl hk)]

@[simp] theorem historyNoise_zero {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T : ℕ) (ω : History α T) :
    historyNoise K f T 0 ω = 0 := by simp [historyNoise]

@[simp] theorem historyCounter_zero {α : Type*} (v : ℕ → α → ℝ)
    (T : ℕ) (ω : History α T) : historyCounter v T 0 ω = 0 := by simp [historyCounter]

theorem historyLaw_current_support {α : Type*} (initial : PMF α)
    (K : ℕ → α → PMF α) (T k : ℕ) (hk : k ≤ T)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T k).support) :
    ω (historyIndex T k) ∈ (markovLaw initial K k).support := by
  rw [← historyLaw_marginal initial K T k hk]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨ω,hω,rfl⟩

theorem historyNoise_frozen {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T k : ℕ) (hk : T ≤ k)
    (ω : History α T) : historyNoise K f T (k + 1) ω = historyNoise K f T k ω := by
  simp only [historyNoise,Nat.min_eq_right hk,Nat.min_eq_right (by omega : T ≤ k + 1)]

theorem historyCounter_frozen {α : Type*} (v : ℕ → α → ℝ) (T k : ℕ) (hk : T ≤ k)
    (ω : History α T) : historyCounter v T (k + 1) ω = historyCounter v T k ω := by
  simp only [historyCounter,Nat.min_eq_right hk,Nat.min_eq_right (by omega : T ≤ k + 1)]

theorem history_noise_freedman {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (f v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support,
        |f (k + 1) b - pmfMean (K k a) (f (k + 1))| ≤ c)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b =>
        (f (k + 1) b - pmfMean (K k a) (f (k + 1))) ^ 2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyNoise K f T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0) ≤ Real.exp (-r ^ 2 / (4 * (V + c * r))) := by
  classical
  apply finite_freedman (historyInitial initial T) (historyKernel K T)
    (historyNoise K f T) (historyCounter v T) (historyCounterRate v T) c hc
  · intro ω _
    simp only [historyNoise_zero,historyCounter_zero,le_refl,and_self]
  · intro j ω hω π hπ
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hπ
      obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hπ
      rw [historyNoise_update K f T j hj]
      have hb' := hbounded j hj _ (historyLaw_current_support initial K T j hj.le ω hω) b hb
      convert hb' using 1; congr 1; ring
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hπ
      subst π
      rw [historyNoise_frozen K f T j (Nat.le_of_not_gt hj),sub_self,abs_zero]
      exact hc.le
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map]
      have he (b : α) : historyNoise K f T (j + 1)
          (Function.update ω (historyIndex T (j + 1)) b) - historyNoise K f T j ω =
          f (j + 1) b - pmfMean (K j (ω (historyIndex T j))) (f (j + 1)) := by
        rw [historyNoise_update K f T j hj]
        ring
      simp_rw [he]
      rw [pmfMean_sub,pmfMean_const,sub_self]
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyNoise_frozen K f T j (Nat.le_of_not_gt hj),sub_self]
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map,historyCounterRate,ite_eq_left hj]
      have he (b : α) : historyNoise K f T (j + 1)
          (Function.update ω (historyIndex T (j + 1)) b) - historyNoise K f T j ω =
          f (j + 1) b - pmfMean (K j (ω (historyIndex T j))) (f (j + 1)) := by
        rw [historyNoise_update K f T j hj]
        ring
      simp_rw [he]
      exact hvar j hj _ (historyLaw_current_support initial K T j hj.le ω hω)
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyNoise_frozen K f T j (Nat.le_of_not_gt hj),sub_self,
        historyCounterRate,ite_eq_right hj,zero_pow (by decide : 2 ≠ 0)]
  · intro j ω _ π hπ
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hπ
      obtain ⟨b,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hπ
      rw [historyCounter_update v T j hj,historyCounterRate,ite_eq_left hj]
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hπ
      subst π
      rw [historyCounter_frozen v T j (Nat.le_of_not_gt hj),
        historyCounterRate,ite_eq_right hj,add_zero]
  · exact hr
  · exact hV


end

end Hagi.Probability
/-!
# HistoryPastMean — past-measurability and the union bound


Ported verbatim from openai/math,
OAI.Combinatorics.TriangleRemoval.Probability.
HistoryLawPastMean (the E:/math audit, Fam 188):
historyLaw_past_mean (past-measurable functions have
time-consistent laws), pmfMean_event_union (the finite
union bound for PMF expectations), pmfMean_finset_sum, and
the history_noise_freedman_maximal corollaries — the
prerequisites for the joint two-sided maximal Freedman.
-/

namespace Hagi.Probability

section
open scoped BigOperators Topology
open Filter

theorem historyLaw_past_mean {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (T j k : ℕ) (hjk : j ≤ k)
    (f : History α T → ℝ)
    (hf : ∀ ω π, (∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) → f ω = f π) :
    pmfMean (historyLaw initial K T k) f =
      pmfMean (historyLaw initial K T j) f := by
  classical
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | @succ k hjk ih =>
    change pmfMean ((historyLaw initial K T k).bind (historyKernel K T k)) f = _
    rw [pmfMean_bind]
    have he (ω : History α T) : pmfMean (historyKernel K T k ω) f = f ω := by
      by_cases hk : k < T
      · rw [historyKernel,ite_eq_left hk,pmfMean_map]
        have hu (b : α) : f (Function.update ω (historyIndex T (k+1)) b) = f ω := by
          apply hf
          intro i hi
          apply Function.update_of_ne
          intro hh
          have hval := congrArg Fin.val hh
          simp only [historyIndex,Nat.min_eq_left (by omega : k+1 ≤ T)] at hval
          have : i.val ≤ j := hi.trans (Nat.min_le_left _ _)
          omega
        simp_rw [hu]
        exact pmfMean_const _ _
      · rw [historyKernel,ite_eq_right hk,pmfMean_pure]
    simp_rw [he]
    exact ih

lemma historyNoise_past {α : Type*} [Fintype α] (K : ℕ → α → PMF α)
    (f : ℕ → α → ℝ) (T j : ℕ) (ω π : History α T)
    (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) :
    historyNoise K f T j ω = historyNoise K f T j π := by
  unfold historyNoise
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < min j T := Finset.mem_range.mp hs
  have hsc : (historyIndex T s).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (Nat.le_of_lt hs')
  have hsn : (historyIndex T (s+1)).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (by omega)
  simp only [historyIncrement,h _ hsc,h _ hsn]

lemma historyCounter_past {α : Type*} (v : ℕ → α → ℝ)
    (T j : ℕ) (ω π : History α T)
    (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) :
    historyCounter v T j ω = historyCounter v T j π := by
  unfold historyCounter
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < min j T := Finset.mem_range.mp hs
  have hsc : (historyIndex T s).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (Nat.le_of_lt hs')
  rw [h _ hsc]

lemma pmfMean_finset_sum {α J : Type*} [Fintype α] (p : PMF α)
    (s : Finset J) (f : J → α → ℝ) :
    pmfMean p (fun a => ∑ j ∈ s, f j a) = ∑ j ∈ s, pmfMean p (f j) := by
  simp only [pmfMean,Finset.mul_sum]
  exact Finset.sum_comm

open Classical in

theorem pmfMean_event_union {α J : Type*} [Fintype α] (p : PMF α)
    (s : Finset J) (P : J → α → Prop) :
    pmfMean p (fun a => if ∃ j ∈ s, P j a then 1 else 0) ≤
      ∑ j ∈ s, pmfMean p (fun a => if P j a then 1 else 0) := by
  classical
  rw [← pmfMean_finset_sum]
  apply pmfMean_mono
  intro a _
  by_cases h : ∃ j ∈ s, P j a
  · obtain ⟨j,hj,hP⟩ := h
    rw [ite_eq_left ⟨j,hj,hP⟩]
    have hh := Finset.single_le_sum (f := fun j => (if P j a then (1 : ℝ) else 0))
      (fun _ _ => by positivity) hj
    simpa only [ite_eq_left hP] using hh
  · rw [ite_eq_right h]
    positivity

theorem history_noise_freedman_maximal {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (f v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support,
        |f (k+1) b - pmfMean (K k a) (f (k+1))| ≤ c)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b =>
        (f (k+1) b - pmfMean (K k a) (f (k+1)))^2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ historyNoise K f T j ω ∧
        historyCounter v T j ω ≤ V then 1 else 0) ≤
      (T+1 : ℝ) * Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  have hcov := pmfMean_event_union (historyLaw initial K T T) (Finset.range (T+1))
    (fun j ω => r ≤ historyNoise K f T j ω ∧ historyCounter v T j ω ≤ V)
  have hsum : (∑ j ∈ Finset.range (T+1),
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyNoise K f T j ω ∧ historyCounter v T j ω ≤ V
          then 1 else 0)) ≤ (T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (T+1), Real.exp (-r^2/(4*(V+c*r))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjT : j ≤ T := by have := Finset.mem_range.mp hj; omega
        rw [historyLaw_past_mean initial K T j T hjT _ (by
          intro ω π h
          rw [historyNoise_past K f T j ω π h,historyCounter_past v T j ω π h])]
        exact history_noise_freedman initial K f v T c hc hbounded hvar j r V hr hV
      _ = _ := by simp
  apply le_trans _ hsum
  convert hcov using 1 <;> try rfl
  · apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    simp only [Finset.mem_range,Nat.lt_succ_iff]
  · apply Finset.sum_congr rfl
    intro j _
    apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    split_ifs <;> rfl


end

end Hagi.Probability

/-!
# HistoryFreedman — the JOINT ANYTIME maximal Freedman on
paths ( port — closes the last open Freedman form of
plan section 1.2)

Ported verbatim from openai/math,
OAI.Combinatorics.TriangleRemoval.Process.HistoryAdditive
(the E:/math audit, Fam 188):

* `historyAdditive` — additive path functionals
  Σⱼ g(state_j, state_{j+1}) over the first k steps;
* `history_additive_freedman` — the fixed-time tail on
  paths: P[S_k ≥ r, V_k ≤ V] ≤ exp(−r²/(4(V + c·r)));
* `history_additive_freedman_maximal` — THE JOINT ANYTIME
  FORM: P[∃ j ≤ T: S_j ≥ r ∧ V_j ≤ V] ≤ (T+1)·
  exp(−r²/(4(V + c·r))) — the union of the time-uniform
  tails over the horizon (the two-sided |S| form follows
  by applying to S and −S and doubling, 2(T+1)·exp(...)).

0 sorry in the source, 0 here; axioms standard.
-/

namespace Hagi.Probability

section
open scoped BigOperators Topology
open Filter

noncomputable def historyAdditive {α : Type*} (g : ℕ → α → α → ℝ)
    (T k : ℕ) (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), g j (ω (historyIndex T j)) (ω (historyIndex T (j+1)))

lemma historyAdditive_update {α : Type*} (g : ℕ → α → α → ℝ)
    (T k : ℕ) (hk : k < T) (ω : History α T) (b : α) :
    historyAdditive g T (k+1) (Function.update ω (historyIndex T (k+1)) b) =
      historyAdditive g T k ω + g k (ω (historyIndex T k)) b := by
  unfold historyAdditive
  rw [Nat.min_eq_left (by omega : k+1 ≤ T),Nat.min_eq_left hk.le,Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjk := Finset.mem_range.mp hj
    rw [Function.update_of_ne (historyIndex_ne_succ hjk.le hk),
       Function.update_of_ne (historyIndex_ne_succ (by omega : j+1 ≤ k) hk)]
  · rw [Function.update_self,Function.update_of_ne (historyIndex_ne_succ le_rfl hk)]

@[simp] lemma historyAdditive_zero {α : Type*} (g : ℕ → α → α → ℝ)
    (T : ℕ) (ω : History α T) : historyAdditive g T 0 ω = 0 := by
  simp [historyAdditive]

lemma historyAdditive_frozen {α : Type*} (g : ℕ → α → α → ℝ)
    (T k : ℕ) (hk : T ≤ k) (ω : History α T) :
    historyAdditive g T (k+1) ω = historyAdditive g T k ω := by
  simp only [historyAdditive,Nat.min_eq_right hk,Nat.min_eq_right (by omega : T ≤ k+1)]

theorem history_additive_freedman {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyAdditive g T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0) ≤ Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  apply finite_freedman (historyInitial initial T) (historyKernel K T)
    (historyAdditive g T) (historyCounter v T) (historyCounterRate v T) c hc
  · intro ω _
    simp only [historyAdditive_zero,historyCounter_zero,le_refl,and_self]
  · intro j ω hω π hπ
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hπ
      obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hπ
      rw [historyAdditive_update g T j hj,add_sub_cancel_left]
      exact hbounded j hj _ (historyLaw_current_support initial K T j hj.le ω hω) b hb
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hπ
      subst π
      rw [historyAdditive_frozen g T j (Nat.le_of_not_gt hj),sub_self,abs_zero]
      exact hc.le
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map]
      simp_rw [historyAdditive_update g T j hj,add_sub_cancel_left]
      exact (hmean j hj _ (historyLaw_current_support initial K T j hj.le ω hω)).le
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyAdditive_frozen g T j (Nat.le_of_not_gt hj),sub_self]
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map,historyCounterRate,ite_eq_left hj]
      simp_rw [historyAdditive_update g T j hj,add_sub_cancel_left]
      exact hvar j hj _ (historyLaw_current_support initial K T j hj.le ω hω)
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyAdditive_frozen g T j (Nat.le_of_not_gt hj),sub_self,
        historyCounterRate,ite_eq_right hj,zero_pow (by decide : 2 ≠ 0)]
  · intro j ω _ π hπ
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hπ
      obtain ⟨b,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hπ
      rw [historyCounter_update v T j hj,historyCounterRate,ite_eq_left hj]
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hπ
      subst π
      rw [historyCounter_frozen v T j (Nat.le_of_not_gt hj),
        historyCounterRate,ite_eq_right hj,add_zero]
  · exact hr
  · exact hV

lemma historyAdditive_past {α : Type*} (g : ℕ → α → α → ℝ)
    (T j : ℕ) (ω π : History α T)
    (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) :
    historyAdditive g T j ω = historyAdditive g T j π := by
  unfold historyAdditive
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < min j T := Finset.mem_range.mp hs
  have hsc : (historyIndex T s).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (Nat.le_of_lt hs')
  have hsn : (historyIndex T (s+1)).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (by omega)
  rw [h _ hsc,h _ hsn]

theorem history_additive_freedman_maximal {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
        historyCounter v T j ω ≤ V then 1 else 0) ≤
      (T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  have hcov := pmfMean_event_union (historyLaw initial K T T) (Finset.range (T+1))
    (fun j ω => r ≤ historyAdditive g T j ω ∧ historyCounter v T j ω ≤ V)
  have hsum : (∑ j ∈ Finset.range (T+1),
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T j ω ∧ historyCounter v T j ω ≤ V
          then 1 else 0)) ≤ (T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (T+1), Real.exp (-r^2/(4*(V+c*r))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjT : j ≤ T := by have := Finset.mem_range.mp hj; omega
        rw [historyLaw_past_mean initial K T j T hjT _ (by
          intro ω π h
          rw [historyAdditive_past g T j ω π h,historyCounter_past v T j ω π h])]
        exact history_additive_freedman initial K g v T c hc hbounded hmean hvar j r V hr hV
      _ = _ := by simp
  apply le_trans _ hsum
  convert hcov using 1 <;> try rfl
  · apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    simp only [Finset.mem_range,Nat.lt_succ_iff]
  · apply Finset.sum_congr rfl
    intro j _
    apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    split_ifs <;> rfl



/-- **Anytime-Freedman с k-зависимыми порогами (R541)**:
лестница {r j, V j} по горизонту j ≤ T — обобщение
равнопороговой `history_additive_freedman_maximal`:
P[∃ j ≤ T: r j ≤ S_j ∧ C_j ≤ V_j]
  ≤ Σ_{j=0}^{T} exp(−r j² / (4·(V j + c·r j))).
Каждый член лестницы — собственный Freedman-хвост;
мост законов — `historyLaw_past_mean` (событие j-го
префикса не зависит от «заморозки» после j). -/
theorem anytime_freedman_thresholds {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ)
    (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hV : ∀ j, 0 ≤ V j) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
        historyCounter v T j ω ≤ V j then 1 else 0) ≤
      ∑ j ∈ Finset.range (T+1),
        Real.exp (-(r j)^2/(4*(V j + c * r j))) := by
  classical
  have hcov := pmfMean_event_union (historyLaw initial K T T)
    (Finset.range (T+1))
    (fun j ω => r j ≤ historyAdditive g T j ω ∧
      historyCounter v T j ω ≤ V j)
  have hsum : (∑ j ∈ Finset.range (T+1),
      pmfMean (historyLaw initial K T T)
        (fun ω => if r j ≤ historyAdditive g T j ω ∧
          historyCounter v T j ω ≤ V j then 1 else 0)) ≤
      ∑ j ∈ Finset.range (T+1),
        Real.exp (-(r j)^2/(4*(V j + c * r j))) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjT : j ≤ T := by have := Finset.mem_range.mp hj; omega
    rw [historyLaw_past_mean initial K T j T hjT _ (by
      intro ω π h
      rw [historyAdditive_past g T j ω π h,
        historyCounter_past v T j ω π h])]
    exact history_additive_freedman initial K g v T c hc
      hbounded hmean hvar j (r j) (V j) (hr j) (hV j)
  apply le_trans _ hsum
  convert hcov using 1 <;> try rfl
  · apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    simp only [Finset.mem_range, Nat.lt_succ_iff]
  · apply Finset.sum_congr rfl
    intro j _
    apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    split_ifs <;> rfl

end

end Hagi.Probability

/-!
# FreedmanTwoSided — the |S| form of the joint maximal
Freedman (: the Hagi corollary closing the plan's
"two-sided anytime joint" line)

The plan (§1.2) asks for
P[∃j≤T: |S_j| ≥ r ∧ V_j ≤ v] ≤ 2(T+1)·exp(−r²/(4(v+cr))).
The ported one-sided maximal form applies to S and to −S
(negation preserves the bound and second-moment conditions;
the mean condition holds with equality); the two-sided
event is the union of the two one-sided events and the
finite union bound (pmfMean_event_union) doubles the
one-sided bound.
-/

namespace Hagi.Probability

open scoped BigOperators

/-- **The two-sided joint anytime Freedman**: for centered
bounded increments with the variance counter,
P[∃j≤T: |S_j| ≥ r ∧ V_j ≤ V] ≤ 2(T+1)·exp(−r²/(4(V+c·r))). -/
theorem history_additive_freedman_two_sided
    {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
        historyCounter v T j ω ≤ V then 1 else 0) ≤
      2 * ((T : ℝ) + 1) * Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  -- the negated functional satisfies the same conditions
  have hbounded' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |(-g) k a b| ≤ c := by
    intro k hk a ha b hb
    show |-(g k a b)| ≤ c
    rw [abs_neg]
    exact hbounded k hk a ha b hb
  have hmean' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) ((fun k a b => -g k a b) k a) = 0 := by
    intro k hk a ha
    show pmfMean (K k a) (fun b => -(g k a b)) = 0
    have h0 : pmfMean (K k a) (fun b => g k a b) = 0 := hmean k hk a ha
    have hneg : pmfMean (K k a) (fun b => -(g k a b))
        = -pmfMean (K k a) (fun b => g k a b) := by
      have := pmfMean_const_mul (K k a) (-1) (fun b => g k a b)
      simpa using this
    rw [hneg, h0]
    ring
  have hvar' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => ((fun k a b => -g k a b) k a b)^2) ≤ v k a := by
    intro k hk a ha
    show pmfMean (K k a) (fun b => (-(g k a b))^2) ≤ v k a
    have hsq : pmfMean (K k a) (fun b => (-(g k a b))^2)
        = pmfMean (K k a) (fun b => (g k a b)^2) :=
      pmfMean_congr (K k a) (fun b _ => neg_sq (g k a b))
    rw [hsq]
    exact hvar k hk a ha
  -- the two one-sided maximal bounds
  have h1 := history_additive_freedman_maximal initial K g v T c hc
    hbounded hmean hvar r V hr hV
  have h2 := history_additive_freedman_maximal initial K
    (fun k a b => -g k a b) v T c hc hbounded' hmean' hvar' r V hr hV
  -- negated-functional sums: pointwise identity under funext
  have hnegfun : ∀ ω : History α T,
      (fun (j : ℕ) => historyAdditive (fun k a b => -g k a b) T j ω)
      = fun (j : ℕ) => -historyAdditive g T j ω := by
    intro ω
    funext j
    unfold historyAdditive
    rw [← Finset.sum_neg_distrib]
  -- the two-sided mean splits via the ADDITIVE indicator bound
  have hsplit : pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
        historyCounter v T j ω ≤ V then 1 else 0)
      ≤ pmfMean (historyLaw initial K T T)
        (fun ω => (if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)
          + (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)) := by
    refine pmfMean_mono _ (fun ω _ => ?_)
    by_cases hex : ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
      historyCounter v T j ω ≤ V
    · rw [ite_eq_left hex]
      by_cases hpos : ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
        historyCounter v T j ω ≤ V
      · rw [ite_eq_left hpos]
        have hz : (0:ℝ) ≤ (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then 1 else 0) :=
          ite_nonneg (by norm_num) (by norm_num)
        linarith
      · -- S never reaches r upward, but |S| does: so -S does
        obtain ⟨j, hj, habs, hctr⟩ := hex
        have hnegup : r ≤ -historyAdditive g T j ω := by
          by_contra hcon
          push_neg at hcon
          have hS : historyAdditive g T j ω < r :=
            lt_of_not_ge (fun h => hpos ⟨j, hj, h, hctr⟩)
          have habslt : |historyAdditive g T j ω| < r :=
            abs_lt.mpr ⟨by linarith, hS⟩
          linarith
        rw [ite_eq_right hpos,
          ite_eq_left ⟨j, hj, hnegup, hctr⟩]
        norm_num
    · rw [ite_eq_right hex]
      have hz1 : (0:ℝ) ≤ (if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
          historyCounter v T j ω ≤ V then 1 else 0) :=
        ite_nonneg (by norm_num) (by norm_num)
      have hz2 : (0:ℝ) ≤ (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
          historyCounter v T j ω ≤ V then 1 else 0) :=
        ite_nonneg (by norm_num) (by norm_num)
      linarith
  -- mean of the sum = sum of the means; rewrite the negated part
  have hsum : pmfMean (historyLaw initial K T T)
      (fun ω => (if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)
          + (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0))
      = pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)
        + pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T,
            r ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0) := by
    rw [pmfMean_add]
    congr 1
    · refine pmfMean_congr _ (fun ω _ => ?_)
      have hj : ∀ j, historyAdditive (fun k a b => -g k a b) T j ω
          = -historyAdditive g T j ω := fun j => congrFun (hnegfun ω) j
      simp only [hj]
  calc pmfMean (historyLaw initial K T T)
        (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
          historyCounter v T j ω ≤ V then 1 else 0)
      ≤ pmfMean (historyLaw initial K T T)
          (fun ω => (if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
              historyCounter v T j ω ≤ V then (1:ℝ) else 0)
            + (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
              historyCounter v T j ω ≤ V then (1:ℝ) else 0)) := hsplit
    _ = pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)
        + pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T,
            r ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0) := hsum
    _ ≤ ((T : ℝ) + 1) * Real.exp (-r^2/(4*(V+c*r)))
        + ((T : ℝ) + 1) * Real.exp (-r^2/(4*(V+c*r))) :=
        add_le_add h1 h2
    _ = 2 * ((T : ℝ) + 1) * Real.exp (-r^2/(4*(V+c*r))) := by ring


/-- **Двусторонняя anytime-лестница с k-зависимыми
порогами (R542)**: композиция R541 (`anytime_freedman_
thresholds`) с двусторонним расщеплением:
P[∃ j ≤ T: |S_j| ≥ r j ∧ C_j ≤ V j] ≤ 2·Σ_j exp(−r j²/(4(V j + c·r j))).
Каждое плечо (S и −S) — своя пороговая лестница. -/
theorem anytime_freedman_thresholds_two_sided
    {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ)
    (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hV : ∀ j, 0 ≤ V j) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r j ≤ |historyAdditive g T j ω| ∧
        historyCounter v T j ω ≤ V j then 1 else 0) ≤
      2 * ∑ j ∈ Finset.range (T+1),
        Real.exp (-(r j)^2/(4*(V j + c * r j))) := by
  classical
  -- negated functional: same conditions
  have hbounded' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |(-g) k a b| ≤ c := by
    intro k hk a ha b hb
    show |-(g k a b)| ≤ c
    rw [abs_neg]
    exact hbounded k hk a ha b hb
  have hmean' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) ((fun k a b => -g k a b) k a) = 0 := by
    intro k hk a ha
    show pmfMean (K k a) (fun b => -(g k a b)) = 0
    have h0 : pmfMean (K k a) (fun b => g k a b) = 0 := hmean k hk a ha
    have hneg : pmfMean (K k a) (fun b => -(g k a b))
        = -pmfMean (K k a) (fun b => g k a b) := by
      have := pmfMean_const_mul (K k a) (-1) (fun b => g k a b)
      simpa using this
    rw [hneg, h0]
    ring
  have hvar' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => ((fun k a b => -g k a b) k a b)^2)
        ≤ v k a := by
    intro k hk a ha
    show pmfMean (K k a) (fun b => (-(g k a b))^2) ≤ v k a
    have hsq : pmfMean (K k a) (fun b => (-(g k a b))^2)
        = pmfMean (K k a) (fun b => (g k a b)^2) :=
      pmfMean_congr (K k a) (fun b _ => neg_sq (g k a b))
    rw [hsq]
    exact hvar k hk a ha
  -- additive indicator split: |S| event ⊆ S-event + (−S)-event
  have hsplit : pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r j ≤ |historyAdditive g T j ω| ∧
        historyCounter v T j ω ≤ V j then 1 else 0)
      ≤ pmfMean (historyLaw initial K T T)
        (fun ω => (if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0)
          + (if ∃ j ≤ T, r j ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0)) := by
    refine pmfMean_mono _ (fun ω _ => ?_)
    by_cases hex : ∃ j ≤ T, r j ≤ |historyAdditive g T j ω| ∧
      historyCounter v T j ω ≤ V j
    · rw [ite_eq_left hex]
      by_cases hpos : ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
        historyCounter v T j ω ≤ V j
      · rw [ite_eq_left hpos]
        have hz : (0:ℝ) ≤ (if ∃ j ≤ T, r j ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then 1 else 0) :=
          ite_nonneg (by norm_num) (by norm_num)
        linarith
      · obtain ⟨j, hj, habs, hctr⟩ := hex
        have hnegup : r j ≤ -historyAdditive g T j ω := by
          by_contra hcon
          push_neg at hcon
          have hS : historyAdditive g T j ω < r j :=
            lt_of_not_ge (fun h => hpos ⟨j, hj, h, hctr⟩)
          have habslt : |historyAdditive g T j ω| < r j :=
            abs_lt.mpr ⟨by linarith, hS⟩
          linarith
        rw [ite_eq_right hpos,
          ite_eq_left ⟨j, hj, hnegup, hctr⟩]
        norm_num
    · rw [ite_eq_right hex]
      have hz1 : (0:ℝ) ≤ (if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
          historyCounter v T j ω ≤ V j then 1 else 0) :=
        ite_nonneg (by norm_num) (by norm_num)
      have hz2 : (0:ℝ) ≤ (if ∃ j ≤ T, r j ≤ -historyAdditive g T j ω ∧
          historyCounter v T j ω ≤ V j then 1 else 0) :=
        ite_nonneg (by norm_num) (by norm_num)
      linarith
  -- second summand: rewrite −S additive as negated functional
  have hsum : pmfMean (historyLaw initial K T T)
      (fun ω => (if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0)
          + (if ∃ j ≤ T, r j ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0))
      = pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0)
        + pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T,
            r j ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0) := by
    rw [pmfMean_add]
    congr 1
    · refine pmfMean_congr _ (fun ω _ => ?_)
      have hj : ∀ j, historyAdditive (fun k a b => -g k a b) T j ω
          = -historyAdditive g T j ω := fun j => by
        unfold historyAdditive
        rw [← Finset.sum_neg_distrib]
      simp only [hj]
  calc pmfMean (historyLaw initial K T T)
        (fun ω => if ∃ j ≤ T, r j ≤ |historyAdditive g T j ω| ∧
          historyCounter v T j ω ≤ V j then 1 else 0)
      ≤ pmfMean (historyLaw initial K T T)
          (fun ω => (if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
              historyCounter v T j ω ≤ V j then (1:ℝ) else 0)
            + (if ∃ j ≤ T, r j ≤ -historyAdditive g T j ω ∧
              historyCounter v T j ω ≤ V j then (1:ℝ) else 0)) := hsplit
    _ = pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0)
        + pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T,
            r j ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0) := hsum
    _ ≤ ∑ j ∈ Finset.range (T+1),
          Real.exp (-(r j)^2/(4*(V j + c * r j)))
        + ∑ j ∈ Finset.range (T+1),
          Real.exp (-(r j)^2/(4*(V j + c * r j))) :=
        add_le_add
          (anytime_freedman_thresholds initial K g v T c hc
            hbounded hmean hvar r V hr hV)
          (anytime_freedman_thresholds initial K
            (fun k a b => -g k a b) v T c hc hbounded' hmean' hvar'
            r V hr hV)
    _ = 2 * ∑ j ∈ Finset.range (T+1),
          Real.exp (-(r j)^2/(4*(V j + c * r j))) := by ring

end Hagi.Probability

namespace Hagi
export Hagi.Probability (history_additive_freedman_two_sided
  anytime_freedman_thresholds_two_sided)
end Hagi

