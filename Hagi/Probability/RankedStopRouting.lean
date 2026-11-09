/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.MarkovPathSupport

/-!
# Bounded terminal hitting for directed ranked-stop kernels

This isolated candidate adapts the canonical `map`/`bind` support induction
from `Hagi.Probability.MarkovPathSupport` in the reverse direction.  A plain
directed relation, strict rank progress on every nonterminal supported row,
and explicit pure terminal stops imply terminal at the rank-budget coordinate
of every supported full history.  No initial rank-zero premise is needed.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Probability.RankedStopRouting

open Hagi.Probability

universe u

variable {α : Type u}

/-- Full-law support gives the supported initial state and each actual
transition through the recorded prefix. -/
theorem start_and_steps_of_historyLaw_support
    (initial : PMF α) (K : ℕ → α → PMF α)
    {T k : ℕ} (hk : k ≤ T) (ω : History α T)
    (hω : ω ∈ (historyLaw initial K T k).support) :
    ω (historyIndex T 0) ∈ initial.support ∧
      ∀ j < k,
        ω (historyIndex T (j + 1)) ∈
          (K j (ω (historyIndex T j))).support := by
  induction k generalizing ω with
  | zero =>
      change ω ∈ (historyInitial initial T).support at hω
      rw [historyInitial] at hω
      obtain ⟨a, ha, hωa⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
      constructor
      · have h0 := congrFun hωa (historyIndex T 0)
        rw [← h0]
        exact ha
      · intro j hj
        omega
  | succ k ih =>
      have hkT : k < T := by omega
      change ω ∈
        ((historyLaw initial K T k).bind (historyKernel K T k)).support at hω
      obtain ⟨π, hπ, hkernel⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
      rw [historyKernel, ite_eq_left hkT] at hkernel
      obtain ⟨b, hb, hupdate⟩ := (PMF.mem_support_map_iff _ _ _).mp hkernel
      obtain ⟨hstart, hsteps⟩ := ih (by omega) π hπ
      constructor
      · rw [← hupdate,
          Function.update_of_ne (historyIndex_ne_succ (Nat.zero_le k) hkT)]
        exact hstart
      · intro j hj
        by_cases hjk : j < k
        · rw [← hupdate,
            Function.update_of_ne
              (historyIndex_ne_succ (by omega : j + 1 ≤ k) hkT),
            Function.update_of_ne (historyIndex_ne_succ hjk.le hkT)]
          exact hsteps j hjk
        · have hjk' : j = k := by omega
          subst j
          rw [← hupdate, Function.update_self,
            Function.update_of_ne (historyIndex_ne_succ le_rfl hkT)]
          exact hb

/-- Normalization and strict supported-rank progress rule out a nonterminal
state at the maximum rank. -/
theorem nonterminal_rank_lt
    (K : ℕ → α → PMF α) (R : α → α → Prop)
    (terminal : α → Prop) (rank : α → ℕ) (B : ℕ)
    (hbound : ∀ a, rank a ≤ B)
    (hstep : ∀ t a, ¬ terminal a →
      ∀ b ∈ (K t a).support, R a b ∧ rank a < rank b)
    {a : α} (ha : ¬ terminal a) : rank a < B := by
  obtain ⟨b, hb⟩ := (K 0 a).support_nonempty
  have hrank := (hstep 0 a ha b hb).2
  have hb' := hbound b
  omega

/-- Every supported full history is terminal at its rank-budget coordinate.
The base of the induction uses only `0 ≤ rank`, not an initial rank-zero
assumption. -/
theorem terminal_at_rankBudget_of_historyLaw_support
    (initial : PMF α) (K : ℕ → α → PMF α)
    (R : α → α → Prop) (terminal : α → Prop) (rank : α → ℕ)
    (B T : ℕ) (hBT : B ≤ T)
    (hbound : ∀ a, rank a ≤ B)
    (hstop : ∀ t a, terminal a → K t a = PMF.pure a)
    (hstep : ∀ t a, ¬ terminal a →
      ∀ b ∈ (K t a).support, R a b ∧ rank a < rank b)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T T).support) :
    terminal (ω (historyIndex T B)) := by
  obtain ⟨_, hsteps⟩ := start_and_steps_of_historyLaw_support
    initial K le_rfl ω hω
  have hprogress : ∀ j < T, terminal (ω (historyIndex T j)) →
      terminal (ω (historyIndex T (j + 1))) := by
    intro j hj ht
    have hnext := hsteps j hj
    rw [hstop j _ ht, PMF.mem_support_pure_iff] at hnext
    rw [hnext]
    exact ht
  have hinvariant : ∀ j ≤ B,
      terminal (ω (historyIndex T j)) ∨ j ≤ rank (ω (historyIndex T j)) := by
    intro j
    induction j with
    | zero =>
        intro _
        exact Or.inr (Nat.zero_le _)
    | succ j ih =>
        intro hjB
        have hjT : j < T := by omega
        by_cases ht : terminal (ω (historyIndex T j))
        · exact Or.inl (hprogress j hjT ht)
        · have hnext := hsteps j hjT
          have hrank := (hstep j _ ht _ hnext).2
          rcases ih (by omega) with ht' | hr
          · exact (ht ht').elim
          · exact Or.inr (by omega)
  by_cases ht : terminal (ω (historyIndex T B))
  · exact ht
  · have hlt := nonterminal_rank_lt K R terminal rank B hbound hstep ht
    rcases hinvariant B le_rfl with ht' | hge
    · exact ht'
    · omega

/-- Existential bounded-hit form of terminality at the budget coordinate. -/
theorem exists_terminal_le_of_historyLaw_support
    (initial : PMF α) (K : ℕ → α → PMF α)
    (R : α → α → Prop) (terminal : α → Prop) (rank : α → ℕ)
    (B T : ℕ) (hBT : B ≤ T)
    (hbound : ∀ a, rank a ≤ B)
    (hstop : ∀ t a, terminal a → K t a = PMF.pure a)
    (hstep : ∀ t a, ¬ terminal a →
      ∀ b ∈ (K t a).support, R a b ∧ rank a < rank b)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T T).support) :
    ∃ j ≤ B, terminal (ω (historyIndex T j)) :=
  ⟨B, le_rfl, terminal_at_rankBudget_of_historyLaw_support
    initial K R terminal rank B T hBT hbound hstop hstep ω hω⟩

/-- A larger recorded budget is also terminal: weaken the same rank cap to
its later coordinate and apply the budget theorem again. -/
theorem terminal_at_later_budget_of_historyLaw_support
    (initial : PMF α) (K : ℕ → α → PMF α)
    (R : α → α → Prop) (terminal : α → Prop) (rank : α → ℕ)
    (L H T : ℕ) (hLH : L ≤ H) (hHT : H ≤ T)
    (hbound : ∀ a, rank a ≤ L)
    (hstop : ∀ t a, terminal a → K t a = PMF.pure a)
    (hstep : ∀ t a, ¬ terminal a →
      ∀ b ∈ (K t a).support, R a b ∧ rank a < rank b)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T T).support) :
    terminal (ω (historyIndex T H)) :=
  terminal_at_rankBudget_of_historyLaw_support initial K R terminal rank H T hHT
    (fun a => (hbound a).trans hLH) hstop hstep ω hω

/-- The exact bounded-hit event has outer mass one, by support inclusion. -/
theorem historyLaw_ranked_hitBy_eq_one
    (initial : PMF α) (K : ℕ → α → PMF α)
    (R : α → α → Prop) (terminal : α → Prop) (rank : α → ℕ)
    (L T : ℕ) (hLT : L ≤ T)
    (hbound : ∀ a, rank a ≤ L)
    (hstop : ∀ t a, terminal a → K t a = PMF.pure a)
    (hstep : ∀ t a, ¬ terminal a →
      ∀ b ∈ (K t a).support, R a b ∧ rank a < rank b) :
    (historyLaw initial K T T).toOuterMeasure
      {ω | ∃ j ≤ L, terminal (ω (historyIndex T j))} = 1 := by
  apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
  intro ω hω
  exact exists_terminal_le_of_historyLaw_support
    initial K R terminal rank L T hLT hbound hstop hstep ω hω

/-- Accepted outcomes of the raw-row classifier. -/
inductive RoutingOutcome (α : Type u) where
  | Arrived (endpoint : α)
  | Hold
  | Unknown

/-- A raw terminal step is explicitly pure; a raw nonterminal step must come
from an actual row and satisfy both directedness and strict rank progress. -/
def StepOKAt (rows : ℕ → α → Option (PMF α)) (R : α → α → Prop)
    (terminal : α → Prop) (rank : α → ℕ) (t : ℕ) (a b : α) : Prop :=
  (terminal a ∧ b = a ∧ rows t a = some (PMF.pure a)) ∨
    (¬ terminal a ∧ ∃ p, rows t a = some p ∧ b ∈ p.support ∧
      R a b ∧ rank a < rank b)

/-- Validity of the recorded raw prefix through coordinate `k`. -/
def PrefixOKAt (rows : ℕ → α → Option (PMF α)) (R : α → α → Prop)
    (terminal : α → Prop) (rank : α → ℕ) (T k : ℕ) (ω : History α T) : Prop :=
  ∀ j < k, StepOKAt rows R terminal rank j
    (ω (historyIndex T j)) (ω (historyIndex T (j + 1)))

/-- A current terminal needs no outgoing row.  A nonterminal row is ready only
when present and all its supported successors satisfy the directed rank guard. -/
def RowReady (rows : ℕ → α → Option (PMF α)) (R : α → α → Prop)
    (terminal : α → Prop) (rank : α → ℕ) (t : ℕ) (a : α) : Prop :=
  terminal a ∨ ∃ p, rows t a = some p ∧
    ∀ b ∈ p.support, R a b ∧ rank a < rank b

/-- Honest routing status: a valid current terminal has priority over budget;
valid continuation is possible only before budget with a ready current row. -/
noncomputable def classifyRouting (rows : ℕ → α → Option (PMF α))
    (R : α → α → Prop) (terminal : α → Prop) (rank : α → ℕ)
    (T k : ℕ) (ω : History α T) : RoutingOutcome α := by
  classical
  exact if terminal (ω (historyIndex T k)) ∧ PrefixOKAt rows R terminal rank T k ω then
    .Arrived (ω (historyIndex T k))
  else if k < T ∧ PrefixOKAt rows R terminal rank T k ω ∧
      RowReady rows R terminal rank k (ω (historyIndex T k)) then
    .Hold
  else
    .Unknown

/-- Valid current terminal reports its actual endpoint. -/
theorem classifyRouting_eq_arrived
    (rows : ℕ → α → Option (PMF α)) (R : α → α → Prop)
    (terminal : α → Prop) (rank : α → ℕ) (T k : ℕ) (ω : History α T)
    (hprefix : PrefixOKAt rows R terminal rank T k ω)
    (ht : terminal (ω (historyIndex T k))) :
    classifyRouting rows R terminal rank T k ω =
      .Arrived (ω (historyIndex T k)) := by
  simp [classifyRouting, hprefix, ht]

/-- A valid nonterminal with budget and a ready row holds. -/
theorem classifyRouting_eq_hold
    (rows : ℕ → α → Option (PMF α)) (R : α → α → Prop)
    (terminal : α → Prop) (rank : α → ℕ) (T k : ℕ) (ω : History α T)
    (hk : k < T) (hprefix : PrefixOKAt rows R terminal rank T k ω)
    (hready : RowReady rows R terminal rank k (ω (historyIndex T k)))
    (ht : ¬ terminal (ω (historyIndex T k))) :
    classifyRouting rows R terminal rank T k ω = .Hold := by
  simp [classifyRouting, hk, hprefix, hready, ht]

/-- Exhausted budget never holds a nonterminal, even if its row is ready. -/
theorem classifyRouting_eq_unknown_of_budget
    (rows : ℕ → α → Option (PMF α)) (R : α → α → Prop)
    (terminal : α → Prop) (rank : α → ℕ) (T k : ℕ) (ω : History α T)
    (hk : ¬ k < T) (ht : ¬ terminal (ω (historyIndex T k))) :
    classifyRouting rows R terminal rank T k ω = .Unknown := by
  simp [classifyRouting, hk, ht]

/-- Invalid input is not repaired into either a positive outcome or an
accidental terminal arrival. -/
theorem classifyRouting_eq_unknown_of_not_prefixOK
    (rows : ℕ → α → Option (PMF α)) (R : α → α → Prop)
    (terminal : α → Prop) (rank : α → ℕ) (T k : ℕ) (ω : History α T)
    (hprefix : ¬ PrefixOKAt rows R terminal rank T k ω) :
    classifyRouting rows R terminal rank T k ω = .Unknown := by
  simp [classifyRouting, hprefix]

/-- A nonterminal missing/invalid current row cannot continue. -/
theorem classifyRouting_eq_unknown_of_not_rowReady
    (rows : ℕ → α → Option (PMF α)) (R : α → α → Prop)
    (terminal : α → Prop) (rank : α → ℕ) (T k : ℕ) (ω : History α T)
    (ht : ¬ terminal (ω (historyIndex T k)))
    (hready : ¬ RowReady rows R terminal rank k (ω (historyIndex T k))) :
    classifyRouting rows R terminal rank T k ω = .Unknown := by
  simp [classifyRouting, hready, ht]

/-- Every prefix of a supported full history is valid for the accepted
normalized rows. -/
theorem prefixOKAt_some_of_historyLaw_support
    (initial : PMF α) (K : ℕ → α → PMF α)
    (R : α → α → Prop) (terminal : α → Prop) (rank : α → ℕ)
    {T k : ℕ} (hk : k ≤ T)
    (hstop : ∀ t a, terminal a → K t a = PMF.pure a)
    (hstep : ∀ t a, ¬ terminal a →
      ∀ b ∈ (K t a).support, R a b ∧ rank a < rank b)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T T).support) :
    PrefixOKAt (fun t a => some (K t a)) R terminal rank T k ω := by
  obtain ⟨_, hsteps⟩ := start_and_steps_of_historyLaw_support
    initial K le_rfl ω hω
  intro j hj
  have hnext := hsteps j (by omega)
  by_cases ht : terminal (ω (historyIndex T j))
  · rw [hstop j _ ht, PMF.mem_support_pure_iff] at hnext
    exact Or.inl ⟨ht, hnext, congrArg some (hstop j _ ht)⟩
  · obtain ⟨hR, hrank⟩ := hstep j _ ht _ hnext
    exact Or.inr ⟨ht, K j (ω (historyIndex T j)), rfl, hnext, hR, hrank⟩

/-- Every current normalized row is ready; terminal rows branch without
requiring an outgoing edge. -/
theorem rowReady_some
    (K : ℕ → α → PMF α) (R : α → α → Prop)
    (terminal : α → Prop) (rank : α → ℕ)
    (hstep : ∀ t a, ¬ terminal a →
      ∀ b ∈ (K t a).support, R a b ∧ rank a < rank b)
    (t : ℕ) (a : α) :
    RowReady (fun t a => some (K t a)) R terminal rank t a := by
  by_cases ht : terminal a
  · exact Or.inl ht
  · exact Or.inr ⟨K t a, rfl, hstep t a ht⟩

/-- A terminal coordinate of a supported normalized history classifies as its
actual terminal endpoint. -/
theorem classifyRouting_some_eq_arrived
    (initial : PMF α) (K : ℕ → α → PMF α)
    (R : α → α → Prop) (terminal : α → Prop) (rank : α → ℕ)
    {T k : ℕ} (hk : k ≤ T)
    (hstop : ∀ t a, terminal a → K t a = PMF.pure a)
    (hstep : ∀ t a, ¬ terminal a →
      ∀ b ∈ (K t a).support, R a b ∧ rank a < rank b)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T T).support)
    (ht : terminal (ω (historyIndex T k))) :
    classifyRouting (fun t a => some (K t a)) R terminal rank T k ω =
      .Arrived (ω (historyIndex T k)) :=
  classifyRouting_eq_arrived _ _ _ _ _ _ _
    (prefixOKAt_some_of_historyLaw_support initial K R terminal rank hk hstop hstep ω hω) ht

/-- Before budget, a nonterminal coordinate of a supported normalized history
holds rather than promising future arrival. -/
theorem classifyRouting_some_eq_hold
    (initial : PMF α) (K : ℕ → α → PMF α)
    (R : α → α → Prop) (terminal : α → Prop) (rank : α → ℕ)
    {T k : ℕ} (hk : k < T)
    (hstop : ∀ t a, terminal a → K t a = PMF.pure a)
    (hstep : ∀ t a, ¬ terminal a →
      ∀ b ∈ (K t a).support, R a b ∧ rank a < rank b)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T T).support)
    (ht : ¬ terminal (ω (historyIndex T k))) :
    classifyRouting (fun t a => some (K t a)) R terminal rank T k ω = .Hold :=
  classifyRouting_eq_hold _ _ _ _ _ _ _ hk
    (prefixOKAt_some_of_historyLaw_support initial K R terminal rank hk.le hstop hstep ω hω)
    (rowReady_some K R terminal rank hstep k _) ht

/-- At rank budget, the supported normalized history classifies as arrived. -/
theorem classifyRouting_some_ranked_arrived
    (initial : PMF α) (K : ℕ → α → PMF α)
    (R : α → α → Prop) (terminal : α → Prop) (rank : α → ℕ)
    (L T : ℕ) (hLT : L ≤ T)
    (hbound : ∀ a, rank a ≤ L)
    (hstop : ∀ t a, terminal a → K t a = PMF.pure a)
    (hstep : ∀ t a, ¬ terminal a →
      ∀ b ∈ (K t a).support, R a b ∧ rank a < rank b)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T T).support) :
    classifyRouting (fun t a => some (K t a)) R terminal rank T L ω =
      .Arrived (ω (historyIndex T L)) :=
  classifyRouting_some_eq_arrived initial K R terminal rank hLT hstop hstep ω hω
    (terminal_at_rankBudget_of_historyLaw_support
      initial K R terminal rank L T hLT hbound hstop hstep ω hω)

end Hagi.Probability.RankedStopRouting
