/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: HAGI_v2 formalization team
-/
import Hagi.Contracts.AuditLedger
import Hagi.Cert.StepGen

/-!
# Continual-learning forgetting control bound (C327, rank item c)

Continual-learning contract: NEW tasks arrive, the router/system
adapts (sleeping experts C325 compete on awake rounds — the GAIN
side, NOT claimed here), and the question is what bounds the HARM
to OLD tasks. The answer is TWO INDEPENDENT CHANNELS:

* **Construction channel (deterministic, free)**: a trajectory of
  certified adaptations is a `Hagi.Cert.CertStepGen` sequence, and
  the kernel FLOOR FIELD LAW (`floorsKept` field, C278) keeps every
  obligation floor at each post-state — by construction, with NO
  probability budget. `floorsKept_trajectory` transports this field
  law to whole trajectories: floors are CARRIED, not telescoped
  (the kernel law is a per-step field — which is exactly why this
  channel costs nothing).
* **Audit channel (statistical, budgeted)**: harm events `Bad t`
  (a repeat-task floor MEASUREMENT falsely reporting harm) are
  covered by the spent α of task t in the C274 ledger. Over a
  sequence of m accepted adaptations each spending its slice δₖ,
  the chained ledger `auditSpendChain` has total spend
  ∑ spent₀ + ∑ₖ δₖ (δ-SPLIT arithmetic), so
  `continual_forgetting_bound` gives
  P(∃ t, Bad t) ≤ ∑ spent₀ + ∑ₖ δₖ ≤ δtotal — the master
  (C264 `gate_pipeline_false_commit`) applied at δ := the SPENT
  total, the sharper honest form. "New task adaptation" is just
  another audited proposal: the same audit bound covers it.

`floor_floor_telescope` packages the two-channel guarantee as THE
continual-learning contract. Honest scope (pinned):

* NO bound on the GAIN side (C320/C325 territory, cited not
  imported); NO adaptive-adversary claim (fixed `Bad` events — the
  oblivious C264 union form); floors are PREMISE-valued metrics
  (how a floor was measured stays with CertifiedEstimator —
  `audit_alpha_spends_radius` is the radius bridge, cited not
  re-proved); NO new concentration math — the contribution is the
  continual packaging, the δ-split bookkeeping lemma, and the
  construction channel (challenge-pin resolution, plan-review A1).

Canary-ramp exposure bounding (C324 `canary_ramp_harm_bound`,
`canary_step_certified` — a ramp step IS a CertStepGen) is the
mechanism that turns an adaptation into a certified step entering
channel 1; premise-cited as in C324, not imported (Deployment layer).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Learning.ContinualForgetting

open Finset Hagi.Probability

variable {σ ι : Type} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]

/-! ## Chained α-spending over a sequence of adaptations -/

/-- The ledger after m accepted adaptations: adaptation k spends its
slice α k on task `tsk k`. Single-update form of a chain of C274
`auditSpend` steps (spent is the pointwise sum of the slices); the
validity hypotheses are the SEQUENCE-lift of the one-step C274
precondition (`audit_consume_alpha_valid`): slices nonnegative and
their total inside the remaining budget. Streams, floors, rejected
count and the final-test bookkeeping are untouched — spending does
not consume samples (rejected-candidate consumption is a separate
C274 operation). -/
def auditSpendChain (L : Hagi.Contracts.AuditLedger.AuditLedger σ ι)
    (tsk : ℕ → ι) (α : ℕ → ℝ) (m : ℕ)
    (hα : ∀ k ∈ Finset.range m, 0 ≤ α k)
    (hle : ∑ k ∈ Finset.range m, α k ≤ L.δtotal - ∑ u, L.spent u) :
    Hagi.Contracts.AuditLedger.AuditLedger σ ι where
  δtotal := L.δtotal
  streams := L.streams
  floors := L.floors
  spent := fun u => L.spent u + ∑ k ∈ Finset.range m,
    (if u = tsk k then α k else 0)
  rejected := L.rejected
  finalTest := L.finalTest
  finalLo := L.finalLo
  finalHi := L.finalHi
  streamsDisjoint := L.streamsDisjoint
  spentNonneg := by
    intro u
    have h1 : 0 ≤ ∑ k ∈ Finset.range m, (if u = tsk k then α k else 0) := by
      apply Finset.sum_nonneg
      intro k hk'
      by_cases h : u = tsk k <;> simp [h]
      · exact hα k hk'
    linarith [L.spentNonneg u]
  spentTotal := by
    have hswap : ∑ u ∈ Finset.univ, ∑ k ∈ Finset.range m,
        (if u = tsk k then α k else 0) = ∑ k ∈ Finset.range m, α k := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Finset.sum_ite_eq' Finset.univ (tsk k) (fun _ => α k)]
    rw [Finset.sum_add_distrib, hswap]
    linarith [L.spentTotal]
  finalIsolated := L.finalIsolated

/-- δ-SPLIT ARITHMETIC (the forgetting budget telescope): the
chained ledger's total spend is the initial spend plus the slices —
∑_u ∑_k [u = tsk k]·α k = ∑_k α k, because every task index of the
sequence is a task of the ledger. This is the bookkeeping lemma
C274 does not have (its master is single-snapshot). -/
theorem auditSpendChain_delta_split
    (L : Hagi.Contracts.AuditLedger.AuditLedger σ ι) (tsk : ℕ → ι)
    (α : ℕ → ℝ) (m : ℕ)
    (hα : ∀ k ∈ Finset.range m, 0 ≤ α k)
    (hle : ∑ k ∈ Finset.range m, α k ≤ L.δtotal - ∑ u, L.spent u) :
    ∑ u, (auditSpendChain L tsk α m hα hle).spent u
      = (∑ u, L.spent u) + ∑ k ∈ Finset.range m, α k := by
  have hswap : ∑ u ∈ Finset.univ, ∑ k ∈ Finset.range m,
      (if u = tsk k then α k else 0) = ∑ k ∈ Finset.range m, α k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Finset.sum_ite_eq' Finset.univ (tsk k) (fun _ => α k)]
  change ∑ u ∈ Finset.univ, (L.spent u + ∑ k ∈ Finset.range m,
      (if u = tsk k then α k else 0))
    = (∑ u, L.spent u) + ∑ k ∈ Finset.range m, α k
  rw [Finset.sum_add_distrib, hswap]

/-! ## Channel 2: the audit bound (forgetting control) -/

/-- MAIN 1 — continual forgetting control: over m accepted
adaptations, each audited with its slice δₖ from the ledger, the
probability that SOME old task's floor is falsely harmed is at most
the total spent budget ∑ spent₀ + ∑ₖ δₖ, which stays inside
δtotal. "New task adaptation" is an audited proposal like any
other: the C264 master (`gate_pipeline_false_commit`) applies at
δ := the SPENT total — sharper than C274's δtotal form — plus
complement algebra (`prodPq_compl`, `prodPq_iff`). The premise
`htail` (P(Bad t) ≤ spent t) is the e-process tail premise of the
C274 master; the radius that justifies a spend is
`audit_alpha_spends_radius` (cited, not re-proved). NO new union
mathematics is derived. -/
theorem continual_forgetting_bound {V : Type} [Fintype V] [Nonempty V]
    {n : ℕ} (L : Hagi.Contracts.AuditLedger.AuditLedger σ ι)
    (tsk : ℕ → ι) (δ : ℕ → ℝ) (m : ℕ)
    (hδ : ∀ k ∈ Finset.range m, 0 ≤ δ k)
    (hle : ∑ k ∈ Finset.range m, δ k ≤ L.δtotal - ∑ u, L.spent u)
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (Bad : ι → (Fin n → V) → Prop) [∀ t, DecidablePred (Bad t)]
    [DecidablePred (fun ω => ∃ t ∈ (Finset.univ : Finset ι), Bad t ω)]
    (htail : ∀ t, prodPq p (Bad t)
      ≤ (auditSpendChain L tsk δ m hδ hle).spent t) :
    prodPq p (fun ω => ∃ t ∈ (Finset.univ : Finset ι), Bad t ω)
      ≤ (∑ u, L.spent u) + ∑ k ∈ Finset.range m, δ k
      ∧ (∑ u, L.spent u) + ∑ k ∈ Finset.range m, δ k ≤ L.δtotal := by
  classical
  set Lc := auditSpendChain L tsk δ m hδ hle with hLc
  have hsplit := auditSpendChain_delta_split L tsk δ m hδ hle
  have hmaster := Hagi.Contracts.GatePipeline.gate_pipeline_false_commit
    p hp Bad Lc.spent htail (le_refl _)
  have hcompl := prodPq_compl p hp
    (fun ω => ∀ t ∈ (Finset.univ : Finset ι), ¬ Bad t ω)
  have heq : prodPq p (fun ω => ∃ t ∈ (Finset.univ : Finset ι), Bad t ω)
      = 1 - prodPq p (fun ω => ∀ t ∈ (Finset.univ : Finset ι), ¬ Bad t ω) := by
    rw [prodPq_iff p (fun ω => ∃ t ∈ (Finset.univ : Finset ι), Bad t ω)
      (fun ω => ¬ ∀ t ∈ (Finset.univ : Finset ι), ¬ Bad t ω)
      (fun ω => by
        constructor
        · rintro ⟨t, hm, hb⟩ hcall
          exact hcall t hm hb
        · intro h
          exact Classical.byContradiction
            (fun hcall => h (fun t hm hb => hcall ⟨t, hm, hb⟩)))]
    rw [hcompl]
  rw [heq]
  constructor
  · linarith [hsplit]
  · linarith [L.spentTotal, hsplit]

/-! ## Channel 1: the construction channel (kernel floor field law) -/

/-- Channel 1: the CertStepGen floor FIELD LAW carries all
obligation floors along a trajectory of certified adaptations —
the last certificate's `floorsKept` field is the guarantee at the
terminal state (floors are carried, not telescoped: the kernel law
is a per-step field, which is why this channel is free). -/
theorem floorsKept_trajectory {S TaskId : Type}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId) (deltaLevel : S → ℝ)
    (n : ℕ) (t : ℕ → S) (h₀ : Hagi.Cert.FloorsKept M obl (t 0))
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (t j) (t (j + 1))) :
    Hagi.Cert.FloorsKept M obl (t n) := by
  match n with
  | 0 => exact h₀
  | m + 1 => exact (steps m).floorsKept

/-! ## THE contract: two-channel guarantee -/

/-- MAIN 2 — the continual-learning contract: after n certified
state transitions (channel 1) and m audited task adaptations each
spending δₖ (channel 2), the terminal state keeps every obligation
floor BY CONSTRUCTION (no budget spent), while the probability of
a falsely-harmed old-task floor MEASUREMENT is bounded by the
exactly-spent budget ∑ spent₀ + ∑ₖ δₖ ≤ δtotal. The channels are
complementary, not redundant: construction keeps the premise-valued
floor metrics; the audit pays for the measurement noise that
construction cannot see. -/
theorem floor_floor_telescope {S TaskId : Type}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId) (deltaLevel : S → ℝ)
    (n : ℕ) (t : ℕ → S) (h₀ : Hagi.Cert.FloorsKept M obl (t 0))
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (t j) (t (j + 1)))
    {V : Type} [Fintype V] [Nonempty V] {n' : ℕ}
    (L : Hagi.Contracts.AuditLedger.AuditLedger σ ι)
    (tsk : ℕ → ι) (δ : ℕ → ℝ) (m : ℕ)
    (hδ : ∀ k ∈ Finset.range m, 0 ≤ δ k)
    (hle : ∑ k ∈ Finset.range m, δ k ≤ L.δtotal - ∑ u, L.spent u)
    (p : Fin n' → V → ℝ) (hp : IsProbSys p)
    (Bad : ι → (Fin n' → V) → Prop) [∀ t', DecidablePred (Bad t')]
    [DecidablePred (fun ω => ∃ t' ∈ (Finset.univ : Finset ι), Bad t' ω)]
    (htail : ∀ t', prodPq p (Bad t')
      ≤ (auditSpendChain L tsk δ m hδ hle).spent t') :
    Hagi.Cert.FloorsKept M obl (t n)
      ∧ prodPq p (fun ω => ∃ t' ∈ (Finset.univ : Finset ι), Bad t' ω)
        ≤ (∑ u, L.spent u) + ∑ k ∈ Finset.range m, δ k
      ∧ (∑ u, L.spent u) + ∑ k ∈ Finset.range m, δ k ≤ L.δtotal := by
  obtain ⟨hb1, hb2⟩ :=
    continual_forgetting_bound L tsk δ m hδ hle p hp Bad htail
  exact ⟨floorsKept_trajectory M obl deltaLevel n t h₀ steps, hb1, hb2⟩

/-! ## Anchors: 2 tasks, 2 adaptations, δ-split arithmetic -/

namespace Anchor

open Hagi.Contracts.AuditLedger

/-- Anchor ledger: one empty stream, two tasks, δtotal = 1/2, no
initial spend (the final-test interval [1, 2) is disjoint from the
empty stream [0, 0)). -/
noncomputable def anchorLedger : AuditLedger (Fin 1) (Fin 2) where
  δtotal := 1 / 2
  streams := fun _ => ⟨0, 0, 0, by norm_num, by norm_num⟩
  floors := fun _ => 0
  spent := fun _ => 0
  rejected := 0
  finalTest := false
  finalLo := 1
  finalHi := 2
  streamsDisjoint := by
    intro u v huv
    exact absurd (Subsingleton.elim u v) huv
  spentNonneg := by intro _; norm_num
  spentTotal := by norm_num
  finalIsolated := by
    intro _ _
    left
    norm_num

/-- Anchor task sequence: adaptation 0 audits task 0, adaptation 1
audits task 1. -/
noncomputable def atask : ℕ → Fin 2 := fun k => if k = 0 then 0 else 1

/-- Anchor δ-slices: 1/8 for adaptation 0, 1/16 for adaptation 1. -/
noncomputable def adelta : ℕ → ℝ := fun k => if k = 0 then 1 / 8 else 1 / 16

/-- The chained anchor ledger (both adaptations accepted). -/
noncomputable def achain : AuditLedger (Fin 1) (Fin 2) :=
  auditSpendChain anchorLedger atask adelta 2
    (by intro k _; by_cases h : k = 0 <;> simp [adelta, h])
    (by simp [adelta, anchorLedger, Finset.sum_range_succ]; norm_num)

/-- Anchor δ-split: task 0's spend is exactly its slice 1/8, task
1's exactly 1/16 — the per-task indicator sums separate. -/
theorem forgetting_anchor_split :
    achain.spent 0 = 1 / 8 ∧ achain.spent 1 = 1 / 16 := by
  constructor
  · simp only [achain, auditSpendChain, anchorLedger, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, atask, adelta]
    norm_num
  · simp only [achain, auditSpendChain, anchorLedger, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, atask, adelta]
    norm_num

/-- Anchor total: the chained budget telescopes to 1/8 + 1/16 =
3/16 ≤ δtotal = 1/2, and task 0's per-task remainder stays
nonnegative — all through the MAIN chain lemma, not bare norm_num
on the right-hand side. -/
theorem forgetting_anchor_total :
    ∑ u, achain.spent u = 3 / 16
      ∧ 3 / 16 ≤ anchorLedger.δtotal
      ∧ 0 ≤ remainingOf achain 0 := by
  have h := auditSpendChain_delta_split anchorLedger atask adelta 2
    (by intro k _; by_cases h' : k = 0 <;> simp [h', adelta])
    (by simp [adelta, anchorLedger, Finset.sum_range_succ]; norm_num)
  have hs := forgetting_anchor_split
  constructor
  · simp only [achain, auditSpendChain, anchorLedger, adelta,
      Fin.sum_univ_two, Finset.sum_range_succ, Finset.sum_range_zero,
      atask, zero_add, add_zero] at h ⊢
    norm_num at h ⊢
  · constructor
    · simp only [anchorLedger]
      norm_num
    · unfold remainingOf
      rw [hs.1]
      simp only [achain, auditSpendChain, anchorLedger]
      norm_num

end Anchor

end Hagi.Learning.ContinualForgetting
