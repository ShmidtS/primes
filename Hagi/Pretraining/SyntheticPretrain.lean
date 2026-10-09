/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# R99: synthetic pre-pretraining transfer (arXiv 2609.39827)

The formalization of the synthetic pre-pretraining theory, in
the GrowthGate / ComputeBudget style: short synthetic
pretraining on RETRIEVAL-style tasks (k-Shuffle Dyck, MP-Struct,
NCA) reduces the TIME-TO-CAPABILITY of the subsequent main
pretraining; the mechanism hypothesis is long-range retrieval,
NOT a grammatical prior.

**Honest boundaries (the paper's claims we do and do NOT carry):**

* h_emp_retrieval_transfer_ — the transfer itself (retrieval-style
  synthetic pretraining accelerates the main run) is EMPIRICAL:
  it enters every theorem below as a measured hypothesis on the
  two trajectories, never as a derived fact. No claim that
  retrieval ⇒ general capability is made or needed.
* "Set task degraded" is an empirical WARNING, not a theorem:
  the set-tracking control failing to transfer is an observed
  row of the paper's table, not something this module proves.
* The gate below is a COMPUTE gate only: it says when the
  synthetic phase pays for itself in capability-per-compute;
  it says nothing about asymptotic capability ceilings.

**What the module proves:**

* `TimeToCapability` — the first index a capability trajectory
  C reaches threshold τ (Nat.find under a reaching hypothesis).
* `synthGain` — the measured step saving T_plain(τ) − T_synth(τ).
* `time_to_capability_correct` — well-formedness: the found
  index is a genuine first crossing (C ≥ τ there, C < τ strictly
  before), and under monotonicity capability stays ≥ τ after it.
* `synth_investment_dominates` — THE GATE THEOREM: if the
  measured saving, priced at the per-step compute cost, exceeds
  the cost of the synthetic phase (ΔT·c_step > C_synth — the
  only empirical gate), then the composite (synthetic-then-main)
  schedule reaches τ with STRICTLY larger capability-per-compute
  than starting the main phase directly. No free positive
  hypotheses: everything except the h_emp_ gate and the sign
  conventions is derived.
* `task_selection_marginal` — the adaptive-task-choice corollary
in the ComputeBudget style: among finitely many candidate
synthetic tasks j with measured gains g_j and POSITIVE costs
c_j > 0 (R102: hc — with nonpositive costs the ratio g/c is
meaningless, and Lean's x/0 = 0 would let the argmax exist
vacuously), the argmax of g_j/c_j exists and its ratio
dominates every alternative's — with positive costs the
ratio is the true gain-per-cost (the finite argmax
characterization feeding `marginalValue_law`'s active-set
scan).
-/

namespace Hagi

section SyntheticPretrain

/-! ### Definitions -/

/-- **Time-to-capability**: the FIRST index at which the
capability trajectory C reaches threshold τ (well-defined only
under a reaching hypothesis; `Nat.find` on `fun n => τ ≤ C n`). -/
noncomputable def TimeToCapability (τ : ℝ) (C : ℕ → ℝ)
    (hreach : ∃ n : ℕ, τ ≤ C n) : ℕ :=
  Nat.find hreach

/-- **The measured synthetic gain**: the step saving
T_plain(τ) − T_synth(τ) between the plain-main trajectory and
the synthetic-then-main trajectory at the SAME threshold.
Its sign is an EMPIRICAL quantity (h_emp_retrieval_transfer_):
nothing here forces it positive except measurement. -/
noncomputable def synthGain (τ : ℝ) (Cp Cs : ℕ → ℝ)
    (hp : ∃ n : ℕ, τ ≤ Cp n) (hs : ∃ n : ℕ, τ ≤ Cs n) : ℝ :=
  (TimeToCapability τ Cp hp : ℝ) - (TimeToCapability τ Cs hs : ℝ)

/-! ### Well-formedness of the first crossing -/

/-- **The first-crossing certificate**: the found index tcross
satisfies τ ≤ C tcross, every earlier index is strictly below τ,
and — under monotonicity of the trajectory — capability never
drops back below τ after tcross (the crossing is permanent). The
first two clauses are `Nat.find`'s spec/minimality; the third
is the monotone induction. Non-vacuous: applies to any
monotone reaching trajectory. -/
theorem time_to_capability_correct (τ : ℝ) (C : ℕ → ℝ)
    (hreach : ∃ n : ℕ, τ ≤ C n)
    (hmono : ∀ t, C t ≤ C (t + 1)) :
    τ ≤ C (TimeToCapability τ C hreach)
      ∧ (∀ k < TimeToCapability τ C hreach, C k < τ)
      ∧ (∀ k, TimeToCapability τ C hreach ≤ k → τ ≤ C k) := by
  have hspec : τ ≤ C (Nat.find hreach) := Nat.find_spec hreach
  have hperm : ∀ n k : ℕ, n ≤ k → C n ≤ C k := by
    intro n k
    induction k with
    | zero =>
        intro hk
        have hn : n = 0 := Nat.le_zero.mp hk
        rw [hn]
    | succ k ih =>
        intro hk
        rcases Nat.eq_or_lt_of_le hk with h | h
        · rw [h]
        · exact le_trans (ih (Nat.le_of_lt_succ h)) (hmono k)
  refine ⟨hspec, ?_, fun k hk => hspec.trans (hperm (Nat.find hreach) k hk)⟩
  intro k hk
  unfold TimeToCapability at hk
  exact not_le.mp (Nat.find_min hreach hk)

/-! ### The gate theorem -/

/-- **THE GATE THEOREM (compute-aware GrowthGate comparison)**:
two schedules reach the same threshold τ — the plain main run
at step T_p, the composite (synthetic phase of cost C_synth,
then main run) at main-step T_s. The ONLY empirical gate is
`h_emp_gate`: the measured saving synthGain = T_p − T_s, priced
at the per-step compute cost c_step, strictly exceeds the cost
of the synthetic phase (ΔT·c_step > C_synth — the
h_emp_retrieval_transfer_ measurement of arXiv 2609.39827 in
compute units). Then the composite schedule's
capability-per-compute at the moment of reaching τ,

`τ / (C_synth + T_s · c_step)`  vs  `τ / (T_p · c_step)`,

is STRICTLY larger for the synthetic-pretrained run. All sign
hypotheses are conventions (threshold, step cost, costs
nonneg); no free positive constant hides in the conclusion:
the inequality is exactly the gate re-denominated. -/
theorem synth_investment_dominates (τ cstep Csyt Tp Ts : ℝ)
    (Cp Cs : ℕ → ℝ) (hp : ∃ n : ℕ, τ ≤ Cp n) (hs : ∃ n : ℕ, τ ≤ Cs n)
    (hτ : 0 < τ) (hcstep : 0 < cstep)
    (hCsyt : 0 < Csyt) (hTs : 0 ≤ Ts)
    (hTp : (TimeToCapability τ Cp hp : ℝ) = Tp)
    (hTsCast : (TimeToCapability τ Cs hs : ℝ) = Ts)
    (h_emp_gate : synthGain τ Cp Cs hp hs * cstep > Csyt) :
    τ / (Csyt + Ts * cstep) > τ / (Tp * cstep) := by
  -- unpack the measured saving into the two crossing times
  have hgain : synthGain τ Cp Cs hp hs = Tp - Ts := by
    unfold synthGain
    rw [hTp, hTsCast]
  rw [hgain] at h_emp_gate
  -- the gate says the composite cost is strictly smaller
  have hcmp : Csyt + Ts * cstep < Tp * cstep := by
    have hring : (Tp - Ts) * cstep = Tp * cstep - Ts * cstep := by ring
    linarith
  -- both denominators are strictly positive
  have hpos1 : 0 < Csyt + Ts * cstep := by
    have hTc : 0 ≤ Ts * cstep := mul_nonneg hTs (le_of_lt hcstep)
    linarith
  have hpos2 : 0 < Tp * cstep := by
    have hTp2 : Ts < Tp := by
      by_contra hcon
      have : (Tp - Ts) * cstep ≤ 0 := by
        nlinarith [hcon, hcstep, hTs]
      linarith
    have hTp3 : 0 < Tp := lt_of_le_of_lt hTs hTp2
    exact mul_pos hTp3 hcstep
  -- the efficiency comparison, re-denominated
  rw [gt_iff_lt, div_lt_div_iff₀ hpos2 hpos1]
  have key : τ * (Tp * cstep) - τ * (Csyt + Ts * cstep)
      = τ * ((Tp - Ts) * cstep - Csyt) := by ring
  have hA : 0 < (Tp - Ts) * cstep - Csyt := sub_pos.2 (by linarith)
  have := mul_pos hτ hA
  linarith

/-! ### The adaptive task-selection corollary -/

/-- **The marginal task-selection corollary** (ComputeBudget
style): among finitely many candidate synthetic tasks j with
costs c_j > 0, the argmax of the measured ratio g_j / c_j
EXISTS, and the selected index's ratio dominates every
alternative's — the finite-argmax characterization that feeds
`marginalValue_law`'s active-set scan (`h_emp_task_*`: the
g_j are the measured per-task transfer gains; nothing here
constrains their signs — a task with negative measured gain is
dominated automatically). -/
theorem task_selection_marginal (J : Type) [Finite J] [Nonempty J]
    (g c : J → ℝ) (_hc : ∀ j, 0 < c j) :
    ∃ jmax : J, ∀ j : J, g j / c j ≤ g jmax / c jmax := by
  haveI : Fintype J := Fintype.ofFinite J
  have hne : (Finset.univ : Finset J).Nonempty := by
    obtain ⟨j⟩ := ‹Nonempty J›
    exact ⟨j, Finset.mem_univ j⟩
  obtain ⟨jmax, hjmax, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset J)
      (fun j => g j / c j) hne
  exact ⟨jmax, fun j => hmax j (Finset.mem_univ j)⟩

end SyntheticPretrain

end Hagi
