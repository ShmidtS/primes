/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.GPMRelaxed
import Mathlib.Tactic

set_option relaxedAutoImplicit false

/-!
# Hybrid continual mechanism selection (C510, beat C509)

The C509 roadmap top-1: ONE continual loop whose per-step step
mechanism is selected DETERMINISTICALLY from the measured state
(the C509 decision table): span fullness `rank(span A ∪ B) < dim`
(a measurable exact-rational Gram-Schmidt predicate) and the
conflict sign `⟨g, g_old⟩`. The selection is a pure case-on-state;
the SOUNDNESS theorem states that whatever branch is chosen, the
guarantee of THAT branch holds — a disjunction of the three
existing mechanisms with NO weakening:

- full-GPM branch (span not exhausted): the step `g − P·g` is
  exactly orthogonal to every old input in the projected span —
  the exact zero-forgetting face of
  `Hagi.Theory.GPMRelaxed.gpm_full_zero` /
  `Hagi.Step.gpm_zero_forgetting`;
- A-GEM free branch (span exhausted, no conflict): the free step
  keeps non-negative first-order old-interference — the free case
  of `Hagi.Theory.GPMRelaxed.agem_step_nonneg_interf`;
- rank-trunc branch (span exhausted, conflict): the projected
  step satisfies the per-point forgetting bound — the statement
  of `Hagi.Theory.GPMRelaxed.rank_trunc_forgetting_bound`,
  instantiated here with the one-row step matrix.

## Statements

- `proj_compl_orth`: for an orthogonal projector `P` (idempotent
  and symmetric), the complement-projected direction is exactly
  orthogonal to the projected subspace — the shared computation
  behind both the full-GPM and rank-trunc branches.
- `hybrid_step_sound` (main): for every measured state, the
  mechanism selected by `hybridSelect` yields a step satisfying
  the guarantee of the selected branch (match on the selector;
  each branch is the existing theorem instance).

Layer decision: Theory (7) — consumes `Hagi.Theory.GPMRelaxed`
(theory) and cites its three mechanism theorems; consumed by the
C510 bench witness (hybrid-continual mode of `bench_bridge.py`).
-/

namespace Hagi.Theory.HybridContinual

open scoped Matrix
open Hagi.Theory.GPMRelaxed

/-- The three continual mechanisms of the C509 decision table:
full-GPM (exact projection, zero forgetting), A-GEM free step
(no conflict), rank-trunc relaxed GPM (per-point forgetting
bound). -/
inductive HybridMech : Type
  | fullGPM | agemFree | rankTrunc

/-- **hybridSelect (C510, def)**: the deterministic per-step
mechanism selector on the two MEASURED predicates of the C509
decision table — span fullness (`spanFree = rank(span A ∪ B) <
dim`, an exact rational Gram-Schmidt fact) and the conflict sign
`⟨g, g_old⟩`. No randomness, no thresholds beyond the measured
numbers themselves. -/
noncomputable def hybridSelect {n : ℕ} (spanFree : Bool)
    (g g_old : Fin n → ℝ) : HybridMech :=
  if spanFree then HybridMech.fullGPM
  else if 0 ≤ g ⬝ᵥ g_old then HybridMech.agemFree
  else HybridMech.rankTrunc

/-- **hybridStep (C510, def)**: the step direction of each
mechanism. `P` is the orthogonal projector onto the relevant old
subspace (full span of the old task for full-GPM, the kept
top-k directions for rank-trunc); the free A-GEM branch takes
the raw gradient. -/
noncomputable def hybridStep {n : ℕ} (m : HybridMech)
    (g _g_old : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    Fin n → ℝ :=
  match m with
  | HybridMech.fullGPM => g - P *ᵥ g
  | HybridMech.agemFree => g
  | HybridMech.rankTrunc => g - P *ᵥ g

/-- **proj_compl_orth (C510)**: for an orthogonal projector
(`P² = P`, `Pᵀ = P`) the complement-projected direction is
exactly orthogonal to the projected subspace. This single
computation powers both the full-GPM branch (exact zero
interference with every old input in the span) and the
`gpmOrthP` hypothesis of the rank-trunc branch. -/
theorem proj_compl_orth {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P) (hPs : Pᵀ = P) (g v : Fin n → ℝ) :
    (g - P *ᵥ g) ⬝ᵥ (P *ᵥ v) = 0 := by
  have hgl : (g - P *ᵥ g) ⬝ᵥ (P *ᵥ v)
      = g ⬝ᵥ (P *ᵥ v) - (P *ᵥ g) ⬝ᵥ (P *ᵥ v) := by
    rw [sub_dotProduct]
  have hR : (P *ᵥ g) ⬝ᵥ (P *ᵥ v) = g ⬝ᵥ (P *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose,
        Matrix.mulVec_mulVec, hPs, hP]
  rw [hgl, hR, sub_self]

/-- **hybrid_step_sound (C510, main)**: selecting the continual
mechanism by the measured per-step state preserves the guarantee
of the SELECTED branch — a disjunction of the three C509/C498
mechanisms with no weakening. In the full-GPM branch the step is
exactly orthogonal to every old input of the projected span
(zero forgetting, the `gpm_zero_forgetting` face); in the free
A-GEM branch the first-order old-interference is non-negative
(the free case of `agem_step_nonneg_interf`); in the rank-trunc
branch the per-point forgetting bound of
`rank_trunc_forgetting_bound` holds (instantiated by the one-row
step matrix, whose `gpmOrthP` hypothesis is `proj_compl_orth`).
The proof is pure case-on-state. -/
theorem hybrid_step_sound {n : ℕ} (g g_old : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P) (hPs : Pᵀ = P) (spanFree : Bool) :
    match hybridSelect spanFree g g_old with
    | HybridMech.fullGPM =>
        ∀ x : Fin n → ℝ, x = P *ᵥ x →
          hybridStep HybridMech.fullGPM g g_old P ⬝ᵥ x = 0
    | HybridMech.agemFree =>
        0 ≤ hybridStep HybridMech.agemFree g g_old P ⬝ᵥ g_old
    | HybridMech.rankTrunc =>
        ∀ x : Fin n → ℝ,
          |hybridStep HybridMech.rankTrunc g g_old P ⬝ᵥ x|
            ≤ nrm (g - P *ᵥ g) * sigmaTail P x := by
  unfold hybridSelect
  cases spanFree with
  | true =>
    simp only [ite_true]
    intro x hx
    show (g - P *ᵥ g) ⬝ᵥ x = 0
    rw [hx]
    exact proj_compl_orth P hP hPs g x
  | false =>
    by_cases hdot : 0 ≤ g ⬝ᵥ g_old
    · simp only [ite_eq_left hdot]
      exact hdot
    · simp only [ite_eq_right hdot]
      intro x
      have horth : (g - P *ᵥ g) ⬝ᵥ (P *ᵥ x) = 0 :=
        proj_compl_orth P hP hPs g x
      have hgpmOrthP : gpmOrthP
          (Matrix.of fun _ : Fin 1 => (g - P *ᵥ g) :
             Matrix (Fin 1) (Fin n) ℝ)
          (fun _ : Fin 1 => x) P := by
        intro i k
        exact horth
      have hbound := rank_trunc_forgetting_bound
        (Matrix.of fun _ : Fin 1 => (g - P *ᵥ g) :
           Matrix (Fin 1) (Fin n) ℝ) (fun _ : Fin 1 => x) P
        hgpmOrthP 0 0
      show |hybridStep HybridMech.rankTrunc g g_old P ⬝ᵥ x|
          ≤ nrm (g - P *ᵥ g) * sigmaTail P x
      simpa [hybridStep, Matrix.of_apply, dotProduct, nrm] using hbound

end Hagi.Theory.HybridContinual
