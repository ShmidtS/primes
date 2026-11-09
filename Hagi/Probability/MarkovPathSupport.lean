/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.FreedmanTwoSided

/-!
# Positive support for finite Markov paths

This isolated candidate uses the existing `historyInitial`, `historyKernel`,
and `historyLaw` from `Hagi.Probability.FreedmanTwoSided`.  The induction is on
`k ≤ T` inside one ambient `History α T`; it introduces no new path law or
transition-weight product.  The support constructions use Mathlib's exact
`PMF.mem_support_map_iff` and `PMF.mem_support_bind_iff` characterizations.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Probability.MarkovPathSupport

open Hagi.Probability

universe u

variable {α : Type u}

/-- Equality of two ambient histories on the recorded finite prefix. -/
private def prefixAgree {T : ℕ} (k : ℕ) (π ω : History α T) : Prop :=
  ∀ i : Fin (T + 1), i.val ≤ k → π i = ω i

/-- A supported start and supported transitions up to `k` produce a supported
history agreeing with the requested path on its prefix.  No statement is made
about coordinates after `k`. -/
theorem historyLaw_support_of_path (initial : PMF α) (K : ℕ → α → PMF α)
    {T k : ℕ} (hk : k ≤ T) (ω : History α T)
    (hstart : ω (historyIndex T 0) ∈ initial.support)
    (hsteps : ∀ j < k,
      ω (historyIndex T (j + 1)) ∈ (K j (ω (historyIndex T j))).support) :
    ∃ π ∈ (historyLaw initial K T k).support,
      ∀ i : Fin (T + 1), i.val ≤ k → π i = ω i := by
  induction k generalizing ω with
  | zero =>
      let π : History α T := fun _ => ω (historyIndex T 0)
      have hπ : π ∈ (historyLaw initial K T 0).support := by
        change π ∈ (historyInitial initial T).support
        rw [historyInitial]
        exact (PMF.mem_support_map_iff _ _ _).mpr
          ⟨ω (historyIndex T 0), hstart, rfl⟩
      have hagree : prefixAgree 0 π ω := by
        intro i hi
        have hi0 : i = historyIndex T 0 := by
          apply Fin.ext
          simp only [historyIndex_val]
          omega
        subst i
        rfl
      exact ⟨π, hπ, hagree⟩
  | succ k ih =>
      have hkT : k < T := by omega
      have hk_le : k ≤ T := by omega
      obtain ⟨π, hπ, hagree⟩ := ih hk_le ω hstart (fun j hj => hsteps j (by omega))
      change prefixAgree k π ω at hagree
      have hsource : π (historyIndex T k) = ω (historyIndex T k) :=
        hagree _ (by simp only [historyIndex_val, Nat.min_le_left])
      have hnext := hsteps k (Nat.lt_succ_self k)
      rw [← hsource] at hnext
      let b := ω (historyIndex T (k + 1))
      let π' := Function.update π (historyIndex T (k + 1)) b
      have hπ' : π' ∈ (historyLaw initial K T (k + 1)).support := by
        change π' ∈ ((historyLaw initial K T k).bind (historyKernel K T k)).support
        apply (PMF.mem_support_bind_iff _ _ _).mpr
        refine ⟨π, hπ, ?_⟩
        rw [historyKernel, ite_eq_left hkT]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨b, hnext, rfl⟩
      have hagree' : prefixAgree (k + 1) π' ω := by
        intro i hi
        dsimp only [π', b]
        by_cases hi_eq : i = historyIndex T (k + 1)
        · subst i
          simp only [Function.update_self]
        · rw [Function.update_of_ne hi_eq]
          apply hagree i
          have hi_val : i.val ≤ k := by
            by_contra hnot
            have hi_succ : i.val = k + 1 := by omega
            apply hi_eq
            apply Fin.ext
            simp only [historyIndex_val]
            omega
          exact hi_val
      exact ⟨π', hπ', hagree'⟩

/-- At the full horizon, the supported prefix witness is the requested history
itself. -/
theorem historyLaw_full_support (initial : PMF α) (K : ℕ → α → PMF α)
    {T : ℕ} (ω : History α T)
    (hstart : ω (historyIndex T 0) ∈ initial.support)
    (hsteps : ∀ j < T,
      ω (historyIndex T (j + 1)) ∈ (K j (ω (historyIndex T j))).support) :
    ω ∈ (historyLaw initial K T T).support := by
  obtain ⟨π, hπ, hagree⟩ := historyLaw_support_of_path initial K le_rfl ω hstart hsteps
  have hπω : π = ω := by
    funext i
    exact hagree i (by omega)
  rwa [hπω] at hπ

/-- Positive point-mass form of full-history support. -/
theorem historyLaw_full_apply_pos (initial : PMF α) (K : ℕ → α → PMF α)
    {T : ℕ} (ω : History α T)
    (hstart : ω (historyIndex T 0) ∈ initial.support)
    (hsteps : ∀ j < T,
      ω (historyIndex T (j + 1)) ∈ (K j (ω (historyIndex T j))).support) :
    0 < historyLaw initial K T T ω :=
  (PMF.apply_pos_iff _ _).mpr (historyLaw_full_support initial K ω hstart hsteps)

end Hagi.Probability.MarkovPathSupport
