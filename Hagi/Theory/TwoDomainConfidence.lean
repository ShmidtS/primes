/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Unified.GuardedRobustSelection

/-!
# Conditional two-domain confidence transport for guarded selection

On one finite independent-product law, simultaneous old-estimate and bounded
fixed-family target accuracy imply old non-regression and a strict target
population-loss gap at an actual feasible guarded successor.  The observed
margin is an explicit per-sample certificate for every feasible representative
of the existing guarded output; this is not a target-aware selector.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Unified.TwoDomainConfidence

open Hagi.Probability
open Hagi.Probability.FiniteFamilyConfidence
open Hagi.Unified.ParetoExecution
open Hagi.Unified.GuardedRobustSelection

open scoped Classical in
/-- A common union-bound allowance transports old guarded non-regression and
an observed fixed-family target margin to a strict population-loss gap. -/
theorem finite_family_two_domain_guarded_improvement
    {V A : Type} {S : Type*} [Fintype V] [Nonempty V] [Fintype A]
    {n : ℕ} (law : Fin n → V → ℝ) (hp : IsProbSys law)
    (p : ControllerProblem A S) [DecidablePred p.safe]
    (estimate : (Fin n → V) → S → ℝ)
    (target : A → Fin n → V → ℝ)
    (h_target : ∀ a i v, 0 ≤ target a i v ∧ target a i v ≤ 1)
    (s : S) (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (eps_old eps_target delta : ℝ)
    (hn : 0 < n) (h_eps_old : 0 < eps_old) (h_eps_target : 0 < eps_target)
    (h_old : 1 - delta ≤ prodPq law (fun ω => ∀ a,
      |p.value (p.step a s) - estimate ω (p.step a s)| ≤ eps_old))
    (h_delta : 2 * (Fintype.card A : ℝ) *
      Real.exp (-2 * (n : ℝ) * eps_target ^ 2) ≤ delta)
    (h_observed : ∀ ω a, a ∈ feasible p M C →
      guardedRobustNext p (estimate ω) eps_old s M C stay h0 = p.step a s →
      2 * eps_target < empiricalMean (target stay) ω -
        empiricalMean (target a) ω) :
    1 - 2 * delta ≤ prodPq law (fun ω =>
      p.value (p.step stay s) ≤
        p.value (guardedRobustNext p (estimate ω) eps_old s M C stay h0) ∧
      ∃ a ∈ feasible p M C,
        guardedRobustNext p (estimate ω) eps_old s M C stay h0 = p.step a s ∧
        0 < populationMean law (target stay) - populationMean law (target a)) := by
  classical
  let OldGood : (Fin n → V) → Prop := fun ω => ∀ a,
    |p.value (p.step a s) - estimate ω (p.step a s)| ≤ eps_old
  let TargetGood : (Fin n → V) → Prop := fun ω => ∀ a,
    |populationMean law (target a) - empiricalMean (target a) ω| ≤ eps_target
  let Branches : Bool → (Fin n → V) → Prop := fun b ω =>
    if b then TargetGood ω else OldGood ω
  have hTargetConfidence : 1 - delta ≤ prodPq law TargetGood := by
    have ht := finite_family_abs_error_confidence law hp target h_target hn
      eps_target h_eps_target
    dsimp only [TargetGood]
    calc
      1 - delta ≤ 1 - 2 * (Fintype.card A : ℝ) *
          Real.exp (-2 * (n : ℝ) * eps_target ^ 2) := by linarith
      _ ≤ prodPq law TargetGood := ht
  have hBranches : ∀ b ∈ (Finset.univ : Finset Bool),
      1 - delta ≤ prodPq law (Branches b) := by
    intro b _hb
    cases b
    · simpa only [Branches, Bool.false_eq_true, ↓reduceIte] using h_old
    · simpa only [Branches, ↓reduceIte] using hTargetConfidence
  have hmain := probable_conclusion law hp (Finset.univ : Finset Bool) Branches
    (fun ω =>
      p.value (p.step stay s) ≤
        p.value (guardedRobustNext p (estimate ω) eps_old s M C stay h0) ∧
      ∃ a ∈ feasible p M C,
        guardedRobustNext p (estimate ω) eps_old s M C stay h0 = p.step a s ∧
        0 < populationMean law (target stay) - populationMean law (target a))
    delta hBranches (by
      intro ω hω
      have hOldGood : OldGood ω := by
        simpa only [Branches, Bool.false_eq_true, ↓reduceIte] using
          hω false (Finset.mem_univ false)
      have hTargetGood : TargetGood ω := by
        simpa only [Branches, ↓reduceIte] using
          hω true (Finset.mem_univ true)
      have hold := guardedRobustNext_quality_ge_stay p (estimate ω) eps_old
        s M C stay h0 (fun a _ha => hOldGood a)
      obtain ⟨a, ha, hnext⟩ := guardedRobustNext_exists p (estimate ω) eps_old
        s M C stay h0
      refine ⟨hold, a, ha, hnext, ?_⟩
      have hobs := h_observed ω a ha hnext
      have hb := abs_le.mp (hTargetGood stay)
      have haError := abs_le.mp (hTargetGood a)
      dsimp only [TargetGood] at hTargetGood
      linarith)
  simpa only [Finset.card_univ, Fintype.card_bool, Nat.cast_ofNat] using hmain

end Hagi.Unified.TwoDomainConfidence
