/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Model.CEHeldout
import Hagi.Probability.FreedmanFamilyConfidence

/-!
# Markov confidence for a finite bank of normalized coded CE losses

The current bank supplies each model code and the next state supplies the
categorical label.  This is one fixed-terminal specialization of the existing
finite-family Freedman theorem, not a training or adaptivity statement.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model.CEMarkovConfidence

open Hagi.Model.CEHeldout
open Hagi.Probability
open Hagi.Probability.FreedmanFamilyConfidence

/-- Fixed-terminal simultaneous confidence for every member of a finite coded
model bank on the supplied bank-by-label Markov history law. -/
theorem normalized_bank_freedman_confidence
    {G m : ℕ} {Label : Type} [Fintype Label] [Nonempty Label]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix Label (Fin (5 * G)) ℝ)
    (initial : PMF ((Fin m → JointCode G) × Label))
    (K : ℕ → ((Fin m → JointCode G) × Label) →
      PMF ((Fin m → JointCode G) × Label))
    (T : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    1 - 2 * (m : ℝ) * Real.exp (-r ^ 2 / (4 * (V + r))) ≤
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∀ i : Fin m,
          historyCounter (fun k a => pmfMean (K k a)
            (fun (next : (Fin m → JointCode G) × Label) =>
            (normalizedCE (G := G) (V := Label) e X (a.1 i) next.2 -
              pmfMean (K k a)
                (fun (next : (Fin m → JointCode G) × Label) =>
                  normalizedCE (G := G) (V := Label) e X (a.1 i) next.2)) ^ 2)) T T ω ≤ V →
            |historyAdditive (fun k a next =>
              normalizedCE (G := G) (V := Label) e X (a.1 i) next.2 -
                pmfMean (K k a)
                  (fun (next : (Fin m → JointCode G) × Label) =>
                    normalizedCE (G := G) (V := Label) e X (a.1 i) next.2)) T T ω| < r
          then 1 else 0) := by
  classical
  let F : Fin m → ℕ → ((Fin m → JointCode G) × Label) →
      ((Fin m → JointCode G) × Label) → ℝ :=
    fun i _ a next => normalizedCE (G := G) (V := Label) e X (a.1 i) next.2
  let μ : Fin m → ℕ → ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a => pmfMean (K k a) (F i k a)
  let g : Fin m → ℕ → ((Fin m → JointCode G) × Label) →
      ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a next => F i k a next - μ i k a
  let v : Fin m → ℕ → ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a => pmfMean (K k a)
      (fun (next : (Fin m → JointCode G) × Label) =>
        (F i k a next - μ i k a) ^ 2)
  have hμ (i : Fin m) (k : ℕ) (a : (Fin m → JointCode G) × Label) :
      0 ≤ μ i k a ∧ μ i k a ≤ 1 := by
    constructor
    · apply pmfMean_nonneg
      intro next _
      exact (normalizedCE_mem_unit e X (a.1 i) next.2).1
    · calc
        μ i k a ≤ pmfMean (K k a) (fun _ => 1) := by
          apply pmfMean_mono
          intro next _
          exact (normalizedCE_mem_unit e X (a.1 i) next.2).2
        _ = 1 := pmfMean_const _ _
  have hg (i : Fin m) (k : ℕ) (a next : (Fin m → JointCode G) × Label) :
      |g i k a next| ≤ 1 := by
    have hF := normalizedCE_mem_unit e X (a.1 i) next.2
    have hmean := hμ i k a
    rw [abs_le]
    dsimp only [g, F]
    constructor <;> linarith [hF.1, hF.2, hmean.1, hmean.2]
  have hmean (i : Fin m) (k : ℕ) (a : (Fin m → JointCode G) × Label) :
      pmfMean (K k a) (g i k a) = 0 := by
    dsimp only [g]
    rw [pmfMean_sub, pmfMean_const, sub_self]
  have hconf := finite_family_freedman_confidence initial K T
    (Finset.univ : Finset (Fin m)) g v 1 r V (by norm_num) hr hV
    (fun i _ k _ a _ next _ => hg i k a next)
    (fun i _ k _ a _ => hmean i k a)
    (fun _ _ _ _ _ _ => le_rfl)
  simpa only [Finset.card_univ, Fintype.card_fin, one_mul, v, g, μ, F,
    Finset.mem_univ, forall_const] using hconf

/-- Fixed-terminal simultaneous confidence for the actual raw CE of every
member of a finite coded model bank on the supplied bank-by-label history. -/
theorem raw_bank_freedman_confidence
    {G m : ℕ} {Label : Type} [Fintype Label] [Nonempty Label]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix Label (Fin (5 * G)) ℝ)
    (initial : PMF ((Fin m → JointCode G) × Label))
    (K : ℕ → ((Fin m → JointCode G) × Label) →
      PMF ((Fin m → JointCode G) × Label))
    (T : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    1 - 2 * (m : ℝ) * Real.exp (-r ^ 2 / (4 * (V + ceBound X * r))) ≤
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∀ i : Fin m,
          historyCounter (fun k a => pmfMean (K k a)
            (fun (next : (Fin m → JointCode G) × Label) =>
            (Hagi.ceOneHot next.2 (ceLogits X (decodeJoint e (a.1 i))) -
              pmfMean (K k a)
                (fun (next : (Fin m → JointCode G) × Label) =>
                  Hagi.ceOneHot next.2 (ceLogits X (decodeJoint e (a.1 i))))) ^ 2)) T T ω ≤ V →
            |historyAdditive (fun k a next =>
              Hagi.ceOneHot next.2 (ceLogits X (decodeJoint e (a.1 i))) -
                pmfMean (K k a)
                  (fun (next : (Fin m → JointCode G) × Label) =>
                    Hagi.ceOneHot next.2 (ceLogits X (decodeJoint e (a.1 i))))) T T ω| < r
          then 1 else 0) := by
  classical
  let B := ceBound X
  have hB : 0 < B := ceBound_pos X
  let F : Fin m → ℕ → ((Fin m → JointCode G) × Label) →
      ((Fin m → JointCode G) × Label) → ℝ :=
    fun i _ a next => Hagi.ceOneHot next.2 (ceLogits X (decodeJoint e (a.1 i)))
  let FN : Fin m → ℕ → ((Fin m → JointCode G) × Label) →
      ((Fin m → JointCode G) × Label) → ℝ :=
    fun i _ a next => normalizedCE (G := G) (V := Label) e X (a.1 i) next.2
  let μ : Fin m → ℕ → ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a => pmfMean (K k a) (F i k a)
  let μN : Fin m → ℕ → ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a => pmfMean (K k a) (FN i k a)
  let g : Fin m → ℕ → ((Fin m → JointCode G) × Label) →
      ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a next => F i k a next - μ i k a
  let gN : Fin m → ℕ → ((Fin m → JointCode G) × Label) →
      ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a next => FN i k a next - μN i k a
  let v : Fin m → ℕ → ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a => pmfMean (K k a) (fun next => (g i k a next) ^ 2)
  let vN : Fin m → ℕ → ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a => pmfMean (K k a) (fun next => (gN i k a next) ^ 2)
  have hF (i : Fin m) (k : ℕ) (a next : (Fin m → JointCode G) × Label) :
      F i k a next = B * FN i k a next := by
    dsimp only [F, FN, B, normalizedCE]
    exact (mul_div_cancel₀ _ hB.ne').symm
  have hμ (i : Fin m) (k : ℕ) (a : (Fin m → JointCode G) × Label) :
      μ i k a = B * μN i k a := by
    dsimp only [μ, μN]
    calc
      pmfMean (K k a) (F i k a) =
          pmfMean (K k a) (fun next => B * FN i k a next) :=
        pmfMean_congr _ (fun next _ => hF i k a next)
      _ = B * pmfMean (K k a) (FN i k a) := pmfMean_const_mul _ _ _
  have hg (i : Fin m) (k : ℕ) (a next : (Fin m → JointCode G) × Label) :
      g i k a next = B * gN i k a next := by
    dsimp only [g, gN]
    rw [hF i k a next, hμ i k a]
    ring
  have hv (i : Fin m) (k : ℕ) (a : (Fin m → JointCode G) × Label) :
      v i k a = B ^ 2 * vN i k a := by
    dsimp only [v, vN]
    calc
      pmfMean (K k a) (fun next => (g i k a next) ^ 2) =
          pmfMean (K k a) (fun next => B ^ 2 * (gN i k a next) ^ 2) :=
        pmfMean_congr _ (fun next _ => by rw [hg]; ring)
      _ = B ^ 2 * pmfMean (K k a) (fun next => (gN i k a next) ^ 2) :=
        pmfMean_const_mul _ _ _
  have hcounter (i : Fin m) (ω : History ((Fin m → JointCode G) × Label) T) :
      historyCounter (v i) T T ω = B ^ 2 * historyCounter (vN i) T T ω := by
    unfold historyCounter
    simp_rw [hv]
    rw [Finset.mul_sum]
  have hadditive (i : Fin m) (ω : History ((Fin m → JointCode G) × Label) T) :
      historyAdditive (g i) T T ω = B * historyAdditive (gN i) T T ω := by
    unfold historyAdditive
    simp_rw [hg]
    rw [Finset.mul_sum]
  have hguard (i : Fin m) (ω : History ((Fin m → JointCode G) × Label) T) :
      historyCounter (v i) T T ω ≤ V ↔ historyCounter (vN i) T T ω ≤ V / B ^ 2 := by
    rw [hcounter, le_div_iff₀ (sq_pos_of_pos hB)]
    constructor <;> intro h <;> simpa only [mul_comm] using h
  have herror (i : Fin m) (ω : History ((Fin m → JointCode G) × Label) T) :
      |historyAdditive (g i) T T ω| < r ↔
        |historyAdditive (gN i) T T ω| < r / B := by
    rw [hadditive, abs_mul, abs_of_pos hB, lt_div_iff₀ hB]
    simp only [mul_comm]
  have hgood (ω : History ((Fin m → JointCode G) × Label) T) :
      (∀ i : Fin m, historyCounter (v i) T T ω ≤ V →
        |historyAdditive (g i) T T ω| < r) ↔
      (∀ i : Fin m, historyCounter (vN i) T T ω ≤ V / B ^ 2 →
        |historyAdditive (gN i) T T ω| < r / B) := by
    constructor
    · intro h i hi
      exact (herror i ω).mp (h i ((hguard i ω).mpr hi))
    · intro h i hi
      exact (herror i ω).mpr (h i ((hguard i ω).mp hi))
  have hconf := normalized_bank_freedman_confidence (G := G) (m := m) e X initial K T
    (r / B) (V / B ^ 2) (div_pos hr hB) (div_nonneg hV (sq_nonneg B))
  change 1 - 2 * (m : ℝ) * Real.exp (-(r / B) ^ 2 / (4 * (V / B ^ 2 + r / B))) ≤
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∀ i : Fin m, historyCounter (vN i) T T ω ≤ V / B ^ 2 →
        |historyAdditive (gN i) T T ω| < r / B then 1 else 0) at hconf
  have hexponent : -(r / B) ^ 2 / (4 * (V / B ^ 2 + r / B)) =
      -r ^ 2 / (4 * (V + B * r)) := by
    field_simp [hB.ne']
  rw [hexponent] at hconf
  have hraw : 1 - 2 * (m : ℝ) * Real.exp (-r ^ 2 / (4 * (V + B * r))) ≤
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∀ i : Fin m, historyCounter (v i) T T ω ≤ V →
          |historyAdditive (g i) T T ω| < r then 1 else 0) := by
    refine hconf.trans_eq ?_
    apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    exact if_congr (hgood ω).symm rfl rfl
  simpa only [v, g, μ, F, B] using hraw

end Hagi.Model.CEMarkovConfidence
