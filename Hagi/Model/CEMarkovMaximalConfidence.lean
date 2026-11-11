/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Model.CEMarkovConfidence

/-!
# Raw-bank finite-prefix Freedman confidence

A finite union of exact conditional-moment CE increments on one bounded
history law. This is statistical confidence, not training progress.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model.CEMarkovMaximalConfidence

open Hagi.Model.CEHeldout
open Hagi.Probability
open scoped BigOperators

/-- Simultaneous finite-bank, finite-horizon prefix-maximal confidence for
centered raw decoded cross-entropy increments on the supplied history law. -/
theorem raw_bank_freedman_maximal_confidence
    {G m : ℕ} {Label : Type} [Fintype Label] [Nonempty Label]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix Label (Fin (5 * G)) ℝ)
    (initial : PMF ((Fin m → JointCode G) × Label))
    (K : ℕ → ((Fin m → JointCode G) × Label) →
      PMF ((Fin m → JointCode G) × Label))
    (T : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    1 - 2 * (m : ℝ) * ((T : ℝ) + 1) * Real.exp (-r ^ 2 / (4 * (V + ceBound X * r))) ≤
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∀ i : Fin m, ∀ j ≤ T,
          historyCounter (fun k a => pmfMean (K k a)
            (fun (next : (Fin m → JointCode G) × Label) =>
            (Hagi.ceOneHot next.2 (ceLogits X (decodeJoint e (a.1 i))) -
              pmfMean (K k a)
                (fun (next : (Fin m → JointCode G) × Label) =>
                  Hagi.ceOneHot next.2 (ceLogits X (decodeJoint e (a.1 i))))) ^ 2)) T j ω ≤ V →
            |historyAdditive (fun k a next =>
              Hagi.ceOneHot next.2 (ceLogits X (decodeJoint e (a.1 i))) -
                pmfMean (K k a)
                  (fun (next : (Fin m → JointCode G) × Label) =>
                    Hagi.ceOneHot next.2 (ceLogits X (decodeJoint e (a.1 i))))) T j ω| < r
          then 1 else 0) := by
  classical
  let F : Fin m → ℕ → ((Fin m → JointCode G) × Label) →
      ((Fin m → JointCode G) × Label) → ℝ :=
    fun i _ a next => Hagi.ceOneHot next.2 (ceLogits X (decodeJoint e (a.1 i)))
  let μ : Fin m → ℕ → ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a => pmfMean (K k a) (F i k a)
  let g : Fin m → ℕ → ((Fin m → JointCode G) × Label) →
      ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a next => F i k a next - μ i k a
  let v : Fin m → ℕ → ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a => pmfMean (K k a) (fun next => (g i k a next) ^ 2)
  have hF_nonneg (i : Fin m) (k : ℕ) (a next : (Fin m → JointCode G) × Label) :
      0 ≤ F i k a next := by
    dsimp only [F]
    exact ceOneHot_nonneg _ _
  have hF_upper (i : Fin m) (k : ℕ) (a next : (Fin m → JointCode G) × Label) :
      F i k a next ≤ ceBound X := by
    dsimp only [F]
    exact ceOneHot_decodeJoint_le_ceBound e X next.2 (a.1 i)
  have hμ (i : Fin m) (k : ℕ) (a : (Fin m → JointCode G) × Label) :
      0 ≤ μ i k a ∧ μ i k a ≤ ceBound X := by
    constructor
    · apply pmfMean_nonneg
      intro next _
      exact hF_nonneg i k a next
    · calc
        μ i k a ≤ pmfMean (K k a) (fun _ => ceBound X) := by
          apply pmfMean_mono
          intro next _
          exact hF_upper i k a next
        _ = ceBound X := pmfMean_const _ _
  have hc : 0 < ceBound X := ceBound_pos X
  have hg (i : Fin m) (k : ℕ) (a next : (Fin m → JointCode G) × Label) :
      |g i k a next| ≤ ceBound X := by
    have hFlo := hF_nonneg i k a next
    have hFhi := hF_upper i k a next
    have hmean := hμ i k a
    rw [abs_le]
    dsimp only [g]
    constructor <;> linarith [hFlo, hFhi, hmean.1, hmean.2, hc.le]
  have hmean (i : Fin m) (k : ℕ) (a : (Fin m → JointCode G) × Label) :
      pmfMean (K k a) (g i k a) = 0 := by
    dsimp only [g]
    rw [pmfMean_sub, pmfMean_const, sub_self]
  have htail (i : Fin m) :
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive (g i) T j ω| ∧
          historyCounter (v i) T j ω ≤ V then 1 else 0) ≤
        2 * ((T : ℝ) + 1) * Real.exp (-r ^ 2 / (4 * (V + ceBound X * r))) := by
    exact history_additive_freedman_two_sided initial K (g i) (v i) T
      (ceBound X) hc
      (fun k _ a _ next _ => hg i k a next)
      (fun k _ a _ => hmean i k a)
      (fun _ _ _ _ => le_rfl) r V hr hV
  have hunion := pmfMean_event_union (historyLaw initial K T T)
    (Finset.univ : Finset (Fin m))
    (fun i ω => ∃ j ≤ T, r ≤ |historyAdditive (g i) T j ω| ∧
      historyCounter (v i) T j ω ≤ V)
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin m)),
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive (g i) T j ω| ∧
          historyCounter (v i) T j ω ≤ V then 1 else 0)) ≤
      2 * (m : ℝ) * ((T : ℝ) + 1) * Real.exp (-r ^ 2 / (4 * (V + ceBound X * r))) := by
    calc
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin m)),
          2 * ((T : ℝ) + 1) * Real.exp (-r ^ 2 / (4 * (V + ceBound X * r))) :=
        Finset.sum_le_sum (fun i hi => htail i)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hbad : pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ i : Fin m, ∃ j ≤ T, r ≤ |historyAdditive (g i) T j ω| ∧
        historyCounter (v i) T j ω ≤ V then 1 else 0) ≤
      2 * (m : ℝ) * ((T : ℝ) + 1) * Real.exp (-r ^ 2 / (4 * (V + ceBound X * r))) := by
    apply le_trans ?_ hsum
    convert hunion using 1
    · apply congrArg (pmfMean (historyLaw initial K T T))
      funext ω
      simp only [Finset.mem_univ, true_and]
    · apply Finset.sum_congr rfl
      intro i _
      apply congrArg (pmfMean (historyLaw initial K T T))
      funext ω
      split_ifs <;> rfl
  have hcompl (ω : History ((Fin m → JointCode G) × Label) T) :
      (∀ i : Fin m, ∀ j ≤ T, historyCounter (v i) T j ω ≤ V →
        |historyAdditive (g i) T j ω| < r) ↔
      ¬(∃ i : Fin m, ∃ j ≤ T, r ≤ |historyAdditive (g i) T j ω| ∧
        historyCounter (v i) T j ω ≤ V) := by
    constructor
    · intro hgood ⟨i, j, hj, hradius, hcounter⟩
      exact (not_lt_of_ge hradius) (hgood i j hj hcounter)
    · intro hgood i j hj hcounter
      by_contra hradius
      exact hgood ⟨i, j, hj, le_of_not_gt hradius, hcounter⟩
  have hgoodMean : pmfMean (historyLaw initial K T T)
      (fun ω => if ∀ i : Fin m, ∀ j ≤ T, historyCounter (v i) T j ω ≤ V →
        |historyAdditive (g i) T j ω| < r then 1 else 0) =
      1 - pmfMean (historyLaw initial K T T)
        (fun ω => if ∃ i : Fin m, ∃ j ≤ T, r ≤ |historyAdditive (g i) T j ω| ∧
          historyCounter (v i) T j ω ≤ V then 1 else 0) := by
    calc
      _ = pmfMean (historyLaw initial K T T)
          (fun ω => (1 : ℝ) - (if ∃ i : Fin m, ∃ j ≤ T,
            r ≤ |historyAdditive (g i) T j ω| ∧
              historyCounter (v i) T j ω ≤ V then 1 else 0)) := by
        apply pmfMean_congr
        intro ω _
        by_cases hB : ∃ i : Fin m, ∃ j ≤ T, r ≤ |historyAdditive (g i) T j ω| ∧
          historyCounter (v i) T j ω ≤ V
        · have hG : ¬(∀ i : Fin m, ∀ j ≤ T, historyCounter (v i) T j ω ≤ V →
            |historyAdditive (g i) T j ω| < r) := fun h => (hcompl ω).mp h hB
          rw [ite_eq_right hG, ite_eq_left hB]
          norm_num
        · have hG : (∀ i : Fin m, ∀ j ≤ T, historyCounter (v i) T j ω ≤ V →
            |historyAdditive (g i) T j ω| < r) := (hcompl ω).mpr hB
          rw [ite_eq_left hG, ite_eq_right hB]
          norm_num
      _ = pmfMean (historyLaw initial K T T) (fun _ => (1 : ℝ)) -
          pmfMean (historyLaw initial K T T)
            (fun ω => if ∃ i : Fin m, ∃ j ≤ T, r ≤ |historyAdditive (g i) T j ω| ∧
              historyCounter (v i) T j ω ≤ V then 1 else 0) :=
        pmfMean_sub _ _ _
      _ = _ := by rw [pmfMean_const]
  have hfinal : 1 - 2 * (m : ℝ) * ((T : ℝ) + 1) *
      Real.exp (-r ^ 2 / (4 * (V + ceBound X * r))) ≤
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∀ i : Fin m, ∀ j ≤ T, historyCounter (v i) T j ω ≤ V →
          |historyAdditive (g i) T j ω| < r then 1 else 0) := by
    rw [hgoodMean]
    linarith
  simpa only [v, g, μ, F] using hfinal

end Hagi.Model.CEMarkovMaximalConfidence
