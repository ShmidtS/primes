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

end Hagi.Model.CEMarkovConfidence
