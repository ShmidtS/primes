/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.FreedmanTwoSided

/-!
# Fixed-terminal Freedman confidence for a fixed finite family

The probability input is the existing finite Markov history law.  The two-sided
fixed-terminal tail is obtained from `history_additive_freedman` at `k = T` on
`g` and `-g`; the family estimate is one union bound over a pre-fixed finset.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Probability.FreedmanFamilyConfidence

open Hagi.Probability
open scoped BigOperators

private theorem historyAdditive_neg {α : Type*}
    (g : ℕ → α → α → ℝ) (T k : ℕ) (ω : History α T) :
    historyAdditive (fun k a b => -g k a b) T k ω = -historyAdditive g T k ω := by
  unfold historyAdditive
  rw [← Finset.sum_neg_distrib]

private theorem history_additive_freedman_two_sided_fixed
    {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if r ≤ |historyAdditive g T T ω| ∧ historyCounter v T T ω ≤ V
        then 1 else 0) ≤ 2 * Real.exp (-r ^ 2 / (4 * (V + c * r))) := by
  classical
  have hbounded_neg : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support,
        |(fun k a b => -g k a b) k a b| ≤ c := by
    intro k hk a ha b hb
    exact (abs_neg (g k a b)).le.trans (hbounded k hk a ha b hb)
  have hmean_neg : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) ((fun k a b => -g k a b) k a) = 0 := by
    intro k hk a ha
    have h := pmfMean_const_mul (K k a) (-1) (g k a)
    rw [hmean k hk a ha, mul_zero] at h
    simpa only [neg_one_mul] using h
  have hvar_neg : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => ((fun k a b => -g k a b) k a b) ^ 2) ≤ v k a := by
    intro k hk a ha
    have hsq : pmfMean (K k a) (fun b => (-(g k a b)) ^ 2) =
        pmfMean (K k a) (fun b => (g k a b) ^ 2) :=
      pmfMean_congr (K k a) (fun b _ => neg_sq (g k a b))
    exact hsq.le.trans (hvar k hk a ha)
  have hpos := history_additive_freedman initial K g v T c hc
    hbounded hmean hvar T r V hr hV
  have hneg := history_additive_freedman initial K
    (fun k a b => -g k a b) v T c hc hbounded_neg hmean_neg hvar_neg T r V hr hV
  have hsplit : pmfMean (historyLaw initial K T T)
      (fun ω => if r ≤ |historyAdditive g T T ω| ∧ historyCounter v T T ω ≤ V
        then 1 else 0) ≤
      pmfMean (historyLaw initial K T T)
        (fun ω =>
          (if r ≤ historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V
            then (1 : ℝ) else 0) +
          (if r ≤ -historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V
            then (1 : ℝ) else 0)) := by
    apply pmfMean_mono
    intro ω _
    by_cases hbad : r ≤ |historyAdditive g T T ω| ∧ historyCounter v T T ω ≤ V
    · rw [ite_eq_left hbad]
      by_cases hpos : r ≤ historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V
      · rw [ite_eq_left hpos]
        exact le_add_of_nonneg_right (by positivity)
      · have hneg' : r ≤ -historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V := by
          refine ⟨?_, hbad.2⟩
          have hslt : historyAdditive g T T ω < r := lt_of_not_ge (fun h => hpos ⟨h, hbad.2⟩)
          by_contra hcon
          have hcon' : -historyAdditive g T T ω < r := lt_of_not_ge hcon
          have habslt : |historyAdditive g T T ω| < r :=
            abs_lt.mpr ⟨by linarith, hslt⟩
          linarith
        rw [ite_eq_right hpos, ite_eq_left hneg']
        norm_num
    · rw [ite_eq_right hbad]
      positivity
  have hsum : pmfMean (historyLaw initial K T T)
      (fun ω =>
        (if r ≤ historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V
          then (1 : ℝ) else 0) +
        (if r ≤ -historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V
          then (1 : ℝ) else 0)) =
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V
          then 1 else 0) +
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive (fun k a b => -g k a b) T T ω ∧
          historyCounter v T T ω ≤ V then 1 else 0) := by
    rw [pmfMean_add]
    congr 1
    apply pmfMean_congr
    intro ω _
    rw [historyAdditive_neg]
  calc
    _ ≤ _ := hsplit
    _ = _ := hsum
    _ ≤ Real.exp (-r ^ 2 / (4 * (V + c * r))) +
        Real.exp (-r ^ 2 / (4 * (V + c * r))) := add_le_add hpos hneg
    _ = 2 * Real.exp (-r ^ 2 / (4 * (V + c * r))) := by ring

private theorem pmfMean_compl_indicator_lower_bound
    {α : Type*} [Fintype α] (p : PMF α) (Bad Good : α → Prop)
    [DecidablePred Bad] [DecidablePred Good] (bound : ℝ)
    (hcompl : ∀ ω, Good ω ↔ ¬Bad ω)
    (hbad : pmfMean p (fun ω => if Bad ω then 1 else 0) ≤ bound) :
    1 - bound ≤ pmfMean p (fun ω => if Good ω then 1 else 0) := by
  classical
  have heq : pmfMean p (fun ω => if Good ω then 1 else 0) =
      1 - pmfMean p (fun ω => if Bad ω then 1 else 0) := by
    calc
      _ = pmfMean p (fun ω => (1 : ℝ) - (if Bad ω then 1 else 0)) := by
        apply pmfMean_congr
        intro ω _
        by_cases hB : Bad ω
        · have hG : ¬Good ω := fun h => (hcompl ω).mp h hB
          simp only [hB, hG, ite_true, ite_false]
          norm_num
        · have hG : Good ω := (hcompl ω).mpr hB
          simp only [hB, hG, ite_true, ite_false]
          norm_num
      _ = pmfMean p (fun _ => (1 : ℝ)) - pmfMean p (fun ω => if Bad ω then 1 else 0) :=
        pmfMean_sub p (fun _ => 1) (fun ω => if Bad ω then 1 else 0)
      _ = _ := by rw [pmfMean_const]
  rw [heq]
  linarith

/-- Simultaneous fixed-terminal two-sided Freedman confidence for a pre-fixed
finite family on the existing finite Markov history law. -/
theorem finite_family_freedman_confidence
    {α ι : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (T : ℕ)
    (s : Finset ι) (g : ι → ℕ → α → α → ℝ) (v : ι → ℕ → α → ℝ)
    (c r V : ℝ) (hc : 0 < c) (hr : 0 < r) (hV : 0 ≤ V)
    (hbounded : ∀ i ∈ s, ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g i k a b| ≤ c)
    (hmean : ∀ i ∈ s, ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g i k a) = 0)
    (hvar : ∀ i ∈ s, ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g i k a b) ^ 2) ≤ v i k a) :
    1 - 2 * (s.card : ℝ) * Real.exp (-r ^ 2 / (4 * (V + c * r))) ≤
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∀ i ∈ s, historyCounter (v i) T T ω ≤ V →
          |historyAdditive (g i) T T ω| < r then 1 else 0) := by
  classical
  have htail (i : ι) (hi : i ∈ s) :
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ |historyAdditive (g i) T T ω| ∧
          historyCounter (v i) T T ω ≤ V then 1 else 0) ≤
        2 * Real.exp (-r ^ 2 / (4 * (V + c * r))) :=
    history_additive_freedman_two_sided_fixed initial K (g i) (v i) T c hc
      (hbounded i hi) (hmean i hi) (hvar i hi) r V hr hV
  have hunion := pmfMean_event_union (historyLaw initial K T T) s
    (fun i ω => r ≤ |historyAdditive (g i) T T ω| ∧ historyCounter (v i) T T ω ≤ V)
  have hsum : (∑ i ∈ s, pmfMean (historyLaw initial K T T)
      (fun ω => if r ≤ |historyAdditive (g i) T T ω| ∧
        historyCounter (v i) T T ω ≤ V then 1 else 0)) ≤
      2 * (s.card : ℝ) * Real.exp (-r ^ 2 / (4 * (V + c * r))) := by
    calc
      _ ≤ ∑ _i ∈ s, 2 * Real.exp (-r ^ 2 / (4 * (V + c * r))) :=
        Finset.sum_le_sum (fun i hi => htail i hi)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hcompl : ∀ ω : History α T,
      (∀ i ∈ s, historyCounter (v i) T T ω ≤ V →
        |historyAdditive (g i) T T ω| < r) ↔
      ¬(∃ i ∈ s, r ≤ |historyAdditive (g i) T T ω| ∧
        historyCounter (v i) T T ω ≤ V) := by
    intro ω
    constructor
    · intro hgood ⟨i, hi, hradius, hcounter⟩
      exact (not_lt_of_ge hradius) (hgood i hi hcounter)
    · intro hgood i hi hcounter
      by_contra hradius
      exact hgood ⟨i, hi, le_of_not_gt hradius, hcounter⟩
  have hconf := pmfMean_compl_indicator_lower_bound (historyLaw initial K T T)
    (fun ω => ∃ i ∈ s, r ≤ |historyAdditive (g i) T T ω| ∧
      historyCounter (v i) T T ω ≤ V)
    (fun ω => ∀ i ∈ s, historyCounter (v i) T T ω ≤ V →
      |historyAdditive (g i) T T ω| < r)
    (2 * (s.card : ℝ) * Real.exp (-r ^ 2 / (4 * (V + c * r))))
    hcompl (by
      apply le_trans ?_ hsum
      convert hunion using 1
      · apply congrArg (pmfMean (historyLaw initial K T T))
        funext ω
        split_ifs <;> rfl
      · apply Finset.sum_congr rfl
        intro i _
        apply congrArg (pmfMean (historyLaw initial K T T))
        funext ω
        split_ifs <;> rfl)
  refine hconf.trans_eq ?_
  apply pmfMean_congr
  intro ω _
  by_cases hbad : ∃ i ∈ s, r ≤ |historyAdditive (g i) T T ω| ∧
    historyCounter (v i) T T ω ≤ V
  · have hgood : ¬(∀ i ∈ s, historyCounter (v i) T T ω ≤ V →
      |historyAdditive (g i) T T ω| < r) := fun h => (hcompl ω).mp h hbad
    simp only [hgood, ite_false]
  · have _hgood := (hcompl ω).mpr hbad
    rfl

/-- On the simultaneous good event, the two selected counter guards transfer
an observed gap to the corresponding conditional-risk gap with loss `2 * r`. -/
theorem finite_family_selected_conditional_gap_of_good
    {α ι : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (T : ℕ)
    (s : Finset ι) (f : ι → ℕ → α → α → ℝ) (v : ι → ℕ → α → ℝ)
    (b : ι) (σ : History α T → ι) (r V : ℝ) (ω : History α T)
    (hb : b ∈ s) (hσ : σ ω ∈ s)
    (hgood : ∀ i ∈ s, historyCounter (v i) T T ω ≤ V →
      |historyAdditive (fun k a next =>
        f i (k + 1) a next - pmfMean (K k a) (fun next => f i (k + 1) a next))
        T T ω| < r)
    (hbv : historyCounter (v b) T T ω ≤ V)
    (hσv : historyCounter (v (σ ω)) T T ω ≤ V) :
    (historyAdditive (fun k a next => f b (k + 1) a next) T T ω -
      historyAdditive (fun k a next => f (σ ω) (k + 1) a next) T T ω) - 2 * r ≤
      historyAdditive (fun k a _ =>
        pmfMean (K k a) (fun next => f b (k + 1) a next)) T T ω -
      historyAdditive (fun k a _ =>
        pmfMean (K k a) (fun next => f (σ ω) (k + 1) a next)) T T ω := by
  have hcenter (i : ι) :
      historyAdditive (fun k a next =>
        f i (k + 1) a next - pmfMean (K k a) (fun next => f i (k + 1) a next))
          T T ω =
        historyAdditive (fun k a next => f i (k + 1) a next) T T ω -
        historyAdditive (fun k a _ =>
          pmfMean (K k a) (fun next => f i (k + 1) a next)) T T ω := by
    unfold historyAdditive
    rw [Finset.sum_sub_distrib]
  have hbc := abs_lt.mp (hgood b hb hbv)
  have hσc := abs_lt.mp (hgood (σ ω) hσ hσv)
  rw [hcenter b] at hbc
  rw [hcenter (σ ω)] at hσc
  linarith

/-- A strict observed baseline-minus-selected gap gives a strictly positive
conditional-risk gap on the existing simultaneous Good event. -/
theorem finite_family_selected_conditional_gap_pos_of_good
    {α ι : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (T : ℕ)
    (s : Finset ι) (f : ι → ℕ → α → α → ℝ) (v : ι → ℕ → α → ℝ)
    (b : ι) (σ : History α T → ι) (r V : ℝ) (ω : History α T)
    (hb : b ∈ s) (hσ : σ ω ∈ s)
    (hgood : ∀ i ∈ s, historyCounter (v i) T T ω ≤ V →
      |historyAdditive (fun k a next =>
        f i (k + 1) a next - pmfMean (K k a) (fun next => f i (k + 1) a next))
        T T ω| < r)
    (hbv : historyCounter (v b) T T ω ≤ V)
    (hσv : historyCounter (v (σ ω)) T T ω ≤ V)
    (hobserved : 2 * r <
      historyAdditive (fun k a next => f b (k + 1) a next) T T ω -
      historyAdditive (fun k a next => f (σ ω) (k + 1) a next) T T ω) :
    0 < historyAdditive (fun k a _ =>
        pmfMean (K k a) (fun next => f b (k + 1) a next)) T T ω -
      historyAdditive (fun k a _ =>
        pmfMean (K k a) (fun next => f (σ ω) (k + 1) a next)) T T ω := by
  have hgap := finite_family_selected_conditional_gap_of_good
    K T s f v b σ r V ω hb hσ hgood hbv hσv
  linarith

end Hagi.Probability.FreedmanFamilyConfidence
