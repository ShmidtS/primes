/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.HistoryFreedman

/-!
# FreedmanTwoSided — the |S| form of the joint maximal
Freedman (R234: the Hagi corollary closing the plan's
"two-sided anytime joint" line)

The plan (§1.2) asks for
P[∃j≤T: |S_j| ≥ r ∧ V_j ≤ v] ≤ 2(T+1)·exp(−r²/(4(v+cr))).
The ported one-sided maximal form applies to S and to −S
(negation preserves the bound and second-moment conditions;
the mean condition holds with equality); the two-sided
event is the union of the two one-sided events and the
finite union bound (pmfMean_event_union) doubles the
one-sided bound.
-/

namespace Hagi

open scoped BigOperators

/-- **The two-sided joint anytime Freedman**: for centered
bounded increments with the variance counter,
P[∃j≤T: |S_j| ≥ r ∧ V_j ≤ V] ≤ 2(T+1)·exp(−r²/(4(V+c·r))). -/
theorem history_additive_freedman_two_sided
    {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
        historyCounter v T j ω ≤ V then 1 else 0) ≤
      2 * ((T : ℝ) + 1) * Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  -- the negated functional satisfies the same conditions
  have hbounded' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |(-g) k a b| ≤ c := by
    intro k hk a ha b hb
    show |-(g k a b)| ≤ c
    rw [abs_neg]
    exact hbounded k hk a ha b hb
  have hmean' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) ((fun k a b => -g k a b) k a) = 0 := by
    intro k hk a ha
    show pmfMean (K k a) (fun b => -(g k a b)) = 0
    have h0 : pmfMean (K k a) (fun b => g k a b) = 0 := hmean k hk a ha
    have hneg : pmfMean (K k a) (fun b => -(g k a b))
        = -pmfMean (K k a) (fun b => g k a b) := by
      have := pmfMean_const_mul (K k a) (-1) (fun b => g k a b)
      simpa using this
    rw [hneg, h0]
    ring
  have hvar' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => ((fun k a b => -g k a b) k a b)^2) ≤ v k a := by
    intro k hk a ha
    show pmfMean (K k a) (fun b => (-(g k a b))^2) ≤ v k a
    have hsq : pmfMean (K k a) (fun b => (-(g k a b))^2)
        = pmfMean (K k a) (fun b => (g k a b)^2) :=
      pmfMean_congr (K k a) (fun b _ => neg_sq (g k a b))
    rw [hsq]
    exact hvar k hk a ha
  -- the two one-sided maximal bounds
  have h1 := history_additive_freedman_maximal initial K g v T c hc
    hbounded hmean hvar r V hr hV
  have h2 := history_additive_freedman_maximal initial K
    (fun k a b => -g k a b) v T c hc hbounded' hmean' hvar' r V hr hV
  -- negated-functional sums: pointwise identity under funext
  have hnegfun : ∀ ω : History α T,
      (fun (j : ℕ) => historyAdditive (fun k a b => -g k a b) T j ω)
      = fun (j : ℕ) => -historyAdditive g T j ω := by
    intro ω
    funext j
    unfold historyAdditive
    rw [← Finset.sum_neg_distrib]
  -- the two-sided mean splits via the ADDITIVE indicator bound
  have hsplit : pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
        historyCounter v T j ω ≤ V then 1 else 0)
      ≤ pmfMean (historyLaw initial K T T)
        (fun ω => (if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)
          + (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)) := by
    refine pmfMean_mono _ (fun ω _ => ?_)
    by_cases hex : ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
      historyCounter v T j ω ≤ V
    · rw [ite_eq_left hex]
      by_cases hpos : ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
        historyCounter v T j ω ≤ V
      · rw [ite_eq_left hpos]
        have hz : (0:ℝ) ≤ (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then 1 else 0) :=
          ite_nonneg (by norm_num) (by norm_num)
        linarith
      · -- S never reaches r upward, but |S| does: so -S does
        obtain ⟨j, hj, habs, hctr⟩ := hex
        have hnegup : r ≤ -historyAdditive g T j ω := by
          by_contra hcon
          push_neg at hcon
          have hS : historyAdditive g T j ω < r :=
            lt_of_not_ge (fun h => hpos ⟨j, hj, h, hctr⟩)
          have habslt : |historyAdditive g T j ω| < r :=
            abs_lt.mpr ⟨by linarith, hS⟩
          linarith
        rw [ite_eq_right hpos,
          ite_eq_left ⟨j, hj, hnegup, hctr⟩]
        norm_num
    · rw [ite_eq_right hex]
      have hz1 : (0:ℝ) ≤ (if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
          historyCounter v T j ω ≤ V then 1 else 0) :=
        ite_nonneg (by norm_num) (by norm_num)
      have hz2 : (0:ℝ) ≤ (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
          historyCounter v T j ω ≤ V then 1 else 0) :=
        ite_nonneg (by norm_num) (by norm_num)
      linarith
  -- mean of the sum = sum of the means; rewrite the negated part
  have hsum : pmfMean (historyLaw initial K T T)
      (fun ω => (if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)
          + (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0))
      = pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)
        + pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T,
            r ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0) := by
    rw [pmfMean_add]
    congr 1
    · refine pmfMean_congr _ (fun ω _ => ?_)
      have hj : ∀ j, historyAdditive (fun k a b => -g k a b) T j ω
          = -historyAdditive g T j ω := fun j => congrFun (hnegfun ω) j
      simp only [hj]
  calc pmfMean (historyLaw initial K T T)
        (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
          historyCounter v T j ω ≤ V then 1 else 0)
      ≤ pmfMean (historyLaw initial K T T)
          (fun ω => (if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
              historyCounter v T j ω ≤ V then (1:ℝ) else 0)
            + (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
              historyCounter v T j ω ≤ V then (1:ℝ) else 0)) := hsplit
    _ = pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)
        + pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T,
            r ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0) := hsum
    _ ≤ ((T : ℝ) + 1) * Real.exp (-r^2/(4*(V+c*r)))
        + ((T : ℝ) + 1) * Real.exp (-r^2/(4*(V+c*r))) :=
        add_le_add h1 h2
    _ = 2 * ((T : ℝ) + 1) * Real.exp (-r^2/(4*(V+c*r))) := by ring

end Hagi
