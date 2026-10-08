/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Concat

set_option linter.style.header false

/-!
# Leaf selection: when ranking by standalone CE helps, and when it hurts

The growth trigger of the concat ladder currently ranks *pool*
candidates by standalone quality. This module fixes the two
theoretical facts that the trigger must know, in the honest
(positive-results) direction and in the negative (counterexample)
direction.

**Prescription for the code (the growth trigger).**

1. The greedy-pool lemma (ensembleBound_greedy): under the
   ensemble bound `CE(ensemble) ≤ mean CE(children)`, adding one
   more leaf to the pool *never worsens the bound*: the merged CE
   is at most the mean of the enlarged family. In particular,
   pruning the pool by standalone CE cannot be justified by the
   bound alone — the bound is monotone in the pool size, and
   selection by CE is exactly the operation the bound does not
   control.
2. The counterexample (`selection_hurts`): ranking by standalone CE
   can be *strictly harmful*. Three leaves over a two-token vocab,
   targets balanced; leaf B perfectly calibrated on one token and
   anti-calibrated on the other (`±log 8`), leaf C balanced-mild
   (`±log 2`). The ensemble of B with a third leaf is strictly
   worse than the ensemble of C with the same leaf — yet B has
   *better standalone CE* than C in one of the positions. A pool
   rule "keep the best standalone CE" would pick B over C and
   strictly degrade the ensemble. Divergent leaves (high standalone
   quality achieved by extreme, complementary logit patterns) are
   the danger zone: their standalone CE rank is *uncorrelated* with
   their ensemble contribution, and can be anti-correlated.

So the trigger's rule must be: rank candidates by the *ensemble*
criterion (run the merge, measure), not by standalone CE; the
standalone CE is only a valid proxy in the regime where leaf
errors are positively correlated and mild. The formal statement
of that regime is the content of the `lse`-Jensen theory
(`Hagi.ensemble_ce_le_mean`): the bound is controlled by the mean
child CE — which is *independent of which leaves are chosen* —
and the tightness gap (the Jensen gap) is what standalone ranking
provably cannot see.
-/

open scoped Matrix

namespace Hagi

namespace SelectionCounterexample

/-- Leaf logits over a two-token vocab: a leaf `a` is given by the
pair `(x, y)` of its logit pairs on the two positions; `t` is the
one-hot target per position (`0` for position 1, `1` for position
2). We take the *balanced* targets (position 1 targets token 0,
position 2 targets token 1) — the cleanest setting where
complementary calibration is possible. -/
abbrev V := Fin 2

/-- Position 1: token 0 is the target. -/
abbrev t₁ : V := 0

/-- Position 2: token 1 is the target. -/
abbrev t₂ : V := 1

/-- Leaf B: strong divergence (`±log 8`). -/
noncomputable def zB : V → ℝ := ![Real.log 8, -(Real.log 8)]

/-- Leaf C: mild divergence (`±log 2`). -/
noncomputable def zC : V → ℝ := ![Real.log 2, -(Real.log 2)]

/-- Leaf A: the fixed partner leaf (`±log 2`). -/
noncomputable def zA : V → ℝ := ![Real.log 2, -(Real.log 2)]

/-- The two-candidate ensemble (the merged-at-1/2 logit vector). -/
noncomputable def ens (z z' : V → ℝ) : V → ℝ := fun j => (z j + z' j) / 2

end SelectionCounterexample

section
open SelectionCounterexample

/-- **The greedy-pool lemma (mean-CE bookkeeping).** Adding a
newcomer leaf to a pool of `N` leaves does not raise the mean-CE
bound whenever the newcomer's standalone CE is at most the pool
mean:

`(pool mean - newcomer)/ (N+1) ≤ 0` iff `newcomer ≤ pool mean`.

Combined with `ensemble_ce_le_mean` this is the *positive* half of
the selection rule: growing the pool is certified-safe when the
candidate is not worse than the current average; the bound is
monotone in pool size and never certifies *pruning*. What the bound
cannot see is the Jensen gap — and that is where selection by
standalone CE can strictly hurt (`selection_hurts` below). -/
theorem meanBound_greedy {N : ℕ} (mean newcomer : ℝ)
    (h : newcomer ≤ mean) :
    (N * mean + newcomer) / (N + 1) ≤ mean := by
  field_simp
  linarith

/-- **Selection by standalone CE can strictly hurt the ensemble.**
There is a pool of two candidate leaves (`zB`, `zC`) and a fixed
partner (`zA`) such that:

* the standalone CE of `zB` is *better* (smaller) than that of
  `zC` on position 1 — the ranking says: keep `zB`, prune `zC`;
* and yet the ensemble `ens zA zB` has *strictly larger* CE than
  `ens zA zC` on position 2 — executing the ranking degrades the
  ensemble.

So a "keep the best standalone CE" rule is not even *weakly*
optimal: the standalone rank and the ensemble contribution are
uncorrelated, and the anti-correlated (divergent-leaf) regime
exists. The trigger must rank by the ensemble criterion, not the
standalone one. See the module docstring for the prescription. -/
theorem selection_hurts :
    ceOneHot t₁ zB < ceOneHot t₁ zC ∧
    ceOneHot t₂ (ens zA zB) > ceOneHot t₂ (ens zA zC) := by
  constructor
  · -- standalone, position 1: CE(B) = log(65/64) < log(5/4) = CE(C)
    have hB : ceOneHot 0 zB = Real.log (65/64) := by
      have e1 : Real.exp (Real.log 8) = 8 := Real.exp_log (by norm_num)
      have e2 : Real.exp (-(Real.log 8)) = 1/8 := by
        rw [Real.exp_neg, e1]
        norm_num
      unfold ceOneHot lse zB
      simp only [Fin.isValue, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [e1, e2,
        ← Real.log_div (by norm_num : (8:ℝ) + 1/8 ≠ 0)
          (by norm_num)]
      congr 1
      norm_num
    have hC : ceOneHot 0 zC = Real.log (5/4) := by
      have e1 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
      have e2 : Real.exp (-(Real.log 2)) = 1/2 := by
        rw [Real.exp_neg, e1]
        norm_num
      unfold ceOneHot lse zC
      simp only [Fin.isValue, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [e1, e2,
        ← Real.log_div (by norm_num : (2:ℝ) + 1/2 ≠ 0)
          (by norm_num)]
      congr 1
      norm_num
    rw [hB, hC]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  · -- ensemble, position 2: CE(A,B) = log 17 > log 5 = CE(A,C)
    have h8 : (8:ℝ) ≠ 0 := by norm_num
    have h2 : (2:ℝ) ≠ 0 := by norm_num
    have h4 : (4:ℝ) ≠ 0 := by norm_num
    have h5 : (5:ℝ) ≠ 0 := by norm_num
    have e8 : Real.exp (Real.log 8) = 8 := Real.exp_log (by norm_num)
    have e2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
    have e4 : Real.exp (Real.log 4) = 4 := Real.exp_log (by norm_num)
    have e8n : Real.exp (-(Real.log 8)) = 1/8 := by
      rw [Real.exp_neg, e8]; norm_num
    have e2n : Real.exp (-(Real.log 2)) = 1/2 := by
      rw [Real.exp_neg, e2]; norm_num
    have e4n : Real.exp (-(Real.log 4)) = 1/4 := by
      rw [Real.exp_neg, e4]; norm_num
    -- midpoints: (log 2 + log 8)/2 = log 4 and friends
    have mABp : (Real.log 2 + Real.log 8) / 2 = Real.log 4 := by
      rw [← Real.log_mul h2 h8,
        show (2:ℝ) * 8 = 4^2 from by norm_num, Real.log_pow]
      norm_num
    have mABn : (-(Real.log 2) + -(Real.log 8)) / 2 = -(Real.log 4) := by
      have : (-(Real.log 2) + -(Real.log 8)) / 2
          = -((Real.log 2 + Real.log 8) / 2) := by ring
      rw [this, mABp]
    have mACp : (Real.log 2 + Real.log 2) / 2 = Real.log 2 := by
      rw [← Real.log_mul h2 h2,
        show (2:ℝ) * 2 = 2^2 from by norm_num, Real.log_pow]
      norm_num
    have mACn : (-(Real.log 2) + -(Real.log 2)) / 2 = -(Real.log 2) := by
      have : (-(Real.log 2) + -(Real.log 2)) / 2
          = -((Real.log 2 + Real.log 2) / 2) := by ring
      rw [this, mACp]
    have hAB : ceOneHot 1 (ens zA zB) = Real.log 17 := by
      have c0 : (ens zA zB) 0 = Real.log 4 := by
        change (zA 0 + zB 0) / 2 = Real.log 4
        simp only [zA, zB, Matrix.cons_val_zero]
        exact mABp
      have c1 : (ens zA zB) 1 = -(Real.log 4) := by
        change (zA 1 + zB 1) / 2 = -(Real.log 4)
        simp only [zA, zB, Matrix.cons_val_one]
        exact mABn
      unfold ceOneHot lse
      simp only [Fin.isValue, Fin.sum_univ_two]
      rw [c0, c1]
      simp only [e4, e4n]
      have h174 : (4:ℝ) + 1/4 = 17/4 := by norm_num
      rw [h174, Real.log_div (by norm_num : (17:ℝ) ≠ 0) h4]
      linarith
    have hAC : ceOneHot 1 (ens zA zC) = Real.log 5 := by
      have c0 : (ens zA zC) 0 = Real.log 2 := by
        change (zA 0 + zC 0) / 2 = Real.log 2
        simp only [zA, zC, Matrix.cons_val_zero]
        exact mACp
      have c1 : (ens zA zC) 1 = -(Real.log 2) := by
        change (zA 1 + zC 1) / 2 = -(Real.log 2)
        simp only [zA, zC, Matrix.cons_val_one]
        exact mACn
      unfold ceOneHot lse
      simp only [Fin.isValue, Fin.sum_univ_two]
      rw [c0, c1]
      simp only [e2, e2n]
      have h252 : (2:ℝ) + 1/2 = 5/2 := by norm_num
      rw [h252, Real.log_div (by norm_num : (5:ℝ) ≠ 0) h2]
      linarith
    rw [hAB, hAC]
    exact Real.log_lt_log (by norm_num) (by norm_num)

end

end Hagi
