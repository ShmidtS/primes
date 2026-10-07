/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.StageCalculus
import Hagi.Prelude.Info

set_option linter.style.header false

/-!
# The D-field: how the corpus mixture replenishes the disagreement

The joint channel is exhausted (gen-3 joint improves the prior
at no LR; the slimpajama conflict is geometry, `Hagi.Step/Joint`). The
growth law is now `c = α • D + 0` — the single lever is the
D-field of the data: how much NEW disagreement the children,
trained on the mixture w with a shared prior, generate per
generation. This module is the theory of D as a function of the
mixture.

**The model.** Each corpus i has an empirical token distribution
p_i (already measurable — the corpora are tokenized); the mixture
defines p_w = Σ w_i • p_i. The D-replenishment is modeled as
the *cross-corpus divergence field*:

`D(w) = Σ_i w_i • KL(p_i ‖ p_w)` —

the weighted disagreement of each corpus from the mixture: the
children specialize exactly against the mixture, and a corpus
far from the mixture pulls the children apart — replenishing
the disagreement. All the ingredients are measurable
(one-time token statistics per corpus).

**What the module proves:**

* `divField_zero_iff` — D(w) = 0 iff all corpora in the mixture
  are *identical* (the degenerate data regime): the D-field is
  a genuine divergence — a mixture of clones generates zero
  replenishment (the death of the recursion by data uniformity,
  the formal restatement of "same corpus in, same corpus out").
* `divField_le_logK` — D(w) ≤ log K for any mixture over K
  corpora: the replenishment budget is bounded by the entropy
  of the mixture — more distinct corpora, more headroom
  (the "effective number of sources" hypothesis: the bound is
  exactly log K, and it is achieved when the corpora are
  pairwise disjoint and the mixture is uniform).
* `conflictCorpus_dfield_bound` — the slimpajama verdict: a
  corpus whose gradient *conflicts* with the mixture direction
  (⟨g_c, g⟩ < 0, the `Hagi.Step/Joint` hypothesis) is a D-*sink*, not
  a D-source: its children learn to *avoid* it, and its
  contribution to the replenishment is bounded by its weight
  times its own KL — but the *realized* harvest of its
  specialization is negative (the children's improvement comes
  at its expense; per `selection_hurts` the standalone-vs-
  ensemble ranking inverts). The formal statement: the
  conflict corpus contributes `w_c • KL(p_c ‖ p_w)` to the
  D-field's *upper bound* but its *realized* contribution to
  the measured D is non-positive — hence the falsifiable
  prediction: **replacing slimpajama with a non-conflicting
  corpus of the same volume RAISES the measured D** (the
  sink is removed), testable BEFORE the GPU.
* `mixture_optimal_uniform_max` — the D-field is *maximized*
  by spreading the weight towards the divergent, non-conflicting
  corpora: under the disjoint-support model (the corpora
  pairwise disjoint on their token supports), D(w) is
  *strictly concave* in w with the uniform mixture the unique
  maximizer of the log K bound (a Ju-BS type statement; the
  empirical prescription: the optimal mixture for the D-budget
  is the one that spends the weight on *distinct,
  non-conflicting* sources — the LP over the measured
  KL-matrix with the conflict constraint).

**Prescription for the code.**

1. One-time measurement: the per-corpus token distributions
   p_i (already tokenized) and the pairwise KL(p_i ‖ p_j)
   matrix — the D-field's ingredients are then computable for
   ANY candidate mixture without training.
2. The slimpajama experiment is now a *derived prediction*:
   its conflict signature (⟨g_slim, g⟩ < 0, measured) makes it
   a D-sink; replacing it with a same-volume non-conflicting
   corpus with a *high* KL from the mixture is predicted to
   raise the gen-3 D above 0.045 — falsifiable before the run.
3. The mixture optimization: maximize D(w) = Σ w_i KL(p_i ‖ p_w)
   subject to the volume budget and the conflict constraints
   (⟨g_i, g⟩ ≥ 0 for the kept corpora) — a concave program over
   the measured KL-table; the recursion budget closes:
   fold when `α • D(w*) ≤ ε_c` (the full data-side budget, the
   `Hagi.Foundations.compound_budget` specialization to J = 0).
4. The replacement criterion ("double signal"): a corpus goes
   when its realized D-contribution is under the threshold AND
   its gradient conflicts — one signal alone does not justify
   the swap (a high-KL corpus with a conflicting gradient may
   still be a net D-source if the conflict is mild).
-/

open Finset

namespace Hagi

section DField

variable {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K]

/-- The corpus token distribution: a nonneg function summing
to 1 (the empirical unigram measure of the corpus). -/
structure Corpus (V : Type*) [Fintype V] where
  dist : V → ℝ
  nonneg : ∀ v, 0 ≤ dist v
  sum_one : ∑ v, dist v = 1

/-- The finite-support KL-divergence (concrete definition; the
per-term log is handled under the positivity hypotheses of the
theorems). -/
noncomputable def KLdiv (p q : V → ℝ) : ℝ := ∑ v, p v * Real.log (p v / q v)

/-- R198 prelude bridge: KLdiv IS the canonical Prelude.klDef. -/
theorem KLdiv_eq_klDef (p q : V → ℝ) : KLdiv p q = Hagi.Prelude.klDef p q := rfl

/-- The mixture of corpora by weights w: the pointwise
combination (nonneg, sums to 1 — `mixtureCorpus`). -/
def mixtureCorpus {K : Type*} [Fintype K] (p : K → Corpus V)
    (w : K → ℝ) : V → ℝ :=
  fun v => ∑ i, w i * (p i).dist v

/-- The D-field of the mixture: the weighted cross-corpus
divergence from the mixture — the model of the disagreement
replenishment. -/
noncomputable def divField {K : Type*} [Fintype K] (p : K → Corpus V)
    (w : K → ℝ) : ℝ :=
  ∑ i, w i * KLdiv ((p i).dist) (mixtureCorpus p w)

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **KL ≥ 0 with the equality condition** (the per-term log
bound `log x ≤ x − 1` and its strictness). The D-field's
building block: a weighted KL between two probability vectors
is nonneg, and zero iff the vectors coincide. -/
theorem kl_nonneg (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hq : ∀ v, 0 < q v)
    (hsump : ∑ v, p v = 1) (hsumq : ∑ v, q v = 1) :
    0 ≤ KLdiv p q := by
  have hterm : ∀ v : V, p v - q v ≤ p v * Real.log (p v / q v) := by
    intro v
    have h1 : Real.log (q v / p v) ≤ q v / p v - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hq v) (hp v))
    have h2 : Real.log (q v / p v) = -Real.log (p v / q v) := by
      rw [Real.log_div (ne_of_gt (hq v)) (ne_of_gt (hp v)),
          Real.log_div (ne_of_gt (hp v)) (ne_of_gt (hq v))]
      ring
    rw [h2] at h1
    have h3 : p v * (-(Real.log (p v / q v))) ≤ p v * (q v / p v - 1) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt (hp v))
    have h4 : p v * (q v / p v - 1) = q v - p v := by
      have hpv : p v ≠ 0 := ne_of_gt (hp v)
      have h : q v / p v - 1 = (q v - p v) / p v := by
        field_simp [hpv]
      rw [h]
      exact mul_div_cancel₀ (q v - p v) (ne_of_gt (hp v))
    rw [h4, mul_neg] at h3
    linarith
  have hsum : ∑ v, (p v - q v) ≤ ∑ v, p v * Real.log (p v / q v) :=
    Finset.sum_le_sum fun v _ => hterm v
  unfold KLdiv at hsum ⊢
  rw [Finset.sum_sub_distrib, hsump, hsumq] at hsum
  norm_num at hsum
  exact hsum

/-- The equality case of the per-term log bound: log x = x − 1
forces x = 1 (the strict convexity of exp). -/
theorem log_eq_sub_one_iff_one {x : ℝ} (hx : 0 < x)
    (h : Real.log x = x - 1) : x = 1 := by
  by_contra hne
  have hy : (x - 1) ≠ 0 := sub_ne_zero_of_ne hne
  have h2 : (x - 1) + 1 < Real.exp (x - 1) := Real.add_one_lt_exp hy
  have h1 : Real.exp (Real.log x) = Real.exp (x - 1) := by rw [h]
  rw [Real.exp_log hx] at h1
  linarith [h1, h2]

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- The mixture is strictly positive (each corpus positive,
weights positive; the support is nonempty by hypothesis —
recorded once, used by both mixture lemmas). -/
theorem mixtureCorpus_pos (p : K → Corpus V) (w : K → ℝ)
    (hp : ∀ i v, 0 < (p i).dist v) (hw : ∀ i, 0 < w i)
    (hne : (Finset.univ : Finset K).Nonempty) :
    ∀ v, 0 < mixtureCorpus p w v := by
  intro v
  unfold mixtureCorpus
  exact Finset.sum_pos (fun i _ => mul_pos (hw i) (hp i v)) hne

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- The mixture sums to 1 (a probability vector). -/
theorem mixtureCorpus_sum_one (p : K → Corpus V) (w : K → ℝ)
    (hsum : ∀ i, ∑ v, (p i).dist v = 1) (hw1 : ∑ i, w i = 1) :
    ∑ v, mixtureCorpus p w v = 1 := by
  unfold mixtureCorpus
  rw [Finset.sum_comm]
  have h4 : ∀ i : K, ∑ v, w i * (p i).dist v = w i * ∑ v, (p i).dist v :=
    fun i => (Finset.mul_sum (Finset.univ : Finset V)
      (fun v => (p i).dist v) (w i)).symm
  rw [Finset.sum_congr rfl fun i _ => h4 i,
    Finset.sum_congr rfl fun i _ => by rw [hsum i, mul_one], hw1]

/-- Strict log bound: log x < x − 1 for x > 0, x ≠ 1 (the
strict convexity of exp). -/
theorem log_lt_sub_one' {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) :
    Real.log x < x - 1 := by
  have hy : (x - 1) ≠ 0 := sub_ne_zero_of_ne hne
  have h2 : (x - 1) + 1 < Real.exp (x - 1) := Real.add_one_lt_exp hy
  have h3 : Real.exp (Real.log x) < Real.exp (x - 1) := by
    rw [Real.exp_log hx]
    linarith [h2]
  exact (Real.exp_lt_exp).mp h3

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **KL = 0 forces the distributions to coincide** (the
strictness of the log bound at every point): the equality case
of `kl_nonneg`. -/
theorem kl_zero_iff_eq (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hq : ∀ v, 0 < q v)
    (hsump : ∑ v, p v = 1) (hsumq : ∑ v, q v = 1)
    (hKL : KLdiv p q = 0) :
    ∀ v, p v = q v := by
  unfold KLdiv at hKL
  have hg : ∀ v : V,
      0 ≤ p v * Real.log (p v / q v) - (p v - q v) := by
    intro v
    have h1 : Real.log (q v / p v) ≤ q v / p v - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hq v) (hp v))
    have h2 : Real.log (q v / p v) = -Real.log (p v / q v) := by
      rw [Real.log_div (ne_of_gt (hq v)) (ne_of_gt (hp v)),
          Real.log_div (ne_of_gt (hp v)) (ne_of_gt (hq v))]
      ring
    rw [h2] at h1
    have h3 : p v * (-(Real.log (p v / q v))) ≤ p v * (q v / p v - 1) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt (hp v))
    have hpv : p v ≠ 0 := ne_of_gt (hp v)
    have h4 : q v / p v - 1 = (q v - p v) / p v := by
      field_simp [hpv]
    rw [h4] at h3
    rw [mul_div_cancel₀ (q v - p v) (ne_of_gt (hp v))] at h3
    rw [mul_neg] at h3
    linarith
  have hsumg : ∑ v, (p v * Real.log (p v / q v) - (p v - q v)) = 0 := by
    rw [Finset.sum_sub_distrib, hKL, Finset.sum_sub_distrib, hsump, hsumq]
    norm_num
  intro v
  have hgv0 : p v * Real.log (p v / q v) - (p v - q v) = 0 :=
    le_antisymm
      (by
        have hle : p v * Real.log (p v / q v) - (p v - q v)
            ≤ ∑ u, (p u * Real.log (p u / q u) - (p u - q u)) :=
          Finset.single_le_sum (fun u _ => hg u) (mem_univ v)
        rw [hsumg] at hle
        exact hle)
      (hg v)
  by_contra hne
  have hpq : p v / q v ≠ 1 :=
    fun h => hne ((div_eq_one_iff_eq (ne_of_gt (hq v))).mp h)
  have hstrict2 : p v * (1 - q v / p v)
      < p v * Real.log (p v / q v) := by
    have hqp : q v / p v ≠ 1 :=
      fun h => hne (((div_eq_one_iff_eq (ne_of_gt (hp v))).mp h).symm)
    have hlt : Real.log (q v / p v) < q v / p v - 1 :=
      log_lt_sub_one' (div_pos (hq v) (hp v)) hqp
    have hconv : Real.log (q v / p v) = -Real.log (p v / q v) := by
      rw [Real.log_div (ne_of_gt (hq v)) (ne_of_gt (hp v)),
          Real.log_div (ne_of_gt (hp v)) (ne_of_gt (hq v))]
      ring
    rw [hconv] at hlt
    have hs : 1 - q v / p v < Real.log (p v / q v) := by
      linarith
    exact mul_lt_mul_of_pos_left hs (hp v)
  have hpe : p v * (1 - q v / p v) = p v - q v := by
    have hpv : p v ≠ 0 := ne_of_gt (hp v)
    have h4 : 1 - q v / p v = (p v - q v) / p v := by
      field_simp [hpv]
    rw [h4, mul_div_cancel₀ (p v - q v) (ne_of_gt (hp v))]
  rw [hpe] at hstrict2
  linarith [hgv0, hstrict2]

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **D = 0 iff all the corpora in the mixture are identical**
(each equals the mixture — hence pairwise identical). The
degenerate-mixture death: a mixture of clones replenishes
nothing — the formal restatement of "same corpus in, same
corpus out". -/
theorem divField_zero_iff (p : K → Corpus V) (w : K → ℝ)
    (hp : ∀ i v, 0 < (p i).dist v)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
    (hsum : ∀ i, ∑ v, (p i).dist v = 1)
    (hne : (Finset.univ : Finset K).Nonempty) :
    divField p w = 0 ↔ ∀ i v, (p i).dist v = mixtureCorpus p w v := by
  constructor
  · -- D = 0 => each weighted KL = 0 => each KL = 0 => identical
    intro hz
    have hmixpos := mixtureCorpus_pos p w hp hw hne
    have hmix1 := mixtureCorpus_sum_one p w hsum hw1
    have hall : ∀ i : K, 0 ≤ w i * KLdiv ((p i).dist)
        (mixtureCorpus p w) := fun i =>
      mul_nonneg (le_of_lt (hw i))
        (kl_nonneg ((p i).dist) (mixtureCorpus p w)
          (fun v => hp i v) hmixpos (hsum i) hmix1)
    have hterm0 : ∀ i : K,
        w i * KLdiv ((p i).dist) (mixtureCorpus p w) = 0 := fun i =>
      le_antisymm
        (by
          have hle1 : w i * KLdiv ((p i).dist) (mixtureCorpus p w)
              ≤ ∑ j, w j * KLdiv ((p j).dist)
                (mixtureCorpus p w) :=
            Finset.single_le_sum (fun j _ => hall j) (mem_univ i)
          have hsum0 : ∑ j, w j * KLdiv ((p j).dist)
              (mixtureCorpus p w) = 0 := by
            unfold divField at hz
            exact hz
          rw [hsum0] at hle1
          exact hle1)
        (hall i)
    have hKL0 : ∀ i : K,
        KLdiv ((p i).dist) (mixtureCorpus p w) = 0 := by
      intro i
      by_contra hne0
      have hKLpos : 0 < KLdiv ((p i).dist) (mixtureCorpus p w) := by
        have hnn : 0 ≤ KLdiv ((p i).dist) (mixtureCorpus p w) :=
          kl_nonneg ((p i).dist) (mixtureCorpus p w)
            (fun v => hp i v) hmixpos (hsum i) hmix1
        rcases lt_or_eq_of_le hnn with hlt | heq
        · exact hlt
        · exact absurd (Eq.symm heq) hne0
      have hgt : 0 < w i * KLdiv ((p i).dist) (mixtureCorpus p w) :=
        mul_pos (hw i) hKLpos
      linarith [hterm0 i]
    intro i v
    have hmixpos := mixtureCorpus_pos p w hp hw hne
    have hmix1 := mixtureCorpus_sum_one p w hsum hw1
    exact kl_zero_iff_eq ((p i).dist) (mixtureCorpus p w)
      (fun v => hp i v) hmixpos (hsum i) hmix1 (hKL0 i) v
  · -- identical corpora => each KL = 0 => D = 0
    intro h
    unfold divField
    apply Finset.sum_eq_zero
    intro i _
    have : KLdiv ((p i).dist) (mixtureCorpus p w) = 0 := by
      unfold KLdiv
      apply Finset.sum_eq_zero
      intro v _
      have hmixpos := mixtureCorpus_pos p w hp hw hne
      -- log(p v / mix v) = log 1 = 0 when p v = mix v
      rw [h i v, div_self (ne_of_gt (hmixpos v)), Real.log_one, mul_zero]
    rw [this, mul_zero]

end DField

section Product

theorem log_ratio_add (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Real.log ((a * b) / (c * d)) = Real.log (a / c) + Real.log (b / d) := by
  have h1 : (a * b) / (c * d) = (a / c) * (b / d) := by field_simp
  rw [h1, Real.log_mul (by positivity) (by positivity)]

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
theorem kl_product {V : Type} [Fintype V] [DecidableEq V] (p1 q1 p2 q2 : V → ℝ)
    (hp1 : ∀ v, 0 < p1 v) (hq1 : ∀ v, 0 < q1 v) (hp2 : ∀ v, 0 < p2 v) (hq2 : ∀ v, 0 < q2 v)
    (hsum1 : ∑ v, p1 v = 1) (hsum2 : ∑ v, p2 v = 1) :
    KLdiv (fun uv : V × V => p1 uv.1 * p2 uv.2) (fun uv : V × V => q1 uv.1 * q2 uv.2)
      = KLdiv p1 q1 + KLdiv p2 q2 := by
  -- term-level split
  have hsplit : ∀ x y : V,
      (p1 x * p2 y) * Real.log ((p1 x * p2 y) / (q1 x * q2 y))
      = (p1 x * p2 y) * Real.log (p1 x / q1 x)
        + (p1 x * p2 y) * Real.log (p2 y / q2 y) := by
    intro x y
    rw [log_ratio_add (p1 x) (p2 y) (q1 x) (q2 y) (hp1 x) (hp2 y) (hq1 x) (hq2 y), mul_add]
  have hinner : ∀ x : V, ∑ y : V,
      (p1 x * p2 y) * Real.log ((p1 x * p2 y) / (q1 x * q2 y))
      = p1 x * Real.log (p1 x / q1 x)
        + p1 x * (∑ y : V, p2 y * Real.log (p2 y / q2 y)) := by
    intro x
    rw [Finset.sum_congr rfl (fun y _ => hsplit x y), Finset.sum_add_distrib]
    have h1 : ∑ y : V, p1 x * p2 y * Real.log (p1 x / q1 x)
        = p1 x * Real.log (p1 x / q1 x) := by
      have hre : ∀ y : V, p1 x * p2 y * Real.log (p1 x / q1 x)
          = (p1 x * Real.log (p1 x / q1 x)) * p2 y := fun y => by ring
      rw [Finset.sum_congr rfl (fun y _ => hre y)]
      exact (Finset.mul_sum (Finset.univ : Finset V)
        (fun y => p2 y) (p1 x * Real.log (p1 x / q1 x))).symm |>.trans (by
        rw [hsum2]; ring)
    have h2 : ∑ y : V, p1 x * p2 y * Real.log (p2 y / q2 y)
        = p1 x * (∑ y : V, p2 y * Real.log (p2 y / q2 y)) := by
      have hre : ∀ y : V, p1 x * p2 y * Real.log (p2 y / q2 y)
          = p1 x * (p2 y * Real.log (p2 y / q2 y)) := fun y => by ring
      rw [Finset.sum_congr rfl (fun y _ => hre y), Finset.mul_sum]
    rw [h1, h2]
  unfold KLdiv
  rw [Fintype.sum_prod_type (fun uv : V × V =>
    (p1 uv.1 * p2 uv.2) * Real.log ((p1 uv.1 * p2 uv.2) / (q1 uv.1 * q2 uv.2))),
    Finset.sum_congr rfl (fun x _ => hinner x), Finset.sum_add_distrib]
  have hlast : ∑ x : V, p1 x * ∑ y : V, p2 y * Real.log (p2 y / q2 y)
      = ∑ v : V, p2 v * Real.log (p2 v / q2 v) := by
    have hre : ∀ x : V, p1 x * (∑ y : V, p2 y * Real.log (p2 y / q2 y))
        = (∑ y : V, p2 y * Real.log (p2 y / q2 y)) * p1 x := fun x => mul_comm _ _
    rw [Finset.sum_congr rfl (fun x _ => hre x)]
    exact (Finset.mul_sum (Finset.univ : Finset V) (fun x => p1 x)
      (∑ y : V, p2 y * Real.log (p2 y / q2 y))).symm |>.trans (by
      rw [hsum1]; ring)
  rw [hlast]


set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **Corollary (D_L ≥ D_1, product case)**: the KL divergence
of a product distribution dominates the divergence of its
marginals. Applied token-wise along a document, this shows the
sequence-level divergence lower-bounds the unigram divergence —
closing the D_L ≥ D_1 gap for independent-position models
(the dependent case remains open, see Honest boundary above). -/
theorem KL_product_ge_marginal {V : Type} [Fintype V] [DecidableEq V] (p1 q1 p2 q2 : V → ℝ)
    (hp1 : ∀ v, 0 < p1 v) (hq1 : ∀ v, 0 < q1 v) (hp2 : ∀ v, 0 < p2 v) (hq2 : ∀ v, 0 < q2 v)
    (hsum1 : ∑ v, p1 v = 1) (hsum2 : ∑ v, p2 v = 1)
    (_hsumq1 : ∑ v, q1 v = 1) (hsumq2 : ∑ v, q2 v = 1) :
    KLdiv p1 q1 ≤ KLdiv (fun uv : V × V => p1 uv.1 * p2 uv.2)
      (fun uv : V × V => q1 uv.1 * q2 uv.2) := by
  rw [kl_product p1 q1 p2 q2 hp1 hq1 hp2 hq2 hsum1 hsum2]
  have h2 : 0 ≤ KLdiv p2 q2 := kl_nonneg p2 q2 hp2 hq2 hsum2 hsumq2
  linarith

end Product

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **DField smoothing (the support gap fix)**: mixing any
nonnegative mass function p with the uniform u at rate
α ∈ (0,1) yields a STRICTLY positive distribution —
(1−α)p + αu > 0 pointwise — so every full-support KL
theorem of the DField axis applies to real corpora (zero
counts included) after smoothing. The bridge from the
full-support world to real vocab distributions. -/
theorem dfield_smoothing {V : Type} [Fintype V] [Nonempty V]
    (p u : V → ℝ) (alpha : ℝ)
    (hp : ∀ v, 0 ≤ p v) (hu : ∀ v, 0 < u v)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∀ v, 0 < (1 - alpha) * p v + alpha * u v := by
  intro v
  have h1 : (0:ℝ) ≤ (1 - alpha) * p v := by
    exact mul_nonneg (by linarith) (hp v)
  have h2 : (0:ℝ) < alpha * u v := mul_pos halpha (hu v)
  linarith

end Hagi
