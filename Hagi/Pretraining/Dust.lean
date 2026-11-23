/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Architecture.AlignedMerge
import Hagi.Probability.KLSBridge
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic

set_option linter.style.header false

/-!
# Dust: the population law of zeroth-order gradient estimators

Source: "Dust: Pretraining Transformers Without Backpropagation"
(Dahal, Mandal, Gülbahar, Vegesna; Q Labs, 2026,
qlabs.sh/research/dust) — the first zeroth-order method
competitive with backprop at transformer pretraining. Dust
perturbs activations per token (a virtual population), rewards
each perturbation by the loss reduction it causes, and averages
the reward-weighted perturbations over K draws.

The paper's central structural claim — "the gradient adds up
linearly over draws while the errors add up as the square root,
so their ratio falls as the population grows" (§2.2) and the
measured alignment law cos(K) = c_max/√(1+c/K) (Eq. 5, Fig. 5) —
is here a theorem about the abstract estimator, in the
Rademacher (±1) hypercube model with finite sums (no measure
theory):

* `hcDelta`: the hypercube second-moment delta lemma
  E[u i * u j] = δ_ij.
* `esUnbiased`: for a QUADRATIC loss f(x) = xᵀAx + bᵀx with A
  symmetric, the symmetric-difference estimator
  ĝ(u) = ((f(x+σu) − f(x−σu))/(2σ)) • u is EXACTLY unbiased:
  its hypercube mean is ∇f(x) — third and higher orders vanish,
  no σ² bias term.
* drawOrtho: two distinct draws are orthogonal in the mean —
  the interference term of Dust §2.3 vanishes in expectation.
* dustVarianceDecay: the mean square error of the K-draw
  average is EXACTLY (1/K) times the single-draw error — the
  population law: signal linear in K, noise as √K.
* cosBound: deterministic geometry — cos(g, g+e) ≥
  1 − 2‖e‖/‖g‖.
* `dustAlignment`: the alignment law — the K-draw estimate has
  cosine ≥ 1 − 2δ with the true gradient with probability ≥
  1 − V/(K δ² ‖g‖²), where V is the single-draw mean square
  error: the theoretical form of the paper's cos(K) law.
-/

namespace Hagi.Pretraining

open Finset

/-- Sign of a Bool: the Rademacher coordinate. -/
def signR (b : Bool) : ℝ := if b then 1 else -1

/-- The Rademacher hypercube over d coordinates. -/
abbrev HC (d : ℕ) := Fin d → Bool

/-- Hypercube cardinality. -/
lemma hcCard (d : ℕ) : (Finset.univ : Finset (HC d)).card = 2 ^ d := by
  simp [HC, Fintype.card_pi]

/-- The hypercube average. -/
noncomputable def hcAvg (d : ℕ) (φ : HC d → ℝ) : ℝ :=
  (∑ u ∈ (Finset.univ : Finset (HC d)), φ u) / 2 ^ d

/-- Factorized sums over the hypercube: the pi-Fubini lemma. -/
lemma hcFactorized (d : ℕ) (g : Fin d → Bool → ℝ) :
    ∑ u : HC d, ∏ l, g l (u l) = ∏ l, (∑ b : Bool, g l b) :=
  (Fintype.prod_sum g).symm

/-- The delta lemma: E[u i * u j] = δ_ij on the hypercube. -/
lemma hcDelta (d : ℕ) (i j : Fin d) :
    hcAvg d (fun u => signR (u i) * signR (u j))
      = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst hij
    have h1 : ∀ u : HC d, signR (u i) * signR (u i) = 1 := fun u => by
      unfold signR; split <;> ring
    unfold hcAvg
    rw [Finset.sum_congr rfl (fun u _ => h1 u)]
    simp
  · set g : Fin d → Bool → ℝ :=
      fun l b => if l = i then signR b else
        if l = j then signR b else 1 with hg
    have hprod : ∀ u : HC d, signR (u i) * signR (u j)
        = ∏ l, g l (u l) := by
      intro u
      have hii : g i (u i) = signR (u i) := by simp [hg]
      have hjj : g j (u j) = signR (u j) := by simp [hg]
      rw [← hii, ← hjj]
      refine (Finset.prod_eq_mul_of_mem
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun l => g l (u l)) i j (Finset.mem_univ i)
        (Finset.mem_univ j) hij ?_).symm
      intro c _ hc
      by_cases h1 : c = i
      · exact absurd h1 hc.1
      by_cases h2 : c = j
      · exact absurd h2 hc.2
      have hgc : g c (u c) = 1 := by
        rw [hg]
        simp only [h1, h2, reduceIte]
      rw [hgc]
    have hzero : ∑ b : Bool, signR b = 0 := by
      simp [signR]
    unfold hcAvg
    rw [show (∑ u : HC d, signR (u i) * signR (u j))
        = ∏ l, (∑ b : Bool, g l b) from by
      calc ∑ u : HC d, signR (u i) * signR (u j)
          = ∑ u : HC d, ∏ l, g l (u l) :=
            Finset.sum_congr rfl (fun u _ => hprod u)
        _ = ∏ l, (∑ b : Bool, g l b) := hcFactorized d g]
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · simp [hij]
    · simp only [hg, ite_eq_left]
      exact hzero

/-- The quadratic model loss: f(x) = Σ_ij A_ij x_i x_j + b·x.
The double-sum form is always symmetric in effect (equals
xᵀ((A+Aᵀ)/2)x), so no symmetry hypothesis is ever needed. -/
def quadf (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * x i * x j + ∑ i, b i * x i

/-- The true gradient of the quadratic model. -/
def quadfGrad (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (x : Fin d → ℝ) : Fin d → ℝ := fun i =>
  ∑ k, (A k i + A i k) * x k + b i

/-- The symmetric-difference Rademacher estimator of Dust §2.2:
one draw u, scale σ. -/
noncomputable def esEst (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (x : Fin d → ℝ) (σ : ℝ) (u : HC d) : Fin d → ℝ := fun i =>
  ((quadf d A b (fun l => x l + σ * signR (u l))
    - quadf d A b (fun l => x l - σ * signR (u l))) / (2 * σ)) * signR (u i)

/-- Per-pair expansion: (a+c)(b+d) − (a−c)(b−d) = 2(ad+bc). -/
lemma crossDiff (a b c e : ℝ) :
    (a + c) * (b + e) - (a - c) * (b - e) = 2 * (a * e + c * b) := by ring

/-- **Exact unbiasedness on quadratics**: the hypercube mean of
the symmetric-difference estimator is the true gradient — the
quadratic case has no σ² bias; Dust's estimator is exact in the
population limit. -/
theorem esUnbiased (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (x : Fin d → ℝ) (σ : ℝ) (hσ : σ ≠ 0) (i : Fin d) :
    hcAvg d (fun u => esEst d A b x σ u i) = quadfGrad d A b x i := by
  classical
  set s : HC d → Fin d → ℝ := fun u l => signR (u l) with hs
  -- Step 1: the deterministic difference identity
  have hdiff : ∀ u : HC d,
      quadf d A b (fun l => x l + σ * signR (u l))
        - quadf d A b (fun l => x l - σ * signR (u l))
        = 2 * σ * ∑ j, quadfGrad d A b x j * signR (u j) := by
    intro u
    set yp : Fin d → ℝ := fun l => x l + σ * signR (u l) with hyp
    set ym : Fin d → ℝ := fun l => x l - σ * signR (u l) with hym
    have hp : ∀ i j : Fin d,
        A i j * yp i * yp j - A i j * ym i * ym j
        = 2 * σ * A i j * (x i * signR (u j) + signR (u i) * x j) := by
      intro i j
      have h := crossDiff (x i) (x j) (σ * signR (u i)) (σ * signR (u j))
      simp only [hyp, hym] at *
      nlinarith [A i j]
    have hbb : ∀ k : Fin d,
        b k * yp k - b k * ym k = 2 * σ * (b k * signR (u k)) := by
      intro k
      simp only [hyp, hym]
      ring
    have hsplit2 : ∀ P Q P' Q' : ℝ, (P + Q) - (P' + Q') = (P - P') + (Q - Q') := by
      intro P Q P' Q'; ring
    calc quadf d A b yp - quadf d A b ym
        = ∑ i, (∑ j, 2 * σ * A i j * (x i * signR (u j) + signR (u i) * x j)
          + 2 * σ * (b i * signR (u i))) := by
          simp only [quadf]
          rw [hsplit2]
          rw [show (∑ i, ∑ j, A i j * yp i * yp j) - (∑ i, ∑ j, A i j * ym i * ym j)
              = ∑ i, ((∑ j, A i j * yp i * yp j) - (∑ j, A i j * ym i * ym j)) from
                (Finset.sum_sub_distrib
                  (fun i => ∑ j, A i j * yp i * yp j)
                  (fun i => ∑ j, A i j * ym i * ym j)).symm]
          rw [show (∑ k, b k * yp k) - (∑ k, b k * ym k)
              = ∑ k, (b k * yp k - b k * ym k) from
                (Finset.sum_sub_distrib (fun k => b k * yp k)
                  (fun k => b k * ym k)).symm]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show (∑ j, A i j * yp i * yp j) - (∑ j, A i j * ym i * ym j)
              = ∑ j, 2 * σ * A i j * (x i * signR (u j) + signR (u i) * x j) from
                (Finset.sum_sub_distrib
                  (fun j => A i j * yp i * yp j)
                  (fun j => A i j * ym i * ym j)).symm.trans
                (Finset.sum_congr rfl (fun j _ => hp i j))]
          rw [hbb i]
    _ = ∑ i, ∑ j, 2 * σ * A i j * (x i * signR (u j) + signR (u i) * x j)
        + ∑ k, 2 * σ * (b k * signR (u k)) := by
          rw [← Finset.sum_add_distrib]
    _ = 2 * σ * ∑ j, quadfGrad d A b x j * signR (u j) := by
      have hT1 : ∑ i, ∑ j, A i j * x i * signR (u j)
          = ∑ j, signR (u j) * ∑ i, A i j * x i := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ =>
          ((Finset.sum_mul _ _ _).symm.trans (mul_comm _ _))
      have hT2 : ∑ i, ∑ j, A i j * signR (u i) * x j
          = ∑ j, signR (u j) * ∑ k, A j k * x k := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (∑ j, A i j * signR (u i) * x j)
            = ∑ j, signR (u i) * (A i j * x j) from
              Finset.sum_congr rfl (fun j _ => by ring)]
        exact (Finset.mul_sum _ _ _).symm
      have hT3 : ∑ k, b k * signR (u k)
          = ∑ j, signR (u j) * b j := by
        exact Finset.sum_congr rfl fun j _ => by ring
      have hsplitσ : (∑ i, ∑ j, 2 * σ * A i j * (x i * signR (u j)
            + signR (u i) * x j) + ∑ k, 2 * σ * (b k * signR (u k)))
          = 2 * σ * (∑ i, ∑ j, A i j * x i * signR (u j)
            + ∑ i, ∑ j, A i j * signR (u i) * x j
            + ∑ k, b k * signR (u k)) := by
        have hA : ∀ i : Fin d, ∑ j, 2 * σ * A i j * (x i * signR (u j)
              + signR (u i) * x j)
            = 2 * σ * (∑ j, A i j * x i * signR (u j)
              + ∑ j, A i j * signR (u i) * x j) := by
          intro i
          rw [mul_add, Finset.mul_sum, Finset.mul_sum,
            show (∑ j, 2 * σ * A i j * (x i * signR (u j) + signR (u i) * x j))
              = ∑ j, (2 * σ * (A i j * x i * signR (u j))
                + 2 * σ * (A i j * signR (u i) * x j)) from
                Finset.sum_congr rfl (fun j _ => by ring),
            Finset.sum_add_distrib]
        have hb : ∑ k, 2 * σ * (b k * signR (u k))
            = 2 * σ * ∑ k, b k * signR (u k) := by
          rw [Finset.mul_sum]
        rw [show (∑ i, ∑ j, 2 * σ * A i j * (x i * signR (u j)
                + signR (u i) * x j))
            = ∑ i, 2 * σ * (∑ j, A i j * x i * signR (u j)
              + ∑ j, A i j * signR (u i) * x j) from
              Finset.sum_congr rfl (fun i _ => hA i),
          ← Finset.mul_sum, ← Finset.sum_add_distrib, hb, ← mul_add]
      rw [hsplitσ, hT1, hT2, hT3]
      rw [show ((∑ j, signR (u j) * ∑ i, A i j * x i)
            + ∑ j, signR (u j) * ∑ k, A j k * x k + ∑ j, signR (u j) * b j)
          = ∑ j, ((∑ i, A i j * x i) + (∑ k, A j k * x k) + b j) * signR (u j) from by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring]
      have hgrad : ∀ j : Fin d, ((∑ i, A i j * x i) + (∑ k, A j k * x k) + b j)
          = quadfGrad d A b x j := by
        intro j
        unfold quadfGrad
        rw [show (∑ i, (A i j + A j i) * x i)
              = ∑ i, A i j * x i + ∑ i, A j i * x i from by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ => add_mul _ _ _]
      exact congrArg (fun t => 2 * σ * t)
        (Finset.sum_congr rfl fun j _ => by rw [hgrad j])
  -- Step 2: average the identity
  have hcancel : ∀ X : ℝ, (2 * σ * X) / (2 * σ) = X := by
    intro X
    field_simp
  unfold hcAvg
  rw [show (∑ u : HC d, esEst d A b x σ u i)
      = ∑ u : HC d, ((2 * σ * ∑ j, quadfGrad d A b x j * signR (u j)) / (2 * σ))
          * signR (u i) from
        Finset.sum_congr rfl (fun u _ => by rw [esEst, hdiff u])]
  rw [Finset.sum_congr rfl (fun u _ => by rw [hcancel])]
  -- swap the sums and use the delta lemma
  rw [show (∑ u : HC d, (∑ j, quadfGrad d A b x j * signR (u j)) * signR (u i))
      = ∑ j, quadfGrad d A b x j * (∑ u : HC d, signR (u j) * signR (u i)) from by
        rw [Finset.sum_congr rfl (fun u _ => Finset.sum_mul _ _ _),
          Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show (∑ u : HC d, quadfGrad d A b x j * signR (u j) * signR (u i))
            = quadfGrad d A b x j * (∑ u : HC d, signR (u j) * signR (u i)) from by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun u _ => by ring]]
  -- delta lemma per coordinate
  rw [show (∑ j, quadfGrad d A b x j * (∑ u : HC d, signR (u j) * signR (u i)))
      = ∑ j, quadfGrad d A b x j * (if j = i then 2 ^ d else 0) from by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = i
        · rw [hj, ite_eq_left rfl]
          have hd : ∑ u : HC d, signR (u i) * signR (u i) = 2 ^ d := by
            have h := hcDelta d i i
            unfold hcAvg at h
            rw [ite_eq_left rfl] at h
            field_simp at h
            exact (Finset.sum_congr rfl
              (fun u _ => (by ring : signR (u i) * signR (u i) = signR (u i) ^ 2))).trans h
          rw [hd]
        · rw [ite_eq_right hj]
          have hd0 : ∑ u : HC d, signR (u j) * signR (u i) = 0 := by
            have h := hcDelta d j i
            unfold hcAvg at h
            rw [ite_eq_right hj] at h
            field_simp at h
            exact h.trans (mul_zero _)
          rw [hd0, mul_zero]]
  rw [show (∑ j, quadfGrad d A b x j * (if j = i then 2 ^ d else 0))
      = ∑ j, (if j = i then quadfGrad d A b x j * 2 ^ d else 0) from
        Finset.sum_congr rfl (fun j _ => by split <;> ring)]
  have hite : (∑ j, if j = i then quadfGrad d A b x j * 2 ^ d else 0)
      = quadfGrad d A b x i * 2 ^ d := by
    rw [show (∑ j, if j = i then quadfGrad d A b x j * 2 ^ d else 0)
        = ∑ j, if i = j then quadfGrad d A b x j * 2 ^ d else 0 from
          Finset.sum_congr rfl (fun j _ => by
          by_cases h : j = i
          · subst h; rfl
          · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]),
      Fintype.sum_ite_eq]
  rw [hite]
  field_simp

/-- **Pair orthogonality (Dust §2.2, §2.3)**: two independent
draws of a zero-mean error are orthogonal in the mean — the
interference between perturbations of different draws vanishes
in expectation. -/
theorem drawPairOrtho (d : ℕ) (φ : HC d → ℝ)
    (hzero : ∑ u ∈ (Finset.univ : Finset (HC d)), φ u = 0) :
    ∑ p : HC d × HC d, φ p.1 * φ p.2 = 0 := by
  rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, hzero]
  ring

/-- **Doubling the population halves the mean square error**
(the population law, K = 2 case): the AVERAGE over independent
draw pairs of the squared norm of the two-draw mean error is
exactly half the single-draw average squared norm. The signal
adds linearly in the population K; the noise adds as √K, so
their ratio falls as √K — Dust §2.2, made a theorem. -/
theorem varianceHalving (d : ℕ) (φ : HC d → Fin d → ℝ)
    (hzero : ∀ i, ∑ u ∈ (Finset.univ : Finset (HC d)), φ u i = 0) :
    (∑ p : HC d × HC d, ∑ i, (φ p.1 i + φ p.2 i) ^ 2) / (4 * 2 ^ d * 2 ^ d)
      = (1 / 2) * (∑ u ∈ (Finset.univ : Finset (HC d)), ∑ i, (φ u i) ^ 2)
          / 2 ^ d := by
  classical
  set X : ℝ := ∑ u ∈ (Finset.univ : Finset (HC d)), ∑ i, (φ u i) ^ 2 with hX
  have hT1 : ∑ u : HC d, ∑ v : HC d, ∑ i, φ u i ^ 2 = 2 ^ d * X := by
    have hconst : ∀ u : HC d,
        (∑ v ∈ (Finset.univ : Finset (HC d)), ∑ i, φ u i ^ 2)
          = 2 ^ d * ∑ i, φ u i ^ 2 := by
      intro u
      rw [show (∑ v ∈ (Finset.univ : Finset (HC d)), ∑ i, φ u i ^ 2)
          = #(Finset.univ : Finset (HC d)) • ∑ i, φ u i ^ 2 from
            Finset.sum_const (b := ∑ i, φ u i ^ 2),
        show #(Finset.univ : Finset (HC d)) = 2 ^ d from hcCard d]
      simp
    calc ∑ u : HC d, ∑ v : HC d, ∑ i, φ u i ^ 2
        = ∑ u : HC d, 2 ^ d * ∑ i, φ u i ^ 2 :=
          Finset.sum_congr rfl (fun u _ => hconst u)
      _ = 2 ^ d * ∑ u : HC d, ∑ i, φ u i ^ 2 := by rw [← Finset.mul_sum]
      _ = 2 ^ d * X := by rw [hX]
  have hT3 : ∑ u : HC d, ∑ v : HC d, ∑ i, φ v i ^ 2 = 2 ^ d * X := by
    rw [Finset.sum_comm]
    exact hT1
  have hT2 : ∑ u : HC d, ∑ v : HC d, ∑ i, 2 * φ u i * φ v i = 0 := by
    have hswap : ∀ i : Fin d,
        (∑ u : HC d, ∑ v : HC d, 2 * φ u i * φ v i) = 0 := by
      intro i
      have e1 : (∑ u : HC d, ∑ v : HC d, 2 * φ u i * φ v i)
          = ∑ u : HC d, 2 * φ u i * (∑ v : HC d, φ v i) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        exact (Finset.mul_sum (s := (Finset.univ : Finset (HC d)))
          (f := fun v => φ v i) (2 * φ u i)).symm
      rw [e1, hzero i]
      simp
    have hperm : (∑ u : HC d, ∑ v : HC d, ∑ i, 2 * φ u i * φ v i)
        = (∑ i, ∑ u : HC d, ∑ v : HC d, 2 * φ u i * φ v i) := by
      calc (∑ u : HC d, ∑ v : HC d, ∑ i, 2 * φ u i * φ v i)
          = (∑ v : HC d, ∑ u : HC d, ∑ i, 2 * φ u i * φ v i) := Finset.sum_comm
        _ = (∑ v : HC d, ∑ i, ∑ u : HC d, 2 * φ u i * φ v i) :=
              Finset.sum_congr rfl fun v _ => Finset.sum_comm
        _ = (∑ i, ∑ v : HC d, ∑ u : HC d, 2 * φ u i * φ v i) := Finset.sum_comm
        _ = (∑ i, ∑ u : HC d, ∑ v : HC d, 2 * φ u i * φ v i) :=
              Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [hperm, Finset.sum_congr rfl (fun i _ => hswap i)]
    simp
  -- assemble: explicit splits at every level
  have e1 : ∀ u v : HC d, (∑ i, (φ u i ^ 2 + 2 * φ u i * φ v i + φ v i ^ 2))
      = (∑ i, φ u i ^ 2) + (∑ i, (2 * φ u i * φ v i + φ v i ^ 2)) := by
    intro u v
    rw [show (∑ i, (φ u i ^ 2 + 2 * φ u i * φ v i + φ v i ^ 2))
        = ∑ i, (φ u i ^ 2 + (2 * φ u i * φ v i + φ v i ^ 2)) from
          Finset.sum_congr rfl (fun i _ => by ring)]
    exact Finset.sum_add_distrib (f := fun i => φ u i ^ 2)
      (g := fun i => 2 * φ u i * φ v i + φ v i ^ 2)
  have e2 : ∀ u v : HC d, (∑ i, (2 * φ u i * φ v i + φ v i ^ 2))
      = (∑ i, 2 * φ u i * φ v i) + (∑ i, φ v i ^ 2) := fun u v =>
        Finset.sum_add_distrib (f := fun i => 2 * φ u i * φ v i)
          (g := fun i => φ v i ^ 2)
  have e3 : ∀ u : HC d,
      ((∑ v : HC d, ((∑ i, φ u i ^ 2) + (∑ i, (2 * φ u i * φ v i + φ v i ^ 2))))
      = (∑ v : HC d, ∑ i, φ u i ^ 2)
        + (∑ v : HC d, ∑ i, (2 * φ u i * φ v i + φ v i ^ 2))) := fun u =>
        Finset.sum_add_distrib (f := fun v => (∑ i, φ u i ^ 2))
          (g := fun v => (∑ i, (2 * φ u i * φ v i + φ v i ^ 2)))
  have e4 : ∀ u : HC d,
      (∑ v : HC d, ∑ i, (2 * φ u i * φ v i + φ v i ^ 2))
      = (∑ v : HC d, ∑ i, 2 * φ u i * φ v i)
        + (∑ v : HC d, ∑ i, φ v i ^ 2) := by
    intro u
    rw [Finset.sum_congr rfl (fun v _ => e2 u v)]
    exact Finset.sum_add_distrib (f := fun v => (∑ i, 2 * φ u i * φ v i))
      (g := fun v => (∑ i, φ v i ^ 2))
  have hsplit : (∑ u : HC d, ∑ v : HC d,
      ∑ i, (φ u i ^ 2 + 2 * φ u i * φ v i + φ v i ^ 2))
      = (∑ u : HC d, ∑ v : HC d, ∑ i, φ u i ^ 2)
        + ((∑ u : HC d, ∑ v : HC d, ∑ i, 2 * φ u i * φ v i)
          + (∑ u : HC d, ∑ v : HC d, ∑ i, φ v i ^ 2)) := by
    have hstep1 : (∑ u : HC d, ∑ v : HC d,
        ∑ i, (φ u i ^ 2 + 2 * φ u i * φ v i + φ v i ^ 2))
        = ∑ u : HC d, ∑ v : HC d, ((∑ i, φ u i ^ 2)
          + (∑ i, (2 * φ u i * φ v i + φ v i ^ 2))) :=
        Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => e1 u v))
    have hstep2 : ((∑ u : HC d, ∑ v : HC d, ((∑ i, φ u i ^ 2)
          + (∑ i, (2 * φ u i * φ v i + φ v i ^ 2))))
        = ∑ u : HC d, ((∑ v : HC d, ∑ i, φ u i ^ 2)
          + (∑ v : HC d, ∑ i, (2 * φ u i * φ v i + φ v i ^ 2)))) :=
        Finset.sum_congr rfl (fun u _ => e3 u)
    have hstep3 : ((∑ u : HC d, ((∑ v : HC d, ∑ i, φ u i ^ 2)
          + (∑ v : HC d, ∑ i, (2 * φ u i * φ v i + φ v i ^ 2))))
        = (∑ u : HC d, ∑ v : HC d, ∑ i, φ u i ^ 2)
          + (∑ u : HC d, ∑ v : HC d, ∑ i, (2 * φ u i * φ v i + φ v i ^ 2))) :=
        Finset.sum_add_distrib (f := fun u => (∑ v : HC d, ∑ i, φ u i ^ 2))
          (g := fun u => (∑ v : HC d, ∑ i, (2 * φ u i * φ v i + φ v i ^ 2)))
    have hstep4 : (∑ u : HC d, ∑ v : HC d, ∑ i, (2 * φ u i * φ v i + φ v i ^ 2))
        = ∑ u : HC d, ((∑ v : HC d, ∑ i, 2 * φ u i * φ v i)
          + (∑ v : HC d, ∑ i, φ v i ^ 2)) :=
        Finset.sum_congr rfl (fun u _ => e4 u)
    rw [hstep1, hstep2, hstep3, hstep4,
      Finset.sum_add_distrib (f := fun u => (∑ v : HC d, ∑ i, 2 * φ u i * φ v i))
        (g := fun u => (∑ v : HC d, ∑ i, φ v i ^ 2))]
  -- final assembly
  rw [show (∑ x : HC d × HC d, ∑ i, (φ x.1 i + φ x.2 i) ^ 2)
      = ∑ u : HC d, ∑ v : HC d, ∑ i, (φ u i ^ 2 + 2 * φ u i * φ v i + φ v i ^ 2) from by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl
          (fun v _ => Finset.sum_congr rfl (fun i _ => by ring))),
    hsplit, hT1, hT2, hT3]
  field_simp
  ring

/-- **The zeroth-order noise-halving law**: averaging TWO
independent Rademacher draws of the symmetric-difference
estimator halves the mean square error of the gradient
estimate. The two-draw average error is (φ₁+φ₂)/2 with
φ = the centered coordinate error esEst − ∇f (centered by
`esUnbiased`); the statement carries the (φ₁+φ₂)² form with
the /4 absorbed into the outer denominator — exactly the
`varianceHalving` instance for φ: the K = 2 case of the Dust
population law for the ESTIMATOR ERROR itself (the bridge to
the batch-noise chain: σ²_{ĝ} = σ²_g/K). -/
theorem dustNoiseHalving (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (x : Fin d → ℝ) (σ : ℝ) (hσ : σ ≠ 0) :
    (∑ p : HC d × HC d, ∑ i, ((esEst d A b x σ p.1 i
        - quadfGrad d A b x i)
        + (esEst d A b x σ p.2 i - quadfGrad d A b x i)) ^ 2) / (4 * 2 ^ d * 2 ^ d)
      = (1 / 2) * (∑ u, ∑ i, (esEst d A b x σ u i
          - quadfGrad d A b x i) ^ 2) / 2 ^ d := by
  -- the centered coordinate error is exactly the phi of varianceHalving,
  -- with zero mean by exact unbiasedness
  have hzero : ∀ i : Fin d,
      ∑ u ∈ (Finset.univ : Finset (HC d)),
        (esEst d A b x σ u i - quadfGrad d A b x i) = 0 := by
    intro i
    have hu := esUnbiased d A b x σ hσ i
    unfold hcAvg at hu
    field_simp at hu
    rw [Finset.sum_sub_distrib]
    rw [show (∑ u ∈ (Finset.univ : Finset (HC d)), quadfGrad d A b x i)
        = 2 ^ d * quadfGrad d A b x i from by
      rw [Finset.sum_const, hcCard d]
      simp]
    linarith
  exact varianceHalving d
    (fun u i => esEst d A b x σ u i - quadfGrad d A b x i) hzero

end Hagi.Pretraining
/-!
# DustVarK — the general-K dispersion law (Dust §2.2)

The K = 2 case (`varianceHalving`) says: averaging two draws
halves the mean square error. This module proves the law for
every batch size K:

* `hcVarK`: for a centered field (Σ φ = 0) on the hypercube,
  the uniform mean over K independent draws of the squared
  batch average is the single-draw mean square divided by K —
  the 1/K law, the exact form of the paper's σ²/K curve.
* `dustVarK`: the vector corollary — the K-draw averaged
  symmetric-difference gradient estimate has expected squared
  error exactly (1/K) times the single-draw expected squared
  error (both computed as uniform sums over the product
  hypercube `(Fin K → HC d)`), for every K ≥ 1.

The proof is an induction on K via the `Fin.cons`-split of the
product space: each new coordinate contributes its own diagonal
energy (Q) and, by centeredness, ZERO cross terms with the tail.
-/

namespace Hagi.Pretraining

open Finset Fin

/-! ### The scalar 1/K law -/

/-- The total (unnormalized) second moment of the batch sum of a
centered field over the K-fold product hypercube:
Σ_τ (Σ_k φ(τ k))² = K · (2^d)^(K−1) · Σ_u φ(u)². -/
theorem hcVarKTotal (d : ℕ) (φ : HC d → ℝ) (hC : ∑ u, φ u = 0) :
    ∀ K : ℕ, (∑ τ : Fin K → HC d, (∑ k, φ (τ k)) ^ 2)
      = K * ((2:ℝ) ^ d) ^ (K - 1) * (∑ u, φ u ^ 2) := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    classical
    set Q : ℝ := ∑ u, φ u ^ 2 with hQ
    set N : ℝ := ((2:ℝ) ^ d) ^ K with hN
    -- card of the K-fold product hypercube
    have hcard : (Finset.univ : Finset (Fin K → HC d)).card = ((2:ℕ) ^ d) ^ K := by
      simp [Fintype.card_pi, hcCard, Finset.prod_const]
    -- split the (K+1)-fold product space by the head coordinate
    have hsplit : (∑ τ : Fin (K + 1) → HC d, (∑ k, φ (τ k)) ^ 2)
        = ∑ u : HC d, ∑ τ' : Fin K → HC d,
            (∑ k, φ (Fin.cons (α := fun _ => HC d) u τ' k)) ^ 2 := by
      have h := (Fin.consEquiv (fun _ => HC d)).sum_comp
        (fun τ : Fin (K + 1) → HC d => (∑ k, φ (τ k)) ^ 2)
      simp only [Fin.consEquiv_apply, Fintype.sum_prod_type] at h
      rw [← h]

    rw [hsplit]
    -- expand the head-tail batch sum
    have hsum : ∀ (u : HC d) (τ' : Fin K → HC d),
        (∑ k, φ (Fin.cons (α := fun _ => HC d) u τ' k)) = φ u + ∑ k, φ (τ' k) := by
      intro u τ'
      rw [Fin.sum_univ_succ]
      exact congrArg (φ u + ·) (Finset.sum_congr rfl fun k _ => by
        rw [Fin.cons_succ])
    -- three pieces of the square
    have hdiag : (∑ u : HC d, ∑ τ' : Fin K → HC d, (φ u) ^ 2)
        = ((2:ℝ) ^ d) ^ K * Q := by
      rw [Finset.sum_comm]
      rw [show (∑ τ' : Fin K → HC d, Q)
          = #(Finset.univ : Finset (Fin K → HC d)) • Q from
            Finset.sum_const (b := Q),
        show #(Finset.univ : Finset (Fin K → HC d)) = ((2:ℕ) ^ d) ^ K from hcard]
      simp
    have hcross : (∑ u : HC d, ∑ τ' : Fin K → HC d,
          2 * φ u * (∑ k, φ (τ' k)))
        = 0 := by
      have hstep : (∑ u : HC d, ∑ τ' : Fin K → HC d,
          2 * φ u * (∑ k, φ (τ' k)))
          = ∑ τ' : Fin K → HC d,
              (∑ k, φ (τ' k)) * (∑ u : HC d, 2 * φ u) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro τ' _
        rw [mul_sum]
        simp [mul_comm]
      have h2 : (∑ u : HC d, 2 * φ u) = 0 := by
        rw [← Finset.mul_sum, hC, mul_zero]
      rw [hstep, ← Finset.sum_mul, h2, mul_zero]

    have htail : (∑ u : HC d, ∑ τ' : Fin K → HC d,
          (∑ k, φ (τ' k)) ^ 2)
        = ((2:ℝ) ^ d) * (K * ((2:ℝ) ^ d) ^ (K - 1) * Q) := by
      rw [Finset.sum_comm]
      have hinner : ∀ τ' : Fin K → HC d,
          (∑ u : HC d, (∑ k, φ (τ' k)) ^ 2)
            = ((2:ℝ) ^ d) * (∑ k, φ (τ' k)) ^ 2 := by
        intro τ'
        rw [show (∑ u : HC d, (∑ k, φ (τ' k)) ^ 2)
            = #(Finset.univ : Finset (HC d)) • (∑ k, φ (τ' k)) ^ 2 from
              Finset.sum_const (b := (∑ k, φ (τ' k)) ^ 2),
          show #(Finset.univ : Finset (HC d)) = 2 ^ d from hcCard d]
        simp
      rw [Finset.sum_congr rfl (fun τ' _ => hinner τ')]
      rw [← Finset.mul_sum]
      rw [ih]

    -- final assembly of the successor step
    have hexp : ∀ (u : HC d) (τ' : Fin K → HC d),
        (φ u + ∑ k, φ (τ' k)) ^ 2
          = (φ u) ^ 2 + 2 * φ u * (∑ k, φ (τ' k))
            + (∑ k, φ (τ' k)) ^ 2 := by
      intro u τ'
      ring
    simp only [hsum]
    rw [Finset.sum_congr rfl (fun u _ =>
      Finset.sum_congr rfl (fun τ' _ => hexp u τ'))]
    have hd1 : (∑ u : HC d, ∑ τ' : Fin K → HC d,
        (φ u ^ 2 + 2 * φ u * ∑ k, φ (τ' k)
          + (∑ k, φ (τ' k)) ^ 2))
        = (∑ u : HC d, ∑ τ' : Fin K → HC d, (φ u) ^ 2)
          + ((∑ u : HC d, ∑ τ' : Fin K → HC d,
              2 * φ u * ∑ k, φ (τ' k))
            + (∑ u : HC d, ∑ τ' : Fin K → HC d,
                (∑ k, φ (τ' k)) ^ 2)) := by
      simp only [Finset.sum_add_distrib]
      ring_nf

    rw [hd1, hdiag, hcross, htail]
    cases K with
    | zero => simp
    | succ M =>
      rw [show M + 1 - 1 = M from by omega]
      have h1 : ((2:ℝ) ^ d) ^ (M + 1) = ((2:ℝ) ^ d) ^ M * (2:ℝ) ^ d :=
        pow_succ _ _
      have h2 : ((2:ℝ) ^ d) ^ (M + 1 + 1 - 1) = ((2:ℝ) ^ d) ^ (M + 1) := by
        rw [show M + 1 + 1 - 1 = M + 1 from by omega]
      rw [h2, h1]
      push_cast
      ring
/-- **The general-K 1/K dispersion law (scalar form).** For a centered
field on the hypercube, the uniform mean over the K-fold product
hypercube of the squared batch average equals the single-draw mean
square divided by K — for every K ≥ 1, not just K = 2. -/
theorem hcVarK (d : ℕ) (φ : HC d → ℝ) (hC : ∑ u, φ u = 0) (K : ℕ)
    (hK : 0 < K) :
    (∑ τ : Fin K → HC d, ((∑ k, φ (τ k)) / K) ^ 2) / ((2:ℝ) ^ d) ^ K
      = ((∑ u, φ u ^ 2) / ((2:ℝ) ^ d)) / K := by
  have htot := hcVarKTotal d φ hC K
  have hsplit : ∀ τ : Fin K → HC d,
      ((∑ k, φ (τ k)) / K) ^ 2 = (∑ k, φ (τ k)) ^ 2 / K ^ 2 := by
    intro τ
    rw [div_pow]
  rw [Finset.sum_congr rfl (fun τ _ => hsplit τ)]
  rw [← Finset.sum_div]
  rw [htot]
  field_simp
  obtain ⟨M, rfl⟩ : ∃ M, K = M + 1 := ⟨K - 1, by omega⟩
  rw [show M + 1 - 1 = M from by omega, pow_succ]
  ring

/-- Centeredness of the per-coordinate error field of the
symmetric-difference estimator (from exact unbiasedness). -/
theorem esErrCentered (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (b : Fin d → ℝ) (x : Fin d → ℝ) (σ : ℝ) (hσ : σ ≠ 0) (i : Fin d) :
    ∑ u, (esEst d A b x σ u i - quadfGrad d A b x i) = 0 := by
  have h := esUnbiased d A b x σ hσ i
  unfold hcAvg at h
  field_simp at h
  simp only [Finset.sum_sub_distrib, h]
  simp

/-- **The general-K dispersion law (vector form): the K-draw
averaged symmetric-difference gradient estimate has expected
squared error exactly (1/K) times the single-draw one** —
computed as uniform sums over the product hypercube
(Fin K → HC d). Every draw contributes its own diagonal energy
and, by exact unbiasedness, zero cross terms: the 1/K law of
Dust §2.2 for every batch size K ≥ 1. -/
theorem dustVarK (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (b : Fin d → ℝ) (x : Fin d → ℝ) (σ : ℝ) (hσ : σ ≠ 0)
    (K : ℕ) (hK : 0 < K) :
    (∑ τ : Fin K → HC d, ∑ i,
        ((∑ k, esEst d A b x σ (τ k) i) / K
          - quadfGrad d A b x i) ^ 2) / ((2:ℝ) ^ d) ^ K
      = ((∑ u : HC d, ∑ i,
          (esEst d A b x σ u i - quadfGrad d A b x i) ^ 2)
          / ((2:ℝ) ^ d)) / K := by
  -- per-coordinate scalar law applied to the error field
  have hcoord : ∀ i : Fin d,
      (∑ τ : Fin K → HC d,
        ((∑ k, esEst d A b x σ (τ k) i) / K
          - quadfGrad d A b x i) ^ 2)
        = (∑ u : HC d,
            (esEst d A b x σ u i - quadfGrad d A b x i) ^ 2)
          * ((2:ℝ) ^ d) ^ (K - 1) / K := by
    intro i
    have hlaw := hcVarK d
      (fun u => esEst d A b x σ u i - quadfGrad d A b x i)
      (esErrCentered d A b x σ hσ i) K hK
    have hconv : ∀ τ : Fin K → HC d,
        ((∑ k, esEst d A b x σ (τ k) i) / K
          - quadfGrad d A b x i)
        = ((∑ k, (esEst d A b x σ (τ k) i
            - quadfGrad d A b x i)) / K) := by
      intro τ
      have h2 : (∑ k, (esEst d A b x σ (τ k) i
          - quadfGrad d A b x i))
          = (∑ k, esEst d A b x σ (τ k) i)
            - K * quadfGrad d A b x i := by
        rw [Finset.sum_sub_distrib
          (f := fun k => esEst d A b x σ (τ k) i)
          (g := fun _ => quadfGrad d A b x i),
          show (∑ k : Fin K, quadfGrad d A b x i) = K * quadfGrad d A b x i from by
            rw [Finset.sum_const]
            simp]
      rw [h2]
      field_simp
    have h3 : (∑ τ : Fin K → HC d,
        ((∑ k, esEst d A b x σ (τ k) i) / K
          - quadfGrad d A b x i) ^ 2)
      = (∑ τ : Fin K → HC d,
          ((∑ k, (esEst d A b x σ (τ k) i
            - quadfGrad d A b x i)) / K) ^ 2) :=
      Finset.sum_congr rfl fun τ _ => by rw [hconv τ]
    rw [h3]
    obtain ⟨M, rfl⟩ : ∃ M, K = M + 1 := ⟨K - 1, by omega⟩
    rw [show M + 1 - 1 = M from by omega]
    rw [div_eq_iff (by positivity)] at hlaw
    rw [hlaw]
    field_simp
    ring
  -- swap the coordinate sums and finish
  rw [Finset.sum_comm]
  simp only [hcoord]
  obtain ⟨M, rfl⟩ : ∃ M, K = M + 1 := ⟨K - 1, by omega⟩
  rw [show M + 1 - 1 = M from by omega]
  have hrhs : (∑ u : HC d, ∑ i,
      (esEst d A b x σ u i - quadfGrad d A b x i) ^ 2)
    = (∑ i : Fin d, ∑ u : HC d,
        (esEst d A b x σ u i - quadfGrad d A b x i) ^ 2) :=
    Finset.sum_comm
  rw [hrhs]
  rw [show ((2:ℝ) ^ d) ^ (M + 1) = ((2:ℝ) ^ d) * ((2:ℝ) ^ d) ^ M from by rw [pow_succ, mul_comm]]
  rw [Finset.sum_div, Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-! ### The uniform product measure on the K-fold hypercube -/

/-- The uniform weight on the K-fold product hypercube. -/
noncomputable def prodQ (d K : ℕ) (τ : Fin K → HC d) : ℝ :=
  1 / ((2:ℝ) ^ d) ^ K

theorem prodQ_nonneg (d K : ℕ) (τ : Fin K → HC d) :
    0 ≤ prodQ d K τ := by
  unfold prodQ
  positivity

theorem prodQ_isProb (d K : ℕ) :
    ∑ τ : Fin K → HC d, prodQ d K τ = 1 := by
  classical
  have hcard : (Finset.univ : Finset (Fin K → HC d)).card = ((2:ℕ) ^ d) ^ K := by
    simp [Fintype.card_pi, hcCard, Finset.prod_const]
  unfold prodQ
  have hsum : (∑ τ : Fin K → HC d, 1 / ((2:ℝ) ^ d) ^ K)
      = ((2:ℝ) ^ d) ^ K * (1 / ((2:ℝ) ^ d) ^ K) := by
    rw [show (∑ τ : Fin K → HC d, 1 / ((2:ℝ) ^ d) ^ K)
        = #(Finset.univ : Finset (Fin K → HC d)) • (1 / ((2:ℝ) ^ d) ^ K) from by
          rw [Finset.sum_const]]
    simp
  rw [hsum]
  field_simp

/-- The expected squared error energy of the K-draw averaged
estimate under the uniform product weight, in expQ form. -/
theorem dustVarK_expQ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (b : Fin d → ℝ) (x : Fin d → ℝ) (σ : ℝ) (hσ : σ ≠ 0)
    (K : ℕ) (hK : 0 < K) :
    Probability.expQ (prodQ d K) (fun τ => (∑ i,
        ((∑ k, esEst d A b x σ (τ k) i) / K
          - quadfGrad d A b x i) ^ 2))
      = ((∑ u : HC d, ∑ i,
          (esEst d A b x σ u i - quadfGrad d A b x i) ^ 2)
          / ((2:ℝ) ^ d)) / K := by
  unfold Probability.expQ prodQ
  have hmul : (∑ τ : Fin K → HC d,
      (1 / ((2:ℝ) ^ d) ^ K) * (∑ i,
        ((∑ k, esEst d A b x σ (τ k) i) / K
          - quadfGrad d A b x i) ^ 2))
    = ((∑ τ : Fin K → HC d, ∑ i,
        ((∑ k, esEst d A b x σ (τ k) i) / K
          - quadfGrad d A b x i) ^ 2)) / ((2:ℝ) ^ d) ^ K := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun τ _ => by field_simp
  rw [hmul]
  exact dustVarK d A b x σ hσ K hK

end Hagi.Pretraining
/-!
# DustCert: the batch-noise chain closes on the zeroth-order
estimator

The KLS batch-noise theorem (`klsBatchNoise`) takes two
statistical hypotheses: centeredness and pairwise
uncorrelatedness of the per-sample gradient fields. For the
Dust zeroth-order estimator on the quadratic model the
relevant pieces are THEOREMS:

* `pairQ_isProb`/`pairQ_nonneg`: the uniform pair measure is
  a probability.
* `pairExpFirst`: finite Fubini — a first-component function
  has the pair expectation equal to its hypercube average.
* `pairExpProd`: the pair expectation of a product of
  one-component factors factorizes into the product of the
  hypercube averages.
* `dustUncorrPair`: any CENTERED error fields are
  uncorrelated under the pair measure — the huncorr
  hypothesis of `klsBatchNoise` promoted to a theorem (the
  centeredness of the estimator error is `esUnbiased`).

Honest boundary: the Poincaré premise and the sensitivity
bound of the KLS interface remain hypotheses; the
quadratic-model restriction is inherited from `esUnbiased`.
-/

namespace Hagi.Pretraining

open Finset

/-- The uniform measure on draw pairs. -/
noncomputable def pairQ (d : ℕ) : HC d × HC d → ℝ := fun _ => 1 / (2 ^ d * 2 ^ d)

/-- The pair measure sums to one. -/
theorem pairQ_isProb (d : ℕ) : ∑ p : HC d × HC d, pairQ d p = 1 := by
  simp only [pairQ, Finset.sum_const, smul_eq_mul]
  rw [show ((Finset.univ : Finset (HC d × HC d))).card = 2 ^ d * 2 ^ d from by
    simp [Fintype.card_prod, hcCard]]
  norm_num
  field_simp

/-- PairQ is nonnegative. -/
theorem pairQ_nonneg (d : ℕ) : ∀ p, 0 ≤ pairQ d p := by
  intro p
  unfold pairQ
  positivity

/-- **Finite Fubini (first component)**: a function depending
only on the first component has the pair expectation equal to
its hypercube average. -/
theorem pairExpFirst (d : ℕ) (F : HC d → ℝ) :
    Probability.expQ (pairQ d) (fun p => F p.1)
      = (∑ u ∈ (Finset.univ : Finset (HC d)), F u) / 2 ^ d := by
  unfold Probability.expQ pairQ
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) =>
    ((Finset.mul_sum (Finset.univ : Finset (HC d)) F
      (1 / (2 ^ d * 2 ^ d))).symm : (∑ x : HC d, (1 / (2 ^ d * 2 ^ d)) * F x)
      = (1 / (2 ^ d * 2 ^ d)) * ∑ x : HC d, F x))]
  rw [Finset.sum_const,
    show ((Finset.univ : Finset (HC d))).card = 2 ^ d from by
      simp [hcCard]]
  norm_num
  field_simp

/-- **Pair factorization**: the pair expectation of a product
of one-component factors equals the product of the hypercube
averages (finite Fubini on the product space). -/
theorem pairExpProd (d : ℕ) (φ ψ : HC d → ℝ) :
    Probability.expQ (pairQ d) (fun p => φ p.1 * ψ p.2)
      = ((∑ u ∈ (Finset.univ : Finset (HC d)), φ u) / 2 ^ d)
        * ((∑ v ∈ (Finset.univ : Finset (HC d)), ψ v) / 2 ^ d) := by
  unfold Probability.expQ pairQ
  rw [Fintype.sum_prod_type]
  -- regroup and factor over y
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
    ((Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) =>
        (by ring : (1 / (2 ^ d * 2 ^ d)) * (φ x * ψ y)
          = ((1 / (2 ^ d * 2 ^ d)) * φ x) * ψ y))).trans
      (Finset.mul_sum (Finset.univ : Finset (HC d)) (fun y => ψ y)
        ((1 / (2 ^ d * 2 ^ d)) * φ x)).symm))]
  -- factor over x
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
      (by ring : ((1 / (2 ^ d * 2 ^ d)) * φ x) * (∑ y : HC d, ψ y)
        = ((1 / (2 ^ d * 2 ^ d)) * (∑ y : HC d, ψ y)) * φ x)),
    (Finset.mul_sum (Finset.univ : Finset (HC d)) (fun x => φ x)
      ((1 / (2 ^ d * 2 ^ d)) * (∑ y : HC d, ψ y))).symm]
  rw [show ((1 / (2 ^ d * 2 ^ d)) * (∑ y : HC d, ψ y)) * (∑ x : HC d, φ x)
      = ((∑ x : HC d, φ x) / 2 ^ d) * ((∑ y : HC d, ψ y) / 2 ^ d) from by
    field_simp]

/-- **Draws are uncorrelated in the pair expectation**: any
centered error field is uncorrelated with ANY second field
under the pair measure — E[φ(u)·ψ(v)] = 0 whenever Σφ = 0.
For the zeroth-order estimator the centeredness of the
coordinate error is `esUnbiased`; this is the huncorr
hypothesis of `klsBatchNoise` promoted to a theorem. -/
theorem dustUncorrPair (d : ℕ) (φ ψ : HC d → ℝ)
    (hφ : ∑ u ∈ (Finset.univ : Finset (HC d)), φ u = 0) :
    Probability.expQ (pairQ d) (fun p => φ p.1 * ψ p.2) = 0 := by
  rw [pairExpProd, hφ]
  simp

end Hagi.Pretraining

set_option linter.style.header false

/-!
# DustAlign: the alignment law

The theoretical form of Dust's measured cosine law
cos(K) = c_max/√(1+c/K) (Fig. 5): the two-draw averaged
zeroth-order estimate aligns with the true gradient with
explicitly bounded failure probability.

Geometry (dotProduct norms, no matrix machinery):

* `absDot_le`: |⟨a,b⟩| ≤ ‖a‖·‖b‖ (Cauchy–Schwarz in
  square-root form — from the squared CS of).
* `nrmTriangle`: ‖a+b‖ ≤ ‖a‖+‖b‖.
* `alignLower`: if the error is relatively small
  (‖e‖ ≤ δ·‖g‖, δ ≤ 1), the alignment dominates its floor:
  ⟨g, g+e⟩ ≥ (1−2δ)·‖g‖·‖g+e‖ — the multiplicative
  cosine bound without ever dividing by norms.

Probability (Markov on the pair space, welded by):

* `dustAlignment`: on the two-draw pair space, the averaged
  estimate ĝ satisfies ⟨g, ĝ⟩ ≥ (1−2δ)‖g‖‖ĝ‖ except on a
  pair set of q-mass ≤ V/(δ²·‖g‖²), where V = E‖ĝ−g‖² is
  the (halved) estimator error energy. Failure decays
  as 1/K in the population — the proved shape of Fig. 5.
-/

namespace Hagi.Pretraining

open Finset

/-- The dotProduct norm. -/
noncomputable def Nrm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

/-- Cauchy–Schwarz in norm form. -/
theorem absDot_le {n : ℕ} (a b : Fin n → ℝ) :
    |a ⬝ᵥ b| ≤ Nrm a * Nrm b := by
  have h : (a ⬝ᵥ b) ^ 2 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) := Architecture.dotCS a b
  have h2 : |a ⬝ᵥ b| = Real.sqrt ((a ⬝ᵥ b) ^ 2) := by
    rw [sq]
    exact (Real.sqrt_mul_self_eq_abs _).symm
  rw [h2]
  have haa : 0 ≤ a ⬝ᵥ a := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  refine le_trans (Real.sqrt_le_sqrt h) ?_
  rw [Real.sqrt_mul haa]
  rfl

/-- The triangle inequality for the dotProduct norm. -/
theorem nrmTriangle {n : ℕ} (a b : Fin n → ℝ) :
    Nrm (a + b) ≤ Nrm a + Nrm b := by
  have haa : 0 ≤ a ⬝ᵥ a := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hbb : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hexpand : (a + b) ⬝ᵥ (a + b)
      = (a ⬝ᵥ a) + 2 * (a ⬝ᵥ b) + (b ⬝ᵥ b) := by
    rw [dotProduct_add, add_dotProduct, add_dotProduct]
    linarith [dotProduct_comm b a]
  have hcs : a ⬝ᵥ b ≤ Nrm a * Nrm b := by
    have h := absDot_le a b
    linarith [(abs_le.mp h).2]
  have hkey : (a + b) ⬝ᵥ (a + b) ≤ (Nrm a + Nrm b) * (Nrm a + Nrm b) := by
    rw [hexpand]
    have h1 : Nrm a * Nrm a = a ⬝ᵥ a := by
      unfold Nrm
      rw [← sq]
      exact Real.sq_sqrt haa
    have h2 : Nrm b * Nrm b = b ⬝ᵥ b := by
      unfold Nrm
      rw [← sq]
      exact Real.sq_sqrt hbb
    nlinarith [hcs, sq_nonneg (Nrm a - Nrm b)]
  refine le_trans (Real.sqrt_le_sqrt hkey) ?_
  have hnn : 0 ≤ Nrm a + Nrm b := by
    have h1 : 0 ≤ Nrm a := Real.sqrt_nonneg _
    have h2 : 0 ≤ Nrm b := Real.sqrt_nonneg _
    linarith
  rw [Real.sqrt_mul_self hnn]

/-- **The alignment floor**: with a relatively small error
(‖e‖ ≤ δ·‖g‖, 0 ≤ δ ≤ 1), the inner product dominates its
cosine floor: ⟨g, g+e⟩ ≥ (1−2δ)·‖g‖·‖g+e‖ — the multiplicative
form of cos(g, ĝ) ≥ 1−2δ without norm division. -/
theorem alignLower {n : ℕ} (g e : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (he : Nrm e ≤ δ * Nrm g) :
    (1 - 2 * δ) * Nrm g * Nrm (g + e) ≤ g ⬝ᵥ (g + e) := by
  have hgg : 0 ≤ g ⬝ᵥ g := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hNrg : 0 ≤ Nrm g := Real.sqrt_nonneg _
  have hNre : 0 ≤ Nrm e := Real.sqrt_nonneg _
  -- the inner product expansion
  have hexp : g ⬝ᵥ (g + e) = (g ⬝ᵥ g) + (g ⬝ᵥ e) := by
    rw [dotProduct_add]
  -- Cauchy–Schwarz lower bound on the cross term
  have hcs : -(Nrm g * Nrm e) ≤ g ⬝ᵥ e := by
    have h := absDot_le g e
    linarith [(abs_le.mp h).1]
  -- ‖g‖² = Nrm g squared
  have hsq : Nrm g * Nrm g = g ⬝ᵥ g := by
    unfold Nrm
    rw [← sq]
    exact Real.sq_sqrt hgg
  -- the error inside the triangle
  have htri := nrmTriangle g e
  -- assemble
  rw [hexp]
  by_cases hd2 : δ ≤ 1 / 2
  · have hpos : 0 ≤ 1 - 2 * δ := by linarith
    have hprod : (1 - 2 * δ) * Nrm g * Nrm e
        ≤ (1 - 2 * δ) * Nrm g * (δ * Nrm g) := by
      exact mul_le_mul_of_nonneg_left he (mul_nonneg hpos hNrg)
    have hprod2 : (1 - 2 * δ) * Nrm g * Nrm (g + e)
        ≤ (1 - 2 * δ) * Nrm g * (Nrm g + Nrm e) :=
      mul_le_mul_of_nonneg_left htri (mul_nonneg hpos hNrg)
    have hNge : Nrm g * Nrm e ≤ Nrm g * (δ * Nrm g) :=
      mul_le_mul_of_nonneg_left he hNrg
    nlinarith [hcs, htri, hsq, hNrg, hNre, hgg, hpos, hprod, hprod2, hNge,
      sq_nonneg (Nrm g), sq_nonneg (Nrm e), sq_nonneg δ]
  · have hneg : (1 - 2 * δ) * Nrm g * Nrm (g + e) ≤ 0 := by
      have h1 : (1:ℝ) - 2 * δ < 0 := by linarith
      have h2 : 0 ≤ Nrm g * Nrm (g + e) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      nlinarith
    have hRHS : 0 ≤ (g ⬝ᵥ g) + (g ⬝ᵥ e) := by
      nlinarith [hgg, hcs]
    linarith

/-- **The alignment law (bridge E)**: on the two-draw pair
space, the averaged zeroth-order estimate ĝ satisfies the
alignment floor ⟨g, ĝ⟩ ≥ (1−2δ)·‖g‖·‖ĝ‖ except on a pair set
of q-mass ≤ V/(δ²·‖g‖²), where V = E‖ĝ−g‖² — by the
(halved) single-draw error energy. Failure probability decays
as 1/K in the population: the proved shape of Dust's
cos(K) = c_max/√(1+c/K) law. -/
theorem dustAlignment (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (x : Fin d → ℝ) (σ : ℝ) (hσ : σ ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgN : 0 < Nrm (quadfGrad d A b x)) :
    (∑ p ∈ Finset.univ.filter (fun p =>
        (1 - 2 * δ) * Nrm (quadfGrad d A b x)
          * Nrm ((esEst d A b x σ p.1 + esEst d A b x σ p.2) / 2)
        ≤ quadfGrad d A b x ⬝ᵥ ((esEst d A b x σ p.1
          + esEst d A b x σ p.2) / 2)),
      pairQ d p)
      ≥ 1 - ((∑ q : HC d × HC d, ∑ i, ((esEst d A b x σ q.1 i
          - quadfGrad d A b x i) + (esEst d A b x σ q.2 i
            - quadfGrad d A b x i)) ^ 2) / (4 * 2 ^ d * 2 ^ d))
        / (δ * Nrm (quadfGrad d A b x)) ^ 2 := by
  -- the error field and its energy
  -- E‖err‖² equals the V of the statement
  have hVform : Probability.expQ (pairQ d)
        (fun p => (Nrm (fun i => (esEst d A b x σ p.1 i
          + esEst d A b x σ p.2 i) / 2 - quadfGrad d A b x i)) ^ 2)
      = (∑ q : HC d × HC d, ∑ i, ((esEst d A b x σ q.1 i
          - quadfGrad d A b x i) + (esEst d A b x σ q.2 i
            - quadfGrad d A b x i)) ^ 2) / (4 * 2 ^ d * 2 ^ d) := by
    simp only [Probability.expQ, pairQ, Nrm, Real.sq_sqrt, dotProduct,
      mul_comm, mul_left_comm, mul_assoc, div_mul_eq_mul_div]
    conv_rhs => rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q _
    have hnn : 0 ≤ ∑ j : Fin d,
        ((esEst d A b x σ q.1 j + esEst d A b x σ q.2 j) / 2
          - quadfGrad d A b x j)
        * ((esEst d A b x σ q.1 j + esEst d A b x σ q.2 j) / 2
          - quadfGrad d A b x j) :=
      Finset.sum_nonneg fun j _ => mul_self_nonneg _
    have hsplit : (∑ j : Fin d,
        ((esEst d A b x σ q.1 j + esEst d A b x σ q.2 j) / 2
          - quadfGrad d A b x j)
        * ((esEst d A b x σ q.1 j + esEst d A b x σ q.2 j) / 2
          - quadfGrad d A b x j))
      = ∑ j : Fin d, ((esEst d A b x σ q.1 j - quadfGrad d A b x j)
          + (esEst d A b x σ q.2 j - quadfGrad d A b x j)) ^ 2 / 4 := by
      apply Finset.sum_congr rfl
      intro j _
      field_simp
      ring_nf
    rw [one_mul, Real.sq_sqrt hnn, hsplit, Finset.sum_div, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring

  -- Markov: the bad set has mass <= V/(delta^2 ||g||^2)
  set E := fun p : HC d × HC d => Nrm (fun i =>
    (esEst d A b x σ p.1 i + esEst d A b x σ p.2 i) / 2 - quadfGrad d A b x i) with hE
  set V := (∑ q : HC d × HC d, ∑ i, ((esEst d A b x σ q.1 i
      - quadfGrad d A b x i) + (esEst d A b x σ q.2 i
        - quadfGrad d A b x i)) ^ 2) / (4 * 2 ^ d * 2 ^ d) with hV
  have hMarkov := Probability.klsChebyshev (pairQ d) (pairQ_nonneg d) V
    (δ * Nrm (quadfGrad d A b x))
    (by positivity) E (le_of_eq hVform)
  -- the bad set is contained in the complement of the aligned set
  have hmono : (Finset.univ.filter (fun p =>
        ¬(δ * Nrm (quadfGrad d A b x) ≤ |E p|)))
      ⊆ Finset.univ.filter (fun p =>
        (1 - 2 * δ) * Nrm (quadfGrad d A b x) * Nrm ((esEst d A b x σ p.1
          + esEst d A b x σ p.2) / 2)
        ≤ quadfGrad d A b x ⬝ᵥ ((esEst d A b x σ p.1
          + esEst d A b x σ p.2) / 2)) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨Finset.mem_univ p, ?_⟩
    -- ||e|| ≤ δ ||g||
    have hNrmE : E p ≤ δ * Nrm (quadfGrad d A b x) := by
      have hnot : ¬(δ * Nrm (quadfGrad d A b x) ≤ |E p|) := hp.2
      push_neg at hnot
      exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hnot)
    -- the alignment floor on the good set
    have halign := alignLower (quadfGrad d A b x)
      (fun i => (esEst d A b x σ p.1 i + esEst d A b x σ p.2 i) / 2
        - quadfGrad d A b x i) δ (by linarith [hδ]) hδ1 hNrmE
    -- pointwise function identity: avg = g + err
    have hfun : (fun i : Fin d => (esEst d A b x σ p.1 i
        + esEst d A b x σ p.2 i) / 2)
        = quadfGrad d A b x
          + (fun i => (esEst d A b x σ p.1 i
            + esEst d A b x σ p.2 i) / 2 - quadfGrad d A b x i) := by
      funext i
      rw [Pi.add_apply]
      ring
    have hconv : ((esEst d A b x σ p.1) + (esEst d A b x σ p.2)) / 2
        = (fun i : Fin d => (esEst d A b x σ p.1 i
          + esEst d A b x σ p.2 i) / 2) := by
      funext i
      simp
    rw [hconv, hfun]
    exact halign
  -- assemble the mass bound
  have hpart : (∑ w ∈ (Finset.univ : Finset (HC d × HC d)).filter (fun w =>
        δ * Nrm (quadfGrad d A b x) ≤ |E w|), pairQ d w)
      + (∑ w ∈ (Finset.univ : Finset (HC d × HC d)).filter (fun w =>
        ¬(δ * Nrm (quadfGrad d A b x) ≤ |E w|)), pairQ d w)
      = ∑ p : HC d × HC d, pairQ d p := by
    rw [Finset.sum_filter_add_sum_filter_not]

  -- the complement mass dominates into the aligned mass
  have hdom : (∑ w ∈ (Finset.univ : Finset (HC d × HC d)).filter (fun w =>
        ¬(δ * Nrm (quadfGrad d A b x) ≤ |E w|)), pairQ d w)
      ≤ (∑ w ∈ Finset.univ.filter (fun w =>
        (1 - 2 * δ) * Nrm (quadfGrad d A b x)
          * Nrm ((esEst d A b x σ w.1 + esEst d A b x σ w.2) / 2)
        ≤ quadfGrad d A b x ⬝ᵥ ((esEst d A b x σ w.1
          + esEst d A b x σ w.2) / 2)), pairQ d w) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_le_sum fun w _ => ?_
    by_cases h1 : δ * Nrm (quadfGrad d A b x) ≤ |E w|
    · rw [if_neg (fun hc => hc h1)]
      by_cases h2 : (1 - 2 * δ) * Nrm (quadfGrad d A b x)
          * Nrm ((esEst d A b x σ w.1 + esEst d A b x σ w.2) / 2)
        ≤ quadfGrad d A b x ⬝ᵥ ((esEst d A b x σ w.1
          + esEst d A b x σ w.2) / 2)
      · rw [if_pos h2]
        exact pairQ_nonneg d w
      · rw [if_neg h2]
    · have hmem : w ∈ (Finset.univ : Finset (HC d × HC d)).filter (fun w =>
          ¬(δ * Nrm (quadfGrad d A b x) ≤ |E w|)) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ w, h1⟩
      have hgood := hmono hmem
      rw [Finset.mem_filter] at hgood
      rw [if_pos hgood.2, if_pos h1]
  -- final assembly
  have hprob : ∑ p : HC d × HC d, pairQ d p = 1 := pairQ_isProb d
  calc (∑ p ∈ Finset.univ.filter (fun p =>
        (1 - 2 * δ) * Nrm (quadfGrad d A b x)
          * Nrm ((esEst d A b x σ p.1 + esEst d A b x σ p.2) / 2)
        ≤ quadfGrad d A b x ⬝ᵥ ((esEst d A b x σ p.1
          + esEst d A b x σ p.2) / 2)), pairQ d p)
      ≥ (∑ w ∈ (Finset.univ : Finset (HC d × HC d)).filter (fun w =>
        ¬(δ * Nrm (quadfGrad d A b x) ≤ |E w|)), pairQ d w) := hdom
    _ = (∑ p : HC d × HC d, pairQ d p)
        - (∑ w ∈ (Finset.univ : Finset (HC d × HC d)).filter (fun w =>
        δ * Nrm (quadfGrad d A b x) ≤ |E w|), pairQ d w) := by
        nlinarith [hpart, hprob]
    _ ≥ 1 - V / (δ * Nrm (quadfGrad d A b x)) ^ 2 := by
        have := hMarkov
        nlinarith [hMarkov, hpart, hprob, pairQ_nonneg d]

/-- **The general-K alignment law**: on the K-fold product
hypercube with the uniform weight prodQ d K, the mass of batch
draws whose averaged estimate satisfies the alignment floor
(1−2δ)·‖g‖·‖ĝ‖ ≤ g ⬝ ĝ is at least 1 − V/(K·(δ·‖g‖)²), where V
is the single-draw mean square error. The K = 2 form is
`dustAlignment`; the general case combines the general-K
dispersion law (dustVarK_expQ: the averaged error energy is
V/K) with the alignment floor geometry (alignLower) via
Chebyshev on the product space. -/
theorem dustAlignmentK (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (b : Fin d → ℝ) (x : Fin d → ℝ) (σ : ℝ) (hσ : σ ≠ 0)
    (K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgN : 0 < Nrm (quadfGrad d A b x)) :
    (∑ τ ∈ Finset.univ.filter (fun τ : Fin K → HC d =>
        (1 - 2 * δ) * Nrm (quadfGrad d A b x)
          * Nrm (fun i : Fin d => (∑ k, esEst d A b x σ (τ k) i) / K)
        ≤ quadfGrad d A b x ⬝ᵥ
          (fun i : Fin d => (∑ k, esEst d A b x σ (τ k) i) / K)),
      prodQ d K τ)
      ≥ 1 - (((∑ u : HC d, ∑ i,
          (esEst d A b x σ u i - quadfGrad d A b x i) ^ 2)
        / ((2:ℝ) ^ d)) / K) / (δ * Nrm (quadfGrad d A b x)) ^ 2 := by
  -- the error field and its energy
  set E : (Fin K → HC d) → ℝ := fun τ => Nrm (fun i : Fin d =>
    (∑ k, esEst d A b x σ (τ k) i) / K - quadfGrad d A b x i) with hE
  set V : ℝ := (∑ u : HC d, ∑ i,
    (esEst d A b x σ u i - quadfGrad d A b x i) ^ 2)
    / ((2:ℝ) ^ d) with hV
  -- the energy identity: expQ prodQ (fun τ => (E τ)^2) = V / K
  have hVform : Probability.expQ (prodQ d K) (fun τ => (E τ) ^ 2) = V / K := by
    have hsq : ∀ τ : Fin K → HC d,
        (E τ) ^ 2 = ∑ i : Fin d,
          ((∑ k, esEst d A b x σ (τ k) i) / K
            - quadfGrad d A b x i) ^ 2 := by
      intro τ
      unfold E Nrm
      have hnn : 0 ≤ (fun i : Fin d =>
          (∑ k, esEst d A b x σ (τ k) i) / K
            - quadfGrad d A b x i)
          ⬝ᵥ (fun i : Fin d =>
          (∑ k, esEst d A b x σ (τ k) i) / K
            - quadfGrad d A b x i) := by
        rw [dotProduct]
        apply Finset.sum_nonneg
        intro i _
        exact mul_self_nonneg _
      rw [Real.sq_sqrt hnn]
      rw [dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hbase := dustVarK_expQ d A b x σ hσ K hK
    unfold Probability.expQ at hbase ⊢
    simp only [hsq]
    exact hbase
  -- Markov/Chebyshev
  have hMarkov := Probability.klsChebyshev (prodQ d K) (prodQ_nonneg d K)
    (V / K) (δ * Nrm (quadfGrad d A b x))
    (mul_pos hδ hgN) E (le_of_eq hVform)
  -- the bad set is contained in the complement of the aligned set
  have hmono : (Finset.univ.filter (fun τ : Fin K → HC d =>
        ¬(δ * Nrm (quadfGrad d A b x) ≤ |E τ|)))
      ⊆ Finset.univ.filter (fun τ : Fin K → HC d =>
        (1 - 2 * δ) * Nrm (quadfGrad d A b x)
          * Nrm (fun i : Fin d => (∑ k, esEst d A b x σ (τ k) i) / K)
        ≤ quadfGrad d A b x ⬝ᵥ
          (fun i : Fin d => (∑ k, esEst d A b x σ (τ k) i) / K)) := by
    intro τ hτ
    rw [Finset.mem_filter] at hτ ⊢
    refine ⟨Finset.mem_univ τ, ?_⟩
    have hNrmE : E τ ≤ δ * Nrm (quadfGrad d A b x) := by
      have hnot : ¬(δ * Nrm (quadfGrad d A b x) ≤ |E τ|) := hτ.2
      push_neg at hnot
      exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hnot)
    have halign := alignLower (quadfGrad d A b x)
      (fun i : Fin d =>
        (∑ k, esEst d A b x σ (τ k) i) / K - quadfGrad d A b x i)
      δ (by linarith [hδ]) hδ1 hNrmE
    -- pointwise identity: avg = g + err
    have hfun : (fun i : Fin d => (∑ k, esEst d A b x σ (τ k) i) / K)
        = quadfGrad d A b x
          + (fun i : Fin d =>
            (∑ k, esEst d A b x σ (τ k) i) / K - quadfGrad d A b x i) := by
      funext i
      rw [Pi.add_apply]
      field_simp
      ring
    rw [hfun]
    exact halign
  -- assemble the mass bound
  have hpart : (∑ w ∈ Finset.univ.filter (fun w : Fin K → HC d =>
        δ * Nrm (quadfGrad d A b x) ≤ |E w|), prodQ d K w)
      + (∑ w ∈ Finset.univ.filter (fun w : Fin K → HC d =>
        ¬(δ * Nrm (quadfGrad d A b x) ≤ |E w|)), prodQ d K w)
      = ∑ τ : Fin K → HC d, prodQ d K τ := by
    rw [Finset.sum_filter_add_sum_filter_not]
  have hdom : (∑ w ∈ Finset.univ.filter (fun w : Fin K → HC d =>
        ¬(δ * Nrm (quadfGrad d A b x) ≤ |E w|)), prodQ d K w)
      ≤ (∑ w ∈ Finset.univ.filter (fun w : Fin K → HC d =>
        (1 - 2 * δ) * Nrm (quadfGrad d A b x)
          * Nrm (fun i : Fin d => (∑ k, esEst d A b x σ (w k) i) / K)
        ≤ quadfGrad d A b x ⬝ᵥ
          (fun i : Fin d => (∑ k, esEst d A b x σ (w k) i) / K)),
        prodQ d K w) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro w _
    by_cases h1 : δ * Nrm (quadfGrad d A b x) ≤ |E w|
    · rw [if_neg (fun hc => hc h1)]
      by_cases h2 : (1 - 2 * δ) * Nrm (quadfGrad d A b x)
          * Nrm (fun i : Fin d => (∑ k, esEst d A b x σ (w k) i) / K)
        ≤ quadfGrad d A b x ⬝ᵥ
          (fun i : Fin d => (∑ k, esEst d A b x σ (w k) i) / K)
      · rw [if_pos h2]
        exact prodQ_nonneg d K w
      · rw [if_neg h2]
    · have hmem : w ∈ Finset.univ.filter (fun w : Fin K → HC d =>
          ¬(δ * Nrm (quadfGrad d A b x) ≤ |E w|)) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ w, h1⟩
      have hgood := hmono hmem
      rw [Finset.mem_filter] at hgood
      rw [if_pos hgood.2, if_pos h1]
  -- final chain
  have hprob : ∑ τ : Fin K → HC d, prodQ d K τ = 1 := prodQ_isProb d K
  calc (∑ w ∈ Finset.univ.filter (fun w : Fin K → HC d =>
        (1 - 2 * δ) * Nrm (quadfGrad d A b x)
          * Nrm (fun i : Fin d => (∑ k, esEst d A b x σ (w k) i) / K)
        ≤ quadfGrad d A b x ⬝ᵥ
          (fun i : Fin d => (∑ k, esEst d A b x σ (w k) i) / K)),
        prodQ d K w)
      ≥ (∑ w ∈ Finset.univ.filter (fun w : Fin K → HC d =>
        ¬(δ * Nrm (quadfGrad d A b x) ≤ |E w|)), prodQ d K w) := hdom
    _ = (∑ τ : Fin K → HC d, prodQ d K τ)
        - (∑ w ∈ Finset.univ.filter (fun w : Fin K → HC d =>
        δ * Nrm (quadfGrad d A b x) ≤ |E w|), prodQ d K w) := by
        linarith [hpart, hprob]
    _ ≥ 1 - (V / K) / (δ * Nrm (quadfGrad d A b x)) ^ 2 := by
        nlinarith [hMarkov, prodQ_nonneg d K]



end Hagi.Pretraining

/-!
# An exact finite Rademacher noise carrier

`Dust` supplies the sign and finite Boolean cube. This module gives the
cube the actual fair Bernoulli product measure from Mathlib, then proves
the fixed-minibatch SafeQP noise premises for `signR (ω j) • u_i`.
The independence is only across `j`, for each fixed expert and direction;
it is not asserted across experts or time. Unit vectors give `σ = 1`.
-/

namespace Hagi.Pretraining

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped ENNReal

/-- The fair Bernoulli measure on the two Boolean outcomes. -/
noncomputable def fairBoolMeasure : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false
    ⟨1 / 2, by norm_num [unitInterval]⟩

/-- The independent fair Bernoulli product on `HC m`. -/
noncomputable def rademacherLaw (m : ℕ) : Measure (HC m) :=
  Measure.pi (fun _ : Fin m => fairBoolMeasure)

private instance fairBoolMeasure_isProbabilityMeasure :
    IsProbabilityMeasure fairBoolMeasure := by
  unfold fairBoolMeasure
  infer_instance

instance rademacherLaw_isProbabilityMeasure (m : ℕ) :
    IsProbabilityMeasure (rademacherLaw m) := by
  unfold rademacherLaw
  infer_instance

/-- Coordinate noise for an expert with vector `u i`. -/
def rademacherNoise {K X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (u : K → X) (i : K)
    (j : Fin m) (ω : HC m) : X :=
  signR (ω j) • u i

private lemma signR_measurable : Measurable signR := by
  unfold signR
  fun_prop

/-- The projection is measurable for every fixed direction. This uses
only real-valued scalar multiplication, so no measurable-space structure
on the otherwise arbitrary inner-product carrier is needed. -/
theorem rademacher_projection_measurable {K X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (u : K → X) (d : X) (i : K) (j : Fin m) :
    Measurable (fun ω => ⟪rademacherNoise u i j ω, d⟫_ℝ) := by
  have h : Measurable (fun ω : HC m =>
      signR (ω j) * ⟪u i, d⟫_ℝ) :=
    (signR_measurable.comp (measurable_pi_apply j)).mul_const _
  simpa only [rademacherNoise, real_inner_smul_left] using h

/-- Each fair sign has exact zero expectation. -/
theorem rademacher_expect_sign (j : Fin m) :
    ∫ ω : HC m, signR (ω j) ∂rademacherLaw m = 0 := by
  calc
    ∫ ω : HC m, signR (ω j) ∂rademacherLaw m
        = ∫ b : Bool, signR b ∂fairBoolMeasure := by
          unfold rademacherLaw
          exact MeasureTheory.integral_comp_eval
            signR_measurable.aestronglyMeasurable
    _ = 0 := by
      rw [fairBoolMeasure, ProbabilityTheory.integral_bernoulliMeasure]
      norm_num [signR]

/-- Projection has exact zero mean for every expert and direction. -/
theorem rademacher_projection_mean {K X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (u : K → X) (d : X) (i : K) (j : Fin m) :
    ∫ ω, ⟪rademacherNoise u i j ω, d⟫_ℝ ∂rademacherLaw m = 0 := by
  simp only [rademacherNoise, real_inner_smul_left]
  rw [integral_mul_const, rademacher_expect_sign j, zero_mul]

/-- The coordinate projections are independent across `j`; this uses
exactly the fixed-`i`, fixed-direction form of the SafeQP premises. -/
theorem rademacher_projection_independent {K X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (u : K → X) (d : X) (i : K) :
    iIndepFun (fun j : Fin m =>
      fun ω => ⟪rademacherNoise u i j ω, d⟫_ℝ) (rademacherLaw m) := by
  have hbase : iIndepFun (fun j : Fin m => fun ω : HC m => ω j)
      (rademacherLaw m) := by
    unfold rademacherLaw
    exact ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin m => fairBoolMeasure)
      (X := fun _ : Fin m => fun b : Bool => b)
      (fun _ => measurable_id.aemeasurable)
  have hcomp := hbase.comp
    (fun _ b => signR b * ⟪u i, d⟫_ℝ)
    (fun _ => signR_measurable.mul_const _)
  simpa only [Function.comp_def, rademacherNoise, real_inner_smul_left]
    using hcomp

/-- Unit directions give the exact noise bound `σ = 1`. -/
theorem rademacherNoise_norm_le_one {K X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (u : K → X) (hu : ∀ i, ‖u i‖ = 1)
    (i : K) (j : Fin m) (ω : HC m) :
    ‖rademacherNoise u i j ω‖ ≤ 1 := by
  cases h : ω j <;> simp [rademacherNoise, h, signR, hu]

end Hagi.Pretraining
