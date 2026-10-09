/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

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

namespace Hagi.Dust

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

end Hagi.Dust
