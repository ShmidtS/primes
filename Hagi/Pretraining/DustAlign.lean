/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.AlignedMerge
import Hagi.Probability.KLSBridge
import Hagi.Pretraining.Dust
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
  the (halved,) estimator error energy. Failure decays
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
