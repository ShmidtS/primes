/-
Copyright (c) 2026. All rights reserved.
-/
import Hagi.Pretraining.Dust

/-!
# DustVarK — the general-K dispersion law (Dust §2.2)

The K = 2 case (`varianceHalving`) says: averaging two draws
halves the mean square error. This module proves the law for
EVERY batch size K:

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

namespace Hagi.Dust

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
square divided by K — for EVERY K ≥ 1, not just K = 2. -/
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

end Hagi.Dust
