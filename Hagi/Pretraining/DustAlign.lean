/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Pretraining.DustCert
import Hagi.Architecture.AlignedMerge
import Hagi.Pretraining.DustVarK

set_option linter.style.header false

/-!
# DustAlign: the alignment law (R187 — bridge E)

The theoretical form of Dust's measured cosine law
cos(K) = c_max/√(1+c/K) (Fig. 5): the two-draw averaged
zeroth-order estimate aligns with the true gradient with
explicitly bounded failure probability.

Geometry (dotProduct norms, no matrix machinery):

* `absDot_le`: |⟨a,b⟩| ≤ ‖a‖·‖b‖ (Cauchy–Schwarz in
  square-root form — from the squared CS of R182).
* `nrmTriangle`: ‖a+b‖ ≤ ‖a‖+‖b‖.
* `alignLower`: if the error is relatively small
  (‖e‖ ≤ δ·‖g‖, δ ≤ 1), the alignment dominates its floor:
  ⟨g, g+e⟩ ≥ (1−2δ)·‖g‖·‖g+e‖ — the multiplicative
  cosine bound without ever dividing by norms.

Probability (Markov on the pair space, welded by R185):

* `dustAlignment`: on the two-draw pair space, the averaged
  estimate ĝ satisfies ⟨g, ĝ⟩ ≥ (1−2δ)‖g‖‖ĝ‖ except on a
  pair set of q-mass ≤ V/(δ²·‖g‖²), where V = E‖ĝ−g‖² is
  the (halved, R184) estimator error energy. Failure decays
  as 1/K in the population — the proved shape of Fig. 5.
-/

namespace Hagi.Dust

open Finset

/-- The dotProduct norm. -/
noncomputable def Nrm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

/-- Cauchy–Schwarz in norm form. -/
theorem absDot_le {n : ℕ} (a b : Fin n → ℝ) :
    |a ⬝ᵥ b| ≤ Nrm a * Nrm b := by
  have h : (a ⬝ᵥ b) ^ 2 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) := Cortex.dotCS a b
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
of q-mass ≤ V/(δ²·‖g‖²), where V = E‖ĝ−g‖² — by R184 the
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
  have hVform : KLS.expQ (pairQ d)
        (fun p => (Nrm (fun i => (esEst d A b x σ p.1 i
          + esEst d A b x σ p.2 i) / 2 - quadfGrad d A b x i)) ^ 2)
      = (∑ q : HC d × HC d, ∑ i, ((esEst d A b x σ q.1 i
          - quadfGrad d A b x i) + (esEst d A b x σ q.2 i
            - quadfGrad d A b x i)) ^ 2) / (4 * 2 ^ d * 2 ^ d) := by
    simp only [KLS.expQ, pairQ, Nrm, Real.sq_sqrt, dotProduct,
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
  have hMarkov := KLS.klsChebyshev (pairQ d) (pairQ_nonneg d) V
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
  have hVform : KLS.expQ (prodQ d K) (fun τ => (E τ) ^ 2) = V / K := by
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
    unfold KLS.expQ at hbase ⊢
    simp only [hsq]
    exact hbase
  -- Markov/Chebyshev
  have hMarkov := KLS.klsChebyshev (prodQ d K) (prodQ_nonneg d K)
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



end Hagi.Dust
