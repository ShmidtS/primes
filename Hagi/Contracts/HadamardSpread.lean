/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Contracts.HadamardTernaryBridge
set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# The Hadamard spread ternary error bound (average-case, deterministic)

Audit A10 §9 item 5: «Теорема о контракции реального квантайзера.
Худший случай даёт (α≈0.106, ε), а для блоков после Адамара нужна
средняя версия: измерено ≈0.33». This module delivers the honest
formalizable core of the "average version": a DETERMINISTIC
coordinate/energy-spread story, no measure theory.

The mechanism (QuIP#-style, but pinned to THIS repo's carriers —
`Hagi.Core.hadamardOrthonormal` and `Hagi.Runtime.qTern`):

* `hadamard_spread_bound` — Parseval: the orthonormal Hadamard
  transform preserves energy EXACTLY, `∑ (Hx)² = ∑ x²`. Spread is
  not energy loss; it is relocation.
* `hadamard_large_coord_count_le` — Markov count on that energy:
  #{j : |Hx j| > t} · t² ≤ ‖x‖². Few coordinates can be large.
* `hadamard_ternary_error_bound` — the main decomposition: total
  ternary quantization error on the Hadamard image is at most
  `2^k·(s/2)² + (energy in out-of-range coordinates)` —
  `n·ε_small² + energy-above-threshold` with ε_small = s/2 the
  exact `qTern_error_in` half-step of the C238/C246 carrier.
* `hadamard_ternary_error_bound_of_spread` — conditional ρ-form:
  if the out-of-range energy is ≤ ρ·‖x‖², the error is
  ≤ n(s/2)² + ρ‖x‖². `hadamard_ternary_error_worst_case` is the
  unconditional ρ = 1 reference. ρ < 1 is a PREMISE (like the
  bridge's μ-incoherence): Hadamard does NOT universally spread —
  see the bridge's `hadamard_not_universally_incoherent`.

Honesty notes: "average case" here means the deterministic
energy-fraction premise, NOT probabilistic sphere averaging
(measure theory is out of scope). The empirical constants
(worst-case α ≈ 0.106, measured post-Hadamard ≈ 0.33) stay in this
docstring as motivation only — the theorems carry no empirical
numbers. In-scale coordinates contribute ε_small = s/2 per
coordinate, not 0 (the real ternary grid is not exact on ℝ); that
is the honest instantiation of the audit item's ε_small.
-/

open scoped Matrix Classical
open Hagi.Core Hagi.Runtime Hagi.Contracts.HadamardTernaryBridge

namespace Hagi.Contracts.HadamardSpread

/-! ## 1. Parseval (exact energy) for the orthonormal Hadamard -/

/-- **`hadamard_spread_bound`** — Parseval for the orthonormal
Sylvester transform: `∑ j, (Hx) j ^ 2 = ∑ j, x j * x j`. The
normalized Hadamard (entries ±1/√(2^k), see
`Hagi.Core.hadamardOrthonormal`) preserves energy exactly —
orthogonality (`hadamardOrthonormal_mul_transpose`) plus symmetry
(`hadamardOrthonormal_transpose`) via `dotProduct_mulVec`. -/
theorem hadamard_spread_bound {k : ℕ} (x : (Fin k → ZMod 2) → ℝ) :
    ∑ j, ((hadamardOrthonormal k *ᵥ x) j) ^ 2 = ∑ j, x j * x j := by
  have hsymm := hadamardOrthonormal_transpose k
  have hHT : (hadamardOrthonormal k)ᵀ * hadamardOrthonormal k = 1 := by
    have h2 := hadamardOrthonormal_mul_transpose (k := k)
    rw [hsymm] at h2
    rw [hsymm]
    exact h2
  have h1 : ∑ j, ((hadamardOrthonormal k *ᵥ x) j) ^ 2
      = dotProduct (hadamardOrthonormal k *ᵥ x) (hadamardOrthonormal k *ᵥ x) := by
    simp [dotProduct, pow_two]
  rw [h1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, hHT, Matrix.one_mulVec]
  rfl

/-- **`hadamard_spread_bound_image`** — Parseval through the
bridge's reindex `hadamardImage x : Fin (2^k) → ℝ`: the energy of
the reindexed Hadamard image equals the source energy. Reindex
invariance (`Fintype.sum_equiv`) — no dependence on the choice of
bijection. -/
theorem hadamard_spread_bound_image {k : ℕ} (x : (Fin k → ZMod 2) → ℝ) :
    ∑ i, (hadamardImage x i) ^ 2 = ∑ j, x j * x j := by
  have hcard : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by simp
  unfold hadamardImage
  calc ∑ i : Fin (2 ^ k), ((hadamardOrthonormal k *ᵥ x)
        ((Fintype.equivFinOfCardEq hcard).symm i)) ^ 2
      = ∑ j : (Fin k → ZMod 2), ((hadamardOrthonormal k *ᵥ x) j) ^ 2 :=
        Fintype.sum_equiv (Fintype.equivFinOfCardEq hcard).symm
          (fun i => ((hadamardOrthonormal k *ᵥ x)
            ((Fintype.equivFinOfCardEq hcard).symm i)) ^ 2)
          (fun j => ((hadamardOrthonormal k *ᵥ x) j) ^ 2)
          (fun i => by simp)
    _ = ∑ j, x j * x j := hadamard_spread_bound x

/-! ## 2. Markov count lemma on the transform energy -/

/-- **`hadamard_large_coord_count_le`** — the Markov count lemma:
for `t > 0`, the number of transform coordinates with `|Hx j| > t`
satisfies `count · t² ≤ ∑ x²`. Each large coordinate carries more
than `t²` of the (Parseval-preserved) energy, so large coordinates
are proportionally rare — the deterministic core of the
post-Hadamard spread story. Stated on the source index type; no
reindex involved. -/
theorem hadamard_large_coord_count_le {k : ℕ} (t : ℝ) (ht : 0 < t)
    (x : (Fin k → ZMod 2) → ℝ) :
    ((Finset.univ.filter
        (fun j => t < |(hadamardOrthonormal k *ᵥ x) j|)).card : ℝ) * t ^ 2
      ≤ ∑ j, x j * x j := by
  have hle : ∀ j ∈ Finset.univ.filter
      (fun j => t < |(hadamardOrthonormal k *ᵥ x) j|),
      t ^ 2 ≤ ((hadamardOrthonormal k *ᵥ x) j) ^ 2 := by
    intro j hj
    have hlt := (Finset.mem_filter.mp hj).2
    have habs : 0 ≤ |(hadamardOrthonormal k *ᵥ x) j| := abs_nonneg _
    have h2 : t ^ 2 < |(hadamardOrthonormal k *ᵥ x) j| ^ 2 := by nlinarith
    rw [sq_abs] at h2
    linarith
  have hsub : ∑ j ∈ Finset.univ.filter
      (fun j => t < |(hadamardOrthonormal k *ᵥ x) j|),
      ((hadamardOrthonormal k *ᵥ x) j) ^ 2 ≤ ∑ j, x j * x j := by
    calc ∑ j ∈ Finset.univ.filter
          (fun j => t < |(hadamardOrthonormal k *ᵥ x) j|),
          ((hadamardOrthonormal k *ᵥ x) j) ^ 2
        ≤ ∑ j, ((hadamardOrthonormal k *ᵥ x) j) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _)
            (fun _ _ _ => sq_nonneg _)
      _ = ∑ j, x j * x j := hadamard_spread_bound x
  have hcard : ((Finset.univ.filter
      (fun j => t < |(hadamardOrthonormal k *ᵥ x) j|)).card : ℝ) * t ^ 2
      ≤ ∑ j ∈ Finset.univ.filter
          (fun j => t < |(hadamardOrthonormal k *ᵥ x) j|),
          ((hadamardOrthonormal k *ᵥ x) j) ^ 2 := by
    calc ((Finset.univ.filter
            (fun j => t < |(hadamardOrthonormal k *ᵥ x) j|)).card : ℝ) * t ^ 2
        = ∑ j ∈ Finset.univ.filter
            (fun j => t < |(hadamardOrthonormal k *ᵥ x) j|), t ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.univ.filter
            (fun j => t < |(hadamardOrthonormal k *ᵥ x) j|),
            ((hadamardOrthonormal k *ᵥ x) j) ^ 2 := Finset.sum_le_sum hle
  exact le_trans hcard hsub

/-! ## 3. The spread ternary error bound -/

/-- **`hadamard_ternary_error_bound`** (MAIN) — the deterministic
average-case decomposition of the ternary quantizer error on the
Hadamard image: total squared error ≤ `2^k · (s/2)²` (in-scale
half-step rounding, `qTern_error_in`, ε_small = s/2) plus the
energy sitting in out-of-range coordinates (`ternInRange s (·)`
false). From `ternary_split_le` + the pointwise overshoot bound
`(|w i| − s)² ≤ w i²` valid whenever `|w i| > 3s/2`. -/
theorem hadamard_ternary_error_bound {k : ℕ} (s : ℝ) (hs : 0 < s)
    (x : (Fin k → ZMod 2) → ℝ) :
    ∑ i, (hadamardImage x i - qTern s (hadamardImage x i)) ^ 2
      ≤ (2 ^ k : ℝ) * (s / 2) ^ 2
        + ∑ i ∈ Finset.univ.filter
            (fun i => ¬ ternInRange s (hadamardImage x i)),
            (hadamardImage x i) ^ 2 := by
  have hsplit := ternary_split_le s hs (hadamardImage x)
  push_cast at hsplit
  have hsat : satTail s (hadamardImage x)
      ≤ ∑ i ∈ Finset.univ.filter
          (fun i => ¬ ternInRange s (hadamardImage x i)),
          (hadamardImage x i) ^ 2 := by
    unfold satTail
    apply Finset.sum_le_sum
    intro i hi
    have hout : 3 * s / 2 < |hadamardImage x i| :=
      not_le.mp (Finset.mem_filter.mp hi).2
    have hnneg : 0 ≤ |hadamardImage x i| := abs_nonneg _
    have h1 : 0 ≤ |hadamardImage x i| - s := by linarith
    have h2 : |hadamardImage x i| - s ≤ |hadamardImage x i| := by linarith
    have h3 : (|hadamardImage x i| - s) ^ 2 ≤ (hadamardImage x i) ^ 2 := by
      rw [← sq_abs (hadamardImage x i)]
      exact sq_le_sq' (by linarith) h2
    exact h3
  linarith

/-- **`hadamard_ternary_error_bound_of_spread`** — the conditional
ρ-form: if the out-of-range energy of the Hadamard image is at most
`ρ · ‖x‖²`, the total ternary error is at most
`2^k·(s/2)² + ρ·‖x‖²`. For spread vectors (ρ small) this beats the
worst case `hadamard_ternary_error_worst_case` (ρ = 1) — the
conditional theorem telling the audit's «после Адамара ≈0.33 vs
худший случай α≈0.106» story. ρ is a PREMISE: Hadamard does not
universally spread (bridge: `hadamard_not_universally_incoherent`). -/
theorem hadamard_ternary_error_bound_of_spread {k : ℕ} (s ρ : ℝ) (hs : 0 < s)
    (x : (Fin k → ZMod 2) → ℝ)
    (hspread : ∑ i ∈ Finset.univ.filter
        (fun i => ¬ ternInRange s (hadamardImage x i)),
        (hadamardImage x i) ^ 2 ≤ ρ * ∑ j, x j * x j) :
    ∑ i, (hadamardImage x i - qTern s (hadamardImage x i)) ^ 2
      ≤ (2 ^ k : ℝ) * (s / 2) ^ 2 + ρ * ∑ j, x j * x j := by
  have h := hadamard_ternary_error_bound s hs x
  linarith

/-- **`hadamard_ternary_error_worst_case`** — the unconditional
reference point (ρ = 1): without any spread premise the total
ternary error on the Hadamard image is at most `2^k·(s/2)² + ‖x‖²`
(the whole energy could, in the worst case, sit in saturating
coordinates). This is the formal counterpart of the audit's
worst-case α-regime that the spread premise improves upon. -/
theorem hadamard_ternary_error_worst_case {k : ℕ} (s : ℝ) (hs : 0 < s)
    (x : (Fin k → ZMod 2) → ℝ) :
    ∑ i, (hadamardImage x i - qTern s (hadamardImage x i)) ^ 2
      ≤ (2 ^ k : ℝ) * (s / 2) ^ 2 + ∑ j, x j * x j := by
  have h := hadamard_ternary_error_bound s hs x
  have hsub : ∑ i ∈ Finset.univ.filter
      (fun i => ¬ ternInRange s (hadamardImage x i)),
      (hadamardImage x i) ^ 2 ≤ ∑ i, (hadamardImage x i) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
  rw [hadamard_spread_bound_image x] at hsub
  linarith

/-! ## 4. Anchors (n = 2, k = 1): the spread vector `x0 = (2, 0)` -/

/-- **`x0`** — the anchor source: energy 4 concentrated in one
coordinate (`x0 j = 2` on the zero index, 0 elsewhere), the
pre-rotation spike that saturates any ternary grid at scale 1
(`|2| > 3/2`). -/
def x0 : (Fin 1 → ZMod 2) → ℝ := fun j => if j 0 = 0 then 2 else 0

/-- **`hsq_two`** — the numeric fact `√2 · √2 = 2` backing the
anchor computations. -/
theorem hsq_two : Real.sqrt 2 * Real.sqrt 2 = 2 := by
  rw [← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **`hsqrt_big`** — `1 < √2` (both anchor coordinates exceed
t = 1). -/
theorem hsqrt_big : (1 : ℝ) < Real.sqrt 2 := by
  by_contra hc
  have hc' : Real.sqrt 2 ≤ 1 := le_of_not_gt hc
  have h1 : Real.sqrt 2 * Real.sqrt 2 ≤ 1 * 1 :=
    mul_le_mul hc' hc' (by positivity) (by norm_num)
  rw [hsq_two] at h1
  norm_num at h1

/-- **`hsqrt_32`** — `√2 ≤ 3/2` (both anchor coordinates are INSIDE
the ternary range at scale s = 1). -/
theorem hsqrt_32 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hsq_two]

/-- **`x0_two_term_sum`** — enumeration helper for the 2-element
index type `Fin 1 → ZMod 2`: any sum is the two explicit terms. -/
theorem x0_two_term_sum (F : (Fin 1 → ZMod 2) → ℝ) :
    ∑ l, F l = F (fun _ => 0) + F (fun _ => 1) := by
  have hne : (fun _ : Fin 1 => (0 : ZMod 2)) ≠ (fun _ : Fin 1 => (1 : ZMod 2)) := by
    intro hc
    exact zero_ne_one (congrFun hc 0)
  have henum : (Finset.univ : Finset (Fin 1 → ZMod 2))
      = ({fun _ => 0, fun _ => (1 : ZMod 2)} :
          Finset (Fin 1 → ZMod 2)) := by
    ext j'
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    rcases zmod2_cases (j' 0) with h | h
    · left
      funext l
      rw [show l = 0 from Subsingleton.elim _ _, h]
    · right
      funext l
      rw [show l = 0 from Subsingleton.elim _ _, h]
  rw [henum]
  simp [hne]

/-- **`x0_Hx`** — the spread computation: the Hadamard image of the
spike `x0 = (2, 0)` is `H x0 = (√2, √2)` — energy 4 spread over
BOTH coordinates, ∞-norm drops from 2 to √2 ≈ 1.41, below the
ternary ceiling 3s/2 = 1.5 at s = 1. This is the n = 2 instance of
the audit's post-Hadamard spreading mechanism. -/
theorem x0_Hx (j : Fin 1 → ZMod 2) :
    (hadamardOrthonormal 1 *ᵥ x0) j = Real.sqrt 2 := by
  rcases zmod2_cases (j 0) with h | h
  · unfold hadamardOrthonormal hadamardReal Matrix.mulVec x0
    simp [dotProduct, sylvester, chi2, h, Fin.isValue]
    rw [x0_two_term_sum]
    simp
    field_simp
    nlinarith [hsq_two]
  · unfold hadamardOrthonormal hadamardReal Matrix.mulVec x0
    simp [dotProduct, sylvester, chi2, h, Fin.isValue]
    rw [x0_two_term_sum]
    simp
    field_simp
    nlinarith [hsq_two]

/-- **`spread_anchor_large_coord_count`** — the count lemma
numerically: at t = 1 BOTH transform coordinates exceed t
(count = 2 = full dimension of `Fin 1 → ZMod 2`), and the lemma
reads `2 · 1² ≤ 4` — energy 4 accommodates two coordinates above
t = 1 but nothing more. Note t = 1 here is a free parameter of the
count lemma, distinct from the ternary threshold 3s/2 = 1.5 used by
`spread_anchor_error`. -/
theorem spread_anchor_large_coord_count :
    (Finset.univ.filter (fun j : Fin 1 → ZMod 2 =>
      (1 : ℝ) < |(hadamardOrthonormal 1 *ᵥ x0) j|)).card = 2 := by
  have hall : ∀ j : Fin 1 → ZMod 2,
      (1 : ℝ) < |(hadamardOrthonormal 1 *ᵥ x0) j| := by
    intro j
    rw [x0_Hx j, abs_of_pos (by positivity)]
    exact hsqrt_big
  have huniv : Finset.univ.filter (fun j : Fin 1 → ZMod 2 =>
      (1 : ℝ) < |(hadamardOrthonormal 1 *ᵥ x0) j|) = Finset.univ := by
    ext j
    simp [Finset.mem_filter, hall j]
  rw [huniv, Finset.card_univ, Fintype.card_fun]
  norm_num

/-- **`spread_anchor_error`** — the error bound numerically:
`H x0 = (√2, √2)` is fully spread, both coordinates in ternary
range at s = 1 (saturation energy 0), so `hadamard_ternary_error_bound`
instantiates to total error ≤ `2 · (1/2)²` — pure half-step
rounding. Before rotation the spike 2 saturated (error (2−1)² = 1 ≥
the whole post-rotation budget); the rotation converts a saturation
problem into a rounding problem. -/
theorem spread_anchor_error :
    ∑ i, (hadamardImage x0 i - qTern 1 (hadamardImage x0 i)) ^ 2
      ≤ (2 : ℝ) * (1 / 2) ^ 2 := by
  have himg : ∀ i, hadamardImage x0 i = Real.sqrt 2 := fun i => x0_Hx _
  have hin : ∀ i, ternInRange 1 (hadamardImage x0 i) := by
    intro i
    rw [himg i, ternInRange, abs_of_pos (by positivity)]
    simpa using hsqrt_32
  have h := hadamard_ternary_error_bound (k := 1) (s := 1) (by norm_num) x0
  have h0 : ∑ i ∈ Finset.univ.filter
      (fun i => ¬ ternInRange 1 (hadamardImage x0 i)),
      (hadamardImage x0 i) ^ 2 = 0 := by
    rw [Finset.sum_eq_zero]
    intro i hi
    exact absurd (hin i) (Finset.mem_filter.mp hi).2
  rw [h0] at h
  norm_num at h ⊢
  linarith

end Hagi.Contracts.HadamardSpread
