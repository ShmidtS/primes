/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.FirstLayerGrad

/-!
# BatchRankOne — батч-градиент по `W1` и оптимальность шага

Продолжение `FirstLayerGrad`: батч из входов
`x t : δ → ℝ`, `t : τ`. Батч-градиент по `W1` —
`batchGrad g x i j = Σ_t g t i · x t j`, т.е. `Σ_t g_t ⊗ x_t`
(сумма rank-one). Код: `W1 -= (cos_lr * 0.7) *
newton_schulz_orthogonalize(m1, iters=3)` (hagi/core.py:1755
@ca52eb4) — Muon-шаг по `W1`; `newton_schulz_orthogonalize`
(core.py:1350 @ca52eb4); лосс — `cross_entropy` по батчу со
средним (lm.py:688 @ca52eb4). Здесь матрицы — функции
`ι → δ → ℝ`, `frobSq A = Σ_{ij} A i j²`, `fdot G Δ = Σ_{ij} G i j·Δ i j`.

* `batch_directional_derivative` — (T1) directional derivative по
  батчу: `Σ_t⟨p_t − y_t, J_t·Δ⟩ = −Σ_{ij} (batchGrad g x i j)·Δ i j`.
* `frob_inner_le`, `frob_step_le`, `sgd_step_attains` — (T2) при
  `frobSq Δ ≤ R²` спуск `-⟨G,Δ⟩ ≤ R·‖G‖_F`, и `Δ = −(R/‖G‖_F)•G`
  достигает границы: SGD-направление оптимально в шаре Фробениуса.
* `rank_one_inner`, `rank_one_le`, `rank_one_best_v` — (T3'') для
  rank-one семейства `Δ = u ⊗ v` при фикс. `u`: `⟨G, u⊗v⟩ = ⟨v, Gᵀu⟩`,
  при `‖v‖ = 1` не превосходит `‖Gᵀu‖`, и `v = Gᵀu/‖Gᵀu‖`
  достигает `‖Gᵀu‖` — оптимум ВНУТРИ rank-one-семейства.

Честная граница (down-scope): спектральный аналог T2 (max `⟨G,Δ⟩`
при `‖Δ‖_2 ≤ 1` равен `σ_max` и достигается на `U Vᵀ` — ядро
Muon) НЕ доказан: нужна дуальность спектральной/ядерной нормы
(hbridge, см. `Hagi.Step.FrobeniusLMO`). Доказан только
rank-one срез. -/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.BatchRankOne

open scoped BigOperators
open Hagi.Theory.FunctionPreservingGrowth
open Hagi.Theory.FirstLayerGrad

variable {ι δ K τ : Type} [Fintype ι] [Fintype δ] [Fintype K] [Fintype τ]

/-- Батч-градиент по `W1`: `Σ_t g_t ⊗ x_t`, т.е. `G i j = Σ_t g t i · x t j`. -/
noncomputable def batchGrad (g : τ → ι → ℝ) (x : τ → δ → ℝ) : ι → δ → ℝ :=
  fun i j => ∑ t, g t i * x t j

/-- Frobenius-скалярное произведение `Σ_{ij} G i j · Δ i j`. -/
noncomputable def fdot (G Δ : ι → δ → ℝ) : ℝ := ∑ i, ∑ j, G i j * Δ i j

/-- Квадрат нормы Фробениуса `Σ_{ij} A i j²`. -/
noncomputable def frobSq (A : ι → δ → ℝ) : ℝ := ∑ i, ∑ j, (A i j) ^ 2

/-- Строка градиента `g t i` слоя `W1` для входа `x t` (как в `w1_grad_rank_one`). -/
noncomputable def rowGrad (x : δ → ℝ) (b : ι → ℝ) (wo : ι → K → ℝ)
    (W1 : ι → δ → ℝ) (p y : K → ℝ) : ι → ℝ :=
  fun i => Hagi.Theory.FunctionPreservingGrowth.chainGrad
    (fun v i => reluMask (w1Pre x W1 i + b i) * wo i v) p y i

/-- **`batch_directional_derivative`** (T1): по батчу входов
`Σ_t⟨p_t − y_t, J_t·Δ⟩ = −Σ_{ij} (batchGrad g x i j)·Δ i j`. -/
theorem batch_directional_derivative (x : τ → δ → ℝ) (b : ι → ℝ) (wo : ι → K → ℝ)
    (W1 Δ : ι → δ → ℝ) (p y : τ → K → ℝ) :
    ∑ t, ∑ v, (p t v - y t v) * w1Jac (x t) b wo W1 Δ v
      = -∑ i, ∑ j, batchGrad (fun t => rowGrad (x t) b wo W1 (p t) (y t)) x i j * Δ i j := by
  have hn : (fun t => -(∑ i, ∑ j, rowGrad (x t) b wo W1 (p t) (y t) i * x t j * Δ i j))
      = fun t => ∑ v, (p t v - y t v) * w1Jac (x t) b wo W1 Δ v := by
    funext t
    rw [w1_directional_derivative (x t) b wo W1 Δ (p t) (y t)]
    congr 1
  rw [← hn]
  show ∑ t, -(∑ i, ∑ j, rowGrad (x t) b wo W1 (p t) (y t) i * x t j * Δ i j) = _
  rw [Finset.sum_neg_distrib (fun t => ∑ i, ∑ j,
    rowGrad (x t) b wo W1 (p t) (y t) i * x t j * Δ i j)]
  have h2 : (∑ t, ∑ i, ∑ j, rowGrad (x t) b wo W1 (p t) (y t) i * x t j * Δ i j)
      = ∑ i, ∑ j, batchGrad (fun t => rowGrad (x t) b wo W1 (p t) (y t)) x i j * Δ i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    simp only [batchGrad]
    refine Finset.sum_congr rfl fun j _ => ?_
    calc ∑ t, rowGrad (x t) b wo W1 (p t) (y t) i * x t j * Δ i j
        = ∑ t, (rowGrad (x t) b wo W1 (p t) (y t) i * x t j) * Δ i j :=
          Finset.sum_congr rfl fun t _ => by ring
      _ = (∑ t, rowGrad (x t) b wo W1 (p t) (y t) i * x t j) * Δ i j :=
          (Finset.sum_mul _ _ _).symm
  rw [h2]

/-- `frobSq` неотрицательна. -/
theorem frobSq_nonneg (A : ι → δ → ℝ) : 0 ≤ frobSq A := by
  unfold frobSq
  positivity

/-- Коши–Шварц в алгебраической форме по `ι × δ`:
`(∑ q, G q Δ q)² ≤ (∑ q, G q²)·(∑ q, Δ q²)`. -/
theorem fdot_sq_le (G Δ : ι → δ → ℝ) :
    (fdot G Δ) ^ 2 ≤ frobSq G * frobSq Δ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × δ))
    (fun q => G q.1 q.2) (fun q => Δ q.1 q.2)
  simpa only [fdot, frobSq, Fintype.sum_prod_type] using h

/-- **`frob_inner_abs_le`**: Коши–Шварц в форме Фробениуса:
`|⟨G, Δ⟩| ≤ ‖G‖_F·‖Δ‖_F`. -/
theorem frob_inner_abs_le (G : ι → δ → ℝ) (Δ : ι → δ → ℝ) :
    |fdot G Δ| ≤ Real.sqrt (frobSq G) * Real.sqrt (frobSq Δ) := by
  have h' := Real.sqrt_le_sqrt (fdot_sq_le G Δ)
  rw [Real.sqrt_mul (frobSq_nonneg G), Real.sqrt_sq_eq_abs] at h'
  exact h'

/-- **`frob_inner_le`**: `⟨G, Δ⟩ ≤ ‖G‖_F·‖Δ‖_F`. -/
theorem frob_inner_le (G Δ : ι → δ → ℝ) :
    fdot G Δ ≤ Real.sqrt (frobSq G) * Real.sqrt (frobSq Δ) :=
  le_trans (le_abs_self _) (frob_inner_abs_le G Δ)

/-- **`frob_step_le`** (T2, граница): в шаре `frobSq Δ ≤ R²`, `R ≥ 0`,
спуск не лучше `-R·‖G‖_F`: `-R·‖G‖_F ≤ ⟨G, Δ⟩`. -/
theorem frob_step_le (G Δ : ι → δ → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hΔ : frobSq Δ ≤ R ^ 2) :
    -R * Real.sqrt (frobSq G) ≤ fdot G Δ := by
  have hle : Real.sqrt (frobSq Δ) ≤ R := by
    rw [← Real.sqrt_sq hR]
    exact Real.sqrt_le_sqrt hΔ
  have hnn : 0 ≤ Real.sqrt (frobSq G) := Real.sqrt_nonneg _
  have h1 : Real.sqrt (frobSq G) * Real.sqrt (frobSq Δ)
      ≤ Real.sqrt (frobSq G) * R := mul_le_mul_of_nonneg_left hle hnn
  have h2 := le_trans (frob_inner_abs_le G Δ) h1
  rw [mul_comm] at h2
  linarith [(abs_le.mp h2).1]

/-- **`sgd_step_attains`** (T2, достижимость): для `G ≠ 0` шаг
`Δ = -(R/‖G‖_F)•G` допустим (`frobSq Δ = R²`) и достигает границы
`⟨G, Δ⟩ = -R·‖G‖_F` — SGD-направление оптимально. -/
theorem sgd_step_attains (G : ι → δ → ℝ) {R : ℝ} (hG : G ≠ 0) :
    frobSq (-(R / Real.sqrt (frobSq G)) • G) = R ^ 2 ∧
      fdot G (-(R / Real.sqrt (frobSq G)) • G) = -R * Real.sqrt (frobSq G) := by
  have hs : 0 < frobSq G := by
    by_contra h0
    have h1 : frobSq G = 0 := le_antisymm (by linarith) (frobSq_nonneg G)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hG
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)).mp h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp
      (hz i (Finset.mem_univ i)) j (Finset.mem_univ j)
    exact hj (show G i j = 0 by nlinarith [h2])
  have hsq : Real.sqrt (frobSq G) ^ 2 = frobSq G := Real.sq_sqrt hs.le
  have hs0 : Real.sqrt (frobSq G) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
  have hfrob (c : ℝ) : frobSq (c • G) = c ^ 2 * frobSq G := by
    simp only [frobSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_pow]
  have hsmul (c : ℝ) : fdot G (c • G) = c * frobSq G := by
    simp only [fdot, frobSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  constructor
  · rw [hfrob, neg_sq, div_pow, hsq]
    exact div_mul_cancel₀ _ (ne_of_gt hs)
  · have h4 : R * frobSq G / Real.sqrt (frobSq G) = R * Real.sqrt (frobSq G) := by
      rw [div_eq_iff hs0]
      linarith [congrArg (fun z => R * z) hsq]
    rw [hsmul, neg_mul, div_mul_eq_mul_div, h4]
    ring

/-- Rank-one матрица `u ⊗ v`: `(u ⊗ v) i j = u i · v j`. -/
noncomputable def r1 (u : ι → ℝ) (v : δ → ℝ) : ι → δ → ℝ :=
  fun i j => u i * v j

/-- `Gᵀ u`: столбцовая комбинация `(Gᵀ u) j = Σ_i G i j · u i`. -/
noncomputable def colComb (G : ι → δ → ℝ) (u : ι → ℝ) : δ → ℝ :=
  fun j => ∑ i, G i j * u i

omit [Fintype K] [Fintype τ] in
/-- **`rank_one_inner`**: `⟨G, u ⊗ v⟩ = ⟨v, Gᵀ u⟩` — спаривание с
rank-one шагом зависит от `G` только через `Gᵀ u`. -/
theorem rank_one_inner (G : ι → δ → ℝ) (u : ι → ℝ) (v : δ → ℝ) :
    fdot G (r1 u v) = ∑ j, v j * colComb G u j := by
  simp only [fdot, r1, colComb, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- **`rank_one_le`** (T3'', граница): `⟨G, u ⊗ v⟩ ≤ ‖v‖·‖Gᵀ u‖` и
`‖Gᵀ u‖ ≤ ‖u‖·‖G‖_F`. -/
theorem rank_one_le (G : ι → δ → ℝ) (u : ι → ℝ) (v : δ → ℝ) :
    fdot G (r1 u v) ≤ Real.sqrt (∑ j, v j ^ 2) * Real.sqrt (∑ j, colComb G u j ^ 2) ∧
      (∑ j, colComb G u j ^ 2) ≤ (∑ i, u i ^ 2) * frobSq G := by
  constructor
  · have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset δ) v (colComb G u)
    have h' := Real.sqrt_le_sqrt h
    rw [Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg _), Real.sqrt_sq_eq_abs] at h'
    rw [rank_one_inner]
    exact (abs_le.mp h').2
  · have hj : ∀ j, (colComb G u j) ^ 2
        ≤ (∑ i, u i ^ 2) * (∑ i, (G i j) ^ 2) := by
      intro j
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
        (fun i => G i j) u
      simpa only [colComb, mul_comm] using h
    calc ∑ j, colComb G u j ^ 2 ≤ ∑ j, (∑ i, u i ^ 2) * (∑ i, (G i j) ^ 2) :=
          Finset.sum_le_sum fun j _ => hj j
      _ = (∑ i, u i ^ 2) * frobSq G := by
          simp only [Finset.sum_mul, frobSq, Finset.mul_sum]
          rw [Finset.sum_comm]

omit [Fintype K] [Fintype τ] in
/-- **`rank_one_best_v`** (T3'', достижимость): при фикс. `u`, `Gᵀ u ≠ 0`,
шаг `v = (Gᵀu)/‖Gᵀu‖` единичный и достигает `⟨G, u ⊗ v⟩ = ‖Gᵀ u‖` —
совместно с `rank_one_le` (`‖v‖ = 1`) это оптимум внутри rank-one-семейства. -/
theorem rank_one_best_v (G : ι → δ → ℝ) (u : ι → ℝ) (hw : colComb G u ≠ 0) :
    let s := Real.sqrt (∑ k, colComb G u k ^ 2)
    (∑ j, (s⁻¹ * colComb G u j) ^ 2 = 1) ∧
      fdot G (r1 u fun j => s⁻¹ * colComb G u j) = s := by
  intro s
  have hp : 0 < ∑ k, colComb G u k ^ 2 := by
    by_contra h0
    have h1 : ∑ k, colComb G u k ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun k _ => sq_nonneg _)
    obtain ⟨q, hq⟩ := Function.ne_iff.mp hw
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)).mp h1
      q (Finset.mem_univ q)
    exact hq (show colComb G u q = 0 by nlinarith [h2])
  have hs0 : s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hw2 : s ^ 2 = ∑ k, colComb G u k ^ 2 := Real.sq_sqrt hp.le
  constructor
  · simp only [mul_pow, ← Finset.mul_sum]
    rw [← hw2]
    field_simp
  · rw [rank_one_inner]
    have hsqv : ∑ j, colComb G u j * colComb G u j = s ^ 2 := by
      rw [hw2]
      exact Finset.sum_congr rfl fun j _ => (sq (colComb G u j)).symm
    rw [Finset.sum_congr rfl fun j _ => show s⁻¹ * colComb G u j * colComb G u j
        = s⁻¹ * (colComb G u j * colComb G u j) by ring]
    rw [← Finset.mul_sum, hsqv]
    field_simp

end Hagi.Theory.BatchRankOne
