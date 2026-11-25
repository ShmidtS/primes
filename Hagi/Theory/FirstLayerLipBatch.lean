/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.FirstLayerLip
import Hagi.Theory.MuonDescentW1Rect

/-!
# FirstLayerLipBatch — гладкость CE-слоя `W1` по БАТЧУ входов

C685. Батч-версия `Hagi.Theory.FirstLayerLip.w1CE_descent_lemma` (C684):
цель — сумма CE по входам `x : τ → δ → ℝ` (`w1BatchCE`, тот же объект,
что `w1BatchObjR`), направление — `D_batch = Σ_t g_t ⊗ x_t`
(`w1BatchDescentDir` = минус `w1BatchGradR`).

* `xMaxSq`, `S_batch` — `S_batch = ‖wo‖_F²·Σ_t ‖x t‖₂²` (сумма
  констант C684 по входам); `S_batch_le_max`: `S_batch ≤
  B·‖wo‖_F²·max_t ‖x t‖₂²` (батч непустой: `Nonempty τ`).
* `w1BatchCE_descent_lemma` — сумма лемм C684 с `S_t = ‖wo‖_F²·‖x t‖₂² ≤ S_batch`.
* `w1BatchCE_drop_of_step`, `w1BatchCE_optimal_step_drop` — шаг
  `W1 + γ•D_batch`: drop ≥ `nlDrop γ S_batch ‖D_batch‖_F`,
  `γ*_batch = 1/S_batch`, drop `‖D_batch‖²/(2S_batch)`.
* `w1MeanCE_optimal_step_drop` — форма кода (`ce(reduction="mean")`,
  lm.py:299 @ca52eb4): `S_mean = S_batch/B`, `γ* = B/S_batch`,
  drop `‖D_batch/B‖²/(2·S_batch/B)`.

Условие то же, что в C684: маски активации каждого входа равны вдоль
шага (relu-блок негладкий на kink). -/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.FirstLayerLipBatch

open scoped BigOperators
open Hagi.Theory.FirstLayerGrad
open Hagi.Theory.FirstLayerLip
open Hagi.Theory.FunctionPreservingGrowth

variable {ι δ K τ : Type} [Fintype ι] [Fintype δ] [Fintype K] [Nonempty K] [DecidableEq K]
  [Fintype τ] [Nonempty τ]

/-- Сумма CE по батчу входов (тот же объект, что `w1BatchObjR`). -/
noncomputable def w1BatchCE (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ)
    (x : τ → δ → ℝ) (W1 : ι → δ → ℝ) : ℝ :=
  ∑ t, w1CE (y t) b wo (x t) W1

/-- Максимальный квадрат ℓ₂-нормы входа батча: `max_t ‖x t‖₂²`
(батч непустой: `Nonempty τ`). -/
noncomputable def xMaxSq (x : τ → δ → ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun t => ∑ j, x t j ^ 2)

/-- Гладкость суммы CE по батчу: `S_batch = ‖wo‖_F²·Σ_t ‖x t‖₂²`
(сумма констант C684 по входам; `S_batch_le_max` даёт границу
`‖wo‖_F²·B·max_t ‖x t‖₂²`). -/
noncomputable def S_batch (wo : ι → K → ℝ) (x : τ → δ → ℝ) : ℝ :=
  (∑ i, ∑ v, wo i v ^ 2) * ∑ t, ∑ j, x t j ^ 2

/-- Направление спуска суммы CE по батчу: `D_batch (i,j) = Σ_t g_t i·x t j`
(`g_t` — rank-one градиент входа `t`), т.е. минус `w1BatchGradR`. -/
noncomputable def w1BatchDescentDir (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ)
    (x : τ → δ → ℝ) (W1 : ι → δ → ℝ) : ι → δ → ℝ :=
  Hagi.Theory.BatchRankOne.batchGrad
    (fun t => Hagi.Theory.BatchRankOne.rowGrad (x t) b wo W1
      (Hagi.Energy.smax (w1L W1 b wo (x t))) (Hagi.Theory.MuonDescentW1.onehot (y t))) x

omit [Nonempty τ] in
omit [Nonempty K] [Nonempty τ] in
/-- `w1BatchDescentDir` — минус батч-градиент `w1BatchGradR`. -/
theorem w1BatchDescentDir_eq (y : τ → K) (b : ι → ℝ)
    (wo : ι → K → ℝ) (x : τ → δ → ℝ) (W1 : ι → δ → ℝ) (i : ι) (j : δ) :
    w1BatchDescentDir y b wo x W1 i j
      = -Hagi.Theory.MuonDescentW1Rect.w1BatchGradR x y b wo W1 i j := by
  simp [w1BatchDescentDir, Hagi.Theory.MuonDescentW1Rect.w1BatchGradR]

/-- `Σ_t ‖x t‖₂² ≤ B·max_t ‖x t‖₂²`. -/
theorem sum_xMaxSq_le (x : τ → δ → ℝ) :
    (∑ t, ∑ j, x t j ^ 2) ≤ (Fintype.card τ : ℝ) * xMaxSq x := by
  have hle : (∑ t, ∑ j, x t j ^ 2) ≤ ∑ _t, xMaxSq x :=
    Finset.sum_le_sum (fun t _ => Finset.le_sup' (fun t => ∑ j, x t j ^ 2) (Finset.mem_univ t))
  rw [Finset.sum_const, nsmul_eq_mul] at hle
  exact hle

omit [DecidableEq K] [Nonempty K] in
/-- Граница через максимум: `S_batch ≤ B·‖wo‖_F²·max_t ‖x t‖₂²`. -/
theorem S_batch_le_max (wo : ι → K → ℝ) (x : τ → δ → ℝ) :
    S_batch wo x ≤ (Fintype.card τ : ℝ) * (∑ i, ∑ v, wo i v ^ 2) * xMaxSq x := by
  unfold S_batch
  have hF : (0:ℝ) ≤ ∑ i, ∑ v, wo i v ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun v _ => sq_nonneg _))
  nlinarith [sum_xMaxSq_le x, hF]

omit [Nonempty K] [DecidableEq K] [Nonempty τ] in
/-- `w1BatchCE` — тот же объект, что `w1BatchObjR`. -/
theorem w1BatchCE_eq (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ)
    (x : τ → δ → ℝ) (W1 : ι → δ → ℝ) :
    w1BatchCE y b wo x W1 = Hagi.Theory.MuonDescentW1Rect.w1BatchObjR x y b wo W1 := rfl

/-- Сумма квадратов масштабированного направления:
`Σᵢⱼ (c·D i j)² = c²·Σᵢⱼ D i j²`. -/
theorem sum_sq_smul (c : ℝ) (D : ι → δ → ℝ) :
    (∑ i, ∑ j, (c * D i j) ^ 2) = c ^ 2 * ∑ i, ∑ j, D i j ^ 2 := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **`w1BatchCE_descent_lemma`**: гладкость суммы CE по `W1` внутри
области активации КАЖДОГО входа батча с константой
`S_batch = ‖wo‖_F²·Σ_t ‖x t‖₂²` (сумма констант C684; через максимум:
`S_batch ≤ B·‖wo‖_F²·max_t ‖x t‖₂²` — `S_batch_le_max`):
`CE_batch (V1) ≤ CE_batch (W1) − Σᵢⱼ D_batch i j·Δ i j + S_batch/2·‖Δ‖_F²`,
`Δ = V1 − W1`, `D_batch = Σ_t g_t ⊗ x_t`. Вывод: сумма лемм C684
(`w1CE_descent_lemma`) с `S_t ≤ S_batch` (`sum_xMaxSq_le`). -/
theorem w1BatchCE_descent_lemma (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ)
    (x : τ → δ → ℝ) (W1 V1 : ι → δ → ℝ)
    (hsame : ∀ t i, reluMask (w1Pre (x t) V1 i + b i)
      = reluMask (w1Pre (x t) W1 i + b i)) :
    w1BatchCE y b wo x V1 ≤ w1BatchCE y b wo x W1
      - ∑ i, ∑ j, w1BatchDescentDir y b wo x W1 i j * parDiff W1 V1 i j
      + S_batch wo x / 2 * (∑ i, ∑ j, parDiff W1 V1 i j ^ 2) := by
  have hF : (0:ℝ) ≤ ∑ i, ∑ v, wo i v ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun v _ => sq_nonneg _))
  have hΔ : (0:ℝ) ≤ ∑ i, ∑ j, parDiff W1 V1 i j ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hmax := sum_xMaxSq_le x
  -- сумма лемм по t
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) =>
    w1CE_descent_lemma (y t) b wo (x t) W1 V1 (hsame t))
  -- линейная часть: Σ_t Σᵢⱼ g_t i·x t j·Δ i j = Σᵢⱼ D_batch i j·Δ i j
  have hswap : (∑ t, ∑ i, ∑ j, Hagi.Theory.FunctionPreservingGrowth.chainGrad
          (fun v i => reluMask (w1Pre (x t) W1 i + b i) * wo i v)
          (Hagi.Energy.smax (w1L W1 b wo (x t))) (fun v => if v = y t then 1 else 0) i
          * x t j * parDiff W1 V1 i j)
        = ∑ i, ∑ j, ∑ t, Hagi.Theory.FunctionPreservingGrowth.chainGrad
          (fun v i => reluMask (w1Pre (x t) W1 i + b i) * wo i v)
          (Hagi.Energy.smax (w1L W1 b wo (x t))) (fun v => if v = y t then 1 else 0) i
          * x t j * parDiff W1 V1 i j := by
    calc (∑ t, ∑ i, ∑ j, Hagi.Theory.FunctionPreservingGrowth.chainGrad
            (fun v i => reluMask (w1Pre (x t) W1 i + b i) * wo i v)
            (Hagi.Energy.smax (w1L W1 b wo (x t))) (fun v => if v = y t then 1 else 0) i
            * x t j * parDiff W1 V1 i j)
        = ∑ i, ∑ t, ∑ j, Hagi.Theory.FunctionPreservingGrowth.chainGrad
            (fun v i => reluMask (w1Pre (x t) W1 i + b i) * wo i v)
            (Hagi.Energy.smax (w1L W1 b wo (x t))) (fun v => if v = y t then 1 else 0) i
            * x t j * parDiff W1 V1 i j := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have hlin : (∑ i, ∑ j, ∑ t, Hagi.Theory.FunctionPreservingGrowth.chainGrad
          (fun v i => reluMask (w1Pre (x t) W1 i + b i) * wo i v)
          (Hagi.Energy.smax (w1L W1 b wo (x t))) (fun v => if v = y t then 1 else 0) i
          * x t j * parDiff W1 V1 i j)
      = ∑ i, ∑ j, w1BatchDescentDir y b wo x W1 i j * parDiff W1 V1 i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [w1BatchDescentDir, Hagi.Theory.BatchRankOne.batchGrad]
    calc (∑ t, Hagi.Theory.FunctionPreservingGrowth.chainGrad
            (fun v i => reluMask (w1Pre (x t) W1 i + b i) * wo i v)
            (Hagi.Energy.smax (w1L W1 b wo (x t))) (fun v => if v = y t then 1 else 0) i
            * x t j * parDiff W1 V1 i j)
        = ∑ t, parDiff W1 V1 i j *
            (Hagi.Theory.FunctionPreservingGrowth.chainGrad
              (fun v i => reluMask (w1Pre (x t) W1 i + b i) * wo i v)
              (Hagi.Energy.smax (w1L W1 b wo (x t))) (fun v => if v = y t then 1 else 0) i
              * x t j) :=
          Finset.sum_congr rfl fun t _ => by ring
      _ = _ := by rw [mul_comm]; exact (Finset.mul_sum _ _ _).symm
  simp only [w1CE, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [hswap, hlin] at hsum
  -- квадратичная часть: Σ_t S_t/2·‖Δ‖² = S_batch/2·‖Δ‖²
  have hquad : (∑ t, ((∑ i, ∑ v, wo i v ^ 2) * (∑ j, x t j ^ 2)) / 2
        * (∑ i, ∑ j, parDiff W1 V1 i j ^ 2))
      ≤ S_batch wo x / 2 * (∑ i, ∑ j, parDiff W1 V1 i j ^ 2) := by
    have hA : (∑ t, (∑ i, ∑ v, wo i v ^ 2) * ∑ j, x t j ^ 2)
        = (∑ i, ∑ v, wo i v ^ 2) * ∑ t, ∑ j, x t j ^ 2 := (Finset.mul_sum _ _ _).symm
    have hB : (∑ t, ((∑ i, ∑ v, wo i v ^ 2) * (∑ j, x t j ^ 2)) / 2
        * (∑ i, ∑ j, parDiff W1 V1 i j ^ 2))
        = ((∑ t, (∑ i, ∑ v, wo i v ^ 2) * (∑ j, x t j ^ 2)) / 2)
          * (∑ i, ∑ j, parDiff W1 V1 i j ^ 2) := by
      simp only [Finset.sum_mul, Finset.sum_div]
    unfold S_batch
    rw [hB, hA]
  -- сборка
  simp only [w1BatchCE, w1CE]
  linarith

/-- **`w1BatchCE_drop_of_step`**: шаг `W1 + γ•D_batch` внутри области
активации каждого входа батча даёт certified drop
`nlDrop γ S_batch ‖D_batch‖_F`. -/
theorem w1BatchCE_drop_of_step (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ)
    (x : τ → δ → ℝ) (W1 : ι → δ → ℝ) (γ : ℝ)
    (hsame : ∀ t i, reluMask (w1Pre (x t)
        (fun i j => W1 i j + γ * w1BatchDescentDir y b wo x W1 i j) i + b i)
      = reluMask (w1Pre (x t) W1 i + b i)) :
    w1BatchCE y b wo x (fun i j => W1 i j + γ * w1BatchDescentDir y b wo x W1 i j)
      ≤ w1BatchCE y b wo x W1
        - Hagi.Theory.NegativeTransfer.nlDrop γ (S_batch wo x)
          (parNorm (w1BatchDescentDir y b wo x W1)) := by
  have h := w1BatchCE_descent_lemma y b wo x W1
    (fun i j => W1 i j + γ * w1BatchDescentDir y b wo x W1 i j) hsame
  set D := w1BatchDescentDir y b wo x W1 with hD
  have hexp : ∀ i j, parDiff W1 (fun i j => W1 i j + γ * D i j) i j = γ * D i j := by
    intro i j; unfold parDiff; ring
  have hquad : (∑ i, ∑ j, parDiff W1 (fun i j => W1 i j + γ * D i j) i j ^ 2)
      = γ ^ 2 * parNorm D ^ 2 := by
    simp only [hexp, parNorm_sq]
    exact sum_sq_smul γ D
  have hlin : (∑ i, ∑ j, D i j * parDiff W1 (fun i j => W1 i j + γ * D i j) i j)
      = γ * parNorm D ^ 2 := by
    simp only [hexp, parNorm_sq]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hquad, hlin] at h
  unfold Hagi.Theory.NegativeTransfer.nlDrop
  linarith

/-- **`w1BatchCE_optimal_step_drop`**: `S_batch > 0` ⇒ оптимальный шаг
суммы CE по батчу `γ*_batch = 1/S_batch` с drop `‖D_batch‖²/(2S_batch)`;
`S_batch = ‖wo‖_F²·Σ_t ‖x t‖₂²` — явное число. -/
theorem w1BatchCE_optimal_step_drop (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ)
    (x : τ → δ → ℝ) (W1 : ι → δ → ℝ)
    (hS : 0 < S_batch wo x)
    (hsame : ∀ t i, reluMask (w1Pre (x t)
        (fun i j => W1 i j + (1 / S_batch wo x) * w1BatchDescentDir y b wo x W1 i j) i + b i)
      = reluMask (w1Pre (x t) W1 i + b i)) :
    w1BatchCE y b wo x (fun i j => W1 i j
        + (1 / S_batch wo x) * w1BatchDescentDir y b wo x W1 i j)
      ≤ w1BatchCE y b wo x W1
        - parNorm (w1BatchDescentDir y b wo x W1) ^ 2 / (2 * S_batch wo x) := by
  have h := w1BatchCE_drop_of_step y b wo x W1 (1 / S_batch wo x) hsame
  have ho := Hagi.Theory.NegativeTransfer.nl_drop_optimal (S_batch wo x)
    (parNorm (w1BatchDescentDir y b wo x W1)) hS
  rw [ho] at h
  exact h

/-- Квадрат нормы масштабированного направления:
`parNorm (c • D) ^ 2 = c²·parNorm D ^ 2`. -/
theorem parNorm_sq_smul (c : ℝ) (D : ι → δ → ℝ) :
    parNorm (c • D) ^ 2 = c ^ 2 * parNorm D ^ 2 := by
  rw [parNorm_sq, parNorm_sq]
  exact sum_sq_smul c D

/-- **`w1MeanCE_optimal_step_drop`**: форма кода — mean CE по батчу
(`ce(reduction="mean")`, lm.py:299 @ca52eb4), `B = |τ| > 0`, шаг
`W1 + γ•(D_batch/B)` с направлением `D_mean = (1/B)·D_batch`:
`S_mean = S_batch/B`, оптимальный шаг `γ* = B/S_batch`, drop
`‖D_mean‖²/(2·S_batch/B)`. Скалярная выкладка из
`w1BatchCE_optimal_step_drop`. -/
theorem w1MeanCE_optimal_step_drop (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ)
    (x : τ → δ → ℝ) (W1 : ι → δ → ℝ)
    (hB : (0 : ℝ) < Fintype.card τ) (hS : 0 < S_batch wo x)
    (hsame : ∀ t i, reluMask (w1Pre (x t)
        (fun i j => W1 i j + (1 / S_batch wo x) * w1BatchDescentDir y b wo x W1 i j) i + b i)
      = reluMask (w1Pre (x t) W1 i + b i)) :
    w1BatchCE y b wo x (fun i j => W1 i j
        + ((Fintype.card τ : ℝ) / S_batch wo x)
          * ((1 / (Fintype.card τ : ℝ)) * w1BatchDescentDir y b wo x W1 i j)) / Fintype.card τ
      ≤ w1BatchCE y b wo x W1 / Fintype.card τ
        - parNorm (fun i j => (1 / (Fintype.card τ : ℝ))
            * w1BatchDescentDir y b wo x W1 i j) ^ 2
          / (2 * (S_batch wo x / Fintype.card τ)) := by
  set B := (Fintype.card τ : ℝ) with hBdef
  set S := S_batch wo x with hSdef
  set D := w1BatchDescentDir y b wo x W1 with hDdef
  have hB0 : B ≠ 0 := ne_of_gt hB
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hstep : (fun i j => W1 i j + (B / S) * ((1 / B) * D i j))
      = fun i j => W1 i j + (1 / S) * D i j := by
    funext i j
    field_simp
  have h := w1BatchCE_optimal_step_drop y b wo x W1 hS (by
    intro t i; exact hsame t i)
  have h' : w1BatchCE y b wo x (fun i j => W1 i j + (B / S) * ((1 / B) * D i j))
      ≤ w1BatchCE y b wo x W1 - parNorm D ^ 2 / (2 * S) := by
    rw [hstep]; exact h
  have hnorm : parNorm (fun i j => (1 / B) * D i j) ^ 2 = (1 / B) ^ 2 * parNorm D ^ 2 := by
    rw [parNorm_sq, parNorm_sq]
    exact sum_sq_smul (1 / B) D
  have hid : (1 / B) ^ 2 * parNorm D ^ 2 / (2 * (S / B))
      = (parNorm D ^ 2 / (2 * S)) / B := by
    field_simp
  have h2 : B * (w1BatchCE y b wo x W1 / B - (parNorm D ^ 2 / (2 * S)) / B)
      = w1BatchCE y b wo x W1 - parNorm D ^ 2 / (2 * S) := by
    field_simp
  rw [hnorm, hid]
  exact (div_le_iff₀ hB).2 (by linarith)

end Hagi.Theory.FirstLayerLipBatch
