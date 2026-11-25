/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.FirstLayerGrad
import Hagi.Model.CEGlobalConvergence
import Hagi.Theory.NegativeTransfer

/-!
# FirstLayerLip — вычислимая константа `L` для CE relu-блока по `W1`

C684. Закрывает главный honest-gap `docs/DERIVED-CONFIG.md` («Adam lr:
`L` не измеряется»). Носитель — слой `W1 : ι → δ → ℝ` из
`Hagi.Theory.FirstLayerGrad` (`w1Pre`, `w1L`); цель одного входа
`w1CE W1 = ceOneHot t (w1L W1 b wo x)`. Норма параметра —
`parNorm W1 = √(Σᵢⱼ W1 i j²)` (Frobenius функционального носителя).

Две РАЗНЫЕ константы, которые код и теория до C684 смешивали:

* `w1CE_lipschitz_param` — липшицевость ФУНКЦИИ по параметру
  (глобально, через kink): `Lfun = 2·‖wo‖_F·‖x‖₂`
  (`C_CE = 2` — `headCE_abs_sub_le_of_l2`).
  Из липшицевости функции спуск НЕ следует (нужна гладкость).
* `w1CE_descent_lemma` — ГЛАДКОСТЬ (липшицевость градиента) по
  параметру ВНУТРИ области активации (маска `reluMask` не меняется):
  `S = ‖wo‖_F²·‖x‖₂²` (та же цепочка, что у Lfun, но с
  квадратом, потому что слагаемое второй порядок: логиты линейны по
  `Δ` в области, а `lse_descent` (`Hagi.Model.CEGlobalConvergence`)
  даёт гессиан CE по логитам `⪯ I`.
  Релу-блок глобально НЕ гладкий (kink), поэтому глобальной
  гладкости по `W1` нет — это не дефект доказательства.
* `w1CE_drop_of_step`, `w1CE_optimal_step_drop` — спуск по
  rank-one направлению `D = g ⊗ x` (`w1DescentDir`, конвенция
  `chainGrad`: `⟨∇CE, Δ⟩ = −Σ (gᵢxⱼ)Δᵢⱼ`, шаг `W1 + γ•D`) в форме
  `nlDrop` и оптимальный шаг `γ* = 1/S` с drop `‖D‖²/(2S)`:
  `S` — ЯВНОЕ число из весов слоя и входа (внутри области
  активации шага). -/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.FirstLayerLip

open scoped BigOperators
open Hagi.Theory.FunctionPreservingGrowth
open Hagi.Theory.FirstLayerGrad

variable {ι δ K : Type} [Fintype ι] [Fintype δ] [Fintype K]

/-- Норма параметра `W1 : ι → δ → ℝ` (Frobenius функционального
носителя): `parNorm W1 = √(Σᵢⱼ W1 i j²)`. -/
noncomputable def parNorm (W1 : ι → δ → ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, W1 i j ^ 2)

/-- Цель одного входа по матрице `W1`: `w1CE W1 = CE_t (w1L W1 b wo x)`. -/
noncomputable def w1CE (t : K) (b : ι → ℝ) (wo : ι → K → ℝ) (x : δ → ℝ)
    (W1 : ι → δ → ℝ) : ℝ :=
  Hagi.ceOneHot t (w1L W1 b wo x)

/-- Возмущение параметра `V1 − W1` как функция `(i, j)`. -/
noncomputable def parDiff (W1 V1 : ι → δ → ℝ) : ι → δ → ℝ :=
  fun i j => V1 i j - W1 i j

/-- Квадрат нормы возмущения: `Σᵢⱼ (V1 − W1) i j²`. -/
theorem parNorm_sq_parDiff (W1 V1 : ι → δ → ℝ) :
    parNorm (parDiff W1 V1) ^ 2 = ∑ i, ∑ j, (V1 i j - W1 i j) ^ 2 := by
  unfold parNorm parDiff
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))

/-- Квадрат нормы параметра: `parNorm f ^ 2 = Σᵢⱼ f i j²`. -/
theorem parNorm_sq (f : ι → δ → ℝ) :
    parNorm f ^ 2 = ∑ i, ∑ j, f i j ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))

/-- Строчная Коши–Шварц: `Σᵢ (Δᵢ · x)² ≤ ‖Δ‖_F²·‖x‖₂²`. -/
theorem row_sq_le (Δ : ι → δ → ℝ) (x : δ → ℝ) :
    (∑ i, (∑ j, Δ i j * x j) ^ 2)
      ≤ (∑ i, ∑ j, Δ i j ^ 2) * (∑ j, x j ^ 2) := by
  have hrow : ∀ i : ι, (∑ j, Δ i j * x j) ^ 2
      ≤ (∑ j, Δ i j ^ 2) * ∑ j, x j ^ 2 :=
    fun i => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => Δ i j) (fun j => x j)
  calc (∑ i, (∑ j, Δ i j * x j) ^ 2)
      ≤ ∑ i, (∑ j, Δ i j ^ 2) * ∑ j, x j ^ 2 :=
        Finset.sum_le_sum (fun i _ => hrow i)
    _ = (∑ i, ∑ j, Δ i j ^ 2) * (∑ j, x j ^ 2) := (Finset.sum_mul _ _ _).symm

/-- Столбцовая Коши–Шварц для карты «нейрон → класс»: для любых
`f : ι → K → ℝ` и `u : ι → ℝ`
`Σ_v (Σᵢ f i v·u i)² ≤ (Σᵢᵥ f i v²)·(Σᵢ u i²)`. -/
theorem sum_mul_sq_le (f : ι → K → ℝ) (u : ι → ℝ) :
    (∑ v, (∑ i, f i v * u i) ^ 2)
      ≤ (∑ i, ∑ v, f i v ^ 2) * (∑ i, u i ^ 2) := by
  have hcol : ∀ v : K, (∑ i, f i v * u i) ^ 2
      ≤ (∑ i, f i v ^ 2) * ∑ i, u i ^ 2 :=
    fun v => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => f i v) (fun i => u i)
  have hswap : (∑ v, (∑ i, f i v ^ 2) * ∑ i, u i ^ 2)
      = (∑ i, ∑ v, f i v ^ 2) * (∑ i, u i ^ 2) := by
    calc (∑ v, (∑ i, f i v ^ 2) * ∑ i, u i ^ 2)
        = (∑ v, ∑ i, f i v ^ 2) * ∑ i, u i ^ 2 := (Finset.sum_mul _ _ _).symm
      _ = (∑ i, ∑ v, f i v ^ 2) * ∑ i, u i ^ 2 := by rw [Finset.sum_comm]
  calc (∑ v, (∑ i, f i v * u i) ^ 2)
      ≤ ∑ v, (∑ i, f i v ^ 2) * ∑ i, u i ^ 2 :=
        Finset.sum_le_sum (fun v _ => hcol v)
    _ = (∑ i, ∑ v, f i v ^ 2) * (∑ i, u i ^ 2) := hswap

/-- Квадрат ℓ₂-разности логитов ограничен тремя множителями:
`Σ_v (w1L W1 − w1L V1) v² ≤ ‖wo‖_F²·‖W1 − V1‖_F²·‖x‖₂²` (глобально:
relu 1-Липшиц по координате — `relu_lip_abs`). -/
theorem w1Logits_sq_le (b : ι → ℝ) (wo : ι → K → ℝ) (x : δ → ℝ)
    (W1 V1 : ι → δ → ℝ) :
    (∑ v, (w1L W1 b wo x v - w1L V1 b wo x v) ^ 2)
      ≤ (∑ i, ∑ v, wo i v ^ 2)
        * ((∑ i, ∑ j, (V1 i j - W1 i j) ^ 2) * (∑ j, x j ^ 2)) := by
  -- разность логитов = Σᵢ uᵢ·wo i v, u = relu-разности pre-активаций
  have hdiff : ∀ v, w1L W1 b wo x v - w1L V1 b wo x v
      = ∑ i, (Hagi.Theory.BlockLipschitz.relu (w1Pre x W1 i + b i)
        - Hagi.Theory.BlockLipschitz.relu (w1Pre x V1 i + b i)) * wo i v := by
    intro v
    simp only [w1L, reluL]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hstep := sum_mul_sq_le wo (fun i =>
    Hagi.Theory.BlockLipschitz.relu (w1Pre x W1 i + b i)
      - Hagi.Theory.BlockLipschitz.relu (w1Pre x V1 i + b i))
  -- |uᵢ| ≤ |Δᵀx|ᵢ (relu 1-Липшиц) ⇒ Σ uᵢ² ≤ Σ (Δᵀx)ᵢ²
  have hpre : ∀ i, w1Pre x V1 i - w1Pre x W1 i
      = ∑ j, parDiff W1 V1 i j * x j := by
    intro i
    simp only [w1Pre, parDiff, sub_mul, Finset.sum_sub_distrib]
  have hrelu : ∀ i, (Hagi.Theory.BlockLipschitz.relu (w1Pre x W1 i + b i)
        - Hagi.Theory.BlockLipschitz.relu (w1Pre x V1 i + b i)) ^ 2
      ≤ (∑ j, parDiff W1 V1 i j * x j) ^ 2 := by
    intro i
    have h1 := Hagi.Theory.BlockLipschitz.relu_lip_abs
      (w1Pre x W1 i + b i) (w1Pre x V1 i + b i)
    have h2 : w1Pre x W1 i + b i - (w1Pre x V1 i + b i)
        = -∑ j, parDiff W1 V1 i j * x j := by rw [← hpre i]; ring
    rw [h2, abs_neg] at h1
    have h4 : |Hagi.Theory.BlockLipschitz.relu (w1Pre x W1 i + b i)
        - Hagi.Theory.BlockLipschitz.relu (w1Pre x V1 i + b i)| ^ 2
        ≤ |∑ j, parDiff W1 V1 i j * x j| ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 h1
    rwa [sq_abs, sq_abs] at h4

  have hcs := row_sq_le (parDiff W1 V1) x
  have hsum : (∑ i, (Hagi.Theory.BlockLipschitz.relu (w1Pre x W1 i + b i)
        - Hagi.Theory.BlockLipschitz.relu (w1Pre x V1 i + b i)) ^ 2)
      ≤ (∑ i, ∑ j, parDiff W1 V1 i j ^ 2) * (∑ j, x j ^ 2) :=
    le_trans (Finset.sum_le_sum (fun i _ => hrelu i)) hcs
  have hF : (0:ℝ) ≤ ∑ i, ∑ v, wo i v ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun v _ => sq_nonneg _))
  have hstep2 : (∑ v, (w1L W1 b wo x v - w1L V1 b wo x v) ^ 2)
      ≤ (∑ i, ∑ v, wo i v ^ 2)
        * ((∑ i, ∑ j, parDiff W1 V1 i j ^ 2) * (∑ j, x j ^ 2)) := by
    have hrewrite : (∑ v, (w1L W1 b wo x v - w1L V1 b wo x v) ^ 2)
        = ∑ v, (∑ i, (Hagi.Theory.BlockLipschitz.relu (w1Pre x W1 i + b i)
            - Hagi.Theory.BlockLipschitz.relu (w1Pre x V1 i + b i)) * wo i v) ^ 2 :=
      Finset.sum_congr rfl (fun v _ => by rw [hdiff v])
    rw [hrewrite]
    calc (∑ v, (∑ i, (Hagi.Theory.BlockLipschitz.relu (w1Pre x W1 i + b i)
          - Hagi.Theory.BlockLipschitz.relu (w1Pre x V1 i + b i)) * wo i v) ^ 2)
        ≤ (∑ i, ∑ v, wo i v ^ 2)
            * (∑ i, (Hagi.Theory.BlockLipschitz.relu (w1Pre x W1 i + b i)
              - Hagi.Theory.BlockLipschitz.relu (w1Pre x V1 i + b i)) ^ 2) := by
          simpa only [mul_comm] using hstep
      _ ≤ (∑ i, ∑ v, wo i v ^ 2)
          * ((∑ i, ∑ j, parDiff W1 V1 i j ^ 2) * (∑ j, x j ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum hF
  have hsq : (∑ i, ∑ j, parDiff W1 V1 i j ^ 2)
      = ∑ i, ∑ j, (V1 i j - W1 i j) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => rfl))
  rw [hsq] at hstep2
  exact hstep2

/-- **`w1CE_lipschitz_param`**: CE relu-блока липшицева по матрице
`W1` ГЛОБАЛЬНО (через kink) с вычислимой константой
`Lfun = 2·‖wo‖_F·‖x‖₂`: `|w1CE W1 − w1CE V1| ≤ Lfun·‖W1 − V1‖_F`.
Это липшицевость ФУНКЦИИ (уровень «C-Cauchy»): спуск из неё не
следует; для `γ* = 1/L` нужна гладкость `S` (`w1CE_descent_lemma`). -/
theorem w1CE_lipschitz_param (t : K) (b : ι → ℝ) (wo : ι → K → ℝ) (x : δ → ℝ)
    (W1 V1 : ι → δ → ℝ) [Nonempty K] :
    |w1CE t b wo x W1 - w1CE t b wo x V1|
      ≤ 2 * Real.sqrt (∑ i, ∑ v, wo i v ^ 2) * parNorm (parDiff W1 V1)
        * Real.sqrt (∑ j, x j ^ 2) := by
  have hlog := w1Logits_sq_le b wo x W1 V1
  have hce := Hagi.Theory.BlockSmooth.headCE_abs_sub_le_of_l2 t
    (w1L W1 b wo x) (w1L V1 b wo x)
  rw [Hagi.Model.SoftmaxHead.headCE_ident, Hagi.Model.SoftmaxHead.headCE_ident] at hce
  have hsqrt : Real.sqrt (∑ v, (w1L W1 b wo x v - w1L V1 b wo x v) ^ 2)
      ≤ Real.sqrt (∑ i, ∑ v, wo i v ^ 2)
        * (parNorm (parDiff W1 V1) * Real.sqrt (∑ j, x j ^ 2)) := by
    have h := Real.sqrt_le_sqrt hlog
    rw [Real.sqrt_mul (Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun v _ => sq_nonneg _))),
      Real.sqrt_mul (Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => sq_nonneg _)))] at h
    have hpow : Real.sqrt (∑ i, ∑ j, (V1 i j - W1 i j) ^ 2)
        = parNorm (parDiff W1 V1) := by
      unfold parNorm parDiff
      rfl
    rw [hpow] at h
    exact h
  change |Hagi.ceOneHot t (w1L W1 b wo x) - Hagi.ceOneHot t (w1L V1 b wo x)| ≤ _
  calc |Hagi.ceOneHot t (w1L W1 b wo x) - Hagi.ceOneHot t (w1L V1 b wo x)|
      ≤ 2 * Real.sqrt (∑ v, (w1L W1 b wo x v - w1L V1 b wo x v) ^ 2) := hce
    _ ≤ 2 * (Real.sqrt (∑ i, ∑ v, wo i v ^ 2)
        * (parNorm (parDiff W1 V1) * Real.sqrt (∑ j, x j ^ 2))) :=
        mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ = 2 * Real.sqrt (∑ i, ∑ v, wo i v ^ 2) * parNorm (parDiff W1 V1)
        * Real.sqrt (∑ j, x j ^ 2) := by ring

omit [Fintype K] in
/-- Смещение логитов возмущением `Δ = V1 − W1` — линейно по `Δ` внутри
области активации: если маска каждого нейрона в `V1` совпадает с маской
в `W1`, то `w1L V1 v = w1L W1 v + w1Jac Δ v`. -/
theorem w1L_eq_add_jac_of_mask_eq (b : ι → ℝ) (wo : ι → K → ℝ) (x : δ → ℝ)
    (W1 V1 : ι → δ → ℝ)
    (hsame : ∀ i, reluMask (w1Pre x V1 i + b i) = reluMask (w1Pre x W1 i + b i))
    (v : K) :
    w1L V1 b wo x v = w1L W1 b wo x v + w1Jac x b wo W1 (parDiff W1 V1) v := by
  have hpre : ∀ i, w1Pre x V1 i = w1Pre x W1 i + ∑ j, parDiff W1 V1 i j * x j := by
    intro i
    simp only [w1Pre, parDiff, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [w1Jac_apply]
  simp only [w1L, reluL]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hstep : ∀ a c : ℝ, reluMask (a + c) = reluMask a →
      Hagi.Theory.BlockLipschitz.relu (a + c)
        = Hagi.Theory.BlockLipschitz.relu a + reluMask a * c := by
    intro a c h
    unfold Hagi.Theory.BlockLipschitz.relu reluMask at h ⊢
    split_ifs at h ⊢ <;> linarith
  have hsame' : ∀ i, reluMask (w1Pre x W1 i + b i + ∑ j, parDiff W1 V1 i j * x j)
      = reluMask (w1Pre x W1 i + b i) := by
    intro i
    have h5 : w1Pre x W1 i + b i + ∑ j, parDiff W1 V1 i j * x j
        = w1Pre x V1 i + b i := by rw [hpre i]; ring
    rw [h5]
    exact hsame i
  have h := hstep (w1Pre x W1 i + b i) (∑ j, parDiff W1 V1 i j * x j) (hsame' i)
  have h5 : w1Pre x W1 i + ∑ j, parDiff W1 V1 i j * x j + b i
      = w1Pre x W1 i + b i + ∑ j, parDiff W1 V1 i j * x j := by ring
  rw [hpre, h5, h]
  ring

/-- **`w1CE_descent_lemma`**: гладкость CE по `W1` ВНУТРИ области
активации с константой `S = ‖wo‖_F²·‖x‖₂²`:
`CE (V1) ≤ CE (W1) − Σᵢⱼ (gᵢ·xⱼ)·(V1 − W1)ᵢⱼ + S/2·‖V1 − W1‖_F²`,
где `gᵢ = Σ_v (y_v − p_v)·maskᵢ·wo i v` — rank-one градиент
(`w1_grad_rank_one`). Множитель `1` гессиана CE по логитам —
`lse_descent`; к квадрату константы ведёт цепочка Коши–Шварца
(`sum_mul_sq_le`, `row_sq_le`). Глобальной гладкости нет: relu-блок
имеет kink. -/
theorem w1CE_descent_lemma (t : K) (b : ι → ℝ) (wo : ι → K → ℝ) (x : δ → ℝ)
    (W1 V1 : ι → δ → ℝ) [Nonempty K] [DecidableEq K]
    (hsame : ∀ i, reluMask (w1Pre x V1 i + b i) = reluMask (w1Pre x W1 i + b i)) :
    w1CE t b wo x V1 ≤ w1CE t b wo x W1
      - (∑ i, ∑ j, (Hagi.Theory.FunctionPreservingGrowth.chainGrad
          (fun v i => reluMask (w1Pre x W1 i + b i) * wo i v)
          (Hagi.Energy.smax (w1L W1 b wo x)) (fun v => if v = t then 1 else 0) i * x j)
          * parDiff W1 V1 i j)
      + ((∑ i, ∑ v, wo i v ^ 2) * (∑ j, x j ^ 2)) / 2
        * (∑ i, ∑ j, parDiff W1 V1 i j ^ 2) := by
  set p := Hagi.Energy.smax (w1L W1 b wo x) with hp
  set y : K → ℝ := fun v => if v = t then 1 else 0 with hy
  set d : K → ℝ := fun v => w1L V1 b wo x v - w1L W1 b wo x v with hd
  -- (1) descent lemma для lse по логитам: lse (z + d) ≤ lse z + ⟨p, d⟩ + ‖d‖²/2
  have hadd : w1L W1 b wo x + d = w1L V1 b wo x := by funext v; simp [hd]
  have hlsed := Hagi.Model.CEGlobalConvergence.lse_descent (w1L W1 b wo x) d
  rw [hadd] at hlsed
  -- (2) линейность логитов в области активации: d = J·Δ
  have hjac : ∀ v, d v = w1Jac x b wo W1 (parDiff W1 V1) v := by
    intro v
    have h1 : w1L V1 b wo x v = w1L W1 b wo x v + w1Jac x b wo W1 (parDiff W1 V1) v :=
      w1L_eq_add_jac_of_mask_eq b wo x W1 V1 hsame v
    show (fun v => w1L V1 b wo x v - w1L W1 b wo x v) v = _
    simp only []
    rw [h1]
    ring
  -- (3) pairing = −Σ gᵢxⱼΔᵢⱼ
  have hdd := w1_directional_derivative x b wo W1 (parDiff W1 V1) p y
  have hdd2 : (∑ v, (p v - y v) * d v)
      = -∑ i, ∑ j, Hagi.Theory.FunctionPreservingGrowth.chainGrad
          (fun v i => reluMask (w1Pre x W1 i + b i) * wo i v) p y i * x j * parDiff W1 V1 i j := by
    have h1 : (∑ v, (p v - y v) * d v)
        = ∑ v, (p v - y v) * w1Jac x b wo W1 (parDiff W1 V1) v :=
      Finset.sum_congr rfl (fun v _ => by rw [hjac v])
    rw [h1]
    exact hdd
  -- pairing softmax минус one-hot
  have hpair : (∑ v, Hagi.Prelude.softDef (w1L W1 b wo x) v * d v) - d t
      = ∑ v, (p v - y v) * d v := by
    have hty : ∑ v, (if v = t then 1 else 0) * d v = d t := by simp
    simp only [show Hagi.Prelude.softDef (w1L W1 b wo x) = p from rfl, hy,
      sub_mul, Finset.sum_sub_distrib, hty]
  -- (4) квадратичная часть: ‖d‖² ≤ S·‖Δ‖²
  have hlog := w1Logits_sq_le b wo x W1 V1
  have hnorm : (∑ i, ∑ j, (V1 i j - W1 i j) ^ 2) = ∑ i, ∑ j, parDiff W1 V1 i j ^ 2 :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => rfl))
  rw [hnorm] at hlog
  have hsum : (∑ v, d v * d v) / 2
      ≤ ((∑ i, ∑ v, wo i v ^ 2) * (∑ j, x j ^ 2)) / 2
        * (∑ i, ∑ j, parDiff W1 V1 i j ^ 2) := by
    have hsq : (∑ v, d v * d v) = ∑ v, (w1L W1 b wo x v - w1L V1 b wo x v) ^ 2 :=
      Finset.sum_congr rfl (fun v _ => by rw [hd]; ring)
    have hnn : (0:ℝ) ≤ ∑ v, (w1L W1 b wo x v - w1L V1 b wo x v) ^ 2 :=
      Finset.sum_nonneg (fun v _ => sq_nonneg _)
    calc (∑ v, d v * d v) / 2 = (∑ v, (w1L W1 b wo x v - w1L V1 b wo x v) ^ 2) / 2 := by rw [hsq]
      _ ≤ ((∑ i, ∑ v, wo i v ^ 2) * ((∑ i, ∑ j, parDiff W1 V1 i j ^ 2) * (∑ j, x j ^ 2))) / 2 :=
        div_le_div_of_nonneg_right hlog (by norm_num)
      _ = ((∑ i, ∑ v, wo i v ^ 2) * (∑ j, x j ^ 2)) / 2
          * (∑ i, ∑ j, parDiff W1 V1 i j ^ 2) := by ring
  -- сборка
  have hdt : d t = w1L V1 b wo x t - w1L W1 b wo x t := congrFun hd t
  have hce : Hagi.lse (w1L V1 b wo x) - w1L V1 b wo x t = w1CE t b wo x V1 := rfl
  have hce0 : Hagi.lse (w1L W1 b wo x) - w1L W1 b wo x t = w1CE t b wo x W1 := rfl
  rw [← hce, ← hce0]
  linarith [hdd2]

/-- Направление спуска CE по `W1` (минус градиент, конвенция
`chainGrad`/`useful_of_adam_first`): `D (i, j) = gᵢ·xⱼ` с
`gᵢ = Σ_v (y_v − p_v)·maskᵢ·wo i v` — rank-one (`w1_grad_rank_one`);
`⟨∇CE, Δ⟩ = −Σᵢⱼ (gᵢxⱼ)·Δᵢⱼ` (`w1_directional_derivative`), поэтому шаг
спуска — `W1 + γ•D`. -/
noncomputable def w1DescentDir (t : K) (b : ι → ℝ) (wo : ι → K → ℝ) (x : δ → ℝ)
    (W1 : ι → δ → ℝ) [DecidableEq K] : ι → δ → ℝ :=
  fun i j => Hagi.Theory.FunctionPreservingGrowth.chainGrad
    (fun v i => reluMask (w1Pre x W1 i + b i) * wo i v)
    (Hagi.Energy.smax (w1L W1 b wo x)) (fun v => if v = t then 1 else 0) i * x j

/-- **`w1CE_drop_of_step`**: шаг `W1' = W1 + γ•D` по направлению спуска
`D` (rank-one, `w1DescentDir`) внутри области активации даёт certified drop
`nlDrop γ S ‖D‖_F` с `S = ‖wo‖_F²·‖x‖₂²` — посылка `nlDrop_le_optimal`
выполнена, `γ* = 1/S`. -/
theorem w1CE_drop_of_step (t : K) (b : ι → ℝ) (wo : ι → K → ℝ) (x : δ → ℝ)
    (W1 : ι → δ → ℝ) (γ : ℝ) [Nonempty K] [DecidableEq K]
    (hsame : ∀ i, reluMask (w1Pre x (fun i j => W1 i j + γ * w1DescentDir t b wo x W1 i j) i + b i)
      = reluMask (w1Pre x W1 i + b i)) :
    w1CE t b wo x (fun i j => W1 i j + γ * w1DescentDir t b wo x W1 i j)
      ≤ w1CE t b wo x W1
        - Hagi.Theory.NegativeTransfer.nlDrop γ ((∑ i, ∑ v, wo i v ^ 2) * (∑ j, x j ^ 2))
          (parNorm (w1DescentDir t b wo x W1)) := by
  have h := w1CE_descent_lemma t b wo x W1
    (fun i j => W1 i j + γ * w1DescentDir t b wo x W1 i j) hsame
  have hexp : ∀ i j, parDiff W1 (fun i j => W1 i j + γ * w1DescentDir t b wo x W1 i j) i j
      = γ * w1DescentDir t b wo x W1 i j := by
    intro i j; unfold parDiff; ring
  -- квадратичная часть: ‖Δ‖² = γ²‖D‖²
  have hquad : (∑ i, ∑ j, parDiff W1 (fun i j => W1 i j + γ * w1DescentDir t b wo x W1 i j) i j ^ 2)
      = γ ^ 2 * parNorm (w1DescentDir t b wo x W1) ^ 2 := by
    have h2 : ∑ i, ∑ j, (γ * w1DescentDir t b wo x W1 i j) ^ 2
        = γ ^ 2 * parNorm (w1DescentDir t b wo x W1) ^ 2 := by
      rw [parNorm_sq]
      simp only [mul_pow]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ _).symm)
    simp only [hexp, sq]
    have h3 : (∑ i, ∑ j, γ * w1DescentDir t b wo x W1 i j * (γ * w1DescentDir t b wo x W1 i j))
        = ∑ i, ∑ j, (γ * w1DescentDir t b wo x W1 i j) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    rw [h3, h2]
    ring
  -- линейная часть: −Σ (gᵢxⱼ)·Δᵢⱼ = −γ‖D‖²
  have hlin : (∑ i, ∑ j, (Hagi.Theory.FunctionPreservingGrowth.chainGrad
        (fun v i => reluMask (w1Pre x W1 i + b i) * wo i v)
        (Hagi.Energy.smax (w1L W1 b wo x)) (fun v => if v = t then 1 else 0) i * x j)
        * parDiff W1 (fun i j => W1 i j + γ * w1DescentDir t b wo x W1 i j) i j)
      = γ * parNorm (w1DescentDir t b wo x W1) ^ 2 := by
    have h2 : ∀ i j, (Hagi.Theory.FunctionPreservingGrowth.chainGrad
          (fun v i => reluMask (w1Pre x W1 i + b i) * wo i v)
          (Hagi.Energy.smax (w1L W1 b wo x)) (fun v => if v = t then 1 else 0) i * x j)
          * parDiff W1 (fun i j => W1 i j + γ * w1DescentDir t b wo x W1 i j) i j
        = γ * (w1DescentDir t b wo x W1 i j * w1DescentDir t b wo x W1 i j) := by
      intro i j
      rw [hexp]
      unfold w1DescentDir
      ring
    rw [parNorm_sq]
    simp only [h2, Finset.mul_sum]
    ring
  rw [hquad, hlin] at h
  unfold Hagi.Theory.NegativeTransfer.nlDrop
  linarith

/-- **`w1CE_optimal_step_drop`**: при оптимальном шаге `γ* = 1/S`,
`S = ‖wo‖_F²·‖x‖₂² > 0`, certified drop равен `‖D‖²/(2S)` —
`nl_drop_optimal`; `S` вычисляется из весов слоя и входа. -/
theorem w1CE_optimal_step_drop (t : K) (b : ι → ℝ) (wo : ι → K → ℝ) (x : δ → ℝ)
    (W1 : ι → δ → ℝ) [Nonempty K] [DecidableEq K]
    (hS : 0 < (∑ i, ∑ v, wo i v ^ 2) * (∑ j, x j ^ 2))
    (hsame : ∀ i, reluMask (w1Pre x (fun i j => W1 i j
        + (1 / ((∑ i, ∑ v, wo i v ^ 2) * (∑ j, x j ^ 2))) * w1DescentDir t b wo x W1 i j) i + b i)
      = reluMask (w1Pre x W1 i + b i)) :
    w1CE t b wo x (fun i j => W1 i j
        + (1 / ((∑ i, ∑ v, wo i v ^ 2) * (∑ j, x j ^ 2))) * w1DescentDir t b wo x W1 i j)
      ≤ w1CE t b wo x W1
        - parNorm (w1DescentDir t b wo x W1) ^ 2
          / (2 * ((∑ i, ∑ v, wo i v ^ 2) * (∑ j, x j ^ 2))) := by
  have h := w1CE_drop_of_step t b wo x W1
    (1 / ((∑ i, ∑ v, wo i v ^ 2) * (∑ j, x j ^ 2))) hsame
  have ho := Hagi.Theory.NegativeTransfer.nl_drop_optimal
    ((∑ i, ∑ v, wo i v ^ 2) * (∑ j, x j ^ 2)) (parNorm (w1DescentDir t b wo x W1)) hS
  rw [ho] at h
  exact h

end Hagi.Theory.FirstLayerLip
