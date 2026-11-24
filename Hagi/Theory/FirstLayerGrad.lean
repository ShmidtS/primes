/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.FunctionPreservingGrowth

/-!
# FirstLayerGrad — производная по первому слою `W1` relu-блока

C668. Закрывает honest-пин F3 карты `FunctionPreservingGrowth`
(«производная по W1 не формализована»). Код: блок роста
`h = h + relu(a @ W1 + b1) @ Wo` (hagi/lm.py:586 @ca52eb4;
`W1 : dim × hidden` — lm.py:594 @ca52eb4). Слой `W1` здесь —
матрица `W1 : ι → δ → ℝ` (строка `i`, столбец `j`); для одного
входа `x : δ → ℝ` pre-активация `w i = Σ_j W1 i j * x j`, логиты
`w1L W1 b wo x = reluL w b wo` (`reluL` из FunctionPreservingGrowth).

* `w1Pre`, `w1L`, `w1Jac` — носитель: логиты как функция матрицы
  `W1`; якобиан `w1Jac x b wo Δ v = Σ_i mask i·(Δᵀx) i·wo i v`.
* `hasFDerivAt_w1L` — вне kink `W1 ↦ logits` дифференцируема:
  `W1 ↦ W1ᵀx` линейна (`preLin`), relu-слой — `hasFDerivAt_reluL`,
  chain rule `HasFDerivAt.scomp`.
* `w1_grad_rank_one` — градиент по `W1` имеет RANK-ONE структуру:
  `g (i, j) = gᵢ · xⱼ`, где `g i = Σ_v (y v − p v)·mask i·wo i v`
  — это `(W2ᵀ r)` строки, помноженный на вход.
* `w1_directional_derivative` — pairing: `⟨p − y, J·Δ⟩
  = −Σ_{ij} (g i · x j)·Δ i j` (Frobenius-скалярное произведение
  градиента с возмущением).
* `useful_of_adam_first_w1` — T5: Adam-first по матрице `W1`
  ⇒ строгое убывание CE для малого η (certified-величина drop
  не выводится — как для b1, honest).
* `w1_rank_one_step_eq_bias` — rank-one обновление `ΔW1 = c • (u ⊗ x)`
  эквивалентно сдвигу bias на `c·‖x‖² • u`: первый слой вдоль
  входа — тот же b1-слой. -/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.FirstLayerGrad

open scoped BigOperators
open Topology
open Hagi.Theory.FunctionPreservingGrowth
open Hagi.Step (adamDot adamDir)

variable {ι δ K : Type} [Fintype ι] [Fintype δ] [Fintype K]

/-- Pre-активация строки `i`: `w i = Σ_j W1 i j * x j` (`a @ W1`). -/
noncomputable def w1Pre (x : δ → ℝ) (W1 : ι → δ → ℝ) : ι → ℝ :=
  fun i => ∑ j, W1 i j * x j

/-- Логиты relu-блока как функция МАТРИЦЫ `W1` (один вход `x`):
`w1L W1 b wo x = reluL (W1ᵀx) b wo`. -/
noncomputable def w1L (W1 : ι → δ → ℝ) (b : ι → ℝ) (wo : ι → K → ℝ)
    (x : δ → ℝ) : K → ℝ :=
  reluL (w1Pre x W1) b wo

/-- `W1 ↦ W1ᵀx` линейно и непрерывно (finite types). -/
noncomputable def w1PreCLM (x : δ → ℝ) : (ι → δ → ℝ) →L[ℝ] (ι → ℝ) where
  toFun W1 := w1Pre x W1
  map_add' _ _ := by
    funext i; simp only [Pi.add_apply, w1Pre, add_mul, Finset.sum_add_distrib]
  map_smul' r _ := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul, w1Pre, Finset.mul_sum, mul_assoc,
      RingHom.id_apply]
  cont := by
    unfold w1Pre
    fun_prop

/-- Якобиан по `W1`: `(w1Jac x b wo Δ) v = Σ_i mask i·(Δᵀx) i·wo i v`
— производная `reluL` по `b` (`reluJac`), применённая к `Δᵀx`. -/
noncomputable def w1Jac (x : δ → ℝ) (b : ι → ℝ) (wo : ι → K → ℝ) (W1 : ι → δ → ℝ) :
    (ι → δ → ℝ) →L[ℝ] (K → ℝ) :=
  (Hagi.Theory.FunctionPreservingGrowth.reluJac (w1Pre x W1) b wo).comp (w1PreCLM x)

omit [Fintype K] in
theorem w1Jac_apply (x : δ → ℝ) (b : ι → ℝ) (wo : ι → K → ℝ) (W1 : ι → δ → ℝ)
    (Δ : ι → δ → ℝ) (v : K) :
    w1Jac x b wo W1 Δ v
      = ∑ i, reluMask (w1Pre x W1 i + b i) * (∑ j, Δ i j * x j) * wo i v := by
  simp only [w1Jac, ContinuousLinearMap.coe_comp, Function.comp_def, w1PreCLM]
  exact Hagi.Theory.FunctionPreservingGrowth.reluJac_apply _ _ _ _ v

/-- **`hasFDerivAt_w1L`**: вне kink (`w i + b i ≠ 0`) логиты
дифференцируемы по матрице `W1`, производная — `w1Jac`
(chain rule: линейная `W1 ↦ W1ᵀx`, затем `hasFDerivAt_reluL`). -/
theorem hasFDerivAt_w1L (b : ι → ℝ) (wo : ι → K → ℝ) (x : δ → ℝ) (W1 : ι → δ → ℝ)
    (hact : ∀ i, w1Pre x W1 i + b i ≠ 0) :
    HasFDerivAt (w1L · b wo x) (w1Jac x b wo W1) W1 := by
  have hpre : HasFDerivAt (w1Pre x) (w1PreCLM x) W1 :=
    (w1PreCLM x).hasFDerivAt
  have h0 : HasFDerivAt (fun c : ι → ℝ => reluL c b wo)
      (Hagi.Theory.FunctionPreservingGrowth.reluJac (w1Pre x W1) b wo) (w1Pre x W1) := by
    have h := hasFDerivAt_reluL b (w1Pre x W1) wo
      (fun i h0 => hact i (add_comm (w1Pre x W1 i) (b i) ▸ h0))
    have hsym : (fun c : ι → ℝ => reluL c b wo) = fun c => reluL b c wo := by
      funext c v
      simp only [reluL]
      exact Finset.sum_congr rfl fun i _ => by rw [add_comm]
    rw [hsym]
    refine h.congr_fderiv ?_
    ext d v
    simp only [Hagi.Theory.FunctionPreservingGrowth.reluJac_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_comm (b i)]
  have h := h0.comp W1 hpre
  refine h.congr_fderiv ?_
  ext Δ v
  simp [w1Jac]

/-- Запись якобиана по `W1` в индексах параметра `(i, j)`:
`J v (i, j) = mask i · wo i v · x j` — `DL(b) = W2 · diag(mask) · x`
(цепочка `x → W1 → relu → Wo` для одного входа). -/
noncomputable def w1Entry (x : δ → ℝ) (b : ι → ℝ) (wo : ι → K → ℝ)
    (W1 : ι → δ → ℝ) : K → ι × δ → ℝ :=
  fun v q => reluMask (w1Pre x W1 q.1 + b q.1) * wo q.1 v * x q.2

omit [Fintype ι] in
/-- **`w1_grad_rank_one`**: градиент `CE ∘ L` по матрице `W1`
(посылка о линейной части, `chainGrad` по `w1Entry`) — RANK-ONE:
`g (i, j) = gᵢ · xⱼ`, где `g i = Σ_v (y v − p v)·mask i·wo i v`
— строка `W2ᵀ r`, умноженная на вход (`r = y − p`). -/
theorem w1_grad_rank_one (x : δ → ℝ) (b : ι → ℝ) (wo : ι → K → ℝ)
    (W1 : ι → δ → ℝ) (p y : K → ℝ) (q : ι × δ) :
    Hagi.Theory.FunctionPreservingGrowth.chainGrad (w1Entry x b wo W1) p y q
      = Hagi.Theory.FunctionPreservingGrowth.chainGrad
          (fun v i => reluMask (w1Pre x W1 i + b i) * wo i v) p y q.1 * x q.2 := by
  have hterm : ∀ v, w1Entry x b wo W1 v q * (y v - p v)
      = (reluMask (w1Pre x W1 q.1 + b q.1) * wo q.1 v) * (y v - p v) * x q.2 := by
    intro v
    simp only [w1Entry]
    ring
  simp only [Hagi.Theory.FunctionPreservingGrowth.chainGrad, hterm,
    Finset.sum_mul]

/-- **`w1_directional_derivative`**: pairing линейной части range-леммы
по возмущению `Δ` матрицы `W1` равно Frobenius-скалярному произведению
`−Σ_{ij} (g i · x j)·Δ i j` — градиент rank-one, скалярное произведение
с `Δ` — «`⟨∂/∂W1, Δ⟩`» в терминах строк `g` и входа `x`. -/
theorem w1_directional_derivative (x : δ → ℝ) (b : ι → ℝ) (wo : ι → K → ℝ)
    (W1 Δ : ι → δ → ℝ) (p y : K → ℝ) :
    ∑ v, (p v - y v) * w1Jac x b wo W1 Δ v
      = -∑ i, ∑ j, (Hagi.Theory.FunctionPreservingGrowth.chainGrad
          (fun v i => reluMask (w1Pre x W1 i + b i) * wo i v) p y i * x j) * Δ i j := by
  have hD : ∀ v, w1Jac x b wo W1 Δ v
      = ∑ q, w1Entry x b wo W1 v q * (fun q => Δ q.1 q.2) q := by
    intro v
    rw [w1Jac_apply]
    simp only [Fintype.sum_prod_type, w1Entry]
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h := Hagi.Theory.FunctionPreservingGrowth.chain_linear (w1Entry x b wo W1) p y
    (fun q => Δ q.1 q.2) _ hD
  beta_reduce at h
  rw [h]
  simp only [Hagi.Step.adamDot, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Hagi.Theory.FunctionPreservingGrowth.chainGrad, w1Entry, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- **T5 `useful_of_adam_first_w1`**: Adam-first по МАТРИЦЕ `W1`
(параметр `ι × δ`), вне kink, `g ≠ 0` ⇒ `∃ η > 0`, для которого
`CE_t (w1L (W1 + η • d)) < CE_t (w1L W1)` — строгое убывание CE
(уровень T3/T4: certified-величина drop не выводится — honest). -/
theorem useful_of_adam_first_w1 [Nonempty ι] [Nonempty δ] [Nonempty K] [DecidableEq K]
    (b : ι → ℝ) (wo : ι → K → ℝ) (x : δ → ℝ) (W1 : ι → δ → ℝ) (t : K)
    (g : ι × δ → ℝ) (d : ι → δ → ℝ) {eps : ℝ} (heps : 0 < eps)
    (hact : ∀ i, w1Pre x W1 i + b i ≠ 0)
    (hg : g = Hagi.Theory.FunctionPreservingGrowth.chainGrad (w1Entry x b wo W1)
      (Hagi.Energy.smax (w1L W1 b wo x)) (fun v => if v = t then 1 else 0))
    (hgne : g ≠ 0) (hd : (fun q => d q.1 q.2) = adamDir g (fun q => g q ^ 2) eps) :
    ∃ η : ℝ, 0 < η ∧
      Hagi.ceOneHot t (w1L (W1 + η • d) b wo x) < Hagi.ceOneHot t (w1L W1 b wo x) :=
  useful_of_adam_first_fderiv (w1L · b wo x) (w1Jac x b wo W1) W1 d (w1Entry x b wo W1) t
    g (fun q => d q.1 q.2) heps (hasFDerivAt_w1L b wo x W1 hact)
    (fun v => by
      rw [w1Jac_apply]
      simp only [Fintype.sum_prod_type, w1Entry]
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    hg hgne hd

omit [Fintype K] in
/-- Rank-one шаг по `W1` вдоль входа: `ΔW1 = (c/s) • (u ⊗ x)`,
`s = Σ xⱼ²` — эквивалентен сдвигу bias на `c • u`. -/
theorem w1_rank_one_step_eq_bias (x : δ → ℝ) (b u : ι → ℝ) (wo : ι → K → ℝ)
    (W1 : ι → δ → ℝ) (c : ℝ) (hs : (∑ j, x j ^ 2) ≠ 0) :
    w1L (fun i j => W1 i j + c / (∑ j, x j ^ 2) * (u i * x j)) b wo x
      = w1L W1 (b + c • u) wo x := by
  have hpre (i : ι) : (∑ j, (W1 i j + c / (∑ k, x k ^ 2) * (u i * x j)) * x j)
      = w1Pre x W1 i + c * u i := by
    simp only [w1Pre, add_mul, Finset.sum_add_distrib]
    have h2 : (∑ j, x j ^ 2) = ∑ j, x j * x j :=
      Finset.sum_congr rfl fun j _ => pow_two (x j)
    have hsplit : ∑ j, (c / (∑ k, x k ^ 2) * (u i * x j)) * x j
        = c / (∑ k, x k ^ 2) * (u i * ∑ j, x j * x j) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit, ← h2]
    field_simp
  unfold w1L
  funext v
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp : w1Pre x (fun i j => W1 i j + c / (∑ k, x k ^ 2) * (u i * x j)) i
      = ∑ j, (W1 i j + c / (∑ k, x k ^ 2) * (u i * x j)) * x j := rfl
  rw [hp, hpre i]
  simp only [Pi.add_apply, smul_eq_mul, Pi.smul_apply]
  congr 1
  ring

end Hagi.Theory.FirstLayerGrad
