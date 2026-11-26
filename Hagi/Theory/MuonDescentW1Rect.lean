/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.MuonDescentW1
import Hagi.Theory.WideSVD

/-!
# MuonDescentW1Rect — мост «прямоугольный слой `W1 : ι → δ → ℝ` → широкий Muon-шаг»

`Hagi/Theory/MuonDescentW1.lean` требует `ι = δ = n`, потому что
`muonStep` квадратный; в коде слой `W1 : dim × hidden` (lm.py:586 @ca52eb4).
Здесь шаг — `wide_iter k Ĝ` (`MuonWide`) на `Matrix ι δ ℝ`,
`Ĝ = G/‖G‖_F` (`wnormed`), сертификат — `wide_alignment_ge_gradient'` и
`useful_of_neg_fderiv` (generic по носителю `E`).

Носитель параметра — координатное пространство `ι → δ → ℝ` (как в
`FirstLayerGrad`); градиент `G : Matrix ι δ ℝ`; спаривание — `fdot_wide`.

* `w1GradR` — градиент CE по `W1` (один вход), `G = −(g ⊗ x)`; тот же объект,
  что `w1Grad`, без квадратности.
* `w1_fderiv_apply_R` — `f'(W1)[Δ] = ⟨G, Δ⟩` (вне kink).
* `w1GradR_ne` — `g ≠ 0`, `x ≠ 0 ⇒ G ≠ 0`.
* `w1StepR`, `fdot_wide_w1StepR_pos`, `muon_step_rect_of_fderiv` — ядро моста.
* `muon_step_useful_w1_rect` — `∃ η > 0`, `CE_t (w1L (W1 − η•d)) < CE_t (w1L W1)`,
  `d = wide_iter k Ĝ`.
* `w1BatchObjR`, `w1BatchGradR`, `w1Batch_fderiv_apply_R`,
  `muon_step_useful_w1_rect_batch` — то же для суммы CE по батчу.

Честная граница: в батче `G ≠ 0` — посылка; `η` только существует; код применяет
NS к momentum `m1`. Посылка размерности `card ι ≤ card δ` снята в `section Tall`
(prime-теоремы в конце файла).
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.MuonDescentW1Rect

open scoped BigOperators
open Hagi.Theory.FirstLayerGrad

variable {ι δ K τ : Type} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Fintype K] [Nonempty K] [DecidableEq K] [Fintype τ]

/-- Градиент `CE_t ∘ w1L` по прямоугольному `W1` (один вход): `G = −(g ⊗ x)`. -/
noncomputable def w1GradR (x : δ → ℝ) (b : ι → ℝ) (wo : ι → K → ℝ) (W1 : ι → δ → ℝ)
    (t : K) : Matrix ι δ ℝ :=
  -(Matrix.of (Hagi.Theory.BatchRankOne.r1
    (Hagi.Theory.BatchRankOne.rowGrad x b wo W1
      (Hagi.Energy.smax (w1L W1 b wo x)) (Hagi.Theory.MuonDescentW1.onehot t)) x))

omit [DecidableEq ι] [DecidableEq δ] [Nonempty K] in
/-- Спаривание: `⟨−A, Δ⟩` равно минус сумме `Σ A i j·Δ i j`. -/
theorem fdot_wide_neg_of (A : ι → δ → ℝ) (Δ : ι → δ → ℝ) :
    Hagi.Theory.MuonWide.fdot_wide (-(Matrix.of A)) Δ
      = -∑ i, ∑ j, A i j * Δ i j := by
  simp [Hagi.Theory.MuonWide.fdot_wide, Matrix.neg_apply, Finset.sum_neg_distrib]

omit [DecidableEq ι] [DecidableEq δ] in
/-- **`w1_fderiv_apply_R`**: `f'(W1)[Δ] = ⟨G, Δ⟩` (широкое спаривание),
`G = −(g ⊗ x)` — вне kink. -/
theorem w1_fderiv_apply_R (x : δ → ℝ) (b : ι → ℝ) (wo : ι → K → ℝ) (W1 Δ : ι → δ → ℝ)
    (t : K) (hact : ∀ i, w1Pre x W1 i + b i ≠ 0) :
    fderiv ℝ (fun c => Hagi.ceOneHot t (w1L c b wo x)) W1 Δ
      = Hagi.Theory.MuonWide.fdot_wide (w1GradR x b wo W1 t) Δ := by
  have hL := hasFDerivAt_w1L b wo x W1 hact
  rw [Hagi.Model.CEGradient.fderiv_ceOneHot_comp_apply _ _ _ Δ t hL]
  have hsoft : ∀ v, Hagi.Prelude.softDef (w1L W1 b wo x) v
      = Hagi.Energy.smax (w1L W1 b wo x) v := fun _ => rfl
  rw [Finset.sum_congr rfl fun v _ => by rw [hsoft v]]
  rw [w1_directional_derivative x b wo W1 Δ _ _, w1GradR]
  exact (fdot_wide_neg_of _ _).symm

omit [DecidableEq ι] [DecidableEq δ] [Nonempty K] in
/-- `w1GradR_ne`: `g ≠ 0`, `x ≠ 0 ⇒ −(g ⊗ x) ≠ 0`. -/
theorem w1GradR_ne {x : δ → ℝ} {g : ι → ℝ} (hg : g ≠ 0) (hx : x ≠ 0)
    (b : ι → ℝ) (wo : ι → K → ℝ) (W1 : ι → δ → ℝ) (t : K)
    (hgdef : g = Hagi.Theory.BatchRankOne.rowGrad x b wo W1
      (Hagi.Energy.smax (w1L W1 b wo x)) (Hagi.Theory.MuonDescentW1.onehot t)) :
    w1GradR x b wo W1 t ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, g i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg (funext hcon)
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  intro h0
  have h1 := congrFun (congrFun h0 i) j
  rw [w1GradR, ← hgdef] at h1
  have h2 : g i = 0 ∨ x j = 0 := by
    simpa [Hagi.Theory.BatchRankOne.r1, mul_eq_zero] using h1
  rcases h2 with h2 | h2
  · exact hi h2
  · exact hj h2

/-- Шаг кода: `d = wide_iter k Ĝ` как элемент носителя `ι → δ → ℝ`. -/
noncomputable def w1StepR (G : Matrix ι δ ℝ) (k : ℕ) : ι → δ → ℝ := fun i j =>
  Hagi.Theory.MuonWide.wide_iter k (Hagi.Theory.WideSVD.wnormed G) i j

/-- Выравнивание широкого шага в направлении градиента: `G ≠ 0`,
`card ι ≤ card δ ⇒ 0 < ⟨G, d⟩`. -/
theorem fdot_wide_w1StepR_pos {G : Matrix ι δ ℝ} (hmn : Fintype.card ι ≤ Fintype.card δ)
    (hG : G ≠ 0) (k : ℕ) :
    0 < Hagi.Theory.MuonWide.fdot_wide G (w1StepR G k) :=
  lt_of_lt_of_le (Real.sqrt_pos.2 (Hagi.Theory.WideSVD.wfrobSq_pos hG))
    (Hagi.Theory.WideSVD.wide_alignment_ge_gradient' G hmn hG k).2

/-- Ядро моста: дифференцируемая в `W1` цель с `f'(W1)[Δ] = ⟨G, Δ⟩`, `G ≠ 0`,
`card ι ≤ card δ` ⇒ `∃ η > 0`, убывание вдоль `W1 − η·wide_iter k Ĝ`. -/
theorem muon_step_rect_of_fderiv (f : (ι → δ → ℝ) → ℝ) (W1 : ι → δ → ℝ)
    (G : Matrix ι δ ℝ) (hdiff : DifferentiableAt ℝ f W1)
    (hfd : ∀ Δ : ι → δ → ℝ, fderiv ℝ f W1 Δ = Hagi.Theory.MuonWide.fdot_wide G Δ)
    (hG : G ≠ 0) (hmn : Fintype.card ι ≤ Fintype.card δ) (k : ℕ) :
    ∃ η : ℝ, 0 < η ∧ f (fun i j => W1 i j - η * w1StepR G k i j) < f W1 := by
  set d : ι → δ → ℝ := w1StepR G k with hd
  have hneg : (fderiv ℝ f W1) (-d) < 0 := by
    have hm := map_neg (fderiv ℝ f W1) d
    rw [map_neg, hfd]
    rw [neg_lt_zero]
    exact fdot_wide_w1StepR_pos hmn hG k
  obtain ⟨η, hη, hlt⟩ := Hagi.Theory.MuonDescent.useful_of_neg_fderiv hdiff.hasFDerivAt hneg
  refine ⟨η, hη, ?_⟩
  have heq : W1 + η • (-d) = fun i j => W1 i j - η * d i j := by
    funext i j
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]; ring
  rwa [heq] at hlt

/-- **`muon_step_useful_w1_rect`**: вне kink, при `g ≠ 0`, `x ≠ 0`,
`card ι ≤ card δ`, шаг кода `W1 ← W1 − η·wide_iter k Ĝ` строго убывает
`CE_t` для малого `η > 0`. -/
theorem muon_step_useful_w1_rect (x : δ → ℝ) (b : ι → ℝ) (wo : ι → K → ℝ)
    (W1 : ι → δ → ℝ) (t : K) (k : ℕ) (hact : ∀ i, w1Pre x W1 i + b i ≠ 0)
    (hg : Hagi.Theory.BatchRankOne.rowGrad x b wo W1
      (Hagi.Energy.smax (w1L W1 b wo x)) (Hagi.Theory.MuonDescentW1.onehot t) ≠ 0)
    (hx : x ≠ 0) (hmn : Fintype.card ι ≤ Fintype.card δ) :
    ∃ η : ℝ, 0 < η ∧ Hagi.ceOneHot t
        (w1L (fun i j => W1 i j - η * w1StepR (w1GradR x b wo W1 t) k i j) b wo x)
      < Hagi.ceOneHot t (w1L W1 b wo x) := by
  have hdiff : DifferentiableAt ℝ (fun c : ι → δ → ℝ => Hagi.ceOneHot t (w1L c b wo x)) W1 :=
    Hagi.Model.CEGradient.differentiableAt_ceOneHot_comp _ _ t
      (hasFDerivAt_w1L b wo x W1 hact).differentiableAt
  have hfd : ∀ Δ : ι → δ → ℝ,
      fderiv ℝ (fun c => Hagi.ceOneHot t (w1L c b wo x)) W1 Δ
        = Hagi.Theory.MuonWide.fdot_wide (w1GradR x b wo W1 t) Δ :=
    fun Δ => w1_fderiv_apply_R x b wo W1 Δ t hact
  have hne : w1GradR x b wo W1 t ≠ 0 := w1GradR_ne hg hx b wo W1 t rfl
  exact muon_step_rect_of_fderiv _ W1 _ hdiff hfd hne hmn k

/-- Батч-лосс: сумма `CE_{y t}` по входам `x t` (mean lm.py:688 —
тот же аргмин, отличается множителем `1/|τ|`). -/
noncomputable def w1BatchObjR (x : τ → δ → ℝ) (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ)
    (W1 : ι → δ → ℝ) : ℝ := ∑ t, Hagi.ceOneHot (y t) (w1L W1 b wo (x t))

/-- Батч-градиент по прямоугольному `W1`: `G = −Σ_t g_t ⊗ x_t`. -/
noncomputable def w1BatchGradR (x : τ → δ → ℝ) (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ)
    (W1 : ι → δ → ℝ) : Matrix ι δ ℝ :=
  -(Matrix.of (Hagi.Theory.BatchRankOne.batchGrad
    (fun t => Hagi.Theory.BatchRankOne.rowGrad (x t) b wo W1
      (Hagi.Energy.smax (w1L W1 b wo (x t))) (Hagi.Theory.MuonDescentW1.onehot (y t))) x))

/-- **`w1Batch_fderiv_apply_R`**: по батчу `f'(W1)[Δ] = ⟨G, Δ⟩`,
`G = −Σ_t g_t ⊗ x_t` (вне kink на каждом входе). -/
theorem w1Batch_fderiv_apply_R (x : τ → δ → ℝ) (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ)
    (W1 Δ : ι → δ → ℝ) (hact : ∀ t i, w1Pre (x t) W1 i + b i ≠ 0) :
    fderiv ℝ (fun c => w1BatchObjR x y b wo c) W1 Δ
      = Hagi.Theory.MuonWide.fdot_wide (w1BatchGradR x y b wo W1) Δ := by
  have hterm (t : τ) : HasFDerivAt
      (fun c : ι → δ → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t)))
      (fderiv ℝ (fun c : ι → δ → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t))) W1) W1 :=
    (Hagi.Model.CEGradient.differentiableAt_ceOneHot_comp _ _ (y t)
      (hasFDerivAt_w1L b wo (x t) W1 (hact t)).differentiableAt).hasFDerivAt
  have hsum := HasFDerivAt.sum (u := (Finset.univ : Finset τ))
    (A := fun t c => Hagi.ceOneHot (y t) (w1L c b wo (x t)))
    (A' := fun t => fderiv ℝ
      (fun c : ι → δ → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t))) W1)
    (fun t _ => hterm t)
  have hsum' : HasFDerivAt (fun c : ι → δ → ℝ => w1BatchObjR x y b wo c)
      (∑ t, fderiv ℝ
        (fun c : ι → δ → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t))) W1) W1 := by
    have e : (∑ t : τ, fun c : ι → δ → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t)))
        = fun c => ∑ t, Hagi.ceOneHot (y t) (w1L c b wo (x t)) := by funext c; simp
    rw [e] at hsum
    simpa [w1BatchObjR] using hsum
  rw [hsum'.fderiv]
  simp only [sum_apply]
  have hterm' (t : τ) : fderiv ℝ
        (fun c : ι → δ → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t))) W1 Δ
      = ∑ v, (Hagi.Energy.smax (w1L W1 b wo (x t)) v - (if v = y t then 1 else 0))
          * w1Jac (x t) b wo W1 Δ v := by
    rw [Hagi.Model.CEGradient.fderiv_ceOneHot_comp_apply _ _ _ Δ (y t)
      (hasFDerivAt_w1L b wo (x t) W1 (hact t))]
    exact Finset.sum_congr rfl fun v _ => rfl
  rw [Finset.sum_congr rfl fun t _ => hterm' t]
  rw [Hagi.Theory.BatchRankOne.batch_directional_derivative x b wo W1 Δ _ _, w1BatchGradR]
  exact (fdot_wide_neg_of _ _).symm

/-- **`muon_step_useful_w1_rect_batch`**: вне kink, при `G ≠ 0`,
`card ι ≤ card δ`, шаг `W1 ← W1 − η·wide_iter k Ĝ` строго убывает сумму
`CE` по батчу для малого `η > 0` (а значит и mean-лосс lm.py:688). -/
theorem muon_step_useful_w1_rect_batch (x : τ → δ → ℝ) (y : τ → K) (b : ι → ℝ)
    (wo : ι → K → ℝ) (W1 : ι → δ → ℝ) (k : ℕ) (hact : ∀ t i, w1Pre (x t) W1 i + b i ≠ 0)
    (hG : w1BatchGradR x y b wo W1 ≠ 0) (hmn : Fintype.card ι ≤ Fintype.card δ) :
    ∃ η : ℝ, 0 < η ∧ w1BatchObjR x y b wo (fun i j => W1 i j
        - η * w1StepR (w1BatchGradR x y b wo W1) k i j)
      < w1BatchObjR x y b wo W1 := by
  have hdiff : DifferentiableAt ℝ (fun c : ι → δ → ℝ => w1BatchObjR x y b wo c) W1 := by
    have hterm (t : τ) : DifferentiableAt ℝ
        (fun c : ι → δ → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t))) W1 :=
      Hagi.Model.CEGradient.differentiableAt_ceOneHot_comp _ _ (y t)
        (hasFDerivAt_w1L b wo (x t) W1 (hact t)).differentiableAt
    have hsum := DifferentiableAt.sum (u := (Finset.univ : Finset τ))
      (A := fun t c => Hagi.ceOneHot (y t) (w1L c b wo (x t))) (fun t _ => hterm t)
    have e : (∑ t : τ, fun c : ι → δ → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t)))
        = fun c => ∑ t, Hagi.ceOneHot (y t) (w1L c b wo (x t)) := by funext c; simp
    rw [e] at hsum
    simpa [w1BatchObjR] using hsum
  have hfd : ∀ Δ : ι → δ → ℝ, fderiv ℝ (fun c => w1BatchObjR x y b wo c) W1 Δ
      = Hagi.Theory.MuonWide.fdot_wide (w1BatchGradR x y b wo W1) Δ :=
    fun Δ => w1Batch_fderiv_apply_R x y b wo W1 Δ hact
  exact muon_step_rect_of_fderiv _ W1 _ hdiff hfd hG hmn k

/-! ### Высокий слой — транспонирование снимает посылку размерности

`wide_iter` определён для любой формы `m×n` (`ns_step` без ограничений), и
`code_ns_eq_wide_iter` говорит, что код-выход равен `wide_iter k G` и для
высокой матрицы. Спаривание и нормировка ковариантны: `⟨Gᵀ, Hᵀ⟩ = ⟨G, H⟩`,
`‖Gᵀ‖_F = ‖G‖_F`, `wnormed Gᵀ = (wnormed G)ᵀ`; с `wide_iter_transpose`
сертификат `wide_alignment_ge_gradient'` для `Gᵀ` переносится на высокий `G`.

* `fdot_transpose`, `wfrobSq_transpose`, `wnormed_transpose` — (L1, L2).
* `tall_alignment_ge_gradient`, `alignment_ge_gradient_any` — (L3) высокий `G`
  через `wide_iter_transpose`; итог для любой формы.
* `fdot_wide_w1StepR_pos'`, `w1StepR_eq_code_ns`, `muon_step_rect_of_fderiv'`,
  `muon_step_useful_w1_rect'`, `muon_step_useful_w1_rect_batch'` — (L4) те же
  сертификаты БЕЗ посылки размерности (версии с `hmn` не менялись).
-/

section Tall

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- **(L1) `fdot_transpose`**: спаривание Фробениуса инвариантно относительно
одновременного транспонирования (сумма по `i j` симметрична). -/
theorem fdot_transpose (G H : Matrix m n ℝ) :
    Hagi.Theory.MuonWide.fdot_wide (Matrix.transpose G) (Matrix.transpose H)
      = Hagi.Theory.MuonWide.fdot_wide G H := by
  simp only [Hagi.Theory.MuonWide.fdot_wide, Matrix.transpose_apply]
  exact Finset.sum_comm

omit [DecidableEq m] [DecidableEq n] in
/-- **(L2) `wfrobSq_transpose`**: `‖Gᵀ‖_F = ‖G‖_F`. -/
theorem wfrobSq_transpose (G : Matrix m n ℝ) :
    Hagi.Theory.WideSVD.wfrobSq (Matrix.transpose G) = Hagi.Theory.WideSVD.wfrobSq G := by
  simp only [Hagi.Theory.WideSVD.wfrobSq, Matrix.transpose_apply]
  exact Finset.sum_comm

omit [DecidableEq m] [DecidableEq n] in
/-- **(L2) `wnormed_transpose`**: `wnormed Gᵀ = (wnormed G)ᵀ` — нормировка
*не* фиксирует форму (`wnormed` через `wfrobSq`, скаляр тот же). -/
theorem wnormed_transpose (G : Matrix m n ℝ) :
    Hagi.Theory.WideSVD.wnormed (Matrix.transpose G)
      = Matrix.transpose (Hagi.Theory.WideSVD.wnormed G) := by
  simp only [Hagi.Theory.WideSVD.wnormed, wfrobSq_transpose, Matrix.transpose_smul]

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
theorem transpose_ne_zero {G : Matrix m n ℝ} (hG : G ≠ 0) : Matrix.transpose G ≠ 0 := by
  intro h
  exact hG (by rw [← Matrix.transpose_transpose G, h]; rfl)

/-- **(L3) `tall_alignment_ge_gradient`**: для ВЫСОКОГО `G` (`card n ≤ card m`)
выравнивание шага `wide_iter k Ĝ` (той же формы, что `G`) не хуже `‖G‖_F`. -/
theorem tall_alignment_ge_gradient (G : Matrix m n ℝ) (hnm : Fintype.card n ≤ Fintype.card m)
    (hG : G ≠ 0) (k : ℕ) :
    Real.sqrt (Hagi.Theory.WideSVD.wfrobSq G)
      ≤ Hagi.Theory.MuonWide.fdot_wide G
          (Hagi.Theory.MuonWide.wide_iter k (Hagi.Theory.WideSVD.wnormed G)) := by
  have hstep : Matrix.transpose (Hagi.Theory.MuonWide.wide_iter k (Hagi.Theory.WideSVD.wnormed G))
      = Hagi.Theory.MuonWide.wide_iter k (Hagi.Theory.WideSVD.wnormed (Matrix.transpose G)) := by
    rw [← Hagi.Theory.MuonWide.wide_iter_transpose k, ← wnormed_transpose]
  have hsq : Hagi.Theory.WideSVD.wfrobSq (Matrix.transpose G) = Hagi.Theory.WideSVD.wfrobSq G :=
    wfrobSq_transpose G
  have h := (Hagi.Theory.WideSVD.wide_alignment_ge_gradient' (Matrix.transpose G) hnm
    (transpose_ne_zero hG) k).2
  rw [hsq] at h
  calc Real.sqrt (Hagi.Theory.WideSVD.wfrobSq G)
      ≤ Hagi.Theory.MuonWide.fdot_wide (Matrix.transpose G)
          (Hagi.Theory.MuonWide.wide_iter k (Hagi.Theory.WideSVD.wnormed (Matrix.transpose G))) :=
        h
    _ = Hagi.Theory.MuonWide.fdot_wide G
          (Hagi.Theory.MuonWide.wide_iter k (Hagi.Theory.WideSVD.wnormed G)) := by
          rw [← hstep, fdot_transpose]

/-- **`alignment_ge_gradient_any`**: для `G : m×n` ЛЮБОЙ формы (`m ≤ n`, `m > n`
или равенство) `‖G‖_F ≤ ⟨G, wide_iter k Ĝ⟩` — посылка размерности снята
разбором случаев `le_total`. -/
theorem alignment_ge_gradient_any (G : Matrix m n ℝ) (hG : G ≠ 0) (k : ℕ) :
    Real.sqrt (Hagi.Theory.WideSVD.wfrobSq G)
      ≤ Hagi.Theory.MuonWide.fdot_wide G
          (Hagi.Theory.MuonWide.wide_iter k (Hagi.Theory.WideSVD.wnormed G)) := by
  rcases le_total (Fintype.card m) (Fintype.card n) with h | h
  · exact (Hagi.Theory.WideSVD.wide_alignment_ge_gradient' G h hG k).2
  · exact tall_alignment_ge_gradient G h hG k

end Tall

/-! ### Теоремы без посылки `card ι ≤ card δ` (prime-версии) -/

/-- Выравнивание шага для слоя любой формы: `G ≠ 0 ⇒ 0 < ⟨G, d⟩`,
`d = wide_iter k Ĝ`. -/
theorem fdot_wide_w1StepR_pos' {G : Matrix ι δ ℝ} (hG : G ≠ 0) (k : ℕ) :
    0 < Hagi.Theory.MuonWide.fdot_wide G (w1StepR G k) :=
  lt_of_lt_of_le (Real.sqrt_pos.2 (Hagi.Theory.WideSVD.wfrobSq_pos hG))
    (alignment_ge_gradient_any G hG k)

/-- **`w1StepR_eq_code_ns`**: шаг `w1StepR` слоя любой формы равен выводу кода
`code_ns` (core.py:1358–1361 транспонирует высокую матрицу). -/
theorem w1StepR_eq_code_ns (G : Matrix ι δ ℝ) (k : ℕ) :
    w1StepR G k
      = fun i j => Hagi.Theory.MuonWide.code_ns k (Hagi.Theory.WideSVD.wnormed G) i j := by
  funext i j
  simp only [w1StepR, Hagi.Theory.MuonWide.code_ns_eq_wide_iter]

/-- **`muon_step_rect_of_fderiv'`**: ядро моста без посылки размерности. -/
theorem muon_step_rect_of_fderiv' (f : (ι → δ → ℝ) → ℝ) (W1 : ι → δ → ℝ)
    (G : Matrix ι δ ℝ) (hdiff : DifferentiableAt ℝ f W1)
    (hfd : ∀ Δ : ι → δ → ℝ, fderiv ℝ f W1 Δ = Hagi.Theory.MuonWide.fdot_wide G Δ)
    (hG : G ≠ 0) (k : ℕ) :
    ∃ η : ℝ, 0 < η ∧ f (fun i j => W1 i j - η * w1StepR G k i j) < f W1 := by
  have hpos : 0 < Hagi.Theory.MuonWide.fdot_wide G (w1StepR G k) := fdot_wide_w1StepR_pos' hG k
  have hneg : (fderiv ℝ f W1) (-(w1StepR G k)) < 0 := by
    rw [map_neg, hfd, neg_lt_zero]
    exact hpos
  obtain ⟨η, hη, hlt⟩ := Hagi.Theory.MuonDescent.useful_of_neg_fderiv hdiff.hasFDerivAt hneg
  refine ⟨η, hη, ?_⟩
  have heq : W1 + η • (-(w1StepR G k)) = fun i j => W1 i j - η * w1StepR G k i j := by
    funext i j
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
    ring
  rwa [heq] at hlt

/-- **`muon_step_useful_w1_rect'`**: вне kink, при `g ≠ 0`, `x ≠ 0`, слой
`W1 : ι → δ → ℝ` ЛЮБОЙ формы — шаг кода `W1 ← W1 − η·wide_iter k Ĝ` строго
убывает `CE_t` для малого `η > 0`. -/
theorem muon_step_useful_w1_rect' (x : δ → ℝ) (b : ι → ℝ) (wo : ι → K → ℝ)
    (W1 : ι → δ → ℝ) (t : K) (k : ℕ) (hact : ∀ i, w1Pre x W1 i + b i ≠ 0)
    (hg : Hagi.Theory.BatchRankOne.rowGrad x b wo W1
      (Hagi.Energy.smax (w1L W1 b wo x)) (Hagi.Theory.MuonDescentW1.onehot t) ≠ 0)
    (hx : x ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ Hagi.ceOneHot t
        (w1L (fun i j => W1 i j - η * w1StepR (w1GradR x b wo W1 t) k i j) b wo x)
      < Hagi.ceOneHot t (w1L W1 b wo x) := by
  have hdiff : DifferentiableAt ℝ (fun c : ι → δ → ℝ => Hagi.ceOneHot t (w1L c b wo x)) W1 :=
    Hagi.Model.CEGradient.differentiableAt_ceOneHot_comp _ _ t
      (hasFDerivAt_w1L b wo x W1 hact).differentiableAt
  have hfd : ∀ Δ : ι → δ → ℝ,
      fderiv ℝ (fun c => Hagi.ceOneHot t (w1L c b wo x)) W1 Δ
        = Hagi.Theory.MuonWide.fdot_wide (w1GradR x b wo W1 t) Δ :=
    fun Δ => w1_fderiv_apply_R x b wo W1 Δ t hact
  have hne : w1GradR x b wo W1 t ≠ 0 := w1GradR_ne hg hx b wo W1 t rfl
  exact muon_step_rect_of_fderiv' _ W1 _ hdiff hfd hne k

/-- **`muon_step_useful_w1_rect_batch'`**: вне kink, при `G ≠ 0`, слой
`W1 : ι → δ → ℝ` ЛЮБОЙ формы — шаг `W1 ← W1 − η·wide_iter k Ĝ` строго
убывает сумму `CE` по батчу для малого `η > 0` (а значит и mean-лосс). -/
theorem muon_step_useful_w1_rect_batch' (x : τ → δ → ℝ) (y : τ → K) (b : ι → ℝ)
    (wo : ι → K → ℝ) (W1 : ι → δ → ℝ) (k : ℕ) (hact : ∀ t i, w1Pre (x t) W1 i + b i ≠ 0)
    (hG : w1BatchGradR x y b wo W1 ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ w1BatchObjR x y b wo (fun i j => W1 i j
        - η * w1StepR (w1BatchGradR x y b wo W1) k i j)
      < w1BatchObjR x y b wo W1 := by
  have hdiff : DifferentiableAt ℝ (fun c : ι → δ → ℝ => w1BatchObjR x y b wo c) W1 := by
    have hterm (t : τ) : DifferentiableAt ℝ
        (fun c : ι → δ → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t))) W1 :=
      Hagi.Model.CEGradient.differentiableAt_ceOneHot_comp _ _ (y t)
        (hasFDerivAt_w1L b wo (x t) W1 (hact t)).differentiableAt
    have hsum := DifferentiableAt.sum (u := (Finset.univ : Finset τ))
      (A := fun t c => Hagi.ceOneHot (y t) (w1L c b wo (x t))) (fun t _ => hterm t)
    have e : (∑ t : τ, fun c : ι → δ → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t)))
        = fun c => ∑ t, Hagi.ceOneHot (y t) (w1L c b wo (x t)) := by funext c; simp
    rw [e] at hsum
    simpa [w1BatchObjR] using hsum
  have hfd : ∀ Δ : ι → δ → ℝ, fderiv ℝ (fun c => w1BatchObjR x y b wo c) W1 Δ
      = Hagi.Theory.MuonWide.fdot_wide (w1BatchGradR x y b wo W1) Δ :=
    fun Δ => w1Batch_fderiv_apply_R x y b wo W1 Δ hact
  exact muon_step_rect_of_fderiv' _ W1 _ hdiff hfd hG k

end Hagi.Theory.MuonDescentW1Rect
