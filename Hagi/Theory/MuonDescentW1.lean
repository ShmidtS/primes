/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.MuonDescent
import Hagi.Theory.BatchRankOne

/-!
# MuonDescentW1 — мост «слой `W1` (lm.py:586) → Muon-шаг» без гипотезы на дифференциал

C676. Снимает гипотезу `hφ : ∀ Δ, φ Δ = ⟨g, Δ⟩` теоремы `muon_step_useful`
(`Hagi/Theory/MuonDescent.lean`) для реального слоя: носитель —
функциональный `n → n → ℝ` (как в C668/C669), дифференциал `CE_t ∘ w1L`
построен явно (`hasFDerivAt_w1L`, C668; `fderiv_ceOneHot_comp_apply`), и
его значение в направлении `Δ` равно `⟨G, Δ⟩` с `G = −(g ⊗ x)`
(`w1_directional_derivative`, C668). Спуск — `useful_of_neg_fderiv` (C675),
направление — `muonStep G k` (C675) в том же носителе.

* `w1Grad` — градиент CE по `W1` для одного входа: `G = −(g ⊗ x)`.
* `w1_fderiv_apply` — `f'(W1)[Δ] = ⟨G, Δ⟩`: гипотеза `φ` выведена (вне kink).
* `w1Grad_ne` — `g ≠ 0`, `x ≠ 0 ⇒ G ≠ 0`.
* `muon_step_useful_w1` — итог: `∃ η > 0`,
  `CE_t (w1L (W1 − η•X₃)) < CE_t (w1L W1)`, `X₃ = ns_iter k Ĝ`.
* `w1BatchGrad`, `w1Batch_fderiv_apply`, `muon_step_useful_w1_batch` — то же
  для суммы CE по батчу входов (`batch_directional_derivative`, C669);
  mean-лосс lm.py:688 отличается положительным множителем.

Честная граница: слой квадратный (`ι = δ = n`; в коде `W1 : dim × hidden`);
в батче `G ≠ 0` — посылка; `η` только существует.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.MuonDescentW1

open scoped BigOperators
open Hagi.Theory.FirstLayerGrad

variable {n K : Type} [Fintype n] [DecidableEq n] [Fintype K] [Nonempty K] [DecidableEq K]
  {τ : Type} [Fintype τ]

/-- One-hot метка `t`. -/
noncomputable def onehot (t : K) : K → ℝ := fun v => if v = t then 1 else 0

/-- Градиент `CE_t ∘ w1L` по `W1` (один вход): `G = −(g ⊗ x)`,
`g = rowGrad x b wo W1 p y` (C668, `w1_grad_rank_one`). -/
noncomputable def w1Grad (x : n → ℝ) (b : n → ℝ) (wo : n → K → ℝ) (W1 : n → n → ℝ)
    (t : K) : Matrix n n ℝ :=
  -(Matrix.of (Hagi.Theory.BatchRankOne.r1
    (Hagi.Theory.BatchRankOne.rowGrad x b wo W1
      (Hagi.Energy.smax (w1L W1 b wo x)) (onehot t)) x))

omit [DecidableEq n] [Nonempty K] in
/-- Спаривание: `⟨−A, Δ⟩` равно минус сумме `Σ A i j·Δ i j`. -/
theorem fdot_neg_of (A : n → n → ℝ) (Δ : n → n → ℝ) :
    Hagi.Theory.MuonSpectral.fdot (-(Matrix.of A)) (Matrix.of Δ)
      = -∑ i, ∑ j, A i j * Δ i j := by
  simp [Hagi.Theory.MuonSpectral.fdot, Matrix.neg_apply, Finset.sum_neg_distrib]

omit [DecidableEq n] in
/-- **`w1_fderiv_apply`**: значение дифференциала слоя в направлении `Δ`:
`f'(W1)[Δ] = ⟨G, Δ⟩`, `G = −(g ⊗ x)` — гипотеза `φ` теоремы
`muon_step_useful` выведена (вне kink). -/
theorem w1_fderiv_apply (x : n → ℝ) (b : n → ℝ) (wo : n → K → ℝ) (W1 Δ : n → n → ℝ)
    (t : K) (hact : ∀ i, w1Pre x W1 i + b i ≠ 0) :
    fderiv ℝ (fun c => Hagi.ceOneHot t (w1L c b wo x)) W1 Δ
      = Hagi.Theory.MuonSpectral.fdot (w1Grad x b wo W1 t) (Matrix.of Δ) := by
  have hL := hasFDerivAt_w1L b wo x W1 hact
  rw [Hagi.Model.CEGradient.fderiv_ceOneHot_comp_apply _ _ _ Δ t hL]
  have hsoft : ∀ v, Hagi.Prelude.softDef (w1L W1 b wo x) v
      = Hagi.Energy.smax (w1L W1 b wo x) v := fun _ => rfl
  rw [Finset.sum_congr rfl fun v _ => by rw [hsoft v]]
  rw [w1_directional_derivative x b wo W1 Δ _ _, w1Grad]
  exact (fdot_neg_of _ _).symm

omit [DecidableEq n] [Nonempty K] in
/-- `w1Grad_ne`: `g ≠ 0`, `x ≠ 0 ⇒ −(g ⊗ x) ≠ 0`. -/
theorem w1Grad_ne {x g : n → ℝ} (hg : g ≠ 0) (hx : x ≠ 0) (b : n → ℝ) (wo : n → K → ℝ)
    (W1 : n → n → ℝ) (t : K)
    (hgdef : g = Hagi.Theory.BatchRankOne.rowGrad x b wo W1
      (Hagi.Energy.smax (w1L W1 b wo x)) (onehot t)) :
    w1Grad x b wo W1 t ≠ 0 := by
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
  rw [w1Grad, ← hgdef] at h1
  have h2 : g i = 0 ∨ x j = 0 := by
    simpa [Hagi.Theory.BatchRankOne.r1, mul_eq_zero] using h1
  rcases h2 with h2 | h2
  · exact hi h2
  · exact hj h2

/-- **`muon_step_useful_w1`** — гипотеза `φ` снята: вне kink, при `g ≠ 0`,
`x ≠ 0`, шаг кода `W1 ← W1 − η·ns_iter k Ĝ` строго убывает `CE_t` для
малого `η > 0`. -/
theorem muon_step_useful_w1 [Nonempty n] (x : n → ℝ) (b : n → ℝ) (wo : n → K → ℝ)
    (W1 : n → n → ℝ) (t : K) (k : ℕ) (hact : ∀ i, w1Pre x W1 i + b i ≠ 0)
    (hg : Hagi.Theory.BatchRankOne.rowGrad x b wo W1
      (Hagi.Energy.smax (w1L W1 b wo x)) (onehot t) ≠ 0) (hx : x ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ Hagi.ceOneHot t (w1L (fun i j => W1 i j
        - η * Hagi.Theory.MuonDescent.muonStep (w1Grad x b wo W1 t) k i j) b wo x)
      < Hagi.ceOneHot t (w1L W1 b wo x) := by
  set G := w1Grad x b wo W1 t with hG
  have hdiff : DifferentiableAt ℝ (fun c : n → n → ℝ => Hagi.ceOneHot t (w1L c b wo x)) W1 :=
    Hagi.Model.CEGradient.differentiableAt_ceOneHot_comp _ _ t
      (hasFDerivAt_w1L b wo x W1 hact).differentiableAt
  have hne : G ≠ 0 := w1Grad_ne hg hx b wo W1 t rfl
  have hpos : 0 < Hagi.Theory.MuonSpectral.fdot G (Hagi.Theory.MuonDescent.muonStep G k) :=
    lt_of_lt_of_le (Real.sqrt_pos.2 (Hagi.Theory.MuonDescent.frobSq_pos hne))
      (Hagi.Theory.MuonDescent.muon_step_inner_ge_frob hne k).2
  set d : n → n → ℝ := fun i j => Hagi.Theory.MuonDescent.muonStep G k i j with hd
  have hdeq : Matrix.of d = Hagi.Theory.MuonDescent.muonStep G k := by
    ext i j
    rfl
  have hneg : (fderiv ℝ (fun c : n → n → ℝ => Hagi.ceOneHot t (w1L c b wo x)) W1) (-d) < 0 := by
    have hm := map_neg (fderiv ℝ (fun c : n → n → ℝ => Hagi.ceOneHot t (w1L c b wo x)) W1) d
    have hf : Hagi.Theory.MuonSpectral.fdot G (Matrix.of d)
        = Hagi.Theory.MuonSpectral.fdot G (Hagi.Theory.MuonDescent.muonStep G k) := by
      rw [← hdeq]
    have hfd := w1_fderiv_apply x b wo W1 d t hact
    rw [hf] at hfd
    rw [hm, hfd, neg_lt_zero]
    exact hpos
  obtain ⟨η, hη, hlt⟩ := Hagi.Theory.MuonDescent.useful_of_neg_fderiv hdiff.hasFDerivAt hneg
  refine ⟨η, hη, ?_⟩
  have heq : W1 + η • (-d) = fun i j => W1 i j - η * d i j := by
    ext i j
    simp [sub_eq_add_neg]
  rwa [heq] at hlt

omit [DecidableEq n] [Nonempty K] in
/-- Батч-лосс: сумма `CE_{y t}` по входам `x t` (mean lm.py:688 —
тот же аргмин, отличается множителем `1/|τ|`). -/
noncomputable def w1BatchObj (x : τ → n → ℝ) (y : τ → K) (b : n → ℝ) (wo : n → K → ℝ)
    (W1 : n → n → ℝ) : ℝ := ∑ t, Hagi.ceOneHot (y t) (w1L W1 b wo (x t))

omit [DecidableEq n] [Nonempty K] in
/-- Батч-градиент по `W1`: `G = −Σ_t g_t ⊗ x_t` (`batchGrad`, C669). -/
noncomputable def w1BatchGrad (x : τ → n → ℝ) (y : τ → K) (b : n → ℝ) (wo : n → K → ℝ)
    (W1 : n → n → ℝ) : Matrix n n ℝ :=
  -(Matrix.of (Hagi.Theory.BatchRankOne.batchGrad
    (fun t => Hagi.Theory.BatchRankOne.rowGrad (x t) b wo W1
      (Hagi.Energy.smax (w1L W1 b wo (x t))) (onehot (y t))) x))

omit [DecidableEq n] in
/-- **`w1Batch_fderiv_apply`**: по батчу `f'(W1)[Δ] = ⟨G, Δ⟩`,
`G = −Σ_t g_t ⊗ x_t` (вне kink на каждом входе). -/
theorem w1Batch_fderiv_apply (x : τ → n → ℝ) (y : τ → K) (b : n → ℝ) (wo : n → K → ℝ)
    (W1 Δ : n → n → ℝ) (hact : ∀ t i, w1Pre (x t) W1 i + b i ≠ 0) :
    fderiv ℝ (fun c => w1BatchObj x y b wo c) W1 Δ
      = Hagi.Theory.MuonSpectral.fdot (w1BatchGrad x y b wo W1) (Matrix.of Δ) := by
  have hterm (t : τ) : HasFDerivAt
      (fun c : n → n → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t)))
      (fderiv ℝ (fun c : n → n → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t))) W1) W1 :=
    (Hagi.Model.CEGradient.differentiableAt_ceOneHot_comp _ _ (y t)
      (hasFDerivAt_w1L b wo (x t) W1 (hact t)).differentiableAt).hasFDerivAt
  have hsum := HasFDerivAt.sum (u := (Finset.univ : Finset τ))
    (A := fun t c => Hagi.ceOneHot (y t) (w1L c b wo (x t)))
    (A' := fun t => fderiv ℝ
      (fun c : n → n → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t))) W1)
    (fun t _ => hterm t)
  have hsum' : HasFDerivAt (fun c : n → n → ℝ => w1BatchObj x y b wo c)
      (∑ t, fderiv ℝ
        (fun c : n → n → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t))) W1) W1 := by
    have e : (∑ t : τ, fun c : n → n → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t)))
        = fun c => ∑ t, Hagi.ceOneHot (y t) (w1L c b wo (x t)) := by funext c; simp
    rw [e] at hsum
    simpa [w1BatchObj] using hsum
  rw [hsum'.fderiv]
  simp only [sum_apply]
  have hterm' (t : τ) : fderiv ℝ
        (fun c : n → n → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t))) W1 Δ
      = ∑ v, (Hagi.Energy.smax (w1L W1 b wo (x t)) v - (if v = y t then 1 else 0))
          * w1Jac (x t) b wo W1 Δ v := by
    rw [Hagi.Model.CEGradient.fderiv_ceOneHot_comp_apply _ _ _ Δ (y t)
      (hasFDerivAt_w1L b wo (x t) W1 (hact t))]
    exact Finset.sum_congr rfl fun v _ => rfl
  rw [Finset.sum_congr rfl fun t _ => hterm' t]
  rw [Hagi.Theory.BatchRankOne.batch_directional_derivative x b wo W1 Δ _ _, w1BatchGrad]
  exact (fdot_neg_of _ _).symm

/-- **`muon_step_useful_w1_batch`**: гипотеза `φ` снята по батчу: вне
kink, при `G ≠ 0`, шаг `W1 ← W1 − η·ns_iter k Ĝ` строго убывает сумму `CE`
по батчу для малого `η > 0` (а значит и mean-лосс lm.py:688). -/
theorem muon_step_useful_w1_batch [Nonempty n] (x : τ → n → ℝ) (y : τ → K) (b : n → ℝ)
    (wo : n → K → ℝ) (W1 : n → n → ℝ) (k : ℕ) (hact : ∀ t i, w1Pre (x t) W1 i + b i ≠ 0)
    (hG : w1BatchGrad x y b wo W1 ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ w1BatchObj x y b wo (fun i j => W1 i j
        - η * Hagi.Theory.MuonDescent.muonStep (w1BatchGrad x y b wo W1) k i j)
      < w1BatchObj x y b wo W1 := by
  set G := w1BatchGrad x y b wo W1 with hGdef
  have hdiff : DifferentiableAt ℝ (fun c : n → n → ℝ => w1BatchObj x y b wo c) W1 := by
    have hterm (t : τ) : DifferentiableAt ℝ
        (fun c : n → n → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t))) W1 :=
      Hagi.Model.CEGradient.differentiableAt_ceOneHot_comp _ _ (y t)
        (hasFDerivAt_w1L b wo (x t) W1 (hact t)).differentiableAt
    have := DifferentiableAt.sum (u := (Finset.univ : Finset τ))
      (A := fun t c => Hagi.ceOneHot (y t) (w1L c b wo (x t))) (fun t _ => hterm t)
    have e : (∑ t : τ, fun c : n → n → ℝ => Hagi.ceOneHot (y t) (w1L c b wo (x t)))
        = fun c => ∑ t, Hagi.ceOneHot (y t) (w1L c b wo (x t)) := by funext c; simp
    rw [e] at this
    simpa [w1BatchObj] using this
  have hpos : 0 < Hagi.Theory.MuonSpectral.fdot G (Hagi.Theory.MuonDescent.muonStep G k) :=
    lt_of_lt_of_le (Real.sqrt_pos.2 (Hagi.Theory.MuonDescent.frobSq_pos hG))
      (Hagi.Theory.MuonDescent.muon_step_inner_ge_frob hG k).2
  set d : n → n → ℝ := fun i j => Hagi.Theory.MuonDescent.muonStep G k i j with hd
  have hdeq : Matrix.of d = Hagi.Theory.MuonDescent.muonStep G k := by
    ext i j
    rfl
  have hneg : (fderiv ℝ (fun c : n → n → ℝ => w1BatchObj x y b wo c) W1) (-d) < 0 := by
    have hm := map_neg (fderiv ℝ (fun c : n → n → ℝ => w1BatchObj x y b wo c) W1) d
    have hf : Hagi.Theory.MuonSpectral.fdot G (Matrix.of d)
        = Hagi.Theory.MuonSpectral.fdot G (Hagi.Theory.MuonDescent.muonStep G k) := by
      rw [← hdeq]
    have hfd := w1Batch_fderiv_apply x y b wo W1 d hact
    rw [hf] at hfd
    rw [hm, hfd, neg_lt_zero]
    exact hpos
  obtain ⟨η, hη, hlt⟩ := Hagi.Theory.MuonDescent.useful_of_neg_fderiv hdiff.hasFDerivAt hneg
  refine ⟨η, hη, ?_⟩
  have heq : W1 + η • (-d) = fun i j => W1 i j - η * d i j := by
    ext i j
    simp [sub_eq_add_neg]
  rwa [heq] at hlt

end Hagi.Theory.MuonDescentW1
