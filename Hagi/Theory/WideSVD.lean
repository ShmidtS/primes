/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.MuonDescent
import Hagi.Theory.MuonWide

/-!
# WideSVD — вещественный прямоугольный SVD из квадратного (pad-to-square)

C679. Для широкой вещественной `G : Matrix m n ℝ` (`card m ≤ card n`)
существует разложение `G = U·diag σ·Vᵀ` с `U : m×m`, `V : n×m`,
`UᵀU = 1`, `VᵀV = 1`, `σ ≥ 0`. Тем самым гипотеза `G = U·diag σ·Vᵀ`
в MuonWide (T1–T5) снимается: `wide_alignment_exact'`,
`wide_alignment_ge_gradient'`, `wide_step_optimal'` — без посылок о
разложении.

Вывод (pad-to-square). `padSquare e r G = [G; 0] : n×n` (дополнение
нулями снизу), квадратный `svd_decomposition Ĝ = U Σ Vᵀ` (`SVDReal.lean`).
Собственные значения `ĜᵀĜ` антонатонны (`eigenvalues₀_antitone`), число
ненулевых равно `rank (GᵀG) = rank G ≤ card m` (`rank_eq_card_non_zero_eigs`,
`rank_transpose_mul_self`, `rank_le_card_height`), поэтому `σ i = 0` вне
первых `card m` индексов. Оставляем первые `card m` строк `U` и столбцов
`V`: `G = U₀ Σ₀ V₀ᵀ`.

Граница: порядок `σ` (↓) не утверждается — он зависит от перенумерации
`Fintype.equivFin`; MuonWide он не нужен. Порядок `σ` (↓) не утверждается.

C680 (S1, S3): `wfrobSq_eq_sum_sigma_sq` — `‖G‖_F² = Σ σ i²` для спектра из
`exists_wide_svd`; `wnormed_sigma_le_one` — спектр нормированного `Ĝ = G/‖G‖_F`
лежит в `[0, 1]`; `wide_alignment_ge_gradient'` — T3 без единой посылки о
структуре `G`; `muon_step_useful_wide` — сертификат спуска для широкого шага.

Граница: только широкая форма `card m ≤ card n` (высокий случай —
`MuonWide.code_ns_eq_wide_iter`); носитель сертификата — координатное
пространство `m → n → ℝ`, мост к слою `W1` и носителю C676 не формализован;
проверка `norm < 1e-12 → return X` (core.py:1355) и число итераций вне теории.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace Hagi.Theory.WideSVD

open scoped BigOperators
open Matrix Hagi.External.Flywheel

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Дополнение нулями до квадратной: строки вне `range e` нулевые,
строка `e i` равна строке `i` матрицы `G`. -/
def padSquare (e : m → n) (r : n → m) (G : Matrix m n ℝ) : Matrix n n ℝ :=
  Matrix.of fun x y => if x ∈ Set.range e then G (r x) y else 0

omit [DecidableEq m] [Fintype n] in
lemma padSquare_apply (e : m → n) (r : n → m) (her : ∀ i, r (e i) = i)
    (G : Matrix m n ℝ) (i : m) (y : n) : padSquare e r G (e i) y = G i y := by
  simp [padSquare, her i]

omit [DecidableEq m] in
lemma padSquare_eq_zero (e : m → n) (r : n → m) (G : Matrix m n ℝ) {x : n}
    (hx : x ∉ Set.range e) (y : n) : padSquare e r G x y = 0 := by
  simp only [padSquare, Matrix.of_apply, if_neg hx]

lemma padSquare_transpose_mul_self (e : m → n) (r : n → m) (hei : Function.Injective e)
    (her : ∀ i, r (e i) = i) (G : Matrix m n ℝ) :
    (padSquare e r G)ᵀ * padSquare e r G = Gᵀ * G := by
  ext a b
  show (∑ j, padSquare e r G j a * padSquare e r G j b) = ∑ j, G j a * G j b
  rw [← Finset.sum_subset (s₁ := Finset.image e (Finset.univ : Finset m)) (Finset.subset_univ _) _]
  · refine (Finset.sum_image (s := Finset.univ)
      (f := fun x : n => padSquare e r G x a * padSquare e r G x b) (g := e)
      (fun x _ y _ h => hei h)).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [padSquare_apply e r her, padSquare_apply e r her]
  · intro x _ hx
    have h : x ∉ Set.range e := fun hc => hx (Finset.mem_image.mpr
      ⟨hc.choose, Finset.mem_univ _, hc.choose_spec⟩)
    simp only [padSquare, Matrix.of_apply, if_neg h, zero_mul]

/-- Нумерация конечного типа, согласованная с `IsHermitian.eigenvalues`. -/
noncomputable def enum (n : Type) [Fintype n] : n ≃ Fin (Fintype.card n) :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm

/-- `eigenvalues` занумерованы через `enum`. -/
lemma eigenvalues_enum {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i = hA.eigenvalues₀ (enum n i) := rfl

/-- Первые `card m` индексов типа `n` (в порядке `enum`). -/
noncomputable def leadingEmbedding (m : Type) [Fintype m] {n : Type} [Fintype n]
    (h : Fintype.card m ≤ Fintype.card n) : m → n :=
  fun i => (enum n).symm (Fin.castLE h ((enum m) i))

omit [DecidableEq m] [DecidableEq n] in
lemma leadingEmbedding_injective (m : Type) [Fintype m] {n : Type} [Fintype n]
    (h : Fintype.card m ≤ Fintype.card n) :
    Function.Injective (leadingEmbedding (n := n) (m := m) h) := by
  intro a b hab
  simpa only [leadingEmbedding, Equiv.symm_apply_eq, Fin.castLE_inj, Equiv.apply_eq_iff_eq]
    using hab

omit [DecidableEq m] in
lemma not_mem_range_leadingEmbedding (m : Type) [Fintype m] {n : Type} [Fintype n]
    (h : Fintype.card m ≤ Fintype.card n) {x : n}
    (hx : x ∉ Set.range (leadingEmbedding (n := n) (m := m) h)) :
    Fintype.card m ≤ enum n x := by
  by_contra hlt
  have hle : enum n x < Fintype.card m := by omega
  refine hx ⟨(enum m).symm ⟨enum n x, hle⟩, ?_⟩
  show (enum n).symm (Fin.castLE h ((enum m) ((enum m).symm ⟨enum n x, hle⟩))) = x
  simp only [Equiv.apply_symm_apply]
  exact Equiv.symm_apply_apply _ _

omit [DecidableEq m] in
/-- Антонатонный по `enum` кортеж `σ : n → ℝ` с числом ненулевых `≤ card m`
зануляется вне первых `card m` индексов. -/
lemma zeros_outside_leading (m : Type) [Fintype m] {n : Type} [Fintype n] [DecidableEq n]
    (σ : n → ℝ) (h0 : ∀ i, 0 ≤ σ i)
    (hanti : Antitone (fun j : Fin (Fintype.card n) => σ ((enum n).symm j)))
    (hcard : Fintype.card {i : n // σ i ≠ 0} ≤ Fintype.card m) (hmn : Fintype.card m ≤ Fintype.card n)
    {x : n} (hx : x ∉ Set.range (leadingEmbedding (n := n) (m := m) hmn)) : σ x = 0 := by
  have hle := not_mem_range_leadingEmbedding m hmn hx
  have hc : Fintype.card {j : Fin (Fintype.card n) // σ ((enum n).symm j) ≠ 0}
      ≤ Fintype.card m := by
    have hu : {j : Fin (Fintype.card n) // σ ((enum n).symm j) ≠ 0}
        ≃ {i : n // σ i ≠ 0} := Equiv.subtypeEquiv (enum n).symm (fun j => Iff.rfl)
    rw [Fintype.card_congr hu]
    exact hcard
  simpa using antitone_nonneg_zeros_after_rank _ hanti (fun j => h0 _) hc _ hle

omit [DecidableEq m] in
/-- Если `f` зануляется вне `range e`, то сумма по первым индексам равна полной. -/
lemma sum_leading (e : m → n) (hei : Function.Injective e) (f : n → ℝ)
    (h0 : ∀ c ∉ Set.range e, f c = 0) : ∑ j, f (e j) = ∑ c, f c := by
  classical
  refine Eq.trans (Finset.sum_image (s := (Finset.univ : Finset m)) (f := f) (g := e)
    (fun x _ y _ h => hei h)).symm ?_
  refine Finset.sum_subset (Finset.subset_univ _)
    (s₁ := Finset.image e (Finset.univ : Finset m)) (f := f) ?_
  intro c _ hc
  exact h0 c fun hc' => hc (Finset.mem_image.mpr ⟨hc'.choose, Finset.mem_univ _, hc'.choose_spec⟩)

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Корень из антонатонного неотрицательного кортежа антонатонен. -/
lemma antitone_real_sqrt_nonneg {ι : Type*} [Preorder ι] (f : ι → ℝ) (hf : Antitone f)
    (_h0 : ∀ i, 0 ≤ f i) : Antitone (fun i => Real.sqrt (f i)) :=
  fun _a _b hab => Real.sqrt_le_sqrt (hf hab)

set_option maxHeartbeats 1000000 in
/-- **`exists_wide_svd`**: для широкой вещественной `G : m×n` (`card m ≤ card n`)
существует прямоугольный SVD `G = U·diag σ·Vᵀ`, `U : m×m`, `V : n×m`,
`UᵀU = 1`, `VᵀV = 1`, `σ ≥ 0`. -/
theorem exists_wide_svd (G : Matrix m n ℝ) (hmn : Fintype.card m ≤ Fintype.card n) :
    ∃ (U : Matrix m m ℝ) (σ : m → ℝ) (V : Matrix n m ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ (∀ i, 0 ≤ σ i) ∧
      G = U * Matrix.diagonal σ * Vᵀ := by
  classical
  by_cases hm : IsEmpty m
  · have : IsEmpty m := hm
    haveI := this
    refine ⟨0, fun i => isEmptyElim i, 0, ?_, ?_, fun i => isEmptyElim i, ?_⟩ <;>
      · ext i j
        exact isEmptyElim i
  have : Nonempty m := not_isEmpty_iff.mp hm
  haveI := this
  obtain ⟨e, he⟩ : ∃ e : m → n, e = leadingEmbedding (m := m) (n := n) hmn := ⟨_, rfl⟩
  have hei : Function.Injective e := he ▸ leadingEmbedding_injective m hmn
  obtain ⟨r, her⟩ : ∃ r : n → m, ∀ i, r (e i) = i :=
    ⟨Function.invFun e, fun i => Function.leftInverse_invFun hei i⟩
  obtain ⟨Gp, hGp⟩ : ∃ Gp, Gp = padSquare e r G := ⟨_, rfl⟩
  obtain ⟨Uq, hUq⟩ : ∃ Uq : Matrix n n ℝ, Uq = (Matrix.SVD.Real.constructedU_real Gp : Matrix n n ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨Vq, hVq⟩ : ∃ Vq : Matrix n n ℝ, Vq = (Matrix.SVD.Real.rightOrthogonal Gp : Matrix n n ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : n → ℝ, s = Matrix.SVD.Real.realSingularValues Gp := ⟨_, rfl⟩
  have hs0 : ∀ i, 0 ≤ s i := by
    rw [hs]; exact fun i => Real.sqrt_nonneg _
  have hU : Uqᵀ * Uq = 1 := by
    have h := (Matrix.SVD.Real.constructedU_real Gp).2
    rw [Matrix.mem_orthogonalGroup_iff'] at h
    rw [hUq]; exact h
  have hV : Vqᵀ * Vq = 1 := by
    have h := (Matrix.SVD.Real.rightOrthogonal Gp).2
    rw [Matrix.mem_orthogonalGroup_iff'] at h
    rw [hVq]; exact h
  have hVV : Vq * Vqᵀ = 1 := by
    have h := (Matrix.SVD.Real.rightOrthogonal Gp).2
    rw [Matrix.mem_orthogonalGroup_iff] at h
    rw [hVq]; exact h
  have hAV : Gp * Vq = Uq * Matrix.diagonal s := by
    rw [hUq, hVq, hs]
    exact Matrix.SVD.Real.realAV_eq_constructedU_real_mul_sigma Gp
  have hdec : Gp = Uq * Matrix.diagonal s * Vqᵀ := by
    calc Gp = Gp * 1 := (mul_one _).symm
      _ = Gp * (Vq * Vqᵀ) := by rw [hVV]
      _ = (Gp * Vq) * Vqᵀ := (Matrix.mul_assoc _ _ _).symm
      _ = (Uq * Matrix.diagonal s) * Vqᵀ := by rw [hAV]
      _ = _ := rfl
  -- (i) нулевые σ — вне range e
  have hH : (Gpᵀ * Gp).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr (Matrix.SVD.Real.transpose_mul_self_isSymm _)
  have hrank : Fintype.card {i : n // s i ≠ 0} ≤ Fintype.card m := by
    have hcard : Fintype.card {i : n // s i ≠ 0}
        = Fintype.card {i : n // hH.eigenvalues i ≠ 0} := by
      rw [hs]
      refine Fintype.card_congr (Equiv.subtypeEquivRight fun i => ?_)
      have hnn := Matrix.SVD.Real.eigenvalues_transpose_mul_self_nonneg Gp i
      show (Matrix.SVD.Real.realSingularValues Gp i ≠ 0) ↔ _
      simp only [Matrix.SVD.Real.realSingularValues, ne_eq, Real.sqrt_eq_zero hnn]
    rw [hcard, ← hH.rank_eq_card_non_zero_eigs, hGp,
      padSquare_transpose_mul_self e r hei her G, Matrix.rank_transpose_mul_self]
    exact le_trans (Matrix.rank_le_card_height _) (by simp)
  have hz : ∀ x ∉ Set.range e, s x = 0 := by
    intro x hx
    refine zeros_outside_leading m s (fun i => hs0 i) ?_ hrank hmn (he ▸ hx)
    rw [hs]
    simp only [Matrix.SVD.Real.realSingularValues]
    refine antitone_real_sqrt_nonneg _ (fun a b hab => ?_) ?_
    · show hH.eigenvalues ((enum n).symm b) ≤ hH.eigenvalues ((enum n).symm a)
      have h := hH.eigenvalues₀_antitone hab
      rw [show b = enum n ((enum n).symm b) from (Equiv.symm_apply_apply _ _).symm,
        show a = enum n ((enum n).symm a) from (Equiv.symm_apply_apply _ _).symm] at h
      rw [eigenvalues_enum hH, eigenvalues_enum hH]
      exact h
    · exact fun j => Matrix.SVD.Real.eigenvalues_transpose_mul_self_nonneg _ _
  -- (ii) V₀ : n×m — первые card m столбцов Vq (изометрия)
  obtain ⟨V₀, hV₀def⟩ : ∃ V₀ : Matrix n m ℝ, ∀ a j, V₀ a j = Vq a (e j) :=
    ⟨Matrix.of fun a j => Vq a (e j), fun a j => rfl⟩
  have hV₀ : V₀ᵀ * V₀ = 1 := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hV₀def, Matrix.one_apply]
    have h1 : ∀ a b : n, ∑ x, Vq x a * Vq x b = (Vqᵀ * Vq) a b := fun a b => rfl
    have h2 : (Vqᵀ * Vq) (e i) (e k) = if e i = e k then 1 else 0 := by rw [hV, Matrix.one_apply]
    rw [h1 (e i) (e k), h2]
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg (hei.ne h), if_neg h]
  -- (iii) K := G·V₀ : m×m, и G = K·V₀ᵀ
  obtain ⟨K, hKdef⟩ : ∃ K : Matrix m m ℝ, ∀ i j, K i j = ∑ x, G i x * Vq x (e j) :=
    ⟨G * V₀, fun i j => by
      show (∑ x, G i x * V₀ x j) = _
      exact Finset.sum_congr rfl fun x _ => by rw [hV₀def]⟩
  have hKij : ∀ i j, K i j = s (e j) * Uq (e i) (e j) := by
    intro i j
    have h1 : ∀ (A : Matrix n n ℝ) a b, ∑ x, A a x * (Vq x b) = (A * Vq) a b :=
      fun A a b => rfl
    have hPV := congrFun (congrFun hAV (e i)) (e j)
    have hGi : ∀ x, G i x = Gp (e i) x := fun x => (hGp ▸ padSquare_apply e r her G i x).symm
    rw [hKdef i j]
    refine Eq.trans (Finset.sum_congr rfl fun x _ => by rw [hGi x]) ?_
    refine Eq.trans (h1 Gp (e i) (e j)) ?_
    rw [hPV]
    show (∑ x, Uq (e i) x * (if x = e j then s x else 0)) = _
    rw [Finset.sum_eq_single (e j) (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
    ring
  have hrow : ∀ i y, G i y = (K * V₀ᵀ) i y := by
    intro i y
    have h := congrFun (congrFun hdec (e i)) y
    rw [Matrix.mul_apply] at h
    have hGi : G i y = Gp (e i) y := (hGp ▸ padSquare_apply e r her G i y).symm
    refine Eq.trans hGi ?_
    calc Gp (e i) y = ∑ c, Uq (e i) c * s c * Vq y c := by
          rw [h]
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
          rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]
          simp
      _ = ∑ x, s (e x) * Uq (e i) (e x) * Vq y (e x) := by
          have hsl := sum_leading e hei (fun c => s c * Uq (e i) c * Vq y c)
            (fun c hc => by rw [hz c hc]; ring)
          exact (Finset.sum_congr rfl fun c _ => by ring).trans hsl.symm
      _ = ∑ x, K i x * Vq y (e x) := Finset.sum_congr rfl fun x _ => by rw [hKij i x]
      _ = (K * V₀ᵀ) i y := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun x _ => by rw [Matrix.transpose_apply, hV₀def]
  -- (iv) квадратный SVD для K : m×m и сборка
  obtain ⟨W, Ũ, sg, hsg0, hKdec⟩ := Matrix.SVD.Real.svd_decomposition K
  have hW := W.2
  have hŨ := Ũ.2
  rw [Matrix.mem_orthogonalGroup_iff'] at hW hŨ
  refine ⟨(W : Matrix m m ℝ), sg, V₀ * (Ũ : Matrix m m ℝ), hW, ?_, hsg0, ?_⟩
  · have h1 : ((Ũ : Matrix m m ℝ))ᵀ * (V₀ᵀ * (V₀ * (Ũ : Matrix m m ℝ))) = 1 := by
      rw [show V₀ᵀ * (V₀ * (Ũ : Matrix m m ℝ)) = (V₀ᵀ * V₀) * (Ũ : Matrix m m ℝ) from
        (Matrix.mul_assoc _ _ _).symm, hV₀, Matrix.one_mul, hŨ]
    rw [Matrix.transpose_mul]
    exact (Matrix.mul_assoc _ _ _).trans h1
  · have hG : G = K * V₀ᵀ := by ext i y; exact hrow i y
    rw [hG, hKdec]
    simp only [Matrix.mul_assoc, Matrix.transpose_mul]

/-- **`wide_iter_svd'`** (T1' без гипотезы разложения): итерации широкого шага
сохраняют сингулярные базисы некоторого прямоугольного SVD. -/
theorem wide_iter_svd' (G : Matrix m n ℝ) (hmn : Fintype.card m ≤ Fintype.card n) (k : ℕ) :
    ∃ (U : Matrix m m ℝ) (σ : m → ℝ) (V : Matrix n m ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ (∀ i, 0 ≤ σ i) ∧
      MuonWide.wide_iter k G
        = U * Matrix.diagonal (fun i => NewtonSchulzSigma.ns_seq k (σ i)) * Vᵀ := by
  obtain ⟨U, σ, V, hU, hV, hσ, hG⟩ := exists_wide_svd G hmn
  exact ⟨U, σ, V, hU, hV, hσ, MuonWide.ns_iter_wide_svd U V σ hU hV hG k⟩

/-- **`wide_alignment_exact'`** (T2 без гипотезы разложения): для некоторого
неотрицательного спектра `σ` выполнено `⟨G, X_k⟩ = Σ_i σ i·ns_seq k (σ i)`. -/
theorem wide_alignment_exact' (G : Matrix m n ℝ) (hmn : Fintype.card m ≤ Fintype.card n)
    (k : ℕ) :
    ∃ σ : m → ℝ, (∀ i, 0 ≤ σ i) ∧
      MuonWide.fdot_wide G (MuonWide.wide_iter k G)
        = ∑ i, σ i * NewtonSchulzSigma.ns_seq k (σ i) := by
  obtain ⟨U, σ, V, hU, hV, hσ, hG⟩ := exists_wide_svd G hmn
  exact ⟨σ, hσ, MuonWide.wide_alignment_exact U V σ hU hV hG k⟩

/-- **`wide_step_optimal'`** (T4–T5 без гипотезы разложения): среди строчных
изометрий `ΔΔᵀ = 1` максимум `⟨G, Δ⟩` равен `Σ σ i` (для спектра `σ` из
`exists_wide_svd`) и достигается на полярном факторе `U Vᵀ`. -/
theorem wide_step_optimal' (G : Matrix m n ℝ) (hmn : Fintype.card m ≤ Fintype.card n) :
    ∃ (σ : m → ℝ) (P : Matrix m n ℝ),
      (∀ i, 0 ≤ σ i) ∧ P * Pᵀ = 1 ∧ MuonWide.fdot_wide G P = ∑ i, σ i ∧
      ∀ Δ : Matrix m n ℝ, Δ * Δᵀ = 1 → MuonWide.fdot_wide G Δ ≤ ∑ i, σ i := by
  obtain ⟨U, σ, V, hU, hV, hσ, hG⟩ := exists_wide_svd G hmn
  obtain ⟨hle, Δ, hΔ, heq⟩ := MuonWide.wide_step_optimal U V σ hG hU
    (mul_eq_one_comm.mp hU) hV hσ
  exact ⟨σ, Δ, hσ, hΔ, heq, hle⟩

/-! ### C680: нормировка широкого градиента (S1) и сертификат спуска (S3)

Короткий путь: `Σ σ i² = ‖G‖_F²` для спектра из `exists_wide_svd`, поэтому
`wsmax`/`padSquare`-оценки не нужны — `σ i ≤ √(Σ σ²)`. -/

/-- Frobenius-норма в квадрате для `m×n`. -/
noncomputable def wfrobSq (G : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, G i j ^ 2

/-- Нормированный широкий градиент кода: `Ĝ = G/‖G‖_F` (core.py:1353). -/
noncomputable def wnormed (G : Matrix m n ℝ) : Matrix m n ℝ :=
  (1 / Real.sqrt (wfrobSq G)) • G

omit [DecidableEq m] [DecidableEq n] in
lemma wfrobSq_nonneg (G : Matrix m n ℝ) : 0 ≤ wfrobSq G :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq m] [DecidableEq n] in
lemma wfrobSq_pos {G : Matrix m n ℝ} (hG : G ≠ 0) : 0 < wfrobSq G := by
  by_contra h0
  have h1 : wfrobSq G = 0 := le_antisymm (by linarith) (wfrobSq_nonneg G)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp h1
  refine hG (funext fun i => funext fun j => ?_)
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => sq_nonneg _)).mp (hz i (Finset.mem_univ i))
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hi j (Finset.mem_univ j))

omit [DecidableEq m] [DecidableEq n] in
lemma fdot_wide_smul_left (G Δ : Matrix m n ℝ) (c : ℝ) :
    MuonWide.fdot_wide (c • G) Δ = c * MuonWide.fdot_wide G Δ := by
  simp only [MuonWide.fdot_wide, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq m] [DecidableEq n] in
lemma fdot_wide_smul_right (G Δ : Matrix m n ℝ) (c : ℝ) :
    MuonWide.fdot_wide G (c • Δ) = c * MuonWide.fdot_wide G Δ := by
  simp only [MuonWide.fdot_wide, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq m] [DecidableEq n] in
lemma wfrobSq_smul (G : Matrix m n ℝ) (c : ℝ) : wfrobSq (c • G) = c ^ 2 * wfrobSq G := by
  have h : ∀ i j, ((c • G) i j) ^ 2 = c ^ 2 * G i j ^ 2 := fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul]; ring
  simp only [wfrobSq, h, ← Finset.mul_sum]

/-- Носитель: `‖G‖_F² = Σ_i σ i²` для спектра любого широкого SVD `G`. -/
lemma wfrobSq_eq_sum_sigma_sq (U : Matrix m m ℝ) (V : Matrix n m ℝ) (σ : m → ℝ)
    (hUt : Uᵀ * U = 1) (hVt : Vᵀ * V = 1) {G : Matrix m n ℝ}
    (hG : G = U * Matrix.diagonal σ * Vᵀ) : wfrobSq G = ∑ i, σ i ^ 2 := by
  have h1 : wfrobSq G = (Gᵀ * G).trace := by
    simp only [wfrobSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => sq (G j i)
  have h2 : Gᵀ * G = V * Matrix.diagonal (fun i => σ i * σ i) * Vᵀ := by
    rw [hG]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hUt, Matrix.one_mul,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal σ), Matrix.diagonal_mul_diagonal]
  rw [h1, h2, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hVt, Matrix.mul_one]
  simp [Matrix.trace, Matrix.diag_apply, sq]

/-- **(S1) `wnormed_sigma_le_one`**: для `G ≠ 0` (широкая) спектр нормированного
градиента `Ĝ = G/‖G‖_F` в любом разложении `Ĝ = U·diag σ·Vᵀ` с
изометриями лежит в `[0, 1]` — посылка `σ ≤ 1` теоремы T3 снята. -/
theorem wnormed_sigma_le_one {G : Matrix m n ℝ} (hG : G ≠ 0) (U : Matrix m m ℝ) (σ : m → ℝ)
    (V : Matrix n m ℝ) (hUt : Uᵀ * U = 1) (hVt : Vᵀ * V = 1)
    (hGn : wnormed G = U * Matrix.diagonal σ * Vᵀ) (i : m) : 0 ≤ σ i ^ 2 ∧ σ i ^ 2 ≤ 1 := by
  have hs : 0 < Real.sqrt (wfrobSq G) := Real.sqrt_pos.2 (wfrobSq_pos hG)
  have h1 : wfrobSq (wnormed G) = 1 := by
    rw [wnormed, wfrobSq_smul, div_pow, one_pow, Real.sq_sqrt (wfrobSq_nonneg G)]
    exact div_mul_cancel₀ 1 (ne_of_gt (wfrobSq_pos hG))
  rw [wfrobSq_eq_sum_sigma_sq U V σ hUt hVt hGn] at h1
  refine ⟨sq_nonneg _, ?_⟩
  have hle : σ i ^ 2 ≤ ∑ j : m, σ j ^ 2 := Finset.single_le_sum (s := Finset.univ) (a := i)
    (f := fun j => σ j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

/-- **(S1) `wnormed_inner_eq_one`**: `⟨Ĝ, Ĝ⟩ = 1`. -/
theorem wnormed_inner_eq_one {G : Matrix m n ℝ} (hG : G ≠ 0) :
    MuonWide.fdot_wide (wnormed G) (wnormed G) = 1 := by
  have hs : 0 < Real.sqrt (wfrobSq G) := Real.sqrt_pos.2 (wfrobSq_pos hG)
  have hF : MuonWide.fdot_wide G G = wfrobSq G := by
    simp only [MuonWide.fdot_wide, wfrobSq]; exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => (sq (G i j)).symm
  rw [wnormed, fdot_wide_smul_right, fdot_wide_smul_left, hF]
  field_simp [Real.sq_sqrt (wfrobSq_nonneg G)]
  exact (Real.sq_sqrt (wfrobSq_nonneg G)).symm

/-- **(S1) `wide_alignment_ge_gradient'`** (T3 без гипотез): для широкой
`G ≠ 0` `⟨Ĝ, Ĝ⟩ ≤ ⟨Ĝ, wide_iter k Ĝ⟩`, т.е. в единицах `G`:
`‖G‖_F ≤ ⟨G, wide_iter k Ĝ⟩`. -/
theorem wide_alignment_ge_gradient' (G : Matrix m n ℝ) (hmn : Fintype.card m ≤ Fintype.card n)
    (hG : G ≠ 0) (k : ℕ) :
    MuonWide.fdot_wide (wnormed G) (wnormed G)
        ≤ MuonWide.fdot_wide (wnormed G) (MuonWide.wide_iter k (wnormed G)) ∧
      Real.sqrt (wfrobSq G) ≤ MuonWide.fdot_wide G (MuonWide.wide_iter k (wnormed G)) := by
  obtain ⟨U, σ, V, hU, hV, hσ0, hdec⟩ := exists_wide_svd (wnormed G) hmn
  have hσ1 := wnormed_sigma_le_one hG U σ V hU hV hdec
  have hσ : ∀ i, 0 ≤ σ i ∧ σ i ≤ 1 := fun i =>
    ⟨hσ0 i, by nlinarith [hσ0 i, (hσ1 i).2]⟩
  have h1 := MuonWide.wide_alignment_ge_gradient U V σ hU hV hdec k hσ
  refine ⟨h1, ?_⟩
  have hs : 0 < Real.sqrt (wfrobSq G) := Real.sqrt_pos.2 (wfrobSq_pos hG)
  have h1' : 1 ≤ MuonWide.fdot_wide (wnormed G) (MuonWide.wide_iter k (wnormed G)) := by
    rw [← wnormed_inner_eq_one hG]; exact h1
  have he : MuonWide.fdot_wide G (MuonWide.wide_iter k (wnormed G))
      = Real.sqrt (wfrobSq G) * MuonWide.fdot_wide (wnormed G) (MuonWide.wide_iter k (wnormed G)) := by
    rw [wnormed, fdot_wide_smul_left]
    field_simp
  rw [he]
  calc Real.sqrt (wfrobSq G) = Real.sqrt (wfrobSq G) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h1' hs.le

/-- **(S3) `muon_step_useful_wide`** — сертификат спуска широкого Muon-шага.
Носитель — координатное пространство `W Δ : m → n → ℝ` (для прямоугольной
`Matrix m n ℝ` нормированного пространства в репо нет; `Matrix m n ℝ` —
то же координатное пространство). Если `f` дифференцируема в `W`
с дифференциалом `φ`, `φ Δ = ⟨G, Δ⟩` (широкое спаривание), и `G ≠ 0`, то для
малого `η` шаг кода `W ← W − η·wide_iter k Ĝ` строго убывает `f`. -/
theorem muon_step_useful_wide (G W : Matrix m n ℝ) (hmn : Fintype.card m ≤ Fintype.card n)
    (f : (m → n → ℝ) → ℝ) (φ : (m → n → ℝ) →L[ℝ] ℝ) (hL : HasFDerivAt f φ (fun i j => W i j))
    (hφ : ∀ Δ : m → n → ℝ, φ Δ = MuonWide.fdot_wide G Δ) (hG : G ≠ 0) (k : ℕ) :
    ∃ η : ℝ, 0 < η ∧
      f (fun i j => W i j - η * MuonWide.wide_iter k (wnormed G) i j) < f (fun i j => W i j) := by
  have h1 := (wide_alignment_ge_gradient' G hmn hG k).2
  have hpos : 0 < MuonWide.fdot_wide G (MuonWide.wide_iter k (wnormed G)) :=
    lt_of_lt_of_le (Real.sqrt_pos.2 (wfrobSq_pos hG)) h1
  have hneg : φ (-(fun i j => MuonWide.wide_iter k (wnormed G) i j)) < 0 := by
    rw [map_neg, hφ]; exact neg_neg_of_pos hpos
  obtain ⟨η, hη, hlt⟩ := Hagi.Theory.MuonDescent.useful_of_neg_fderiv
    (f := f) (x := fun i j => W i j) (d := -(fun i j => MuonWide.wide_iter k (wnormed G) i j)) (φ := φ) hL hneg
  refine ⟨η, hη, ?_⟩
  have heq : ((fun i j => W i j) + η • -(fun i j => MuonWide.wide_iter k (wnormed G) i j))
      = fun i j => W i j - η * MuonWide.wide_iter k (wnormed G) i j := by
    funext i j
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; ring

  rwa [heq] at hlt

end Hagi.Theory.WideSVD
