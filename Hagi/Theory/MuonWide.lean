/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.MuonAlignment

/-!
# MuonWide — прямоугольный шаг Muon: широкая форма, сингулярные базисы, оптимум

C678. Слой кода `W1 : dim × hidden` прямоугольный, и
`newton_schulz_orthogonalize` (hagi/core.py:1349 @ca52eb4) приводит градиент
к «широкой» форме `m ≤ n`: если строк больше столбцов — транспонирует
(core.py:1358), итерирует `X = 0.5 * (3.0 * I_m - X @ X.T) @ X`
(core.py:1363) и транспонирует обратно. Здесь `X : Matrix m n ℝ`,
`G = U·diag σ·Vᵀ` с `U : m×m`, `V : n×m`, `UᵀU = VᵀV = 1`.

* `code_step`, `code_step_eq_ns_step` — (K) строка core.py:1363 равна
  `NewtonSchulzSigma.ns_step` (правая форма `X(3I − XᵀX)/2`).
* `ns_step_wide_svd` — (T1) `X = U·diag τ·Vᵀ ⇒ ns_step X = U·diag (ns_p∘τ)·Vᵀ`.
* `wide_iter`, `ns_iter_wide_svd` — (T1') `X_k = U·diag (ns_seq k∘σ)·Vᵀ`.
* `fdot_wide`, `wide_alignment_exact` — (T2) `⟨G, X_k⟩ = Σ_i σ i·ns_seq k (σ i)`.
* `wide_alignment_ge_gradient` — (T3) `σ ≤ 1 ⇒ ⟨G, G⟩ ≤ ⟨G, X_k⟩`.
* `wide_row_isometry` — (T4) `U Vᵀ` — строчная изометрия `Y Yᵀ = 1`.
* `wide_inner_le_sigma_sum`, `wide_step_optimal` — (T5) среди строчных
  изометрий `ΔΔᵀ = 1` максимум `⟨G, Δ⟩` равен `Σ σ i`, достигается на `U Vᵀ`.
* `ns_step_transpose`, `wide_iter_transpose`, `code_ns_eq_wide_iter` — (C680)
  высокий случай `m > n`: код-выход для любой формы равен `wide_iter k G`.

Честная граница: разложение `G = U·diag σ·Vᵀ` — ГИПОТЕЗА теорем этого модуля;
существование доказано в C679 (`WideSVD.exists_wide_svd`, там же T3 без
посылок и сертификат спуска, C680). Проверка `norm < 1e-12 → return X`
(core.py:1355), число итераций (по умолчанию 4, вызов 3, core.py:1755),
обновление `W1` и мост к функциональному носителю C676 не формализованы.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.MuonWide

open scoped BigOperators
open Matrix NewtonSchulzSigma

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Строка кода core.py:1363: `X = 0.5 * (3.0 * I_m - X @ X.T) @ X`. -/
noncomputable def code_step (X : Matrix m n ℝ) : Matrix m n ℝ :=
  (1 / 2 : ℝ) • ((3 : ℝ) • 1 - X * Xᵀ) * X

/-- **`code_step_eq_ns_step`** (K): строка кода равна `ns_step` — правой
форме `X(3I − XᵀX)/2` (равенство `(3I − XXᵀ)X = X(3I − XᵀX)`). -/
theorem code_step_eq_ns_step (X : Matrix m n ℝ) :
    code_step X = NewtonSchulzSigma.ns_step X := by
  simp only [code_step, NewtonSchulzSigma.ns_step, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have hc : (1 / 2 : ℝ) * (3 : ℝ) = (3 : ℝ) * (1 / 2) := mul_comm _ _
  rw [smul_sub, smul_smul, smul_smul, hc, Matrix.mul_assoc]

set_option linter.unusedSimpArgs false in
/-- **`ns_step_wide_svd`** (T1): широкий шаг делит сингулярные базисы. -/
theorem ns_step_wide_svd (U : Matrix m m ℝ) (V : Matrix n m ℝ) (τ : m → ℝ)
    (hUt : Uᵀ * U = 1) (hVt : Vᵀ * V = 1)
    {X : Matrix m n ℝ} (hX : X = U * Matrix.diagonal τ * Vᵀ) :
    NewtonSchulzSigma.ns_step X
      = U * Matrix.diagonal (fun i => NewtonSchulzSigma.ns_p (τ i)) * Vᵀ := by
  rw [NewtonSchulzSigma.ns_step, hX]
  have hd : Matrix.diagonal τ * Matrix.diagonal τ
      = Matrix.diagonal (fun i => τ i * τ i) := Matrix.diagonal_mul_diagonal _ _
  have hXX : ((U * Matrix.diagonal τ * Vᵀ)ᵀ * (U * Matrix.diagonal τ * Vᵀ))
      = V * Matrix.diagonal (fun i => τ i * τ i) * Vᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hUt, Matrix.one_mul]
    have hd2 : Matrix.diagonal τ * (Matrix.diagonal τ * Vᵀ)
        = Matrix.diagonal (fun i => τ i * τ i) * Vᵀ := by
      rw [← Matrix.mul_assoc, hd]
    rw [hd2, ← Matrix.mul_assoc V]
  have hX3 : (U * Matrix.diagonal τ * Vᵀ) * ((3 : ℝ) • (1 : Matrix n n ℝ))
      = (3 : ℝ) • (U * Matrix.diagonal τ * Vᵀ) := by
    rw [Matrix.mul_smul, Matrix.mul_one]
  have hXD : (U * Matrix.diagonal τ * Vᵀ)
      * (V * Matrix.diagonal (fun i => τ i * τ i) * Vᵀ)
      = U * (Matrix.diagonal τ * Matrix.diagonal (fun i => τ i * τ i)) * Vᵀ := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, hVt, Matrix.one_mul]
  have hB : U * ((3 : ℝ) • Matrix.diagonal τ
        - Matrix.diagonal τ * Matrix.diagonal (fun i => τ i * τ i)) * Vᵀ
      = (3 : ℝ) • (U * Matrix.diagonal τ * Vᵀ)
        - U * (Matrix.diagonal τ * Matrix.diagonal (fun i => τ i * τ i)) * Vᵀ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hD : (3 : ℝ) • Matrix.diagonal τ
        - Matrix.diagonal τ * Matrix.diagonal (fun i => τ i * τ i)
      = Matrix.diagonal (fun i => 3 * τ i - τ i * (τ i * τ i)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply,
        Finset.sum_ite_eq']
    · simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, h,
        Finset.sum_ite_eq']
  have hDE : (1 / 2 : ℝ) • Matrix.diagonal (fun i => 3 * τ i - τ i * (τ i * τ i))
      = Matrix.diagonal (fun i => NewtonSchulzSigma.ns_p (τ i)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.smul_apply, Matrix.diagonal_apply, NewtonSchulzSigma.ns_p, smul_eq_mul, reduceIte]
      ring
    · simp [Matrix.smul_apply, Matrix.diagonal_apply, h]
  rw [hXX, Matrix.mul_sub, Matrix.smul_mul, Matrix.smul_mul, hX3, hXD, ← smul_sub, ← hB,
    Matrix.mul_assoc U, ← Matrix.mul_smul U, ← Matrix.smul_mul,
    Matrix.mul_assoc U, hD, hDE]

/-- k итераций кодового шага: `wide_iter k X = ns_step^[k] X`. -/
noncomputable def wide_iter (k : ℕ) (X : Matrix m n ℝ) : Matrix m n ℝ :=
  (NewtonSchulzSigma.ns_step)^[k] X

/-- **`ns_iter_wide_svd`** (T1'): все итерации имеют те же сингулярные базисы. -/
theorem ns_iter_wide_svd (U : Matrix m m ℝ) (V : Matrix n m ℝ) (σ : m → ℝ)
    (hUt : Uᵀ * U = 1) (hVt : Vᵀ * V = 1)
    {G : Matrix m n ℝ} (hG : G = U * Matrix.diagonal σ * Vᵀ) (k : ℕ) :
    wide_iter k G = U * Matrix.diagonal (fun i => NewtonSchulzSigma.ns_seq k (σ i)) * Vᵀ := by
  induction k with
  | zero => simp [wide_iter, hG, NewtonSchulzSigma.ns_seq]
  | succ k ih =>
      rw [wide_iter, Function.iterate_succ_apply']
      have h0 : (NewtonSchulzSigma.ns_step)^[k] G
          = U * Matrix.diagonal (fun i => NewtonSchulzSigma.ns_seq k (σ i)) * Vᵀ := by
        simpa [wide_iter] using ih
      have h1 := ns_step_wide_svd U V _ hUt hVt (hX := h0)
      simpa [NewtonSchulzSigma.ns_seq] using h1

/-- Скалярное произведение Фробениуса на `m×n`: `⟨G, Y⟩ = Σ_i Σ_j G i j·Y i j`. -/
noncomputable def fdot_wide (G Y : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, G i j * Y i j

omit [DecidableEq m] [DecidableEq n] in
/-- Носитель: `⟨G, Y⟩ = tr(GᵀY)`. -/
lemma fdot_wide_eq_trace (G Y : Matrix m n ℝ) :
    fdot_wide G Y = (Gᵀ * Y).trace := by
  simp only [fdot_wide, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
set_option linter.unusedSimpArgs false in
/-- Носитель: `⟨G, Y⟩ = Σ_i σ i·(UᵀYV) i i`. -/
lemma wide_inner_eq_sigma_weighted_diag (U : Matrix m m ℝ) (V : Matrix n m ℝ) (σ : m → ℝ)
    (G Y : Matrix m n ℝ) (hG : G = U * Matrix.diagonal σ * Vᵀ) :
    fdot_wide G Y = ∑ i, σ i * (Uᵀ * Y * V) i i := by
  rw [fdot_wide_eq_trace]
  have h1 : Gᵀ * Y = V * Matrix.diagonal σ * (Uᵀ * Y) := by
    rw [hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose]
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.mul_assoc, Matrix.trace_mul_comm V, Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]
  have h2 : ∀ (Q : Matrix m m ℝ) (i : m), (Matrix.diagonal σ * Q) i i = σ i * Q i i := by
    intro Q i
    simp only [Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun j _ hj => by rw [if_neg (Ne.symm hj), zero_mul])]
    simp
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_assoc, h2]

/-- **`wide_alignment_exact`** (T2): точное выравнивание
`⟨G, X_k⟩ = Σ_i σ i·ns_seq k (σ i)`. -/
theorem wide_alignment_exact (U : Matrix m m ℝ) (V : Matrix n m ℝ) (σ : m → ℝ)
    (hUt : Uᵀ * U = 1) (hVt : Vᵀ * V = 1)
    {G : Matrix m n ℝ} (hG : G = U * Matrix.diagonal σ * Vᵀ) (k : ℕ) :
    fdot_wide G (wide_iter k G)
      = ∑ i, σ i * NewtonSchulzSigma.ns_seq k (σ i) := by
  have hX := ns_iter_wide_svd U V σ hUt hVt hG k
  have hQ : Uᵀ * (wide_iter k G) * V
      = Matrix.diagonal (fun i => NewtonSchulzSigma.ns_seq k (σ i)) := by
    simp only [hX, ← Matrix.mul_assoc, hUt, Matrix.one_mul]
    rw [Matrix.mul_assoc, hVt, Matrix.mul_one]
  rw [wide_inner_eq_sigma_weighted_diag U V σ G (wide_iter k G) hG, hQ]
  simp

/-- **`wide_alignment_ge_gradient`** (T3): при `σ i ∈ [0, 1]` широкий шаг NS
не хуже градиентного: `⟨G, G⟩ ≤ ⟨G, X_k⟩`. -/
theorem wide_alignment_ge_gradient (U : Matrix m m ℝ) (V : Matrix n m ℝ) (σ : m → ℝ)
    (hUt : Uᵀ * U = 1) (hVt : Vᵀ * V = 1)
    {G : Matrix m n ℝ} (hG : G = U * Matrix.diagonal σ * Vᵀ) (k : ℕ)
    (hσ : ∀ i, 0 ≤ σ i ∧ σ i ≤ 1) :
    fdot_wide G G ≤ fdot_wide G (wide_iter k G) := by
  have h0 := wide_alignment_exact U V σ hUt hVt hG 0
  simp only [NewtonSchulzSigma.ns_seq] at h0
  change fdot_wide G (wide_iter 0 G) ≤ fdot_wide G (wide_iter k G)
  rw [h0, wide_alignment_exact U V σ hUt hVt hG k]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (NewtonSchulzSigma.ns_seq_bounds (hσ i).1 (hσ i).2 k).1 (hσ i).1

omit [DecidableEq n] in
/-- **`wide_row_isometry`** (T4): полярный фактор `U Vᵀ` — строчная изометрия
`Y Yᵀ = 1` (то, к чему сходится итерация при `σ → 1`). -/
theorem wide_row_isometry (U : Matrix m m ℝ) (V : Matrix n m ℝ)
    (hU : U * Uᵀ = 1) (hVt : Vᵀ * V = 1) :
    (U * Vᵀ) * (U * Vᵀ)ᵀ = 1 := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc U Vᵀ (V * Uᵀ), ← Matrix.mul_assoc Vᵀ V Uᵀ, hVt, Matrix.one_mul, hU]

/-- Носитель: столбец матрицы с ортонормальными столбцами имеет норму 1. -/
lemma col_sq_eq_one {p q : Type} [Fintype p] [Fintype q] [DecidableEq q] (M : Matrix p q ℝ)
    (hM : Mᵀ * M = 1) (k : q) : ∑ l, M l k * M l k = 1 := by
  have h : ∑ l, M l k * M l k = (Mᵀ * M) k k := by
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  rw [h, hM, Matrix.one_apply]
  simp

omit [DecidableEq n] in
/-- **`wide_inner_le_sigma_sum`** (T5, граница): для строчной изометрии
`ΔΔᵀ = 1` выполнено `⟨G, Δ⟩ ≤ Σ σ i` (Cauchy–Schwarz: `Δᵀ` — изометрия). -/
theorem wide_inner_le_sigma_sum (U : Matrix m m ℝ) (V : Matrix n m ℝ) (σ : m → ℝ)
    {G : Matrix m n ℝ} (hG : G = U * Matrix.diagonal σ * Vᵀ)
    (hUt : Uᵀ * U = 1) (hVt : Vᵀ * V = 1) (Δ : Matrix m n ℝ) (hΔ : Δ * Δᵀ = 1)
    (hσ : ∀ i, 0 ≤ σ i) :
    fdot_wide G Δ ≤ ∑ i, σ i := by
  have h1 : ∀ i, (Uᵀ * Δ * V) i i ≤ 1 := by
    intro i
    set a : n → ℝ := Δᵀ.mulVec (fun l => U l i) with ha
    have hq : (Uᵀ * Δ * V) i i = ∑ k, a k * V k i := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, ha, Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun k _ =>
        congrArg (· * V k i) (Finset.sum_congr rfl fun l _ => mul_comm (U l i) (Δ l k))
    -- ‖a‖² = ⟨Δᵀu, Δᵀu⟩ = ⟨u, ΔΔᵀu⟩ = ‖u‖² = 1
    have hdot : a ⬝ᵥ a = (fun l => U l i) ⬝ᵥ (fun l => U l i) := by
      calc a ⬝ᵥ a = a ⬝ᵥ (Δᵀ *ᵥ (fun l => U l i)) := by rw [ha]
        _ = a ᵥ* Δᵀ ⬝ᵥ (fun l => U l i) := Matrix.dotProduct_mulVec _ _ _
        _ = (Δ *ᵥ a) ⬝ᵥ (fun l => U l i) := by rw [Matrix.vecMul_transpose]
        _ = ((Δ * Δᵀ) *ᵥ (fun l => U l i)) ⬝ᵥ (fun l => U l i) := by
              rw [ha, Matrix.mulVec_mulVec]
        _ = (fun l => U l i) ⬝ᵥ (fun l => U l i) := by rw [hΔ, Matrix.one_mulVec]
    have haa : ∑ k, a k ^ 2 = 1 := by
      refine Eq.trans (Finset.sum_congr rfl fun k _ => sq (a k)) ?_
      exact hdot.trans (col_sq_eq_one U hUt i)
    have hbb : ∑ k, V k i ^ 2 = 1 :=
      (Finset.sum_congr rfl fun k _ => sq (V k i)).trans (col_sq_eq_one V hVt i)
    have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun k => V k i)
    rw [haa, hbb, mul_one] at hs
    rw [hq]
    exact le_trans (le_abs_self _) ((sq_le_one_iff_abs_le_one _).1 hs)
  rw [wide_inner_eq_sigma_weighted_diag U V σ G Δ hG]
  exact Finset.sum_le_sum fun i _ => by simpa using mul_le_mul_of_nonneg_left (h1 i) (hσ i)

omit [DecidableEq n] in
/-- **`wide_step_optimal`** (T5): среди строчных изометрий `ΔΔᵀ = 1`
максимум `⟨G, Δ⟩` равен `Σ σ i`; достигается на `Δ = U Vᵀ`. -/
theorem wide_step_optimal (U : Matrix m m ℝ) (V : Matrix n m ℝ) (σ : m → ℝ)
    {G : Matrix m n ℝ} (hG : G = U * Matrix.diagonal σ * Vᵀ)
    (hUt : Uᵀ * U = 1) (hU : U * Uᵀ = 1) (hVt : Vᵀ * V = 1) (hσ : ∀ i, 0 ≤ σ i) :
    (∀ Δ : Matrix m n ℝ, Δ * Δᵀ = 1 → fdot_wide G Δ ≤ ∑ i, σ i) ∧
      ∃ Δ : Matrix m n ℝ, Δ * Δᵀ = 1 ∧ fdot_wide G Δ = ∑ i, σ i := by
  refine ⟨fun Δ hΔ => wide_inner_le_sigma_sum U V σ hG hUt hVt Δ hΔ hσ, U * Vᵀ,
    wide_row_isometry U V hU hVt, ?_⟩
  have hQ : Uᵀ * (U * Vᵀ) * V = 1 := by
    simp only [Matrix.mul_assoc, hVt, hUt, Matrix.mul_one]
  rw [wide_inner_eq_sigma_weighted_diag U V σ G (U * Vᵀ) hG, hQ]
  simp

/-! ### C680: высокий случай — транспонирование коммутирует с шагом -/

/-- **`ns_step_transpose`** (S2, C680): транспонирование коммутирует с шагом
NS для любых форм: `ns_step Xᵀ = (ns_step X)ᵀ`. -/
theorem ns_step_transpose (X : Matrix m n ℝ) :
    NewtonSchulzSigma.ns_step Xᵀ = (NewtonSchulzSigma.ns_step X)ᵀ := by
  simp only [NewtonSchulzSigma.ns_step, Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]

/-- **`wide_iter_transpose`** (S2): все итерации коммутируют с транспонированием. -/
theorem wide_iter_transpose (k : ℕ) (X : Matrix m n ℝ) :
    wide_iter k Xᵀ = (wide_iter k X)ᵀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [wide_iter, wide_iter, Function.iterate_succ_apply', Function.iterate_succ_apply']
      change ns_step (wide_iter k Xᵀ) = (ns_step (wide_iter k X))ᵀ
      rw [ih]
      exact ns_step_transpose _

/-- Кодовый выход итераций newton_schulz_orthogonalize (core.py:1358–1361):
при `m > n` — транспонировать, итерировать, транспонировать обратно. -/
noncomputable def code_ns (k : ℕ) (G : Matrix m n ℝ) : Matrix m n ℝ :=
  if Fintype.card m > Fintype.card n then (wide_iter k Gᵀ)ᵀ else wide_iter k G

/-- **`code_ns_eq_wide_iter`** (S2): для ЛЮБОЙ формы `G : m×n` код-выход равен
`wide_iter k G` — единая формула для широкой и высокой матрицы;
транспонирование в коде — только эффективность (I_m вместо I_n). -/
theorem code_ns_eq_wide_iter (k : ℕ) (G : Matrix m n ℝ) : code_ns k G = wide_iter k G := by
  unfold code_ns
  split
  · rw [wide_iter_transpose k G, Matrix.transpose_transpose]
  · rfl

end Hagi.Theory.MuonWide
