/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.MuonIsometry
import Hagi.Theory.NewtonSchulzSigma

/-!
# MuonAlignment — Newton–Schulz делит сингулярные векторы с градиентом: точное выравнивание

Шаг кода `X ← (1/2)·X(3I − XᵀX)`
(hagi/core.py:1363 @ca52eb4) — правое умножение на матрицу, симметричную
относительно `X`, поэтому `X_k = U·diag(ns_seq k ∘ σ)·Vᵀ`: итерации НЕ
сходятся к произвольной изометрии, а сохраняют сингулярные векторы `G`, и
`Q = UᵀX_kV` ДИАГОНАЛЬНА. Отсюда `⟨G, X_k⟩ = Σ_i σ i·ns_seq k (σ i)`
(без σ_min и без леммы о диагонали): каждая компонента спектра взвешена
своим скалярным образом. С `ns_sigma_min_three` (`σ₀ ∈ [1/2, 1] ⇒ σ₃ ≥ 39/40`) это даёт
почти оптимальность на массе спектра с `σ ≥ 1/2`.

* `ns_iter` — `k` итераций шага кода.
* `ns_step_svd` — (T1) `X = U·diag τ·Vᵀ ⇒ ns_step X = U·diag (ns_p∘τ)·Vᵀ`.
* `ns_iter_svd` — (T1') `X_k = U·diag (ns_seq k∘σ)·Vᵀ`.
* `muon_alignment_exact` — (T2) `⟨G, X_k⟩ = Σ_i σ i·ns_seq k (σ i)`.
* `kept`, `muon_near_optimal` — (T3) `σ ≤ 1 ⇒ ⟨G, X₃⟩ ≥ (39/40)·Σ_{σ i ≥ 1/2} σ i`.
* `muon_alignment_ge_gradient` — (T4) `σ ≤ 1 ⇒ ⟨G, X_k⟩ ≥ ⟨G, G⟩`.

Честная граница: гипотеза `σ i ≤ 1` — нормировка Frobenius (core.py:1353)
формализована лишь как `smax ≤ ‖G‖_F`, не как `σ i ≤ 1` для
нормированного `G`; малые `σ i < 1/2` в T3 не учитываются (они и не
поднимаются за 3 итерации); множитель шага `η = cos_lr·0.7`, прямоугольный
`G`, обновление `W1` (core.py:1755) не формализованы.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.MuonAlignment

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

set_option linter.unusedSimpArgs false in
theorem ns_step_svd (U V : Matrix n n ℝ) (τ : n → ℝ)
    (hUt : Uᵀ * U = 1) (hVt : Vᵀ * V = 1) (hV : V * Vᵀ = 1)
    {X : Matrix n n ℝ} (hX : X = U * Matrix.diagonal τ * Vᵀ) :
    NewtonSchulzSigma.ns_step X
      = U * Matrix.diagonal (fun i => NewtonSchulzSigma.ns_p (τ i)) * Vᵀ := by
  set E := (3 : ℝ) • 1 - Matrix.diagonal τ * Matrix.diagonal τ with hE
  rw [NewtonSchulzSigma.ns_step, hX]
  have hXX : ((U * Matrix.diagonal τ * Vᵀ)ᵀ * (U * Matrix.diagonal τ * Vᵀ))
      = V * (Matrix.diagonal τ * Matrix.diagonal τ) * Vᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hUt, Matrix.one_mul,
      Matrix.mul_assoc U, Matrix.mul_assoc U]
  have h3 : V * ((3 : ℝ) • 1) * Vᵀ = (3 : ℝ) • 1 := by
    rw [Matrix.mul_smul V (3 : ℝ) 1, Matrix.mul_one, Matrix.smul_mul (3 : ℝ) V Vᵀ, hV]
  have hst : ((3 : ℝ) • 1 - V * (Matrix.diagonal τ * Matrix.diagonal τ) * Vᵀ) = V * E * Vᵀ := by
    rw [hE, Matrix.mul_sub, Matrix.sub_mul, h3]
  have hA : ∀ (c : ℝ) (E : Matrix n n ℝ), ((c • (U * Matrix.diagonal τ * Vᵀ)) * (V * E * Vᵀ))
      = U * (c • (Matrix.diagonal τ * E)) * Vᵀ := by
    intro c E
    have hA0 : (U * Matrix.diagonal τ * Vᵀ) * (V * E * Vᵀ) = U * (Matrix.diagonal τ * E) * Vᵀ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V (E * Vᵀ), hVt, Matrix.one_mul]
    rw [Matrix.smul_mul, hA0, Matrix.mul_assoc U (Matrix.diagonal τ * E) Vᵀ,
      ← Matrix.mul_smul U c (Matrix.diagonal τ * E * Vᵀ),
      ← Matrix.smul_mul c (Matrix.diagonal τ * E) Vᵀ, ← Matrix.mul_assoc U]
  rw [hXX, hst, hA (1 / 2 : ℝ) E]
  have hD1 : Matrix.diagonal τ * ((3 : ℝ) • 1) = (3 : ℝ) • Matrix.diagonal τ := by
    rw [Matrix.mul_smul, Matrix.mul_one]
  have hDE : (1 / 2 : ℝ) • (Matrix.diagonal τ * E)
      = Matrix.diagonal (fun i => NewtonSchulzSigma.ns_p (τ i)) := by
    rw [hE, Matrix.mul_sub, hD1, smul_sub]
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply,
        NewtonSchulzSigma.ns_p, Finset.sum_ite_eq', smul_eq_mul]
      ring
    · simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, h,
        Finset.sum_ite_eq']
  rw [hDE]

/-- k итераций шага кода: `ns_iter k X = ns_step^[k] X`. -/
noncomputable def ns_iter (k : ℕ) (X : Matrix n n ℝ) : Matrix n n ℝ :=
  (NewtonSchulzSigma.ns_step)^[k] X

/-- (T1') Все итерации имеют те же сингулярные векторы:
`X₀ = U·diag σ·Vᵀ ⇒ X_k = U·diag (ns_seq k ∘ σ)·Vᵀ`. -/
theorem ns_iter_svd (U V : Matrix n n ℝ) (σ : n → ℝ)
    (hUt : Uᵀ * U = 1) (hVt : Vᵀ * V = 1) (hV : V * Vᵀ = 1)
    {G : Matrix n n ℝ} (hG : G = U * Matrix.diagonal σ * Vᵀ) (k : ℕ) :
    ns_iter k G = U * Matrix.diagonal (fun i => NewtonSchulzSigma.ns_seq k (σ i)) * Vᵀ := by
  induction k with
  | zero => simp [ns_iter, hG, NewtonSchulzSigma.ns_seq]
  | succ k ih =>
      rw [ns_iter, Function.iterate_succ_apply']
      have h0 : (NewtonSchulzSigma.ns_step)^[k] G = U * Matrix.diagonal (fun i => NewtonSchulzSigma.ns_seq k (σ i)) * Vᵀ := by
        simpa [ns_iter] using ih
      have h1 := ns_step_svd U V _ hUt hVt hV (hX := h0)
      simpa [NewtonSchulzSigma.ns_seq] using h1
/-- (T2) Точное выравнивание: `⟨G, X_k⟩ = Σ_i σ i·ns_seq k (σ i)`. -/
theorem muon_alignment_exact (G : Matrix n n ℝ) (k : ℕ) :
    Hagi.Theory.MuonSpectral.fdot G (ns_iter k G)
      = ∑ i, Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i
          * NewtonSchulzSigma.ns_seq k
            (Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i) := by
  classical
  obtain ⟨U, V, σ, hUo, hVo, hσdef, hG⟩ := Hagi.Theory.MuonSpectral.smax_svd G
  have hUt : Uᵀ * U = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl n)).1
    ((mem_orthogonalGroup_iff n ℝ).1 hUo)
  have hVt : Vᵀ * V = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl n)).1
    ((mem_orthogonalGroup_iff n ℝ).1 hVo)
  have hV : V * Vᵀ = 1 := (mem_orthogonalGroup_iff n ℝ).1 hVo
  have hX := ns_iter_svd U V σ hUt hVt hV hG k
  have hQ : Uᵀ * (ns_iter k G) * V = Matrix.diagonal (fun i => NewtonSchulzSigma.ns_seq k (σ i)) := by
    simp only [hX, ← Matrix.mul_assoc, hUt, Matrix.one_mul]
    rw [Matrix.mul_assoc, hVt, Matrix.mul_one]
  rw [Hagi.Theory.MuonIsometry.inner_eq_sigma_weighted_diag U V σ G (ns_iter k G) hG, hQ]
  simp only [Matrix.diagonal_apply, ite_true]
  rw [← hσdef]

/-- Множество «выживших» направлений: `1/2 ≤ σ i ≤ 1`. -/
noncomputable def kept (G : Matrix n n ℝ) : Finset n :=
  Finset.univ.filter (fun i => 1 / 2 ≤ Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i
    ∧ Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i ≤ 1)

/-- (T3) Почти оптимальность на массе спектра с `σ i ≥ 1/2` (нормировка
Frobenius даёт `σ i ≤ 1`): `⟨G, X₃⟩ ≥ (39/40)·Σ_{i ∈ kept} σ i`. -/
theorem muon_near_optimal (G : Matrix n n ℝ)
    (hnorm : ∀ i, Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i ≤ 1) :
    39 / 40 * ∑ i ∈ kept G, Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i
      ≤ Hagi.Theory.MuonSpectral.fdot G (ns_iter 3 G) := by
  classical
  rw [muon_alignment_exact]
  have hn : ∀ i, 0 ≤ Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i :=
    fun i => Real.sqrt_nonneg _
  calc 39 / 40 * ∑ i ∈ kept G, Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i
      = ∑ i ∈ kept G, 39 / 40 * Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ kept G,
        Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i *
          NewtonSchulzSigma.ns_seq 3 (Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i) := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hi
        have h3 := NewtonSchulzSigma.ns_sigma_min_three hlo hhi
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left h3 (hn i)
    _ ≤ ∑ i, Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i *
          NewtonSchulzSigma.ns_seq 3 (Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i) := by
        have hnn : ∀ i ∈ kept G, 0 ≤ Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i *
            NewtonSchulzSigma.ns_seq 3 (Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i) := by
          intro i _
          have h1 := NewtonSchulzSigma.ns_seq_bounds (hn i) (hnorm i) 3
          exact mul_nonneg (hn i) (le_trans (hn i) h1.1)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => mul_nonneg (hn i)
            (le_trans (hn i) (NewtonSchulzSigma.ns_seq_bounds (hn i) (hnorm i) 3).1))

/-- (T4) Шаг NS не хуже градиентного: при `σ i ∈ [0, 1]` `⟨G, X_k⟩ ≥ ⟨G, G⟩ = Σ σ i²`. -/
theorem muon_alignment_ge_gradient (G : Matrix n n ℝ) (k : ℕ)
    (hnorm : ∀ i, Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i ≤ 1) :
    Hagi.Theory.MuonSpectral.fdot G G
      ≤ Hagi.Theory.MuonSpectral.fdot G (ns_iter k G) := by
  classical
  have hn : ∀ i, 0 ≤ Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i :=
    fun i => Real.sqrt_nonneg _
  have h0 := muon_alignment_exact G 0
  simp only [NewtonSchulzSigma.ns_seq] at h0
  change Hagi.Theory.MuonSpectral.fdot G (ns_iter 0 G) ≤ Hagi.Theory.MuonSpectral.fdot G (ns_iter k G)
  rw [h0, muon_alignment_exact G k]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := NewtonSchulzSigma.ns_seq_bounds (hn i) (hnorm i) k
  exact mul_le_mul_of_nonneg_left h1.1 (hn i)

end Hagi.Theory.MuonAlignment
