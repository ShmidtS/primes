/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.MuonSpectral

/-!
# NewtonSchulzSigma — скалярная динамика Ньютона–Шульца и граница `σ_min` после k итераций

Итерация `X = 0.5 * (3.0 * I_m - X @ X.T) @ X` (hagi/core.py:1363
@ca52eb4) — квадратичная схема `a = 3/2`, `b = −1/2`, без кубичного члена.
Её сингулярные числа следуют скалярной динамике `σ ← (3σ − σ³)/2`
(`ns_step_eigenvalue_sigma`: для `A = XᵀX` и собственного вектора с числом `σ²`
матрица `YᵀY` имеет собственное число `(ns_p σ)²`).

Пусть `d = 1 − σ` — дефект. Тогда `d ← d²(3 − d)/2` — квадратичное
сжатие к нулю, `σ` растёт к 1, не превосходя 1.

* `ns_p`, `ns_seq` — шаг `t(3 − t²)/2` и его k-я итерация.
* `ns_quadratic_invariant` — (T1) `t ∈ [0, 1] ⇒ t ≤ ns_p t ≤ 1`.
* `ns_seq_bounds` — (T1') `t ≤ ns_seq k t ≤ 1` для всех `k`.
* `ns_defect_contraction` — (T2) `1 − ns_p t ≤ (3/2)·(1 − t)²`.
* `ns_defect_bound` — (T3) `d₀ ≤ 1/2 ⇒ 1 − ns_seq k (1 − d₀) ≤ (2/3)·(3/4)^(2^k)`.
* `ns_sigma_min_three` — (T4) `σ₀ ∈ [1/2, 1] ⇒ ns_seq 3 σ₀ ≥ 39/40`.
* `ns_step_eigenvalue`, `ns_step_eigenvalue_sigma` — (T5, T5') мост к итерации кода
  (собственное число `YᵀY`; скалярная динамика `σ ← ns_p σ`).

Границы: `σ₀ ≥ 1/2` — гипотеза (в коде нормировка Frobenius даёт лишь
`σ₀ ≤ 1`); прямоугольный случай, сходимость к `U Vᵀ` и оценка `⟨G, Δ_k⟩`
через дефект не формализованы.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.NewtonSchulzSigma

open scoped BigOperators
open Matrix

/-- Скалярный шаг квадратичной схемы Ньютона–Шульца: `p(t) = t(3 − t²)/2`. -/
noncomputable def ns_p (t : ℝ) : ℝ := t * (3 - t ^ 2) / 2

/-- `k`-я итерация `ns_p`, начиная с `t`. -/
noncomputable def ns_seq (k : ℕ) (t : ℝ) : ℝ :=
  match k with
  | 0 => t
  | k + 1 => ns_p (ns_seq k t)

/-- (T1) Инвариант `[0, 1]` и рост: `0 ≤ t ≤ 1 ⇒ t ≤ ns_p t ≤ 1`. -/
theorem ns_quadratic_invariant {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t ≤ ns_p t ∧ ns_p t ≤ 1 := by
  have e1 : ns_p t - t = t * (1 - t ^ 2) / 2 := by
    unfold ns_p; ring
  have e2 : 1 - ns_p t = (1 - t) ^ 2 * (t + 2) / 2 := by
    unfold ns_p; ring
  have s1 : 0 ≤ 1 - t ^ 2 := by nlinarith
  have s2 : 0 ≤ (1 - t) ^ 2 * (t + 2) / 2 := by positivity
  constructor <;> nlinarith

/-- (T1') Все итерации остаются в `[t, 1]`. -/
theorem ns_seq_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (k : ℕ) :
    t ≤ ns_seq k t ∧ ns_seq k t ≤ 1 := by
  induction k with
  | zero => exact ⟨le_rfl, h1⟩
  | succ k ih =>
      obtain ⟨hl0, hu⟩ := ih
      obtain ⟨hl, hu'⟩ := ns_quadratic_invariant (by nlinarith) hu
      simp only [ns_seq]
      exact ⟨hl0.trans hl, hu'⟩

/-- (T2) Квадратичное сжатие дефекта: `1 − ns_p t ≤ (3/2)·(1 − t)²` на `[0, 1]`. -/
theorem ns_defect_contraction {t : ℝ} (ht : t ≤ 1) :
    1 - ns_p t ≤ 3 / 2 * (1 - t) ^ 2 := by
  have e : 1 - ns_p t = (1 - t) ^ 2 * (3 - (1 - t)) / 2 := by
    unfold ns_p; ring
  have s : 0 ≤ (1 - t) ^ 2 := by positivity
  have h3 : 3 - (1 - t) ≤ 3 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 s]

/-- (T3) Явная граница дефекта после `k` итераций: `d₀ ≤ 1/2 ⇒
`1 − ns_seq k (1 − d₀) ≤ (2/3)·(3/4)^(2^k)` (двойная экспонента). -/
theorem ns_defect_bound {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1 / 2) (k : ℕ) :
    1 - ns_seq k (1 - d) ≤ 2 / 3 * (3 / 4) ^ (2 ^ k) := by
  have ht : 0 ≤ 1 - d ∧ 1 - d ≤ 1 := by constructor <;> linarith
  have key : ∀ k, 1 - ns_seq k (1 - d) ≤ 2 / 3 * (3 / 4) ^ (2 ^ k) ∧ 1 - d ≤ ns_seq k (1 - d) := by
    intro k
    induction k with
    | zero => simp [ns_seq]; nlinarith
    | succ k ih =>
        obtain ⟨ih, hl⟩ := ih
        have hu : ns_seq k (1 - d) ≤ 1 := (ns_seq_bounds ht.1 ht.2 k).2
        have hc := ns_defect_contraction hu
        have hnn : 0 ≤ 1 - ns_seq k (1 - d) := by nlinarith
        have c : (0 : ℝ) ≤ (3 / 4) ^ (2 ^ k) := by positivity
        have hps : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := Nat.two_pow_succ _
        rw [hps, pow_add]
        simp only [ns_seq]
        constructor
        · nlinarith [sq_nonneg ((3 / 4) ^ (2 ^ k)), sq_nonneg (1 - ns_seq k (1 - d))]
        · exact hl.trans (ns_quadratic_invariant (by nlinarith) hu).1
  exact (key k).1

/-- Монотонность шага на `[0, 1]`. -/
lemma ns_p_mono {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ns_p s ≤ ns_p t := by
  have e : ns_p t - ns_p s = (t - s) * (3 - (t ^ 2 + t * s + s ^ 2)) / 2 := by
    unfold ns_p; ring
  have a : 0 ≤ t - s := sub_nonneg.mpr hst
  have b : 0 ≤ 3 - (t ^ 2 + t * s + s ^ 2) := by nlinarith
  have := mul_nonneg a b
  nlinarith

/-- Монотонность итераций по начальному значению. -/
lemma ns_seq_mono {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) (k : ℕ) :
    ns_seq k s ≤ ns_seq k t := by
  induction k with
  | zero => simpa [ns_seq] using hst
  | succ k ih =>
      obtain ⟨_, hu⟩ := ns_seq_bounds h0 (by nlinarith) k
      simp only [ns_seq]
      exact ns_p_mono (by nlinarith) ih ((ns_seq_bounds (by nlinarith) ht k).2)

/-- (T4) Явное число для `iters = 3`: `σ₀ ∈ [1/2, 1] ⇒ σ₃ ≥ 39/40 = 0.975`
(точная итерация от `σ₀ = 1/2`: дефект `1/2 → 5/16 → 1075/8192 → < 1/40`). -/
theorem ns_sigma_min_three {σ : ℝ} (h0 : 1 / 2 ≤ σ) (h1 : σ ≤ 1) :
    39 / 40 ≤ ns_seq 3 σ := by
  have h := ns_seq_mono (by nlinarith) h0 h1 3
  have e2 : ns_seq 2 (1 / 2) = 1 - 1075 / 8192 := by
    norm_num [ns_seq, ns_p]
  have e3 : ns_seq 3 (1 / 2) = 1 - ((1075 / 8192 : ℝ) ^ 2 * (3 - 1075 / 8192) / 2) := by
    norm_num [ns_seq, ns_p, e2]
  rw [e3] at h
  have fin : (1075 / 8192 : ℝ) ^ 2 * (23 / 8) / 2 ≤ 1 / 40 := by
    rw [sq, div_le_div_iff₀ (by norm_num) (by norm_num)]
    norm_num
  have hm : (1075 / 8192 : ℝ) ^ 2 * (3 - 1075 / 8192) / 2 ≤
      (1075 / 8192 : ℝ) ^ 2 * (23 / 8) / 2 := by
    have h3 : 3 - (1075 / 8192 : ℝ) ≤ 23 / 8 := by norm_num
    have hs : (0 : ℝ) ≤ (1075 / 8192) ^ 2 := by positivity
    gcongr
  have fin2 : (1075 / 8192 : ℝ) ^ 2 * (3 - 1075 / 8192) / 2 ≤ 1 / 40 := hm.trans fin
  calc 39 / 40 = 1 - 1 / 40 := by ring
    _ ≤ 1 - (1075 / 8192 : ℝ) ^ 2 * (3 - 1075 / 8192) / 2 := sub_le_sub_left fin2 _
    _ ≤ ns_seq 3 σ := h

/-- Матричный шаг кода: `Y = (1/2)·X(3I − XᵀX)`. -/
noncomputable def ns_step {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (X : Matrix m n ℝ) : Matrix m n ℝ :=
  (1 / 2 : ℝ) • X * ((3 : ℝ) • 1 - Xᵀ * X)

lemma ns_shift_mulVec {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (v : n → ℝ)
    (μ : ℝ) (h : Matrix.mulVec A v = μ • v) :
    Matrix.mulVec ((3 : ℝ) • 1 - A) v = (3 - μ) • v := by
  have hi : ∀ i, (∑ j, A i j * v j) = μ * v i := fun i => by
    have := congrFun h i
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using this
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h, sub_smul]

/-- (T5) Собственное число шага: если `v` — собственный вектор `XᵀX` с числом `μ`
(`μ = σ²`), то `YᵀY` имеет на `v` собственное число `μ·((3 − μ)/2)²`, т.е. `σ² ← σ·p(σ)²`
и `σ ← (3σ − σ³)/2`. -/
theorem ns_step_eigenvalue {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (X : Matrix m n ℝ) (v : n → ℝ) (μ : ℝ)
    (h : Matrix.mulVec (Xᵀ * X) v = μ • v) :
    Matrix.mulVec ((ns_step X)ᵀ * ns_step X) v = (μ * ((3 - μ) / 2) ^ 2) • v := by
  have hsym : ((3 : ℝ) • 1 - Xᵀ * X)ᵀ = (3 : ℝ) • 1 - Xᵀ * X := by
    ext i j
    simp [Matrix.transpose_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.mul_apply, mul_comm,
      eq_comm]
  have hY : (ns_step X)ᵀ * ns_step X =
      (1 / 4 : ℝ) • (((3 : ℝ) • 1 - Xᵀ * X) * (Xᵀ * X) * ((3 : ℝ) • 1 - Xᵀ * X)) := by
    simp only [ns_step, Matrix.transpose_mul, Matrix.transpose_smul, hsym, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, mul_assoc]
    have hq : (1 / 2 : ℝ) * (1 / 2) = 1 / 4 := by norm_num
    rw [hq]
    refine congrArg _ ?_
    rw [Matrix.mul_assoc ((3 : ℝ) • 1 - Xᵀ * X) Xᵀ, Matrix.mul_assoc Xᵀ X]

  have h1 := ns_shift_mulVec (Xᵀ * X) v μ h
  have eig : ∀ c : ℝ, Matrix.mulVec (Xᵀ * X) (c • v) = (c * μ) • v := by
    intro c; rw [Matrix.mulVec_smul, h, smul_smul]
  have sh : ∀ c : ℝ, Matrix.mulVec ((3 : ℝ) • 1 - Xᵀ * X) (c • v) = ((3 - μ) * c) • v := by
    intro c
    rw [Matrix.mulVec_smul, h1, smul_smul, mul_comm]
  have hm : Matrix.mulVec ((1 / 4 : ℝ) • (((3 : ℝ) • 1 - Xᵀ * X) * (Xᵀ * X) *
      ((3 : ℝ) • 1 - Xᵀ * X))) v =
      (1 / 4 : ℝ) • Matrix.mulVec ((3 : ℝ) • 1 - Xᵀ * X)
        (Matrix.mulVec (Xᵀ * X) (Matrix.mulVec ((3 : ℝ) • 1 - Xᵀ * X) v)) := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h0 : Matrix.mulVec ((ns_step X)ᵀ * ns_step X) v =
      Matrix.mulVec ((1 / 4 : ℝ) • (((3 : ℝ) • 1 - Xᵀ * X) * (Xᵀ * X) *
        ((3 : ℝ) • 1 - Xᵀ * X))) v := by rw [hY]
  rw [h0, hm, h1, eig, sh]
  have e : 1 / 4 * ((3 - μ) * ((3 - μ) * μ)) = μ * ((3 - μ) / 2) ^ 2 := by ring
  rw [smul_smul, e]

/-- (T5') В терминах `σ`: если `XᵀX v = σ²•v`, то `(YᵀY) v = (ns_p σ)²•v` —
сингулярные числа следуют скалярной динамике `σ ← ns_p σ`. -/
theorem ns_step_eigenvalue_sigma {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (X : Matrix m n ℝ) (v : n → ℝ) (σ : ℝ)
    (h : Matrix.mulVec (Xᵀ * X) v = σ ^ 2 • v) :
    Matrix.mulVec ((ns_step X)ᵀ * ns_step X) v = (ns_p σ) ^ 2 • v := by
  have := ns_step_eigenvalue X v (σ ^ 2) h
  rw [show σ ^ 2 * ((3 - σ ^ 2) / 2) ^ 2 = (σ * (3 - σ ^ 2) / 2) ^ 2 from by ring] at this
  rw [this]; rfl

end Hagi.Theory.NewtonSchulzSigma
