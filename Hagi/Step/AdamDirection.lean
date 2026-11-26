/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib

/-!
# AdamDirection — знак ⟨g, d_Adam⟩

Код-факт (HAGI_v2 READ-ONLY @b3740e0): `torch.optim.Adam(...)`
без `betas`/`eps` — lm.py:349,403,779,930, unified.py:473,548 —
значит torch-дефолты β₁ = 0.9, β₂ = 0.999, eps = 1e-8. Шаг Адама:
`m_t = β₁ m_{t−1} + (1−β₁) g_t`, `v_t = β₂ v_{t−1} + (1−β₂) g_t²`,
`m̂ = m_t/(1−β₁^t)`, `v̂ = v_t/(1−β₂^t)`, `d = m̂/(√v̂ + eps)`.

ВОПРОС: является ли `⟨g_t, d_t⟩ ≥ 0` код-фактом?

ОТВЕТ (honest, два теоремы + один негатив):

* `adam_first_step_dot_nonneg` — на ПЕРВОМ шаге (t = 1) коррекция
  смещения точна: `m̂ = g`, `v̂ = g²`, так что `d_i = g_i/(|g_i|+eps)` и
  `⟨g, d⟩ = Σ g_i²/(|g_i|+eps) ≥ 0`; строго `> 0` при `g ≠ 0`
  (`adam_first_step_dot_pos`).
* `adam_coord_sign_flip_neg` — покомпонентно знак `d_i` — это знак
  `m̂_i`, НЕ `g_i`: при разногласии `g_i m̂_i < 0` вклад `g_i d_i < 0`.
* `ema_sign_flip_negative` — контрпример на шаге 2 (β₁ = 9/10,
  β₂ = 999/1000, g₁ = 1, g₂ = −1/10): `m̂₂ = (2/25)/(19/100) > 0`,
  поэтому `⟨g₂, d₂⟩ < 0` — общий шаг Адама НЕ является
  сертифицированным спуском. В коде HAGI_v2 шаг поэтому принимается
  только измерённым гейтом `backtrackAccept` (selfmodel.py:134-169)
  — градиентное соглашение `min_dot` считается для направления
  MGDA ДО Адама (selfmodel.py:119-123).
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

open scoped BigOperators

namespace Hagi.Step

/-- Экспоненциальная средняя (первый/второй момент Адама),
нулевая инициализация: `ema 0 = 0`, `ema (t+1) = β·ema t + (1−β)·g t`. -/
def ema (β : ℝ) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => β * ema β g t + (1 - β) * g t

/-- Одна координата направления Адама: `m̂/(√v̂ + eps)`. -/
noncomputable def adamCoord (mhat vhat eps : ℝ) : ℝ :=
  mhat / (Real.sqrt vhat + eps)

/-- Направление Адама покомпонентно. -/
noncomputable def adamDir {ι : Type*} (mhat vhat : ι → ℝ) (eps : ℝ) : ι → ℝ :=
  fun i => adamCoord (mhat i) (vhat i) eps

/-- Скалярное произведение ⟨a, b⟩ = Σ a_i b_i. -/
noncomputable def adamDot {ι : Type*} [Fintype ι] (a b : ι → ℝ) : ℝ :=
  ∑ i, a i * b i

/-! ## Первый шаг: коррекция смещения точна -/

/-- `ema` на шаге 1: `m₁ = (1−β)·g₁`. -/
theorem ema_one (β : ℝ) (g : ℕ → ℝ) : ema β g 1 = (1 - β) * g 0 := by
  simp [ema]

/-- Первый момент на шаге 1 после коррекции смещения: `m̂₁ = g₁`. -/
theorem ema_one_unbiased (β : ℝ) (g : ℕ → ℝ) (hβ : β ≠ 1) :
    ema β g 1 / (1 - β ^ 1) = g 0 := by
  rw [ema_one, pow_one]
  field_simp

/-- Первый шаг Адама — спуск по знаку каждой координаты:
`g_i·(g_i/(|g_i|+eps)) = g_i²/(|g_i|+eps) ≥ 0`. -/
theorem adam_first_step_dot_nonneg {ι : Type*} [Fintype ι]
    (g : ι → ℝ) {eps : ℝ} (heps : 0 ≤ eps) :
    0 ≤ adamDot g (adamDir g (fun i => g i ^ 2) eps) := by
  refine Finset.sum_nonneg fun i _ => ?_
  have h2 : g i * (g i / (Real.sqrt (g i ^ 2) + eps)) = g i ^ 2 / (|g i| + eps) := by
    rw [Real.sqrt_sq_eq_abs]; ring
  simp only [adamDir, adamCoord]
  rw [h2]
  exact div_nonneg (sq_nonneg (g i)) (by positivity)

/-- На первом шаге `⟨g, d⟩ > 0`, если градиент ненулевой (и eps > 0). -/
theorem adam_first_step_dot_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ι → ℝ) (hg : g ≠ 0) {eps : ℝ} (heps : 0 < eps) :
    0 < adamDot g (adamDir g (fun i => g i ^ 2) eps) := by
  have hterm : ∀ i, g i * (g i / (Real.sqrt (g i ^ 2) + eps))
      = g i ^ 2 / (|g i| + eps) := by
    intro i
    rw [Real.sqrt_sq_eq_abs]; ring
  simp only [adamDot, adamDir, adamCoord]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_const_zero]
  refine Finset.sum_lt_sum (fun i _ => div_nonneg (sq_nonneg (g i)) (by positivity)) ?_
  obtain ⟨i, hne⟩ : ∃ i, g i ≠ 0 := by
    by_contra hcon
    exact hg (funext fun i => not_not.mp fun h => hcon ⟨i, h⟩)
  refine ⟨i, Finset.mem_univ i, ?_⟩
  exact div_pos (sq_pos_of_ne_zero hne) (by positivity)


/-! ## Общий шаг: знак координаты — знак момента -/

/-- Покомпонентный факт: `d_i` имеет знак `m̂_i`, не `g_i`; при
разногласии `g_i·m̂_i < 0` вклад координты отрицателен. -/
theorem adam_coord_sign_flip_neg {g m v eps : ℝ}
    (hv : 0 < v) (heps : 0 ≤ eps) (h : g * m < 0) :
    g * adamCoord m v eps < 0 := by
  have hrew : g * (m / (Real.sqrt v + eps)) = g * m / (Real.sqrt v + eps) := by
    rw [mul_div_assoc]
  rw [adamCoord, hrew]
  exact div_neg_of_neg_of_pos h (by positivity)

/-- Негатив: общий шаг Адама НЕ является безусловным спуском —
`⟨g, d⟩ ≥ 0` не верно для всех `g, m̂, v̂`. -/
theorem adam_step_not_always_descent :
    ¬ ∀ g m v eps : ℝ, 0 ≤ g * (m / (Real.sqrt v + eps)) := by
  intro h
  have := h 1 (-1) 1 0
  norm_num at this

/-- Контрпример на шаге 2 (β₁ = 9/10, β₂ = 999/1000, g₁ = 1,
g₂ = −1/10): после коррекции смещения `m̂₂ = (2/25)/(19/100) > 0`,
`v̂₂ = (1009/10^6)/(1999/10^6) > 0`, поэтому `⟨g₂, d₂⟩ < 0`. -/
theorem ema_sign_flip_negative {eps : ℝ} (heps : 0 ≤ eps) :
    0 < ema (999 / 1000) (fun t => (if t = 0 then 1 else -1 / 10) ^ 2) 2
        / (1 - (999 / 1000) ^ 2) ∧
      (-1 / 10) * (ema (9 / 10) (fun t => if t = 0 then 1 else -1 / 10) 2
          / (1 - (9 / 10) ^ 2)) < 0 ∧
      adamDot (fun _ : Fin 1 => (-1 : ℝ) / 10)
          (adamDir
            (fun _ => ema (9 / 10) (fun t => if t = 0 then 1 else -1 / 10) 2
              / (1 - (9 / 10) ^ 2))
            (fun _ => ema (999 / 1000) (fun t => (if t = 0 then 1 else -1 / 10) ^ 2) 2
              / (1 - (999 / 1000) ^ 2)) eps) < 0 := by
  have hm : ema (9 / 10) (fun t => if t = 0 then 1 else -1 / 10) 2 = 2 / 25 := by
    norm_num [ema]
  have hv : ema (999 / 1000) (fun t => (if t = 0 then 1 else -1 / 10) ^ 2) 2
      = 1009 / 10 ^ 6 := by
    norm_num [ema]
  have hdm : (0:ℝ) < 1 - (9 / 10) ^ 2 := by norm_num
  have hdv : (0:ℝ) < 1 - (999 / 1000) ^ 2 := by norm_num
  have hmhat : 0 < ema (9 / 10) (fun t => if t = 0 then 1 else -1 / 10) 2
      / (1 - (9 / 10) ^ 2) := by
    rw [hm]
    exact div_pos (by norm_num) hdm
  have hvhat : 0 < ema (999 / 1000) (fun t => (if t = 0 then 1 else -1 / 10) ^ 2) 2
      / (1 - (999 / 1000) ^ 2) := by
    rw [hv]
    exact div_pos (by norm_num) hdv
  refine ⟨hvhat, ?_, ?_⟩
  · exact mul_neg_of_neg_of_pos (by norm_num) hmhat
  · simp only [adamDot, adamDir, adamCoord, Finset.univ_unique, Finset.sum_singleton]
    exact adam_coord_sign_flip_neg (g := -1 / 10)
      (m := ema (9 / 10) (fun t => if t = 0 then 1 else -1 / 10) 2
        / (1 - (9 / 10) ^ 2))
      (v := ema (999 / 1000) (fun t => (if t = 0 then 1 else -1 / 10) ^ 2) 2
        / (1 - (999 / 1000) ^ 2))
      hvhat heps (mul_neg_of_neg_of_pos (by norm_num) hmhat)

/-- Веса EMA на шаге `T`: `π_s = (1−d_s)·∏_{s<j<T} d_j` для `s < T`. -/
noncomputable def emaWeights (dm : ℕ → ℝ) (T s : ℕ) : ℝ :=
  if s < T then (1 - dm (s+1)) * ∏ j ∈ Finset.Ico (s+1) T, dm (j+1) else 0
theorem emaWeights_nonneg (dm : ℕ → ℝ) (hd : ∀ t, 0 ≤ dm t ∧ dm t ≤ 1) (T s : ℕ) :
    0 ≤ emaWeights dm T s := by
  unfold emaWeights
  split
  · have hprod : 0 ≤ ∏ j ∈ Finset.Ico (s+1) T, dm (j+1) := Finset.prod_nonneg (fun j _ => (hd (j+1)).1)
    exact mul_nonneg (by have := hd (s+1); linarith) hprod
  · exact le_refl 0
/-- Сумма весов: `1 − ∏_{j<T} d_j`; при `d_{T−1} < 1` — выпуклая комбинация. -/
theorem emaWeights_sum (dm : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range T, emaWeights dm T s = 1 - ∏ j ∈ Finset.Ico 0 T, dm (j+1) := by
  induction T with
  | zero => simp [emaWeights]
  | succ k ih =>
    have hlast : emaWeights dm (k+1) k = 1 - dm (k+1) := by
      unfold emaWeights; rw [if_pos (Nat.lt_succ_self k)]; simp
    have hprev : ∀ s ∈ Finset.range k,
        emaWeights dm (k+1) s = emaWeights dm k s * dm (k+1) := by
      intro s hs
      unfold emaWeights
      rw [if_pos (lt_of_lt_of_le (Finset.mem_range.1 hs) (Nat.le_succ k)),
        if_pos (Finset.mem_range.1 hs), Finset.prod_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.1 hs))]
      ring
    rw [Finset.sum_range_succ, hlast, Finset.sum_congr rfl hprev, ← Finset.sum_mul, ih]
    rw [Finset.prod_Ico_succ_top (Nat.zero_le k)]
    ring
/-- EMA весов `w` — выпуклая комбинация `∑ π_s·w_s`; для выпуклой `L`
`L(EMA_T) ≤ ∑ π_s·L(w_s)`: контроль EMA не хуже средней loss траектории. -/
theorem ema_convex_le (dm : ℕ → ℝ) (hd : ∀ t, 0 ≤ dm t ∧ dm t ≤ 1) (hd1 : dm 1 = 0)
    (T : ℕ) (hT : 0 < T) (w : ℕ → ℝ) (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L) :
    L (∑ s ∈ Finset.range T, emaWeights dm T s * w s) ≤
      ∑ s ∈ Finset.range T, emaWeights dm T s * L (w s) := by
  classical
  have hnonneg : ∀ s ∈ Finset.range T, 0 ≤ emaWeights dm T s :=
    fun s _ => emaWeights_nonneg dm hd T s
  have hsum : ∑ s ∈ Finset.range T, emaWeights dm T s = 1 := by
    rw [emaWeights_sum]
    have hzero : ∏ j ∈ Finset.Ico 0 T, dm (j+1) = 0 := by
      rw [Finset.prod_eq_zero (Finset.mem_Ico.2 ⟨Nat.zero_le 0, hT⟩)]
      simpa using hd1
    rw [hzero, sub_zero]
  have hmem : ∀ s ∈ Finset.range T, w s ∈ Set.univ := fun _ _ => Set.mem_univ _
  have h := hconv.map_sum_le hnonneg hsum hmem
  simpa [nsmul_eq_mul] using h

/-- Доля старых весов (до смены домена) в EMA после `k` шагов с постоянным `d`:
`∏_{j<k} d = d^k`. -/
theorem emaWeights_const_prod (d : ℝ) (k : ℕ) :
    ∏ j ∈ Finset.Ico 0 k, d = d ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.prod_Ico_succ_top (Nat.zero_le k), ih]; ring
/-- При `d ≤ 1 − δ` доля старого веса убывает геометрически. -/
theorem ema_stale_decay (d δ : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ 1 - δ) (k : ℕ) :
    d ^ k ≤ (1 - δ) ^ k := by
  exact pow_le_pow_left₀ hd0 hd k
/-- Экспоненциальная граница: `d^k ≤ exp(−k·δ)` при `0 < d`, `log d ≤ −δ`. -/
theorem ema_stale_exp (d : ℝ) (k : ℕ) (δ : ℝ) (hd0 : 0 < d) (hd : Real.log d ≤ -δ) :
    d ^ k ≤ Real.exp (-(k : ℝ) * δ) := by
  have hpos : 0 < d ^ k := pow_pos hd0 k
  rw [← Real.exp_log hpos, Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have := mul_le_mul_of_nonneg_left hd hk
  push_cast at this
  nlinarith

/-- EMA потока `w` с постоянным `d`, стартующая с `e0`: `e_{k+1} = d·e_k + (1−d)·w_{k+1}`. -/
noncomputable def emaFrom (d : ℝ) (w : ℕ → ℝ) (e0 : ℝ) : ℕ → ℝ
  | 0 => e0
  | k + 1 => d * emaFrom d w e0 k + (1 - d) * w (k + 1)
/-- Вклад стартового значения в EMA после `k` шагов — ровно `d^k`. -/
theorem ema_init_share (d : ℝ) (w : ℕ → ℝ) (k : ℕ) (e0 e0' : ℝ) :
    emaFrom d w e0 k - emaFrom d w e0' k = d ^ k * (e0 - e0') := by
  induction k generalizing e0 e0' with
  | zero => simp [emaFrom]
  | succ k ih =>
    rw [emaFrom, emaFrom]
    calc d * emaFrom d w e0 k + (1 - d) * w (k + 1) - (d * emaFrom d w e0' k + (1 - d) * w (k + 1))
        = d * (emaFrom d w e0 k - emaFrom d w e0' k) := by ring
      _ = d * (d ^ k * (e0 - e0')) := by rw [ih e0 e0']
      _ = d ^ (k + 1) * (e0 - e0') := by rw [pow_succ]; ring
/-- При `e0 = w 0` (копия стартовых весов) и `|d| ≤ 1` вклад `w 0` убывает как `d^k`. -/
theorem ema_init_copy_share_le (d : ℝ) (w : ℕ → ℝ) (k : ℕ) (hd : |d| ≤ 1) :
    |d| ^ k * |w 0| ≤ |w 0| := by
  calc |d| ^ k * |w 0| ≤ 1 ^ k * |w 0| := by gcongr
    _ = |w 0| := by simp

end Hagi.Step
