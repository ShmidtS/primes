import Hagi.Optimization.InexactContraction
namespace Hagi.Optimization

open Hagi.Optimization
open Finset

/-- ЯДРО РОББИНСА-МОНРО (детерминированное): при затухающих
шагах η_k ∈ [0,1] с расходящейся суммой ошибка рекурсии
x_{k+1} ≤ (1−η_k)·x_k стремится к нулю: произведение
∏(1−η) ≤ e^{−Ση} → 0 — сходящиеся шаги с бесконечной суммой
гасят любую начальную ошибку (основа стохастической
аппроксимации и затухающих learning rate). -/
theorem robbins_monro_decay (x η : ℕ → ℝ)
    (hx0 : 0 ≤ x 0)
    (hη : ∀ k, 0 ≤ η k ∧ η k ≤ 1)
    (hstep : ∀ k, x (k + 1) ≤ (1 - η k) * x k)
    (hdiv : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, η k)
      Filter.atTop Filter.atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ s : ℕ, T ≤ s → x s ≤ ε := by
  -- поточечная граница: x_s ≤ x_0 · ∏_{k<s}(1−η_k)
  have hprod : ∀ n : ℕ, x n ≤ x 0 * ∏ k ∈ Finset.range n,
      (1 - η k) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        have h1 := hstep m
        have h2 : x (m + 1) ≤ (1 - η m) * (x 0 * ∏ k ∈ Finset.range m,
            (1 - η k)) := by
          calc x (m + 1) ≤ (1 - η m) * x m := h1
            _ ≤ (1 - η m) * (x 0 * ∏ k ∈ Finset.range m,
                (1 - η k)) := by
                refine mul_le_mul_of_nonneg_left ih ?_
                have := hη m
                linarith
        rw [Finset.prod_range_succ]
        nlinarith [h2, hη m]
  -- экспоненциальная мажоранта: ∏(1−η) ≤ e^{−Ση}
  have hexp : ∀ n : ℕ, ∏ k ∈ Finset.range n, (1 - η k)
      ≤ Real.exp (-∑ k ∈ Finset.range n, η k) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [Finset.prod_range_succ, Finset.sum_range_succ,
          neg_add, Real.exp_add]
        calc (∏ k ∈ Finset.range m, (1 - η k)) * (1 - η m)
            ≤ (∏ k ∈ Finset.range m, (1 - η k))
                * Real.exp (-(η m)) := by
              refine mul_le_mul_of_nonneg_left
                (Real.one_sub_le_exp_neg (η m))
                (Finset.prod_nonneg fun k _ => by
                  have := hη k; linarith)
          _ ≤ Real.exp (-(∑ k ∈ Finset.range m, η k))
                * Real.exp (-(η m)) :=
              mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)
  -- комбинирование: x_s ≤ x_0·e^{−Σ_{<s}η} → 0 при Σ → ∞
  have hx0exp : (0:ℝ) ≤ x 0 := hx0
  by_cases hx0pos : 0 < x 0
  · -- x_0 > 0: e^{−Σ} → 0, ждём x_0·e^{−Σ} < ε
    have hsumbot : Filter.Tendsto
        (fun n => -(∑ k ∈ Finset.range n, η k))
        Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atBot_iff.mpr hdiv
    have hexpbot : Filter.Tendsto
        (fun n => Real.exp (-(∑ k ∈ Finset.range n, η k)))
        Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hsumbot
    have hev : ∀ᶠ s in Filter.atTop,
        x 0 * Real.exp (-(∑ k ∈ Finset.range s, η k)) < ε := by
      have hmem : ∀ᶠ s in Filter.atTop,
          Real.exp (-(∑ k ∈ Finset.range s, η k)) < ε / x 0 :=
        Filter.Tendsto.eventually hexpbot
          (gt_mem_nhds (div_pos hε hx0pos))
      refine hmem.mono fun s hs => ?_
      rw [mul_comm]
      exact (lt_div_iff₀ hx0pos).mp hs
    rw [Filter.eventually_atTop] at hev
    obtain ⟨T, hT⟩ := hev
    refine ⟨T, fun s hs => ?_⟩
    have h1 := hprod s
    have h2 := hexp s
    have h3 : Real.exp (-(∑ k ∈ Finset.range s, η k)) * x 0 < ε := by
      have h4 := hT s hs
      rw [mul_comm] at h4
      exact h4
    nlinarith [h1, h2, h3, hx0exp]
  · -- x_0 ≤ 0: индукция даёт x_s ≤ 0 ≤ ε
    refine ⟨0, fun s _ => ?_⟩
    have h1 := hprod s
    have h2 : (0:ℝ) ≤ ∏ k ∈ Finset.range s, (1 - η k) :=
      Finset.prod_nonneg (fun k _ => by have := hη k; linarith)
    have : x 0 ≤ 0 := by
      by_contra hc; push_neg at hc; linarith
    nlinarith [h1, h2, this]

/-- РОББИНС-МОНРО ПО МОДУЛЮ: закон |y_{k+1}| ≤ (1−η_k)|y_k|
с расходящейся суммой шагов гасит |y| к нулю независимо от
знака начальной ошибки (применение ядра к |y|). -/
theorem robbins_monro_abs (y η : ℕ → ℝ)
    (hη : ∀ k, 0 ≤ η k ∧ η k ≤ 1)
    (hstep : ∀ k, |y (k + 1)| ≤ (1 - η k) * |y k|)
    (hdiv : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, η k)
      Filter.atTop Filter.atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ s : ℕ, T ≤ s → |y s| ≤ ε :=
  robbins_monro_decay (fun k => |y k|) η (abs_nonneg _) hη hstep hdiv ε hε

/-- РОББИНС-МОНРО СО СИСТЕМАТИЧЕСКИМ СМЕЩЕНИЕМ:
если δ_k ≤ D·η_k, то limsup x ≤ D: центрирование
y = x − D даёт y_{k+1} ≤ (1−η_k) y_k, и RM-ядро
(или тривиальность при y₀ ≤ 0) даёт y_s ≤ ε. -/
theorem robbins_monro_bias (x η : ℕ → ℝ) (D : ℝ)
    (hη : ∀ k, 0 ≤ η k ∧ η k ≤ 1)
    (hstep : ∀ k, x (k + 1) ≤ (1 - η k) * x k + D * η k)
    (hdiv : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, η k)
      Filter.atTop Filter.atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ s : ℕ, T ≤ s → x s ≤ D + ε := by
  -- центрированная последовательность y = x − D
  set y : ℕ → ℝ := fun k => x k - D with hy
  have hystep : ∀ k, y (k + 1) ≤ (1 - η k) * y k := by
    intro k
    have h := hstep k
    have hcc : (1 - η k) * D + D * η k = D := by ring
    linarith [h, hcc]
  by_cases hy0 : 0 < y 0
  · -- y₀ > 0: применяем RM-ядро к y
    have hy0nn : (0:ℝ) ≤ y 0 := le_of_lt hy0
    have hrm := robbins_monro_decay y η hy0nn hη hystep hdiv ε hε
    obtain ⟨T, hT⟩ := hrm
    refine ⟨T, fun s hs => ?_⟩
    have h1 := hT s hs
    linarith [h1]
  · -- y₀ ≤ 0: индукция даёт y_s ≤ 0 ≤ ε
    have hy0le : y 0 ≤ 0 := by
      by_contra hc; push_neg at hc; exact hy0 hc
    have hprod : ∀ n : ℕ, y n ≤ 0 := by
      intro n
      induction n with
      | zero => exact hy0le
      | succ m ih =>
          have h := hystep m
          have hηm := hη m
          have h1 : (1 - η m) * y m ≤ 0 := by
            nlinarith [ih, hηm.1, hηm.2]
          linarith [h, h1]
    refine ⟨0, fun s _ => ?_⟩
    have h1 := hprod s
    linarith [h1]

end Hagi.Optimization
