/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Probability.GibbsCore
import Hagi.Probability.GibbsCooling
import Hagi.Probability.EntropyConvexity
import Hagi.Probability.FannesPinsker
import Hagi.Probability.ChernoffCGF
import Hagi.Probability.MomentBounds
import Hagi.Probability.FreedmanTwoSided
import Hagi.Optimization.MirrorHedgeCore

set_option linter.style.header false

/-!
# MirrorHedgeRegret

Итерированные зеркальные веса: mirrorIterate, regret-оценки (mirror_step_regret, mirror_regret), semigroup-свойство и кумулятивность.
Split from `MirrorHedge` (C259).
-/

namespace Hagi.Optimization

open Finset

/-- Итерированные зеркальные веса: w₀ = ρ₀,
w_{k+1} = mirrorStep w_k (ℓ_k) T — траектория hedge/MWU
при постоянной температуре T. -/
noncomputable def mirrorIterate {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) : ℕ → V → ℝ
  | 0 => ρ₀
  | k+1 => mirrorStep (mirrorIterate ρ₀ ℓs T k) (ℓs k) T

/-- Позитивность траектории сохраняется. -/
theorem mirrorIterate_pos {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (k : ℕ) :
    ∀ v, 0 < mirrorIterate ρ₀ ℓs T k v := by
  induction k with
  | zero => exact hρ₀
  | succ n ih =>
      intro v
      unfold mirrorIterate
      exact mirrorStep_pos _ _ T hT ih v

/-- Траектория остаётся распределением. -/
theorem mirrorIterate_sum_one {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1) (k : ℕ) :
    ∑ v, mirrorIterate ρ₀ ℓs T k v = 1 := by
  induction k with
  | zero => exact hρ₀1
  | succ n ih =>
      unfold mirrorIterate
      exact mirrorStep_sum_one _ _ T hT
        (mirrorIterate_pos ρ₀ ℓs T hT hρ₀ n)

/-- ОДНОШАГОВОЕ НЕРАВЕНСТВО РЕГРЕТА: обновлённые веса γ
проигрывают цели ρ* не более убыли T·KL:
⟨γ,ℓ⟩ − ⟨ρ*,ℓ⟩ ≤ T·(KL(ρ*‖ρ₀) − KL(ρ*‖γ)) — следствие
тождества прогресса и неотрицательности KL(γ‖ρ₀). -/
theorem mirror_step_regret {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v) - (∑ v, ρ v * ℓ v)
      ≤ T * ((∑ v, ρ v * Real.log (ρ v / ρ₀ v))
        - (∑ v, ρ v * Real.log (ρ v
            / mirrorStep ρ₀ ℓ T v))) := by
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  have hγ1 : ∑ v, mirrorStep ρ₀ ℓ T v = 1 :=
    mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  have hklγ : (0:ℝ) ≤ T * (∑ v, mirrorStep ρ₀ ℓ T v
      * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)) := by
    have h := finite_kl_nonneg (mirrorStep ρ₀ ℓ T) ρ₀
      hγpos hγ1 hρ₀ hρ₀1
    exact mul_nonneg (le_of_lt hT) h
  -- hprog: ⟨ρ,ℓ⟩ − (⟨γ,ℓ⟩ + T·KL(γ‖ρ₀)) = T(KL(ρ‖γ) − KL(ρ‖ρ₀))
  have hprog := mirror_progress_identity ρ₀ ℓ T hT hρ₀ ρ hρ hρ1
  linarith

/-- ТЕЛЕСКОПИРОВАННЫЙ РЕГРЕТ HEDGE/MWU: суммарное превышение
потерь обновляемых весов w_{k+1} = mirrorStep w_k ℓ_k T над
любой фиксированной целью ρ* ≤ T·KL(ρ*‖w₀) — KL-убыль
телескопирует, регрет ограничен начальным расстоянием
Брегмана: полная формализация regret-границы зеркального
спуска (база MWU/Hedge-анализа). -/
theorem mirror_regret {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1)
    (n : ℕ) :
    ∑ k ∈ Finset.range n,
        ((∑ v, mirrorIterate ρ₀ ℓs T (k+1) v * ℓs k v)
          - (∑ v, ρ v * ℓs k v))
      ≤ T * (∑ v, ρ v * Real.log (ρ v / ρ₀ v)) := by
  -- индукция по n с одношаговым неравенством
  have key : ∀ n : ℕ,
      (∑ k ∈ Finset.range n,
        ((∑ v, mirrorIterate ρ₀ ℓs T (k+1) v * ℓs k v)
          - (∑ v, ρ v * ℓs k v)))
      + T * (∑ v, ρ v * Real.log (ρ v
          / mirrorIterate ρ₀ ℓs T n v))
      ≤ T * (∑ v, ρ v * Real.log (ρ v / ρ₀ v)) := by
    intro n
    induction n with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, add_zero]
        have h0 : ∀ v, mirrorIterate ρ₀ ℓs T 0 v = ρ₀ v :=
          fun v => rfl
        simp only [h0, zero_add]
        exact le_of_eq rfl
    | succ m ih =>
        rw [Finset.sum_range_succ]
        -- одношаговое неравенство на шаге m
        have hposm : ∀ v, 0 < mirrorIterate ρ₀ ℓs T m v :=
          mirrorIterate_pos ρ₀ ℓs T hT hρ₀ m
        have h1m : ∑ v, mirrorIterate ρ₀ ℓs T m v = 1 :=
          mirrorIterate_sum_one ρ₀ ℓs T hT hρ₀ hρ₀1 m
        have hstep := mirror_step_regret
          (mirrorIterate ρ₀ ℓs T m) (ℓs m) T hT hposm h1m
          ρ hρ hρ1
        -- w_{m+1} = mirrorStep w_m ℓ_m T по определению
        have hdef : mirrorIterate ρ₀ ℓs T (m+1)
            = mirrorStep (mirrorIterate ρ₀ ℓs T m) (ℓs m) T := by
          simp only [mirrorIterate]
        rw [hdef]
        linarith
  have h := key n
  -- финальный KL ≥ 0 → регрет ≤ границы
  have hposn : ∀ v, 0 < mirrorIterate ρ₀ ℓs T n v :=
    mirrorIterate_pos ρ₀ ℓs T hT hρ₀ n
  have h1n : ∑ v, mirrorIterate ρ₀ ℓs T n v = 1 :=
    mirrorIterate_sum_one ρ₀ ℓs T hT hρ₀ hρ₀1 n
  have hkl : (0:ℝ) ≤ T * (∑ v, ρ v * Real.log (ρ v
      / mirrorIterate ρ₀ ℓs T n v)) :=
    mul_nonneg (le_of_lt hT)
      (finite_kl_nonneg ρ (mirrorIterate ρ₀ ℓs T n)
        hρ hρ1 hposn h1n)
  linarith


/-- ПОЛУГРУППОВОЙ ЗАКОН ЗЕРКАЛЬНОГО ШАГА: два
последовательных зеркальных шага (ℓ₁, затем ℓ₂, одна
температура T) равны одному шагу с суммарными потерями
ℓ₁+ℓ₂ — экспоненциальные веса перемножаются, нормировки
согласованы (Z₂·Z₁ = Z₁₂): траектория hedge за n шагов
есть один шаг с кумулятивными потерями. -/
theorem mirror_step_semigroup {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ₁ ℓ₂ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) :
    mirrorStep (mirrorStep ρ₀ ℓ₁ T) ℓ₂ T
      = mirrorStep ρ₀ (fun v => ℓ₁ v + ℓ₂ v) T := by
  have hγpos : ∀ w, 0 < mirrorStep ρ₀ ℓ₁ T w :=
    mirrorStep_pos ρ₀ ℓ₁ T hT hρ₀
  have hZ₁ : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-(ℓ₁ w)/T) :=
    Finset.sum_pos
      (fun w _ => mul_pos (hρ₀ w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hZ₂ : (0:ℝ) < ∑ w, mirrorStep ρ₀ ℓ₁ T w
      * Real.exp (-(ℓ₂ w)/T) :=
    Finset.sum_pos
      (fun w _ => mul_pos (hγpos w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have he : ∀ w : V, Real.exp (-(ℓ₁ w)/T)
      * Real.exp (-(ℓ₂ w)/T)
      = Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    intro w
    rw [← Real.exp_add]
    congr 1
    ring
  -- почленно: γ₁(w)·e^{−ℓ₂/T}·Z₁ = ρ₀(w)·e^{−(ℓ₁+ℓ₂)/T}
  have hterm : ∀ w : V, mirrorStep ρ₀ ℓ₁ T w
      * Real.exp (-(ℓ₂ w)/T)
      * (∑ u, ρ₀ u * Real.exp (-(ℓ₁ u)/T))
      = ρ₀ w * Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    intro w
    unfold mirrorStep
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hZ₁.ne',
      show ρ₀ w * Real.exp (-(ℓ₁ w)/T)
          * Real.exp (-(ℓ₂ w)/T)
        = ρ₀ w * (Real.exp (-(ℓ₁ w)/T)
            * Real.exp (-(ℓ₂ w)/T)) from by ring, he w]
  -- суммарно: Z₂·Z₁ = Z₁₂
  have hsum : (∑ w, mirrorStep ρ₀ ℓ₁ T w
      * Real.exp (-(ℓ₂ w)/T))
      * (∑ u, ρ₀ u * Real.exp (-(ℓ₁ u)/T))
      = ∑ w, ρ₀ w * Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun w _ => hterm w)
  -- поэлементное совпадение
  funext v
  have htermv : mirrorStep ρ₀ ℓ₁ T v
      * Real.exp (-(ℓ₂ v)/T)
      = ρ₀ v * Real.exp (-(ℓ₁ v + ℓ₂ v)/T)
        / (∑ u, ρ₀ u * Real.exp (-(ℓ₁ u)/T)) :=
    eq_div_of_mul_eq hZ₁.ne' (hterm v)
  have hL : mirrorStep (mirrorStep ρ₀ ℓ₁ T) ℓ₂ T v
      = (mirrorStep ρ₀ ℓ₁ T v * Real.exp (-(ℓ₂ v)/T))
        / (∑ w, mirrorStep ρ₀ ℓ₁ T w
            * Real.exp (-(ℓ₂ w)/T)) := rfl
  have hR : mirrorStep ρ₀ (fun v => ℓ₁ v + ℓ₂ v) T v
      = ρ₀ v * Real.exp (-(ℓ₁ v + ℓ₂ v)/T)
        / (∑ w, ρ₀ w
            * Real.exp (-(ℓ₁ w + ℓ₂ w)/T)) := by
    dsimp only [mirrorStep]
  rw [hL, hR, htermv, ← hsum]
  field_simp

/-- НУЛЕВЫЕ ПОТЕРИ: зеркальный шаг при ℓ = 0 возвращает
ссылку (Z = Σρ₀·e⁰ = 1): тождественное обновление. -/
theorem mirrorStep_zero_loss {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1) :
    mirrorStep ρ₀ (fun _ => 0) T = ρ₀ := by
  have hexp : ∀ w : V, Real.exp (-(0:ℝ)/T) = 1 := by
    intro w
    have hz : (-(0:ℝ)/T) = 0 := by
      rw [neg_zero, zero_div]
    rw [hz, Real.exp_zero]
  have hZ : (∑ w, ρ₀ w * Real.exp (-(0:ℝ)/T)) = 1 := by
    rw [Finset.sum_congr rfl (fun w _ => by rw [hexp w, mul_one])]
    exact hρ₀1
  funext v
  have hnum : ρ₀ v * Real.exp (-(0:ℝ)/T) = ρ₀ v := by
    rw [hexp v, mul_one]
  unfold mirrorStep
  rw [hZ, div_one, hnum]

/-- N-КРАТНЫЙ ПОЛУГРУППОВОЙ ЗАКОН: траектория hedge за n
шагов есть ОДИН зеркальный шаг с кумулятивными потерями
Σ_{k<n} ℓ_k: экспоненциальные веса накапливают потери
аддитивно, нормировки глобальны. -/
theorem mirrorIterate_cumulative {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ)
    (hT : 0 < T) (hρ₀ : ∀ v, 0 < ρ₀ v)
    (hρ₀1 : ∑ v, ρ₀ v = 1) (n : ℕ) :
    mirrorIterate ρ₀ ℓs T n
      = mirrorStep ρ₀
          (fun v => ∑ k ∈ Finset.range n, ℓs k v) T := by
  induction n with
  | zero =>
      have h0 : mirrorIterate ρ₀ ℓs T 0 = ρ₀ := rfl
      rw [h0]
      exact (mirrorStep_zero_loss ρ₀ T hT hρ₀ hρ₀1).symm
  | succ m ih =>
      have hdef : mirrorIterate ρ₀ ℓs T (m+1)
          = mirrorStep (mirrorIterate ρ₀ ℓs T m) (ℓs m) T := by
        simp only [mirrorIterate]
      rw [hdef, ih, mirror_step_semigroup ρ₀
        (fun v => ∑ k ∈ Finset.range m, ℓs k v) (ℓs m) T hT hρ₀]
      congr 1
      funext v
      simp only [Finset.sum_range_succ]

/-- МОНОТОННОСТЬ ЭНЕРГИИ HEDGE: зеркальный шаг по потерям ℓ
никогда не поднимает ожидаемые потери по ним:
⟨mirrorStep ρ₀ ℓ T, ℓ⟩ ≤ ⟨ρ₀, ℓ⟩. Цепочка:
⟨γ,ℓ⟩ ≤ F(γ) (KL(γ‖ρ₀) ≥ 0), F(γ) = −T·log Z
(attainment), −T·log Z ≤ ⟨ρ₀,ℓ⟩ (Йенсен выпуклости exp:
e^{−⟨ρ₀,ℓ⟩/T} ≤ Z). -/
theorem mirror_energy_decrease {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1) :
    (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v) ≤ (∑ v, ρ₀ v * ℓ v) := by
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  have hγ1 : ∑ v, mirrorStep ρ₀ ℓ T v = 1 :=
    mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  -- KL(γ‖ρ₀) ≥ 0
  have hkl : (0:ℝ) ≤ ∑ v, mirrorStep ρ₀ ℓ T v
      * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v) :=
    finite_kl_nonneg (mirrorStep ρ₀ ℓ T) ρ₀ hγpos hγ1 hρ₀ hρ₀1
  -- attainment: F(γ) = −T·log Z
  have hatt := mirror_descent_attainment ρ₀ ℓ T hT hρ₀
  -- Йенсен: e^{−⟨ρ₀,ℓ⟩/T} ≤ Z
  have hZpos : (0:ℝ) < ∑ v, ρ₀ v * Real.exp (-(ℓ v)/T) :=
    Finset.sum_pos
      (fun v _ => mul_pos (hρ₀ v) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hjensen : Real.exp ((∑ v, ρ₀ v * (-(ℓ v)/T)))
      ≤ ∑ v, ρ₀ v * Real.exp (-(ℓ v)/T) := by
    have hconv := convexOn_exp.map_sum_le
      (p := fun v => -(ℓ v)/T)
      (fun v _ => le_of_lt (hρ₀ v)) hρ₀1
      (fun v _ => Set.mem_univ v)
    simp only [smul_eq_mul] at hconv
    exact hconv
  -- log-монотонность: −⟨ρ₀,ℓ⟩/T ≤ log Z
  have hlogj : (∑ v, ρ₀ v * (-(ℓ v)/T))
      ≤ Real.log (∑ v, ρ₀ v * Real.exp (-(ℓ v)/T)) := by
    have h1 := Real.log_le_log (Real.exp_pos _) hjensen
    rw [Real.log_exp] at h1
    exact h1
  -- линейная сборка
  have hsplit : (∑ v, ρ₀ v * (-(ℓ v)/T))
      = -(∑ v, ρ₀ v * ℓ v)/T := by
    have hterm : ∀ v : V, ρ₀ v * (-(ℓ v)/T)
        = -(ρ₀ v * ℓ v)/T := by
      intro v
      ring
    rw [Finset.sum_congr rfl (fun v _ => hterm v),
      ← Finset.sum_neg_distrib, ← Finset.sum_div]
  rw [hsplit] at hlogj
  -- финал: ⟨γ,ℓ⟩ ≤ F(γ) = −T log Z ≤ ⟨ρ₀,ℓ⟩
  have hTKL : (0:ℝ) ≤ T * (∑ v, mirrorStep ρ₀ ℓ T v
      * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)) :=
    mul_nonneg (le_of_lt hT) hkl
  have h1 : (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
      ≤ (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
        + T * (∑ v, mirrorStep ρ₀ ℓ T v
            * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)) := by
    linarith
  have h2 : ((∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
        + T * (∑ v, mirrorStep ρ₀ ℓ T v
            * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)))
      = -T * Real.log (∑ v, ρ₀ v * Real.exp (-(ℓ v)/T)) :=
    hatt
  rw [h2] at h1
  -- −T·logZ ≤ ⟨ρ₀,ℓ⟩ из hlogj (умножение на T > 0)
  have h3 : -T * Real.log (∑ v, ρ₀ v * Real.exp (-(ℓ v)/T))
      ≤ ∑ v, ρ₀ v * ℓ v := by
    have h4 := (mul_le_mul_of_nonneg_left hlogj (le_of_lt hT))
    -- T·(−⟨ρ₀,ℓ⟩/T) ≤ T·logZ ; T·(−X/T) = −X
    have h5 : T * (-(∑ v, ρ₀ v * ℓ v)/T)
        = -(∑ v, ρ₀ v * ℓ v) := by
      field_simp
    rw [h5] at h4
    linarith
  linarith [hkl, hT]

/-- МОНОТОННОСТЬ ЭНЕРГИИ ВДОЛЬ ТРАЕКТОРИИ: при фиксированных
потерях ℓ повторные зеркальные шаги монотонно не поднимают
ожидаемую энергию: ⟨w_n, ℓ⟩ ≤ ⟨ρ₀, ℓ⟩ для всех n —
итерированный hedge сходится по энергии (индукция из
mirror_energy_decrease). -/
theorem mirrorIterate_energy_monotone {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (n : ℕ) :
    (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
      ≤ (∑ v, ρ₀ v * ℓ v) := by
  induction n with
  | zero =>
      have h0 : mirrorIterate ρ₀ (fun _ => ℓ) T 0 = ρ₀ := rfl
      rw [h0]
  | succ m ih =>
      have hdef : mirrorIterate ρ₀ (fun _ => ℓ) T (m+1)
          = mirrorStep (mirrorIterate ρ₀ (fun _ => ℓ) T m) ℓ T :=
        by simp only [mirrorIterate]
      rw [hdef]
      have hpos : ∀ v, 0 < mirrorIterate ρ₀ (fun _ => ℓ) T m v :=
        mirrorIterate_pos ρ₀ (fun _ => ℓ) T hT hρ₀ m
      have h1 : ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T m v = 1 :=
        mirrorIterate_sum_one ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1 m
      have hstep := mirror_energy_decrease
        (mirrorIterate ρ₀ (fun _ => ℓ) T m) ℓ T hT hpos h1
      linarith

/-- СХОДИМОСТЬ ЭНЕРГИИ ИТЕРАЦИЙ: при фиксированных потерях ℓ
с нижней границей C последовательность энергий
e_n = ⟨w_n, ℓ⟩ убывает шаг за шагом и ограничена снизу,
поэтому входит в ε-коридор над своим инфимумом L:
∀n≥N: L ≤ e_n ≤ L + ε — итерированный hedge сходится по
энергии (полнота ℝ + монотонность). -/
theorem mirrorIterate_energy_converges {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (C : ℝ) (hC : ∀ v, C ≤ ℓ v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (sInf (Set.range (fun k =>
          ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T k v * ℓ v)))
        ≤ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
      ∧ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
        ≤ (sInf (Set.range (fun k =>
            ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T k v * ℓ v))) + ε := by
  set e : ℕ → ℝ := fun k =>
    ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T k v * ℓ v with he
  -- соседняя монотонность: e_{n+1} ≤ e_n
  have hstep : ∀ n : ℕ, e (n+1) ≤ e n := by
    intro n
    have hpos : ∀ v, 0 < mirrorIterate ρ₀ (fun _ => ℓ) T n v :=
      mirrorIterate_pos ρ₀ (fun _ => ℓ) T hT hρ₀ n
    have h1 : ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v = 1 :=
      mirrorIterate_sum_one ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1 n
    have hdef : mirrorIterate ρ₀ (fun _ => ℓ) T (n+1)
        = mirrorStep (mirrorIterate ρ₀ (fun _ => ℓ) T n) ℓ T :=
      by simp only [mirrorIterate]
    have hdec := mirror_energy_decrease
      (mirrorIterate ρ₀ (fun _ => ℓ) T n) ℓ T hT hpos h1
    rw [he]
    show (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T (n+1) v * ℓ v)
        ≤ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
    rw [hdef]
    exact hdec
  -- цепная монотонность: m ≤ n → e_n ≤ e_m
  have hchain : ∀ n m : ℕ, m ≤ n → e n ≤ e m := by
    intro n
    induction n with
    | zero =>
        intro m hm
        have h0 : m = 0 := Nat.le_zero.mp hm
        subst h0
        exact le_refl _
    | succ k ih =>
        intro m hm
        rcases Nat.lt_or_ge m (k+1) with hlt | hge
        · have hk : m ≤ k := Nat.lt_succ_iff.mp hlt
          have a := hstep k
          have b := ih m hk
          linarith
        · have h0 : m = k+1 := Nat.le_antisymm hm hge
          subst h0
          exact le_refl _
  -- ограниченность снизу: C ≤ e_n
  have hbdd : ∀ n : ℕ, C ≤ e n := by
    intro n
    have hpos : ∀ v, 0 < mirrorIterate ρ₀ (fun _ => ℓ) T n v :=
      mirrorIterate_pos ρ₀ (fun _ => ℓ) T hT hρ₀ n
    have h1 : ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v = 1 :=
      mirrorIterate_sum_one ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1 n
    have hle : ∀ v : V, mirrorIterate ρ₀ (fun _ => ℓ) T n v * C
        ≤ mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v :=
      fun v => mul_le_mul_of_nonneg_left (hC v) (le_of_lt (hpos v))
    have hsplit : (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * C)
        ≤ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v) :=
      Finset.sum_le_sum fun v _ => hle v
    have hsumC : (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * C) = C := by
      rw [Finset.sum_congr rfl (fun v _ =>
        mul_comm (mirrorIterate ρ₀ (fun _ => ℓ) T n v) C),
        ← Finset.mul_sum, h1, mul_one]
    rw [he]
    linarith
  -- инфимум L и его свойства
  set L := sInf (Set.range e) with hL
  have hrng : (Set.range e).Nonempty := ⟨e 0, Set.mem_range_self 0⟩
  have hbddBelow : BddBelow (Set.range e) :=
    ⟨C, fun y hy => by
      obtain ⟨n, hn⟩ := Set.mem_range.mp hy
      rw [← hn]
      exact hbdd n⟩
  have hleL : ∀ n : ℕ, L ≤ e n :=
    fun n => csInf_le hbddBelow (Set.mem_range_self n)
  -- ∃ N: e N ≤ L + ε (иначе L+ε — меньшая нижняя граница)
  have hex : ∃ N : ℕ, e N ≤ L + ε := by
    by_contra hcon
    push_neg at hcon
    have hle' : L + ε ≤ L :=
      le_csInf hrng (fun y hy => by
        obtain ⟨n, hn⟩ := Set.mem_range.mp hy
        rw [← hn]
        exact le_of_lt (hcon n))
    linarith
  obtain ⟨N, hN⟩ := hex
  refine ⟨N, fun n hn => ⟨hleL n, ?_⟩⟩
  have h1 := hchain n N hn
  linarith


end Hagi.Optimization
