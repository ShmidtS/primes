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
import Hagi.Optimization.MirrorHedgeRegret

set_option linter.style.header false

/-!
# MirrorHedgeEnergy

Энергетическая монотонность итераций: mirrorIterate_energy_monotone/converges и термодинамический предел mirrorIterate_energy_infimum (Nernst), stepNorm и compose.
Split from `MirrorHedge` (C259).
-/

namespace Hagi.Optimization

open Finset

/-- NERNST-ПРЕДЕЛ ИТЕРАЦИЙ HEDGE: при фиксированных потерях ℓ
повторные зеркальные шаги сходятся по энергии к минимуму
потерь: ∀ε>0 ∃N ∀n≥N: ℓmin ≤ ⟨w_n, ℓ⟩ ≤ ℓmin + ε.
Механизм: w_n = mirrorStep ρ₀ (n·ℓ) T (кумулятивность),
свободная энергия F_n ≤ n·ℓmin − T·log(min ρ₀)
(Z_n ≥ min ρ₀ · e^{−nℓmin/T}), и KL-слагаемое ≥ 0 —
итерированный hedge находит минимум (термодинамический
предел T/n → 0). -/
theorem mirrorIterate_energy_infimum {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Finset.min' (Finset.univ.image ℓ)
          (Finset.image_nonempty.2 Finset.univ_nonempty))
        ≤ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
      ∧ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
        ≤ (Finset.min' (Finset.univ.image ℓ)
            (Finset.image_nonempty.2 Finset.univ_nonempty)) + ε := by
  have hneℓ : (Finset.univ.image ℓ).Nonempty :=
    Finset.image_nonempty.2 Finset.univ_nonempty
  have hneρ : (Finset.univ.image ρ₀).Nonempty :=
    Finset.image_nonempty.2 Finset.univ_nonempty
  set m := Finset.min' (Finset.univ.image ℓ) hneℓ with hm
  set r := Finset.min' (Finset.univ.image ρ₀) hneρ with hr
  -- минимумы достижимы и ограничивают
  obtain ⟨vt, hvt⟩ := Finset.mem_image.mp (Finset.min'_mem _ hneℓ)
  have hmle : ∀ v : V, m ≤ ℓ v := fun v =>
    Finset.min'_le (Finset.univ.image ℓ) (ℓ v)
      (Finset.mem_image_of_mem ℓ (Finset.mem_univ v))
  have hrle : ∀ v : V, r ≤ ρ₀ v := fun v =>
    Finset.min'_le (Finset.univ.image ρ₀) (ρ₀ v)
      (Finset.mem_image_of_mem ρ₀ (Finset.mem_univ v))
  obtain ⟨wt, hwt⟩ := Finset.mem_image.mp (Finset.min'_mem _ hneρ)
  have hrw : r = ρ₀ wt := hwt.2.symm
  have hrpos : (0:ℝ) < r := by rw [hrw]; exact hρ₀ wt
  have hrle1 : r ≤ 1 := by
    rw [hrw]
    have h1 := Finset.single_le_sum
      (fun w _ => le_of_lt (hρ₀ w)) (Finset.mem_univ wt)
    rw [hρ₀1] at h1
    exact h1
  have hlogr : Real.log r ≤ 0 :=
    (Real.log_le_log hrpos hrle1).trans_eq Real.log_one
  -- кумулятивность: w_n = mirrorStep ρ₀ (n·ℓ) T
  have hsum : ∀ (n : ℕ) (v : V),
      (∑ k ∈ Finset.range n, ℓ v) = (n : ℝ) * ℓ v := by
    intro n v
    simp
  have hwn : ∀ n : ℕ, mirrorIterate ρ₀ (fun _ => ℓ) T n
      = mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T := by
    intro n
    rw [mirrorIterate_cumulative ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1 n]
    congr 1
    funext v
    rw [hsum n v]
  -- нижняя граница энергии: e_n ≥ m
  have hposn : ∀ (n : ℕ) (v : V),
      0 < mirrorIterate ρ₀ (fun _ => ℓ) T n v :=
    mirrorIterate_pos ρ₀ (fun _ => ℓ) T hT hρ₀
  have h1n : ∀ n : ℕ,
      ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v = 1 :=
    mirrorIterate_sum_one ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1
  have hlower : ∀ n : ℕ, m ≤ (∑ v,
      mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v) := by
    intro n
    have hle : ∀ v : V,
        mirrorIterate ρ₀ (fun _ => ℓ) T n v * m
        ≤ mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v :=
      fun v => mul_le_mul_of_nonneg_left (hmle v)
        (le_of_lt (hposn n v))
    have hsplit := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hle v)
    have hsumC : (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * m) = m := by
      rw [Finset.sum_congr rfl (fun v _ =>
        mul_comm (mirrorIterate ρ₀ (fun _ => ℓ) T n v) m),
        ← Finset.mul_sum, h1n n, mul_one]
    rw [hsumC] at hsplit
    exact hsplit
  -- верхняя граница: e_n ≤ m + (T/n)·(−log r)
  have hupper : ∀ n : ℕ, (0:ℕ) < n → (∑ v,
      mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
      ≤ m + T * (-(Real.log r)) / (n : ℝ) := by
    intro n hn
    -- KL(w_n ‖ ρ₀) ≥ 0 и attainment для n·ℓ
    have hγpos : ∀ v, 0 < mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v :=
      mirrorStep_pos ρ₀ (fun v => (n : ℝ) * ℓ v) T hT hρ₀
    have hγ1 : ∑ v, mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v = 1 :=
      mirrorStep_sum_one ρ₀ (fun v => (n : ℝ) * ℓ v) T hT hρ₀
    have hkl : (0:ℝ) ≤ T * (∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v
        * Real.log (mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v / ρ₀ v)) :=
      mul_nonneg (le_of_lt hT)
        (finite_kl_nonneg (mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T)
          ρ₀ hγpos hγ1 hρ₀ hρ₀1)
    -- attainment: ⟨γ, nℓ⟩ + T·KL = −T·log Z_n
    have hatt := mirror_descent_attainment ρ₀
      (fun v => (n : ℝ) * ℓ v) T hT hρ₀
    -- нижняя оценка Z_n ≥ r · e^{−nm/T} через vt
    have hZge : (∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T))
        ≥ ρ₀ vt * Real.exp (-((n : ℝ) * m)/T) := by
      have hterm := Finset.single_le_sum
        (f := fun w => ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T))
        (fun w (_ : w ∈ Finset.univ) =>
          mul_nonneg (le_of_lt (hρ₀ w)) (Real.exp_nonneg _))
        (Finset.mem_univ vt)
      rw [hvt.2] at hterm
      exact hterm
    have hrr : ρ₀ vt ≥ r := hrle vt
    have hZge2 : (∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T))
        ≥ r * Real.exp (-((n : ℝ) * m)/T) := by
      nlinarith [hZge, hrr, (Real.exp_pos
        (-((n : ℝ) * m)/T))]
    -- log-монотонность
    have hZpos : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T) := by
      have h0 : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
        mul_pos hrpos (Real.exp_pos _)
      linarith
    have hrpos' : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
      mul_pos hrpos (Real.exp_pos _)
    have hlog : Real.log (r * Real.exp (-((n : ℝ) * m)/T))
        ≤ Real.log (∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T)) :=
      Real.log_le_log hrpos' hZge2
    -- log(r·e^{−nm/T}) = log r − nm/T
    have hlogsplit : Real.log (r * Real.exp (-((n : ℝ) * m)/T))
        = Real.log r + (-((n : ℝ) * m)/T) := by
      rw [Real.log_mul hrpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    rw [hlogsplit] at hlog
    -- собираем: e_n = ⟨γ, ℓ⟩ и ⟨γ, nℓ⟩ = n·e_n
    rw [hwn n]
    have hmul : (∑ v, mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v
        * ((n : ℝ) * ℓ v))
        = (n : ℝ) * (∑ v, mirrorStep ρ₀
            (fun v => (n : ℝ) * ℓ v) T v * ℓ v) := by
      rw [Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) =>
        show mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v
            * ((n : ℝ) * ℓ v)
          = (n : ℝ) * (mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v
              * ℓ v) from by ring)]
      exact (Finset.mul_sum _ _ _).symm
    -- финальная арифметика
    have hnne : ((n : ℝ)) ≠ 0 := by
      have : (0:ℕ) < n := hn
      exact_mod_cast this.ne'
    rw [hmul] at hatt
    -- hlog, умноженный на T: T·log r − n·m ≤ T·logZ
    have hDTneg : T * (-(((n : ℝ) * m)/T))
        = -((n : ℝ) * m) := by
      have hDT : T * (((n : ℝ) * m)/T) = (n : ℝ) * m := by
        field_simp
      have hsplit : T * (-(((n : ℝ) * m)/T))
          = -(T * (((n : ℝ) * m)/T)) := by ring
      rw [hsplit, hDT]
    have hlog' : T * (Real.log r + -(((n : ℝ) * m)/T))
        ≤ T * Real.log (∑ w, ρ₀ w
          * Real.exp (-((n : ℝ) * ℓ w)/T)) := by
      have h := mul_le_mul_of_nonneg_left
        (show Real.log r + -((n : ℝ) * m)/T
            ≤ Real.log (∑ w, ρ₀ w
              * Real.exp (-((n : ℝ) * ℓ w)/T)) from hlog)
        (le_of_lt hT)
      have hnorm : T * (Real.log r + -(((n : ℝ) * m)/T))
          = T * (Real.log r + -((n : ℝ) * m)/T) := by
        congr 1
        congr 1
        field_simp
      rw [hnorm]
      exact h
    have hsplit : T * (Real.log r + -(((n : ℝ) * m)/T))
        = T * Real.log r - (n : ℝ) * m := by
      rw [mul_add, hDTneg]
      ring
    rw [hsplit] at hlog'
    -- hlog' : T·log r − n·m ≤ T·logZ
    -- n·e_n ≤ n·m − T·log r
    have hkey : ((n : ℝ)) * (∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v * ℓ v)
        ≤ (n : ℝ) * m + T * (-(Real.log r)) := by
      linarith [hatt, hkl, hlog']
    -- деление на n > 0
    have hnposR : (0:ℝ) < (n : ℝ) := by
      have := hn; exact_mod_cast this
    have hkey' : ((n : ℝ)) * ((∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v * ℓ v) - m)
        ≤ T * (-(Real.log r)) := by
      nlinarith [hkey]
    have hmuln : ((∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v * ℓ v) - m) * (n : ℝ)
        ≤ T * (-(Real.log r)) := by
      nlinarith [hkey']
    have hdiv : (∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v * ℓ v) - m
        ≤ T * (-(Real.log r)) / (n : ℝ) :=
      (le_div_iff₀ hnposR).mpr hmuln
    linarith
  -- выбор N: T·(−log r)/ε ≤ N
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      T * (-(Real.log r)) / ε ≤ N :=
    exists_nat_ge (T * (-(Real.log r)) / ε)
  refine ⟨N + 1, fun n hn => ⟨hlower n, ?_⟩⟩
  have hnpos : (0:ℕ) < n := by omega
  have hbound := hupper n hnpos
  -- (T/n)(−log r) ≤ ε при n ≥ N+1 > N ≥ T(−log r)/ε
  have hnN : ((N : ℝ)) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hNge : T * (-(Real.log r)) ≤ (N : ℝ) * ε :=
    (div_le_iff₀ hε).mp hN
  have hnnz : ((n : ℝ)) ≠ 0 := by
    have : (0:ℕ) < n := hnpos
    exact_mod_cast this.ne'
  have hfin : T * (-(Real.log r)) / (n : ℝ) ≤ ε := by
    rw [div_le_iff₀ (show (0:ℝ) < (n : ℝ) by
      have := hnpos; exact_mod_cast this)]
    -- T(−log r) ≤ n·ε ⟸ N·ε ≤ n·ε и T(−log r) ≤ N·ε
    nlinarith [hNge, hnN, hε]
  linarith

/-- Пошаговая нормировка зеркального шага: Z(ρ₀,ℓ,T) =
Σ ρ₀·e^{−ℓ/T} — коэффициент перенормировки весов. -/
noncomputable def stepNorm {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) : ℝ :=
  ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T)

/-- НОРМИРОВКИ ПЕРЕМНОЖАЮТСЯ: нормировка двух
последовательных шагов равна нормировке одного шага с
суммарными потерями: Z(γ₁,ℓ₂)·Z(ρ₀,ℓ₁) = Z(ρ₀,ℓ₁+ℓ₂) —
двойник полугруппового закона на уровне нормировок
(свидетельство: hedge-капитал телескопирует). -/
theorem stepNorm_compose {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ₁ ℓ₂ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) :
    stepNorm (mirrorStep ρ₀ ℓ₁ T) ℓ₂ T * stepNorm ρ₀ ℓ₁ T
      = stepNorm ρ₀ (fun v => ℓ₁ v + ℓ₂ v) T := by
  have hγpos : ∀ w, 0 < mirrorStep ρ₀ ℓ₁ T w :=
    mirrorStep_pos ρ₀ ℓ₁ T hT hρ₀
  have hZ₁ : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-(ℓ₁ w)/T) :=
    Finset.sum_pos
      (fun w _ => mul_pos (hρ₀ w) (Real.exp_pos _))
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
  -- суммирование
  unfold stepNorm
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun w _ => hterm w)


end Hagi.Optimization
