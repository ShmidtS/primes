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
import Hagi.Optimization.MirrorHedgeEnergy

set_option linter.style.header false

/-!
# MirrorHedgeWealth

Hedge-капитал: hedge_wealth_product (телескопирование нормировок), hedge_wealth_nernst, hedge_wealth_rate, mirror_step_variational_descent, mirrorIterate_partial_mono.
Split from `MirrorHedge` (C259).
-/

namespace Hagi.Optimization

open Finset

/-- КАПИТАЛ HEDGE ТЕЛЕСКОПИРУЕТ: произведение пошаговых
нормировок траектории равно кумулятивной нормировке:
∏_{k<n} Z(w_k, ℓ_k, T) = Z(ρ₀, Σ_{k<n} ℓ_k, T) —
потенциал-функция MWU/Hedge в замкнутой форме. -/
theorem hedge_wealth_product {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1) (n : ℕ) :
    (∏ k ∈ Finset.range n,
        stepNorm (mirrorIterate ρ₀ ℓs T k) (ℓs k) T)
      = stepNorm ρ₀ (fun v => ∑ k ∈ Finset.range n, ℓs k v) T := by
  induction n with
  | zero =>
      show (1:ℝ) = stepNorm ρ₀
        (fun v => ∑ k ∈ Finset.range 0, ℓs k v) T
      simp only [Finset.range_zero, Finset.sum_empty, neg_zero,
        div_zero, Real.exp_zero, mul_one, stepNorm, zero_div]
      exact hρ₀1.symm
  | succ m ih =>
      -- кумулятивность: w_m = mirrorStep ρ₀ (Σ_{<m}) T
      have hcum : mirrorIterate ρ₀ ℓs T m
          = mirrorStep ρ₀ (fun v => ∑ k ∈ Finset.range m, ℓs k v) T :=
        mirrorIterate_cumulative ρ₀ ℓs T hT hρ₀ hρ₀1 m
      -- композиция нормировок на уровне ρ₀
      have hcomp := stepNorm_compose ρ₀
        (fun v => ∑ k ∈ Finset.range m, ℓs k v) (ℓs m) T hT hρ₀
      -- кумулятивная сумма range (m+1)
      have hsum : (fun v => ∑ k ∈ Finset.range (m+1), ℓs k v)
          = (fun v => (∑ k ∈ Finset.range m, ℓs k v) + ℓs m v) := by
        funext v
        rw [Finset.sum_range_succ]
      rw [Finset.prod_range_succ, hsum, ih, hcum, mul_comm,
        ← hcomp]

/-- НЕРНСТ-СЭНДВИЧ КАПИТАЛА HEDGE: логарифм капитала
(произведения пошаговых нормировок) зажат:
n·ℓmin − T·log|V| ≤ −T·log(∏ Z_k) ≤ n·ℓmin − T·log(min ρ₀).
Низ: каждый член ≤ e^{−nℓmin/T}, сумма ≤ |V|·e^{−nm/T};
верх: Z ≥ (min ρ₀)·e^{−nℓmin/T} — кумулятивная свободная
энергия итераций зажата энтропийным запасом и минимальным
априорным весом (термодинамический предел капитала). -/
theorem hedge_wealth_nernst {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (n : ℕ) :
    ((n : ℝ) * (Finset.min' (Finset.univ.image ℓ)
          (Finset.image_nonempty.2 Finset.univ_nonempty))
        - T * Real.log (Fintype.card V : ℝ)
      ≤ -T * Real.log (∏ k ∈ Finset.range n,
          stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T))
    ∧ (-T * Real.log (∏ k ∈ Finset.range n,
          stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T)
      ≤ (n : ℝ) * (Finset.min' (Finset.univ.image ℓ)
          (Finset.image_nonempty.2 Finset.univ_nonempty))
        - T * Real.log (Finset.min' (Finset.univ.image ρ₀)
          (Finset.image_nonempty.2 Finset.univ_nonempty))) := by
  set m := Finset.min' (Finset.univ.image ℓ)
    (Finset.image_nonempty.2 Finset.univ_nonempty) with hm
  set r := Finset.min' (Finset.univ.image ρ₀)
    (Finset.image_nonempty.2 Finset.univ_nonempty) with hr
  have hneℓ : (Finset.univ.image ℓ).Nonempty :=
    Finset.image_nonempty.2 Finset.univ_nonempty
  have hneρ : (Finset.univ.image ρ₀).Nonempty :=
    Finset.image_nonempty.2 Finset.univ_nonempty
  obtain ⟨vt, hvt⟩ := Finset.mem_image.mp (Finset.min'_mem _ hneℓ)
  obtain ⟨wt, hwt⟩ := Finset.mem_image.mp (Finset.min'_mem _ hneρ)
  have hmle : ∀ v : V, m ≤ ℓ v := fun v =>
    Finset.min'_le (Finset.univ.image ℓ) (ℓ v)
      (Finset.mem_image_of_mem ℓ (Finset.mem_univ v))
  have hrle : ∀ v : V, r ≤ ρ₀ v := fun v =>
    Finset.min'_le (Finset.univ.image ρ₀) (ρ₀ v)
      (Finset.mem_image_of_mem ρ₀ (Finset.mem_univ v))
  have hrpos : (0:ℝ) < r := by
    have hrw : r = ρ₀ wt := hwt.2.symm
    rw [hrw]; exact hρ₀ wt
  -- капитал = кумулятивная нормировка
  have hwealth := hedge_wealth_product ρ₀ (fun _ => ℓ) T hT hρ₀
    hρ₀1 n
  set Z : ℝ := stepNorm ρ₀
    (fun v => ∑ k ∈ Finset.range n, ℓ v) T with hZ
  have hZn : Z = ∑ w, ρ₀ w
      * Real.exp (-((n : ℝ) * ℓ w)/T) := by
    rw [hZ]
    refine Finset.sum_congr rfl fun w _ => ?_
    show ρ₀ w * Real.exp ((-∑ k ∈ Finset.range n, ℓ w)/T)
      = ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Z ≥ r·e^{−nm/T}
  have hZge : r * Real.exp (-((n : ℝ) * m)/T) ≤ Z := by
    rw [hZn]
    have hterm := Finset.single_le_sum
      (f := fun w => ρ₀ w
        * Real.exp (-((n : ℝ) * ℓ w)/T))
      (fun w (_ : w ∈ Finset.univ) =>
        mul_nonneg (le_of_lt (hρ₀ w)) (Real.exp_nonneg _))
      (Finset.mem_univ vt)
    rw [hvt.2] at hterm
    nlinarith [hterm, hrle vt, Real.exp_pos
      (-((n : ℝ) * m)/T)]
  -- Z ≤ |V|·e^{−nm/T}
  have hZle : Z ≤ (Fintype.card V : ℝ)
      * Real.exp (-((n : ℝ) * m)/T) := by
    rw [hZn]
    have hterm : ∀ w : V, ρ₀ w
        * Real.exp (-((n : ℝ) * ℓ w)/T)
        ≤ Real.exp (-((n : ℝ) * m)/T) := by
      intro w
      have h1 : ρ₀ w ≤ 1 := by
        have hs := Finset.single_le_sum
          (fun u (_ : u ∈ Finset.univ) => le_of_lt (hρ₀ u))
          (Finset.mem_univ w)
        rw [hρ₀1] at hs
        exact hs
      have h2 : Real.exp (-((n : ℝ) * ℓ w)/T)
          ≤ Real.exp (-((n : ℝ) * m)/T) := by
        refine Real.exp_le_exp.mpr ?_
        have hnle : ((n : ℝ)) * m ≤ (n : ℝ) * ℓ w :=
          mul_le_mul_of_nonneg_left (hmle w)
            (Nat.cast_nonneg n)
        have hnegr : -((n : ℝ) * ℓ w)
            ≤ -((n : ℝ) * m) := by
          have h1 : -((n : ℝ) * ℓ w) ≤ -((n : ℝ) * m) :=
            neg_le_neg hnle
          exact h1
        exact (div_le_div_iff_of_pos_right (show (0:ℝ) < T by
          exact hT)).mpr hnegr
      exact (mul_le_mul h1 h2 (Real.exp_nonneg _) zero_le_one).trans_eq
        (one_mul _)
    calc (∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T))
        ≤ ∑ w : V, Real.exp (-((n : ℝ) * m)/T) :=
          Finset.sum_le_sum (fun w _ => hterm w)
      _ = (Fintype.card V : ℝ)
          * Real.exp (-((n : ℝ) * m)/T) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- позитивность Z
  have hZpos : (0:ℝ) < Z := by
    have hrpos' : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
      mul_pos hrpos (Real.exp_pos _)
    linarith [hZge, hrpos']
  -- логарифмический сэндвич
  have hZpos : (0:ℝ) < Z := by
    have hrpos' : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
      mul_pos hrpos (Real.exp_pos _)
    linarith [hZge, hrpos']
  have hcardpos : (0:ℝ) < Fintype.card V :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hcpos : (0:ℝ) < (Fintype.card V : ℝ)
      * Real.exp (-((n : ℝ) * m)/T) :=
    mul_pos hcardpos (Real.exp_pos _)
  -- card·e^{−nm/T} = e^{log card − nm/T}
  have hEqC : (Fintype.card V : ℝ)
      * Real.exp (-((n : ℝ) * m)/T)
      = Real.exp (Real.log (Fintype.card V : ℝ)
        - ((n : ℝ) * m)/T) := by
    rw [Real.exp_sub, Real.exp_log hcardpos,
      div_eq_mul_inv (Fintype.card V : ℝ)
        (Real.exp (((n : ℝ) * m)/T)), ← Real.exp_neg]
    congr 1
    ring
  -- log Z ≤ log card − nm/T
  have hlogZle : Real.log Z
      ≤ Real.log (Fintype.card V : ℝ)
        - ((n : ℝ) * m)/T := by
    have h1 := Real.log_le_log hZpos hZle
    rw [hEqC, Real.log_exp] at h1
    exact h1
  -- log r − nm/T ≤ log Z
  -- r·e^{−nm/T} = e^{log r − nm/T}
  have hEqR : r * Real.exp (-((n : ℝ) * m)/T)
      = Real.exp (Real.log r - ((n : ℝ) * m)/T) := by
    rw [Real.exp_sub, Real.exp_log hrpos,
      div_eq_mul_inv r (Real.exp (((n : ℝ) * m)/T)),
      ← Real.exp_neg]
    congr 1
    ring
  -- log r − nm/T ≤ log Z
  have hlogZge : Real.log r - ((n : ℝ) * m)/T ≤ Real.log Z := by
    have hrpos' : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
      mul_pos hrpos (Real.exp_pos _)
    have h1 := Real.log_le_log hrpos' hZge
    rw [hEqR, Real.log_exp] at h1
    exact h1
  -- финальные умножения на −T < 0
  have hTnn : (0:ℝ) ≤ T := le_of_lt hT
  constructor
  · -- nm − T·log card ≤ −T·log Z
    rw [hwealth]
    have hmul := mul_le_mul_of_nonneg_left hlogZle hTnn
    have hsplit : T * (Real.log (Fintype.card V : ℝ)
        - ((n : ℝ) * m)/T)
        = T * Real.log (Fintype.card V : ℝ) - (n : ℝ) * m := by
      rw [mul_sub, mul_div_assoc',
        mul_div_cancel_left₀ _ (ne_of_gt hT)]
    rw [hsplit] at hmul
    have hneg : -T * Real.log Z = -(T * Real.log Z) := by ring
    rw [hneg]
    linarith
  · -- −T·log Z ≤ nm − T·log r
    rw [hwealth]
    have hlogZge' : Real.log r + (-(((n : ℝ) * m)/T))
        ≤ Real.log Z := by
      have := hlogZge
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlogZge' hTnn
    have hkey : T * Real.log r - (n : ℝ) * m ≤ T * Real.log Z := by
      have hTdiv : T * (((n : ℝ) * m)/T) = (n : ℝ) * m :=
        mul_div_cancel₀ _ (ne_of_gt hT)
      have hexp : T * (Real.log r + -(((n : ℝ) * m)/T))
          = T * Real.log r - T * (((n : ℝ) * m)/T) := by ring
      rw [hexp, hTdiv] at hmul
      exact hmul
    have hneg : -T * Real.log Z = -(T * Real.log Z) := by ring
    rw [hneg]
    linarith

/-- СРЕДНИЙ ЛОГ-КАПИТАЛ СХОДИТСЯ К МИНИМУМУ: из
Нернст-сэндвича капитала: −T·log(∏Z_k)/n → ℓmin при
n → ∞ — средняя свободная энергия на шаг итерированного
hedge стремится к минимальным потерям (скорость —
T·log|V|/n сверху и T·log(min ρ₀)/n снизу). -/
theorem hedge_wealth_rate {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      abs ((-T * Real.log (∏ k ∈ Finset.range n,
            stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T))
        / (n : ℝ)
        - (Finset.min' (Finset.univ.image ℓ)
            (Finset.image_nonempty.2 Finset.univ_nonempty))) ≤ ε := by
  set m := Finset.min' (Finset.univ.image ℓ)
    (Finset.image_nonempty.2 Finset.univ_nonempty) with hm
  set r := Finset.min' (Finset.univ.image ρ₀)
    (Finset.image_nonempty.2 Finset.univ_nonempty) with hr
  have hsand : ∀ n : ℕ,
      ((n : ℝ) * m - T * Real.log (Fintype.card V : ℝ)
        ≤ -T * Real.log (∏ k ∈ Finset.range n,
            stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T))
      ∧ (-T * Real.log (∏ k ∈ Finset.range n,
            stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T)
        ≤ (n : ℝ) * m - T * Real.log r) :=
    fun n => hedge_wealth_nernst ρ₀ ℓ T hT hρ₀ hρ₀1 n
  -- границы смещения на шаг n
  set E := fun n : ℕ => (-T * Real.log (∏ k ∈ Finset.range n,
      stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T))
    / (n : ℝ) with hE
  -- |E n − m| ≤ max(T·log card, −T·log r)/n ≤ ε при больших n
  have hcardpos : (0:ℝ) < Fintype.card V :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hrpos : (0:ℝ) < r := by
    have hneρ : (Finset.univ.image ρ₀).Nonempty :=
      Finset.image_nonempty.2 Finset.univ_nonempty
    obtain ⟨wt, hwt⟩ :=
      Finset.mem_image.mp (Finset.min'_mem _ hneρ)
    have hrw : r = ρ₀ wt := hwt.2.symm
    rw [hrw]; exact hρ₀ wt
  have hrle1 : r ≤ 1 := by
    have hneρ : (Finset.univ.image ρ₀).Nonempty :=
      Finset.image_nonempty.2 Finset.univ_nonempty
    obtain ⟨wt, hwt⟩ :=
      Finset.mem_image.mp (Finset.min'_mem _ hneρ)
    have hrw : r = ρ₀ wt := hwt.2.symm
    rw [hrw]
    have h1 := Finset.single_le_sum
      (fun u (_ : u ∈ Finset.univ) => le_of_lt (hρ₀ u))
      (Finset.mem_univ wt)
    rw [hρ₀1] at h1
    exact h1
  have hlogr : Real.log r ≤ 0 :=
    (Real.log_le_log hrpos hrle1).trans_eq Real.log_one
  -- обе границы отклонения: T·log card / n и T·(−log r)/n
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ,
      T * Real.log (Fintype.card V : ℝ) / ε ≤ N1 :=
    exists_nat_ge (T * Real.log (Fintype.card V : ℝ) / ε)
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ,
      T * (-(Real.log r)) / ε ≤ N2 :=
    exists_nat_ge (T * (-(Real.log r)) / ε)
  refine ⟨N1 + N2 + 1, fun n hn => ?_⟩
  have hnpos : (0:ℕ) < n := by omega
  have hnR : (0:ℝ) < (n : ℝ) := by
    have := hnpos; exact_mod_cast this
  obtain ⟨hlo_n, hhi_n⟩ := hsand n
  set W := -T * Real.log (∏ k ∈ Finset.range n,
      stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T) with hWdef
  rw [hWdef] at hlo_n hhi_n
  -- пороги: A := T·log|V| ≥ 0, B := −T·log r ≥ 0
  have hcard1 : (1:ℝ) ≤ (Fintype.card V : ℝ) := by
    have := Fintype.card_pos (α := V)
    exact_mod_cast this
  have hA : (0:ℝ) ≤ T * Real.log (Fintype.card V : ℝ) :=
    mul_nonneg (le_of_lt hT) (Real.log_nonneg hcard1)
  have hB : (0:ℝ) ≤ T * (-(Real.log r)) :=
    mul_nonneg (le_of_lt hT) (neg_nonneg.mpr hlogr)
  -- W/n − m = (W − n·m)/n
  rw [div_sub' hnR.ne', abs_le]
  constructor
  · -- −ε ≤ (W − nm)/n ⟸ nm − A ≤ W и A ≤ n·ε
    rw [le_div_iff₀ hnR]
    -- цель: −ε·n ≤ W − n·m
    have hN1le : (N1 : ℝ) ≤ (n : ℝ) := by
      have : (N1 : ℕ) ≤ n := by omega
      exact_mod_cast this
    have hN1e : T * Real.log (Fintype.card V : ℝ) ≤ (N1 : ℝ) * ε :=
      (div_le_iff₀ hε).mp hN1
    nlinarith [hN1e, hN1le, hε, hlo_n]
  · -- (W − nm)/n ≤ ε ⟸ W ≤ nm + B и B ≤ n·ε
    rw [div_le_iff₀ hnR]
    have hN2le : (N2 : ℝ) ≤ (n : ℝ) := by
      have : (N2 : ℕ) ≤ n := by omega
      exact_mod_cast this
    have hN2e : T * (-(Real.log r)) ≤ (N2 : ℝ) * ε :=
      (div_le_iff₀ hε).mp hN2
    nlinarith [hN2e, hN2le, hε, hhi_n]


/-! ### Источник №70 (arXiv 2609.15897): вариационный шаг как спуск
JKO-подобная схема: каждое экспоненциальное обновление —
минимизация свободной энергии F(q) = ⟨q,ℓ⟩ + T·KL(q‖ρ₀).
Отсюда НЕВОЗРАСТАНИЕ F вдоль итераций при том же ландшафте ℓ
(частный случай: конкурент q = ρ₀ с KL = 0). -/

/-- ВАРИАЦИОННЫЙ СПУСК ЗЕРКАЛЬНОГО ШАГА: γ = mirrorStep ρ₀ ℓ T
даёт F(γ) := ⟨γ,ℓ⟩ + T·KL(γ‖ρ₀) ≤ ⟨ρ₀,ℓ⟩ = F(ρ₀) — каждое
экспоненциальное обновление НЕ УВЕЛИЧИВАЕТ свободную энергию
(конкурент ρ₀ имеет нулевой KL-штраф; частный случай
вариационного принципа источника №70, arXiv 2609.15897). -/
theorem mirror_step_variational_descent {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ1 : ∑ v, ρ₀ v = 1) :
    (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
      + T * (∑ v, mirrorStep ρ₀ ℓ T v
          * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v))
      ≤ ∑ v, ρ₀ v * ℓ v := by
  -- достижимость: F(γ) = −T·log Z ...
  have hatt := mirror_descent_attainment ρ₀ ℓ T hT hρ₀
  -- ... и пол с конкурентом ρ₀ (KL(ρ₀‖ρ₀) = 0):
  --   −T·log Z ≤ ⟨ρ₀,ℓ⟩ + T·KL(ρ₀‖ρ₀) = ⟨ρ₀,ℓ⟩
  have hself : (∑ v, ρ₀ v * Real.log (ρ₀ v / ρ₀ v)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro v _
    rw [div_self (hρ₀ v).ne', Real.log_one, mul_zero]
  have hfloor := mirror_descent_floor ρ₀ ℓ T hT hρ₀ ρ₀ hρ₀ hρ1
  rw [hself, mul_zero] at hfloor
  linarith

/-- ИТЕРАЦИОННАЯ МОНОТОННОСТЬ (№70): при фиксированном
ландшафте ℓ частная свободная энергия шага не возрастает
вдоль траектории mirrorIterate: F_{k+1} ≤ F_k, где
F_k = ⟨ρ_k,ℓ⟩ (KL-штраф относительно ρ_k обнуляется на
следующем шаге). Кумулятивный аналог убывания свободной
энергии в JKO-схеме. -/
theorem mirrorIterate_partial_mono {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ1 : ∑ v, ρ₀ v = 1)
    (ℓs : ℕ → V → ℝ) (k : ℕ) (hls : ℓs k = ℓ) :
    ∑ v, (mirrorIterate ρ₀ ℓs T (k+1)) v * ℓ v
      ≤ ∑ v, (mirrorIterate ρ₀ ℓs T k) v * ℓ v := by
  have hpos : ∀ v, 0 < mirrorIterate ρ₀ ℓs T k v :=
    mirrorIterate_pos ρ₀ ℓs T hT hρ₀ k
  have hsum : ∑ v, mirrorIterate ρ₀ ℓs T k v = 1 :=
    mirrorIterate_sum_one ρ₀ ℓs T hT hρ₀ hρ1 k
  have hstep : mirrorIterate ρ₀ ℓs T (k+1)
      = mirrorStep (mirrorIterate ρ₀ ℓs T k) (ℓs k) T := rfl
  rw [hls] at hstep
  rw [hstep]
  -- KL-штраф ≥ 0, поэтому вариационный спуск даёт ⟨γ,ℓ⟩ ≤ F(γ) ≤ ⟨ρ_k,ℓ⟩
  have hd := mirror_step_variational_descent
    (mirrorIterate ρ₀ ℓs T k) ℓ T hT hpos hsum
  have hKL0 : (0:ℝ) ≤ T * (∑ v, mirrorStep
      (mirrorIterate ρ₀ ℓs T k) ℓ T v
      * Real.log (mirrorStep (mirrorIterate ρ₀ ℓs T k) ℓ T v
        / mirrorIterate ρ₀ ℓs T k v)) := by
    have hγpos : ∀ v, 0 < mirrorStep
        (mirrorIterate ρ₀ ℓs T k) ℓ T v :=
      mirrorStep_pos _ ℓ T hT hpos
    have hγ1 : ∑ v, mirrorStep (mirrorIterate ρ₀ ℓs T k) ℓ T v
        = 1 := mirrorStep_sum_one _ ℓ T hT hpos
    have := finite_kl_nonneg (mirrorStep (mirrorIterate ρ₀ ℓs T k) ℓ T)
      (mirrorIterate ρ₀ ℓs T k) hγpos hγ1 hpos hsum
    exact mul_nonneg hT.le this
  linarith


end Hagi.Optimization
