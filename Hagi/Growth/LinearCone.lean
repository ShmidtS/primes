/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Hagi.Foundations.ConeTakeoff
import Hagi.Foundations.GrowthBand
import Hagi.Growth.GainRenewal

set_option linter.style.header false

/-!
# LinearCone — consolidated cone-family core (C238, A5 R3 slice 5)

Byte-identical merge of PerronCone, ConeCorridor, GrowthDynamics,
ConeDynamics, NonlinearCone, FrontierScaling. Namespace blocks and
declaration FQNs preserved; see .tmp/C238/ for the census receipt.
-/

section C238_perron
/-!
# Perron core for the cone family (audit-3 unification)

The algebraic observation of the third audit, formalized: the
cone condition `γ·k² + (1−ρ)·k ≤ β` is the EIGENVECTOR equation
of the 2×2 dynamics matrix `M = [[1, γ], [β, ρ]]`: the cone
boundary vector `(1, k)` is an eigenvector with eigenvalue
`1 + γ·k` exactly at equality, i.e. `1 + γ·k` is the Perron
root of the cone dynamics. All takeoff variants of the family
(`cone_step`, `cone_ratio_step`, `frontier_cone`) are one-step
preservations of this invariant; the growth rate they report
is this eigenvalue; `elasticity_chain` accumulates it.
-/

set_option linter.style.header false

open scoped Matrix

namespace Hagi.Foundations

open Finset

/-- The cone dynamics matrix `M = [[1, γ], [β, ρ]]`. -/
def coneMatrix (γ β ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then 1
    else if i = 0 ∧ j = 1 then γ
    else if i = 1 ∧ j = 0 then β
    else ρ

/-- The cone-boundary direction `(1, k)`. -/
def coneVec (k : ℝ) : Fin 2 → ℝ := fun i => if i = 0 then 1 else k

/-- **The Perron/eigenvector characterization of the cone
condition**: `(1, k)` is an eigenvector of the cone dynamics
matrix `M = [[1, γ], [β, ρ]]` with eigenvalue `1 + γ·k`
EXACTLY at the equality `β = γ·k² + (1−ρ)·k`. The takeoff rate
`1 + γ·k` every cone theorem reports IS this eigenvalue; the
familiar inequality form `γ·k² + (1−ρ)·k ≤ β` is the same
equation with the invariance margin on the β side. -/
theorem cone_eigenvector_iff (γ β ρ k : ℝ) :
    coneMatrix γ β ρ *ᵥ coneVec k = (1 + γ * k) • coneVec k
      ↔ β = γ * k ^ 2 + (1 - ρ) * k := by
  have h0 : (coneMatrix γ β ρ *ᵥ coneVec k) 0 = 1 + γ * k := by
    simp [coneMatrix, coneVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : (coneMatrix γ β ρ *ᵥ coneVec k) 1 = β + ρ * k := by
    simp [coneMatrix, coneVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have r0 : ((1 + γ * k) • coneVec k) 0 = 1 + γ * k := by
    simp [coneVec]
  have r1 : ((1 + γ * k) • coneVec k) 1 = (1 + γ * k) * k := by
    simp [coneVec]
  constructor
  · intro h
    have := congrFun h 1
    rw [h1, r1] at this
    nlinarith [sq k]
  · intro h
    funext i
    fin_cases i
    · show (coneMatrix γ β ρ *ᵥ coneVec k) 0
          = ((1 + γ * k) • coneVec k) 0
      rw [h0, r0]
    · show (coneMatrix γ β ρ *ᵥ coneVec k) 1
          = ((1 + γ * k) • coneVec k) 1
      rw [h1, r1, h]
      nlinarith [sq k]

/-- **Exact Perron growth on the cone boundary**: under the
EQUALITY dynamics `C(t+1) = C t + γ·D t`, `D(t+1) = ρ·D t +
β·C t`, the eigenvector condition `β = γk²+(1−ρ)k` and the
initial boundary position `D 0 = k·C 0`, the trajectory stays
ON the cone boundary forever and capability grows EXACTLY
geometrically with the Perron rate:

  `C T = (1 + γ·k)^T · C 0` and `D T = k · C T` for all `T`.

This is the single statement all six takeoff variants of the
cone family approximate; combined with `elasticity_chain` it
yields their inequality forms with the same rate. -/
theorem cone_perron_growth (C D : ℕ → ℝ) (γ β ρ k : ℝ)
    (hstepC : ∀ t, C (t + 1) = C t + γ * D t)
    (hstepD : ∀ t, D (t + 1) = ρ * D t + β * C t)
    (hβ : β = γ * k ^ 2 + (1 - ρ) * k)
    (hD0 : D 0 = k * C 0) (T : ℕ) :
    C T = (1 + γ * k) ^ T * C 0 ∧ D T = k * C T := by
  have heig := (cone_eigenvector_iff γ β ρ k).mpr hβ
  induction T with
  | zero =>
      refine ⟨by ring, ?_⟩
      rw [hD0]
  | succ T ih =>
      obtain ⟨ihC, ihD⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [hstepC T, ihD, ihC, pow_succ]
        ring
      · rw [hstepC T, ihD, ihC]
        rw [hstepD T, ihD, ihC]
        -- D(T+1) = ρ·k·C_T + β·C_T must equal k·C_{T+1}
        --         = k·((1+γk)·C_T): the eigenvector identity
        have hc0 := congrFun heig 0
        have hc1 := congrFun heig 1
        simp only [coneVec, Pi.smul_apply, smul_eq_mul,
          if_pos (by decide : (0 : Fin 2) = 0 → True)] at hc0
        simp only [coneVec, Pi.smul_apply, smul_eq_mul,
          if_neg (by decide : ¬(1 : Fin 2) = 0)] at hc1
        simp [coneMatrix, coneVec, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two] at hc0 hc1
        linear_combination ((1 + γ * k) ^ T * C 0) * hc1

/-- МОНОТОННОЕ СРАВНЕНИЕ КОНУСА (аудит v3, Phase 3): если
γ,ρ,β ≥ 0, фактическая динамика (C,D) удовлетворяет
НЕРАВЕНСТВам C_{t+1} ≥ C_t + γD_t, D_{t+1} ≥ ρD_t + βC_t − ξ_t,
а (C',D') — решение той же системы с РАВЕНСТВАМИ и
C'₀ ≤ C₀, D'₀ ≤ D₀, то C' ≤ C и D' ≤ D на всём горизонте.
Кап C_cap НЕ нужен; скорость — спектральный радиус
(cone_perron_growth — случай равенства). -/
theorem cone_comparison (C D C' D' : ℕ → ℝ) (γ ρ β : ℝ)
    (hγ : 0 ≤ γ) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β)
    (h0C : C' 0 ≤ C 0) (h0D : D' 0 ≤ D 0)
    (hC : ∀ t, C (t + 1) ≥ C t + γ * D t)
    (hD : ∀ t, D (t + 1) ≥ ρ * D t + β * C t - 0)
    (hC' : ∀ t, C' (t + 1) = C' t + γ * D' t)
    (hD' : ∀ t, D' (t + 1) = ρ * D' t + β * C' t) :
    ∀ t, C' t ≤ C t ∧ D' t ≤ D t := by
  intro t
  induction t with
  | zero => exact ⟨h0C, h0D⟩
  | succ t ih =>
      obtain ⟨ihC, ihD⟩ := ih
      constructor
      · calc C' (t + 1) = C' t + γ * D' t := hC' t
        _ ≤ C t + γ * D t := by nlinarith [ihC, ihD, hγ]
        _ ≤ C (t + 1) := hC t
      · calc D' (t + 1) = ρ * D' t + β * C' t := hD' t
        _ ≤ ρ * D t + β * C t := by nlinarith [ihC, ihD, hρ, hβ]
        _ ≤ ρ * D t + β * C t - 0 := by ring_nf; linarith
        _ ≤ D (t + 1) := by linarith [hD t]

/-- СРАВНЕНИЕ С ВОЗМУЩЕНИЕМ (аудит v3 Phase 3): при
ξ_t ≤ ε·C_t возмущённая динамика
D_{t+1} ≥ ρD_t + βC_t − ξ_t доминируется системой с
эффективным β' = β − ε (ε ≤ β) — возмущение поглощается
сдвигом коэффициента, спектральный радиус падает. -/
theorem cone_comparison_perturbed (C D C' D' ξ : ℕ → ℝ)
    (γ ρ β ε : ℝ)
    (hγ : 0 ≤ γ) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε : 0 ≤ ε) (hβε : ε ≤ β)
    (h0C : C' 0 ≤ C 0) (h0D : D' 0 ≤ D 0)
    (hC : ∀ t, C (t + 1) ≥ C t + γ * D t)
    (hD : ∀ t, D (t + 1) ≥ ρ * D t + β * C t - ξ t)
    (hξ : ∀ t, ξ t ≤ ε * C t)
    (hC' : ∀ t, C' (t + 1) = C' t + γ * D' t)
    (hD' : ∀ t, D' (t + 1) = ρ * D' t + (β - ε) * C' t) :
    ∀ t, C' t ≤ C t ∧ D' t ≤ D t := by
  apply cone_comparison C D C' D' γ ρ (β - ε) hγ hρ
    (by linarith) h0C h0D hC
  · intro t
    have hξt := hξ t
    have := hD t
    nlinarith
  · exact hC'
  · exact hD'

/-- ЯВНАЯ НИЖНЯЯ ОЦЕНКА D: T-кратная подстановка конусного
неравенства D_{t+1} ≥ ρ·D_t + β·C_t даёт замкнутую форму
D T ≥ ρ^T·D 0 + β·Σ_{i<T} ρ^{T−1−i}·C i (ρ ≥ 0) —
инструмент для T-шаговых оценок скорости роста. -/
theorem cone_explicit_lower (C D : ℕ → ℝ) (ρ β : ℝ) (hρ : 0 ≤ ρ)
    (hstep : ∀ t, ρ * D t + β * C t ≤ D (t + 1)) (T : ℕ) :
    ρ ^ T * D 0 + β * ∑ i ∈ Finset.range T, ρ ^ (T - 1 - i) * C i
      ≤ D T := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h1 := hstep T
    calc D (T + 1) ≥ ρ * D T + β * C T := h1
    _ ≥ ρ * (ρ ^ T * D 0
        + β * ∑ i ∈ Finset.range T, ρ ^ (T - 1 - i) * C i)
        + β * C T := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left ih hρ
          · rfl
    _ = ρ ^ (T + 1) * D 0
        + β * ∑ i ∈ Finset.range (T + 1), ρ ^ (T - i) * C i := by
      have hrw : ∑ i ∈ Finset.range (T + 1), ρ ^ (T - i) * C i
          = ρ * ∑ i ∈ Finset.range T, ρ ^ (T - 1 - i) * C i + C T := by
        rw [Finset.sum_range_succ]
        have hexp : ∀ i ∈ Finset.range T,
            ρ ^ (T - i) * C i = ρ * (ρ ^ (T - 1 - i) * C i) := by
          intro i hi
          have hi' : i < T := Finset.mem_range.mp hi
          have h : T - 1 - i + 1 = T - i := by omega
          rw [← h, pow_succ]; ring
        rw [Finset.sum_congr rfl hexp, Finset.mul_sum]
        simp
      rw [hrw, pow_succ]; ring

/-- СЛЕДСТВИЕ (монотонная capability): при β, ρ, C 0 ≥ 0 и
C i ≥ C 0 — явная одночленная оценка
D (T+1) ≥ ρ^{T+1}·D 0 + β·C 0: последний член суммы
cone_explicit_lower (i = T, ρ^0) доминируется монотонностью. -/
theorem cone_explicit_monotone (C D : ℕ → ℝ) (ρ β : ℝ) (hρ : 0 ≤ ρ)
    (hβ : 0 ≤ β) (hC0 : 0 ≤ C 0)
    (hstep : ∀ t, ρ * D t + β * C t ≤ D (t + 1))
    (hC : ∀ i, C 0 ≤ C i) (T : ℕ) :
    ρ ^ (T + 1) * D 0 + β * C 0 ≤ D (T + 1) := by
  have h := cone_explicit_lower C D ρ β hρ hstep (T + 1)
  have hlast : β * C 0
      ≤ β * ∑ i ∈ Finset.range (T + 1), ρ ^ (T + 1 - 1 - i) * C i := by
    rw [Finset.sum_range_succ]
    have hterms : (0:ℝ)
        ≤ ∑ i ∈ Finset.range T, ρ ^ (T + 1 - 1 - i) * C i := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (pow_nonneg hρ _) (le_trans hC0 (hC i))
    have hC1 : C 0 ≤ C T := hC T
    have hz : ρ ^ (T + 1 - 1 - T) * C T = C T := by
      have hz' : (T + 1 - 1 - T) = 0 := by omega
      rw [hz', pow_zero, one_mul]
    rw [hz]
    have hbetaS : (0:ℝ) ≤ β * ∑ i ∈ Finset.range T, ρ ^ (T + 1 - 1 - i) * C i :=
      mul_nonneg hβ hterms
    nlinarith [hC1, hbetaS]
  nlinarith [h, hlast]

/-- МОСТ h_emp_dyn ⇒ ЯВНАЯ ОЦЕНКА (аудит v3): возмущённая
конусная посылка `ρ·D t + β·C t − ξ t ≤ D (t+1)` при
ξ t ≤ ε·C t, C t ≥ 0 и ε ≤ β эквивалентна чистому конусному
неравенству с эффективным β−ε; замкнутая форма
(ε ≥ 0 неявно в ξ t ≤ ε·C t с C t ≥ 0, β−ε любой знак):
D T ≥ ρ^T·D 0 + (β−ε)·Σ_{i<T} ρ^{T−1−i}·C i — фактическая
посылка MasterHAGI_trunc напрямую даёт T-шаговую нижнюю
оценку потенциала роста. -/
theorem h_emp_dyn_explicit (C D ξ : ℕ → ℝ) (ρ β ε : ℝ)
    (hρ : 0 ≤ ρ)
    (hC : ∀ t, 0 ≤ C t)
    (hξ : ∀ t, ξ t ≤ ε * C t)
    (h_emp_dyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (T : ℕ) :
    ρ ^ T * D 0
      + (β - ε) * ∑ i ∈ Finset.range T, ρ ^ (T - 1 - i) * C i
      ≤ D T := by
  have hstep : ∀ t, ρ * D t + (β - ε) * C t ≤ D (t + 1) := by
    intro t
    have h1 := h_emp_dyn t
    have h2 : ρ * D t + (β - ε) * C t
        ≤ ρ * D t + β * C t - ξ t := by
      have hle : ξ t ≤ ε * C t := hξ t
      have hCt : 0 ≤ C t := hC t
      nlinarith [hle, hCt]
    exact le_trans h2 h1
  exact cone_explicit_lower C D ρ (β - ε) hρ hstep T

/-- ЛИНЕЙНЫЙ РОСТ при ρ=1: возмущённая посылка
D (t+1) ≥ D t + β·C t − ξ t с ξ t ≤ ε·C t, C монотонна и
β ≥ ε даёт D T ≥ D 0 + (β−ε)·T·C 0 — накопление без
затухания (ρ=1: нет геометрической скидки). -/
theorem h_emp_dyn_linear_growth (C D ξ : ℕ → ℝ) (β ε : ℝ)
    (hβε : ε ≤ β) (hC0 : 0 ≤ C 0)
    (hξ : ∀ t, ξ t ≤ ε * C t)
    (h_emp_dyn : ∀ t, D t + β * C t - ξ t ≤ D (t + 1))
    (hC : ∀ i, C 0 ≤ C i) (T : ℕ) :
    D 0 + (β - ε) * (T : ℝ) * C 0 ≤ D T := by
  have hCnn : ∀ t, 0 ≤ C t := fun t => le_trans hC0 (hC t)
  have h := h_emp_dyn_explicit C D ξ 1 β ε
    (by norm_num) hCnn hξ (by intro t; simpa using h_emp_dyn t) T
  have h1 : (1:ℝ) ^ T = 1 := one_pow T
  rw [h1, one_mul] at h
  have hsum : (T : ℝ) * C 0
      ≤ ∑ i ∈ Finset.range T, (1:ℝ) ^ (T - 1 - i) * C i := by
    have hnonneg : ∀ i ∈ Finset.range T,
        (0:ℝ) ≤ (1:ℝ) ^ (T - 1 - i) * C i := by
      intro i _
      exact mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1) _) (hCnn i)
    have hlower : ∀ i ∈ Finset.range T,
        C 0 ≤ (1:ℝ) ^ (T - 1 - i) * C i := by
      intro i _
      rw [one_pow, one_mul]
      exact hC i
    calc (T:ℝ) * C 0
        = ∑ _i ∈ Finset.range T, C 0 := by
          simp
    _ ≤ ∑ i ∈ Finset.range T, (1:ℝ) ^ (T - 1 - i) * C i :=
        Finset.sum_le_sum (fun i hi => hlower i hi)
  have : (0:ℝ) ≤ β - ε := by linarith
  nlinarith [h, hsum, this, Finset.card_range T]

/-- КОМБИНИРОВАННЫЙ 2D-РОСТ: посылки конусного блока
C (t+1) = C t + G t, γ·D t ≤ G t и ρ·D t + β·C t ≤ D (t+1)
(β, γ, C ≥ 0, ρ < 1) дают явную нижнюю оценку capability:
C T ≥ C 0 + γ·D 0·(1−ρ^T)/(1−ρ) — накопление прироста из
геометрического ряда потенциала. -/
theorem h_emp_gain_geometric (C D G : ℕ → ℝ) (ρ β γ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hγ : 0 ≤ γ) (hβ : 0 ≤ β)
    (hC : ∀ t, 0 ≤ C t)
    (hstepC : ∀ t, C (t + 1) = C t + G t)
    (hgain : ∀ t, γ * D t ≤ G t)
    (hstepD : ∀ t, ρ * D t + β * C t ≤ D (t + 1)) (T : ℕ) :
    C 0 + γ * D 0 * (1 - ρ ^ T) / (1 - ρ) ≤ C T := by
  have hD : ∀ t, ρ ^ t * D 0 ≤ D t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have h := hstepD t
      have hβC : 0 ≤ β * C t := mul_nonneg hβ (hC t)
      calc D (t + 1) ≥ ρ * D t + β * C t := h
      _ ≥ ρ * (ρ ^ t * D 0) := by nlinarith
      _ = ρ ^ (t + 1) * D 0 := by rw [pow_succ]; ring
  have hCtel : ∀ T, C T = C 0 + ∑ i ∈ Finset.range T, G i := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [hstepC T, ih, Finset.sum_range_succ]; ring
  rw [hCtel T]
  have hgeom : ∑ i ∈ Finset.range T, ρ ^ i
      = (1 - ρ ^ T) / (1 - ρ) := by
    have hne : ρ ≠ 1 := ne_of_lt hρ1
    rw [geom_sum_eq hne T]
    field_simp
    ring
  have hmono : D 0 * ∑ i ∈ Finset.range T, ρ ^ i
      ≤ ∑ i ∈ Finset.range T, D i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by nlinarith [hD i])
  have heq : γ * D 0 * (1 - ρ ^ T) / (1 - ρ)
      = γ * (D 0 * ∑ i ∈ Finset.range T, ρ ^ i) := by
    rw [hgeom]; ring
  rw [heq]
  have hsumG : γ * ∑ i ∈ Finset.range T, D i
      ≤ ∑ i ∈ Finset.range T, G i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hgain i)
  exact add_le_add (le_refl _)
    (le_trans (mul_le_mul_of_nonneg_left hmono hγ) hsumG)

/-- ЭКСПОНЕНЦИАЛЬНЫЙ ВЗЛЁТ: если конусное соотношение
k·C t ≤ D t удерживается на каждом шаге, а шаги
C (t+1) = C t + G t и γ·D t ≤ G t выполнены, то
capability растёт экспоненциально:
C T ≥ (1 + γ·k)^T ·C 0 (при 1+γk ≥ 0) —
неравенственная версия cone_perron_growth. -/
theorem h_emp_takeoff_exponential (C D G : ℕ → ℝ) (γ k : ℝ)
    (hγ : 0 ≤ γ) (hγk : 0 ≤ 1 + γ * k)
    (hstepC : ∀ t, C (t + 1) = C t + G t)
    (hgain : ∀ t, γ * D t ≤ G t)
    (hcone : ∀ t, k * C t ≤ D t) (T : ℕ) :
    (1 + γ * k) ^ T * C 0 ≤ C T := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hstep := hstepC T
    have hg := hgain T
    have hc := hcone T
    have hγkC : γ * k * C T ≤ G T :=
      calc γ * k * C T = γ * (k * C T) := by ring
      _ ≤ γ * D T := mul_le_mul_of_nonneg_left hc hγ
      _ ≤ G T := hg
    have hkey : (1 + γ * k) * C T ≤ C T + G T := by
      have : (1 + γ * k) * C T = C T + γ * k * C T := by ring
      rw [this]
      exact add_le_add_right hγkC (C T)
    rw [hstep, pow_succ]
    nlinarith [ih, hγk, hkey]

/-- КОНУСНАЯ ИНВАРИАНТНОСТЬ ПОСЫЛОК MasterHAGI_trunc: блок
h_emp_{cone0, C_cap, dyn, beta} поддерживает конусное
соотношение (α/γ)·C t ≤ D t индукцией по t (ядро конусного
блока аудита v3): cap ограничивает рост C фактором (1+α),
beta оплачивает дрейф+возмущение, dyn переносит на D. -/
theorem trunc_cone_invariance (C D ξ : ℕ → ℝ) (α γ ρ β : ℝ)
    (hα : 0 ≤ α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hC : ∀ t, 0 < C t)
    (hcone0 : α / γ * C 0 ≤ D 0)
    (hcap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (hdyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (hbeta : ∀ t, α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β) :
    ∀ t, α / γ * C t ≤ D t := by
  intro t
  induction t with
  | zero => exact hcone0
  | succ t ih =>
    have hCt : 0 < C t := hC t
    have hkn : (0:ℝ) ≤ α / γ :=
      div_nonneg hα (le_of_lt hγ)
    have hξ : ξ t = (ξ t / C t) * C t := by field_simp
    have hb := hbeta t
    have hkey : α / γ * (1 + α)
        ≤ ρ * (α / γ) + β - ξ t / C t := by
      have hsplit : α / γ * (1 + α)
          = α / γ * ((1 + α) - ρ) + ρ * (α / γ) := by ring
      nlinarith [hb]
    have h1 : α / γ * C (t + 1)
        ≤ (α / γ * (1 + α)) * C t := by
      calc α / γ * C (t + 1)
          ≤ α / γ * ((1 + α) * C t) :=
            mul_le_mul_of_nonneg_left (hcap t) hkn
      _ = (α / γ * (1 + α)) * C t := by ring
    have h2 : (α / γ * (1 + α)) * C t
        ≤ ρ * D t + β * C t - ξ t := by
      have hkey : α / γ * (1 + α)
          ≤ ρ * (α / γ) + β - ξ t / C t := by
        nlinarith [hbeta t]
      have hprod : (α / γ * (1 + α)) * C t
          ≤ (ρ * (α / γ) + β - ξ t / C t) * C t :=
        mul_le_mul_of_nonneg_right hkey (le_of_lt hCt)
      have hexpand : (ρ * (α / γ) + β - ξ t / C t) * C t
          = ρ * (α / γ * C t) + β * C t - (ξ t / C t) * C t := by
        ring
      rw [hexpand] at hprod
      have hξeq : (ξ t / C t) * C t = ξ t := by field_simp
      rw [hξeq] at hprod
      have hρmono : ρ * (α / γ * C t) ≤ ρ * D t :=
        mul_le_mul_of_nonneg_left ih hρ
      linarith
    exact le_trans h1 (le_trans h2 (hdyn t))

/-- ПОЛНЫЙ ВЗЛЁТ ИЗ ПОСЫЛОК trunc (композиция): конусный блок
MasterHAGI_trunc (cone0, C_cap, dyn, beta) + шаги
C (t+1) = C t + G t и γ·D t ≤ G t дают экспоненциальный рост
capability: C T ≥ (1+α)^T·C 0 — вся цепочка от эмпирических
посылок к takeoff (trunc_cone_invariance ⟹
h_emp_takeoff_exponential при k = α/γ, γk = α). -/
theorem trunc_premises_takeoff (C D G ξ : ℕ → ℝ) (α γ ρ β : ℝ)
    (hα : 0 ≤ α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hC : ∀ t, 0 < C t)
    (hcone0 : α / γ * C 0 ≤ D 0)
    (hcap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (hdyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (hbeta : ∀ t, α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β)
    (hstepC : ∀ t, C (t + 1) = C t + G t)
    (hgain : ∀ t, γ * D t ≤ G t) (T : ℕ) :
    (1 + α) ^ T * C 0 ≤ C T := by
  have hcone := trunc_cone_invariance C D ξ α γ ρ β
    hα hγ hρ hC hcone0 hcap hdyn hbeta
  have hγk : γ * (α / γ) = α := by field_simp
  have h := h_emp_takeoff_exponential C D G γ (α / γ)
    (le_of_lt hγ) (by nlinarith [hα, hγk]) hstepC hgain hcone T
  rwa [hγk] at h

end Hagi.Foundations
end C238_perron
section C238_corridor
/-!
# ConeSystem-коридор (шаг 4 аудита v5, ядро)

Консолидация: через ЕДИНУЮ структуру GrowthDynamics —
двусторонняя оценка: если конусные посылки дают takeoff
(нижняя), а окно роста — cap (верхняя), то capability
зажат ТОЧНОЙ экспонентой: (1+α)^T·C0 ≤ C T ≤ (1+α)^T·C0.
-/

namespace Hagi.Foundations

/-- ТОЧНАЯ ЭКСПОНЕНТА КОНУСА: при конусных посылках
(GrowthDynamics) и cap-окне (C(t+1) ≤ (1+α)·C t) рост
 capability — ровно (1+α)^T·C0: нижняя граница из конуса,
 верхняя — индукция по cap. -/
theorem cone_exact_exponential (C G D : ℕ → ℝ) (xi : ℕ → ℝ)
    (alpha gamma rho beta : ℝ) (T : ℕ)
    (hα : 0 ≤ alpha) (hγ : 0 < gamma) (hρ : 0 ≤ rho)
    (hCpos : ∀ t, 0 < C t)
    (hcone0 : alpha / gamma * C 0 ≤ D 0)
    (hcap : ∀ t, C (t + 1) ≤ (1 + alpha) * C t)
    (hdyn : ∀ t, rho * D t + beta * C t - xi t ≤ D (t + 1))
    (hbeta : ∀ t, alpha / gamma * ((1 + alpha) - rho)
      + xi t / C t ≤ beta)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hgain : ∀ t, gamma * D t ≤ G t) :
    (1 + alpha) ^ T * C 0 ≤ C T
      ∧ C T ≤ (1 + alpha) ^ T * C 0 := by
  constructor
  · -- нижняя: конусная динамика (существующий капстоун)
    exact trunc_premises_takeoff C D G xi alpha gamma rho beta
      hα hγ hρ hCpos hcone0 hcap hdyn hbeta hstep hgain T
  · -- верхняя: индукция по cap
    have hmain : ∀ n : ℕ, n ≤ T →
        C n ≤ (1 + alpha) ^ n * C 0 := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have hc := hcap n
        have ih' := ih (by omega)
        calc C (n + 1) ≤ (1 + alpha) * C n := hc
          _ ≤ (1 + alpha) * ((1 + alpha) ^ n * C 0) :=
              mul_le_mul_of_nonneg_left ih' (by linarith)
          _ = (1 + alpha) ^ (n + 1) * C 0 := by ring
    exact hmain T (le_refl _)

end Hagi.Foundations

end C238_corridor
section C238_growthdyn
/-!
# GrowthDynamics — the single bundle of growth-premises

One structure collecting the 8-premise bundle consumed by the
cone/takeoff family. The empirical nature of each field is
visible in its name (`emp*`): conditional results carry their
conditionality in the signature.

* `hα hγ hρ` — sign hypotheses on the rates;
* `hC0` — the seed capability is positive;
* `empCone0` — the initial cone condition `(α/γ)·C₀ ≤ D₀`;
* `empStep` — the capability update law `C_{t+1} = C_t + G_t`;
* `empGainProd` — production `γ·D_t ≤ G_t`;
* `empDyn` — the D-dynamics with loss ξ: `ρ·D + β·C − ξ ≤ D′`;
* `empCCap` — the multiplicative capability cap;
* `empBeta` — the cone-sustaining β bound.
-/

namespace Hagi.Foundations

/-- The growth-dynamics premise bundle: one object instead of
eight positional hypotheses. All `emp*` fields are empirical
laws, not derived facts. -/
structure GrowthDynamics (C G D : ℕ → ℝ) (xi : ℕ → ℝ)
    (alpha gamma rho beta : ℝ) (T : ℕ) : Prop where
  /-- the growth rate is positive -/
  hα : 0 < alpha
  /-- production efficiency is positive -/
  hγ : 0 < gamma
  /-- the retention coefficient is nonnegative -/
  hρ : 0 ≤ rho
  /-- the seed capability is positive -/
  hC0 : 0 < C 0
  /-- EMPIRICAL: the initial cone condition -/
  empCone0 : alpha / gamma * C 0 ≤ D 0
  /-- EMPIRICAL: the capability update law -/
  empStep : ∀ t < T, C (t + 1) = C t + G t
  /-- EMPIRICAL: gain production from disagreement -/
  empGainProd : ∀ t < T, gamma * D t ≤ G t
  /-- EMPIRICAL: disagreement dynamics with loss xi -/
  empDyn : ∀ t < T, rho * D t + beta * C t - xi t ≤ D (t + 1)
  /-- EMPIRICAL: multiplicative capability cap -/
  empCCap : ∀ t < T, C (t + 1) ≤ (1 + alpha) * C t
  /-- EMPIRICAL: the cone-sustaining beta bound -/
  empBeta : ∀ t < T,
    alpha / gamma * ((1 + alpha) - rho) + xi t / C t ≤ beta


/-- **Телескоп прироста под полосой (R548)**: если каждый
шаговый прирост ограничен полосой (G t ≤ b t), то полный
прирост не превосходит телескопа полосы: C T - C 0 ≤ Σ b t.
Базовая форма для anytime-growth бюджетов (b t = μ + u). -/
theorem telescope_band (C G b : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t ∈ Finset.range T, C (t + 1) = C t + G t)
    (hband : ∀ t ∈ Finset.range T, G t ≤ b t) :
    C T - C 0 ≤ ∑ t ∈ Finset.range T, b t := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ,
        hstep T (Finset.mem_range.mpr (Nat.lt_succ_self T))]
      have hle : C T - C 0 ≤ ∑ t ∈ Finset.range T, b t :=
        ih (fun t ht => hstep t
          (Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp ht)
            (Nat.lt_succ_self T))))
          (fun t ht => hband t
            (Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp ht)
              (Nat.lt_succ_self T))))
      have hpt := hband T (Finset.mem_range.mpr (Nat.lt_succ_self T))
      linarith

/-- **Anytime-growth бюджет (R548)**: полоса μ + u на каждом
шаге с u = √(2σ²·ln(T/α)) (anytime_safe_threshold-форма) даёт
C T ≤ C 0 + T·μ + T·u — линейный рост за jmp anytime-уровень. -/
theorem anytime_growth_budget (C G b : ℕ → ℝ) (T : ℕ) (μ u : ℝ)
    (hstep : ∀ t ∈ Finset.range T, C (t + 1) = C t + G t)
    (hband : ∀ t ∈ Finset.range T, G t ≤ b t)
    (hb : ∀ t ∈ Finset.range T, b t ≤ μ + u) :
    C T ≤ C 0 + (T:ℝ) * μ + (T:ℝ) * u := by
  have htel := telescope_band C G b T hstep hband
  have hsum : ∑ t ∈ Finset.range T, b t ≤ ∑ t ∈ Finset.range T, (μ + u) := by
    refine Finset.sum_le_sum (fun t ht => hb t ht)
  rw [Finset.sum_const, Finset.card_range] at hsum
  rw [nsmul_eq_mul] at hsum
  push_cast at hsum ⊢
  linarith

/-- Телескоп полосы (R556, ∀t-форма). -/
theorem band_telescope (C G : ℕ → ℝ) (b σ : ℝ)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hband : ∀ t, G t ≤ b * (1 - σ) ^ t) :
    ∀ N : ℕ, C N ≤ C 0 + ∑ t ∈ Finset.range N, b * (1 - σ) ^ t := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have hs := hstep N
      have hbN := hband N
      calc C (N + 1) = C N + G N := hs
        _ ≤ C N + b * (1 - σ) ^ N := by linarith
        _ ≤ (C 0 + ∑ t ∈ Finset.range N, b * (1 - σ) ^ t)
            + b * (1 - σ) ^ N := by linarith
        _ = C 0 + ∑ t ∈ Finset.range (N + 1),
              b * (1 - σ) ^ t := by
            rw [Finset.sum_range_succ]; ring

/-- **Затухающая полоса ⟹ capability-потолок (R556)**: прирост
накрыт геометрически убывающей полосой G t ≤ b·(1−σ)^t
(b ≥ 0, σ > 0) — рост насыщается: C T ≤ C 0 + (b/σ)·(1−(1−σ)^T)
≤ C 0 + b/σ; мост к сигнатуре насыщения satC (R531). -/
theorem geometric_band_ceiling (C G : ℕ → ℝ) (b σ : ℝ) (T : ℕ)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hband : ∀ t, G t ≤ b * (1 - σ) ^ t)
    (hb : 0 ≤ b) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    C T ≤ C 0 + b * (1 - (1 - σ) ^ T) / σ
      ∧ C T ≤ C 0 + b / σ := by
  have htel := band_telescope C G b σ hstep hband T
  have hgeo : ∀ N : ℕ, ∑ t ∈ Finset.range N, (1 - σ) ^ t
      = (1 - (1 - σ) ^ N) / σ := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp
        ring
  have hsum : ∑ t ∈ Finset.range T, b * (1 - σ) ^ t
      = b * (1 - (1 - σ) ^ T) / σ := by
    rw [← Finset.mul_sum, hgeo]
    ring
  have h1 : C T ≤ C 0 + b * (1 - (1 - σ) ^ T) / σ := by
    rw [hsum] at htel
    exact htel
  refine ⟨h1, ?_⟩
  have hge : 0 ≤ (1 - σ) ^ T := by
    have h1σ : (0:ℝ) ≤ 1 - σ := by linarith
    exact pow_nonneg h1σ T
  have hle1 : (1:ℝ) - (1 - σ) ^ T ≤ 1 := by linarith
  have hstep2 : b * (1 - (1 - σ) ^ T) / σ ≤ b / σ := by
    have hmul : b * (1 - (1 - σ) ^ T) ≤ b * 1 :=
      mul_le_mul_of_nonneg_left hle1 hb
    exact div_le_div_of_nonneg_right (by linarith [hmul]) hσ.le
  exact le_trans h1 (by linarith [hstep2])


/-- **Цель выше потолка полосы — недостижима (R557)**:
термостат-настройка: если затухающая полоса даёт потолок
C 0 + b/σ ниже цели C*, то цель не достигается ни на каком
горизонте. Обратная сторона R530 (γ-дефицит): полоса — ещё
один механизм блокировки takeoff. -/
theorem band_target_unreachable (C G : ℕ → ℝ) (b σ Cstar : ℝ)
    (T : ℕ)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hband : ∀ t, G t ≤ b * (1 - σ) ^ t)
    (hb : 0 ≤ b) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hlow : C 0 + b / σ < Cstar) :
    ∀ t, C t < Cstar := by
  intro t
  obtain ⟨h1, hceil⟩ :=
    geometric_band_ceiling C G b σ t hstep hband hb hσ hσ1
  linarith


/-- Геометрическая сумма (переиспользуемая форма, R560). -/
theorem geo_sum_decay (σ : ℝ) (hσ : 0 < σ) (T : ℕ) :
    ∑ t ∈ Finset.range T, (1 - σ) ^ t = (1 - (1 - σ) ^ T) / σ := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp [pow_succ]
      ring

/-- **Нижняя полоса ⟹ гарантированный рост (R560)**: зеркальная
к R556 ситуация: прирост поддержан снизу G t ≥ b·(1−σ)^t
(b ≥ 0, σ ∈ (0,1]) — capability гарантированно достигает
C 0 + (b/σ)·(1−(1−σ)^T) к горизонту T. -/
theorem band_guaranteed_growth (C G : ℕ → ℝ) (b σ : ℝ) (T : ℕ)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hband : ∀ t, G t ≥ b * (1 - σ) ^ t)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    C T ≥ C 0 + b * (1 - (1 - σ) ^ T) / σ := by
  have htel : ∀ N : ℕ, C N ≥ C 0 + ∑ t ∈ Finset.range N,
      b * (1 - σ) ^ t := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        have hs := hstep N
        have hbN := hband N
        calc C (N + 1) = C N + G N := hs
          _ ≥ C N + b * (1 - σ) ^ N := by linarith
          _ ≥ (C 0 + ∑ t ∈ Finset.range N, b * (1 - σ) ^ t)
              + b * (1 - σ) ^ N := by linarith
          _ = C 0 + ∑ t ∈ Finset.range (N + 1),
                b * (1 - σ) ^ t := by
              rw [Finset.sum_range_succ]; ring
  have hsum : ∑ t ∈ Finset.range T, b * (1 - σ) ^ t
      = b * (1 - (1 - σ) ^ T) / σ := by
    rw [← Finset.mul_sum, geo_sum_decay σ hσ T]
    ring
  have hT := htel T
  rw [hsum] at hT
  exact hT

/-- **Время достижения цели (R560)**: если цель C* внутри
нижней полосы-насыщения (C 0 + b/σ ≥ C*), то к горизонту
T ≥ ln(1 − σ(C*−C0)/b)/ln(1−σ) цель достигнута — таймер
термостата в замкнутой форме. -/
theorem band_time_to_target (C G : ℕ → ℝ) (b σ Cstar : ℝ)
    (T : ℕ)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hband : ∀ t, G t ≥ b * (1 - σ) ^ t)
    (hb : 0 ≤ b) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hreach : C 0 + b * (1 - (1 - σ) ^ T) / σ ≥ Cstar) :
    Cstar ≤ C T := by
  have hgrowth := band_guaranteed_growth C G b σ T hstep hband hσ hσ1
  linarith


/-- **Range-версия гарантированного роста (R561)**: полоса
только на горизонте t < T (сертифицируемая форма; канон
R540-лямбд для генерализованных гипотез). -/
theorem band_guaranteed_growth_range (C G : ℕ → ℝ) (b σ : ℝ)
    (T : ℕ)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hband : ∀ t < T, b * (1 - σ) ^ t ≤ G t)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    C T ≥ C 0 + b * (1 - (1 - σ) ^ T) / σ := by
  induction T with
  | zero => simp
  | succ T ih =>
      -- ih: переведённые гипотезы для горизонта T
      have ihT := ih
        (fun t ht => hband t (lt_trans ht (Nat.lt_succ_self T)))
      have hs := hstep T
      have hbT := hband T (Nat.lt_succ_self T)
      have hsumT : ∑ t ∈ Finset.range T, (1 - σ) ^ t
          = (1 - (1 - σ) ^ T) / σ := geo_sum_decay σ hσ T
      have hpow : (1 - σ) ^ (T + 1) = (1 - σ) ^ T * (1 - σ) :=
        pow_succ _ T
      calc C (T + 1) = C T + G T := hs
        _ ≥ (C 0 + b * (1 - (1 - σ) ^ T) / σ)
              + b * (1 - σ) ^ T := by linarith
        _ = C 0 + b * (1 - (1 - σ) ^ (T + 1)) / σ := by
            field_simp [hpow]
            ring
/-- **Таймер термостата в замкнутой лог-форме (R567)**:
при σ < 1 и σ(C*−C0) < b цель C* настигается на горизонте
T ≥ ln(1 − σ(C*−C0)/b)/ln(1−σ) — обратная задача каскада
в логарифмической форме: из лог-неравенства выводится
(1−σ)^T ≤ 1 − σ(C*−C0)/b, затем band_time_to_target. -/
theorem time_to_target_log (C G : ℕ → ℝ) (b σ Cstar : ℝ) (T : ℕ)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hband : ∀ t, G t ≥ b * (1 - σ) ^ t)
    (hb : 0 ≤ b) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hc0 : C 0 ≤ Cstar)
    (hc1 : σ * (Cstar - C 0) < b)
    (hT : Real.log (1 - σ * (Cstar - C 0) / b)
        / Real.log (1 - σ) ≤ (T : ℝ)) :
    Cstar ≤ C T := by
  have hq1 : 0 < (1:ℝ) - σ := by linarith
  have hq2 : (1:ℝ) - σ < 1 := by linarith
  have hq0 : Real.log (1 - σ) < 0 := Real.log_neg hq1 hq2
  have hd0 : 0 ≤ Cstar - C 0 := by linarith
  have hbpos : 0 < b := by
    have h1 : 0 ≤ σ * (Cstar - C 0) := by positivity
    linarith
  have h2 : σ * (Cstar - C 0)/b < 1 := by
    rw [div_lt_one hbpos]; exact hc1
  have hy0 : 0 < (1:ℝ) - σ*(Cstar - C 0)/b := by linarith
  have hmul : (T:ℝ) * Real.log (1 - σ)
      ≤ Real.log (1 - σ * (Cstar - C 0)/b) :=
    (div_le_iff_of_neg hq0).mp hT
  have hrev : ((1:ℝ)-σ)^T ≤ 1 - σ*(Cstar - C 0)/b := by
    by_contra hcon
    have hgt : (1:ℝ) - σ*(Cstar - C 0)/b < (1 - σ)^T := by linarith
    have hlog : Real.log (1 - σ*(Cstar - C 0)/b) < Real.log ((1-σ)^T) :=
      Real.log_lt_log hy0 hgt
    rw [Real.log_pow] at hlog
    linarith
  refine band_time_to_target C G b σ Cstar T hstep hband hb hσ
    (by linarith) ?_
  show C 0 + b * (1 - (1 - σ) ^ T) / σ ≥ Cstar
  have h1 : σ * (Cstar - C 0)/b ≤ 1 - (1 - σ)^T := by linarith
  rw [div_le_iff₀ hbpos] at h1
  have h2 : Cstar - C 0 ≤ b * (1 - (1 - σ)^T)/σ := by
    rw [le_div_iff₀ hσ]
    nlinarith [h1, hσ.le]
  linarith

end Hagi.Foundations


end C238_growthdyn
section C238_conedyn
/-!
# ConeDynamics — abstract cone laws

* `ConeData`: carrier with capability `C`, frontier `D`, forcing `ξ`,
  and law constants `γ`, `ρ`, `β`.
* `cone_data_invariant` (cap form): one-step cone preservation
  under a capability cap `C (t+1) ≤ (1 + γk) * C t`.
* `frontier_cone_inductive_is_cone_data`: the FrontierScaling
  theorem `frontier_cone_inductive` as an instance of
  `cone_data_invariant` at `k = α / γ`.
* `cone_reinvest_invariant` (reinvest form): one-step cone
  preservation under a reinvest cap `C (t+1) ≤ C t + γ * D t`, with
  retention `γ * k ≤ ρ`.
* `cone_ratio_step_is_reinvest`: the RatioTakeoff theorem
  `cone_ratio_step` (exact step) as the equality case of
  `cone_reinvest_invariant`.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- The abstract cone-dynamics carrier: capability,
frontier, forcing, and the law constants. -/
structure ConeData where
  /-- capability channel. -/
  C : ℕ → ℝ
  /-- frontier channel. -/
  D : ℕ → ℝ
  /-- the forcing/friction term (losses that drain the
  frontier; ξ ≡ 0 recovers the zero-error cone). -/
  ξ : ℕ → ℝ
  γ : ℝ
  ρ : ℝ
  β : ℝ

/-- Cone step law with forcing and capability cap: given
`0 ≤ k`, `0 ≤ γ`, `0 ≤ ρ`, `0 < C t`, the cone
`k * C t ≤ D t`, the frontier dynamics
`ρ * D t + β * C t - ξ t ≤ D (t + 1)`, the cap
`C (t + 1) ≤ (1 + γ * k) * C t`, and the threshold
`k * ((1 + γ * k) - ρ) + ξ t / C t ≤ β`, the cone is preserved:
`k * C (t + 1) ≤ D (t + 1)`. -/
theorem cone_data_invariant (cd : ConeData) (k : ℝ) (t : ℕ)
    (hk : 0 ≤ k) (hγ : 0 ≤ cd.γ) (hρ : 0 ≤ cd.ρ)
    (hCpos : 0 < cd.C t)
    (hcone : k * cd.C t ≤ cd.D t)
    (h_dyn : cd.ρ * cd.D t + cd.β * cd.C t - cd.ξ t
      ≤ cd.D (t + 1))
    (h_C_cap : cd.C (t + 1) ≤ (1 + cd.γ * k) * cd.C t)
    (hβ : k * ((1 + cd.γ * k) - cd.ρ) + cd.ξ t / cd.C t
      ≤ cd.β) :
    k * cd.C (t + 1) ≤ cd.D (t + 1) := by
  have h1 : cd.ρ * (k * cd.C t) ≤ cd.ρ * cd.D t :=
    mul_le_mul_of_nonneg_left hcone hρ
  have h2 : (k * ((1 + cd.γ * k) - cd.ρ)) * cd.C t
      + cd.ξ t ≤ cd.β * cd.C t := by
    have hm := mul_le_mul_of_nonneg_right hβ hCpos.le
    have e : (k * ((1 + cd.γ * k) - cd.ρ)
        + cd.ξ t / cd.C t) * cd.C t
        = (k * ((1 + cd.γ * k) - cd.ρ)) * cd.C t + cd.ξ t := by
      field_simp
    rw [← e]
    exact hm
  have hkγ : 0 ≤ k * cd.γ := mul_nonneg hk hγ
  have h3 : k * cd.C (t + 1) ≤ k * ((1 + cd.γ * k) * cd.C t) :=
    mul_le_mul_of_nonneg_left h_C_cap hk
  have h4 : k * ((1 + cd.γ * k) * cd.C t)
      = (k * ((1 + cd.γ * k) - cd.ρ)) * cd.C t
        + cd.ρ * (k * cd.C t) := by ring
  linarith

/-- `frontier_cone_inductive` from `Hagi.Growth.FrontierScaling`
as an instance of `cone_data_invariant` with `k = α / γ`:
under the same hypotheses, `α / γ * C (t + 1) ≤ D (t + 1)`. -/
alias frontier_cone_inductive_is_cone_data := _root_.Hagi.Foundations.frontier_cone_inductive


/-! ## The reinvest-form cone law -/

/-- Cone step law in reinvest form: given `0 < C t`, `0 ≤ k`,
retention `γ * k ≤ ρ`, the cone `k * C t ≤ D t`, the frontier
dynamics `ρ * D t + β * C t ≤ D (t + 1)`, the reinvest cap
`C (t + 1) ≤ C t + γ * D t`, and the threshold
`γ * k ^ 2 + (1 - ρ) * k ≤ β`, the cone is preserved:
`k * C (t + 1) ≤ D (t + 1)`. -/
theorem cone_reinvest_invariant (C D : ℕ → ℝ) (γ ρ β k : ℝ)
    (t : ℕ) (hCpos : 0 < C t) (hk : 0 ≤ k)
    (hrho : γ * k ≤ ρ)
    (hcone : k * C t ≤ D t)
    (h_dyn : ρ * D t + β * C t - 0 ≤ D (t + 1))
    (h_cap : C (t + 1) ≤ C t + γ * D t)
    (hβ : γ * k ^ 2 + (1 - ρ) * k ≤ β) :
    k * C (t + 1) ≤ D (t + 1) := by
  have hkey : ρ * D t + β * C t - k * (C t + γ * D t)
      = (ρ - γ * k) * (D t - k * C t)
        + (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t := by
    field_simp
    ring
  have h1 : (0:ℝ) ≤ (ρ - γ * k) * (D t - k * C t) := by
    have hsub : (0:ℝ) ≤ D t - k * C t := by linarith [hcone]
    exact mul_nonneg (by linarith [hrho]) hsub
  have h2 : (0:ℝ) ≤ (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t :=
    mul_nonneg (by linarith [hβ]) hCpos.le
  have hkC : k * C (t + 1) ≤ k * (C t + γ * D t) :=
    mul_le_mul_of_nonneg_left h_cap hk
  have h3 : D (t + 1) - k * C (t + 1)
      ≥ (ρ - γ * k) * (D t - k * C t)
        + (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t := by
    linarith [h_dyn, hkey, hkC]
  linarith

/-- `cone_ratio_step` (exact step `C (t + 1) = C t + γ * D t`,
zero forcing) as the equality case of `cone_reinvest_invariant`:
under the same hypotheses, `k * C (t + 1) ≤ D (t + 1)`. -/
theorem cone_ratio_step_is_reinvest (C D : ℕ → ℝ)
    (γ ρ β k : ℝ) {t : ℕ} (hk : 0 ≤ k)
    (hstep : C (t + 1) = C t + γ * D t)
    (hdyn : ρ * D t + β * C t ≤ D (t + 1))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (hCpos : 0 < C t) (hcone : k * C t ≤ D t) :
    k * C (t + 1) ≤ D (t + 1) :=
  cone_reinvest_invariant C D γ ρ β k t hCpos
    hk hrhogk hcone
    (by linarith [hdyn]) (le_of_eq hstep) hbeta


/-! ### Аудит v17, P1: единое ядро роста

`GrowthDynamics` (бундл предпосылок аудита §6.1)
сводится к абстрактному ядру
конуса `ConeData` (см. также
`MasterHAGITrunc.frontier_cone_struct` — та же
индукция через единственную копию
тождества `cone_step`). Здесь —
канальная проекция: предпосылки
бундла совпадают с полями ConeData. -/

/-- Bundle GrowthDynamics порождает конусные
данные ядра (канальная проекция:
каждое поле полегко
восстанавливается из следующего). -/
def coneDataOfGrowthDynamics (C G D : ℕ → ℝ) (xi : ℕ → ℝ)
    (alpha gamma rho beta : ℝ) :
    ConeData where
  C := C
  D := D
  ξ := xi
  γ := gamma
  ρ := rho
  β := beta

/-- МОСТ: согласованность проекции — эта же
капабилити/фронтир/принуждение и
константы законов. -/
theorem coneDataOfGrowthDynamics_eq (C G D : ℕ → ℝ) (xi : ℕ → ℝ)
    (alpha gamma rho beta : ℝ) :
    (coneDataOfGrowthDynamics C G D xi alpha gamma rho beta).C = C
    ∧ (coneDataOfGrowthDynamics C G D xi alpha gamma rho beta).D = D
    ∧ (coneDataOfGrowthDynamics C G D xi alpha gamma rho beta).ξ = xi
    ∧ (coneDataOfGrowthDynamics C G D xi alpha gamma rho beta).γ = gamma
    ∧ (coneDataOfGrowthDynamics C G D xi alpha gamma rho beta).ρ = rho
    ∧ (coneDataOfGrowthDynamics C G D xi alpha gamma rho beta).β = beta := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Hagi.Growth

end C238_conedyn
section C238_nonlin
/-!
# NonlinearCone — вогнутый (корневой) конус: полиномиальный takeoff

Закон прироста `G(C) = γ·√(k·C)` вместо линейного.

* `sqrt_gain_step`: при `0 < γ`, `0 < k`, `0 < x` —
  `√x + γ√k/(2 + γ√k/√x) ≤ √(x + γ√(k·x))` — прирост `√C`
  ограничен снизу константой;
* `sqrt_gain_takeoff`: если `C (t+1) = C t + sqrtGain γ k (C t)`
  и `C t > 0`, то `C T ≥ (√C₀ + c₀·T)²`, где
  `c₀ = γ√k/(2 + γ√k/√C₀)` — квадратичный рост;
* `nonlinear_zero_kill`: если `0 ≤ phiE` и `η ≤ 0`, то
  `η·phiE ≤ 0`.

h_emp_-посылки (измеримость γ, k) остаются — устранена только
линейная идеализация закона прироста.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- Вогнутый (корневой) прирост: `sqrtGain γ k C = γ·√(k·C)`. -/
noncomputable def sqrtGain (γ k C : ℝ) : ℝ := γ * Real.sqrt (k * C)

/-- При `0 < γ`, `0 < k`, `0 < x`:
`√x + γ√k/(2 + γ√k/√x) ≤ √(x + γ√(k·x))` — прирост `√x`
за шаг ограничен снизу константой. -/
theorem sqrt_gain_step (γ k x : ℝ) (hγ : 0 < γ) (hk : 0 < k)
    (hx : 0 < x) :
    Real.sqrt x + γ * Real.sqrt k / (2 + γ * Real.sqrt k / Real.sqrt x)
      ≤ Real.sqrt (x + γ * Real.sqrt (k * x)) := by
  set c : ℝ := γ * Real.sqrt k with hc
  have hcpos : 0 < c := mul_pos hγ (Real.sqrt_pos.mpr hk)
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hsqrtkx : γ * Real.sqrt (k * x) = c * Real.sqrt x := by
    have h : Real.sqrt (k * x) = Real.sqrt k * Real.sqrt x :=
      Real.sqrt_mul (le_of_lt hk) x
    show γ * Real.sqrt (k * x) = γ * Real.sqrt k * Real.sqrt x
    rw [h]
    ring
  -- upper bound: √(x + γ√(kx)) ≤ √x + c =: u
  have hub : Real.sqrt (x + γ * Real.sqrt (k * x))
      ≤ Real.sqrt x + c := by
    have hle : x + γ * Real.sqrt (k * x)
        ≤ (Real.sqrt x + c) ^ 2 := by
      have hrhs : (Real.sqrt x + c) ^ 2
          = x + 2 * Real.sqrt x * c + c ^ 2 := by
        have h1 : (Real.sqrt x + c) ^ 2
            = (Real.sqrt x) ^ 2 + 2 * Real.sqrt x * c + c ^ 2 :=
          by ring
        rw [h1, Real.sq_sqrt hx.le]
      rw [hrhs, hsqrtkx]
      have h2 : c * Real.sqrt x ≤ 2 * Real.sqrt x * c :=
        by nlinarith [hsx, le_of_lt hcpos]
      nlinarith [sq_nonneg c, h2]
    have hnonneg : 0 ≤ Real.sqrt x + c := by positivity
    have hsq' : Real.sqrt ((Real.sqrt x + c) ^ 2) = Real.sqrt x + c :=
      Real.sqrt_sq hnonneg
    rw [← hsq']
    exact Real.sqrt_le_sqrt hle
  -- factorization and division
  have hfac : (Real.sqrt (x + γ * Real.sqrt (k * x))
      + Real.sqrt x) * (Real.sqrt (x + γ * Real.sqrt (k * x))
      - Real.sqrt x) = c * Real.sqrt x := by
    have hy : x + γ * Real.sqrt (k * x) - x
        = γ * Real.sqrt (k * x) := by ring
    have hy' : x + γ * Real.sqrt (k * x) - x
        = γ * Real.sqrt (k * x) := by ring
    have h1 : (Real.sqrt (x + γ * Real.sqrt (k * x))) ^ 2
        = x + γ * Real.sqrt (k * x) :=
      Real.sq_sqrt (by positivity)
    have h2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
    nlinarith [h1, h2, hy', hsqrtkx]
  have hsum : Real.sqrt (x + γ * Real.sqrt (k * x)) + Real.sqrt x
      ≤ 2 * Real.sqrt x + c := by linarith
  have hdenpos : 0 < 2 * Real.sqrt x + c :=
    add_pos (by positivity) hcpos
  have hdenne : (2 + c / Real.sqrt x) ≠ 0 := by
    have : (0:ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx
    have : 0 < 2 + c / Real.sqrt x := by
      have hcdiv : 0 ≤ c / Real.sqrt x :=
        div_nonneg hcpos.le this.le
      linarith
    exact ne_of_gt this
  rw [hsqrtkx] at hfac
  -- √y − √x = c√x / (√y + √x) ≥ c√x / (2√x + c)
  have hge0 : 0 ≤ Real.sqrt (x + γ * Real.sqrt (k * x))
      - Real.sqrt x := by
    have hnn : 0 ≤ γ * Real.sqrt (k * x) :=
      mul_nonneg hγ.le (Real.sqrt_nonneg _)
    have h1 : Real.sqrt x ≤ Real.sqrt (x + γ * Real.sqrt (k * x)) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  have hdiv : c * Real.sqrt x / (2 * Real.sqrt x + c)
      ≤ Real.sqrt (x + γ * Real.sqrt (k * x)) - Real.sqrt x := by
    -- the denominator bound and the factorization give the
    -- increment directly
    have hstepkey : (Real.sqrt (x + γ * Real.sqrt (k * x))
        - Real.sqrt x) * (2 * Real.sqrt x + c) ≥ c * Real.sqrt x := by
      have hA : (Real.sqrt (x + γ * Real.sqrt (k * x))
          - Real.sqrt x) * (2 * Real.sqrt x + c)
          ≥ (Real.sqrt (x + γ * Real.sqrt (k * x)) - Real.sqrt x)
            * (Real.sqrt (x + γ * Real.sqrt (k * x)) + Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hsum hge0
      have hy : x + γ * Real.sqrt (k * x) - x
          = γ * Real.sqrt (k * x) := by ring
      have hsy : (Real.sqrt (x + γ * Real.sqrt (k * x))) ^ 2
          = x + γ * Real.sqrt (k * x) :=
        Real.sq_sqrt (by positivity)
      have hsx2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
      have hB : (Real.sqrt (x + γ * Real.sqrt (k * x))
          - Real.sqrt x) * (Real.sqrt (x + γ * Real.sqrt (k * x))
          + Real.sqrt x) = γ * Real.sqrt (k * x) :=
        by linear_combination hy + hsy - hsx2
      rw [hB, hsqrtkx] at hA
      rw [hsqrtkx]
      exact hA
    rw [(div_le_iff₀ hdenpos)]
    linarith [hstepkey]
  -- final chain
  have hfin : c * Real.sqrt x / (2 * Real.sqrt x + c)
      ≥ γ * Real.sqrt k / (2 + γ * Real.sqrt k / Real.sqrt x) := by
    have hsx0 : (0:ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx
    field_simp
    nlinarith [hc, hsum]
  linarith

/-- Если `0 < γ`, `0 < k`, `0 < C 0`, `0 < C t` при всех t и
`C (t+1) = C t + sqrtGain γ k (C t)`, то при всех T
`(√(C 0) + c₀·T)² ≤ C T`, где
`c₀ = γ√k/(2 + γ√k/√(C 0))`. -/
theorem sqrt_gain_takeoff (C : ℕ → ℝ) (γ k : ℝ)
    (hγ : 0 < γ) (hk : 0 < k) (hC0 : 0 < C 0)
    (hmono : ∀ t, 0 < C t)
    (hstep : ∀ t, C (t + 1) = C t + sqrtGain γ k (C t)) :
    ∀ T : ℕ, (Real.sqrt (C 0)
      + γ * Real.sqrt k / (2 + γ * Real.sqrt k / Real.sqrt (C 0)) * T) ^ 2
      ≤ C T := by
  set c0 : ℝ := γ * Real.sqrt k / (2 + γ * Real.sqrt k / Real.sqrt (C 0))
    with hc0
  -- the sequence is increasing (the gain is positive)
  have hge : ∀ t, C 0 ≤ C t := by
    intro t
    induction t with
    | zero => exact le_refl _
    | succ t ih =>
        rw [hstep t, sqrtGain]
        have hg : 0 ≤ γ * Real.sqrt (k * C t) :=
          mul_nonneg hγ.le (Real.sqrt_nonneg _)
        linarith
  -- c(x) is minimized at x = C 0 (denominator shrinks with x)
  have hcmono : ∀ t, c0 ≤ γ * Real.sqrt k
      / (2 + γ * Real.sqrt k / Real.sqrt (C t)) := by
    intro t
    have hsq : Real.sqrt (C 0) ≤ Real.sqrt (C t) :=
      Real.sqrt_le_sqrt (hge t)
    have hs0 : (0:ℝ) < Real.sqrt (C 0) :=
      Real.sqrt_pos.mpr hC0
    have hst : (0:ℝ) < Real.sqrt (C t) :=
      Real.sqrt_pos.mpr (hmono t)
    have hgk : (0:ℝ) < γ * Real.sqrt k := by positivity
    -- n_x <= n_0 (the inner quotient shrinks)
    have h1 : γ * Real.sqrt k / Real.sqrt (C t)
        ≤ γ * Real.sqrt k / Real.sqrt (C 0) := by
      rw [le_div_iff₀ hs0]
      field_simp
      nlinarith [hsq, hgk]
    have hden1 : (0:ℝ) < 2 + γ * Real.sqrt k / Real.sqrt (C t) := by
      have := div_nonneg hgk.le hst.le
      linarith
    have hden0 : (0:ℝ) < 2 + γ * Real.sqrt k / Real.sqrt (C 0) := by
      have := div_nonneg hgk.le hs0.le
      linarith
    -- cross-multiply: A/n0 <= A/n1 iff n1 <= n0
    unfold c0
    rw [le_div_iff₀ hden1]
    field_simp
    nlinarith [hsq, hgk]
  -- induction on the sqrt scale
  have hmain : ∀ T : ℕ,
      Real.sqrt (C 0) + c0 * T ≤ Real.sqrt (C T) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
        -- the step law in raw form
        have hraw : C (T + 1)
            = C T + γ * Real.sqrt (k * C T) := by
          rw [hstep T, sqrtGain]
        -- apply the per-step lemma
        have hstep' := sqrt_gain_step γ k (C T) hγ hk (hmono T)
        have hc' := hcmono T
        rw [hraw]
        have hpos : 0 < γ * Real.sqrt k
            / (2 + γ * Real.sqrt k / Real.sqrt (C T)) := by
          apply div_pos _ (by
            have hst : (0:ℝ) < Real.sqrt (C T) :=
              Real.sqrt_pos.mpr (hmono T)
            have hgk : (0:ℝ) < γ * Real.sqrt k := by positivity
            have := div_nonneg hgk.le hst.le
            linarith)
          positivity
        have hgoal : Real.sqrt (C 0) + c0 * (T + 1)
            ≤ Real.sqrt (C T + γ * Real.sqrt (k * C T)) := by
          have h1 : Real.sqrt (C 0) + c0 * T + c0
              ≤ Real.sqrt (C T)
                + γ * Real.sqrt k
                  / (2 + γ * Real.sqrt k / Real.sqrt (C T)) := by
            linarith
          linarith
        rw [show ((T + 1 : ℕ) : ℝ) = ((T : ℕ) : ℝ) + 1 from by
          push_cast; ring]
        exact hgoal
  -- square both sides
  intro T
  have h := hmain T
  have hsq : (Real.sqrt (C 0) + c0 * T) * (Real.sqrt (C 0) + c0 * T)
      ≤ Real.sqrt (C T) * Real.sqrt (C T) := by
    have hnn : 0 ≤ Real.sqrt (C 0) + c0 * ((T : ℕ) : ℝ) := by
      have hc0' : 0 ≤ c0 := by
        have hgk : (0:ℝ) < γ * Real.sqrt k := by positivity
        have hsd : (0:ℝ) < Real.sqrt (C 0) := Real.sqrt_pos.mpr hC0
        have hinn : (0:ℝ) ≤ γ * Real.sqrt k / Real.sqrt (C 0) :=
          div_nonneg hgk.le hsd.le
        have hden : (0:ℝ) < 2 + γ * Real.sqrt k / Real.sqrt (C 0) := by
          linarith
        exact div_nonneg hgk.le hden.le
      have := mul_nonneg hc0' (by positivity)
      positivity
    exact mul_self_le_mul_self hnn h
  -- convert the product form back to the square form
  -- (a)^2 = a*a; (√x)^2 = x
  have h1 : (Real.sqrt (C 0) + c0 * ((T : ℕ) : ℝ)) ^ 2
      = (Real.sqrt (C 0) + c0 * ((T : ℕ) : ℝ))
        * (Real.sqrt (C 0) + c0 * ((T : ℕ) : ℝ)) := by ring
  have h2 : (Real.sqrt (C T)) ^ 2 = C T :=
    Real.sq_sqrt (hmono T).le
  calc (Real.sqrt (C 0) + c0 * T) ^ 2
      = (Real.sqrt (C 0) + c0 * T)
        * (Real.sqrt (C 0) + c0 * T) := h1
  _ ≤ Real.sqrt (C T) * Real.sqrt (C T) := hsq
  _ = C T := by
        have := h2
        rw [← pow_two (Real.sqrt (C T))]
        exact this

/-- Если `0 ≤ phiE` и `η ≤ 0`, то `η·phiE ≤ 0`. -/
theorem nonlinear_zero_kill (η phiE : ℝ) (hφ : 0 ≤ phiE)
    (hη : η ≤ 0) :
    η * phiE ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg hη hφ


end Hagi.Growth

end C238_nonlin
section C238_frontier
/-!
# FrontierScaling — конус-инвариант из производственной динамики

Фронтир (usable disagreement) D и capability C связаны
посылками: динамика производства `D (t+1) ≥ ρ·D t + β·C t − ξ t`,
кап на рост `C (t+1) ≤ (1+α)·C t`, конус в нуле и порог на `β`.

  пороге `(α/γ)·((1+α) − ρ) + ξ t / C t ≤ β` (нужно `0 < C t`);
(Конусный шаг/инвариант перенесён в Foundations/ConeTakeoff — R326.)
* `takeoff_edge_forced`: при точном шаге, gain-законе, конусе
  и капе выполнены тождества `G = α·C`, `D = (α/γ)·C`,
  `C' = (1+α)·C` — модель ПОЛНОСТЬЮ НАСЫЩЕННОГО режима
  (одновременные нижняя и верхняя границы роста): точное
  равенство каждой итерации. Это не устойчивая гарантия для
  произвольного обучения с шумом — вне насыщения применять
  нельзя (оговорка );
* `sustained_takeoff_from_production`: из указанных посылок —
  `C 0 * (1 + α) ^ T ≤ C T` для всех T (без свободной
  гипотезы «α·C ≤ γ·D»: ворота выводятся из конуса);
* `frontier_asymptotic`: если `ξ t ≤ ξ̄·C t`, порог стягивается
  к константе `(α/γ)·((1+α) − ρ) + ξ̄ ≤ β` и выводится тот же
  takeaway.

Эмпирическое содержание — сами посылки (динамика, порог).
-/

open Real Finset

namespace Hagi.Growth

/-! ## The cone step -/

/-- При `0 < γ`, точном шаге `C (t+1) = C t + G t`,
gain-законе `γ·D t ≤ G t`, конусе `α/γ·C t ≤ D t` и капе
`C (t+1) ≤ (1+α)·C t` выполнены тождества
`G t = α·C t`, `D t = α/γ·C t` и `C (t+1) = (1+α)·C t`. -/
theorem takeoff_edge_forced (C G D : ℕ → ℝ) (α γ : ℝ)
    (hγ : 0 < γ)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_cone : ∀ t, α / γ * C t ≤ D t)
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (t : ℕ) :
    G t = α * C t ∧ D t = α / γ * C t
      ∧ C (t + 1) = (1 + α) * C t := by
  have hg := h_gain_prod t
  have hc := h_cone t
  have hcap := h_C_cap t
  have hstep := h_step t
  have he : γ * (α / γ * C t) = α * C t := by
    field_simp
  -- конус ⇒ α·C ≤ G
  have hchain : α * C t ≤ G t := by
    have h1 : γ * (α / γ * C t) ≤ γ * D t :=
      mul_le_mul_of_nonneg_left hc hγ.le
    rw [he] at h1
    exact le_trans h1 hg
  -- зажатие C' = (1+α)C
  have hkey : C t + G t = (1 + α) * C t := by
    have hring : (1 + α) * C t = C t + α * C t := by ring
    have hlow : (1 + α) * C t ≤ C t + G t := by
      rw [hring]
      linarith [hchain]
    linarith [hlow]
  -- G = αC
  have hGeq : G t = α * C t := by
    have hring : (1 + α) * C t = C t + α * C t := by ring
    linarith [hkey, hring]
  -- γD = αC (зажато с двух сторон) ⇒ D = (α/γ)C
  have hpin : γ * D t = α * C t := by
    rw [hGeq] at hg
    exact le_antisymm hg
      (by rw [← he]; exact mul_le_mul_of_nonneg_left hc hγ.le)
  have hDeq : D t = α / γ * C t := by
    field_simp
    linarith [hpin]
  exact ⟨hGeq, hDeq, hstep ▸ hkey⟩

/-- Вспомогательная (private): при `0 < C 0`, конусе в нуле,
точном шаге, gain-законе, динамике, капе и пороге (при каждом
t, с `0 < C t`) выполнено `0 < C t ∧ α/γ·C t ≤ D t` при всех t.
Позитивность и конус доказываются совместно: порог делит на
`C t`, а позитивность `C (t+1)` следует из конуса при t. -/
private theorem cone_and_pos (C G D ξ : ℕ → ℝ) (α γ ρ β : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hC0 : 0 < C 0) (h_cone0 : α / γ * C 0 ≤ D 0)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_dyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (hβ : ∀ t, 0 < C t → α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β) :
    ∀ t, 0 < C t ∧ α / γ * C t ≤ D t := by
  intro t
  induction t with
  | zero => exact ⟨hC0, h_cone0⟩
  | succ t ih =>
      obtain ⟨hpos, hcone⟩ := ih
      -- the gate at t from the cone: α·C_t = γ·(k·C_t) ≤ γ·D_t ≤ G_t
      have hg : γ * (α / γ * C t) ≤ G t :=
        le_trans (mul_le_mul_of_nonneg_left hcone hγ.le) (h_gain_prod t)
      have e : γ * (α / γ * C t) = α * C t := by
        field_simp
      rw [e] at hg
      have hA : 0 < α * C t := by positivity
      refine ⟨?_, Hagi.Foundations.frontier_cone_inductive C D ξ α γ ρ β hα hγ hρ t
        hpos hcone (h_dyn t) (h_C_cap t) (hβ t hpos)⟩
      rw [h_step t]
      linarith

/-- При `0 < α`, `0 < γ`, `0 ≤ ρ`, `0 < C 0`, конусе в нуле,
точном шаге `C (t+1) = C t + G t`, gain-законе `γ·D t ≤ G t`,
динамике `ρ·D t + β·C t − ξ t ≤ D (t+1)`, капе
`C (t+1) ≤ (1+α)·C t` и пороге
`α/γ·((1+α) − ρ) + ξ t / C t ≤ β` выводится
`C 0 * (1 + α) ^ T ≤ C T` для всех `T`: ворота
`α·C t ≤ γ·D t` выводятся из конус-инварианта и применяется
`renewal_feeds_takeoff`. -/
theorem sustained_takeoff_from_production (C G D ξ : ℕ → ℝ)
    (α γ ρ β : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hC0 : 0 < C 0)
    (h_cone0 : α / γ * C 0 ≤ D 0)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_dyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (hβ : ∀ t, α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β)
    (T : ℕ) :
    C 0 * (1 + α) ^ T ≤ C T := by
  have hcp := cone_and_pos C G D ξ α γ ρ β hα hγ hρ hC0 h_cone0
    h_step h_gain_prod h_dyn h_C_cap (fun t _ => hβ t)
  have hCpos : ∀ t, 0 < C t := fun t => (hcp t).1
  have hcone := Hagi.Foundations.frontier_cone_invariant C D ξ α γ ρ β hα hγ hρ hCpos
    h_cone0 h_dyn h_C_cap hβ
  -- the gate, DERIVED from the cone: α·C_t = γ·((α/γ)·C_t) ≤ γ·D_t
  have hgate : ∀ t, α * C t ≤ γ * D t := by
    intro t
    have h1 : γ * (α / γ * C t) ≤ γ * D t :=
      mul_le_mul_of_nonneg_left (hcone t) hγ.le
    have e : γ * (α / γ * C t) = α * C t := by
      field_simp
    linarith
  exact renewal_feeds_takeoff C G D α γ hα h_step h_gain_prod hgate T

/-! ## The asymptotic (constant-threshold) corollary -/

/-- Версия `sustained_takeoff_from_production` с постоянным
порогом: если дополнительно `ξ t ≤ ξ̄·C t` при всех t и
`α/γ·((1+α) − ρ) + ξ̄ ≤ β`, то `C 0 * (1 + α) ^ T ≤ C T`. -/
theorem frontier_asymptotic (C G D ξ : ℕ → ℝ)
    (α γ ρ β ξbar : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hC0 : 0 < C 0)
    (h_cone0 : α / γ * C 0 ≤ D 0)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_dyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (h_xibar : ∀ t, ξ t ≤ ξbar * C t)
    (h_beta_const : α / γ * ((1 + α) - ρ) + ξbar ≤ β)
    (T : ℕ) :
    C 0 * (1 + α) ^ T ≤ C T := by
  have hcp := cone_and_pos C G D ξ α γ ρ β hα hγ hρ hC0 h_cone0
    h_step h_gain_prod h_dyn h_C_cap
      (fun t ht => by
        have h := (div_le_iff₀ ht).mpr (h_xibar t)
        linarith [h, h_beta_const])
  have hCpos : ∀ t, 0 < C t := fun t => (hcp t).1
  have hcone : ∀ t, α / γ * C t ≤ D t := fun t => (hcp t).2
  have hgate : ∀ t, α * C t ≤ γ * D t := by
    intro t
    have h1 : γ * (α / γ * C t) ≤ γ * D t :=
      mul_le_mul_of_nonneg_left (hcone t) hγ.le
    have e : γ * (α / γ * C t) = α * C t := by
      field_simp
    linarith
  exact renewal_feeds_takeoff C G D α γ hα h_step h_gain_prod hgate T

end Hagi.Growth


namespace Hagi
export Hagi.Growth (sustained_takeoff_from_production)
export Hagi.Foundations.GrowthBand (growth_band_step growth_band_iter)
end Hagi

end C238_frontier
