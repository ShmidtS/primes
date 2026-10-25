import Mathlib.Tactic

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

end Hagi.Foundations