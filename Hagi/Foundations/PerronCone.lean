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

end Hagi.Foundations