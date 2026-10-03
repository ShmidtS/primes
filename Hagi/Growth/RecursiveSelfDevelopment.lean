/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.AdaptiveSuccess
set_option linter.style.header false

/-!
# P5: RecursiveSelfDevelopment — обновление opportunity + замкнутый takeoff

Аудит R122 (§22, §26-P5, §21): ключевая недостающая стрелка
саморазвития — не «найти upgrade» (R118), а

  Success_t ⇒ Opportunity_{t+1} ≥ Opportunity_t + δ_O

— успешный upgrade РАСШИРЯЕТ пространство будущих улучшений.
Без этого система — repeated fine-tuning, не recursive growth.

**Теоремы:**

* `opportunity_renewal` — из динамики frontier
  (D' ≥ ρ·D + β·C − ξ) при ρ ≤ 1: D' ≥ D + δ_O, где
  δ_O ≤ β·C − ξ — успешный шаг (capability не убывает)
  наращивает opportunity.
* `multiplicative_growth` — детерминированная аккумуляция:
  C_{t+1} ≥ C_t·exp(α·S_t − ε_t) ⇒
  C_T ≥ C₀·exp(α·ΣS − Σε) (индукция).
* `closed_loop_takeoff` — §21 аудита: композиция с
  `adaptive_success_concentrated` (R121): при условных
  success-полах ≥ p₀ выполнено
  P[C_T ≥ C₀·exp(α·(n·p₀ − √(n log(1/δ)/2)) − Σε)] ≥ 1−δ.

**Честные границы**: frontier-динамика — измеряемая посылка
(R117 сертифицирует её по разногласию экспертов); стрелка
«runtime ⇒ success» — P0-1/P3, открыто.
-/

open Finset Real

namespace Hagi

/-! ## Обновление opportunity (P5) -/

/-- **P5-стрелка**: при frontier-динамике D' ≥ ρ·D + β·C − ξ
и достаточном производстве
β·C − ξ ≥ (1−ρ)·D + δ_O успешный шаг наращивает opportunity:
D' ≥ D + δ_O. Член (1−ρ)·D — цена декея старого frontier;
δ_O — ЧИСТЫЙ прирост возможности улучшений. -/
theorem opportunity_renewal (D D' C : ℝ) (rho beta xi deltaO : ℝ)
    (hdyn : rho * D + beta * C - xi ≤ D')
    (hfloor : (1 - rho) * D + deltaO ≤ beta * C - xi) :
    D + deltaO ≤ D' := by
  have hsplit : rho * D + ((1 - rho) * D + deltaO) = D + deltaO := by
    ring
  linarith [hdyn, hfloor, hsplit]

/-- **Recursive self-development (P5)**: успешный шаг
(capability растёт: C ≤ C', производство β·C − ξ измерено по
исходному C) при положительном чистом производстве
δ_O > 0 наращивает opportunity: D + δ_O ≤ D' — формальная
стрелка «success ⇒ renewal» (audit §22). -/
theorem recursive_self_development (D D' C C' : ℝ)
    (rho beta xi deltaO : ℝ)
    (hdyn : rho * D + beta * C - xi ≤ D')
    (hsucc : C ≤ C') (hD : 0 ≤ D)
    (hpos : 0 < deltaO)
    (hfloor : (1 - rho) * D + deltaO ≤ beta * C - xi) :
    D + deltaO ≤ D' ∧ 0 < D' := by
  constructor
  · exact opportunity_renewal D D' C rho beta xi deltaO hdyn hfloor
  · have h := opportunity_renewal D D' C rho beta xi deltaO hdyn
      hfloor
    linarith

/-! ## Мультипликативная аккумуляция -/

/-- Аккумуляция мультипликативного роста: если каждый цикл даёт
C_{t+1} ≥ C_t·exp(α·S_t − ε_t) (S_t — уровень успеха [0,1],
ε_t — утечка), то C_T ≥ C₀·exp(α·ΣS − Σε). -/
theorem multiplicative_growth (C : ℕ → ℝ) (S eps : ℕ → ℝ)
    (alpha : ℝ)
    (hstep : ∀ t, C (t + 1) ≥ C t * Real.exp (alpha * S t - eps t))
    (T : ℕ) :
    C 0 * Real.exp (alpha * (∑ t ∈ Finset.range T, S t)
      - ∑ t ∈ Finset.range T, eps t) ≤ C T := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hstep T
      have hsum : (∑ t ∈ Finset.range (T + 1), S t)
          = (∑ t ∈ Finset.range T, S t) + S T := by
        rw [Finset.sum_range_succ]
      have hsume : (∑ t ∈ Finset.range (T + 1), eps t)
          = (∑ t ∈ Finset.range T, eps t) + eps T := by
        rw [Finset.sum_range_succ]
      rw [hsum, hsume]
      have hexp : Real.exp (alpha * ((∑ t ∈ Finset.range T, S t) + S T)
          - ((∑ t ∈ Finset.range T, eps t) + eps T))
          = Real.exp (alpha * (∑ t ∈ Finset.range T, S t)
            - ∑ t ∈ Finset.range T, eps t)
            * Real.exp (alpha * S T - eps T) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      calc C 0 * (Real.exp (alpha * (∑ t ∈ Finset.range T, S t)
            - ∑ t ∈ Finset.range T, eps t)
          * Real.exp (alpha * S T - eps T))
          = (C 0 * Real.exp (alpha * (∑ t ∈ Finset.range T, S t)
              - ∑ t ∈ Finset.range T, eps t))
            * Real.exp (alpha * S T - eps T) := by ring
        _ ≤ C T * Real.exp (alpha * S T - eps T) :=
            mul_le_mul_of_nonneg_right ih (by positivity)
        _ ≤ C (T + 1) := h1

/-! ## Замкнутый takeoff (§21 аудита) -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- Реализованный уровень успеха цикла t (0 за горизонтом n). -/
noncomputable def realizedSuccess {n : ℕ} (Y : Fin n → V → ℝ)
    (omega : Fin n → V) (t : ℕ) : ℝ :=
  if h : t < n then Y ⟨t, h⟩ (omega ⟨t, h⟩) else 0

/-- Сумма реализованных уровней по range n = сумма по Fin n. -/
theorem sum_realized {n : ℕ} (Y : Fin n → V → ℝ) (omega : Fin n → V) :
    ∑ t ∈ Finset.range n, realizedSuccess Y omega t = ∑ i, Y i (omega i) := by
  unfold realizedSuccess
  have hkey := Fin.sum_univ_eq_sum_range
    (fun t => if h : t < n then Y ⟨t, h⟩ (omega ⟨t, h⟩) else 0) n
  refine hkey.symm.trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos (Fin.isLt i)]

/-- **Closed-loop takeoff (audit §21)**: композиция
мультипликативного роста (по реализованным уровням успеха
`realizedSuccess Y ω t`) и адаптивных success-полов (R121):
при per-cycle условных полах ≥ p₀ и законе роста
C_{t+1} ≥ C_t·exp(α·S_t − ε_t) (для всех t; за горизонтом
константное продолжение C делает это тривиальным) с
вероятностью ≥ 1−δ: если success-floor держится, то
C_n ≥ C₀·exp(α·(n·p₀ − √(n log(1/δ)/2)) − Σ_{t<n} ε_t). -/
theorem closed_loop_takeoff {n : ℕ} (p : Fin n → V → ℝ)
    (hp : IsProbSys p)
    (Y : Fin n → V → ℝ) (hY : ∀ i v, 0 ≤ Y i v ∧ Y i v ≤ 1)
    (p0 : ℝ) (hfloor : SuccessFloor p Y p0)
    (hn : 0 < n)
    (C : ℕ → ℝ) (hC0 : 0 ≤ C 0) (eps : ℕ → ℝ) (heps : ∀ t, 0 ≤ eps t)
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (hstep : ∀ (t : ℕ) (omega : Fin n → V),
      C (t + 1) ≥ C t * Real.exp (alpha * realizedSuccess Y omega t
        - eps t))
    (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    1 - delta
      ≤ prodPq p (fun omega =>
        n * p0 - Real.sqrt ((n : ℝ) * Real.log (1 / delta) / 2)
          ≤ ∑ i, Y i (omega i)
          → C 0 * Real.exp (alpha * (n * p0
              - Real.sqrt ((n : ℝ) * Real.log (1 / delta) / 2))
              - ∑ t ∈ Finset.range n, eps t) ≤ C n) := by
  classical
  set deltaT : ℝ := Real.sqrt ((n : ℝ) * Real.log (1 / delta) / 2)
    with hdeltaT
  -- детерминированная аккумуляция при данном omega
  have hgrowth : ∀ omega : Fin n → V,
      n * p0 - deltaT ≤ ∑ i, Y i (omega i) →
      C 0 * Real.exp (alpha * (n * p0 - deltaT)
        - ∑ t ∈ Finset.range n, eps t) ≤ C n := by
    intro omega hfl
    have hacc := multiplicative_growth C
      (realizedSuccess Y omega) eps alpha
      (fun t => hstep t omega) n
    rw [sum_realized Y omega] at hacc
    have hmono : C 0 * Real.exp (alpha * (n * p0 - deltaT)
        - ∑ t ∈ Finset.range n, eps t)
        ≤ C 0 * Real.exp (alpha * (∑ i, Y i (omega i))
          - ∑ t ∈ Finset.range n, eps t) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact Real.exp_le_exp.mpr
        (add_le_add
          (mul_le_mul_of_nonneg_left hfl halpha) (le_refl _))
    exact le_trans hmono hacc
  -- вероятностный перенос (R121 + монотонность)
  have hconc := adaptive_success_concentrated p hp Y hY p0 hfloor
    hn delta hdelta hdelta1
  have hmono : prodPq p (fun omega =>
      n * p0 - Real.sqrt ((n : ℝ) * Real.log (1 / delta) / 2)
        ≤ ∑ i, Y i (omega i))
      ≤ prodPq p (fun omega =>
        n * p0 - Real.sqrt ((n : ℝ) * Real.log (1 / delta) / 2)
          ≤ ∑ i, Y i (omega i)
          → C 0 * Real.exp (alpha * (n * p0
              - Real.sqrt ((n : ℝ) * Real.log (1 / delta) / 2))
              - ∑ t ∈ Finset.range n, eps t) ≤ C n) :=
    prodPq_mono p hp _ _ (fun omega hfl hfl' => hgrowth omega hfl')
  exact le_trans hconc hmono

end Hagi
