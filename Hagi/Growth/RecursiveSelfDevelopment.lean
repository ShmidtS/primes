/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.AdaptiveSuccess
set_option linter.style.header false

/-!
# RecursiveSelfDevelopment — обновление opportunity и замкнутый takeoff

* `opportunity_renewal`: при `ρ·D + β·C − ξ ≤ D'` и
  `(1−ρ)·D + δ_O ≤ β·C − ξ` следует `D + δ_O ≤ D'`;
* `recursive_self_development`: то же плюс `C ≤ C'`, `0 ≤ D`,
  `0 < δ_O` — влечёт `D + δ_O ≤ D' ∧ 0 < D'`;
* `multiplicative_growth`: если
  `C (t+1) ≥ C t·exp(α·S t − ε t)` при всех t, то
  `C 0·exp(α·ΣS − Σε) ≤ C T`;
* `closed_loop_takeoff`: композиция с
  `adaptive_success_concentrated` — при условных success-полах
  ≥ p₀ с вероятностью ≥ 1−δ выполнено
  `C 0·exp(α·(n·p₀ − √(n log(1/δ)/2)) − Σε) ≤ C n`.

Frontier-динамика и стрелка «runtime ⇒ success» — посылки,
здесь не выводятся.
-/

open Finset Real

namespace Hagi

/-! ## Обновление opportunity -/

/-- Если `ρ·D + β·C − ξ ≤ D'` и
`(1−ρ)·D + δ_O ≤ β·C − ξ`, то `D + δ_O ≤ D'`. -/
theorem opportunity_renewal (D D' C : ℝ) (rho beta xi deltaO : ℝ)
    (hdyn : rho * D + beta * C - xi ≤ D')
    (hfloor : (1 - rho) * D + deltaO ≤ beta * C - xi) :
    D + deltaO ≤ D' := by
  have hsplit : rho * D + ((1 - rho) * D + deltaO) = D + deltaO := by
    ring
  linarith [hdyn, hfloor, hsplit]

/-- При посылках `opportunity_renewal`, а также `C ≤ C'`,
`0 ≤ D` и `0 < δ_O` выполнено `D + δ_O ≤ D' ∧ 0 < D'`. -/
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

/-- Если `C (t+1) ≥ C t·exp(α·S t − ε t)` при всех t, то
`C 0·exp(α·ΣS − Σε) ≤ C T`. -/
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

/-! ## Замкнутый takeoff -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- Реализованный уровень успеха цикла t
(0 за горизонтом n). -/
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

/-- При per-cycle условных полах `SuccessFloor p Y p0`,
законе роста `C (t+1) ≥ C t·exp(α·realizedSuccess Y ω t − ε t)`
и `0 < δ < 1`: с вероятностью ≥ 1−δ из события
`n·p₀ − √(n log(1/δ)/2) ≤ Σ Y i (ω i)` следует
`C 0·exp(α·(n·p₀ − √(n log(1/δ)/2)) − Σ_{t<n} ε t) ≤ C n`. -/
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
  -- вероятностный перенос + монотонность
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
