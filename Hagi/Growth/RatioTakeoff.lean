/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.FrontierScaling
set_option linter.style.header false

/-!
# R124: RatioTakeoff — устойчивый takeoff БЕЗ h_C_cap

Аудит R123/124 (главная находка + приоритет №1): конус-метод
(`sustained_takeoff_from_production`) с гипотезой `h_C_cap`
зажимает систему ровно на границу конуса (`takeoff_edge_forced`:
G = αC, D = (α/γ)C тождественно) — сертификат хрупкок.
Правильная постановка — динамика ОТНОШЕНИЯ r = D/C:

  C' = C + γ·D,  D' ≥ ρ·D + β·C − ξ.

Тогда r' ≥ (ρr + β − ξ/C)/(1 + γr), и конус {r ≥ k}
инвариантен при ДВУХ односторонних условиях:

* порог зажигания: β ≥ γ·k² + (1−ρ)·k (+ ξ_t/C_t при
  ненулевом трении — ξ компенсируется ТОЧНО, см. докстринг
  `cone_ratio_step` для ξ = 0-формы);
* скорость декея: ρ ≥ γ·k.

Ключевая алгебра: D' − k·C' ≥ (ρ − γk)·(D − k·C) + margin·C —
одностороннее неравенство, НИЧЕГО не форсирующее.

**Теоремы:**

* `cone_ratio_step` — шаг индукции конуса (ξ = 0 форма).
* `cone_ratio_invariant` — конус при всех t.
* `ratio_takeoff` — C_T ≥ C₀·(1+γk)^T при конусе:
  односторонний рост, БЕЗ верхней границы.
* `frontier_decay_no_growth` — затухающая ветвь бифуркации:
  при β = 0, ρ < 1 frontier геометрически затухает
  (D T ≤ ρ^T·D 0) — без производства нет роста.

**Честные границы**: ξ ≠ 0-компенсация (полю β + ξ/C) —
механическое расширение шага, оставлено вне ядра; полю β —
измеряемое (R117); насыщение C* — открыто.
R132-REV FREEZE (план §7.3): экспоненциальный конус — закон
роста с КОНЕЧНЫМ ГОРИЗОНТОМ T* ≤ ln(C*/C₀)/ln(1+γk):
пошаговое пороговое условие ∀t требует экспоненциально
растущей входной энергии в ограниченном (тернарно
scale-invariant) пространстве; совместим с PL-границей
насыщения только до T*. Содержательные безусловные
утверждения — liveness и насыщение.
-/

open Finset Real

namespace Hagi

/-- Конус отношения: r_t = D_t/C_t ≥ k, без деления. -/
def ConeRatio (C D : ℕ → ℝ) (k : ℝ) : Prop :=
  ∀ t, k * C t ≤ D t

/-- **Шаг индукции конуса отношений** (ξ = 0 форма): при
C' = C + γD, D' ≥ ρD + βC, ρ ≥ γk и полю зажигания
β ≥ γk² + (1−ρ)k конус r ≥ k переходит из t в t+1.
Ключ: D' − kC' ≥ (ρ−γk)(D−kC) + (β−γk²−(1−ρ)k)·C ≥ 0 —
одностороннее неравенство (ничего не форсирует — отличие
от h_C_cap-версии). При ξ ≠ 0 полю усиливается до
β ≥ γk² + (1−ρ)k + ξ/C: ξ-слагаемое компенсируется точно
(добавляется в обе части ключевой алгебры). -/
theorem cone_ratio_step (C D : ℕ → ℝ) (γ ρ β k : ℝ)
    (hstep : ∀ t, C (t + 1) = C t + γ * D t)
    (hdyn : ∀ t, ρ * D t + β * C t ≤ D (t + 1))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    {t : ℕ}
    (hCpos : 0 < C t) (hcone : k * C t ≤ D t) :
    k * C (t + 1) ≤ D (t + 1) := by
  have hd := hdyn t
  have hb := hbeta
  have hs := hstep t
  have hkey : ρ * D t + β * C t - k * (C t + γ * D t)
      = (ρ - γ * k) * (D t - k * C t)
        + (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t := by
    field_simp
    ring
  have h1 : (0:ℝ) ≤ (ρ - γ * k) * (D t - k * C t) := by
    have hsub : (0:ℝ) ≤ D t - k * C t := by linarith [hcone]
    exact mul_nonneg (by linarith [hrhogk]) hsub
  have h2 : (0:ℝ) ≤ (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t :=
    mul_nonneg (by linarith [hb]) hCpos.le
  have h3 : D (t + 1) - k * C (t + 1)
      ≥ (ρ - γ * k) * (D t - k * C t)
        + (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t := by
    rw [hs]
    linarith [hd, hkey]
  linarith

/-- **Инвариант конуса отношений**: при ρ ≥ γk и полю
зажигания β ≥ γk² + (1−ρ)k конус r ≥ k поддерживается
всегда (индукция). -/
theorem cone_ratio_invariant (C D : ℕ → ℝ) (γ ρ β k : ℝ)
    (hCpos : ∀ t, 0 < C t)
    (hstep : ∀ t, C (t + 1) = C t + γ * D t)
    (hdyn : ∀ t, ρ * D t + β * C t ≤ D (t + 1))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (hcone0 : k * C 0 ≤ D 0) :
    ConeRatio C D k := by
  intro t
  induction t with
  | zero => exact hcone0
  | succ t ih =>
      exact cone_ratio_step C D γ ρ β k hstep hdyn hrhogk hbeta
        (hCpos t) ih

/-- **Ratio takeoff**: при инвариантном конусе r ≥ k
C_{t+1} = C + γD ≥ C(1 + γk), следовательно
C_T ≥ C₀·(1+γk)^T — односторонний рост, БЕЗ верхней границы
h_C_cap: система может расти и быстрее сертификата;
возмущения вниз обрабатываются пошагово (шаг конуса
заново проверяется по измерениям), а не ломают всё
мгновенно. -/
theorem ratio_takeoff (C D : ℕ → ℝ) (γ k : ℝ)
    (hγ : 0 < γ) (hk : 0 < k)
    (hstep : ∀ t, C (t + 1) = C t + γ * D t)
    (hcone : ConeRatio C D k) (T : ℕ) :
    C 0 * (1 + γ * k) ^ T ≤ C T := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hc := hcone T
      have hs := hstep T
      have hgrow : (1 + γ * k) * C T ≤ C (T + 1) := by
        rw [hs]
        have hring : C T + γ * k * C T = (1 + γ * k) * C T := by ring
        have hmul : γ * (k * C T) ≤ γ * D T :=
          mul_le_mul_of_nonneg_left hc hγ.le
        have hring2 : C T + γ * k * C T = C T + γ * (k * C T) := by ring
        linarith [hring, hring2, hmul]
      have hcast : (1 + γ * k) ^ (T + 1)
          = (1 + γ * k) ^ T * (1 + γ * k) := by ring
      rw [hcast]
      calc C 0 * ((1 + γ * k) ^ T * (1 + γ * k))
          = (C 0 * (1 + γ * k) ^ T) * (1 + γ * k) := by ring
        _ ≤ C T * (1 + γ * k) :=
            mul_le_mul_of_nonneg_right ih (by positivity)
        _ = (1 + γ * k) * C T := by ring
        _ ≤ C (T + 1) := hgrow

/-- **Затухающая ветвь бифуркации** (audit «зажигание или
коллапс»): без производства frontier (β = 0) и ρ < 1
frontier геометрически затухает: D_T ≤ ρ^T·D₀. Вместе с
`cone_ratio_invariant` (полю β ≥ порога зажигания ⇒ рост
C₀(1+γk)^T) это формализует бифуркацию: β ниже порога —
затухание, выше — экспоненциальный рост. -/
theorem frontier_decay_no_growth (D : ℕ → ℝ) (ρ : ℝ)
    (hrho : 0 ≤ ρ)
    (hdyn : ∀ t, D (t + 1) ≤ ρ * D t) (T : ℕ) :
    D T ≤ ρ ^ T * D 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hdyn T
      have h2 : ρ ^ (T + 1) * D 0 = ρ * (ρ ^ T * D 0) := by ring
      calc D (T + 1) ≤ ρ * D T := h1
        _ ≤ ρ * (ρ ^ T * D 0) :=
            mul_le_mul_of_nonneg_left ih hrho
        _ = ρ ^ (T + 1) * D 0 := h2.symm

end Hagi
