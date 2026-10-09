/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.RatioTakeoff
set_option linter.style.header false

/-!
# R125: Saturation — насыщение ёмкости C* (PL-сжатие зазора)

Аудит R123/124, приоритет №1 (остаток): экспоненциальный рост
`ratio_takeoff` — нижняя оценка НЕОГРАНИЧЕННОЙ величины, а
реальные метрики ограничены. Замыкаем: ёмкость C* и
прогрессивно-сужающийся (PL) закон роста. Контракт — ДВЕ
односторонние пошаговые формы (одним измерением: gain_t):

* hpl_up: C_{t+1} ≤ C_t + σ·(C* − C_t) — шаг не больше
  доли σ остатка (нет перелёта через ёмкость);
* hpl_lo: C_t + σ·(C* − C_t) ≤ C_{t+1} — шаг покрывает
  долю σ остатка (равносильно сжатию зазора
  C* − C_{t+1} ≤ (1−σ)(C* − C_t), чистая алгебра).

**Теоремы:**

* `never_overshoot` — C_t ≤ C* всегда (из hpl_up, индукция).
* `pl_gap_geometric` — зазор сжимается геометрически:
  C* − C_t ≤ (1−σ)^t·(C* − C₀) (из hpl_lo, индукция).
* `saturation_limit` — ∀ε>0 ∃T ∀t≥T: C_t ≥ C* − ε.
  Конструктивно: T·σ·(1−σ)^T ≤ 1 (телескоп
  σ(1−σ)^i = (1−σ)^i − (1−σ)^{i+1}) + архимедовость.
* `takeoff_with_saturation` — ДВУСТОРОННЯЯ полоса:
  C₀·(1+γk)^T ≤ C_T ≤ C* − (1−σ)^T·(C* − C₀):
  экспонента взлёта сопоставлена с ограниченной метрикой.

**Честные границы**: σ и C* — измеряемые (h_emp_-слой);
PL-окно — пошаговый измеряемый сертификат, независимый от
конусной динамики (совместимость проверяется по данным,
горизонт полосы T ограничен областью, где обе посылки живы).
-/

open Finset Real

namespace Hagi

/-- **Ни одного перелёта**: при σ ∈ [0,1] и верхней PL-форме
C_{t+1} ≤ C_t + σ(C*−C_t) capability никогда не превосходит
ёмкость (индукция: при C_t ≤ C* шаг ≤ C* − (1−σ)(C*−C_t) ≤ C*). -/
theorem never_overshoot (C : ℕ → ℝ) (Cstar σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hpl_up : ∀ t, C (t + 1) ≤ C t + σ * (Cstar - C t))
    (hC0 : C 0 ≤ Cstar) (t : ℕ) :
    C t ≤ Cstar := by
  induction t with
  | zero => exact hC0
  | succ t ih =>
      have h := hpl_up t
      have hσ : (0:ℝ) ≤ 1 - σ := by linarith
      have hgap : (0:ℝ) ≤ Cstar - C t := by linarith
      have hX : (0:ℝ) ≤ (1 - σ) * (Cstar - C t) :=
        mul_nonneg hσ hgap
      have hring : C t + σ * (Cstar - C t)
          = Cstar - (1 - σ) * (Cstar - C t) := by ring
      linarith [hring ▸ h]

/-- **Геометрическое сжатие зазора**: нижняя PL-форма
C_t + σ(C*−C_t) ≤ C_{t+1} равносильна сжатию
C* − C_{t+1} ≤ (1−σ)(C* − C_t); индукцией
C* − C_t ≤ (1−σ)^t·(C* − C₀). -/
theorem pl_gap_geometric (C : ℕ → ℝ) (Cstar σ : ℝ)
    (hσ1 : σ ≤ 1)
    (hpl_lo : ∀ t, C t + σ * (Cstar - C t) ≤ C (t + 1))
    (t : ℕ) :
    Cstar - C t ≤ (1 - σ) ^ t * (Cstar - C 0) :=
  Hagi.Foundations.recurrence_pure (1 - σ)
    (fun s => Cstar - C s) t (show (0:ℝ) ≤ 1 - σ by linarith)
    (fun s _ => by
      have h := hpl_lo s
      have hE : (1 - σ) * (Cstar - C s)
          = Cstar - C s - σ * (Cstar - C s) := by ring
      linarith [hE])

/-- **Сходимость к ёмкости**: ∀ε>0 ∃T ∀t≥T: C_t ≥ C* − ε.
Конструктивно: телескоп σ(1−σ)^i = (1−σ)^i − (1−σ)^{i+1}
даёт T·σ·(1−σ)^T ≤ 1; архимедовость даёт T с
(C*−C₀)/(σT) < ε. -/
theorem saturation_limit (C : ℕ → ℝ) (Cstar σ : ℝ)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hpl_lo : ∀ t, C t + σ * (Cstar - C t) ≤ C (t + 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ t ≥ T, Cstar - ε ≤ C t := by
  rcases le_or_gt (C 0) Cstar with hgap0 | hgap0
  · -- типичный случай C₀ ≤ C*: телескоп + архимедовость
    have hσ1m : (0:ℝ) ≤ 1 - σ := by linarith
    have hle1 : (1:ℝ) - σ ≤ 1 := by linarith
    -- телескоп: Σ_{i<N} σ(1−σ)^i = 1 − (1−σ)^N ⇒ N·σ·(1−σ)^N ≤ 1
    have htel : ∀ N : ℕ, (N:ℝ) * σ * (1 - σ) ^ N ≤ 1 := by
      intro N
      have hterm : ∀ i, σ * (1 - σ) ^ i
          = (1 - σ) ^ i - (1 - σ) ^ (i + 1) := by
        intro i
        rw [pow_succ]
        ring
      have h2 : ∑ i ∈ Finset.range N, ((1 - σ) ^ (i + 1) - (1 - σ) ^ i)
          = (1 - σ) ^ N - 1 := by
        exact Finset.sum_range_sub (fun i => (1 - σ) ^ i) N
      have hsum : ∑ i ∈ Finset.range N, (σ * (1 - σ) ^ i)
          = 1 - (1 - σ) ^ N := by
        have h5 : 1 - (1 - σ) ^ N = -((1 - σ) ^ N - 1) := by ring
        rw [h5, ← h2]
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by
          rw [hterm i]
          ring)
      have hlow : ∑ i ∈ Finset.range N, σ * (1 - σ) ^ N
          ≤ ∑ i ∈ Finset.range N, σ * (1 - σ) ^ i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hσ1m hle1
            (Finset.mem_range.mp hi).le) hσ0.le
      have hcard : ∑ _i ∈ Finset.range N, σ * (1 - σ) ^ N
          = (N:ℝ) * (σ * (1 - σ) ^ N) := by
        rw [Finset.sum_const, Finset.card_range]

        ring
      -- N·σ·(1−σ)^N ≤ Σ = 1 − (1−σ)^N ≤ 1
      have hsumle : ∑ i ∈ Finset.range N, σ * (1 - σ) ^ i ≤ 1 := by
        have h6 : ∑ i ∈ Finset.range N, σ * (1 - σ) ^ i
            = 1 - (1 - σ) ^ N := hsum
        have h7 : (0:ℝ) ≤ (1 - σ) ^ N := pow_nonneg hσ1m N
        linarith
      linarith [hcard ▸ hlow, hsumle]
    -- финал: выбор W по архимедовости
    obtain ⟨W, hW⟩ := exists_nat_gt ((Cstar - C 0) / (σ * ε))
    have hpos : (0:ℝ) < σ * ε := mul_pos hσ0 hε
    rw [div_lt_iff₀ hpos] at hW
    have hWnn : (0:ℝ) ≤ (W:ℝ) := Nat.cast_nonneg W
    refine ⟨W + 1, fun t ht => ?_⟩
    have hb := pl_gap_geometric C Cstar σ hσ1 hpl_lo t
    have hpowt : (1 - σ) ^ t ≤ (1 - σ) ^ (W + 1) :=
      pow_le_pow_of_le_one hσ1m hle1 ht
    have hgap0nn : (0:ℝ) ≤ Cstar - C 0 := by linarith
    have hfinal : (1 - σ) ^ t * (Cstar - C 0) ≤ ε := by
      have hP : (0:ℝ) ≤ (1 - σ) ^ (W + 1) :=
        pow_nonneg hσ1m (W + 1)
      set P := (1 - σ) ^ (W + 1) with hPdef
      -- шаг 1: P·gap ≤ P·W·σε (нестрого: при σ=1 P=0 и всё тривиально)
      have h1 : P * (Cstar - C 0) ≤ P * ((W:ℝ) * (σ * ε)) :=
        mul_le_mul_of_nonneg_left hW.le hP
      -- шаг 2: P·W·σ ≤ 1 из телескопа (W ≤ W+1)
      have hsp : (0:ℝ) ≤ σ * P := mul_nonneg hσ0.le hP
      have hringW : ((W:ℝ) + 1) * σ * P
          = (W:ℝ) * σ * P + σ * P := by ring
      have hcast : ((W + 1 : ℕ) : ℝ) = (W:ℝ) + 1 := by push_cast; ring
      have h7 : ((W:ℝ) + 1) * σ * P ≤ 1 := by
        have h8 := htel (W + 1)
        rw [← hcast]
        exact h8
      have h6 : (W:ℝ) * σ * P ≤ ((W:ℝ) + 1) * σ * P := by linarith
      -- шаг 3: P·W·σε = (P·W·σ)·ε ≤ ε
      have h2 : P * ((W:ℝ) * (σ * ε)) ≤ ε := by
        have h5 : P * ((W:ℝ) * (σ * ε)) = ((W:ℝ) * σ * P) * ε := by ring
        rw [h5]
        simpa using mul_le_mul_of_nonneg_right (le_trans h6 h7) hε.le
      -- шаг 4: (1−σ)^t ≤ P, gap ≥ 0
      have h9 : (1 - σ) ^ t * (Cstar - C 0) ≤ P * (Cstar - C 0) :=
        mul_le_mul_of_nonneg_right hpowt hgap0nn
      linarith
    linarith
  · -- C* < C₀: индуктивно C_t ≥ C* всегда
    have hall : ∀ t : ℕ, Cstar ≤ C t := by
      intro t
      induction t with
      | zero => linarith
      | succ t ih =>
          have h := hpl_lo t
          have hring : C t + σ * (Cstar - C t)
              = Cstar + (1 - σ) * (C t - Cstar) := by ring
          have hX : (0:ℝ) ≤ (1 - σ) * (C t - Cstar) := by
            have hσ1m : (0:ℝ) ≤ 1 - σ := by linarith
            exact mul_nonneg hσ1m (by linarith)
          rw [hring] at h
          linarith
    exact ⟨0, fun t _ => by have := hall t; linarith⟩

/-- **Нижняя граница зазора**: верхняя PL-форма
C_{t+1} ≤ C_t + σ(C*−C_t) даёт (чистая алгебра)
C* − C_{t+1} ≥ (1−σ)(C* − C_t); индукцией при C₀ ≤ C*

  (1−σ)^t·(C* − C₀) ≤ C* − C_t

— верхняя граница полосы роста (не быстрее логистики). -/
theorem pl_gap_geometric_lo (C : ℕ → ℝ) (Cstar σ : ℝ)
    (hσ1 : σ ≤ 1)
    (hpl_up : ∀ t, C (t + 1) ≤ C t + σ * (Cstar - C t))
    (hC0 : C 0 ≤ Cstar) (t : ℕ) :
    (1 - σ) ^ t * (Cstar - C 0) ≤ Cstar - C t := by
  have hσ1m : (0:ℝ) ≤ 1 - σ := by linarith
  induction t with
  | zero => simp
  | succ t ih =>
      have h := hpl_up t
      have hE : (1 - σ) * (Cstar - C t)
          = Cstar - C t - σ * (Cstar - C t) := by ring
      have hstep : (1 - σ) * (Cstar - C t) ≤ Cstar - C (t + 1) := by
        linarith [hE]
      have hcast : (1 - σ) ^ (t + 1) = (1 - σ) ^ t * (1 - σ) := by ring
      rw [hcast]
      calc (1 - σ) ^ t * (1 - σ) * (Cstar - C 0)
          = (1 - σ) * ((1 - σ) ^ t * (Cstar - C 0)) := by ring
        _ ≤ (1 - σ) * (Cstar - C t) :=
            mul_le_mul_of_nonneg_left ih hσ1m
        _ ≤ Cstar - C (t + 1) := hstep

/-- **Двусторонняя полоса роста с насыщением**: нижняя
граница — ratio-взлёт `ratio_takeoff` (экспонента, ГАРАНТИЯ
роста), верхняя — PL-окно (ёмкость, физический предел):

  C₀·(1+γk)^T ≤ C_T ≤ C* − (1−σ)^T·(C* − C₀).

Посылки обоих законов — пошаговые измеряемые сертификаты
(конус r ≥ k; PL-окно), поэтому полоса заявляется на том
горизонте T, где оба выполняются. Экспонента взлёта наконец
сопоставлена с ограниченной метрикой. -/
theorem takeoff_with_saturation (C D : ℕ → ℝ)
    (γ k Cstar σ : ℝ)
    (hγ : 0 < γ) (hk : 0 < k) (hσ1 : σ ≤ 1)
    (hstep : ∀ t, C (t + 1) = C t + γ * D t)
    (hpl_up : ∀ t, C (t + 1) ≤ C t + σ * (Cstar - C t))
    (hpl_lo : ∀ t, C t + σ * (Cstar - C t) ≤ C (t + 1))
    (hcone : ConeRatio C D k)
    (hC0 : C 0 ≤ Cstar) (T : ℕ) :
    C 0 * (1 + γ * k) ^ T ≤ C T
      ∧ C T ≤ Cstar - (1 - σ) ^ T * (Cstar - C 0) := by
  refine ⟨ratio_takeoff C D γ k hγ hk hstep hcone T, ?_⟩
  linarith [pl_gap_geometric_lo C Cstar σ hσ1 hpl_up hC0 T]

end Hagi
