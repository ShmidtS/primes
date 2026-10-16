/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

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

end Hagi.Foundations
