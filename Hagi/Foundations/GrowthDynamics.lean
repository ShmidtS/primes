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
end Hagi.Foundations
