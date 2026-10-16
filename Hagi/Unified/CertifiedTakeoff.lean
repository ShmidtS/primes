/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.MasterHAGITrunc
import Hagi.Probability.CertifiedEstimator

/-!
# CertifiedTakeoff — сертифицируемый конус (R554)

Мост «выборочная сертификация → takeoff»: cone0-посылка
(`alpha/gamma·C0 ≤ D0`) вытекает из μ-неравенства средних
(`hbridge`); μ-неравенство сертифицируется по выборке через
`certified_premise` с вероятностью ≥ 1 − 2e^{−2nε²}; на том же
хорошем событии точечно применяется детерминированный
`sustained_takeoff_trunc`. Итог: с тем же уровнем вероятности
верна импликация «измеренный margin → takeoff-граница».
-/

open scoped BigOperators

namespace Hagi.Unified

/-- **Certified cone0 → takeoff (R554)**: с вероятностью
≥ 1 − 2e^{−2nε²} — импликация «измеренный margin → takeoff». -/
theorem certified_cone0_takeoff {n : ℕ} {V : Type}
    [Fintype V] [Nonempty V] (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X Y : Fin n → V → ℝ)
    (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (hY : ∀ i v, 0 ≤ Y i v ∧ Y i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps)
    (C G D : ℕ → ℝ) (D0 : ℝ) (alpha gamma rho beta : ℝ)
    (xi : ℕ → ℝ) (T : ℕ)
    -- мост «μ-неравенство средних → детерминированный cone0»
    (hbridge : ∑ i, coordMean p X i ≤ ∑ i, coordMean p Y i
      → alpha / gamma * C 0 ≤ D 0)
    (hα : 0 < alpha) (hγ : 0 < gamma) (hρ : 0 ≤ rho)
    (hC0 : 0 < C 0)
    (hstep : ∀ t < T, C (t + 1) = C t + G t)
    (hgain : ∀ t < T, gamma * D t ≤ G t)
    (hdyn : ∀ t < T, rho * D t + beta * C t - xi t ≤ D (t + 1))
    (hcap : ∀ t < T, C (t + 1) ≤ (1 + alpha) * C t)
    (hbeta : ∀ t < T,
      alpha / gamma * ((1 + alpha) - rho) + xi t / C t ≤ beta) :
    1 - 2 * Real.exp (- 2 * (n : ℝ) * eps ^ 2)
      ≤ prodPq p (fun ω : Fin n → V =>
        (∑ i, X i (ω i) + 2 * (n : ℝ) * eps ≤ ∑ i, Y i (ω i))
          → C 0 * (1 + alpha) ^ T ≤ C T) := by
  classical
  have hcert := certified_premise p hp X Y hX hY hn eps heps
  refine le_trans hcert (prodPq_mono p hp _ _ ?_)
  intro ω h hmargin
  exact sustained_takeoff_trunc C G D alpha gamma rho beta xi T
    hα hγ hρ hC0 (hbridge (h hmargin)) hstep hgain hdyn hcap hbeta


/-- **Размер выборки из уровня доверия (R558)**: если
n ≥ ln(2T/α)/(2ε²), то экспоненциальный дефект лестницы
2T·e^{−2nε²} ≤ α — замыкающий мост certified-каскада:
сколько измерений нужно, чтобы anytime-уровень R555 был
≥ 1 − α. -/
theorem sample_size_adequate (n T : ℕ) (eps alpha : ℝ)
    (heps : 0 < eps) (hα : 0 < alpha) (hT : 0 < T)
    (hn : Real.log (2 * (T:ℝ) / alpha) / (2 * eps^2) ≤ (n:ℝ)) :
    2 * (T:ℝ) * Real.exp (-2 * (n:ℝ) * eps^2) ≤ alpha := by
  have hTα : 0 < 2 * (T:ℝ) / alpha := by positivity
  have hlog : Real.log (2 * (T:ℝ) / alpha) ≤ 2 * (n:ℝ) * eps^2 := by
    have h1 : (Real.log (2 * (T:ℝ) / alpha)) / (2 * eps^2)
        ≤ (n:ℝ) := hn
    have h2 : 0 < (2:ℝ) * eps^2 := by positivity
    have h3 := (div_le_iff₀ h2).mp h1
    have h4 : (n:ℝ) * (2 * eps^2) = 2 * (n:ℝ) * eps^2 := by ring
    rw [h4] at h3
    exact h3
  -- antitone: e^{−2nε²} ≤ e^{−ln(2T/α)} = α/(2T)
  have hanti : Real.exp (-(2 * (n:ℝ) * eps^2))
      ≤ Real.exp (-(Real.log (2 * (T:ℝ) / alpha))) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hexplog : Real.exp (-(Real.log (2 * (T:ℝ) / alpha)))
      = alpha / (2 * (T:ℝ)) := by
    rw [Real.exp_neg, Real.exp_log hTα]
    field_simp
  rw [hexplog] at hanti
  have h2T : 0 < (2:ℝ) * T := by positivity
  have hmul := mul_le_mul_of_nonneg_left hanti h2T.le
  have hdiv : (2 * (T:ℝ)) * (alpha / (2 * (T:ℝ))) = alpha := by
    field_simp
  rw [hdiv] at hmul
  ring_nf at hmul ⊢
  exact hmul

end Hagi.Unified
