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

end Hagi.Unified
