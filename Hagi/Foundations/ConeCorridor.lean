import Hagi.Foundations.PerronCone

/-!
# ConeSystem-коридор (шаг 4 аудита v5, ядро)

Консолидация: через ЕДИНУЮ структуру GrowthDynamics —
двусторонняя оценка: если конусные посылки дают takeoff
(нижняя), а окно роста — cap (верхняя), то capability
зажат ТОЧНОЙ экспонентой: (1+α)^T·C0 ≤ C T ≤ (1+α)^T·C0.
-/

namespace Hagi.Foundations

/-- ТОЧНАЯ ЭКСПОНЕНТА КОНУСА: при конусных посылках
(GrowthDynamics) и cap-окне (C(t+1) ≤ (1+α)·C t) рост
 capability — ровно (1+α)^T·C0: нижняя граница из конуса,
 верхняя — индукция по cap. -/
theorem cone_exact_exponential (C G D : ℕ → ℝ) (xi : ℕ → ℝ)
    (alpha gamma rho beta : ℝ) (T : ℕ)
    (hα : 0 ≤ alpha) (hγ : 0 < gamma) (hρ : 0 ≤ rho)
    (hCpos : ∀ t, 0 < C t)
    (hcone0 : alpha / gamma * C 0 ≤ D 0)
    (hcap : ∀ t, C (t + 1) ≤ (1 + alpha) * C t)
    (hdyn : ∀ t, rho * D t + beta * C t - xi t ≤ D (t + 1))
    (hbeta : ∀ t, alpha / gamma * ((1 + alpha) - rho)
      + xi t / C t ≤ beta)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hgain : ∀ t, gamma * D t ≤ G t) :
    (1 + alpha) ^ T * C 0 ≤ C T
      ∧ C T ≤ (1 + alpha) ^ T * C 0 := by
  constructor
  · -- нижняя: конусная динамика (существующий капстоун)
    exact trunc_premises_takeoff C D G xi alpha gamma rho beta
      hα hγ hρ hCpos hcone0 hcap hdyn hbeta hstep hgain T
  · -- верхняя: индукция по cap
    have hmain : ∀ n : ℕ, n ≤ T →
        C n ≤ (1 + alpha) ^ n * C 0 := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have hc := hcap n
        have ih' := ih (by omega)
        calc C (n + 1) ≤ (1 + alpha) * C n := hc
          _ ≤ (1 + alpha) * ((1 + alpha) ^ n * C 0) :=
              mul_le_mul_of_nonneg_left ih' (by linarith)
          _ = (1 + alpha) ^ (n + 1) * C 0 := by ring
    exact hmain T (le_refl _)

end Hagi.Foundations
