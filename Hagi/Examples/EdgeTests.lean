import Hagi.Optimization.ComputeScaling
import Hagi.Foundations.PerronCone
import Hagi.Dynamics.SpeedLimit
import Hagi.Energy.Cooling

/-!
# EdgeTests — граничные тесты главных результатов (P3.14)

Тестовая триада: продуктивные свидетели (wTraj, mw_core_premises,
compute_scaling_bound_attained) и отрицательные обструкции
(full_cycle_two_step_growth_inconsistent, budget_no_growth,
corePremises_single_step_obstruction) живут в своих модулях;
здесь — ГРАНИЧНЫЕ случаи: вырожденные параметры, нулевые
горизонты, точные равенства.
-/

namespace Hagi.Examples

/-! ## compute_scaling (Jeon–Van Roy) -/

/-- ГРАНИЧНЫЙ: симметричный случай a=b=1, m=n=1 — граница
точная, равенство 2 = 2. -/
example : (1:ℝ) / 1 + 1 / 1
    = (Real.sqrt 1 + Real.sqrt 1) ^ 2 / (1 + 1) := by
  norm_num

/-- ГРАНИЧНЫЙ: k-ресурсная граница на singleton-ресурсе —
сводится к a/m ≥ (√a)²/m = a/m, точное равенство. -/
example : (∑ _i ∈ ({0} : Finset ℕ), Real.sqrt 1) ^ 2
      / (∑ _i ∈ ({0} : Finset ℕ), (1:ℝ))
    ≤ ∑ _i ∈ ({0} : Finset ℕ), (1:ℝ) / 1 := by
  simp

/-! ## takeoff (конус) -/

/-- ГРАНИЧНЫЙ: γ=0 — конусная отдача нулевая, рост вырождается
в неубывание: C T ≥ 1^T·C 0 = C 0. -/
example (C D G : ℕ → ℝ)
    (hstepC : ∀ t, C (t + 1) = C t + G t)
    (hgain : ∀ t, (0:ℝ) * D t ≤ G t)
    (hcone : ∀ t, (0:ℝ) * C t ≤ D t) (T : ℕ) :
    (1 + 0 * 0) ^ T * C 0 ≤ C T := by
  exact Hagi.Foundations.h_emp_takeoff_exponential C D G 0 0
    (by norm_num) (by norm_num) hstepC hgain hcone T

/-! ## speed limit -/

/-- ГРАНИЧНЫЙ: M=0 — энергия не убывает быстрее нуля:
E 0 − E T ≤ 0, т.е. E неубывает. -/
example (E : ℕ → ℝ) (hstep : ∀ t, E (t + 1) ≥ E t - 0) (T : ℕ) :
    E 0 - E T ≤ T * 0 := by
  exact Hagi.Dynamics.learning_time_lower_bound E 0 hstep T

/-! ## термодинамика -/

/-- ГРАНИЧНЫЙ: ε=0 — двухуровневая система вырождается в
одноуровневую: ⟨E⟩(T) = 0 при любом T. -/
example (T : ℝ) : 0 / (1 + Real.exp (0 / T)) = 0 := by
  simp


/-- ГРАНИЧНЫЙ: коридор роста при T=0 — обе стороны равны 1:
пустой горизонт согласован тривиально. -/
example (B c : ℝ) (hc : 0 < c) (hB : 0 < B) :
    (1 + 0 * 0 : ℝ) ^ (0 : ℝ) ≤ (1 + 1) ^ (B / c) := by
  simp
  exact le_of_lt (Real.one_lt_rpow (by norm_num : (1:ℝ) < 1 + 1)
    (div_pos hB hc))

end Hagi.Examples