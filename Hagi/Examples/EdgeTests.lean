import Hagi.Optimization.ComputeScaling
import Hagi.Foundations.PerronCone
import Hagi.Dynamics.SpeedLimit
import Hagi.Energy.Cooling
import Hagi.Optimization.PLConvergence
import Hagi.Pretraining.RobustnessLaw

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


/-! ## PL-сходимость -/

/-- ГРАНИЧНЫЙ: μ=L — скорость обнуляется (1−μ/L = 0): за один
шаг: (1−μ/L) = 0 ⟹ E t − E* ≤ 0^t·(E 0−E*) — вырожденный
случай факторизации скорости. -/
example (E G : ℕ → ℝ) (Estar L : ℝ) (hL : 0 < L)
    (hE : ∀ t, Estar ≤ E t)
    (hstep : ∀ t, E (t + 1) ≤ E t - G t / (2 * L))
    (hPL : ∀ t, 2 * L * (E t - Estar) ≤ G t) (t : ℕ) :
    E t - Estar ≤ (0:ℝ) ^ t * (E 0 - Estar) := by
  have h0 : (1:ℝ) - L / L = 0 := by
    rw [div_self (ne_of_gt hL), sub_self]
  have h := Hagi.Optimization.pl_linear_convergence E G Estar L L hL hL
    (le_refl _) hE hstep hPL t
  rwa [h0] at h

/-- ГРАНИЧНЫЙ: ε-горизонт при t=0 — достаточность тривиальна:
(1−μ/L)^0·(E 0−E*) = E 0−E* ≤ ε требуется явно (никакого
бесплатного спуска). -/
example (E G : ℕ → ℝ) (Estar μ L ε : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hμL : μ ≤ L) (hE : ∀ t, Estar ≤ E t)
    (hstep : ∀ t, E (t + 1) ≤ E t - G t / (2 * L))
    (hPL : ∀ t, 2 * μ * (E t - Estar) ≤ G t)
    (hε : (E 0 - Estar) ≤ ε) :
    E 0 - Estar ≤ ε :=
  Hagi.Optimization.pl_sufficient_horizon E G Estar μ L ε hL hμ hμL
    hE hstep hPL 0 (by simpa using hε)

/-- ГРАНИЦА 1 (достижимость): f(x)=x — 1-липшицев
интерполятор данных (0→0, 1→1); граница |Δy| ≤ L|Δx|
достигается с L=1. -/
example : |(1:ℝ) - 0| ≤ 1 * |(1:ℝ) - 0| := by
  have h := Hagi.Pretraining.robust_interpolation_lipschitz_floor
    (fun t => t) (fun i => (i : ℝ)) (fun i => (i : ℝ)) 2 1
    (by intro i hi; interval_cases i <;> norm_num)
    (by intro a b; simp) 0 (by norm_num)
  norm_num [h]

/-- ГРАНИЦА 2 (несовместимость): уклон 2 на шаге 1/2
требует L ≥ 4 — L=1 интерполятор НЕ существует. -/
example (f : ℝ → ℝ) (h0 : f 0 = 0) (h1 : f (1 / 2) = 2)
    (hlip : ∀ a b, |f a - f b| ≤ 1 * |a - b|) : False :=
  Hagi.Pretraining.no_lipschitz_interpolator_of_steep f
    (fun i => (i : ℝ) * (1 / 2)) (fun i => if i = 0 then 0 else 2)
    2 0 1 (by norm_num)
    (by intro i hi; interval_cases i
        · simp [h0]
        · simpa using h1)
    hlip (by norm_num)

/-- ГРАНИЦА 3 (step cap): σ = δ = 1, стабильность η·1 ≤ 1
даёт η ≤ 1. -/
example (η : ℝ) (hη : 0 ≤ η) (hstab : η * 1 ≤ 1) : η ≤ 1 := by
  have h := Hagi.Pretraining.noisy_interpolation_step_cap
    (fun t => t) (fun i => (i : ℝ))
    (fun i => if i = 0 then 0 else 1) 2 0 1 1 1 η
    (by norm_num) (by norm_num) (by norm_num) hη
    (by intro i hi; interval_cases i <;> simp)
    (by intro a b; exact le_of_eq (by ring))
    (by norm_num) (by norm_num) hstab
  simpa using h

end Hagi.Examples