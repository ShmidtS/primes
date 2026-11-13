/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Legacy.ArchitectureTheorem
import Hagi.Optimization.ComputeScaling
import Hagi.Growth.LinearCone
import Hagi.Dynamics.Laws
import Hagi.Optimization.PLConvergence
import Hagi.Pretraining.RobustnessLaw
set_option linter.style.header false

/-!
# Параметрические nonvacuity-свидетели ↔ cert_horizon_bound
(R531)

Закрытие открытого пункта STATUS «параметрические
nonvacuity-свидетели ↔ cert_horizon_bound (связать свидетель
с горизонтом)»: семейство траекторий насыщения
`C t = Cstar − Δ(1−σ)^t`, `F t = σΔ(1−σ)^t/γ` реализует
посылки `cert_horizon_bound` на произвольном горизонте T,
совместимом с геометрическим условием конуса
`γk·Cstar ≤ (γk+σ)Δ(1−σ)^t` (t < T). Максимальный T —
наибольшее, на котором конус ещё держится: witness-горизонт
совпадает с горизонтом границы. При T = 1 условие вырождается
в `C 0 ≤ σCstar/(γk+σ)` — параметрическое обобщение
`cert_horizon_witness`.
-/

namespace Hagi.Examples

open Real

/-- Семейство траекторий насыщения: capability. -/
noncomputable def satC (Cstar Δ σ : ℝ) (t : ℕ) : ℝ :=
  Cstar - Δ * (1 - σ) ^ t

/-- Семейство траекторий насыщения: usable frontier. -/
noncomputable def satF (Cstar Δ σ γ : ℝ) (t : ℕ) : ℝ :=
  σ * Δ * (1 - σ) ^ t / γ

/-- Оба шага семейства: точный шаг C' = C + γF и точное
насыщение C' = C + σ(Cstar − C) выполняются тождественно. -/
theorem sat_step_laws (Cstar Δ σ γ : ℝ) (hγ : γ ≠ 0) (t : ℕ) :
    satC Cstar Δ σ (t + 1) = satC Cstar Δ σ t + γ * satF Cstar Δ σ γ t
      ∧ satC Cstar Δ σ (t + 1)
        = satC Cstar Δ σ t + σ * (Cstar - satC Cstar Δ σ t) := by
  constructor <;> simp only [satC, satF] <;>
    (rw [pow_succ]; field_simp; ring)

/-- Конус для семейства — геометрическое условие:
k·C t ≤ F t ⟺ γk·Cstar ≤ (γk+σ)·Δ·(1−σ)^t. -/
theorem sat_cone_iff (γ k σ Cstar Δ : ℝ) (hγ : 0 < γ) (t : ℕ) :
    k * satC Cstar Δ σ t ≤ satF Cstar Δ σ γ t
      ↔ γ * k * Cstar ≤ (γ * k + σ) * Δ * (1 - σ) ^ t := by
  simp only [satC, satF]
  rw [le_div_iff₀ hγ]
  constructor
  · intro h
    nlinarith [mul_mul_mul_comm γ k (Δ * (1 - σ) ^ t),
      mul_mul_mul_comm γ k Cstar, mul_comm (k * (Cstar - Δ * (1 - σ) ^ t)) γ]
  · intro h
    nlinarith [mul_mul_mul_comm γ k (Δ * (1 - σ) ^ t),
      mul_mul_mul_comm γ k Cstar, mul_comm (k * (Cstar - Δ * (1 - σ) ^ t)) γ]

/-- **Параметрический witness горизонтальной длины (R531)**:
при геометрической совместимости конуса на всём t < T
семейство насыщения удовлетворяет ВСЕМ посылкам
`cert_horizon_bound` на горизонте T и даёт честный рост
`C 0 < C T` — связывает nonvacuity-свидетель с горизонтом:
любой конус-совместимый T достижим свидетелем, и на нём
справедлива граница `(1+γk)^(T−1) ≤ σCstar/((γk+σ)C0)`. -/
theorem witness_achieves_horizon (γ k σ Cstar C0 : ℝ) (T : ℕ)
    (hγ : 0 < γ) (hk : 0 < k) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hCstar : 0 < Cstar) (hC0 : 0 < C0) (hC0C : C0 < Cstar)
    (hT1 : 1 ≤ T)
    (hgeo : ∀ t < T,
      γ * k * Cstar ≤ (γ * k + σ) * (Cstar - C0) * (1 - σ) ^ t) :
    -- посылки cert_horizon_bound для семейства
    (∀ t < T, satC Cstar (Cstar - C0) σ (t + 1)
        = satC Cstar (Cstar - C0) σ t
          + γ * satF Cstar (Cstar - C0) σ γ t)
      ∧ (∀ t < T, satC Cstar (Cstar - C0) σ (t + 1)
        = satC Cstar (Cstar - C0) σ t
          + σ * (Cstar - satC Cstar (Cstar - C0) σ t))
      ∧ (∀ t < T, k * satC Cstar (Cstar - C0) σ t
        ≤ satF Cstar (Cstar - C0) σ γ t)
      ∧ satC Cstar (Cstar - C0) σ 0
        < satC Cstar (Cstar - C0) σ T := by
  have hstep := fun t (ht : t < T) =>
    (sat_step_laws Cstar (Cstar - C0) σ γ hγ.ne' t).1
  have hpl := fun t (ht : t < T) =>
    (sat_step_laws Cstar (Cstar - C0) σ γ hγ.ne' t).2
  have hcone := fun t (ht : t < T) =>
    (sat_cone_iff γ k σ Cstar (Cstar - C0) hγ t).mpr (hgeo t ht)
  refine ⟨hstep, hpl, hcone, ?_⟩
  -- рост: C 0 = C0, C T = Cstar − Δ(1−σ)^T > C0
  have hΔpos : 0 < Cstar - C0 := by linarith
  have hdecay : (1 - σ) ^ T < 1 := by
    have hle : (1 - σ) ^ (T - 1) ≤ 1 := by
      induction (T - 1) with
      | zero => norm_num
      | succ n ih =>
          have hmul : (1 - σ) ^ (n + 1) = (1 - σ) ^ n * (1 - σ) :=
            pow_succ _ n
          rw [hmul]
          have hb : 0 ≤ 1 - σ := by linarith
          have hb1 : 1 - σ ≤ 1 := by linarith
          have hfin : (1 - σ) ^ n * (1 - σ) ≤ 1 * 1 :=
            mul_le_mul ih hb1 hb (by norm_num)
          nlinarith [hfin]
    have hsplit : (1 - σ) ^ T = (1 - σ) * (1 - σ) ^ (T - 1) := by
      obtain ⟨n, hn⟩ : ∃ n : ℕ, T = n + 1 := ⟨T - 1, by omega⟩
      subst hn
      rw [Nat.add_sub_cancel, pow_succ, mul_comm]
    rw [hsplit]
    nlinarith
  -- цель: C0 < Cstar − Δ·(1−σ)^T, где Δ = Cstar − C0
  have hxs : 0 < (1 - σ) ^ T := by
    have hb : 0 < 1 - σ := by linarith
    exact pow_pos hb T
  have hstrict : (Cstar - C0) * (1 - σ) ^ T < (Cstar - C0) * 1 :=
    mul_lt_mul_of_pos_left hdecay hΔpos
  rw [mul_one] at hstrict
  simp only [satC, pow_zero, mul_one]
  linarith

end Hagi.Examples

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