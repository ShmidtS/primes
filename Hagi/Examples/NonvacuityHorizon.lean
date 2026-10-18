/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.ArchitectureTheorem
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
