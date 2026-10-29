import Mathlib

/-!
# DPO: неявная награда и восстановление политики (источник №31)

Источник №31: Rafailov et al., "Direct Preference
Optimization" (arXiv 2305.18290). DPO исключает RL-цикл:
награда выражается напрямую через политику —
r(y|x) = β·ln(π_θ(y|x)/π_ref(y|x)), а оптимальная политика —
болцмановская относительно π_ref: π ∝ π_ref·exp(r/β).

Формализованное ядро (строгое, дискретно на Fin n):
- `dpoReward`: r i = β·(ln π i − ln π_ref i);
- `boltzmann_from_reward`: если r задан формулой DPO, то
  π i = π_ref i · exp(r i / β) — политика восстанавливается
  из награды без нормировки;
- `boltzmann_norm`: если π и π_ref — вероятностные
  распределения (суммы = 1, строго положительные), то
  статистическая сумма Z = ∑ π_ref·exp(r/β) равна 1 —
  болцмановская реконструкция АВТОМАТИЧЕСКИ нормирована.
-/

namespace Hagi.Model.DPO

open Real Finset

variable {n : ℕ}

/-- Неявная награда DPO: β·(ln π − ln π_ref). -/
noncomputable def dpoReward (β : ℝ) (pi pref : Fin n → ℝ)
    (i : Fin n) : ℝ := β * (log (pi i) - log (pref i))

/-- Из награды DPO политика восстанавливается точным
болцмановским множителем (без нормировки). -/
theorem boltzmann_from_reward {β : ℝ} (hβ : β ≠ 0)
    (pi pref : Fin n → ℝ) (hpi : ∀ i, 0 < pi i)
    (hpref : ∀ i, 0 < pref i) (i : Fin n) :
    pi i = pref i * Real.exp (dpoReward β pi pref i / β) := by
  unfold dpoReward
  rw [mul_div_cancel_left₀ _ hβ]
  rw [Real.exp_sub (Real.log (pi i)) (Real.log (pref i)),
    Real.exp_log (hpi i), Real.exp_log (hpref i)]
  rw [mul_div_cancel₀ (pi i) (ne_of_gt (hpref i))]

/-- Болцмановская реконструкция автоматически нормирована:
если π и π_ref — распределения, то Z = 1. -/
theorem boltzmann_norm {β : ℝ} (hβ : β ≠ 0)
    (pi pref : Fin n → ℝ)
    (hpi : ∀ i, 0 < pi i) (hpref : ∀ i, 0 < pref i)
    (hsumP : ∑ i, pi i = 1) :
    ∑ i, pref i * Real.exp (dpoReward β pi pref i / β) = 1 := by
  have h : ∀ i ∈ Finset.univ,
      pref i * Real.exp (dpoReward β pi pref i / β) = pi i :=
    fun i _ => (boltzmann_from_reward hβ pi pref hpi hpref i).symm
  rw [Finset.sum_congr rfl h]
  exact hsumP

end Hagi.Model.DPO
