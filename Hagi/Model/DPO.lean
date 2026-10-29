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

/-- Bradley-Terry sigmoid-link: вероятность предпочтения
y1 > y2 по разности наград. -/
noncomputable def btPref (r1 r2 : ℝ) : ℝ :=
  1 / (1 + Real.exp (-(r1 - r2)))

/-- УРОВЕНЬ 2 No31: предпочтение монотонно по награде —
p(y1 > y2) > 1/2 ⟺ r1 > r2 (Bradley-Terry link корректно
кодирует порядок наград). -/
theorem bt_pref_iff (r1 r2 : ℝ) :
    1 / 2 < btPref r1 r2 ↔ r1 > r2 := by
  unfold btPref
  set S := 1 + Real.exp (-(r1 - r2)) with hSdef
  have hSpos : (0:ℝ) < S := by
    have := Real.exp_pos (-(r1 - r2))
    rw [hSdef]
    linarith
  have hkey : (1:ℝ)/2 < (1:ℝ)/S ↔ S < (2:ℝ) := by
    rw [one_div, one_div]
    exact inv_lt_inv₀ (by norm_num : (0:ℝ) < 2) hSpos
  rw [hkey]
  have hexp : Real.exp (-(r1 - r2)) < 1 ↔ -(r1 - r2) < 0 :=
    Real.exp_lt_one_iff
  constructor
  · intro h
    have h1 : Real.exp (-(r1 - r2)) < 1 := by linarith
    have h2 := hexp.mp h1
    linarith
  · intro h
    have hneg : -(r1 - r2) < 0 := by linarith
    have h1 := hexp.mpr hneg
    linarith

end Hagi.Model.DPO
