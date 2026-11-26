/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# SpikeThreshold — спайк-порог входа как адаптивный масштаб

`HagiOptimalLM._spike` (optimal_lm.py): `h ↦ round(h/V)·V`, STE-градиент,
порог `V = ‖h‖₁/(ширина·k)`, причинный. Тот же механизм, что `EF21Scale`,
но для активаций и с порогом по средней величине.

* `spike_pointwise` — ошибка координаты ≤ `V/2`.
* `spike_mass_ge` — `Σ|spike| ≥ ‖h‖₁ − card·V/2`.
* `spike_mass_ge_adaptive` — при адаптивном пороге сохраняется `≥ 1 − 1/(2k)`
  L1-массы (при `k = 3`: ≥ 83%) независимо от данных.
-/

namespace Hagi.Energy.SpikeThreshold

open Finset

variable {ι : Type*} [Fintype ι]
/-- Спайк-округление: `spike V h = round(h/V)·V` (STE: градиент тождественный). -/
noncomputable def spike (V : ℝ) (h : ι → ℝ) : ι → ℝ := fun i => round (h i / V) * V
/-- Ошибка округления каждой координаты не больше половины порога. -/
theorem spike_pointwise (V : ℝ) (hV : 0 < V) (x : ℝ) : |x - round (x / V) * V| ≤ V / 2 := by
  obtain ⟨h1, h2⟩ := (round_eq_iff (x := x / V) (n := round (x / V))).1 rfl
  have hdiv : (x / V) * V = x := by field_simp
  have hlo : (round (x / V) - 1 / 2) * V ≤ x := by
    have := mul_le_mul_of_nonneg_right h1 hV.le
    nlinarith
  have hhi : x ≤ (round (x / V) + 1 / 2) * V := by
    have := (mul_lt_mul_of_pos_right h2 hV).le
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith
/-- Сохранённая L1-масса: `Σ |spike h i| ≥ ‖h‖₁ − card·V/2`. -/
theorem spike_mass_ge (V : ℝ) (hV : 0 < V) (h : ι → ℝ) :
    ∑ i, |h i| - (Fintype.card ι : ℝ) * V / 2 ≤ ∑ i, |spike V h i| := by
  have h1 : ∀ i, |h i| - V / 2 ≤ |spike V h i| := by
    intro i
    have hp := spike_pointwise V hV (h i)
    have h2 : |h i| - |spike V h i| ≤ |h i - spike V h i| := abs_sub_abs_le_abs_sub _ _
    rw [spike] at h2 ⊢
    have := h2.trans hp
    linarith
  calc ∑ i, |h i| - (Fintype.card ι : ℝ) * V / 2
      = ∑ i, (|h i| - V / 2) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ ∑ i, |spike V h i| := Finset.sum_le_sum fun i _ => h1 i
/-- Адаптивный порог `V = ‖h‖₁/(card·k)`: сохраняется ≥ `1 − 1/(2k)` L1-массы. -/
theorem spike_mass_ge_adaptive (k : ℝ) (hk : 0 < k) (h : ι → ℝ) :
    (1 - 1 / (2 * k)) * ∑ i, |h i| ≤
      ∑ i, |spike ((∑ i, |h i|) / ((Fintype.card ι : ℝ) * k)) h i| := by
  rcases Finset.eq_empty_or_nonempty (univ : Finset ι) with he | hne
  · have : IsEmpty ι := Finset.univ_eq_empty_iff.1 he
    simp
  have hcard : (0:ℝ) < Fintype.card ι := by exact_mod_cast Finset.card_pos.2 hne
  by_cases hz : ∑ i, |h i| = 0
  · have hall : ∀ i, h i = 0 := fun i => (abs_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg (h i)).1 hz i (mem_univ i)))
    simp [spike, hall]
  have hpos : 0 < ∑ i, |h i| := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => abs_nonneg _) (Ne.symm hz)
  have hV : 0 < (∑ i, |h i|) / ((Fintype.card ι : ℝ) * k) := div_pos hpos (mul_pos hcard hk)
  have hb := spike_mass_ge _ hV h
  have hVeq : (Fintype.card ι : ℝ) * ((∑ i, |h i|) / ((Fintype.card ι : ℝ) * k)) / 2 =
      (∑ i, |h i|) / (2 * k) := by field_simp
  rw [hVeq] at hb
  have h1 : (1 - 1 / (2 * k)) * ∑ i, |h i| = ∑ i, |h i| - (∑ i, |h i|) / (2 * k) := by ring
  linarith

end Hagi.Energy.SpikeThreshold
