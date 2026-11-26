/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.EmpiricalBernstein

/-!
# PairedGain — сертифицированный гейт парного выигрыша адаптера

`paired_gain(before, after)` (selfdev/unified.py): `gain = mean(before − after)`,
нижняя граница `gain − 2.4·SE`, приём при `lower > ADAPTER_MIN_GAIN = 0.005`
на не более чем `ADAPTER_VAL_WINDOWS = 4096` окнах.

* `diffX` — парная разность CE «до − после» как приращение;
* `diffX_sum` — сумма по выборке равна сумме разностей;
* `admit_false_le` — если истинный выигрыш нулевой (`∑ q·D = 0`), разности
  ограничены `b` и имеют дисперсию ≤ `sig`, то с вероятностью ≥ `1 − α` гейт
  НЕ принимает: EB-радиус `radius` заменяет эвристику `2.4·SE`.

Правило кода `2.4·SE` — асимптотическая нормальная аппроксимация;
`radius` даёт конечную выборку гарантию при любом `n`.
-/

namespace Hagi.Probability.PairedGain
open Hagi.Probability
variable {V : Type} [Fintype V] [Nonempty V]

open Classical in
/-- Гейт адаптера: принять, если нижняя граница парного выигрыша выше `g₀`. -/
def admit (gain r g₀ : ℝ) : Prop := gain - r > g₀
/-- EB-радиус для `n` парных разностей с диапазоном `b` и дисперсией `sig`. -/
noncomputable def radius (sig b n α : ℝ) : ℝ :=
  Real.sqrt (2 * sig * Real.log (2 / α) / n) + 2 * b * Real.log (2 / α) / n
/-- Приращение на шаге `t+1` — парная разность CE «до − после» на окне. -/
def diffX (D : V → ℝ) : ∀ t, (Fin t → V) → ℝ
  | 0, _ => 0
  | t+1, p => D (p (Fin.last t))
omit [Fintype V] [Nonempty V] in
/-- Сумма парных разностей по выборке — то, что измеряет гейт. -/
theorem diffX_sum (D : V → ℝ) (n : ℕ) (ω : Fin n → V) :
    azumaSum (diffX D) n ω = ∑ i, D (ω i) := by
  induction n with
  | zero => simp [azumaSum]
  | succ k ih =>
    rw [azumaSum, ih]
    simp only [diffX]
    rw [Fin.sum_univ_castSucc]
/-- Гейт адаптера с EB-границей: при нулевой гипотезе (средняя разность 0)
вероятность ложного приёма не выше `α`. -/
theorem admit_false_le (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (D : V → ℝ) (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ v, |D v| ≤ b)
    (sig : ℝ) (hsig : 0 < sig) (hmean : ∑ v, q v * D v = 0)
    (hvar : ∑ v, q v * D v ^ 2 ≤ sig)
    (n : ℕ) (hn : 0 < n) (α : ℝ) (hα : 0 < α) (hα2 : α < 1) (g₀ : ℝ) (hg₀ : 0 ≤ g₀) :
    prodPq (fun _ : Fin n => q)
      (fun ω => ¬ ((∑ i, D (ω i)) / n - radius sig b n α > g₀)) ≥ 1 - α := by
  have hXb : ∀ t pref, |diffX D t pref| ≤ b := by
    intro t pref
    match t, pref with
    | 0, _ => simp [diffX]; exact hb
    | k+1, p => simp [diffX, hbnd]
  have hXm : ∀ t pref, ∑ v, q v * diffX D (t+1) (Fin.snoc pref v) = 0 := by
    intro t pref; simp [diffX, Fin.snoc_last, hmean]
  have hXv : ∀ t pref, ∑ v, q v * diffX D (t+1) (Fin.snoc pref v) ^ 2 ≤ sig := by
    intro t pref; simp [diffX, Fin.snoc_last, hvar]
  have h := empirical_bernstein_mean_bound q hq0 hq1 (diffX D) b hb hXb sig hsig hXm hXv n hn α hα hα2
  simp only [diffX_sum, radius] at h ⊢
  have hmono := prodPq_mono (fun _ : Fin n => q) (fun i => ⟨fun v => hq0 v, hq1⟩)
    (fun ω => |(∑ i, D (ω i)) / n| < radius sig b n α)
    (fun ω => ¬ ((∑ i, D (ω i)) / n - radius sig b n α > g₀)) (by
      intro ω habs hgt
      have hle := (abs_lt.1 habs).2
      linarith)
  exact h.trans hmono

end Hagi.Probability.PairedGain
