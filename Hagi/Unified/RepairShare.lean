/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# RepairShare — правило `∝ √Δ` распределения байтов ремонта не minimax

`_repair_bytes` (unified.py): доля старых байтов домена `∝ √Δ`, `Δ` — прирост
CE. Модель: остаток домена после доли бюджета `x` — `Δ·(1 − c√x)` (убывающая
отдача). Minimax-оптимум выравнивает остатки: `Δ₁(1 − c√x₁) = Δ₂(1 − c√x₂)`.

* `resid c Δ x = Δ·(1 − c√x)`;
* `sqrt_share_not_minimax` — контрпример `Δ₁ = 4`, `Δ₂ = 1`, `c = 1/2`:
  правило `√Δ` даёт `x₁ = 2/3`, остатки `≠` — правило не является minimax.
  Minimax здесь требует `x₁ = 1` (весь бюджет — худшему домену);
* `share c Δ r = (1 − r/Δ)₊²/c²` — доля домена при целевом остатке `r`
  (водонапорение: `Δᵢ(1 − c√xᵢ) = r` ⇔ `xᵢ = share c Δᵢ r`);
* `share_mono`, `share_sum_mono` — сумма долей не возрастает по `r`;
* `share_sum_zero` — `F 0 = n/c²`;
* `share_strict_of_neg` — при `r < 0` доля строго больше (поэтому `r ≥ 0`);
* `water_filling_exists` — при `F(m) ≤ 1 ≤ F(0)` (`m = min Δ`) найдётся
  `r ∈ [0, m]` с `∑ share = 1`: budget splits exist and are non-negative.
-/

namespace Hagi.Unified.RepairShare

/-- Остаток прироста CE домена после доли бюджета `x`: `Δ·(1 − c·√x)`. -/
noncomputable def resid (c Δ x : ℝ) : ℝ := Δ * (1 - c * Real.sqrt x)
/-- Правило `∝ √Δ` (`Δ₁ = 4`, `Δ₂ = 1` ⇒ `x₁ = 2/3`) не выравнивает остатки
на двух доменах при `c = 1/2`: `resid 4 (2/3) ≠ resid 1 (1/3)` — правило не
является minimax-оптимумом для `g(x) = c√x` (равные остатки ⇔ оптимально). -/
theorem sqrt_share_not_minimax :
    resid (1/2) 4 (2/3) ≠ resid (1/2) 1 (1 - 2/3) := by
  have hs1 : Real.sqrt (2/3) ^ 2 = 2/3 := Real.sq_sqrt (by norm_num)
  have hs2 : Real.sqrt (1/3) ^ 2 = 1/3 := Real.sq_sqrt (by norm_num)
  have hpos1 : 0 < Real.sqrt (2/3) := Real.sqrt_pos.2 (by norm_num)
  have hpos2 : 0 < Real.sqrt (1/3) := Real.sqrt_pos.2 (by norm_num)
  unfold resid
  simp only [one_div]
  intro h
  have hs1' : Real.sqrt (2/3) = 2 * Real.sqrt (2/3) / 2 := by ring
  have hsq : (2 * Real.sqrt (2/3) - Real.sqrt (1/3) / 2) ^ 2 = 9 := by
    have : 2 * Real.sqrt (2/3) - Real.sqrt (1/3) / 2 = 3 := by linarith [h]
    rw [this]; norm_num
  have hpos : 0 < 2 * Real.sqrt (2/3) - Real.sqrt (1/3) / 2 := by
    have : 2 * Real.sqrt (2/3) - Real.sqrt (1/3) / 2 = 3 := by linarith [h]
    rw [this]; norm_num
  have hprod : 0 ≤ Real.sqrt (2/3) * Real.sqrt (1/3) := mul_nonneg hpos1.le hpos2.le
  nlinarith

/-- Доля бюджета домена с приростом `Δ` при целевом остатке `r`: `x = (1 − r/Δ)₊²/c²`;
домены с `Δ ≤ r` получают ноль. -/
noncomputable def share (c Δ r : ℝ) : ℝ := max 0 (1 - r / Δ) ^ 2 / c ^ 2
/-- Доля домена не возрастает по целевому остатку. -/
theorem share_mono (c : ℝ) (Δ : ℝ) (hΔ : 0 < Δ) (r₁ r₂ : ℝ) (h : r₁ ≤ r₂) :
    share c Δ r₂ ≤ share c Δ r₁ := by
  unfold share
  gcongr
/-- Сумма долей — не возрастает по целевому остатку `r`. -/
theorem share_sum_mono (c : ℝ) (Δ : ℕ → ℝ) (hΔ : ∀ i, 0 < Δ i)
    (r₁ r₂ : ℝ) (h : r₁ ≤ r₂) (n : ℕ) :
    ∑ i ∈ Finset.range n, share c (Δ i) r₂ ≤ ∑ i ∈ Finset.range n, share c (Δ i) r₁ :=
  Finset.sum_le_sum fun i _ => share_mono c (Δ i) (hΔ i) r₁ r₂ h
/-- При `r = 0` сумма долей равна числу доменов, делённому на `c²`. -/
theorem share_sum_zero (c : ℝ) (Δ : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, share c (Δ i) 0 = n / c ^ 2 := by
  have h1 : ∀ i ∈ Finset.range n, share c (Δ i) 0 = 1 / c ^ 2 := by
    intro i _
    unfold share
    rw [zero_div, sub_zero, max_eq_right (by norm_num : (0:ℝ) ≤ 1), one_pow]
  rw [Finset.sum_congr rfl h1]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  ring
/-- Доля строго больше при отрицательном остатке (`r < 0`). -/
theorem share_strict_of_neg (c : ℝ) (hc : 0 < c) (Δ : ℝ) (hΔ : 0 < Δ) (r : ℝ) (hr : r < 0) :
    share c Δ 0 < share c Δ r := by
  unfold share
  rw [zero_div, sub_zero, max_eq_right (by norm_num : (0:ℝ) ≤ 1), one_pow]
  apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hc)).2
  have hrn : r / Δ < 0 := div_neg_of_neg_of_pos hr hΔ
  have hlt1 : (1:ℝ) < 1 - r / Δ := by linarith
  have hpos : 0 < 1 - r / Δ := by linarith
  rw [max_eq_right hpos.le]
  nlinarith [mul_pos hpos hpos, sq_pos_of_pos hpos]
/-- Water-filling: если `F(m) ≤ 1 ≤ F(0)`, найдётся целевой остаток `r ∈ [0, m]`
с `∑ share = 1` — доли бюджета в сумме единица (`m = min Δ` даёт каждый домен
неотрицательную долю, т.к. `r ≤ m ≤ Δ i`). -/
theorem water_filling_exists (c : ℝ) (Δ : ℕ → ℝ) (n : ℕ) (m : ℝ) (hm0 : 0 ≤ m)
    (hlo : ∑ i ∈ Finset.range n, share c (Δ i) m ≤ 1) (hhi : 1 ≤ ∑ i ∈ Finset.range n, share c (Δ i) 0) :
    ∃ r, 0 ≤ r ∧ r ≤ m ∧ ∑ i ∈ Finset.range n, share c (Δ i) r = 1 := by
  classical
  set F : ℝ → ℝ := fun r => ∑ i ∈ Finset.range n, share c (Δ i) r with hF
  have hFcont : Continuous F := by
    rw [hF]
    simp only [share]
    fun_prop
  have h0m : 0 ≤ m := hm0
  have hlo' : F m ≤ 1 := hlo
  have hhi' : (1:ℝ) ≤ F 0 := hhi
  obtain ⟨r, hrm, hrF⟩ :=
    isPreconnected_Icc.intermediate_value (Set.mem_Icc.2 ⟨h0m, le_rfl⟩)
      (Set.mem_Icc.2 ⟨le_rfl, h0m⟩) hFcont.continuousOn
      (Set.mem_Icc.2 ⟨hlo', hhi'⟩)
  refine ⟨r, hrm.1, hrm.2, ?_⟩
  exact hrF

end Hagi.Unified.RepairShare
