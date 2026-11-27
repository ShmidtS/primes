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
  Minimax здесь требует `x₁ = 1` (весь бюджет — худшему домену).
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

end Hagi.Unified.RepairShare
