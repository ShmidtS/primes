/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# ReplayCompute — вычислительная цена replay-ремонта

`_repair_forgetting` (unified.py): replay-раунд — `train_certified(old_bytes,
epochs=2, batch=64)`; байты ремонта распределяются по доменам пропорционально
`√Δ` (Δ — прирост CE).

* `ceil_le_floor_add_one` — `(old + d − 1)/d ≤ old/d + 1`;
* `replay_steps_le` — шагов за раунд ≤ `epochs·(old/(B·k) + 1)`;
* `replay_steps_total` — за `m` раундов ≤ `m` одинарных;
* `sqrt_share_mono` — доля байтов домена монотонна по приросту CE.
-/

namespace Hagi.Unified.ReplayCompute

/-- `(old + d − 1) / d ≤ old / d + 1` для `d > 0`: ceil-деление не больше
floor-деления плюс один. -/
theorem ceil_le_floor_add_one (old d : ℕ) (hd : 0 < d) :
    (old + d - 1) / d ≤ old / d + 1 := by
  apply (Nat.div_le_iff_le_mul hd).2
  have hdm := Nat.div_add_mod old d
  have hmod : old % d < d := Nat.mod_lt _ hd
  have hr : (old / d + 1) * d = d * (old / d) + d := by ring
  rw [hr]
  omega
/-- Шагов в replay-раунде (epochs проходов по `old` байтам батчами `B·k`):
не более `epochs·(old/(B·k) + 1)`. -/
theorem replay_steps_le (epochs B k old : ℕ) (hB : 0 < B) (hk : 0 < k) :
    epochs * ((old + B * k - 1) / (B * k)) ≤ epochs * (old / (B * k) + 1) :=
  Nat.mul_le_mul_left _ (ceil_le_floor_add_one old (B * k) (mul_pos hB hk))
/-- Суммарно за `m` раундов — не более `m` одинарных. -/
theorem replay_steps_total (epochs B k old m : ℕ) (hB : 0 < B) (hk : 0 < k) :
    m * (epochs * ((old + B * k - 1) / (B * k))) ≤ m * (epochs * (old / (B * k) + 1)) :=
  Nat.mul_le_mul_left _ (replay_steps_le epochs B k old hB hk)
/-- Доля байтов ремонта домена `∝ √Δ` (Δ — прирост CE): монотонна по Δ. -/
theorem sqrt_share_mono (Δ₁ Δ₂ : ℝ) (h : Δ₁ ≤ Δ₂) (h2 : 0 ≤ Δ₁) :
    Real.sqrt Δ₁ ≤ Real.sqrt Δ₂ := Real.sqrt_le_sqrt h

end Hagi.Unified.ReplayCompute
