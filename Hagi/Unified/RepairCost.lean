/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# RepairCost — replay против block по памяти

`REPAIR_MODE = "replay"` (unified.py): ремонт забывания переучиванием старых
байтов, а не добавлением блока (`"block"`, `MAX_BLOCKS = 4`, `ADMIT_MEM_COST`).
Block-раунд добавляет `P` параметров навсегда; replay-раунд — ничего.

* `memAfterBlock mem₀ P m = mem₀ + m·P`, `memAfterReplay mem₀ _ = mem₀`;
* `replay_mem_const` — replay не растит память;
* `block_mem_le` — block ≤ `mem₀ + 4·P` (`MAX_BLOCKS`);
* `block_mem_gt` — при `P > 0` block строго дороже с первого раунда.
-/

namespace Hagi.Unified.RepairCost

/-- Память модели после раундов ремонта: block-раунд добавляет `P` параметров
навсегда, replay-раунд — ничего. -/
noncomputable def memAfterBlock (mem₀ P : ℝ) (m : ℕ) : ℝ := mem₀ + m * P
noncomputable def memAfterReplay (mem₀ : ℝ) (_m : ℕ) : ℝ := mem₀
/-- Replay не растит память при любом числе раундов. -/
theorem replay_mem_const (mem₀ : ℝ) (m : ℕ) : memAfterReplay mem₀ m = mem₀ := rfl
/-- Block ограничен `MAX_BLOCKS`: память ≤ `mem₀ + MAX·P`. -/
theorem block_mem_le (mem₀ P : ℝ) (hP : 0 ≤ P) (m : ℕ) (hm : m ≤ 4) :
    memAfterBlock mem₀ P m ≤ mem₀ + 4 * P := by
  unfold memAfterBlock
  have h4 : (m : ℝ) ≤ 4 := Nat.cast_le.2 hm
  nlinarith [mul_le_mul_of_nonneg_left h4 hP]
/-- При `P > 0` block строго дороже по памяти с первого раунда. -/
theorem block_mem_gt (mem₀ P : ℝ) (m : ℕ) (hP : 0 < P) (hm : 0 < m) :
    memAfterReplay mem₀ m < memAfterBlock mem₀ P m := by
  unfold memAfterReplay memAfterBlock
  have : 0 < (m : ℝ) * P := mul_pos (Nat.cast_pos.2 hm) hP
  linarith

end Hagi.Unified.RepairCost
