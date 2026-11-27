/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# ValWindows — когда проверочные окна независимы (условие EB-гейта)

_old_domains_ce_vec (unified.py): начала окон `0, step, 2·step, …`,
`step = max 1 (n // 256)`, длина окна `k = seq_len`. EB-граница
(`admit_false_le` (PairedGain)) предполагает независимые разности; она верна,
только когда соседние окна не делят байты.

* `covers` — окно `i` покрывает `[i·step, i·step + k)`;
* `adjacent_disjoint_iff` — соседние окна не пересекаются ⇔ `k ≤ step`;
* `indep_threshold` — `k ≤ max 1 (n/256) ⇔ k ≤ 1 ∨ 256·k ≤ n`: при `k = 64`
  независимость требует `n ≥ 16384` байт; более короткие домены дают
  перекрывающиеся окна и EB-радиус занижен (honest-граница кода).
-/

namespace Hagi.Data.ValWindows

/-- Окно `i` сетки с шагом `step` покрывает байты `[i·step, i·step + k)`. -/
noncomputable def covers (step k i b : ℕ) : Prop := i * step ≤ b ∧ b < i * step + k
/-- Соседние окна не пересекаются (нет общего байта) ⇔ `k ≤ step`. -/
theorem adjacent_disjoint_iff (k step i : ℕ) :
    (¬ ∃ b, covers step k i b ∧ covers step k (i+1) b) ↔ k ≤ step := by
  have h1 : (i + 1) * step = i * step + step := by ring
  constructor
  · intro h
    by_contra hk
    have hk' : step < k := lt_of_not_ge hk
    refine h ⟨i * step + step, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> first
    | omega
    | (rw [h1]; omega)
  · intro h ⟨b, hb1, hb2⟩
    unfold covers at hb1 hb2
    rw [h1] at hb2
    omega
/-- Порог независимости для сетки `_old_domains_ce_vec`: `step = max 1 (n // 256)`,
окна независимы ⇔ `256·k ≤ n` (при `k = 64`: `n ≥ 16384` байт). -/
theorem indep_threshold (n k : ℕ) :
    k ≤ max 1 (n / 256) ↔ k ≤ 1 ∨ 256 * k ≤ n := by
  constructor
  · intro h
    by_cases h1 : k ≤ 1
    · exact Or.inl h1
    · apply Or.inr
      have h2 : k ≤ n / 256 := le_trans h (max_le (by omega) (le_refl _)) |>.trans (by omega)
      have := (Nat.le_div_iff_mul_le (k := 256) (by norm_num)).1 h2
      rw [mul_comm] at this
      exact this
  · intro h
    rcases h with h | h
    · exact h.trans (le_max_left _ _)
    · have hle : k ≤ n / 256 := (Nat.le_div_iff_mul_le (k := 256) (by norm_num)).2 (by rw [mul_comm]; exact h)
      exact hle.trans (le_max_right _ _)

end Hagi.Data.ValWindows
