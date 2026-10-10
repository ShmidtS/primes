/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Core.SWA
set_option linter.style.header false

/-!
# CausalFilter — каузальная свёртка: нулевая утечка из будущего при левом паддинге

Каузальная свёртка с левым паддингом
`y t = Σ_{i ≤ t} w (t−i) · x i` — выход в t зависит только от
префикса `x 0..t`.

* `causal_prefix_determined`: если входы совпадают на префиксе
  `0..t`, выходы совпадают в t — нулевая утечка из будущего;
* `leak_same_step`: контрпример — центрированная свёртка
  (читающая `x (t+1)`) протекает: изменение `x (t+1)` на c
  меняет выход в t на `w 0 · c` (при `w 0 ≠ 0`).
-/

namespace Hagi.Step
open Finset

/-- Каузальная свёртка с левым паддингом:
`causalConv w x t = Σ_{i ≤ t} w (t−i)·x i` — выход в t зависит
только от префикса `x 0..t`. -/
def causalConv (w x : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (t + 1), w (t - i) * x i

/-- Если `x i = y i` для всех `i ≤ t`, то
`causalConv w x t = causalConv w y t`. -/
theorem causal_prefix_determined (w x y : ℕ → ℝ) (t : ℕ)
    (hagree : ∀ i ≤ t, x i = y i) :
    causalConv w x t = causalConv w y t := by
  unfold causalConv
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have : x i = y i := hagree i (by omega)
  rw [this]

/-- Центрированная свёртка: читает на шаг вперёд
(`Σ_{i ≤ t+1} w (t+1−i)·x i`). -/
def centeredConv (w x : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (t + 2), w (t + 1 - i) * x i

/-- При `w 0 ≠ 0` изменение `x (t+1)` на c меняет выход
центрированной свёртки в t ровно на `w 0 · c`. -/
theorem leak_same_step (w x : ℕ → ℝ) (t : ℕ) (hw : w 0 ≠ 0)
    (c : ℝ) :
    centeredConv w (fun i => if i = t + 1 then x i + c else x i) t
      = centeredConv w x t + w 0 * c := by
  unfold centeredConv
  have key : ∀ i ∈ Finset.range (t + 2),
      w (t + 1 - i) * (if i = t + 1 then x i + c else x i)
      = w (t + 1 - i) * x i
        + (if i = t + 1 then w 0 * c else 0) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    by_cases h : i = t + 1
    · subst h
      rw [if_pos rfl, if_pos rfl, Nat.sub_self]
      ring
    · rw [if_neg h, if_neg h]
      ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  have hlast : ∑ x ∈ Finset.range (t + 2),
      (if x = t + 1 then w 0 * c else 0) = w 0 * c := by
    rw [Finset.sum_eq_single (t + 1)]
    · rw [if_pos rfl]
    · intro b hb hne
      rw [if_neg hne]
    · intro hcon
      exfalso
      simp only [Finset.mem_range] at hcon
      omega
  rw [hlast]

end Hagi.Step

namespace Hagi
export Hagi.Step (causalConv causal_prefix_determined centeredConv leak_same_step)
end Hagi
