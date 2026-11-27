/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# RepairLoop — цикл ремонта забывания: блоки растут, наихудшая CE не растёт

`unified.py`: пока `max_i (post_i − pre_i) > WORST_TOL` и лимит блоков
позволяет — добавить блок-тождество, обучить только его на окнах старых
доменов, мерить заново; нет улучшения → снять блок (точный откат) и стоп.

* `step` — раунд: принять (`k+1`, `f'`) только если `f' < f` и `k < max`;
  иначе откат (`k`, `f`);
* `loop` — структурная рекурсия по топливу `T` ⇒ завершение за ≤ `T` раундов;
* `loop_blocks_bounds` — `k ≤ blocks ≤ max`;
* `loop_f_le` — наихудшая CE не возрастает: каждый принятый раунд её снижает,
  каждый отклонённый — возвращает прежнюю.
-/

namespace Hagi.Unified.RepairLoop

/-- Один раунд ремонта: принять блок, если наихудшая CE строго упала и лимит
блоков не исчерпан; иначе — откат (снять блок, сохранить `k` и `f`). -/
noncomputable def step (max : ℕ) (k : ℕ) (f f' : ℝ) : ℕ × ℝ :=
  if f' < f ∧ k < max then (k + 1, f') else (k, f)
theorem step_k_bounds (max k : ℕ) (f f' : ℝ) (hk : k ≤ max) :
    k ≤ (step max k f f').1 ∧ (step max k f f').1 ≤ max := by
  unfold step
  split
  · rename_i h; omega
  · exact ⟨le_refl k, hk⟩
theorem step_f_le (max k : ℕ) (f f' : ℝ) : (step max k f f').2 ≤ f := by
  unfold step
  split
  · rename_i h; linarith [h.1]
  · exact le_refl f
/-- Цикл по топливу `T`: structural recursion; стоп при откате или исчерпании. -/
noncomputable def loop : ℕ → ℕ → ℕ → ℝ → (ℕ → ℝ) → ℕ × ℝ
  | 0, _, k, f, _ => (k, f)
  | T + 1, max, k, f, f' =>
    let r := step max k f (f' T)
    if r.1 = k then r else loop T max r.1 r.2 f'
theorem loop_blocks_bounds (T max k : ℕ) (f : ℝ) (f' : ℕ → ℝ) (hk : k ≤ max) :
    k ≤ (loop T max k f f').1 ∧ (loop T max k f f').1 ≤ max := by
  induction T generalizing k f with
  | zero => exact ⟨le_refl k, hk⟩
  | succ T ih =>
    rw [loop]
    have hb := step_k_bounds max k f (f' T) hk
    split
    · exact ⟨hb.1, hb.2⟩
    · rcases ih (step max k f (f' T)).1 (step max k f (f' T)).2 hb.2 with ⟨h1, h2⟩
      exact ⟨hb.1.trans h1, h2⟩
theorem loop_f_le (T max k : ℕ) (f : ℝ) (f' : ℕ → ℝ) : (loop T max k f f').2 ≤ f := by
  induction T generalizing k f with
  | zero => exact le_refl f
  | succ T ih =>
    rw [loop]
    have hf := step_f_le max k f (f' T)
    split
    · exact hf
    · exact (ih _ _).trans hf

end Hagi.Unified.RepairLoop
