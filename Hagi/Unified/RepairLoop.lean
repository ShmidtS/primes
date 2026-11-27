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
  каждый отклонённый — возвращает прежнюю;
* `no_tol_guarantee` — честная граница: допуск не гарантирован — при стагнации
  выше `tol` цикл завершается с `f > tol`; код фиксирует остаток откатом.
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

/-- Цикл ремонта НЕ гарантирует достижения допуска: если наихудшая CE
стагнирует выше `tol` (кандидат не лучше текущего), цикл завершается с
`f > tol` — остаток забывания, который код фиксирует откатом. -/
theorem no_tol_guarantee (max : ℕ) (f : ℝ) (hf : 0 < f) (tol : ℝ) (htol : tol < f)
    (T : ℕ) (hT : 0 < T) :
    let f' : ℕ → ℝ := fun _ => f
    (loop T max 0 f f').2 = f ∧ tol < (loop T max 0 f f').2 := by
  intro f'
  have hstep : step max 0 f (f' 0) = (0, f) := by
    unfold step
    have : ¬ (f' 0 < f ∧ 0 < max) := by
      intro h
      linarith [show f' 0 = f from rfl]
    simp [this]
  induction T with
  | zero => simp [loop, htol]
  | succ T ih =>
    rw [loop]
    have hr : (step max 0 f (f' 0)).1 = 0 := by rw [hstep]
    rw [if_pos hr, hstep]
    exact ⟨rfl, htol⟩

end Hagi.Unified.RepairLoop
