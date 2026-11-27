/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# HoldoutPurity — контроль приёма должен быть чистым хвостом нового домена

`_interleave_replay` (unified.py): голова нового домена перемежается с
повтором старого, последние 20% нового — чистый хвост. До de61271 holdout
брался из склейки (`0.15` от combined), и при `REPLAY_FRAC = 1.0` содержал
19–31% нового — сертификат приёма мерил старые домена.

* `combined pre tail = pre ++ tail`, `holdout` — последние `h` элементов;
* `holdout_subset_tail` — если `h ≤ |tail|`, holdout — суффикс чистого хвоста;
* `mem_holdout_imp_mem_tail` — каждый элемент holdout — элемент хвоста.
-/

namespace Hagi.Data.HoldoutPurity

/-- Склейка: перемежение головы нового домена с повтором, затем чистый хвост. -/
def combined (pre tail : List α) : List α := pre ++ tail
/-- Holdout — последние `h` элементов склейки. -/
def holdout (pre tail : List α) (h : ℕ) : List α :=
  (combined pre tail).drop ((combined pre tail).length - h)
/-- Если хвост не короче holdout, holdout целиком лежит в чистом хвосте
нового домена (не содержит повтор старого). -/
theorem holdout_subset_tail (pre tail : List α) (h : ℕ) (hh : h ≤ tail.length) :
    ∃ s, s ++ holdout pre tail h = tail := by
  unfold holdout combined
  rw [List.length_append, List.drop_append]
  have heq : pre.length + tail.length - h - pre.length = tail.length - h := by omega
  rw [heq, List.drop_of_length_le (by omega : pre.length ≤ pre.length + tail.length - h)]
  exact ⟨tail.take (tail.length - h), by simpa using List.take_append_drop tail (tail.length - h)⟩
/-- В частности, каждый элемент holdout — элемент хвоста. -/
theorem mem_holdout_imp_mem_tail (pre tail : List α) (h : ℕ) (hh : h ≤ tail.length)
    (x : α) (hx : x ∈ holdout pre tail h) : x ∈ tail := by
  obtain ⟨s, hs⟩ := holdout_subset_tail pre tail h hh
  rw [← hs]
  exact List.mem_append.2 (Or.inr hx)

end Hagi.Data.HoldoutPurity
