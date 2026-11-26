/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# ReplaySchedule — расписание повторов старых доменов и возраст домена

`_interleave_replay` (selfdev/unified.py): доля повторов `ρ` старых доменов
чередуется с новым. Модель: каждый `p = 1/ρ`-й блок — повтор, домены идут
по кругу по `D`.

* `schedule_at` — в периоде `k` домен `d` повторяется в блоке `k·p·D + d·p`.
* `schedule_hits_window` — возраст домена ≤ `2·p·D` блоков: в любом окне этой
  длины есть повтор каждого домена. Забывание контролируется audit-ledger'ом
  (`continual_forgetting_bound`), здесь — только частота повторов.
-/

namespace Hagi.Data.ReplaySchedule

/-- Round-robin повторов: каждый `p`-й блок — повтор, домены идут по кругу по `D`. -/
noncomputable def schedule (p D : ℕ) (t : ℕ) : ℕ := (t / p) % D
/-- В периоде `k` домен `d` повторяется в блоке `k·p·D + d·p`. -/
theorem schedule_at (p D k d : ℕ) (hp : 0 < p) (hd : d < D) :
    schedule p D (k * (p * D) + d * p) = d := by
  unfold schedule
  have heq : k * (p * D) + d * p = (k * D + d) * p := by ring
  rw [heq, Nat.mul_div_cancel _ hp, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
/-- Возраст домена: в любом окне длины `2·p·D` есть повтор домена `d`. -/
theorem schedule_hits_window (p D : ℕ) (hp : 0 < p) (hD : 0 < D) (d : ℕ) (hd : d < D)
    (t : ℕ) : ∃ s, t ≤ s ∧ s < t + 2 * p * D ∧ schedule p D s = d := by
  have hpos : 0 < p * D := mul_pos hp hD
  have hlt : t % (p * D) < p * D := Nat.mod_lt _ hpos
  have hd' : d * p < p * D := by rw [mul_comm p]; exact Nat.mul_lt_mul_of_pos_right hd hp
  have hq := Nat.div_add_mod t (p * D)
  have h1 : (t / (p * D) + 1) * (p * D) = t / (p * D) * (p * D) + p * D := by ring
  have h2 : t / (p * D) * (p * D) = t - t % (p * D) := by
    have hq' := Nat.div_add_mod t (p * D)
    rw [mul_comm]; omega
  have hlo : t ≤ (t / (p * D) + 1) * (p * D) + d * p := by rw [h1, h2]; omega
  have hhi : (t / (p * D) + 1) * (p * D) + d * p < t + 2 * p * D := by
    rw [h1, h2]
    have : 2 * p * D = p * D + p * D := by ring
    rw [this]
    omega
  exact ⟨(t / (p * D) + 1) * (p * D) + d * p, hlo, hhi, schedule_at p D _ d hp hd⟩

end Hagi.Data.ReplaySchedule
