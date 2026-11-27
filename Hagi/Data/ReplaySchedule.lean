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

Литература: Evron et al. 2025 (arXiv 2504.04579) — случайный порядок задач
с повторениями даёт универсальную скорость забывания
`O(min(T^{-1/4}, (d-r)/T))`; детерминированный round-robin здесь — его
конструктивный аналог с гарантированным возрастом. Zheng et al. 2026
(arXiv 2610.31551) — перезапуск затухания lr на границах задач усиливает
распространение старых возмущений: свежий оптимизатор на домен
(optimal_lm.py) относится к тому же классу расписаний.
Replay × repair (`_repair_forgetting`, `REPLAY_FRAC`): `ForgetModel` — the
forgetting `f` grows by at most `δ` per step and every replay hit (`t % p = 0`)
brings it back to `f₀`; `replay_repair_bounded`: `f t ≤ f₀ + p·δ` for all `t`.
This is the bridge ReplaySchedule × RepairLoop × ContinualForgetting: bounded
forgetting is a theorem as soon as the repair gate holds at the hits.
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

/-- Забывание `f : ℕ → ℝ` (CE старого домена): за шаг без ремонта растёт не
более чем на `δ`; в моменты попадания replay (`t % p = 0`, `t > 0`) ремонт
возвращает `f t ≤ f₀`. -/
structure ForgetModel (p : ℕ) (f : ℕ → ℝ) (f₀ δ : ℝ) : Prop where
  step : ∀ t, f (t + 1) ≤ f t + δ
  repair : ∀ t, 0 < t → t % p = 0 → f t ≤ f₀
/-- Replay + repair ограничивают забывание: `f t ≤ f₀ + p·δ` для всех `t`. -/
theorem replay_repair_bounded (p : ℕ) (hp : 0 < p) (f : ℕ → ℝ) (f₀ δ : ℝ)
    (h : ForgetModel p f f₀ δ) (ht0 : f 0 ≤ f₀) (hδ : 0 ≤ δ) (t : ℕ) :
    f t ≤ f₀ + p * δ := by
  -- индукция по блокам длины p
  have key : ∀ n r : ℕ, r < p → f (n * p + r) ≤ f₀ + r * δ := by
    -- общий факт: r шагов от точки s с f s ≤ B дают f (s + r) ≤ B + r·δ
    have climb : ∀ (s r : ℕ) (B : ℝ), f s ≤ B → f (s + r) ≤ B + r * δ := by
      intro s r B hB
      induction r generalizing B with
      | zero => simpa using hB
      | succ r ihr =>
        have h1 : f (s + r) ≤ B + r * δ := ihr B hB
        have h2 : f (s + r + 1) ≤ f (s + r) + δ := h.step _
        have hs : s + (r + 1) = s + r + 1 := by ring
        rw [hs]
        push_cast
        linarith
    intro n
    induction n with
    | zero =>
      intro r hr
      have : f (0 + r) ≤ f₀ + r * δ := climb 0 r f₀ (by simpa using ht0)
      simpa [Nat.zero_mul, Nat.zero_add] using this
    | succ n ih =>
      intro r hr
      have hrep : f ((n + 1) * p) ≤ f₀ := by
        apply h.repair
        · exact Nat.mul_pos (Nat.succ_pos n) hp
        · simp
      have hs : (n + 1) * p + r = ((n + 1) * p) + r := by ring
      rw [hs]
      exact (climb ((n + 1) * p) r f₀ hrep).trans (by nlinarith [hr, hδ])
  obtain ⟨n, r, ht, hr⟩ : ∃ n r, t = n * p + r ∧ r < p := ⟨t / p, t % p, by rw [Nat.mul_comm (t / p) p]; exact (Nat.div_add_mod t p).symm, Nat.mod_lt _ hp⟩
  rw [ht]
  calc f (n * p + r) ≤ f₀ + r * δ := key n r hr
    _ ≤ f₀ + p * δ := by
      have hrR : (r : ℝ) ≤ p := by exact_mod_cast hr.le
      nlinarith [hrR, hδ]

end Hagi.Data.ReplaySchedule
