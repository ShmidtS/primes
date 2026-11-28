/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# SemCache — kNN-прогноз по скрытому состоянию (SEMCACHE, cmix-neif-2.0 §4.1)

Wölk, Hutter Prize 2026: где трансформер не уверен (p_max < 0.95), ключ —
192-мерное состояние последнего слоя (нормированное, случайная проекция ±1 на
128, 4 бита/значение); 16 хэш-таблиц → до 32 соседей с косинус-весом при
температуре 0.02; у каждого соседа читается следующий байт. Память строится
только из уже закодированных байт, поэтому декодер строит её сам и архив
несёт на неё ноль бит (память — функция `f (decode a)`). Замер: −730 КБ S (0.77 %).

Обобщение `LzpExpert` с одного кандидата на распределение по соседям:
`p_cache[b] = Σ_j w_j·1{y_j = b}`, смесь `p' = (1 − λ·s)·p + λ·s·p_cache`,
где `s` — уверенность (максимальный косинус).
-/

namespace Hagi.Information.SemCache

/-- Смесь эксперта `p` с kNN-распределением `q` при весе `λ·s`. -/
noncomputable def mix (p q lam s : ℝ) : ℝ := (1 - lam * s) * p + lam * s * q

/-- Ложный сосед (истинный символ не встретился ни у одного соседа, `q y = 0`):
проигрыш относительно `p` — ровно `−log(1 − λ·s)` nat; с капом `s ≤ 1` —
не более `−log(1 − λ)`. Аналог `LzpExpert.lzp_false_ce` для распределения. -/
theorem false_ce (py lam s : ℝ) (hq0 : 0 ≤ lam * s) (hs : lam * s < 1) (hpy : 0 < py) :
    -Real.log (mix py 0 lam s) = -Real.log py - Real.log (1 - lam * s) := by
  unfold mix; simp only [mul_zero, add_zero]
  rw [mul_comm, Real.log_mul (ne_of_gt hpy) (ne_of_gt (sub_pos.mpr hs))]; ring

/-- Верный прогноз: если доля соседей с верным байтом равна `q y`, смесь даёт
`p y ≥ λ·s·q y` — выигрыш относительно любого `p y < λ·s·q y`. -/
theorem true_ce_lower (py qy lam s : ℝ) (hpy : 0 ≤ py) (hqy : 0 ≤ qy)
    (hl : lam * s ≤ 1) : lam * s * qy ≤ mix py qy lam s := by
  unfold mix; have : 0 ≤ (1 - lam * s) * py := mul_nonneg (sub_nonneg.mpr (by linarith)) hpy
  linarith

end Hagi.Information.SemCache
