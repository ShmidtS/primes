/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# RareDecay — затухание весов и редкие признаки

Pinto, Galanti, Balestriro, «The Fair Language Model Paradox», arXiv:2410.11985:
weight decay непропорционально подавляет низкочастотные токены. Причина в
масштабе равновесия: при плотном затухании (decay на каждом шаге) и градиенте,
приходящем с частотой `f`, неподвижная точка `w* = f·η·g/λ` пропорциональна `f`.

* `dense_decay_fixed_point` — плотный режим: редкий признак теряет масштаб;
* `coupled_decay_fixed_point` — затухание только на шагах обновления
  (HAGI_v2 `optimal_lm.py` HybridMuonAdamW: `p.mul_(where(act, 1 − lr·wd, 1))`):
  `w* = η·g/λ` — равновесный масштаб не зависит от частоты;
* `dense_over_coupled` — отношение равновесий равно `f`.
-/

namespace Hagi.Step.RareDecay
/-- Плотное затухание (wd на каждом шаге, градиент — с частотой `f`): неподвижная
точка `w* = f·η·g/lam` — редкий признак (малое `f`) подавляется пропорционально
частоте (Fair Language Model Paradox, Pinto–Galanti–Balestriro 2024). -/
theorem dense_decay_fixed_point (f η g lam w : ℝ) (hlam : lam ≠ 0)
    (h : (1 - lam) * w + f * η * g = w) : w = f * η * g / lam := by
  apply (eq_div_iff hlam).2
  linarith [h]
/-- Связанное затухание (wd только на шагах обновления, HAGI_v2 opt. 215:
`p.mul_(where(act, 1 − lr·wd, 1))`): за шаг `w ← (1 − f·lam)·w + f·η·g`;
неподвижная точка `w* = η·g/lam` — не зависит от частоты `f`: редкие и частые
признаки получают одинаковый равновесный масштаб. -/
theorem coupled_decay_fixed_point (f η g lam w : ℝ) (hf : f ≠ 0) (hlam : lam ≠ 0)
    (h : (1 - f * lam) * w + f * η * g = w) : w = η * g / lam := by
  have h' : f * lam * w = f * (η * g) := by nlinarith [h]
  have key : lam * w = η * g := by
    apply mul_left_cancel₀ hf
    calc f * (lam * w) = f * lam * w := by ring
      _ = f * (η * g) := h'
  apply (eq_div_iff hlam).2
  linarith [key]
/-- Отношение равновесий: плотный режим даёт в `f` раз меньший масштаб, чем
связанный — редкий признак (`f < 1`) теряет масштаб. -/
theorem dense_over_coupled (f η g lam : ℝ) (hlam : lam ≠ 0) (hη : η ≠ 0) (hg : g ≠ 0) :
    (f * η * g / lam) / (η * g / lam) = f := by
  apply (div_eq_iff (div_ne_zero (mul_ne_zero hη hg) hlam)).2
  rw [show f * η * g = f * (η * g) by ring]
  field_simp [hη, hg, hlam]

end Hagi.Step.RareDecay
