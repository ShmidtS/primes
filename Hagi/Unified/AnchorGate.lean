/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# AnchorGate — гейт дрейфа старых доменов по опоре

HAGI_v2 1d14568 (unified.py, HAGI_ANCHOR_GATE default on): прирост CE старого
домена считается от его CE при приёме (`gate_anchor`), а не от предыдущего
шага; допуск — четыре ошибки среднего по окнам домена; откат снимает опору.
Математическое содержание: пошаговый допуск растёт с числом шагов, опора — нет.
-/

namespace Hagi.Unified.AnchorGate
/-- Пошаговый гейт дрейфа CE домена с допуском `r` (сравнение с предыдущим
шагом) пропускает после `d` шагов любое суммарное ухудшение до `d·r`:
медленная эрозия старого домена невидима, пока каждый шаг мал. -/
theorem step_gate_accumulates (ℓ : ℕ → ℝ) (r : ℝ) (d : ℕ)
    (h : ∀ t < d, ℓ (t + 1) - ℓ t ≤ r) : ℓ d - ℓ 0 ≤ d * r := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := h d (Nat.lt_succ_self d)
    have h2 := ih (fun t ht => h t (lt_trans ht (Nat.lt_succ_self d)))
    push_cast; linarith
/-- Гейт по опоре (HAGI_v2 1d14568): допуск `r_a` на полный прирост от CE
домена при приёме равен пошаговому допуску `r_a / d` после `d` шагов — бюджет
не растёт с числом шагов, поэтому накопленный дрейф ограничен сразу. -/
theorem anchor_is_step_budget (ℓ : ℕ → ℝ) (r_a : ℝ) (d : ℕ) (hd : 0 < d)
    (h : ∀ t < d, ℓ (t + 1) - ℓ t ≤ r_a / d) : ℓ d - ℓ 0 ≤ r_a := by
  have := step_gate_accumulates ℓ (r_a / d) d h
  rw [mul_div_assoc'] at this
  rw [mul_comm] at this; field_simp at this
  exact this
end Hagi.Unified.AnchorGate
