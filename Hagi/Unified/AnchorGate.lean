/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Probability.PairedGain

/-!
# AnchorGate — гейт дрейфа старых доменов по опоре

HAGI_v2 1d14568 (unified.py, HAGI_ANCHOR_GATE default on): прирост CE старого
домена считается от его CE при приёме (`gate_anchor`), а не от предыдущего
шага; допуск — четыре ошибки среднего по окнам домена; откат снимает опору.
Математическое содержание: пошаговый допуск растёт с числом шагов, опора — нет.
-/

namespace Hagi.Unified.AnchorGate
open Hagi.Probability.PairedGain
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
/-- Цена байта в MDL: сумма длины данных `N·CE` (нат) и длины модели `8·ln 2·B`
(нат) имеет те же минимизаторы, что и `CE + λ·B` с `λ = 8·ln 2 / N`: параметр
`λ` не свободен, он обратен объёму данных. Код: `choose_emb_rows2(lam = 5e-4)`
соответствует `N ≈ 11` кБ; книга 400 кБ даёт `1.4e-5`. -/
theorem mdl_lambda (N : ℝ) (hN : 0 < N) (f B : ℕ → ℝ) (k₀ : ℕ)
    (h : ∀ k, N * f k₀ + 8 * Real.log 2 * B k₀ ≤ N * f k + 8 * Real.log 2 * B k) :
    ∀ k, f k₀ + (8 * Real.log 2 / N) * B k₀ ≤ f k + (8 * Real.log 2 / N) * B k := by
  intro k
  have h' := h k
  have e : ∀ j, N * (f j + (8 * Real.log 2 / N) * B j) = N * f j + 8 * Real.log 2 * B j := by
    intro j; field_simp
  have : N * (f k₀ + (8 * Real.log 2 / N) * B k₀) ≤ N * (f k + (8 * Real.log 2 / N) * B k) := by
    rw [e, e]; exact h'
  exact le_of_mul_le_mul_left this hN
/-- Минимальное число окон домена, при котором прирост CE относительно опоры
сертифицирован на уровне `ε` (`radius ≤ ε` с вероятностью ≥ 1 − α), —
`n* = ⌈1/rootT²⌉`; `4·SE` этим свойством не обладает. Измерено (σ² = 1.6,
`b ∈ [3, 5]`, `ε = 0.25`): `n* = 463…978` окон при Bonferroni 1…16, тогда как
кода `ANCHOR_MIN_WINDOWS = 32` даёт радиус 1.5–3.0 nat — эмпирически ноль ложных
срабатываний при 64+, но без конечной-выборочной гарантии. -/
theorem anchor_windows_certified (sig b α ε : ℝ) (hα : 0 < α) (hα2 : α < 1) (hsig : 0 < sig)
    (hb : 0 < b) (he : 0 < ε) (n : ℕ) (hn : 0 < n)
    (h : 1 / Real.sqrt n ≤ rootT sig b α ε) : radius sig b n α ≤ ε :=
  (radius_le_iff_ge_root sig b α ε hα hα2 hsig hb he n hn).mpr h
end Hagi.Unified.AnchorGate
