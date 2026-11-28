/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Probability.PairedGain

/-!
# DecisionRule — одно правило для всех порогов

Каждая константа-порог в HAGI (MIN_GAIN, SE_MULT, MIN_WINDOWS, λ, θ) — частный
случай одного сравнения: измеренный выигрыш минус его радиус больше цены байт.
См. docs/DERIVED-CONFIG.md §3 (какая константа выводится, какая — честный пробел).
-/

namespace Hagi.Unified.DecisionRule
open Hagi.Probability.PairedGain
/-- Единое правило решения: действие с измеренным выигрышем `ĝ` и ценой байт `λ·ΔB`
сертифицируется, когда `ĝ − radius(n, α) > λ·ΔB`; тогда вероятность ложного
сертифицирования (истинный выигрыш не больше цены) ≤ α. Все гейты HAGI — частные
случаи: приём адаптера/блока (ΔB = 0, `ĝ` = парный выигрыш), откат по наихудшему
домену (с Bonferroni α/16), вторая стадия строк (ΔB = байты строк, `ĝ` из
δ-кривой), MDL (λ = 8·ln 2 / N, `AnchorGate.mdl_lambda`). Порог в правиле — не
константа, а радиус; число окон — не константа, а `n*(ε) = ⌈1/rootT²⌉`. -/
theorem certified_decision (V : Type) [Fintype V] [Nonempty V] (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (D : V → ℝ) (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ v, |D v - ∑ v', q v' * D v'| ≤ b)
    (sig : ℝ) (hsig : 0 < sig) (hvar : ∑ v, q v * (D v - ∑ v', q v' * D v')^2 ≤ sig)
    (n : ℕ) (hn : 0 < n) (α : ℝ) (hα : 0 < α) (hα2 : α < 1) (lam dB : ℝ) (hdB : 0 ≤ dB)
    (hμ : ∑ v, q v * D v ≤ lam * dB) :
    prodPq (fun _ : Fin n => q)
      (fun ω => ¬ ((∑ i, D (ω i)) / n - radius sig b n α > lam * dB)) ≥ 1 - α :=
  admit_false_le_shifted q hq0 hq1 D b hb hbnd sig hsig hvar n hn α hα hα2 (lam * dB) hμ
end Hagi.Unified.DecisionRule
