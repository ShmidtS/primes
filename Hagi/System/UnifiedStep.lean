import Mathlib.Tactic
import Hagi.Prelude.Info
import Hagi.Energy.Quantizer
import Hagi.Energy.Variational
import Hagi.Energy.Cooling

set_option linter.style.header false

/-!
# System.UnifiedStep — композитный шаг единой теории

Единый шаг объединённой теории (аудит 3, «Quantized Mirror
Descent»): веса экспертов — Гиббс/софтмакс при обратной
температуре (оптимальны по `gibbs_optimal_bound`), точка
смешения — выпуклая комбинация экспертов, обновление —
квантованный градиентный шаг по решётке `Δℤ` (`gridQ`),
горизонтный сертификат — `quantized_descent_telescope`
(цена квантования Δ/2 за шаг). Все четыре компонента
объединены в один сертификат шага.
-/

namespace Hagi.System

open Hagi.Prelude Hagi.Energy

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Сертификат композитного шага единой теории**: веса
Гиббс-ансамбля `w = softmax(−L / Tt)` образуют строго
положительное распределение, точка смешения
`m = Σ wᵢ·θᵢ` определена, и квантованное обновление
`Q_Δ(m − γ·g)` отстоит от точной цели не более чем на
полшага `Δ / 2`. Содержательные части: распределение —
канонические свойства софтмакса, ошибка — единый
квантователь `gridQ`; комбинация и есть «единый шаг»
объединённой теории (охлаждение × ансамбль × решётка). -/
theorem unified_step_certificate (θ L : ι → ℝ) (g : ℝ)
    (γ Δ Tt : ℝ) (hΔ : 0 < Δ) :
    let w := softDef (fun i => -(L i) / Tt)
    let m := ∑ i, w i * θ i
    (∀ i, 0 < w i) ∧ (∑ i, w i = 1)
      ∧ |gridQ Δ hΔ (m - γ * g) - (m - γ * g)| ≤ Δ / 2 := by
  intro w m
  refine ⟨fun i => softDef_pos _ i, softDef_sum_one _, ?_⟩
  exact gridQ_error Δ hΔ (m - γ * g)


/-- **Суммарный бюджет качества композитного шага**: Гиббс-
ансамбль при обратной температуре 1/Tt даёт ожидаемую потерю
смеси в Tt·log n-окрестности глобального минимума
(`gibbs_mixture_quality`: термодинамическая цепочка
расписание → свободная энергия → энергия смеси), а
квантованное исполнение шага вносит не более Δ/2 ошибки в
параметрах (`gridQ_error`). Полный вычислительный бюджет
качества HAGI: (Tt·log n) по охлаждению + (Δ/2) по решётке —
оба слагаяемых минимизируются независимо, компромисс
«качество × вычисления» явный. -/
theorem unified_step_budget (θ L : ι → ℝ) (g γ Δ Tt : ℝ)
    (hΔ : 0 < Δ) (hTt : 0 < Tt) :
    (∃ m : ℝ, (∀ i, m ≤ L i)
      ∧ (∑ i, softDef (fun i => -(L i) / Tt) i * L i
          ≤ m + Tt * Real.log ((Fintype.card ι : ℕ):ℝ)))
      ∧ |gridQ Δ hΔ ((∑ i, softDef (fun i => -(L i) / Tt) i * θ i) - γ * g)
          - ((∑ i, softDef (fun i => -(L i) / Tt) i * θ i) - γ * g)| ≤ Δ / 2 := by
  refine ⟨gibbs_mixture_quality L hTt, ?_⟩
  exact gridQ_error Δ hΔ _

end Hagi.System
