import Mathlib.Tactic
import Hagi.StatMech.Hopfield.CharPatterns

set_option linter.style.header false

/-!
# SubMemory — память на подмножестве доменов (цикл 31)

Память Хопфилда на ПОДМНОЖЕСТВЕ доменов S ⊂ куб: паттерны —
характеры χ_w, w ∈ S. Энергия вычисляется ТОЧНО через
частичный Parseval:
  E_S(v) = Σ_{w∈S} ⟨χ_w, v⟩²/(2·2^k) = Σ_{w∈S} ‖P_w v‖².
Следствия (все доказуемы точно):
  1. subset_plus_complement: E_S + E_{Sᶜ} = ‖v‖²/2 — память
     и её дополнение ДЕЛЯТ энергию сигнала без потерь;
  2. subset_le_full: E_S ≤ E_full = ‖v‖²/2 — монотонность
     ёмкости по множеству паттернов;
  3. Для спинов: E_S(σ) + E_{Sᶜ}(σ) = N/2 — выбор подмножества
     S перераспределяет (не создаёт) энергию.
Ёмкостный смысл: размер |S| задаёт максимальную энергию
E_S ≤ ‖v‖²/2, а структура S — КАКАЯ часть спектра сигнала
запоминается. Спектральный выбор S (цикл 27) — выбор по
доменной энергии ‖P_w v‖² — оптимально заполняет бюджет.
-/

open Finset Hagi.Core

namespace Hagi.StatMech.Hopfield.SubMemory

open Hagi.StatMech.Hopfield Hagi.StatMech.Hopfield.CharPatterns
  Hagi.Learning.HadamardProjectors Hagi.Learning.HadamardParseval

variable {k : ℕ}

/-- Энергия памяти на подмножестве доменов S. -/
noncomputable def subsetEnergy (S : Finset (Fin k → ZMod 2))
    (v : (Fin k → ZMod 2) → ℝ) : ℝ :=
  ∑ w ∈ S, (dotProduct (charRowR w) v) ^ 2 / (2 * ((2:ℕ)^k : ℕ))

/-- ЧАСТЧИЧНЫЙ PARSEVAL: энергия подмножества доменов =
ПОЛОВИНЕ суммы доменных энергий:
E_S(v) = (1/2)·Σ_{w∈S} ‖P_w v‖². -/
theorem subsetEnergy_eq (S : Finset (Fin k → ZMod 2))
    (v : (Fin k → ZMod 2) → ℝ) :
    subsetEnergy S v
      = (∑ w ∈ S, dotProduct (charProjR w v) (charProjR w v)) / 2 := by
  unfold subsetEnergy
  have hnorm : ∀ w : Fin k → ZMod 2,
      (dotProduct (charRowR w) v) ^ 2 / (2 * ((2:ℕ)^k : ℕ))
        = dotProduct (charProjR w v) (charProjR w v) / 2 := by
    intro w
    rw [charProjR_norm_sq]
    field_simp
  rw [Finset.sum_congr rfl (fun w (_ : w ∈ S) => hnorm w),
    Finset.sum_div]

/-- РАЗДЕЛЕНИЕ ЭНЕРГИИ: память S и её дополнение делят
полную энергию сигнала без потерь:
E_S(v) + E_{Sᶜ}(v) = ‖v‖²/2. -/
theorem subset_plus_complement (S : Finset (Fin k → ZMod 2))
    (v : (Fin k → ZMod 2) → ℝ) :
    subsetEnergy S v + subsetEnergy (Sᶜ) v
      = dotProduct v v / 2 := by
  rw [subsetEnergy_eq S v, subsetEnergy_eq (Sᶜ) v, ← add_div,
    Finset.sum_add_sum_compl S,
    ← Hagi.Learning.HadamardParseval.parseval v]

/-- МОНОТОННОСТЬ ЁМКОСТИ: подмножество не превосходит полной
памяти: E_S(v) ≤ ‖v‖²/2 (все доменные энергии неотрицательны). -/
theorem subset_le_full (S : Finset (Fin k → ZMod 2))
    (v : (Fin k → ZMod 2) → ℝ) :
    subsetEnergy S v ≤ dotProduct v v / 2 := by
  have hsplit := subset_plus_complement S v
  have hcomp : (0:ℝ) ≤ subsetEnergy (Sᶜ) v := by
    unfold subsetEnergy
    refine Finset.sum_nonneg (fun w _ => ?_)
    exact div_nonneg
      (sq_nonneg (dotProduct (charRowR w) v)) (by positivity)
  linarith

end Hagi.StatMech.Hopfield.SubMemory
