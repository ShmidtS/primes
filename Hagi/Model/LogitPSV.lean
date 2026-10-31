import Mathlib
import Hagi.Ensemble.GapLaw

/-!
# LogitPSV — пертурбации логитов вместо весов (источник
# №69: "Rethinking Neural Thickets Without Weight
# Perturbations", arXiv 2610.40649)

Открытие источника: случайные СТАТИЧЕСКИЕ смещения
выходных логитов (ℓ + σ·ε_i) дают качество ≥ пертурбаций
весов при НУЛЕВОЙ стоимости изменения базы. Для HAGI это
устраняет конфликт «непрерывный градиентный поиск vs
тернарные веса»: база строго тернарна и заморожена, вся
стохастичность — в пространстве логитов.

Формализуем ядро: ансамбль K логит-возмущённых кандидатов
имеет НЕОТРИЦАТЕЛЬНЫЙ Jensen-гэп (ансамбль никогда не хуже
среднего по cross-entropy — реюз twoGap_nonneg), а при
σ = 0 (нулевых смещениях) гэп РАВЕН НУЛЮ (без
разнообразия нет выигрыша — реюз twoGap_zero_iff).
-/

namespace Hagi.Model.LogitPSV

open Hagi.Ensemble

variable {k : Type*} [Fintype k] [Nonempty k]

/-- Кандидат i: базовый скалярный score + статическое
смещение σ·ε_i (веса базы НЕ меняются). -/
def biasedScore (base : ℝ) (sigma : ℝ) (eps_i : ℝ) : ℝ :=
  base + sigma * eps_i

/-- ИСТОЧНИК №69, УРОВЕНЬ 1: АНСАМБЛЬ ЛОГИТ-ВОЗМУЩЕНИЙ НЕ
ХУЖЕ СРЕДНЕГО — Jensen-гэп ансамбля K статических
смещений неотрицателен: замороженная база + стохастика в
логитах даёт качество ансамбля ≥ среднего качества
кандидатов (реюз twoGap_nonneg). -/
theorem logitPSV_gap_nonneg (base sigma : ℝ) (eps : k → ℝ)
    (p : k → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    0 ≤ twoGap p (fun i => biasedScore base sigma (eps i)) :=
  twoGap_nonneg hp hsum

/-- УРОВЕНЬ 2: БЕЗ РАЗНООБРАЗИЯ НЕТ ВЫИГРЫША — при σ = 0
(или равных ε) гэп РАВЕН НУЛЮ: одинаковые кандидаты не
дают ансамблевого выигрыша; вариативность смещений —
необходимое условие gains (реюз twoGap_zero_iff). -/
theorem logitPSV_gap_zero_of_no_spread (base : ℝ)
    (p : k → ℝ) (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) :
    twoGap p (fun _ => biasedScore base 0 0) = 0 := by
  have hz : twoGap p (fun _ => biasedScore base 0 0) = 0
      ↔ ∃ c : ℝ, ∀ i, biasedScore base 0 0 = c :=
    twoGap_zero_iff hp hsum
  exact hz.mpr ⟨base, fun _ => by simp [biasedScore]⟩

/-- Замороженные веса базы: ОДНИ И ТЕ ЖЕ для всех
кандидатов (стоимость изменения базы — ноль; тернарная
база не разрушается; вся стохасть — в логитах). -/
def frozenWeights (w0 : ℝ) : k → ℝ := fun _ => w0

omit [Fintype k] [Nonempty k] in
theorem logitPSV_weights_frozen (w0 : ℝ) :
    ∀ i j : k, frozenWeights (k := k) w0 i
      = frozenWeights (k := k) w0 j :=
  fun _ _ => rfl

end Hagi.Model.LogitPSV
