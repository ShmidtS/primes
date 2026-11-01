import Hagi.Unified.PLQuad

/-!
# Качество за конечный бюджет: PL-горизонт

Сложностное следствие линейной скорости: чтобы сжать
остаточную энергию до порога, достаточно конечного
горизонта, и бюджет пересылки горизонта — точное
произведение шагов на размер носителя. Связка
«качество ↔ минимальные вычисления».
-/

namespace Hagi.Unified.PLBudget

open Hagi.Unified.PLQuad
open Hagi.Unified.PLLoop
open Hagi.Unified.DescentCore
open Hagi.Unified.DescentCoreQuad

variable {k : Type*} [Fintype k]

/-- Бюджет пересылки горизонта: шагов по числу
координат. -/
def plCommBudget (k : Type*) [Fintype k] (n : ℕ) : ℝ :=
  n * (Fintype.card k : ℝ)

/-- ДОСТИЖЕНИЕ ПОРОГА: при линейной скорости конечного
горизонта достаточно, чтобы остаточная энергия упала
ниже порога. -/
theorem quad_pl_eps (a : k → ℝ)
    (f : ℕ → k → ℝ) (drops : ℕ → ℝ) (n : ℕ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hκ2 : 2 * κ < 1)
    (hdrop : ∀ t < n, κ * nrm2 (quadGrad a (f t)) ≤ drops t)
    (hcert : ∀ t < n,
      quadE a (f (t + 1)) ≤ quadE a (f t) - drops t)
    (ε : ℝ) (hε : (1 - 2 * κ)^n * quadE a (f 0) ≤ ε) :
    quadE a (f n) ≤ ε := by
  have hrate := quad_pl_rate a f drops n κ hκ hκ2 hdrop hcert
  linarith

/-- КАЧЕСТВО ЗА БЮДЖЕТ: порог достигается, а бюджет
пересылки равен произведению горизонта на размер
носителя. -/
theorem quad_pl_eps_budget (a : k → ℝ)
    (f : ℕ → k → ℝ) (drops : ℕ → ℝ) (n : ℕ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hκ2 : 2 * κ < 1)
    (hdrop : ∀ t < n, κ * nrm2 (quadGrad a (f t)) ≤ drops t)
    (hcert : ∀ t < n,
      quadE a (f (t + 1)) ≤ quadE a (f t) - drops t)
    (ε : ℝ) (hε : (1 - 2 * κ)^n * quadE a (f 0) ≤ ε) :
    quadE a (f n) ≤ ε
      ∧ n * (Fintype.card k : ℝ) = plCommBudget k n := by
  constructor
  · exact quad_pl_eps a f drops n κ hκ hκ2 hdrop hcert ε hε
  · rfl

end Hagi.Unified.PLBudget
