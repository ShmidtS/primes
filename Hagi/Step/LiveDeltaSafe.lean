/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.LiveDelta
import Hagi.Step.SafeQPStep

set_option linter.style.header false

/-!
# Безопасное обновление низкорангового блока

План интеграции, п. 3: условная гарантия обновления обучаемого
фактора живого блока. Две части:

1. **Окно SafeQP** (`safe_update_window`, абстрактное
   фактор-пространство X): при по-домённым градиентам g_i в X,
   десцент-посылках и шаге η ≤ safeqpEtaMax — изменения
   защищаемых потерь ограничены бюджетами ε_i
   (`safeqp_eta_max`, применённый к X — пространству
   «развёрнутых» факторов блока; флэттенинг
   Matrix r n ℝ ≃ (r×n) → ℝ — изометрия для пары
   Фробениус/стандартная, здесь НЕ формализуется).

2. **Изоляция состояния LiveDelta** (`updateNewest_*`):
   обновление новейшего блока оставляет базу, остальные блоки
   и длину списка в точности неизменными — откат и учёт
   корректны по построению.

Десцент-посылки (линейные оценки изменения потерь) — h_emp_
гипотезы; их вывод не делается.
-/

open Finset Matrix Real InnerProductSpace Hagi.LiveDelta

namespace Hagi.LiveDeltaSafe

variable {m n r : Type} [Fintype m] [Fintype n] [Fintype r]

/-! ## Часть 2: изоляция состояния -/

/-- Обновление новейшего блока: заменяется только его B-фактор. -/
def updateNewest (B' : Matrix r n ℝ) (s : LiveDelta m n r) :
    LiveDelta m n r where
  base := s.base
  blocks := match s.blocks with
    | [] => []
    | (a, _) :: bs => (a, B') :: bs

theorem updateNewest_base (B' : Matrix r n ℝ) (s : LiveDelta m n r) :
    (updateNewest B' s).base = s.base := rfl

theorem updateNewest_length (B' : Matrix r n ℝ) (s : LiveDelta m n r) :
    (updateNewest B' s).blocks.length = s.blocks.length := by
  unfold updateNewest
  cases s.blocks <;> simp

theorem updateNewest_tail (B' : Matrix r n ℝ)
    (s : LiveDelta m n r) (bs : List (Matrix r m ℝ × Matrix r n ℝ))
    (a : Matrix r m ℝ) (b : Matrix r n ℝ)
    (hs : s.blocks = (a, b) :: bs) :
    ∃ rest : List (Matrix r m ℝ × Matrix r n ℝ),
      (updateNewest B' s).blocks.tail = rest
        ∧ rest.length = bs.length := by
  simp [updateNewest, hs]

/-- Стоимость состояния не меняется при обновлении блока. -/
theorem updateNewest_cost (B' : Matrix r n ℝ) (s : LiveDelta m n r) :
    (updateNewest B' s).blocks.length
      * (Fintype.card r * (Fintype.card m + Fintype.card n))
      = s.blocks.length
        * (Fintype.card r * (Fintype.card m + Fintype.card n)) := by
  rw [updateNewest_length]

/-! ## Часть 1: окно SafeQP в фактор-пространстве -/

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {K : Type*} [Fintype K] [Nonempty K]

/-- **Окно безопасного обновления**: если d — направление в
фактор-пространстве (ненулевое), η в окне safeqpEtaMax, и для
каждого защищаемого домена i справедлива линейная оценка
изменения потерь (h_emp_-посылка), то после шага
θ ↦ θ − η•d по фактору каждый домен остаётся в бюджете ε_i. -/
theorem safe_update_window (g : K → X) (eps L : K → ℝ)
    (d : X) (dL : K → ℝ) (eta : ℝ)
    (hL : ∀ i, 0 < L i) (heps : ∀ i, 0 ≤ eps i) (heta : 0 ≤ eta)
    (hd : d ≠ 0)
    (h_lipline : ∀ i, dL i ≤ -eta * ⟪g i, d⟫_ℝ
      + L i * eta * eta * ‖d‖ ^ 2 / 2)
    (h_eta : eta ≤ safeqpEtaMax g eps L d) :
    ∀ i, dL i ≤ eps i :=
  safeqp_eta_max g eps L d dL eta hL heps heta hd h_lipline h_eta

end Hagi.LiveDeltaSafe
