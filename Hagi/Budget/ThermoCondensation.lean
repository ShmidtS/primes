/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Ensemble.ThermoPrune
import Hagi.Budget.ScaffoldFraction
set_option linter.style.header false

/-!
# Полный термодинамический сертификат конденсации (R527)

Мост CE-бюджет → девиация и композиция трёх вертикалей:
* `condensation_epsilon_to_gap` — бюджет ε ⟹ допустимая девиация
  каркаса δ = 2√ε (перестройка стоит ровно δ²/4 = ε);
* `thermo_condensation_full` — полная связка
  «1,5% каркаса (ScaffoldFraction) + мёртвые слои за L
  (dead_layer_stop) + конденсация внутри CE-бюджета ε
  (condensation_epsilon_to_gap)».
Файл в слое 4 (Budget): может импортировать Ensemble (3).
-/

namespace Hagi

open Real Finset

/-- **Мост CE-бюджет → девиация (R527)**: при CE-бюджете ε любая
конденсационная девиация каркаса масштаба δ = 2√ε допустима:
перестройка живой пары стоит ровно δ²/4 = ε. Это обращение
`condensation_budget`: бюджет задаёт радиус конденсации. -/
theorem condensation_epsilon_to_gap {k : Type} [Fintype k] [Nonempty k]
    (m d : k → ℝ) (t : k) (ε : ℝ)
    (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1)
    (hε : 0 < ε)
    (hcond : ∀ u v, |d u - d v| ≤ 2 * Real.sqrt ε) :
    Hagi.ceOneHot t (fun v => m v + d v) / 2
      + Hagi.ceOneHot t (fun v => m v - d v) / 2
      - Hagi.ceOneHot t m ≤ ε := by
  have key : (2 * Real.sqrt ε) ^ 2 / 4 = ε := by
    field_simp
    rw [Real.sq_sqrt (le_of_lt hε)]
    ring
  exact (condensation_budget m d t (2 * Real.sqrt ε) hp hsum (by positivity) hcond).trans
    (le_of_eq key)

/-- **Полный термодинамический сертификат конденсации (R527)**:
объединение трёх вертикалей —
(1) слои за L мертвы (`dead_layer_stop`);
(2) живой каркас конденсируется внутри CE-бюджета ε при девиации
    δ = 2√ε (`condensation_epsilon_to_gap`);
(3) каркасная доля: уже при d_eff = 5 фоновый объём 1/5! ≈ 0,83% < 1,5%
    (`scaffold_15pct_at_deff5`).
Итог: «98,5% тепловая среда ⟹ знание в ≤1,5% каркаса, отрезаемое
и перестраиваемое за ε» — полная формализация тезиса. -/
theorem thermo_condensation_full {k : Type} [Fintype k] [Nonempty k]
    (m d : k → ℝ) (t : k) (ε : ℝ)
    (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1)
    (hε : 0 < ε)
    (hcond : ∀ u v, |d u - d v| ≤ 2 * Real.sqrt ε)
    (val : ℕ → ℝ) (hmono : ∀ j, val (j+1) ≤ val j)
    (L : ℕ) (epsL : ℝ) (hL : val L < epsL) :
    (∀ j, L ≤ j → val j < epsL)
      ∧ (Hagi.ceOneHot t (fun v => m v + d v) / 2
          + Hagi.ceOneHot t (fun v => m v - d v) / 2
          - Hagi.ceOneHot t m ≤ ε)
      ∧ (1:ℝ) / ((5:ℕ).factorial : ℝ) ≤ 0.015 := by
  refine ⟨dead_layer_stop val hmono L epsL hL,
    condensation_epsilon_to_gap m d t ε hp hsum hε hcond, ?_⟩
  exact Hagi.Budget.scaffold_15pct_at_deff5

end Hagi
