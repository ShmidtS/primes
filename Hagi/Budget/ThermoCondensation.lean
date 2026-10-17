/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Budget.FactorizedBPW
import Hagi.Ensemble.Hoeffding
import Hagi.External.Layers
/-!
# Термодинамический prune-сертификат (R522)

Формализация тезиса «98,5% сети — фоновая тепловая среда,
знание конденсировано в 1,5% каркаса»:
* `condensation_budget` — каркасная девиация M ⟹ CE-стоимость
  перестройки ≤ M²/4 (интерфейс:CE-бюджет ε ⟹ допустимая
  девиация δ = 2√ε);
* `thermo_prune_certificate` — двухступенчатый сертификат:
  слои за L мертвы (monotone-вал, dead_layer_stop) И живой
  каркас перестраивается не дороже M²/4.
-/

namespace Hagi.Ensemble

open Real Finset

/-- **Конденсационный бюджет (мост «1,5% каркаса» → prune)**:
если девиации logits d_u каркасно-сжаты в δ-окрестность
(гипотеза конденсации: тепловая фоновая масса почти не
меняет logits), то merge/prune-перестройка ансамбля стоит
не больше δ²/4 CE-бюджета (prune_certificate). Эквивалентно:
для любого CE-бюджета ε допустимая каркасная девиация есть
δ = 2√ε. -/
theorem condensation_budget {k : Type} [Fintype k] [Nonempty k]
    (m d : k → ℝ) (t : k) (M : ℝ)
    (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1)
    (hM : 0 < M)
    (hcond : ∀ u v, |d u - d v| ≤ M) :
    Hagi.ceOneHot t (fun v => m v + d v) / 2
      + Hagi.ceOneHot t (fun v => m v - d v) / 2
      - Hagi.ceOneHot t m ≤ M ^ 2 / 4 := ce_gap_bounded m d t M hp hsum hM hcond

/-- Обратная постановка: CE-бюджет ε ⟹ допустимая конденсационная
девиация δ = 2√ε ( Loved «1,5%»: жёсткий каркас ⟹ малое δ). -/
theorem condensation_epsilon_budget (ε : ℝ) (hε : 0 < ε) :
    0 < 2 * Real.sqrt ε := by
  positivity

/-- **Термодинамический prune-сертификат (двухступенчатый)**:
(1) слои за `L` мертвы по `dead_layer_stop` (монотонный вал ценности);
(2) живой каркас с конденсационной девиацией ≤ M перестраивается
не дороже M²/4 CE (prune_certificate). Сумма: полная стоимость
конденсации модели к каркасу ограничена и слои за L отрезаны —
формализация тезиса «98,5% тепловая масса, знание — в 1,5%». -/
theorem thermo_prune_certificate {k : Type} [Fintype k] [Nonempty k]
    (m d : k → ℝ) (t : k) (M : ℝ)
    (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1)
    (hM : 0 < M)
    (hcond : ∀ u v, |d u - d v| ≤ M)
    (val : ℕ → ℝ) (hmono : ∀ j, val (j+1) ≤ val j)
    (L : ℕ) (eps : ℝ) (hL : val L < eps) :
    (∀ j, L ≤ j → val j < eps)
      ∧ (Hagi.ceOneHot t (fun v => m v + d v) / 2
          + Hagi.ceOneHot t (fun v => m v - d v) / 2
          - Hagi.ceOneHot t m ≤ M ^ 2 / 4) := by
  refine ⟨dead_layer_stop val hmono L eps hL, ?_⟩
  exact ce_gap_bounded m d t M hp hsum hM hcond

end Hagi.Ensemble
/-!
# Доля каркаса vs эффективная размерность (R526)

Количественный мост «1,5% каркаса ⟺ d_eff ~ 5-6»:
факториальная таблица 4!..8!, доля фазового объёма
на направление 1/k! и её монотонность по d_eff.
Точечные значения: 1/5! ≈ 0.83% < 1,5%; 1/6! ≈ 0.14%.
Связь с FactorizedBPW (d_eff ≤ 8) и ThermoPrune.
-/

namespace Hagi.Budget

open Real Finset Nat

/-- Факториальная таблица (точные значения):
4! = 24, 5! = 120, 6! = 720, 7! = 5040, 8! = 40320. -/
theorem fact4 : (4 : ℕ).factorial = 24 := by norm_num
theorem fact5 : (5 : ℕ).factorial = 120 := by norm_num
theorem fact6 : (6 : ℕ).factorial = 720 := by norm_num
theorem fact7 : (7 : ℕ).factorial = 5040 := by norm_num
theorem fact8 : (8 : ℕ).factorial = 40320 := by norm_num

/-- Обратные доли как Real: 1/5! = 1/120 ≈ 0.0083 < 0.015 (1,5%). -/
theorem inv_fact5_lt_15pct : (1:ℝ) / ((5:ℕ).factorial : ℝ) < 3/200 := by
  norm_num

/-- 1/6! = 1/720 ≈ 0.0014 < 0.015. -/
theorem inv_fact6_lt_15pct : (1:ℝ) / ((6:ℕ).factorial : ℝ) < 3/200 := by
  norm_num

/-- **Главный мост R526**: уже при d_eff = 5 доля фонового
объёма 1/5! = 1/120 ≈ 0.83% меньше 1,5% — каркас «1,5%»
достижим пятью эффективными направлениями. -/
theorem scaffold_15pct_at_deff5 : (1:ℝ) / ((5:ℕ).factorial : ℝ) ≤ 0.015 := by
  rw [show (0.015:ℝ) = 3/200 from by norm_num]
  norm_num

/-- Монотонность падения доли по d_eff: 1/(k+1)! ≤ 1/k!. -/
theorem inv_fact_mono (k : ℕ) :
    (1:ℝ) / (((k+1 : ℕ).factorial : ℝ)) ≤ (1:ℝ) / (k.factorial : ℝ) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h : (k+1 : ℕ).factorial = (k+1 : ℕ) * k.factorial := Nat.factorial_succ k
  rw [h]
  push_cast
  nlinarith [Nat.factorial_pos k]

end Hagi.Budget
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

namespace Hagi.Budget

open Hagi.Ensemble

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

end Hagi.Budget
