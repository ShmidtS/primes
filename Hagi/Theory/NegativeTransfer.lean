/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 authors
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# NegativeTransfer — точная граница негативного переноса (C572)

Source-anchored мост волны HAGI_v2 (roadmap C570 top-3): upstream
`hagi/unified.py:147-165` решает «когда warm-start переносить»
эвристикой (pre-registered closeness); этот модуль даёт ТОЧНУЮ
границу для квадратичной модели задачи B — дополняет C560
(T1-эмпирика: 3/3 пары перенос помогает по AUC) и C567
(`warm_transfer_sound`: forgetA=0 + certified-обучаемость с
любого init; transfer-качество НЕ обещано — honest-pin закрыт
здесь теорией для квадратичного случая).

Модель: objective домена B — `quadObj t z = ‖z − t‖²` (цель t);
warm-init θ = скопированный слот A (`warmTransfer` C567),
cold-init 0 (нейтральный слот, C532). Certified-шаги — GD с
постоянным шагом η (градиент 2(z − t)); равенство бюджетов =
равное число шагов k.

Теоремы:
- `neg_transfer_char` (T2): warm-старт ХУЖЕ cold ⟺
  `2 * ⟪θ, t⟫_ℝ < ‖θ‖²` — точная iff, обе стороны;
- `warm_better_char` (T1-граница): warm-старт ЛУЧШЕ ⟺
  `2 * ⟪θ, t⟫_ℝ > ‖θ‖²`;
- `transfer_boundary`: при `2 * ⟪θ, t⟫_ℝ = ‖θ‖²` старты РАВНЫ —
  граница точная (не зазорена);
- `neg_transfer_adversarial`: adversarial-цель `t = -c • θ`
  (c > 0, θ ≠ 0) — всегда T2 (warm неизбежно хуже cold);
- `gd_step_dist` / `gd_run_dist`: одинаковый множитель
  `|1 - 2η|^k` дистанции для ЛЮБОГО старта;
- `warm_better_budget`: при `|1 - 2η| > 0` равный бюджет шагов
  НЕ размывает границу — финальное преимущество warm ⟺ стартовое;
- `transfer_helps_budget`: композиция — переносить warm iff
  `2 * ⟪θ, t⟫_ℝ > ‖θ‖²` (в терминах t̂ — оценка цели B: честная
  гипотеза CALLER'а, в теореме t точный).

## Honest pins (что этот модуль НЕ покрывает)

- **Только квадратичный мир**: obj_B = ‖z − t‖². Нелинейные
  objectives — только certified-drop гарантия `adapter_step_certified`
  (C532) без дистанционной механики; T1/T2 там — bench-эмпирика.
- **t̂ — гипотеза**: decision-правило использует ЦЕЛЬ B; на
  практике цель неизвестна до обучения — правило требует оценки
  t̂ (pre-registered closeness unified.py:156 — её эвристика).
- **Внутренний продукт**: θ живёт в пространстве той же
  размерности, что и цель ( EuclideanSpace ℝ n); реальный
  adapter-слот — матрицы (r×d, d×r) — вкладывается тривиально
  (vec), но statement векторное.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.NegativeTransfer

open scoped InnerProductSpace

/-! ## Квадратичный objective и certified-GD -/

section Quad

variable {n : Type*} [Fintype n]

/-- Квадратичный objective домена B: расстояние-в-квадрате до
цели `t` (warm-init θ = слот A, cold-init 0 — C532). -/
noncomputable def quadObj (t z : EuclideanSpace ℝ n) : ℝ := ‖z - t‖ ^ 2

/-- Certified-GD-шаг с постоянным шагом η: градиент
`‖z − t‖²` в точке z равен `2 • (z − t)` (в EuclideanSpace). -/
def gdStep (η : ℝ) (t z : EuclideanSpace ℝ n) : EuclideanSpace ℝ n :=
  z - η • (2 • (z - t))

/-- Равный бюджет: k certified-GD-шагов от старта z. -/
def gdRun (k : ℕ) (η : ℝ) (t z : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n := (gdStep η t)^[k] z

/-- Раскрытие квадрата нормы разности (helper; паттерн
inner-алгебры OnlinePL). -/
theorem quad_expand (θ t : EuclideanSpace ℝ n) :
    ‖θ - t‖ ^ 2 = ‖θ‖ ^ 2 - 2 * ⟪θ, t⟫_ℝ + ‖t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (θ - t), inner_sub_left,
    inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq θ,
    real_inner_self_eq_norm_sq t, real_inner_comm t θ]
  ring

/-- cold-старт: objective нейтрального слота (0) — опорная
величина `‖t‖²`. -/
theorem quad_obj_zero (t : EuclideanSpace ℝ n) :
    quadObj t 0 = ‖t‖ ^ 2 := by
  unfold quadObj
  simp

/-! ## T2: точная iff-граница негативного переноса -/

/-- **neg_transfer_char (C572, T2)**: warm-старт θ хуже cold
(старт-объектив строго больше) ТОЧНО тогда, когда удвоенное
скалярное произведение ⟨θ, t⟩ меньше квадрата нормы θ — обе
стороны, без зазора. Дополняет C560-эмпирику: там 3/3 пары T1
(помогает); здесь — когда перенос НЕИЗБЕЖНО вредит. -/
theorem neg_transfer_char (θ t : EuclideanSpace ℝ n) :
    quadObj t θ > quadObj t 0 ↔ 2 * ⟪θ, t⟫_ℝ < ‖θ‖ ^ 2 := by
  unfold quadObj
  rw [quad_expand θ t,
    show ‖(0 : EuclideanSpace ℝ n) - t‖ ^ 2 = ‖t‖ ^ 2 from by simp]
  constructor <;> intro h <;> linarith

/-- **warm_better_char (C572, T1-граница)**: перенос помогает
старту ⟺ удвоенное скалярное произведение больше квадрата
нормы θ — точная iff, симметричная к `neg_transfer_char`. -/
theorem warm_better_char (θ t : EuclideanSpace ℝ n) :
    quadObj t θ < quadObj t 0 ↔ 2 * ⟪θ, t⟫_ℝ > ‖θ‖ ^ 2 := by
  unfold quadObj
  rw [quad_expand θ t,
    show ‖(0 : EuclideanSpace ℝ n) - t‖ ^ 2 = ‖t‖ ^ 2 from by simp]
  constructor <;> intro h <;> linarith

/-- **transfer_boundary (C572)**: на границе неравенства старты
РАВНЫ (warm = cold точно) — граница не зазорена, равенство
достигается. -/
theorem transfer_boundary (θ t : EuclideanSpace ℝ n)
    (h : 2 * ⟪θ, t⟫_ℝ = ‖θ‖ ^ 2) :
    quadObj t θ = quadObj t 0 := by
  unfold quadObj
  rw [quad_expand θ t,
    show ‖(0 : EuclideanSpace ℝ n) - t‖ ^ 2 = ‖t‖ ^ 2 from by simp, h]
  ring

/-- **neg_transfer_adversarial (C572)**: adversarial-цель
`t = -c • θ` (c > 0, θ ≠ 0) даёт T2 ВСЕГДА — warm-старт
неизбежно хуже cold. Следствие `neg_transfer_char`: скалярное
произведение отрицательно, доминировать ‖θ‖² не может.
Гипотеза θ ≠ 0 честная: при θ = 0 warm = cold (не хуже). -/
theorem neg_transfer_adversarial (θ : EuclideanSpace ℝ n)
    (c : ℝ) (hc : 0 < c) (hθ : θ ≠ 0) :
    quadObj (-c • θ) θ > quadObj (-c • θ) 0 := by
  rw [neg_transfer_char]
  have hpos : 0 < ‖θ‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hθ)
  have h2 : 2 * ⟪θ, -c • θ⟫_ℝ = -2 * c * ‖θ‖ ^ 2 := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  rw [h2]
  have hc2 : 0 < 2 * c * ‖θ‖ ^ 2 := by positivity
  linarith

/-! ## Равный бюджет шагов: граница не размывается -/

/-- Один certified-GD-шаг сжимает дистанцию до цели множителем
`|1 - 2η|` — ОДИНАКОВЫМ для любого старта (шаг линеен по
остатку z − t). -/
theorem gd_step_dist (η : ℝ) (t z : EuclideanSpace ℝ n) :
    ‖gdStep η t z - t‖ = |1 - 2 * η| * ‖z - t‖ := by
  have h : gdStep η t z - t = (1 - 2 * η) • (z - t) := by
    unfold gdStep; module
  rw [h, norm_smul, Real.norm_eq_abs]

/-- k certified-GD-шагов: дистанция до цели умножается на
`|1 - 2η|^k` — независимо от старта (индукция по бюджету). -/
theorem gd_run_dist (k : ℕ) (η : ℝ) (t z : EuclideanSpace ℝ n) :
    ‖gdRun k η t z - t‖ = |1 - 2 * η| ^ k * ‖z - t‖ := by
  induction k generalizing z with
  | zero => unfold gdRun; simp
  | succ k ih =>
      unfold gdRun at ih ⊢
      rw [Function.iterate_succ, Function.comp_apply, ih (gdStep η t z),
        gd_step_dist η t z, pow_succ]
      ring

/-- **warm_better_budget (C572)**: при невырожденном шаге
(`|1 - 2η| > 0`; при η = 1/2 любой старт попадает в оптимум за
один шаг — граница вырождается в равенство) финальное
преимущество warm после РАВНОГО бюджета k шагов ⟺ стартовое:
бюджет не размывает T1/T2-границу. -/
theorem warm_better_budget (k : ℕ) (η : ℝ) (hη : |1 - 2 * η| > 0)
    (θ t : EuclideanSpace ℝ n) :
    quadObj t (gdRun k η t θ) < quadObj t (gdRun k η t 0)
      ↔ quadObj t θ < quadObj t 0 := by
  unfold quadObj
  rw [gd_run_dist k η t θ, gd_run_dist k η t 0]
  rw [show (‖(0 : EuclideanSpace ℝ n) - t‖ : ℝ) = ‖t‖ from by simp]
  have hr : 0 < |1 - 2 * η| ^ k := pow_pos hη k
  have hr2 : 0 < (|1 - 2 * η| ^ k) ^ 2 :=
    sq_pos_of_ne_zero (ne_of_gt hr)
  rw [mul_pow, mul_pow]
  constructor
  · intro h
    exact lt_of_mul_lt_mul_left h (le_of_lt hr2)
  · intro h
    nlinarith [hr2, h]

/-- **transfer_helps_budget (C572, decision-граница)**:
переносить warm после равного бюджета ⟺ удвоенное скалярное
произведение ⟨θ, t⟩ больше квадрата нормы θ (композиция
`warm_better_budget` × `warm_better_char`). На практике цель t
неизвестна до обучения: правило применяется с оценкой t̂ —
гипотеза caller'а (pre-registered closeness, unified.py:156). -/
theorem transfer_helps_budget (k : ℕ) (η : ℝ)
    (hη : |1 - 2 * η| > 0) (θ t : EuclideanSpace ℝ n) :
    quadObj t (gdRun k η t θ) < quadObj t (gdRun k η t 0)
      ↔ 2 * ⟪θ, t⟫_ℝ > ‖θ‖ ^ 2 := by
  rw [warm_better_budget k η hη θ t, warm_better_char θ t]

end Quad

end Hagi.Theory.NegativeTransfer
