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
- **C592 (нелинейное расширение, секция SmoothNL)**: абстрактный
  L-smooth objective + GD с равным бюджетом — CERTIFIED
  SUFFICIENT-граница (не iff): `smooth_obj_transfer_bound`
  (двусторонняя: финал зажат стартом ± n•`nlBudget`),
  `sufficient_negative_transfer` (стартовый запас > n•`nlBudget` ⇒
  warm хуже после n шагов). Негатив-инстанс (рациональные
  константы): достаточность ≠ необходимость — см. honest pins.

## Honest pins (что этот модуль НЕ покрывает)

- **Только квадратичный мир — ТОЧНАЯ iff-граница** (C572-секция
  Quad): нелинейные objectives — точной iff нет; в C592-секции
  SmoothNL — только консервативная certified-достаточность
  (sufficient, НЕ necessary — негатив-инстанс .tmp/C592/trajNL.lean
  показывает случай «условие не выполнено, но warm всё равно
  хуже»); там же — bench-эмпирика.
- **t̂ — гипотеза**: decision-правило использует ЦЕЛЬ B; на
  практике цель неизвестна до обучения — правило требует оценки
  t̂ (pre-registered closeness unified.py:156 — её эвристика).
- **Внутренний продукт**: θ живёт в пространстве той же
  размерности, что и цель ( EuclideanSpace ℝ n); реальный
  adapter-слот — матрицы (r×d, d×r) — вкладывается тривиально
  (vec), но statement векторное.
-/

set_option relaxedAutoImplicit false

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

/-! ## C592: нелинейное расширение — L-smooth sufficient-граница -/

section SmoothNL

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Нелинейный certified-GD-шаг с постоянным шагом γ по
градиентному полю `grad` (абстрактный objective; квадратичный
случай C572 — `gdStep` = `nlStep` при `grad = 2•(·−t)`). -/
def nlStep {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (γ : ℝ) (grad : F → F) (z : F) : F := z - γ • grad z

/-- Равный бюджет: n нелинейных certified-GD-шагов от старта z. -/
def nlRun {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (γ : ℝ) (grad : F → F) (z : F) : F :=
  (nlStep γ grad)^[n] z

/-- Per-step бюджет certified-убывания для L-smooth objective с
градиентной G-границей: C-S-член γG² + smoothness-член Lγ²G²/2
(двусторонняя descent-композиция; консервативная). -/
noncomputable def nlBudget (γ L G : ℝ) : ℝ := γ * G ^ 2 + L * γ ^ 2 * G ^ 2 / 2

/-- Per-step коэффициент descent-леммы неотрицателен при
`0 < γ ≤ 2 / L`, `L > 0` — шаг GD не увеличивает objective. -/
theorem nl_coef_nonneg (L γ : ℝ) (_hγ : 0 < γ) (hγL : γ ≤ 2 / L)
    (hL : 0 < L) : 0 ≤ 1 - L * γ / 2 := by
  have h := (le_div_iff₀ hL).mp hγL
  have h2 : L * γ ≤ 2 := by linarith
  linarith

/-- **nl_step_mono (C592)**: при `0 < γ ≤ 2/L` GD-шаг по
L-smooth полю (premise-form `hsm`, как `gd_drift_lemma`-конвенция
репо) не увеличивает objective — descent-лемма с неотрицательным
коэффициентом (схема Unified/StochasticCELearning.gd_drift_lemma;
  Theory-слой не импортирует Unified — LayerLint). -/
theorem nl_step_mono (f : E → ℝ) (grad : E → E) (L γ : ℝ)
    (hγ : 0 < γ) (hγL : γ ≤ 2 / L) (hL : 0 < L) (z : E)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2) :
    f (nlStep γ grad z) ≤ f z := by
  have hdef : nlStep γ grad z = z - γ • grad z := rfl
  rw [hdef]
  have hstep := hsm z (z - γ • grad z)
  have hin : ⟪grad z, z - γ • grad z - z⟫_ℝ = -(γ) * ‖grad z‖ ^ 2 := by
    rw [show z - γ • grad z - z = -(γ • grad z) by module,
      inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hnorm : ‖z - γ • grad z - z‖ ^ 2 = γ ^ 2 * ‖grad z‖ ^ 2 := by
    rw [show z - γ • grad z - z = -(γ • grad z) by module,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hγ, mul_pow]
  rw [hin, hnorm] at hstep
  have hc := nl_coef_nonneg L γ hγ hγL hL
  have hnn : 0 ≤ ‖grad z‖ ^ 2 := sq_nonneg _
  nlinarith [hstep, hγ, hL, hc, hnn]

/-- **nl_step_lower (C592)**: per-step убывание ограничено снизу
бюджетом `nlBudget γ L G` — descent-лемма в точке next + C-S +
локальные G-границы градиента (в `z` и в next). -/
theorem nl_step_lower (f : E → ℝ) (grad : E → E) (L γ G : ℝ)
    (hγ : 0 < γ) (hL : 0 < L) (z : E)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (hGz : ‖grad z‖ ≤ G)
    (hGn : ‖grad (nlStep γ grad z)‖ ≤ G) :
    f z - nlBudget γ L G ≤ f (nlStep γ grad z) := by
  have hstep2 := hsm (nlStep γ grad z) z
  have hin2 : ⟪grad (nlStep γ grad z), z - nlStep γ grad z⟫_ℝ
      = γ * ⟪grad (nlStep γ grad z), grad z⟫_ℝ := by
    rw [show z - nlStep γ grad z = γ • grad z by
        unfold nlStep; module, inner_smul_right]
  have hnorm2 : ‖z - nlStep γ grad z‖ ^ 2 = γ ^ 2 * ‖grad z‖ ^ 2 := by
    rw [show z - nlStep γ grad z = γ • grad z by
        unfold nlStep; module, norm_smul, Real.norm_eq_abs,
      abs_of_pos hγ, mul_pow]
  rw [hin2, hnorm2] at hstep2
  set w := nlStep γ grad z with hw
  have hcs : ⟪grad w, grad z⟫_ℝ ≤ G ^ 2 := by
    have h1 := abs_real_inner_le_norm (grad w) (grad z)
    have h5 : |⟪grad w, grad z⟫_ℝ| ≤ G ^ 2 := by
      calc |⟪grad w, grad z⟫_ℝ| ≤ ‖grad w‖ * ‖grad z‖ := h1
        _ ≤ G * G := mul_le_mul hGn hGz (norm_nonneg (grad z))
            (le_trans (norm_nonneg (grad z)) hGz)
        _ = G ^ 2 := by ring
    exact (abs_le.1 h5).2
  have hb : ‖grad z‖ ^ 2 ≤ G ^ 2 := by
    have h6 := mul_self_le_mul_self (norm_nonneg (grad z)) hGz
    nlinarith [h6]
  unfold nlBudget
  have hγcs : γ * ⟪grad w, grad z⟫_ℝ ≤ γ * G ^ 2 :=
    mul_le_mul_of_nonneg_left hcs (le_of_lt hγ)
  have hLb : L / 2 * (γ ^ 2 * ‖grad z‖ ^ 2)
      ≤ L / 2 * (γ ^ 2 * G ^ 2) := by
    have hg2 : γ ^ 2 * ‖grad z‖ ^ 2 ≤ γ ^ 2 * G ^ 2 := by
      nlinarith [hb, sq_nonneg γ]
    exact mul_le_mul_of_nonneg_left hg2 (by positivity)
  nlinarith [hstep2, hγcs, hLb]

/-- **nl_obj_le_start (C592)**: при `0 < γ ≤ 2/L` равный бюджет
n GD-шагов не увеличивает objective (monotone-индукция по n) —
финал любого старта ≤ старту. -/
theorem nl_obj_le_start (f : E → ℝ) (grad : E → E) (L γ : ℝ)
    (hγ : 0 < γ) (hγL : γ ≤ 2 / L) (hL : 0 < L) (n : ℕ) (z : E)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2) :
    f (nlRun n γ grad z) ≤ f z := by
  induction n generalizing z with
  | zero => simp [nlRun]
  | succ n ih =>
      have hmono := nl_step_mono f grad L γ hγ hγL hL z hsm
      have hih := @ih (nlStep γ grad z)
      have heq : nlRun (n + 1) γ grad z
          = nlRun n γ grad (nlStep γ grad z) := by
        unfold nlRun
        exact Function.iterate_succ_apply _ _ _
      rw [heq]
      exact le_trans hih hmono

/-- **nl_obj_ge_budget (C592)**: телескоп-индукция — при
градиентной G-границе вдоль траектории финал ≥ старт −
n•`nlBudget` (per-step убывание ограничено бюджетом). -/
theorem nl_obj_ge_budget (f : E → ℝ) (grad : E → E) (L γ G : ℝ)
    (hγ : 0 < γ) (hL : 0 < L) (n : ℕ) (z : E)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (hG : ∀ k, k ≤ n → ‖grad (nlRun k γ grad z)‖ ≤ G) :
    f z - n * nlBudget γ L G ≤ f (nlRun n γ grad z) := by
  revert hG
  induction n generalizing z with
  | zero => intro _; simp [nlRun]
  | succ n ih =>
      intro hG
      -- под-траектория: сдвиг hG на единицу
      have hG' : ∀ k, k ≤ n →
          ‖grad (nlRun k γ grad (nlStep γ grad z))‖ ≤ G := by
        intro k hk
        have h3 : nlRun k γ grad (nlStep γ grad z)
            = nlRun (k + 1) γ grad z := by
          unfold nlRun
          rw [Function.iterate_succ]
          rfl
        rw [h3]
        exact hG (k + 1) (by omega)
      have hstep := nl_step_lower f grad L γ G hγ hL z hsm
        (hG 0 (by omega))
        (by
          have h1 : nlStep γ grad z = nlRun 1 γ grad z := by
            unfold nlRun; simp
          rw [h1]
          exact hG 1 (by omega))
      have hih := @ih (nlStep γ grad z) hG'
      have heq : nlRun (n + 1) γ grad z
          = nlRun n γ grad (nlStep γ grad z) := by
        unfold nlRun
        exact Function.iterate_succ_apply _ _ _
      rw [heq]
      push_cast
      nlinarith [hstep, hih]

/-- **smooth_obj_transfer_bound (C592, MAIN)**: для L-smooth
objective (premise-form `hsm`) с градиентной G-границей вдоль
траектории (`hG`: ∀ k ≤ n) после n GD-шагов финал зажат
стартом ± бюджет: `f z − n•nlBudget ≤ f (nlRun n z) ≤ f z`.
Квадратичный аналог (C572) точнее: там граница не зазорена; здесь
— консервативная certified-двусторонность для ЛЮБОГО smooth obj. -/
theorem smooth_obj_transfer_bound (f : E → ℝ) (grad : E → E)
    (L γ G : ℝ) (hγ : 0 < γ) (hγL : γ ≤ 2 / L) (hL : 0 < L)
    (n : ℕ) (z : E)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (hG : ∀ k, k ≤ n → ‖grad (nlRun k γ grad z)‖ ≤ G) :
    f z - n * nlBudget γ L G ≤ f (nlRun n γ grad z)
      ∧ f (nlRun n γ grad z) ≤ f z := by
  have hle := nl_obj_le_start f grad L γ hγ hγL hL n z hsm
  have hlow := nl_obj_ge_budget f grad L γ G hγ hL n z hsm hG
  exact ⟨hlow, hle⟩

/-- **sufficient_negative_transfer (C592)**: CERTIFIED
SUFFICIENT-условие негативного переноса для L-smooth objective:
если стартовый запас warm (`f θA − f 0`, θA — скопированный слот
A) больше бюджета `n • nlBudget`, то после РАВНОГО бюджета n
GD-шагов warm СТРОГО хуже cold. КОНСЕРВАТИВНО: НЕ iff —
границы start→finish для нелинейных obj не точны; обратная
импликация ЛОЖНА (негатив-инстанс .tmp/C592/trajNL.lean:условие не выполнено, но warm всё равно хуже). Квадратичный
мир — точная iff `neg_transfer_char` (C572). -/
theorem sufficient_negative_transfer (f : E → ℝ) (grad : E → E)
    (L γ G : ℝ) (hγ : 0 < γ) (hγL : γ ≤ 2 / L) (hL : 0 < L)
    (n : ℕ) (θA : E)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (hGw : ∀ k, k ≤ n → ‖grad (nlRun k γ grad θA)‖ ≤ G)
    (hGc : ∀ k, k ≤ n → ‖grad (nlRun k γ grad 0)‖ ≤ G)
    (hd : f θA - f 0 > n * nlBudget γ L G) :
    f (nlRun n γ grad θA) > f (nlRun n γ grad 0) := by
  have hlow := smooth_obj_transfer_bound f grad L γ G hγ hγL hL n θA
    hsm hGw
  have hle := smooth_obj_transfer_bound f grad L γ G hγ hγL hL n 0
    hsm hGc
  linarith

end SmoothNL

end Hagi.Theory.NegativeTransfer
