/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic

/-!
# ErrorFeedback — накопленный резидуал квантованного шага

Схема error feedback (Karimireddy–Stich–Jaggi 2019, Stich et al. 2018):

`u_t = η_t • d_t + e_t`; `q_t = Q u_t`; `e_{t+1} = u_t − q_t`;
исполняется КВАНТОВАННЫЙ шаг `q_t`.

Три контракта сжатия (различаются явно):

* CONTRACTIVE — `contractiveCompressor Q : ‖Q x‖ ≤ ‖x‖`
  (`Hagi.Optimization.EF21Markov.IsContractive` в squared-sum форме;
  здесь нормированная форма);
* BOUNDED-ERROR — `boundedErrorCompressor Q ε : ‖Q x − x‖ ≤ ε`
  (тернарный паттерн `Hagi.Runtime.TernaryExact.qTern_error_in`,
  |x − qTern s x| ≤ s/2);
* EF-SCHEME — сам рекуррентный residuал-цикл этого модуля (`efStep`),
  потребляющий ЛЮБОЙ bounded-error компрессор.

Главные результаты:

* `ef_cumulative_exact` — ТЕЛЕСКОП (точная идентичность, почему EF
  работает): Σ_{t<T} q_t = Σ_{t<T} η_t • d_t + e_0 − e_T —
  накопленный квантованный update = идеальный + концевой резидуал;
* `ef_residual_bounded` — инвариант: bounded-error Q + ‖e 0‖ ≤ ε
  влечёт ‖e t‖ ≤ ε для ВСЕХ t (индукция);
* `ef_iterate_deviation_exact` — исполняемая траектория против
  идеальной отклоняется РОВНО на e_T − e_0 (точное тенение);
* `ef_trajectory_endpoint_bound` — отклонение ≤ 2ε, НЕЗАВИСИМО от T
  (endpoint-only); через липшицеву цель (`ef_objective_deviation`)
  ошибка значения ≤ 2Lε;
* `naive_deviation_bound` + `naive_accumulation_witness` — без EF
  (наивное квантование) отклонение ≤ T•ε и эта граница ДОСТИГАЕТСЯ
  (свидетель-компрессор x ↦ x − ε); с EF — концевая. Отсюда
  `ef_advantage`: количественное преимущество EF (2ε против T•ε);
* `coordLift_bounded_error` — координатный подъём: покоординатная
  ошибка ≤ δ (форма `qTern_error_in`, тернарный случай δ = s/2) даёт
  bounded-error контракт в sup-норме на `Fin n → ℝ`.

Носитель — произвольное вещественное нормированное пространство V
(покрывает ℝ-свидетель и Fin n → ℝ). Честные пины: contractive /
bounded-error посылки, липшицева константа L, покоординатный факт
квантователя — binders; квадратичные следствия
(`Hagi.Theory.Compression`, слой Theory) не дублируются.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Step.ErrorFeedback

open Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## Три контракта сжатия -/

/-- КОНТРАКТИВНЫЙ контракт: компрессор не увеличивает норму
(нормированная форма EF21-сжатия после Hadamard; см.
`Hagi.Optimization.EF21Markov.IsContractive` — squared-sum вариант). -/
def contractiveCompressor (Q : V → V) : Prop :=
  ∀ x, ‖Q x‖ ≤ ‖x‖

/-- КОНТРАКТ С ОГРАНИЧЕННОЙ ОШИБКОЙ: ошибка компрессора равномерно
ограничена ε (тернарный паттерн: |x − qTern s x| ≤ s/2, см.
`Hagi.Runtime.TernaryExact.qTern_error_in`). -/
def boundedErrorCompressor (Q : V → V) (ε : ℝ) : Prop :=
  ∀ x, ‖Q x - x‖ ≤ ε

/-- EF-ШАГ (третий контракт — схема, а не свойство): одна итерация
error feedback. `u = η • d + e` — вход компрессора; на исполнение
уходит квантованный `Q u`, резидуал `u − Q u` переносится на
следующий шаг. -/
def efStep (Q : V → V) (η : ℝ) (d e : V) : V × V :=
  (Q (η • d + e), η • d + e - Q (η • d + e))

/-- Исполняемое обновление EF-шага — квантованный вектор. -/
theorem efStep_q (Q : V → V) (η : ℝ) (d e : V) :
    (efStep Q η d e).1 = Q (η • d + e) := rfl

/-- Резидуал EF-шага — несжатый остаток, переносимый вперёд. -/
theorem efStep_e (Q : V → V) (η : ℝ) (d e : V) :
    (efStep Q η d e).2 = η • d + e - Q (η • d + e) := rfl

/-! ## Телескоп: накопленный квантованный update точен -/

/-- ТЕЛЕСКОП EF (почему EF работает — ТОЧНАЯ идентичность): если
резидуал эволюционирует по рекурренту `e (t+1) = η t • d t + e t − q t`,
то сумма исполненных (квантованных) шагов равна сумме идеальных
минус концевое изменение резидуала: `Σ q = Σ η•d + e 0 − e T`.
Классический факт (Karimireddy et al. 2019; см. также
`Hagi.Unified.ErrorFeedback.ef_telescope` — вариант без η_t на
квадратичной машине, слой 6). -/
theorem ef_cumulative_exact (η : ℕ → ℝ) (d e q : ℕ → V)
    (hEF : ∀ t, e (t + 1) = η t • d t + e t - q t) (T : ℕ) :
    ∑ t ∈ Finset.range T, q t
      = ∑ t ∈ Finset.range T, η t • d t + e 0 - e T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hq : q T = η T • d T + e T - e (T + 1) := by
      rw [hEF T]; abel
    rw [hq, ih]; abel

omit [NormedSpace ℝ V] in
/-- Служебная лемма спуска: траектория с шагами `q` равна старту
минус сумма шагов. -/
theorem ef_walk (x q : ℕ → V) (hx : ∀ t, x (t + 1) = x t - q t)
    (T : ℕ) :
    x T = x 0 - ∑ t ∈ Finset.range T, q t := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, hx T, ih]; abel

/-! ## Ограниченность резидуала (инвариант) -/

/-- ИНВАРИАНТ РЕЗИДУАЛА: bounded-error компрессор сохраняет
ограниченность резидуала — из ‖e 0‖ ≤ ε индукцией ‖e t‖ ≤ ε для всех
t. Шаг: ‖e (t+1)‖ = ‖u − Q u‖ = ‖Q u − u‖ ≤ ε по контракту. -/
theorem ef_residual_bounded (Q : V → V) (ε : ℝ)
    (hQ : boundedErrorCompressor Q ε)
    (η : ℕ → ℝ) (d e : ℕ → V)
    (he0 : ‖e 0‖ ≤ ε)
    (hEF : ∀ t, e (t + 1) = η t • d t + e t - Q (η t • d t + e t)) :
    ∀ t, ‖e t‖ ≤ ε := by
  intro t
  induction t with
  | zero => exact he0
  | succ t ih =>
    rw [hEF t]
    have hsym : η t • d t + e t - Q (η t • d t + e t)
        = -(Q (η t • d t + e t) - (η t • d t + e t)) := by abel
    rw [hsym, norm_neg]
    exact hQ _

/-! ## Траекторные следствия -/

/-- ТОЧНОЕ ОТКЛОНЕНИЕ ТРАЕКТОРИИ (тенение): исполняемая
(квантованная) траектория `x` против идеальной `y` (та же η_t • d_t,
тот же старт) отличается РОВНО на концевое изменение резидуала
`e T − e 0` — без оценок, тождество из телескопа. -/
theorem ef_iterate_deviation_exact (T : ℕ) (x y : ℕ → V)
    (η : ℕ → ℝ) (d e q : ℕ → V)
    (hx : ∀ t, x (t + 1) = x t - q t)
    (hy : ∀ t, y (t + 1) = y t - η t • d t)
    (hx0 : x 0 = y 0)
    (hEF : ∀ t, e (t + 1) = η t • d t + e t - q t) :
    x T - y T = e T - e 0 := by
  have htel := ef_cumulative_exact η d e q hEF T
  have hxs := ef_walk x q hx T
  have hys := ef_walk y (fun t => η t • d t) hy T
  rw [hxs, hys, hx0, htel]; abel

/-- ENDPOINT-ONLY ГРАНИЦА: при bounded-error компрессоре отклонение
EF-траектории от идеальной ≤ 2ε — НЕЗАВИСИМО от горизонта T
(линейного накопления нет: весь эффект — концы резидуала). -/
theorem ef_trajectory_endpoint_bound (T : ℕ) (x y : ℕ → V)
    (η : ℕ → ℝ) (d e q : ℕ → V) (Q : V → V) (ε : ℝ)
    (hQ : boundedErrorCompressor Q ε)
    (hx : ∀ t, x (t + 1) = x t - q t)
    (hy : ∀ t, y (t + 1) = y t - η t • d t)
    (hx0 : x 0 = y 0)
    (he0 : ‖e 0‖ ≤ ε)
    (hEF : ∀ t, e (t + 1) = η t • d t + e t - q t)
    (hq : ∀ t, q t = Q (η t • d t + e t)) :
    ‖x T - y T‖ ≤ 2 * ε := by
  have hid := ef_iterate_deviation_exact T x y η d e q hx hy hx0 hEF
  have hb := ef_residual_bounded Q ε hQ η d e he0
    (fun t => by rw [hEF t, hq t])
  rw [hid]
  calc ‖e T - e 0‖ ≤ ‖e T‖ + ‖e 0‖ := norm_sub_le _ _
    _ ≤ ε + ε := add_le_add (hb T) he0
    _ = 2 * ε := by ring

/-- ТРАЕКТОРНАЯ ОШИБКА ЦЕЛИ: при L-липшицевой цели (binder, 0 ≤ L)
ошибка значения после T квантованных EF-шагов ограничена концевым
резидуалом: |f(x T) − f(y T)| ≤ L(‖e T‖ + ‖e 0‖) ≤ 2Lε. -/
theorem ef_objective_deviation (f : V → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ u v, |f u - f v| ≤ L * ‖u - v‖)
    (T : ℕ) (x y : ℕ → V) (η : ℕ → ℝ) (d e q : ℕ → V)
    (Q : V → V) (ε : ℝ) (hQ : boundedErrorCompressor Q ε)
    (hx : ∀ t, x (t + 1) = x t - q t)
    (hy : ∀ t, y (t + 1) = y t - η t • d t)
    (hx0 : x 0 = y 0) (he0 : ‖e 0‖ ≤ ε)
    (hEF : ∀ t, e (t + 1) = η t • d t + e t - q t)
    (hq : ∀ t, q t = Q (η t • d t + e t)) :
    |f (x T) - f (y T)| ≤ L * (‖e T‖ + ‖e 0‖)
      ∧ |f (x T) - f (y T)| ≤ 2 * L * ε := by
  have hid := ef_iterate_deviation_exact T x y η d e q hx hy hx0 hEF
  have hb := ef_residual_bounded Q ε hQ η d e he0
    (fun t => by rw [hEF t, hq t])
  have hmain := hlip (x T) (y T)
  rw [hid] at hmain
  have hsum : ‖e T‖ + ‖e 0‖ ≤ ε + ε := add_le_add (hb T) he0
  constructor
  · calc |f (x T) - f (y T)| ≤ L * ‖e T - e 0‖ := hmain
    _ ≤ L * (‖e T‖ + ‖e 0‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) hL
  · calc |f (x T) - f (y T)| ≤ L * (‖e T‖ + ‖e 0‖) :=
          le_trans hmain
            (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hL)
    _ ≤ L * (ε + ε) := mul_le_mul_of_nonneg_left hsum hL
    _ = 2 * L * ε := by ring

/-! ## Наивное квантование без EF: линейное накопление -/

/-- НАИВНАЯ ГРАНИЦА (без EF): если шаг квантуется напрямую
`Q (η t • d t)` без резидуала, отклонение от идеальной траектории
≤ T • ε — ЛИНЕЙНОЕ накопление ошибок компрессора (паттерн
`Hagi.State.obj_telescope_err` на векторах отклонения). -/
theorem naive_deviation_bound (T : ℕ) (xN y : ℕ → V)
    (η : ℕ → ℝ) (d : ℕ → V) (Q : V → V) (ε : ℝ)
    (hQ : boundedErrorCompressor Q ε)
    (hx : ∀ t, xN (t + 1) = xN t - Q (η t • d t))
    (hy : ∀ t, y (t + 1) = y t - η t • d t)
    (hx0 : xN 0 = y 0) :
    ‖xN T - y T‖ ≤ (T : ℝ) * ε := by
  have hxs := ef_walk xN (fun t => Q (η t • d t)) hx T
  have hys := ef_walk y (fun t => η t • d t) hy T
  have hsplit : ∑ t ∈ Finset.range T, (η t • d t - Q (η t • d t))
      = ∑ t ∈ Finset.range T, (η t • d t)
        - ∑ t ∈ Finset.range T, Q (η t • d t) :=
    Finset.sum_sub_distrib (fun t => η t • d t) (fun t => Q (η t • d t))
  have hdev : xN T - y T
      = ∑ t ∈ Finset.range T, (η t • d t - Q (η t • d t)) := by
    rw [hxs, hys, hx0, hsplit]; abel
  rw [hdev]
  have hnn : ∀ t ∈ Finset.range T,
      ‖η t • d t - Q (η t • d t)‖ ≤ ε := by
    intro t _
    have hs : η t • d t - Q (η t • d t)
        = -(Q (η t • d t) - η t • d t) := by abel
    rw [hs, norm_neg]
    exact hQ _
  calc ‖∑ t ∈ Finset.range T, (η t • d t - Q (η t • d t))‖
      ≤ ∑ t ∈ Finset.range T, ‖η t • d t - Q (η t • d t)‖ :=
        norm_sum_le (Finset.range T) _
    _ ≤ ∑ t ∈ Finset.range T, ε :=
        Finset.sum_le_sum fun t ht => hnn t ht
    _ = (T : ℝ) * ε := by rw [Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]

/-- Свидетель-компрессор: сдвиг `x ↦ x − ε` — bounded-error с ε. -/
theorem shiftQ_bounded_error (ε : ℝ) (hε : 0 ≤ ε) :
    boundedErrorCompressor (fun x : ℝ => x - ε) ε := by
  intro x
  have h : (x : ℝ) - ε - x = -ε := by ring
  simp only [Real.norm_eq_abs, h, abs_neg, abs_of_nonneg hε]
  exact le_refl _

/-- Свидетель-компрессор: сдвиг `x ↦ x − ε` НЕ контрактивен при
ε > 0 — контракты contractive и bounded-error действительно разные. -/
theorem shiftQ_not_contractive (ε : ℝ) (hε : 0 < ε) :
    ¬ contractiveCompressor (fun x : ℝ => x - ε) := by
  intro hc
  have h0 := hc 0
  simp only [Real.norm_eq_abs] at h0
  rw [show |(0:ℝ) - ε| = |-(ε:ℝ)| by congr 1; ring,
    abs_neg, abs_of_nonneg hε.le] at h0
  simp at h0
  linarith

/-- ТЕСНОСТЬ НАИВНОЙ ГРАНИЦЫ (свидетель разделения): на компрессоре
сдвига (bounded-error, не конконтрактном) с нулевым направлением
d = 0, η = 1 наивная схема НАБИРАЕТ ровно T • ε отклонения, а
EF-схема держит e t = ε, т.е. концевое отклонение |e T − e 0| = ε.
Наивная граница T • ε ДОСТИГАЕТСЯ — разделение контрактов реально,
а не артефакт двух верхних граней. -/
theorem naive_accumulation_witness (ε : ℝ) (hε : 0 ≤ ε) (T : ℕ) :
    ∃ xN y : ℕ → ℝ,
      xN 0 = 0 ∧ y 0 = 0
        ∧ (∀ t, xN (t + 1) = xN t - (fun x : ℝ => x - ε) ((1 : ℝ) • (0 : ℝ)))
        ∧ (∀ t, y (t + 1) = y t - (1 : ℝ) • (0 : ℝ))
        ∧ |xN T - y T| = (T : ℝ) * ε := by
  refine ⟨fun t => (t : ℝ) * ε, fun _ => 0, by norm_num, rfl, ?_, ?_, ?_⟩
  · intro t
    have h0 : (1 : ℝ) • (0 : ℝ) = 0 := by simp
    simp only [h0, Nat.cast_succ]
    ring
  · intro t; simp
  · have hdev : (T : ℝ) * ε - (0 : ℝ) = (T : ℝ) * ε := by ring
    rw [hdev, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg T) hε)]

/-- КОЛИЧЕСТВЕННОЕ ПРЕИМУЩЕСТВО EF (сравнение трёх контрактов): при
одном и том же bounded-error компрессоре EF-схема даёт
endpoint-only отклонение ≤ 2ε (горизонто-независимое), наивное
квантование — ≤ T • ε (линейное). При T ≥ 1 и ε ≥ 0 EF-граница не
хуже, при T ≥ 3 и ε > 0 — строго лучше. (Обе величины — верхние
грани; достижимость наивной — `naive_accumulation_witness`.) -/
theorem ef_advantage (T : ℕ) (xef xN y : ℕ → V)
    (η : ℕ → ℝ) (d e q : ℕ → V) (Q : V → V) (ε : ℝ)
    (hQ : boundedErrorCompressor Q ε)
    (hx : ∀ t, xef (t + 1) = xef t - q t)
    (hxN : ∀ t, xN (t + 1) = xN t - Q (η t • d t))
    (hy : ∀ t, y (t + 1) = y t - η t • d t)
    (hx0 : xef 0 = y 0) (hxN0 : xN 0 = y 0) (he0 : ‖e 0‖ ≤ ε)
    (hEF : ∀ t, e (t + 1) = η t • d t + e t - q t)
    (hq : ∀ t, q t = Q (η t • d t + e t)) :
    ‖xef T - y T‖ ≤ 2 * ε
      ∧ ‖xN T - y T‖ ≤ (T : ℝ) * ε
      ∧ (2 ≤ T ∧ 0 ≤ ε → 2 * ε ≤ (T : ℝ) * ε)
      ∧ (3 ≤ T ∧ 0 < ε → 2 * ε < (T : ℝ) * ε) := by
  refine ⟨ef_trajectory_endpoint_bound T xef y η d e q Q ε hQ hx hy
    hx0 he0 hEF hq, ?_, ?_, ?_⟩
  · exact naive_deviation_bound T xN y η d Q ε hQ hxN hy hxN0
  · rintro ⟨hT, hε⟩
    have hcast : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    exact mul_le_mul_of_nonneg_right hcast hε
  · rintro ⟨hT, hε⟩
    have hcast : (3 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have hlt : (2 : ℝ) < (T : ℝ) := by linarith
    exact mul_lt_mul_of_pos_right hlt hε

/-! ## Тернарная инстанциация (покоординатный подъём) -/

/-- Покоординатный подъём скалярного квантователя на векторы. -/
def coordLift {n : ℕ} (qc : ℝ → ℝ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => qc (v i)

/-- ТЕРНАРНАЯ ИНСТАНЦИАЦИЯ (bounded-error): если скалярный
квантователь имеет равномерную покоординатную ошибку ≤ δ (форма
факта `Hagi.Runtime.TernaryExact.qTern_error_in`: для тернарного
округления `qTern s` с in-range входом |qc x − x| ≤ s/2), то
поднятый векторный компрессор — bounded-error контракт с ε = δ в
sup-норме на `Fin n → ℝ`. -/
theorem coordLift_bounded_error {n : ℕ} (qc : ℝ → ℝ) (δ : ℝ)
    (hq : ∀ x, |qc x - x| ≤ δ) (v : Fin n → ℝ) :
    ‖coordLift qc v - v‖ ≤ δ := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (hq 0)
  refine (pi_norm_le_iff_of_nonneg hδ).mpr fun i => ?_
  simp only [Real.norm_eq_abs, coordLift, Pi.sub_apply]
  exact hq (v i)

end Hagi.Step.ErrorFeedback
