import Mathlib.Tactic
import Hagi.State.TrainTrajectory
import Hagi.Step.ErrorFeedback

/-!
# MasterEF — EF-мастер-теорема: endpoint-only штраф на траектории

C393 (C391 top-2 co-beat): усиление C392 `master_trajectory_bound`.
В C392 штраф сжатия накапливается ЛИНЕЙНО по траектории
(Σ_t 2·L_lip·ε_{q,t}, форма C389). Здесь исполняется
error-feedback (EF, C381): квантованный шаг несёт резидуал
`e (t+1) = u_t − q_t`, `u_t = η_t • d_t + e_t`, и весь эффект
сжатия ТЕЛЕСКОПИРУЕТСЯ в концевой член — MAIN даёт

`f (xef T) ≤ f (xef 0) − ∑ drop_t + L_lip·(‖e T‖ + ‖e 0‖)`,

замкнутая форма `2·L_lip·ε` — НЕЗАВИСИМО от горизонта T.
Движки: C381 `ef_iterate_deviation_exact` (тенение исполняемой
траектории против идеальной РОВНО на `e T − e 0`) + C375
`obj_telescope_err` (идеальный сертифицированный спуск,
penalty ≡ 0). Новой индукции нет.

Честное отношение drops: certified drops вычисляются на
ИДЕАЛЬНОЙ траектории (поле `hdrop`); исполняемая наследует их
только через концевую коррекцию. Пер-шаговые drops на исполняемой
потребовали бы пер-шагового penalty — это и есть C392 (слабее при
T ≥ 3, см. `master_ef_vs_naive`; per-step crossover — C389).

Честные пины (наследуются):

- **L_lip — binder**: `0 ≤ L` + липшиц-посылка, как в C381.
- **qTern-инстанциация**: через существующий подъём C381
  `coordLift_bounded_error` (цитируется, не дублируется).
- **Адаптивные данные**: caveats C380 наследуются.
- **Carrier-мост**: модуль работает на generic нормированном V с
  абстрактной целью f (тот же уровень, что C381); мост к
  `fullObjective` на `CanonicalTrainState` — пин C392, co-beat.
- **Бюджет/whp-каналы C392** не затрагиваются (additions only).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory

open Finset Hagi.State Hagi.Step.ErrorFeedback

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## EF-траекторная запись -/

/-- EF-ТРАЕКТОРИЯ (запись уровня траектории, носитель C381):
T шагов исполняют квантованные обновления `q t = Q (η t • d t +
e t)` С error feedback — резидуал эволюционирует
`e (t+1) = η t • d t + e t − q t`; `xef` — исполняемая
(квантованная) траектория, `xid` — идеальная (несжатая, та же
`η t • d t`, тот же старт). Certified drops связаны с ИДЕАЛЬНОЙ
траекторией (честно: десцент сертифицирован для несжатой
динамики; исполняемая получает его через концевую коррекцию MAIN).
Законы динамики — для всех t (как в C381), горизонт T — у
сертификата drops. -/
structure EFTrajectory (T : ℕ) where
  /-- Шаги обучения (несжатые направления). -/
  η : ℕ → ℝ
  /-- Направления шагов. -/
  d : ℕ → V
  /-- Резидуал EF (переносимая ошибка сжатия). -/
  e : ℕ → V
  /-- Исполняемые (квантованные) обновления. -/
  q : ℕ → V
  /-- Исполняемая (EF) траектория состояний. -/
  xef : ℕ → V
  /-- Идеальная (несжатая) траектория состояний. -/
  xid : ℕ → V
  /-- Компрессор (квантователь). -/
  Q : V → V
  /-- Полная цель (уровень C381 `ef_objective_deviation`). -/
  f : V → ℝ
  /-- Исполняемая траектория идёт квантованными шагами. -/
  hxef : ∀ t, xef (t + 1) = xef t - q t
  /-- Идеальная траектория идёт несжатыми шагами. -/
  hxid : ∀ t, xid (t + 1) = xid t - η t • d t
  /-- Общий старт исполняемой и идеальной траекторий. -/
  hstart : xef 0 = xid 0
  /-- Рекуррент резидуала EF (C381). -/
  hEF : ∀ t, e (t + 1) = η t • d t + e t - q t
  /-- Исполняемое обновление — выход компрессора из EF-входа. -/
  hq : ∀ t, q t = Q (η t • d t + e t)
  /-- Сертифицированные спуски (на идеальной траектории). -/
  drop : ℕ → ℝ
  /-- Идеальный шаг сертифицированно спускается не меньше drop. -/
  hdrop : ∀ t < T, f (xid (t + 1)) ≤ f (xid t) - drop t

/-! ## MAIN: endpoint-only мастер-граница -/

/-- EF-МАСТЕР-ТЕОРЕМА (endpoint-only штраф): после T EF-шагов
полная цель исполняемой траектории не выше начальной минус сумма
сертифицированных drops ПЛЮС один концевой член
`L_lip·(‖e T‖ + ‖e 0‖)` — вместо ЛИНЕЙНОЙ суммы пер-шаговых
штрафов C392 (Σ_t 2·L_lip·ε_{q,t}). Движки: C381
`ef_iterate_deviation_exact` (тенение: `xef T − xid T = e T − e 0`,
точно) + липшиц + C375 `obj_telescope_err` (идеальный спуск,
penalty ≡ 0). L_lip — binder (пин C381 наследуется). -/
theorem master_trajectory_bound_ef (T : ℕ) (tr : EFTrajectory (V := V) T)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ (u v : V), |tr.f u - tr.f v| ≤ L * ‖u - v‖) :
    tr.f (tr.xef T) ≤ tr.f (tr.xef 0)
      - ∑ t ∈ Finset.range T, tr.drop t
      + L * (‖tr.e T‖ + ‖tr.e 0‖) := by
  have hid := ef_iterate_deviation_exact T tr.xef tr.xid tr.η tr.d
    tr.e tr.q tr.hxef tr.hxid tr.hstart tr.hEF
  have habs := hlip (tr.xef T) (tr.xid T)
  rw [hid] at habs
  have hexec : tr.f (tr.xef T)
      ≤ tr.f (tr.xid T) + L * (‖tr.e T‖ + ‖tr.e 0‖) := by
    have h1 : |tr.f (tr.xef T) - tr.f (tr.xid T)|
        ≤ L * (‖tr.e T‖ + ‖tr.e 0‖) :=
      le_trans habs (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hL)
    have h2 : tr.f (tr.xef T) - tr.f (tr.xid T)
        ≤ L * (‖tr.e T‖ + ‖tr.e 0‖) :=
      le_trans (le_abs_self _) h1
    linarith
  have hideal : tr.f (tr.xid T) ≤ tr.f (tr.xid 0)
      - ∑ t ∈ Finset.range T, tr.drop t := by
    have hkey : ∀ j < T, tr.f (tr.xid (j + 1))
        ≤ tr.f (tr.xid j) - tr.drop j + (0 : ℝ) := by
      intro j hj
      have hstep := tr.hdrop j hj
      linarith [hstep]
    have htel := obj_telescope_err T (fun j => tr.f (tr.xid j))
      tr.drop (fun _ => (0 : ℝ)) hkey
    simpa using htel
  have h0 : tr.f (tr.xid 0) = tr.f (tr.xef 0) := by rw [tr.hstart]
  linarith

/-! ## Инвариант резидуала на траектории -/

/-- ИНВАРИАНТ РЕЗИДУАЛА (траекторный уровень, C381
`ef_residual_bounded` через поля записи): bounded-error компрессор
и `‖e 0‖ ≤ ε` дают `‖e t‖ ≤ ε` для ВСЕХ t — резидуал не
накапливается. Ингредиент замкнутой формы MAIN. -/
theorem master_ef_residual_invariant (T : ℕ) (tr : EFTrajectory (V := V) T)
    (ε : ℝ) (hQ : boundedErrorCompressor tr.Q ε)
    (he0 : ‖tr.e 0‖ ≤ ε) :
    ∀ t, ‖tr.e t‖ ≤ ε :=
  ef_residual_bounded tr.Q ε hQ tr.η tr.d tr.e he0
    (fun t => by rw [tr.hEF t, tr.hq t])

/-! ## Замкнутая форма MAIN -/

/-- EF-МАСТЕР-ТЕОРЕМА, замкнутая форма: bounded-error компрессор
(ε) и `‖e 0‖ ≤ ε` дают `f (xef T) ≤ f (xef 0) − ∑ drop_t +
2·L_lip·ε` — штраф НЕ зависит от T (endpoint-only), тогда как
C392-форма накапливает T·(2·L_lip·ε). qTern-инстанциация ε —
через C381 `coordLift_bounded_error` (покоординатный подъём). -/
theorem master_trajectory_bound_ef_closed (T : ℕ)
    (tr : EFTrajectory (V := V) T) (L ε : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ (u v : V), |tr.f u - tr.f v| ≤ L * ‖u - v‖)
    (hQ : boundedErrorCompressor tr.Q ε) (he0 : ‖tr.e 0‖ ≤ ε) :
    tr.f (tr.xef T) ≤ tr.f (tr.xef 0)
      - ∑ t ∈ Finset.range T, tr.drop t + 2 * L * ε := by
  have h := master_trajectory_bound_ef T tr L hL hlip
  have hres := master_ef_residual_invariant T tr ε hQ he0
  have h2 : L * (‖tr.e T‖ + ‖tr.e 0‖) ≤ 2 * L * ε :=
    calc L * (‖tr.e T‖ + ‖tr.e 0‖) ≤ L * (ε + ε) :=
        mul_le_mul_of_nonneg_left (add_le_add (hres T) he0) hL
      _ = 2 * L * ε := by ring
  linarith

/-! ## Сравнение: endpoint-only против наивной Σ-формы -/

/-- T-ПРОТИВ-ОДНОГО разделение на уровне мастер-теоремы
(траекторный crossover; per-step — C389, нормы без drops — C381
`ef_advantage`): (i) EF endpoint-граница с константой `2·L·ε`;
(ii) наивная C392-форма с равномерным пер-шаговым штрафом `2·L·ε`
даёт границу с `T·(2·L·ε)` (движок C375 `obj_telescope_err`);
(iii) при T не меньше одного EF-штраф не хуже; (iv) при T не
меньше трёх и положительных L, ε — СТРОГО лучше: линейное
накопление реально (свидетель C381 `naive_accumulation_witness`). -/
theorem master_ef_vs_naive (T : ℕ) (tr : EFTrajectory (V := V) T)
    (L ε : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ (u v : V), |tr.f u - tr.f v| ≤ L * ‖u - v‖)
    (hQ : boundedErrorCompressor tr.Q ε) (he0 : ‖tr.e 0‖ ≤ ε) :
    -- (i) EF: endpoint-only штраф
    (tr.f (tr.xef T) ≤ tr.f (tr.xef 0)
      - ∑ t ∈ Finset.range T, tr.drop t + 2 * L * ε)
    -- (ii) наивная Σ-форма: равномерный пер-шаговый штраф
    ∧ (∀ g : ℕ → ℝ, (∀ j < T, g (j + 1) ≤ g j - tr.drop j
        + 2 * L * ε) →
        g T ≤ g 0 - ∑ t ∈ Finset.range T, tr.drop t
          + (T : ℝ) * (2 * L * ε))
    -- (iii) crossover нестрогий
    ∧ (1 ≤ T ∧ 0 ≤ ε → 2 * L * ε ≤ (T : ℝ) * (2 * L * ε))
    -- (iv) crossover строгий
    ∧ (3 ≤ T ∧ 0 < L ∧ 0 < ε → 2 * L * ε < (T : ℝ) * (2 * L * ε)) := by
  refine ⟨master_trajectory_bound_ef_closed T tr L ε hL hlip hQ
    he0, ?_, ?_, ?_⟩
  · intro g hg
    have htel := obj_telescope_err T g tr.drop
      (fun _ => 2 * L * ε) hg
    have hsum : ∑ j ∈ Finset.range T, (2 * L * ε : ℝ)
        = (T : ℝ) * (2 * L * ε) := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum] at htel
    exact htel
  · rintro ⟨hT, hε⟩
    have hcast : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    calc 2 * L * ε = (1 : ℝ) * (2 * L * ε) := by ring
      _ ≤ (T : ℝ) * (2 * L * ε) :=
          mul_le_mul_of_nonneg_right hcast
            (mul_nonneg (by nlinarith : (0 : ℝ) ≤ 2 * L)
              (by linarith : (0 : ℝ) ≤ ε))
  · rintro ⟨hT, hLpos, hεpos⟩
    have hlt : (2 : ℕ) < T := by omega
    have hcast : (2 : ℝ) < (T : ℝ) := by exact_mod_cast hlt
    have hpos : (0 : ℝ) < 2 * L * ε := by
      have := mul_pos hLpos hεpos
      nlinarith [this]
    nlinarith [hcast, hpos]

end Hagi.Theory
