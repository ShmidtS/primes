/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.FreedmanTwoSided

/-!
# Freedman-мост: стохастический безопасный шаг (A14 bridge 1)

Мост между мартингальной концентрацией и CertifiedLoop-контрактом:
посылки о шуме стохастического градиентного шага (ограниченный
условный шум, нулевое условное среднее, ограниченная условная
дисперсия) плюс детерминированный drift конвертируются в
высоковероятностную гарантию реализованного спуска.

Строится на адаптивном Freedman-хвосте `history_additive_freedman`
(P[отклонение ≥ r при компенсаторе ≤ V] ≤ exp(−r²/(4(V+c·r)))).

**C356 (variance-компенсатор):** фиксированный-λ Freedman-хвост с
ФАКТИЧЕСКИМ дисперсионным компенсатором (суммой условных
дисперсий) вместо константного σ: суперmartингал
`history_exp_compensated_le`, хвост `history_variance_freedman_lam`,
замкнутый радиус `freedman_variance_radius`
(exp(−r²/(4V)) при c·r ≤ 2V — без линейного члена) и мост
`stochastic_safe_step_variance` (failure = exp(−r²/(4·T·σ))
при c·r ≤ 2·T·σ; в этом режиме строго лучше C350-радиуса
exp(−r²/(4·(T·σ+c·r)))).

**Что доказано:**

* `historyAdditive_mono` — поточечная монотонность аддитивного
  функционала траектории.
* `driftAdditive` — сумма предсказуемого drift по траектории;
  `historyAdditive_drift_sub` — разложение drift−шум.
* `historyCounter_const` — при константной дисперсионной посылке
  σ компенсатор `historyCounter` детерминирован: (min k T)·σ.
* `freedman_radius_sq` — замкнутая форма радиуса
  R = 2·√(V·L) + 4·c·L: R² ≥ 4·L·(V + c·R) при L ≥ 0.
* `freedman_failure_closed` — с L = −log δ хвост Freedman ≤ δ.
* `CertStochasticStep` — CertStepGen-form контракт: drop,
  drop_pos, failure и whp-закон descent_whp.
* `stochastic_safe_step` — ГЛАВНЫЙ МОСТ: для реализованного
  декремента цели, покрывающего drift минус мартингал-разность,
  drop = T·γ − r достигается с вероятностью ≥ 1 −
  exp(−r²/(4·(T·σ + c·r))).
* `stochastic_safe_step_closed` — то же с замкнутым радиусом
  R = 2·√(T·σ·L) + 4·c·L и failure ≤ δ.

**Честные ограничения (premise-form limitations):**

* адаптивного-λ Freedman нет — используется λ-оптимизация
  фиксированного хвоста из базовой теоремы; C356 добавил
  fixed-λ вариант с фактическим variance-компенсатором, но
  полный Freedman-радиус r²/(2(V+c·r/3)) (Bennett-chord,
  константа 1/(2(1−λc/3))) не достигнут — MGF-константа
  базовой `pmfMean_exp_le` равна 1 (λ·c ≤ 1);
* дисперсионный компенсатор моста — детерминированный порог
  T·σ из посылки условной дисперсии ≤ σ² (посылка (b)); в хвосте
  при этом работает фактический (capped) компенсатор
  min(cond var, σ) ≤ σ глобально, поэтому ветка {C > T·σ} пуста
  и union bound не нужен; улучшение радиуса — только в режиме
  c·r ≤ 2·T·σ (посылка `hrc`), вне режима применима C350-версия;
* λ выбирается априорно под (r, V) (per-instance),
  данные-зависимый λ-процесс не строится;
* `CertStochasticStep` — самодостаточная структура: `CertStepGen`
  живёт в другом слое (import запрещён LayerLint); адаптация в
  `CertStepGen` — задача consumer-слоя (layer 3+).

Посылки все явные, эмпирических констант (`h_emp_`) нет.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Probability

section
open scoped BigOperators

variable {α : Type*}

/-- Поточечная монотонность `historyAdditive`: если h ≤ h'
при всех аргументах, то и суммы по траектории упорядочены. -/
theorem historyAdditive_mono (h h' : ℕ → α → α → ℝ) (T k : ℕ)
    (ω : History α T)
    (hle : ∀ j a b, h j a b ≤ h' j a b) :
    historyAdditive h T k ω ≤ historyAdditive h' T k ω := by
  unfold historyAdditive
  exact Finset.sum_le_sum fun j _ => hle j _ _

/-- Сумма предсказуемого (зависящего только от текущего
состояния) drift-функционала по первым k шагам траектории. -/
noncomputable def driftAdditive (drift : ℕ → α → ℝ) (T k : ℕ)
    (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), drift j (ω (historyIndex T j))

/-- Аддитивный функционал «drift минус шум» раскладывается в
разность сумм drift и шума. -/
theorem historyAdditive_drift_sub (drift : ℕ → α → ℝ)
    (g : ℕ → α → α → ℝ) (T k : ℕ) (ω : History α T) :
    historyAdditive (fun j a b => drift j a - g j a b) T k ω
      = driftAdditive drift T k ω - historyAdditive g T k ω := by
  unfold historyAdditive driftAdditive
  rw [← Finset.sum_sub_distrib]

/-- При константной дисперсионной посылке компенсатор
`historyCounter` не зависит от траектории: он равен
(min k T)·σ. -/
theorem historyCounter_const (σ : ℝ) (T k : ℕ) (ω : History α T) :
    historyCounter (fun _ _ => σ) T k ω = (min k T : ℕ) * σ := by
  unfold historyCounter
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

section
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Замкнутая форма Freedman-радиуса: для R = 2·√(V·L) + 4·c·L
выполнено R² ≥ 4·L·(V + c·R) (достаточное условие хвоста ≤
exp(−L)). -/
theorem freedman_radius_sq (V c L : ℝ) (hV : 0 ≤ V) (hc : 0 ≤ c)
    (hL : 0 ≤ L) :
    4 * L * (V + c * (2 * Real.sqrt (V * L) + 4 * c * L))
      ≤ (2 * Real.sqrt (V * L) + 4 * c * L) ^ 2 := by
  have hVL : 0 ≤ V * L := by positivity
  have hs2 : Real.sqrt (V * L) ^ 2 = V * L := Real.sq_sqrt hVL
  have hsn : 0 ≤ Real.sqrt (V * L) := Real.sqrt_nonneg _
  nlinarith [hs2, mul_nonneg (mul_nonneg hc hL) hsn]

/-- С L = −log δ (δ ∈ (0, 1)) замкнутый радиус
R = 2·√(V·L) + 4·c·L даёт хвост Freedman ≤ δ. -/
theorem freedman_failure_closed (V c δ : ℝ) (hV : 0 ≤ V) (hc : 0 < c)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    Real.exp (-(2 * Real.sqrt (V * (-Real.log δ))
        + 4 * c * (-Real.log δ)) ^ 2
      / (4 * (V + c * (2 * Real.sqrt (V * (-Real.log δ))
        + 4 * c * (-Real.log δ))))) ≤ δ := by
  have hL : 0 < -Real.log δ := by
    have hlt : Real.log δ < Real.log 1 := Real.log_lt_log hδ hδ1
    have h2 : Real.log δ < 0 := by simpa using hlt
    linarith
  have hVL : 0 ≤ V * (-Real.log δ) := by positivity
  have hsn : 0 ≤ Real.sqrt (V * (-Real.log δ)) :=
    Real.sqrt_nonneg _
  have hRnn : 0 ≤ c * (2 * Real.sqrt (V * (-Real.log δ))) :=
    mul_nonneg hc.le (mul_nonneg (by norm_num) hsn)
  have hcl : 0 < c * (-Real.log δ) := mul_pos hc hL
  have h4 : 0 < 4 * c * (-Real.log δ) := by nlinarith [hcl]
  have hRpos : 0 < c * (4 * c * (-Real.log δ)) := mul_pos hc h4
  have hX : 0 < c * (2 * Real.sqrt (V * (-Real.log δ))
      + 4 * c * (-Real.log δ)) := by nlinarith [hRnn, hRpos]
  have hVX : 0 < V + c * (2 * Real.sqrt (V * (-Real.log δ))
      + 4 * c * (-Real.log δ)) := by nlinarith [hV, hX]
  have hden : 0 < 4 * (V + c * (2 * Real.sqrt (V * (-Real.log δ))
      + 4 * c * (-Real.log δ))) := mul_pos (by norm_num) hVX
  have hkey := freedman_radius_sq V c (-Real.log δ) hV hc.le hL.le
  have hdiv : -(2 * Real.sqrt (V * (-Real.log δ))
        + 4 * c * (-Real.log δ)) ^ 2
      / (4 * (V + c * (2 * Real.sqrt (V * (-Real.log δ))
        + 4 * c * (-Real.log δ)))) ≤ Real.log δ := by
    rw [div_le_iff₀ hden]
    nlinarith [hkey]
  have hexp : Real.exp (-(2 * Real.sqrt (V * (-Real.log δ))
        + 4 * c * (-Real.log δ)) ^ 2
      / (4 * (V + c * (2 * Real.sqrt (V * (-Real.log δ))
        + 4 * c * (-Real.log δ)))))
      ≤ Real.exp (Real.log δ) :=
      Real.exp_le_exp.mpr hdiv
  rwa [Real.exp_log hδ] at hexp

/-- CertStepGen-form контракт для стохастического шага:
положительный drop и whp-закон реализованного спуска
(вероятность недостижения drop ≤ failure). Аналог полей
drop/drop_pos/risk канонического сертификационного ядра;
вероятностная версия поля descent. -/
structure CertStochasticStep {Ω : Type*} [Fintype Ω]
    (law : PMF Ω) (realized : Ω → ℝ) where
  /-- Сертифицированная нижняя граница реализованного спуска. -/
  drop : ℝ
  drop_pos : 0 < drop
  /-- Верхняя граница вероятности недостижения drop. -/
  failure : ℝ
  /-- Вероятность события {drop ≤ realized} не меньше 1 − failure. -/
  descent_whp : pmfMean law
      (fun ω => if drop ≤ realized ω then 1 else 0) ≥ 1 - failure

/-- **Freedman-мост (главный)**: пусть на горизонте T ≥ 1 шагов

(a) шум g — мартингал-разность с ограничением |g| ≤ c,
    нулевым условным средним и условной дисперсией ≤ σ²
    (посылки `h_noise_bounded`/`h_noise_cond_mean`/
    `h_noise_cond_var`);
(b) детерминированный drift не хуже γ в шаге
    (`h_drift_floor`);
(c) реализованный декремент цели покрывает drift минус шум
    (`h_step_descent`).

Тогда drop = T·γ − r достигается с вероятностью ≥
1 − exp(−r²/(4·(T·σ + c·r))): `stochastic_safe_step_whp`
(Prop-форма) и обёртка `stochastic_safe_step`. -/
theorem stochastic_safe_step_whp (initial : PMF α) (K : ℕ → α → PMF α)
    (T : ℕ) (hT : 0 < T) (γ c σ r : ℝ)
    (hγ : 0 ≤ γ) (hc : 0 < c) (hσ : 0 ≤ σ) (hr : 0 < r)
    (hdrop : r < T * γ)
    (h g : ℕ → α → α → ℝ) (drift : ℕ → α → ℝ)
    (h_noise_bounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (h_noise_cond_mean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (h_noise_cond_var : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ σ)
    (h_step_descent : ∀ k a b, drift k a - g k a b ≤ h k a b)
    (h_drift_floor : ∀ k a, γ ≤ drift k a) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if T * γ - r ≤ historyAdditive h T T ω then 1 else 0)
      ≥ 1 - Real.exp (-r ^ 2 / (4 * (T * σ + c * r))) := by
    classical
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    -- поточечный спуск: шум-событие {S ≤ r} влечёт drop ≤ Σh
    have hmono : ∀ ω : History α T,
        historyAdditive (fun k a b => drift k a - g k a b) T T ω
          ≤ historyAdditive h T T ω :=
      fun ω => historyAdditive_mono _ _ T T ω
        (fun k a b => h_step_descent k a b)
    have hsplit := historyAdditive_drift_sub drift g T T
    have hfloor : ∀ ω : History α T,
        (T : ℝ) * γ ≤ driftAdditive drift T T ω := by
      intro ω
      unfold driftAdditive
      simp only [Nat.min_self]
      calc (T : ℝ) * γ = ∑ _j ∈ Finset.range T, γ := by
            rw [Finset.sum_const, Finset.card_range]; simp
        _ ≤ _ := Finset.sum_le_sum
          fun j _ => h_drift_floor j (ω (historyIndex T j))
    have hcover : ∀ ω : History α T,
        historyAdditive g T T ω ≤ r →
        T * γ - r ≤ historyAdditive h T T ω := by
      intro ω hSr
      have h1 := hmono ω
      rw [hsplit ω] at h1
      have h2 := hfloor ω
      linarith
    -- компенсатор детерминирован: C = T·σ
    have hcst : ∀ ω : History α T,
        historyCounter (fun _ _ => σ) T T ω = T * σ :=
      fun ω => by rw [historyCounter_const σ T T ω, Nat.min_self]
    -- базовый Freedman-хвост на константном компенсаторе
    have htail := history_additive_freedman initial K g
      (fun _ _ => σ) T c hc h_noise_bounded h_noise_cond_mean
      h_noise_cond_var T r (T * σ) hr
        (mul_nonneg hT'.le hσ)
    simp only [hcst, le_refl, and_true] at htail
    -- поточечная цепочка индикаторов
    have hpt1 : ∀ ω : History α T,
        (if T * γ - r ≤ historyAdditive h T T ω then (1 : ℝ) else 0)
          ≥ (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0) := by
      intro ω
      by_cases hS : historyAdditive g T T ω ≤ r
      · have hcov := hcover ω hS
        simp [hcov, hS]
      · simp only [hS, ite_false, ge_iff_le]
        split_ifs <;> norm_num
    have hpt2 : ∀ ω : History α T,
        (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
          + (if r ≤ historyAdditive g T T ω
              ∧ historyCounter (fun _ _ => σ) T T ω ≤ T * σ
              then (1 : ℝ) else 0) ≥ 1 := by
      intro ω
      rw [hcst ω]
      by_cases hS : historyAdditive g T T ω ≤ r
      · by_cases hrS : r ≤ historyAdditive g T T ω <;>
          simp [hS, hrS]
      · have hrS : r ≤ historyAdditive g T T ω := by
          have hne : ¬(historyAdditive g T T ω ≤ r) := hS
          linarith
        simp [hS, hrS]
    -- вероятностная цепочка
    have hev1 : pmfMean (historyLaw initial K T T)
        (fun ω => if T * γ - r ≤ historyAdditive h T T ω then 1 else 0)
        ≥ pmfMean (historyLaw initial K T T)
        (fun ω => if historyAdditive g T T ω ≤ r then 1 else 0) :=
      pmfMean_mono _ (fun ω _ => hpt1 ω)
    have hev2 : pmfMean (historyLaw initial K T T)
        (fun ω => if historyAdditive g T T ω ≤ r then 1 else 0)
        ≥ 1 - pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T T ω
            ∧ historyCounter (fun _ _ => σ) T T ω ≤ T * σ
            then 1 else 0) := by
      have hsum : pmfMean (historyLaw initial K T T)
          (fun ω => (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
            + (if r ≤ historyAdditive g T T ω
                ∧ historyCounter (fun _ _ => σ) T T ω ≤ T * σ
                then (1 : ℝ) else 0))
          = pmfMean (historyLaw initial K T T)
              (fun ω => if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
            + pmfMean (historyLaw initial K T T)
              (fun ω => if r ≤ historyAdditive g T T ω
                  ∧ historyCounter (fun _ _ => σ) T T ω ≤ T * σ
                  then (1 : ℝ) else 0) :=
        pmfMean_add _ _ _
      have hge : (1 : ℝ) ≤ pmfMean (historyLaw initial K T T)
          (fun ω => (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
            + (if r ≤ historyAdditive g T T ω
                ∧ historyCounter (fun _ _ => σ) T T ω ≤ T * σ
                then (1 : ℝ) else 0)) :=
        le_trans (le_of_eq (pmfMean_const (historyLaw initial K T T) 1).symm)
          (pmfMean_mono (historyLaw initial K T T)
            (fun ω _ => hpt2 ω))
      rw [hsum] at hge
      linarith
    have hmonoC : pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T T ω
            ∧ historyCounter (fun _ _ => σ) T T ω ≤ T * σ
            then 1 else 0)
        ≤ pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T T ω then 1 else 0) :=
      pmfMean_mono _ (fun ω _ => by
        by_cases h1 : r ≤ historyAdditive g T T ω
        · by_cases h2 : historyCounter (fun _ _ => σ) T T ω ≤ T * σ <;>
            simp [h1, h2]
        · simp [h1])
    linarith [hev1, hev2, hmonoC, htail]

/-- Обёртка-сертификат: `stochastic_safe_step_whp` в форме
`CertStochasticStep`. -/
noncomputable def stochastic_safe_step (initial : PMF α) (K : ℕ → α → PMF α)
    (T : ℕ) (hT : 0 < T) (γ c σ r : ℝ)
    (hγ : 0 ≤ γ) (hc : 0 < c) (hσ : 0 ≤ σ) (hr : 0 < r)
    (hdrop : r < T * γ)
    (h g : ℕ → α → α → ℝ) (drift : ℕ → α → ℝ)
    (h_noise_bounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (h_noise_cond_mean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (h_noise_cond_var : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ σ)
    (h_step_descent : ∀ k a b, drift k a - g k a b ≤ h k a b)
    (h_drift_floor : ∀ k a, γ ≤ drift k a) :
    CertStochasticStep (historyLaw initial K T T)
      (historyAdditive h T T) where
  drop := T * γ - r
  drop_pos := by
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    linarith
  failure := Real.exp (-r ^ 2 / (4 * (T * σ + c * r)))
  descent_whp := stochastic_safe_step_whp initial K T hT γ c σ r hγ hc hσ
    hr hdrop h g drift h_noise_bounded h_noise_cond_mean h_noise_cond_var
    h_step_descent h_drift_floor

/-- **Freedman-мост, замкнутый радиус**: то же, что
`stochastic_safe_step`, с явным радиусом
R = 2·√(T·σ·L) + 4·c·L, L = −log δ, и failure ≤ δ. -/
noncomputable def stochastic_safe_step_closed (initial : PMF α)
    (K : ℕ → α → PMF α)
    (T : ℕ) (hT : 0 < T) (γ c σ δ : ℝ)
    (hγ : 0 ≤ γ) (hc : 0 < c) (hσ : 0 ≤ σ)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hdrop : 2 * Real.sqrt (T * σ * (-Real.log δ))
        + 4 * c * (-Real.log δ) < T * γ)
    (h g : ℕ → α → α → ℝ) (drift : ℕ → α → ℝ)
    (h_noise_bounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (h_noise_cond_mean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (h_noise_cond_var : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ σ)
    (h_step_descent : ∀ k a b, drift k a - g k a b ≤ h k a b)
    (h_drift_floor : ∀ k a, γ ≤ drift k a) :
    CertStochasticStep (historyLaw initial K T T)
      (historyAdditive h T T) := by
  classical
  have hstep := stochastic_safe_step_whp initial K T hT γ c σ
    (2 * Real.sqrt (T * σ * (-Real.log δ))
      + 4 * c * (-Real.log δ))
    hγ hc hσ (by
      have hL : 0 < -Real.log δ := by
        have hlt : Real.log δ < Real.log 1 :=
          Real.log_lt_log hδ hδ1
        have h2 : Real.log δ < 0 := by simpa using hlt
        linarith
      have hVL : 0 ≤ T * σ * (-Real.log δ) := by positivity
      have hsn : 0 ≤ Real.sqrt (T * σ * (-Real.log δ)) :=
        Real.sqrt_nonneg _
      have hcl : 0 < c * (-Real.log δ) := mul_pos hc hL
      have h4 : 0 < 4 * c * (-Real.log δ) := by nlinarith [hcl]
      nlinarith [hsn, h4])
    hdrop h g drift h_noise_bounded h_noise_cond_mean
    h_noise_cond_var h_step_descent h_drift_floor
  have htail := freedman_failure_closed (T * σ) c δ
    (by
      have hL : 0 < -Real.log δ := by
        have hlt : Real.log δ < Real.log 1 :=
          Real.log_lt_log hδ hδ1
        have h2 : Real.log δ < 0 := by simpa using hlt
        linarith
      positivity)
    hc hδ hδ1
  refine ⟨T * γ - (2 * Real.sqrt (T * σ * (-Real.log δ))
      + 4 * c * (-Real.log δ)), ?_, δ, ?_⟩
  · have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    linarith
  · linarith [htail]

end

section
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Capped дисперсионный компенсатор min(фактическая условная
дисперсия, σ) поточечно ограничен (min k T)·σ — глобально,
без посылок о support. Это ключ к покрытию ветки {C > V}:
при V = T·σ она пуста, union bound не нужен. -/
theorem historyCounter_var_le (K : ℕ → α → PMF α)
    (g : ℕ → α → α → ℝ) (T k : ℕ) (σ : ℝ) (ω : History α T) :
    historyCounter (fun j a => min
      (pmfMean (K j a) (fun b => g j a b ^ 2)) σ) T k ω
      ≤ (min k T : ℕ) * σ := by
  unfold historyCounter
  calc ∑ j ∈ Finset.range (min k T),
      (fun j a => min (pmfMean (K j a) (fun b => g j a b ^ 2)) σ) j
        (ω (historyIndex T j))
      ≤ ∑ _j ∈ Finset.range (min k T), σ :=
        Finset.sum_le_sum fun j _ => min_le_right _ _
    _ = (min k T : ℕ) * σ := by
        rw [Finset.sum_const, Finset.card_range]; simp

/-- **Variance-compensator суперmartингал** (C356): при
ограниченном шуме (|g| ≤ c), нулевом условном среднем и
условной дисперсии ≤ v, для λ ≥ 0 с λ·c ≤ 1 экспоненциальный
компенсированный потенциал exp(λ·S_k − λ²·C_k) — суперmartingale
на траекториях: его среднее по historyLaw ≤ 1. Здесь C_k —
ФАКТИЧЕСКАЯ сумма условных дисперсий (компенсатор v), а не
константа. Одношаговое ядро — `pmfMean_exp_le` (MGF с
квадратичным variance-членом). -/
theorem history_exp_compensated_le (initial : PMF α) (K : ℕ → α → PMF α)
    (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c lam : ℝ) (hlam : 0 ≤ lam) (hclam : lam * c ≤ 1)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a)
    (k : ℕ) :
    pmfMean (historyLaw initial K T k)
      (fun ω => Real.exp (lam * historyAdditive g T k ω
        - lam ^ 2 * historyCounter v T k ω)) ≤ 1 := by
  classical
  set F : ℕ → History α T → ℝ := fun j ω =>
    Real.exp (lam * historyAdditive g T j ω
      - lam ^ 2 * historyCounter v T j ω) with hF
  have hone : ∀ j : ℕ, ∀ ω : History α T,
      ω ∈ (historyLaw initial K T j).support →
      pmfMean (historyKernel K T j ω) (F (j + 1)) ≤ F j ω := by
    intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel, ite_eq_left hj, pmfMean_map]
      have hsupp := historyLaw_current_support initial K T j hj.le ω hω
      have hfac : ∀ b : α, F (j + 1)
          (Function.update ω (historyIndex T (j + 1)) b)
          = F j ω * Real.exp (lam * g j (ω (historyIndex T j)) b
              - lam ^ 2 * v j (ω (historyIndex T j))) := by
        intro b
        simp only [hF]
        rw [historyAdditive_update g T j hj, historyCounter_update v T j hj,
          ← Real.exp_add]
        congr 1
        ring
      simp_rw [hfac]
      rw [pmfMean_const_mul]
      have hmgf := pmfMean_exp_le (K j (ω (historyIndex T j)))
        (fun b => g j (ω (historyIndex T j)) b) c
        (v j (ω (historyIndex T j))) lam hlam hclam
        (fun b hb => hbounded j hj _ hsupp b hb)
        (by rw [← hmean j hj _ hsupp])
        (hvar j hj _ hsupp)
      have hsplit : pmfMean (K j (ω (historyIndex T j)))
          (fun b => Real.exp (lam * g j (ω (historyIndex T j)) b
            - lam ^ 2 * v j (ω (historyIndex T j))))
          = Real.exp (-lam ^ 2 * v j (ω (historyIndex T j)))
            * pmfMean (K j (ω (historyIndex T j)))
              (fun b => Real.exp (lam * g j (ω (historyIndex T j)) b)) := by
        rw [← pmfMean_const_mul]
        apply pmfMean_congr
        intro b _
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      have hstep1 : F j ω * (Real.exp (-lam ^ 2 * v j (ω (historyIndex T j)))
          * pmfMean (K j (ω (historyIndex T j)))
            (fun b => Real.exp (lam * g j (ω (historyIndex T j)) b)))
          ≤ F j ω * (Real.exp (-lam ^ 2 * v j (ω (historyIndex T j)))
            * Real.exp (lam ^ 2 * v j (ω (historyIndex T j)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hmgf
                (by positivity : (0 : ℝ) ≤ Real.exp
                  (-lam ^ 2 * v j (ω (historyIndex T j)))))
              (by positivity : (0 : ℝ) ≤ F j ω)
      calc F j ω * (Real.exp (-lam ^ 2 * v j (ω (historyIndex T j)))
          * pmfMean (K j (ω (historyIndex T j)))
            (fun b => Real.exp (lam * g j (ω (historyIndex T j)) b)))
          ≤ F j ω * (Real.exp (-lam ^ 2 * v j (ω (historyIndex T j)))
            * Real.exp (lam ^ 2 * v j (ω (historyIndex T j)))) := hstep1
      _ = F j ω := by
            rw [← Real.exp_add]
            simp
    · rw [historyKernel, ite_eq_right (by omega : ¬ j < T), pmfMean_pure]
      simp only [hF]
      rw [historyAdditive_frozen g T j (by omega : T ≤ j),
        historyCounter_frozen v T j (by omega : T ≤ j)]
  induction k with
  | zero => simp
  | succ k ih =>
      have hunfold : pmfMean (historyLaw initial K T (k + 1)) (F (k + 1))
          = pmfMean (historyLaw initial K T k)
            (fun ω => pmfMean (historyKernel K T k ω) (F (k + 1))) := by
        change pmfMean ((historyLaw initial K T k).bind
          (historyKernel K T k)) (F (k + 1)) = _
        rw [pmfMean_bind]
      rw [hunfold]
      have hzero : pmfMean (historyLaw initial K T k)
          (fun ω => pmfMean (historyKernel K T k ω) (F (k + 1)))
          = pmfMean (historyLaw initial K T k)
            (fun ω => if ω ∈ (historyLaw initial K T k).support
              then pmfMean (historyKernel K T k ω) (F (k + 1)) else 0) := by
        apply pmfMean_congr
        intro ω hω
        simp [hω]
      rw [hzero]
      have hmono : pmfMean (historyLaw initial K T k)
          (fun ω => if ω ∈ (historyLaw initial K T k).support
            then pmfMean (historyKernel K T k ω) (F (k + 1)) else 0)
          ≤ pmfMean (historyLaw initial K T k) (F k) := by
            apply pmfMean_mono
            intro ω _
            by_cases hω : ω ∈ (historyLaw initial K T k).support
            · simpa [hω] using hone k ω hω
            · simp [hω]; positivity
      have hFk : pmfMean (historyLaw initial K T k) (F k)
          = pmfMean (historyLaw initial K T k)
            (fun ω => Real.exp (lam * historyAdditive g T k ω
              - lam ^ 2 * historyCounter v T k ω)) := by
            rfl
      exact hmono.trans (hFk.trans_le ih)

/-- **Fixed-λ Freedman-хвост с фактическим компенсатором**
(C356): P[S_k ≥ r ∧ C_k ≤ V] ≤ exp(−λ·r + λ²·V) для любого
λ ∈ [0, 1/c] и детерминированного порога V ≥ 0. Компенсатор
C_k — фактическая сумма условных дисперсий (не константа). -/
theorem history_variance_freedman_lam (initial : PMF α) (K : ℕ → α → PMF α)
    (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c lam : ℝ) (hlam : 0 ≤ lam) (hclam : lam * c ≤ 1)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyAdditive g T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0) ≤ Real.exp (-lam * r + lam ^ 2 * V) :=
  pmfMean_compensated_tail _ (historyAdditive g T k) (historyCounter v T k)
    lam r V hlam
    (history_exp_compensated_le initial K g v T c lam hlam hclam
      hbounded hmean hvar k)

/-- **Замкнутый радиус с variance-компенсатором** (C356):
оптимизация λ = r/(2·V) в режиме c·r ≤ 2·V (λ·c ≤ 1) даёт
P[S_k ≥ r ∧ C_k ≤ V] ≤ exp(−r²/(4·V)) — БЕЗ линейного члена,
строго сильнее базового радиуса exp(−r²/(4·(V+c·r))) при
c > 0, r > 0 в этом режиме. -/
theorem freedman_variance_radius (initial : PMF α) (K : ℕ → α → PMF α)
    (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 < V)
    (hrc : c * r ≤ 2 * V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyAdditive g T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0) ≤ Real.exp (-r ^ 2 / (4 * V)) := by
  have hlam : (0 : ℝ) ≤ r / (2 * V) := by positivity
  have hclam : r / (2 * V) * c ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * V)).mpr
    linarith
  have htail := history_variance_freedman_lam initial K g v T c (r / (2 * V))
    hlam hclam hbounded hmean hvar k r V hr hV.le
  have hexp : -(r / (2 * V)) * r + (r / (2 * V)) ^ 2 * V
      = -r ^ 2 / (4 * V) := by
    field_simp
    ring
  rw [hexp] at htail
  exact htail

/-- **Freedman-мост, variance-форма (C356, главный)**: при тех же
посылках, что `stochastic_safe_step_whp`, плюс режим
`hrc : c·r ≤ 2·T·σ`, drop = T·γ − r достигается с вероятностью
≥ 1 − exp(−r²/(4·T·σ)) — радиус без линейного члена, строго
лучше C350-го exp(−r²/(4·(T·σ+c·r))) в этом режиме. Компенсатор
в хвосте — фактический (capped) дисперсионный процесс
min(cond var, σ) ≤ σ глобально, поэтому ветка {C > T·σ} пуста
и union bound не нужен. Порог T·σ — детерминированный,
apriori наблюдаемый (premise-form). -/
theorem stochastic_safe_step_variance_whp (initial : PMF α)
    (K : ℕ → α → PMF α)
    (T : ℕ) (hT : 0 < T) (γ c σ r : ℝ)
    (hγ : 0 ≤ γ) (hc : 0 < c) (hσ : 0 ≤ σ) (hr : 0 < r)
    (hrc : c * r ≤ 2 * ((T : ℝ) * σ))
    (hdrop : r < T * γ)
    (h g : ℕ → α → α → ℝ) (drift : ℕ → α → ℝ)
    (h_noise_bounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (h_noise_cond_mean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (h_noise_cond_var : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ σ)
    (h_step_descent : ∀ k a b, drift k a - g k a b ≤ h k a b)
    (h_drift_floor : ∀ k a, γ ≤ drift k a) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if T * γ - r ≤ historyAdditive h T T ω then 1 else 0)
      ≥ 1 - Real.exp (-r ^ 2 / (4 * ((T : ℝ) * σ))) := by
    classical
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    have hmono : ∀ ω : History α T,
        historyAdditive (fun k a b => drift k a - g k a b) T T ω
          ≤ historyAdditive h T T ω :=
      fun ω => historyAdditive_mono _ _ T T ω
        (fun k a b => h_step_descent k a b)
    have hsplit := historyAdditive_drift_sub drift g T T
    have hfloor : ∀ ω : History α T,
        (T : ℝ) * γ ≤ driftAdditive drift T T ω := by
      intro ω
      unfold driftAdditive
      simp only [Nat.min_self]
      calc (T : ℝ) * γ = ∑ _j ∈ Finset.range T, γ := by
            rw [Finset.sum_const, Finset.card_range]; simp
        _ ≤ _ := Finset.sum_le_sum
          fun j _ => h_drift_floor j (ω (historyIndex T j))
    have hcover : ∀ ω : History α T,
        historyAdditive g T T ω ≤ r →
        T * γ - r ≤ historyAdditive h T T ω := by
      intro ω hSr
      have h1 := hmono ω
      rw [hsplit ω] at h1
      have h2 := hfloor ω
      linarith
    set v : ℕ → α → ℝ :=
      fun k a => min (pmfMean (K k a) (fun b => g k a b ^ 2)) σ with hv
    have hvarv : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
        pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a := by
      intro k _ a ha
      exact le_min_iff.mpr ⟨le_rfl, h_noise_cond_var k (by omega) a ha⟩
    have hVpos : (0 : ℝ) < (T : ℝ) * σ := by
      by_contra hcon
      push_neg at hcon
      have hle : c * r ≤ 0 := by linarith [hrc]
      have h1 : 0 < c * r := by positivity
      linarith
    have htail := freedman_variance_radius initial K g v T c hc
      h_noise_bounded h_noise_cond_mean hvarv T r ((T : ℝ) * σ) hr hVpos hrc
    have hcongr : pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T T ω then 1 else 0)
        = pmfMean (historyLaw initial K T T)
          (fun ω => if r ≤ historyAdditive g T T ω
            ∧ historyCounter v T T ω ≤ (T : ℝ) * σ then 1 else 0) := by
      apply pmfMean_congr
      intro ω _
      have hcb := historyCounter_var_le K g T T σ ω
      rw [← hv, Nat.min_self] at hcb
      simp [hcb]
    rw [← hcongr] at htail
    have hpt1 : ∀ ω : History α T,
        (if T * γ - r ≤ historyAdditive h T T ω then (1 : ℝ) else 0)
          ≥ (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0) := by
      intro ω
      by_cases hS : historyAdditive g T T ω ≤ r
      · have hcov := hcover ω hS
        simp [hcov, hS]
      · simp only [hS, ite_false, ge_iff_le]
        split_ifs <;> norm_num
    have hev1 : pmfMean (historyLaw initial K T T)
        (fun ω => if T * γ - r ≤ historyAdditive h T T ω then 1 else 0)
        ≥ pmfMean (historyLaw initial K T T)
        (fun ω => if historyAdditive g T T ω ≤ r then 1 else 0) :=
      pmfMean_mono _ (fun ω _ => hpt1 ω)
    have hswitch : pmfMean (historyLaw initial K T T)
        (fun ω => if historyAdditive g T T ω ≤ r then 1 else 0)
        ≥ 1 - pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T T ω then 1 else 0) := by
      have hpt2 : ∀ ω : History α T,
          (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
          + (if r ≤ historyAdditive g T T ω then (1 : ℝ) else 0) ≥ 1 := by
        intro ω
        by_cases hS : historyAdditive g T T ω ≤ r
        · by_cases hrS : r ≤ historyAdditive g T T ω <;>
            simp [hS, hrS]
        · have hrS : r ≤ historyAdditive g T T ω :=
            (not_le.mp hS).le
          simp [hS, hrS]
      have hsum : pmfMean (historyLaw initial K T T)
          (fun ω => (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
            + (if r ≤ historyAdditive g T T ω then (1 : ℝ) else 0))
          = pmfMean (historyLaw initial K T T)
              (fun ω => if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
            + pmfMean (historyLaw initial K T T)
              (fun ω => if r ≤ historyAdditive g T T ω then (1 : ℝ) else 0) :=
        pmfMean_add _ _ _
      have hge : (1 : ℝ) ≤ pmfMean (historyLaw initial K T T)
          (fun ω => (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
            + (if r ≤ historyAdditive g T T ω then (1 : ℝ) else 0)) :=
        le_trans (le_of_eq (pmfMean_const (historyLaw initial K T T) 1).symm)
          (pmfMean_mono (historyLaw initial K T T) (fun ω _ => hpt2 ω))
      rw [hsum] at hge
      linarith
    linarith

/-- Обёртка-сертификат (C356): variance-форма моста в форме
`CertStochasticStep`; failure = exp(−r²/(4·T·σ)) в режиме
c·r ≤ 2·T·σ. -/
noncomputable def stochastic_safe_step_variance (initial : PMF α)
    (K : ℕ → α → PMF α)
    (T : ℕ) (hT : 0 < T) (γ c σ r : ℝ)
    (hγ : 0 ≤ γ) (hc : 0 < c) (hσ : 0 ≤ σ) (hr : 0 < r)
    (hrc : c * r ≤ 2 * ((T : ℝ) * σ))
    (hdrop : r < T * γ)
    (h g : ℕ → α → α → ℝ) (drift : ℕ → α → ℝ)
    (h_noise_bounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (h_noise_cond_mean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (h_noise_cond_var : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ σ)
    (h_step_descent : ∀ k a b, drift k a - g k a b ≤ h k a b)
    (h_drift_floor : ∀ k a, γ ≤ drift k a) :
    CertStochasticStep (historyLaw initial K T T)
      (historyAdditive h T T) where
  drop := T * γ - r
  drop_pos := by
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    linarith
  failure := Real.exp (-r ^ 2 / (4 * ((T : ℝ) * σ)))
  descent_whp := stochastic_safe_step_variance_whp initial K T hT γ c σ r
    hγ hc hσ hr hrc hdrop h g drift h_noise_bounded h_noise_cond_mean
    h_noise_cond_var h_step_descent h_drift_floor

end

end Hagi.Probability
