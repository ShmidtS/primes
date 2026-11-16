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
  фиксированного хвоста из базовой теоремы;
* дисперсионный компенсатор константный (посылка (b) задачи:
  условная дисперсия ≤ σ²); адаптивный компенсатор потребовал бы
  union bound по ветке {компенсатор > V}, которого в базе нет;
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

end Hagi.Probability
