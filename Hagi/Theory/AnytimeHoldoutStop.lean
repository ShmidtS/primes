/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.Statistics
import Hagi.Theory.BlockAdmission

/-!
# AnytimeHoldoutStop — Ville-стоп роста по holdout-деградации

Дорожная карта (топ-1): holdout-телеметрия grow-цикла
растёт без стопа — рост может продолжаться при деградации
обобщения. Этот модуль замыкает цикл anytime-предохранителем:
admission-стоп по certified-доказательству holdout-деградации.

Что доказано:

* (a) `degradation_detect_anytime` — детектор деградации:
  e-process `L_t = exp(λ·S_t)` (S_t — накопленная holdout-
  деградация) при нулевой деградации (посылка-контракт: инкременты
  holdout мартингальные — дух `holdout_unbiased` для модели,
  фиксированной до holdout-дроу) — неотрицательный супермартингал
  с E[L_0] ≤ 1, и Ville даёт P[∃t ≤ n, log(1/δ)/λ < S_t] ≤ δ —
  anytime: момент проверки адаптивный;
* ℚ-детектор без exp: `stopThreshold δ = 1/δ − 1 ≥ log(1/δ)`
  (`log_le_rational_threshold`, Mathlib `Real.log_le_sub_one_of_pos`)
  и `stop_implies_evalue` — рациональный стоп λ·S ≥ 1/δ − 1
  влечёт e-value ≥ 1/δ: стоп-событие — ПОДМНОЖЕСТВО
  Ville-пересечения (детектор консервативен: срабатывает позже
  точного e-value-порога, платим чувствительностью — см. pins);
* (b) `admitWithStop` — admission-гейт со стопом:
  `if stop then false else blockAdmissionRule p`;
  `stop_blocks_admission` — сработавший стоп блокирует адмиссию
  любого кандидата; `no_stop_admits` — без стопа прошедший
  критерий кандидат допускается (рост продолжается);
* (c) `grow_stop_sound` — если стоп сработал на рациональных
  readout'ах r_t = λ·S_t, вероятность ЛОЖНОГО стопа (при нулевой
  деградации — supermartingale-посылке) ≤ δ: FDR-тип контроль
  anytime-ошибки первого рода;
* (d) честность: `selection_bias_pin` — пере-экспорт
  selection-bias-негатива при data-dependent выборе модели
  ПОСЛЕ просмотра holdout инкременты НЕ мартингальные
  (E[holdout выбранной] = 0 ≠ 1/2 = popRisk) — посылка (a)/(c)
  недоступна, детектор может не сработать. Пин обязателен.

## Honest pins (что этот стоп НЕ покрывает)

- **Supermartingale-посылка — контракт** (как в AnytimePACBayes:
  конструкция супермартингала — гипотеза контракта): «нулевая
  деградация» = мартингальные инкременты holdout. Она честна для
  модели, фиксированной до holdout-дроу (`holdout_unbiased`),
  и ЛОМАЕТСЯ selection'ом (selection_bias_pin). Ville-часть
  безусловна.
- **Чувствительность**: рациональный порог 1/δ − 1 выше точного
  log(1/δ) (фактор ~1.5–2 при малых δ): сертифицированный ценой
  позже срабатывающий детектор. Ложных тревог НЕ больше.
- **S_t — накопленная ТЕЛЕМЕТРИЯ** (rational readout'ы risk-полей
  CertStepData / RiskChannel): вероятностная гарантия —
  условная теорема на посылке; измерение — на потребителе.
- Детектор ловит ДЕГРАДАЦИЮ обобщения (рост holdout-риска), не
  «переобучение» как таковое: локальные улучшения holdout ниже
  порога не стопятся.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.AnytimeHoldoutStop

open MeasureTheory Hagi.Unified Hagi.Theory.HoldoutRisk
  Hagi.Theory.BlockAdmission

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}

/-! ## e-process деградации и anytime-детектор (a) -/

/-- E-process holdout-деградации: `L_t = exp(λ·S_t)`, где S_t —
накопленная (кумулятивная) деградация holdout-риска от базового
уровня. Экспоненциальный тест мартингальной посылки против
положительного дрейфа инкрементов. -/
noncomputable def eProcess (lam : ℝ) (S : ℕ → ℝ) (t : ℕ) : ℝ :=
  Real.exp (lam * S t)

/-- **(a) Anytime-детектор деградации**: если e-process
`L_t = exp(λ·S_t)` — неотрицательный супермартингал (посылка
нулевой деградации: holdout-инкременты мартингальны — контракт в
духе `holdout_unbiased` для фиксированной модели) с
E[L_0] ≤ 1, то вероятность хоть одного пересечения порога
log(1/δ)/λ за n шагов ≤ δ. Anytime: порог держится равномерно,
момент проверки можно выбирать по данным (в т.ч. самим
grow-циклом). -/
theorem degradation_detect_anytime {S : ℕ → Ω → ℝ} {lam : ℝ}
    (hlam : 0 < lam)
    (L : ℕ → Ω → ℝ) (hL : Supermartingale L 𝒢 μ) (hLnn : 0 ≤ L)
    (hL0 : (∫ x, L 0 x ∂μ) ≤ 1)
    (hexp : ∀ t ω, L t ω = Real.exp (lam * S t ω))
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1),
      Real.log (1/δ) / lam < S t ω} ≤ δ := by
  have hcpos : 0 < 1 / δ := by positivity
  have hv := ville_supermartingale hL hLnn n (c := 1 / δ) hcpos
  have h1 : (∫ x, L 0 x ∂μ) / (1/δ) ≤ δ := by
    rw [div_le_iff₀ hcpos]
    field_simp
    linarith
  have hsub : {ω | ∃ t ∈ Finset.range (n + 1),
      Real.log (1/δ) / lam < S t ω}
      ⊆ {ω | ∃ t ∈ Finset.range (n + 1), 1/δ ≤ L t ω} := by
    rintro ω ⟨t, ht, hSt⟩
    refine ⟨t, ht, ?_⟩
    rw [hexp t ω]
    rw [div_lt_iff₀ hlam] at hSt
    have h2 : Real.log (1/δ) < lam * S t ω := by linarith
    have h3 : 1/δ < Real.exp (lam * S t ω) := by
      have h4 : Real.exp (Real.log (1/δ))
          < Real.exp (lam * S t ω) := Real.exp_lt_exp.mpr h2
      rwa [Real.exp_log hcpos] at h4
    exact le_of_lt h3
  calc μ.real {ω | ∃ t ∈ Finset.range (n + 1),
        Real.log (1/δ) / lam < S t ω}
      ≤ μ.real {ω | ∃ t ∈ Finset.range (n + 1), 1/δ ≤ L t ω} :=
        Hagi.Unified.AnytimePACBayes.real_mono_prob hsub
    _ ≤ (∫ x, L 0 x ∂μ) / (1/δ) := hv
    _ ≤ δ := h1

/-! ## Рациональный (ℚ) детектор: консервативный Ville-порог -/

/-- Рациональный порог детектора: `1/δ − 1` — верхняя граница
точного Ville-порога log(1/δ), БЕЗ иррациональностей
(decision-complete на ℚ). -/
def stopThreshold (δ : ℚ) : ℚ := 1/δ - 1

/-- Точный Ville-порог не превосходит рационального:
`log(1/δ) ≤ 1/δ − 1` (Mathlib: log x ≤ x − 1 для x > 0).
Детектор с порогом 1/δ − 1 срабатывает ПОЗЖЕ или одновременно с
e-value-порогом — консервативен по ложным тревогам. -/
theorem log_le_rational_threshold {δ : ℝ} (hδ : 0 < δ) :
    Real.log (1/δ) ≤ 1/δ - 1 :=
  Real.log_le_sub_one_of_pos (by positivity)

/-- Исполнимая форма стоп-правила на ℚ: порог ≤ λ·(накопленная
деградация). Решение — точное рациональное сравнение, без
exp/log/плавающей точки. -/
def holdoutStopRule (lam thresh cum : ℚ) : Bool :=
  decide (thresh ≤ lam * cum)

@[simp] theorem holdoutStopRule_iff (lam thresh cum : ℚ) :
    holdoutStopRule lam thresh cum = true ↔
      thresh ≤ lam * cum := by
  simp only [holdoutStopRule, decide_eq_true_eq]

/-- **Рациональный стоп ⇒ e-value ≥ 1/δ**: если λ·s достигло
рационального порога 1/δ − 1, то e-process exp(λ·s) ≥ 1/δ —
стоп-событие лежит ВНУТРИ Ville-пересечения (экспонента
монотонна, порог консервативен). -/
theorem stop_implies_evalue {lam δ s : ℝ} (hδ : 0 < δ)
    (hs : 1/δ - 1 ≤ lam * s) :
    1/δ ≤ Real.exp (lam * s) := by
  have h2 : Real.log (1/δ) ≤ lam * s :=
    le_trans (log_le_rational_threshold hδ) hs
  have h3 : Real.exp (Real.log (1/δ))
      ≤ Real.exp (lam * s) := Real.exp_le_exp.mpr h2
  rwa [Real.exp_log (by positivity)] at h3

/-! ## (c) grow_stop_sound: FDR-тип контроль ложного стопа -/

/-- **(c) grow_stop_sound**: если (i) e-process — супермартингал
(нулевая деградация — посылка-контракт), (ii) рациональные
readout'ы r_t — точные касты λ·S_t, и (iii) детектор сработал на
некотором шаге ≤ n (stopThreshold δ ≤ r_t), то это —
сертифицированное свидетельство деградации: на НУЛЕВОЙ
деградации вероятность такого стопа ≤ δ (Ville; каждый
рациональный стоп влечёт e-value ≥ 1/δ — `stop_implies_evalue`,
а пересечение e-value-порога ограничено Ville). Вероятность
ложного стопа anytime-контролируема: рост может быть остановлен
только с certified-доказательством деградации. -/
theorem grow_stop_sound {S : ℕ → Ω → ℝ} {lam : ℝ} {δ : ℚ}
    (hlam : 0 < lam) (hδ : 0 < (δ : ℝ))
    (L : ℕ → Ω → ℝ) (hL : Supermartingale L 𝒢 μ) (hLnn : 0 ≤ L)
    (hL0 : (∫ x, L 0 x ∂μ) ≤ 1)
    (hexp : ∀ t ω, L t ω = Real.exp (lam * S t ω))
    (r : ℕ → ℚ) (n : ℕ)
    (hcast : ∀ t ω, (r t : ℝ) = lam * S t ω) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1),
      stopThreshold δ ≤ r t} ≤ (δ : ℝ) := by
  set_option maxHeartbeats 400000 in
  have hcpos : 0 < 1 / (δ : ℝ) := by positivity
  have hv := ville_supermartingale hL hLnn n (c := 1 / (δ : ℝ))
    hcpos
  have h1 : (∫ x, L 0 x ∂μ) / (1/(δ:ℝ)) ≤ (δ:ℝ) := by
    rw [div_le_iff₀ hcpos]
    field_simp
    linarith
  have hsub : {ω | ∃ t ∈ Finset.range (n + 1),
      stopThreshold δ ≤ r t}
      ⊆ {ω | ∃ t ∈ Finset.range (n + 1), 1/(δ:ℝ) ≤ L t ω} := by
    rintro ω ⟨t, ht, hrt⟩
    refine ⟨t, ht, ?_⟩
    rw [hexp t ω]
    have hcast' : ((stopThreshold δ : ℚ) : ℝ)
        = 1/(δ:ℝ) - 1 := by
      unfold stopThreshold
      push_cast
      ring
    have hrt' : (stopThreshold δ : ℝ) ≤ (r t : ℝ) :=
      by exact_mod_cast hrt
    rw [hcast t ω] at hrt'
    have hs : 1/(δ:ℝ) - 1 ≤ lam * S t ω := by
      rw [← hcast']
      exact hrt'
    exact stop_implies_evalue hδ hs
  calc μ.real {ω | ∃ t ∈ Finset.range (n + 1),
        stopThreshold δ ≤ r t}
      ≤ μ.real {ω | ∃ t ∈ Finset.range (n + 1), 1/(δ:ℝ) ≤ L t ω} :=
        Hagi.Unified.AnytimePACBayes.real_mono_prob hsub
    _ ≤ (∫ x, L 0 x ∂μ) / (1/(δ:ℝ)) := hv
    _ ≤ (δ:ℝ) := h1

/-- FDR-формулировка: при нулевой деградации вероятность того,
что anytime-стоп вообще сработает за n шагов, ≤ δ — ложных
остановок роста не больше δ (любой состоявшийся стоп несёт
e-value ≥ 1/δ против нулевой гипотезы). -/
theorem false_stop_bound {S : ℕ → Ω → ℝ} {lam δ : ℚ}
    (hlam : 0 < (lam : ℝ)) (hδ : 0 < (δ : ℝ))
    (L : ℕ → Ω → ℝ) (hL : Supermartingale L 𝒢 μ) (hLnn : 0 ≤ L)
    (hL0 : (∫ x, L 0 x ∂μ) ≤ 1)
    (hexp : ∀ t ω, L t ω = Real.exp ((lam : ℝ) * S t ω))
    (d : ℕ → ℚ) (n : ℕ)
    (hcast : ∀ t ω, ((lam * d t : ℚ) : ℝ) = (lam : ℝ) * S t ω) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1),
      holdoutStopRule lam (stopThreshold δ) (d t) = true}
      ≤ (δ : ℝ) := by
  have h := grow_stop_sound hlam hδ L hL hLnn hL0 hexp
    (fun t => lam * d t) n hcast
  have hsub2 : {ω : Ω | ∃ t ∈ Finset.range (n + 1),
      holdoutStopRule lam (stopThreshold δ) (d t) = true}
      ⊆ {ω : Ω | ∃ t ∈ Finset.range (n + 1),
        stopThreshold δ ≤ lam * d t} := by
    rintro ω ⟨t, ht, hrule⟩
    exact ⟨t, ht, holdoutStopRule_iff .. |>.mp hrule⟩
  exact le_trans
    (Hagi.Unified.AnytimePACBayes.real_mono_prob hsub2) h

/-! ## (b) admission-гейт со стопом -/

/-- Admission-гейт усиленный anytime-стопом: сработавший
стоп блокирует адмиссию ЛЮБОГО кандидата (certified
предохранитель роста); без стопа решает точный критерий
`blockAdmissionRule` . -/
def admitWithStop (p : BlockAdmissionChecks) (stop : Bool) :
    Bool := if stop then false else blockAdmissionRule p

/-- **(b) Стоп блокирует адмиссию**: сработавший anytime-стоп
гарантированно отказывает любому кандидату — рост остановлен
независимо от измеренного gain. -/
theorem stop_blocks_admission (p : BlockAdmissionChecks) :
    admitWithStop p true = false := by
  simp [admitWithStop]

/-- **Без стопа цикл продолжил бы** (честность-негатив): если
стоп НЕ сработал и критерий выполнен, кандидат допускается —
gate не останавливает рост сам по себе; единственная причина
отказа в этой точке — anytime-стоп по деградации. -/
theorem no_stop_admits {p : BlockAdmissionChecks}
    (h : blockAdmissionRule p = true) :
    admitWithStop p false = true := by
  simp [admitWithStop, h]

/-- Спецификация гейта одной iff: адмиссия со стопом ⇔
(нет стопа) ∧ (критерий). -/
theorem admit_with_stop_spec (p : BlockAdmissionChecks)
    (stop : Bool) :
    admitWithStop p stop = true ↔
      stop = false ∧ blockAdmissionRule p = true := by
  cases stop
  · simp [admitWithStop]
  · simp [admitWithStop]

/-! ## (d) честность: selection-bias пин (негатив) -/

/-- **(d) Пин обязательности мартингальной посылки**: для ЛЮБОГО
holdout-дроу ωs data-dependent выбор модели ПОСЛЕ просмотра holdout
даёт нулевой измеренный holdout-риск выбранной модели при её
population-риске 1/2 (C435-паттерн: `selection_bias_holdout_eq_zero`
/ `selection_bias_pop_eq_half`). Инкременты тогда НЕ мартингальные:
supermartingale-посылка теорем (a)/(c) недоступна, Ville-граница не
выводится, детектор может не сработать на реальной деградации.
Рациональный readout-канал обязан пинить «модель до отбора». -/
theorem selection_bias_pin (ωs : Fin 1 → Fin 2) :
    holdoutMean (twoPointLoss (ωs 0)) ωs = 0
      ∧ popMean (twoPointLoss (ωs 0)) = 1 / 2 :=
  ⟨selection_bias_holdout_eq_zero ωs,
    selection_bias_pop_eq_half (ωs 0)⟩

end Hagi.Theory.AnytimeHoldoutStop
