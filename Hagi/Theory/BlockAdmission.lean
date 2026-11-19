/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.LMCompose
import Hagi.Architecture.OrthoInjection
import Hagi.Runtime.CertChecker
import Hagi.Theory.CertCEHoldout

/-!
# BlockAdmission — certified-адмиссия нового блока в растущую LM (C444)

Дорожная карта C441 (топ-3, рост/композиция): модель РАСТЁТ — новый
блок допускается в trunk LM только через certified-адмиссию.
Кандидат — орто-fiber-инъекция (посылки OrthoInjection-корпуса:
сигнал только в направлении, ортогональном cortex); критерий — в
стиле MemoryCycle/merge_gate (стоимость + риск + запас покрываются
выигрышем); soundness — через Lipschitz-композицию `trunk_lipschitz`
C436 (константа L_old·L_new, prefix-determined индукцией); отказ —
machine-checked контрпримером (дорогой блок с нулевым gain).

Что доказано:

* (cost) `lmKVCost_grow` — Δcost-канал: KV-стоимость grown-модели
  РАВНА старой + стоимость нового блока (механика `lmKVCost` /
  `gqaKVCost` C436, точное равенство — не телеметрия);
* (критерий a) `blockGainOk` / `blockAdmissionRule` — блок
  допускается, если `λM·Δcost + λR·Δrisk + ε_cert ≤ gain` (стиль
  MemoryCycle `gainOk` / merge_gate `MergeApproved`; значения —
  точные ℚ, как у демо-тренера);
* (b) `block_admission_sound` — при выполненном критерии, gain,
  ограниченном drop'ом certified-шага с валидной holdout-
  телеметрией (RiskChannel, C442), и Δcost = точном KV-приросте:
  grown trunk certified (константа Липшица `L_old·L_new`,
  dPre-граница, prefix-determined — `trunk_lipschitz` /
  `trunk_prefix_determined` C436 на append-списке) И certified
  drop покрывает `λM·Δcost + λR·Δrisk + ε_cert`;
* (c) отказ: `noBlockAdmissionWithoutMargin` (margin не выполнен ⇒
  правило отказывает), `costly_zero_gain_block_refused`
  (контрпример: gain = 0, Δcost = 2, λM = 1, ε = 0) и
  `composition_without_admission` — механическая Lipschitz-
  композиция верна для ЛЮБОГО certified-блока, но дорогой
  бесполезный кандидат НЕ допускается: gate реален, не телеметрия.

## Honest pins (что эта адмиссия НЕ покрывает)

- **gain — измеряемая величина** (certified drop шага обучения),
  а не доказанная априорная нижняя граница: посылка `hgain` в
  `block_admission_sound` — на потребителе, как `estimatedGain`-pin
  C390 (`Hagi.Training.Admission`).
- **Ville-часть — premise-form** (переиспользование паттерна C390
  `admit_sound` без пере-доказательства; слой Training(8) >
  Theory(7) — импорт нелегален): anytime-валидность измерений
  гарантируется потребителем через собственный e-process; здесь
  валидность телеметрии потребляется посылкой `hchan` (RiskChannel,
  C442) — точный accuracy-контракт risk-полей.
- **hLip кандидата — per-block premise** (контракт `CertifiedBlock`
  C436): операторная норма ‖A − U·(Uᵀ·A)‖_op не выводится здесь.
- **Δrisk — телеметрия** (holdout-канал C442/C435): может расти;
  чекер требует лишь 0 ≤ risk'. Критерий учитывает её честно
  (положительный Δrisk ест margin).
- Существование полезного блока НЕ доказывается: адмиссия —
  gate на предъявленный кандидат, не теорема существования.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.BlockAdmission

open Hagi.Model.LMCompose Hagi.Architecture Hagi.Runtime
open Hagi.Theory.CertCEHoldout (RiskChannel)
open Hagi.Theory.HoldoutRisk (holdoutMean)
open scoped Matrix NNReal

variable {V : Type} [Fintype V] {K : Type} [Fintype K] [Nonempty K]
  {d : ℕ}

/-! ## Cost-канал: точный Δcost роста -/

/-- KV-стоимость одного блока (механика `gqaKVCost` C436,
per-block геометрия nKv, d). -/
def kvCostOfBlock (T : ℕ) (b : CertifiedBlock V) : ℕ :=
  Hagi.Model.GQA.gqaKVCost T b.toTransformerBlock.nKv
    b.toTransformerBlock.d

/-- Grown-модель: та же голова, trunk + один блок. -/
def growLM (m : LM V K d) (b : CertifiedBlock V) : LM V K d :=
  { m with blocks := m.blocks ++ [b] }

omit [Nonempty K] in
/-- **Точный Δcost**: KV-стоимость grown-модели РАВНА старой плюс
стоимость нового блока (`List.sum_append` под `lmKVCost`). Это
равенство специфицирует Δcost-канал адмиссии через реальную
cost-механику C436 — не телеметрию. -/
theorem lmKVCost_grow (m : LM V K d) (T : ℕ) (b : CertifiedBlock V) :
    lmKVCost (growLM m b) T = lmKVCost m T + kvCostOfBlock T b := by
  simp only [lmKVCost, growLM, kvCostOfBlock, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]

/-! ## Композиция grown-trunk (механика C436 на append) -/

omit [Nonempty K] in
/-- Константа Липшица grown-trunk: произведение старой константы
на константу нового блока (`List.prod_append`). -/
theorem blocksLip_append_single (bs : List (CertifiedBlock V))
    (b : CertifiedBlock V) :
    blocksLip (bs ++ [b]) = blocksLip bs * b.lip := by
  simp [blocksLip, List.prod_append]

omit [Nonempty K] in
/-- Grown-trunk применяет новый блок ПОСЛЕДНИМ (foldl append). -/
theorem lmTrunk_append_single (bs : List (CertifiedBlock V))
    (b : CertifiedBlock V) (x : ℕ → V → ℝ) :
    lmTrunk (bs ++ [b]) x
      = blockApply b.toTransformerBlock (lmTrunk bs x) := by
  simp [lmTrunk, List.foldl_append]

omit [Nonempty K] in
/-- **Grown-trunk механика certified**: для ЛЮБОГО списка
certified-блоков и любого certified-кандидата append-композиция
Липшиц с константой `blocksLip trunk * lip b` и prefix-determined
— следствия `trunk_lipschitz` / `trunk_prefix_determined` C436 на
расширенном списке. Механика сама по себе адмиссию НЕ решает —
см. `composition_without_admission`. -/
theorem grown_trunk_mechanics (bs : List (CertifiedBlock V))
    (b : CertifiedBlock V) (x y : ℕ → V → ℝ) (t : ℕ)
    (hagree : ∀ i : ℕ, i ≤ t → ∀ v : V, x i v = y i v) :
    dPre (lmTrunk (bs ++ [b]) x) (lmTrunk (bs ++ [b]) y) t
      ≤ (blocksLip bs * b.lip : ℝ≥0) * dPre x y t
      ∧ ∀ v : V, lmTrunk (bs ++ [b]) x t v
          = lmTrunk (bs ++ [b]) y t v := by
  refine ⟨?_, trunk_prefix_determined (bs ++ [b]) x y t hagree⟩
  have h := trunk_lipschitz (bs ++ [b]) x y t
  rwa [blocksLip_append_single, NNReal.coe_mul] at h

/-! ## Кандидат: орто-fiber-инъекция (OrthoInjection-корпус) -/

section OrthoFiber

/-- Агрегатор орто-fiber-инъекции: читает скрытое состояние
позиции t и добавляет residual `(A − U·(Uᵀ·A)) *ᵥ x t` — сигнал
ТОЛЬКО в направлении, ортогональном cortex (свежее направление
роста; `fiberSplitOrtho`: cortex-координаты инъекции нулевые). -/
def orthoFiberAttn {d c : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (x : ℕ → Fin d → ℝ) : ℕ → Fin d → ℝ :=
  fun t v => x t v + ((A - U * (Uᵀ * A)) *ᵥ (x t)) v

/-- Transformer-блок-носитель орто-fiber-кандидата (norm = id,
GQA-геометрия nH = nKv = c). -/
def orthoFiberCore {d c : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) : TransformerBlock (Fin d) where
  attn := orthoFiberAttn U A
  norm := id
  nH := c
  nKv := c
  d := c

/-- Инъекция pointwise: значение на позиции t зависит только от
`x t` — нулевая утечка из будущего. -/
theorem orthoFiberAttn_pointwise {d c : ℕ}
    (U : Matrix (Fin d) (Fin c) ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (x y : ℕ → Fin d → ℝ) (t : ℕ) (h : x t = y t) :
    orthoFiberAttn U A x t = orthoFiberAttn U A y t := by
  unfold orthoFiberAttn
  rw [h]

/-- **Cortex-сохранение**: cortex-координаты скрытого состояния
не меняются инъекцией — буквально
`fiber_injection_preserves_cortex` (OrthoInjection) на payload
`x t`: весь сигнал роста идёт в ортогональном направлении. -/
theorem orthoFiberAttn_cortex_preserved {d c : ℕ}
    (U : Matrix (Fin d) (Fin c) ℝ) (hU : IsOrthoCol U)
    (A : Matrix (Fin d) (Fin d) ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) :
    Uᵀ *ᵥ (orthoFiberAttn U A x t) = Uᵀ *ᵥ (x t) := by
  unfold orthoFiberAttn
  exact fiber_injection_preserves_cortex U hU A (x t) (x t)

/-- Орто-fiber-блок prefix-determined: агрегатор pointwise +
norm = id ⇒ `blockApply` читает только текущую позицию
(per-block посылка `hCausal` контракта CertifiedBlock — доказана
здесь, а не постулирована). -/
theorem orthoFiberCore_causal {d c : ℕ}
    (U : Matrix (Fin d) (Fin c) ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (x y : ℕ → Fin d → ℝ) (t : ℕ)
    (hagree : ∀ i : ℕ, i ≤ t → ∀ v : Fin d, x i v = y i v) :
    ∀ v, blockApply (orthoFiberCore U A) x t v
      = blockApply (orthoFiberCore U A) y t v := by
  intro v
  have hx : orthoFiberAttn U A x t = orthoFiberAttn U A y t :=
    orthoFiberAttn_pointwise U A x y t
      (funext (fun v => hagree t (Nat.le_refl t) v))
  simp only [blockApply, orthoFiberCore]
  rw [hx, hagree t (Nat.le_refl t)]

/-- Блок-кандидат: орто-fiber-инъекция как `CertifiedBlock` —
`hCausal` доказан (`orthoFiberCore_causal`), `hLip` — per-block
premise (контракт C436: операторная норма инъекции на
потребителе; см. pins модуля). -/
def mkOrthoFiberBlock {d c : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (hLip : ℝ≥0)
    (hhLip : ∀ x y : ℕ → Fin d → ℝ, ∀ t : ℕ,
      dPre (blockApply (orthoFiberCore U A) x)
        (blockApply (orthoFiberCore U A) y) t
        ≤ (hLip : ℝ) * dPre x y t) : CertifiedBlock (Fin d) where
  attn := orthoFiberAttn U A
  norm := id
  nH := c
  nKv := c
  d := c
  lip := hLip
  hLip := hhLip
  hCausal := fun x y t hagree =>
    orthoFiberCore_causal U A x y t hagree

end OrthoFiber

/-! ## Критерий адмиссии (стиль MemoryCycle / merge_gate) -/

/-- Проверки адмиссии блока: измеренный gain (certified drop,
ℚ — как у демо-тренера), прирост стоимости Δcost (Δcost-канал
`lmKVCost_grow`), прирост риска Δrisk (holdout-телеметрия),
веса λM/λR и запас ε_cert (стиль MemoryCycle `AdmissionChecks`). -/
structure BlockAdmissionChecks where
  /-- Измеренный выигрыш (certified drop шага; premise, C390-pin). -/
  gain : ℚ
  /-- Прирост стоимости (KV-прирост через lmKVCost_grow). -/
  Δcost : ℚ
  /-- Прирост риска (holdout-телеметрия, C442/C435). -/
  Δrisk : ℚ
  /-- Вес стоимости. -/
  lamM : ℚ
  /-- Вес риска. -/
  lamR : ℚ
  /-- Запас на ошибку оценки. -/
  ε_cert : ℚ

/-- **Критерий (a)**: сертифицированная польза покрывает
стоимость + риск + запас: `λM·Δcost + λR·Δrisk + ε_cert ≤ gain`
(стиль MemoryCycle `gainOk` / merge_gate `MergeApproved`). -/
def blockGainOk (p : BlockAdmissionChecks) : Prop :=
  p.lamM * p.Δcost + p.lamR * p.Δrisk + p.ε_cert ≤ p.gain

/-- Исполнимая форма критерия (Bool на ℚ) — тот же Python-материал
демо `--mode grow`: `decide (λM·Δcost + λR·Δrisk + ε ≤ gain)`. -/
def blockAdmissionRule (p : BlockAdmissionChecks) : Bool :=
    decide (p.lamM * p.Δcost + p.lamR * p.Δrisk + p.ε_cert ≤ p.gain)

/-- Решение — в точности критерий: нет дрейфа между правилом и
его развёрткой (как `admitRule_iff` C390). -/
@[simp] theorem blockAdmissionRule_iff (p : BlockAdmissionChecks) :
    blockAdmissionRule p = true ↔ blockGainOk p := by
  simp only [blockAdmissionRule, blockGainOk, decide_eq_true_eq]

/-- **Gate closure**: невыполненный критерий ⇒ правило отказывает —
какой бы эвристикой ни был получен gain (аналог
`noAdmitWithoutPositiveMargin` C390). -/
theorem noBlockAdmissionWithoutMargin (p : BlockAdmissionChecks)
    (h : p.gain < p.lamM * p.Δcost + p.lamR * p.Δrisk + p.ε_cert) :
    blockAdmissionRule p = false := by
  refine decide_eq_false ?_
  exact not_le.2 h

/-- Контрпример-кандидат (c): нулевой gain, большая стоимость. -/
def costlyZeroGain : BlockAdmissionChecks where
  gain := 0
  Δcost := 2
  Δrisk := 0
  lamM := 1
  lamR := 0
  ε_cert := 0

/-- **Отказ (c), контрпример**: блок с большим cost и нулевым
gain НЕ допускается — margin 2 ≤ 0 ложен, правило отказывает
(COSTS VETO эвристически многообещающему блоку). -/
theorem costly_zero_gain_block_refused :
    blockAdmissionRule costlyZeroGain = false := by
  simp only [blockAdmissionRule, costlyZeroGain]
  norm_num

omit [Nonempty K] in
/-- **Отказ (c), механика ≠ адмиссия**: для ЛЮБОГО certified-блока
b grown-trunk механически certified (Lipschitz `L_old·L_new`,
prefix-determined — `grown_trunk_mechanics`), НО контрпримерный
кандидат `costlyZeroGain` критерий НЕ проходит: композиция
возможна всегда, адмиссия — нет. Gate реален, не телеметрия. -/
theorem composition_without_admission (bs : List (CertifiedBlock V))
    (b : CertifiedBlock V) (x y : ℕ → V → ℝ) (t : ℕ)
    (hagree : ∀ i : ℕ, i ≤ t → ∀ v : V, x i v = y i v) :
    dPre (lmTrunk (bs ++ [b]) x) (lmTrunk (bs ++ [b]) y) t
      ≤ (blocksLip bs * b.lip : ℝ≥0) * dPre x y t
      ∧ ¬ blockGainOk costlyZeroGain := by
  refine ⟨(grown_trunk_mechanics bs b x y t hagree).1, ?_⟩
  unfold blockGainOk costlyZeroGain
  norm_num

/-! ## Soundness (b): критерий ⇒ grown LM certified -/

omit [Nonempty K] in

/-- **block_admission_sound**: если (i) критерий выполнен
(`hcrit`: `λM·Δcost + λR·Δrisk + ε_cert ≤ gain`), (ii) gain —
честная доля certified-шага (`hgain`: gain ≤ drop), чья holdout-
телеметрия валидна (`hchan`: RiskChannel-контракт C442 — точное
равенство risk-полей holdout-средним; Ville/anytime-валидность
измерений — premise-form паттерна C390 `admit_sound`, см. pins),
и (iii) Δcost — точный KV-прирост (`hcost` через `lmKVCost_grow`),
ТО grown trunk certified: (1) certified drop покрывает
`λM·Δcost + λR·Δrisk + ε_cert` (стоимость и риск съедены
доказанным снижением, не эвристикой), (2) константа Липшица
grown-trunk = `L_old·L_new` (`blocksLip_append_single`), (3)
dPre-граница и (4) prefix-determined — индукция C436 на
append-списке. -/
theorem block_admission_sound {Ω Θ : Type}
    {ℓ : Θ → Ω → ℝ} {k : ℕ} {ωs : Fin k → Ω}
    (m : LM V K d) (b : CertifiedBlock V)
    (p : BlockAdmissionChecks) (T : ℕ) (θ θ' : Θ)
    (dstep : CertStepData)
    (hd : checkStep dstep = true)
    (hchan : Hagi.Theory.CertCEHoldout.RiskChannel ℓ θ θ' ωs dstep)
    (hgain : (p.gain : ℝ) ≤ (dstep.drop : ℝ))
    (hcost : (p.Δcost : ℝ) = (kvCostOfBlock T b : ℝ))
    (hrisk : (p.Δrisk : ℝ)
      = (dstep.risk' : ℝ) - (dstep.risk : ℝ))
    (hcrit : blockGainOk p)
    (x y : ℕ → V → ℝ) (t : ℕ)
    (hagree : ∀ i : ℕ, i ≤ t → ∀ v : V, x i v = y i v) :
    0 < (dstep.drop : ℝ)
      ∧ (p.lamM : ℝ) * (kvCostOfBlock T b : ℝ)
          + p.lamR * (holdoutMean (ℓ θ') ωs
            - holdoutMean (ℓ θ) ωs)
          + p.ε_cert ≤ (dstep.drop : ℝ)
      ∧ blocksLip (growLM m b).blocks = blocksLip m.blocks * b.lip
      ∧ dPre (lmTrunk (growLM m b).blocks x)
          (lmTrunk (growLM m b).blocks y) t
        ≤ (blocksLip m.blocks * b.lip : ℝ≥0) * dPre x y t
      ∧ ∀ v : V, lmTrunk (growLM m b).blocks x t v
          = lmTrunk (growLM m b).blocks y t v := by
  have hpos := (checkStep_spec hd).1
  have hmargin : (p.lamM * p.Δcost + p.lamR * p.Δrisk
      + p.ε_cert : ℚ) ≤ (dstep.drop : ℚ) :=
    le_trans hcrit (by exact_mod_cast hgain)
  have hg : (growLM m b).blocks = m.blocks ++ [b] := rfl
  rw [hg]
  refine ⟨by exact_mod_cast hpos, ?_,
    blocksLip_append_single m.blocks b,
    (grown_trunk_mechanics m.blocks b x y t hagree).1,
    (grown_trunk_mechanics m.blocks b x y t hagree).2⟩
  have h1 : (p.lamM * p.Δcost + p.lamR * p.Δrisk
      + p.ε_cert : ℝ) ≤ (dstep.drop : ℝ) := by exact_mod_cast hmargin
  -- the risk part of the margin rides the VALID holdout channel
  -- (hchan): the declared Δrisk equals the exact readout delta
  -- (hrisk), and hchan certifies those readouts are the holdout
  -- means of the pre-/post-admission models
  have hchan' : (dstep.risk' : ℝ) - (dstep.risk : ℝ)
      = holdoutMean (ℓ θ') ωs - holdoutMean (ℓ θ) ωs := by
    rw [← hchan.1, ← hchan.2]
  rw [hcost, hrisk, hchan'] at h1
  exact h1

end Hagi.Theory.BlockAdmission
