/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Model.LMCompose
import Hagi.Theory.BlockAdmission

/-!
# FunctionPreservingGrowth — функция-сохраняющее расширение (A19.5)

Аудит N8: 14 модулей Core/Architecture — острова; центральная идея
«точное слияние/расширение экспертов» (`step0_equivalence` Core/
BlockDiag, `zero_init_identity` Core/NonlinearStep0) не подключена
ни к росту (BlockAdmission C444 / `growLM`), ни к циклу. Этот
модуль — мост (одна теорема-семейство, не переноска островов):

* `identityBlock` — step-0 блок (zero-init attention, identity
  norm): hLip/hCausal ВЫВЕДЕНЫ, не постулированы — blockApply
  identity-блока = id. Это паттерн `zero_init_identity` /
  `step0_equivalence` на носителе контракта `CertifiedBlock`.
* (a) `trunk_function_preserving` — расширение trunk'а
  identity-блоком сохраняет функцию ТОЧНО (равенство, не «≤ ε»);
  следствия `lmLogits_grow_identity` / `lmProbs_grow_identity` —
  grown LM и старая LM вычисляют одни и те же логиты/вероятности.
* (b) `blocksLip_grow_identity` — константа Липшица не меняется
  (`L_old · 1 = L_old`: lip-добавка на шаге 0 = 0, выведена);
  общий случай — per-block premise контракта C436/C444 (см. pins).
* (c) `function_preserving_admissible` — в НЕЙТРАЛЬНОЙ конфигурации
  адмиссии (λM = λR = 0, ε_cert = 0) identity-блок проходит
  `blockAdmissionRule` при любом Δcost: gain = 0 на шаге 0 (точное
  равенство ⇒ нулевой certified drop), блок не портит модель —
  польза приходит из последующего certified-обучения головы/блока.
  Контр-симметрия `margin_positivity_refuses`: ε_cert > 0 ⇒ gate
  отказывает — нейтральность не обходит gate.
* (d) `zero_init_orthoFiber_identity` — орто-fiber-кандидат C444
  (`orthoFiberAttn U A`) при A = 0 — step-0 инстанс: инъекция = id;
  KV-стоимость роста — точный канал `lmKVCost_grow` C444.

Cycle-соответствие: `scripts/bench_bridge.py --mode grow` исполняет
то же правило `decide (λM·Δcost + λR·Δrisk + ε_cert ≤ gain)`
(`blockAdmissionRule`); функция-сохраняющее расширение — его
граничный случай (gain = 0, λ = ε = 0): демо-тренер допускает
нейтральный блок и учит его после — семантика
`function_preserving_admissible` + certified head-step.

## Honest pins (что этот мост НЕ покрывает)

- **gain после шага 0** — measured (certified drop шага обучения),
  не доказанная нижняя граница; на шаге 0 gain = 0 по построению.
- **lip после обучения** — per-block premise контракта
  `CertifiedBlock` (C436/C444): операторная норма обученного
  блока на потребителе. На шаге 0 добавка = 0 выведена здесь.
- **Существование полезного блока** не доказывается: мост —
  gate-совместимость нейтрального расширения, не теорема
  существования (тот же pin, что у BlockAdmission C444).
- **Носители BlockDiag/NonlinearStep0** (Σ-тип, Fin N → V) и
  `CertifiedBlock` (ℕ → V → ℝ) различны: перенос ФОРМУЛЫ
  step0-эквивалентности = identity-инициализация здесь;
  дословная унификация носителей — вне этого бита (KISS).
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.FunctionPreservingGrowth

open Hagi.Model.LMCompose Hagi.Theory.BlockAdmission

variable {V : Type} [Fintype V]

/-! ## Step-0 блок: identity-инициализация как CertifiedBlock -/

/-- Step-0 блок: zero-init attention (`attn = 0`), identity norm,
`lip = 1`. Посылки контракта `CertifiedBlock` ВЫВЕДЕНЫ: `blockApply`
этого блока — тождественное преобразование (паттерн
`zero_init_identity` Core/NonlinearStep0; блочно-диагональная
семантика `step0_equivalence` Core/BlockDiag: новый блок ничего
не меняет — точно). -/
def identityBlock : CertifiedBlock V where
  attn := fun _ _ _ => 0
  norm := fun v => v
  nH := 1
  nKv := 1
  d := 1
  lip := 1
  hLip := by
    intro x y t
    simp [blockApply, dPre]
  hCausal := by
    intro x y t hagree v
    simp only [blockApply]
    rw [hagree t (Nat.le_refl t)]

/-- Тождественность: `blockApply` identity-блока = id — точное
равенство функций (step-0 условие). -/
theorem blockApply_identityBlock (x : ℕ → V → ℝ) :
    blockApply identityBlock.toTransformerBlock x = x := by
  funext t v
  simp [blockApply, identityBlock]

/-! ## (a) Точное сохранение функции при росте -/

/-- **Мост (a)**: расширение trunk'а identity-блоком сохраняет
функцию ТОЧНО — `lmTrunk (bs ++ [identityBlock]) x = lmTrunk bs x`
(равенство последовательностей, не «≤ ε»). Это перенос сути
`step0_equivalence` (в блоке k merged-слой = эксперту k) на рост:
grown trunk = старый trunk всюду. -/
theorem trunk_function_preserving (bs : List (CertifiedBlock V))
    (x : ℕ → V → ℝ) :
    lmTrunk (bs ++ [identityBlock]) x = lmTrunk bs x := by
  rw [lmTrunk_append_single, blockApply_identityBlock]

variable {K : Type} [Fintype K] {d : ℕ}

/-- Следствие (a): grown LM (`growLM` C444 с identity-блоком) и
старая LM имеют ОДИНАКОВЫЕ логиты — certified-голова читает тот же
trunk (`lmFeatures` зависит от trunk'а линейно). -/
theorem lmLogits_grow_identity (m : LM V K d) (x : ℕ → V → ℝ) (t : ℕ) :
    lmLogits (growLM m (identityBlock (V := V))) x t = lmLogits m x t := by
  simp only [lmLogits, lmFeatures, growLM, trunk_function_preserving]

/-- Следствие (a): grown LM и старая LM задают ОДИНАКОВЫЕ выходные
распределения (`lmProbs` = softmax тех же логитов) — функция модели
сохранена точно. -/
theorem lmProbs_grow_identity (m : LM V K d) (x : ℕ → V → ℝ) (t : ℕ) :
    lmProbs (growLM m (identityBlock (V := V))) x t = lmProbs m x t := by
  simp only [lmProbs, lmLogits_grow_identity]

/-! ## (b) Константа Липшица: добавка 0 на шаге 0 -/

/-- **Мост (b)**: константа Липшица grown-trunk РАВНА старой:
`L_old · lip(identity) = L_old · 1 = L_old` (`blocksLip_append_single`
C444; lip-добавка = 0 выведена честно из identity-инициализации).
После обучения добавка — per-block premise контракта C436 (pins). -/
theorem blocksLip_grow_identity (bs : List (CertifiedBlock V)) :
    blocksLip (bs ++ [identityBlock]) = blocksLip bs := by
  rw [blocksLip_append_single]
  simp [identityBlock]

/-- Полная формулировка моста (a)+(b): grown LM = старая LM по
функции (логиты и вероятности) И константа Липшица не выросла. -/
theorem function_preserving_growth (m : LM V K d)
    (x : ℕ → V → ℝ) (t : ℕ) :
    lmProbs (growLM m (identityBlock (V := V))) x t = lmProbs m x t
      ∧ blocksLip (growLM m (identityBlock (V := V))).blocks
        = blocksLip m.blocks :=
  ⟨lmProbs_grow_identity m x t, blocksLip_grow_identity m.blocks⟩

/-! ## (c) Адмиссия нейтрального блока (честная) -/

/-- Нейтральная конфигурация адмиссии для step-0 кандидата:
gain = 0 (точное равенство ⇒ нулевой certified drop), Δrisk = 0,
λM = λR = 0, ε_cert = 0; Δcost = фактический KV-прирост
(`kvCostOfBlock`/`lmKVCost_grow` C444) — любое. -/
def neutralGrowthChecks (kv : ℚ) : BlockAdmissionChecks where
  gain := 0
  Δcost := kv
  Δrisk := 0
  lamM := 0
  lamR := 0
  ε_cert := 0

/-- **Мост (c), честная лемма**: identity-блок адмиссимён в
НЕЙТРАЛЬНОЙ конфигурации: `0 + 0 + 0 ≤ 0` — блок не портит модель
(мост (a)), не растит риск (Δrisk = 0) и проходит gate при любом
Δcost, потому что веса и запас выключены. Польза НЕ на шаге 0 —
она из последующего certified-обучения (head-step на расширенной
модели); на шаге 0 блок гарантированно нейтрален. -/
theorem function_preserving_admissible (kv : ℚ) :
    blockAdmissionRule (neutralGrowthChecks kv) = true := by
  simp [blockAdmissionRule, neutralGrowthChecks]

/-- Строгая (не нейтральная) конфигурация: положительный запас. -/
def strictGrowthChecks (kv ε : ℚ) : BlockAdmissionChecks where
  gain := 0
  Δcost := kv
  Δrisk := 0
  lamM := 0
  lamR := 0
  ε_cert := ε

/-- **Контр-симметрия (c)**: gate реален — нейтральность не
обходит его: при ε_cert > 0 правило ОТКАЗЫВАЕТ (0 < ε нарушает
margin), сколь бы «безвреден» ни был блок. Адмиссия выше — граничный
случай, не лазейка (симметр `noBlockAdmissionWithoutMargin` C444). -/
theorem margin_positivity_refuses (kv ε : ℚ) (hε : 0 < ε) :
    blockAdmissionRule (strictGrowthChecks kv ε) = false := by
  refine decide_eq_false ?_
  simp only [strictGrowthChecks]
  norm_num
  linarith

/-! ## (d) Step-0 инстанс орто-fiber-кандидата C444 -/

/-- **Мост (d)**: орто-fiber-инъекция C444 (`orthoFiberAttn U A`)
при A = 0 — тождественна: резидуал `(A − U·(Uᵀ·A)) *ᵥ x` нулевой
(любой U). Так `mkOrthoFiberBlock U 0` — step-0 инстанс моста:
рост начинается функция-сохраняющим орто-блоком, дальнейший сигнал
идёт строго в ортогональном cortex направлении
(`fiber_injection_preserves_cortex`, C444/CortexFiber);
KV-стоимость роста — точный канал `lmKVCost_grow` C444. -/
theorem zero_init_orthoFiber_identity {D C : ℕ}
    (U : Matrix (Fin D) (Fin C) ℝ)
    (x : ℕ → Fin D → ℝ) (t : ℕ) :
    orthoFiberAttn U 0 x t = x t := by
  unfold orthoFiberAttn
  simp

end Hagi.Theory.FunctionPreservingGrowth
