/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Model.LMCompose
import Hagi.Theory.BlockAdmission
import Hagi.Theory.RollbackGate

/-!
# FunctionPreservingGrowth — функция-сохраняющее расширение (A19.5)

Аудит N8: 14 модулей Core/Architecture — острова; центральная идея
«точное слияние/расширение экспертов» (`step0_equivalence` Core/
BlockDiag, `zero_init_identity` Core/NonlinearStep0) не подключена
ни к росту (BlockAdmission / `growLM`), ни к циклу. Этот
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
  общий случай — per-block premise контракта (см. pins).
* (e) Post warm-up сертификат роста (C642) — `warmup_safe`: при
  identity-старте и certified-шагах train-objective ≤ fOld при
  любом вердикте holdout-гейта.
* (f) Контракт certified-шага (C644) — `CertifiedFiniteStep`
  (COMMIT: drop выше порога ∧ obj θ' ≤ obj θ − drop; HOLD: точный
  rollback, drop = 0) ⇒ h1 (`warmup_h1_of_certified_steps`) ⇒
  композиция с (e); негативы: uncertified-шаг контракт не проходит,
  per-batch drop на другой objective не телескопирует.
* (g) Certified-шаг на параметрах БЛОКА (C646) — range-лемма CE
  живёт на ЛОГИТАХ (`Hagi.Energy.lse_shift_upper`), носитель θ не
  входит: `certified_step_block_of_range` (любое `L : B → K → ℝ`),
  `block_step_certified_of_range_bound` / `block_step_commit_of_range_bound`
  (COMMIT-ветка контракта для `CE ∘ L`); негатив
  `block_range_bound_violated_not_certified`.
* (h) Полезность первого шага (C657) — `useful_first_step`
  (drop(η) = |a|η − R²η²/8, η* = 4|a|/R², drop_max = 2a²/R²),
  `useful_eta_le` (максимум единственный), `exists_useful_eta`,
  `first_step_useful_certified` (COMMIT-контракт на `CE_t ∘ L`),
  `first_step_strict_improves` (obj < fOld); негатив
  `no_signal_no_drop` (a = 0 ⇒ drop ≤ 0).
* (c) `function_preserving_admissible` — в НЕЙТРАЛЬНОЙ конфигурации
  адмиссии (λM = λR = 0, ε_cert = 0) identity-блок проходит
  `blockAdmissionRule` при любом Δcost: gain = 0 на шаге 0 (точное
  равенство ⇒ нулевой certified drop), блок не портит модель —
  польза приходит из последующего certified-обучения головы/блока.
  Контр-симметрия `margin_positivity_refuses`: ε_cert > 0 ⇒ gate
  отказывает — нейтральность не обходит gate.
* (d) `zero_init_orthoFiber_identity` — орто-fiber-кандидат
  (`orthoFiberAttn U A`) при A = 0 — step-0 инстанс: инъекция = id;
  KV-стоимость роста — точный канал `lmKVCost_grow` .

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
  `CertifiedBlock`: операторная норма обученного
  блока на потребителе. На шаге 0 добавка = 0 выведена здесь.
- **Существование полезного блока** — ЛОКАЛЬНО доказано (C657,
  секция «Полезность первого warm-up шага»): при линейном по η
  смещении логитов, descent-сигнале `a < 0` и `stepEps < 2a²/R²`
  первый шаг блока certified COMMIT (`first_step_useful_certified`,
  `first_step_strict_improves`). Глобальная достижимость
  (`drop ≥ δ` после многих шагов, non-convex) — по-прежнему не
  доказана; `a < 0` — гипотеза (chain rule к `⟨g, d⟩` не
  формализован).
- **Носители BlockDiag/NonlinearStep0** (Σ-тип, Fin N → V) и
  `CertifiedBlock` (ℕ → V → ℝ) различны: перенос ФОРМУЛЫ
  step0-эквивалентности = identity-инициализация здесь;
  дословная унификация носителей — вне этого бита (KISS).
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.FunctionPreservingGrowth

open scoped BigOperators
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

/-- Следствие (a): grown LM (`growLM` с identity-блоком) и
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
lip-добавка = 0 выведена честно из identity-инициализации).
После обучения добавка — per-block premise контракта. -/
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
(`kvCostOfBlock`/`lmKVCost_grow`) — любое. -/
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
случай, не лазейка (симметр `noBlockAdmissionWithoutMargin`). -/
theorem margin_positivity_refuses (kv ε : ℚ) (hε : 0 < ε) :
    blockAdmissionRule (strictGrowthChecks kv ε) = false := by
  refine decide_eq_false ?_
  simp only [strictGrowthChecks]
  norm_num
  linarith

/-! ## (d) Step-0 инстанс орто-fiber-кандидата -/

/-- **Мост (d)**: орто-fiber-инъекция (`orthoFiberAttn U A`)
при A = 0 — тождественна: резидуал `(A − U·(Uᵀ·A)) *ᵥ x` нулевой
(любой U). Так `mkOrthoFiberBlock U 0` — step-0 инстанс моста:
рост начинается функция-сохраняющим орто-блоком, дальнейший сигнал
идёт строго в ортогональном cortex направлении
(`fiber_injection_preserves_cortex`, C444/CortexFiber);
KV-стоимость роста — точный канал `lmKVCost_grow` . -/
theorem zero_init_orthoFiber_identity {D C : ℕ}
    (U : Matrix (Fin D) (Fin C) ℝ)
    (x : ℕ → Fin D → ℝ) (t : ℕ) :
    orthoFiberAttn U 0 x t = x t := by
  unfold orthoFiberAttn
  simp

/-! ## (e) Post warm-up сертификат роста (C642)

Разрыв C640: после шага 0 (`Wo ≠ 0`) функция НЕ сохранена —
сертификата «функция сохранена после обучения» нет. Что можно
сертифицировать честно: train-objective НИКОГДА не ухудшается
относительно старой модели, если warm-up стартует с identity и
каждый шаг либо certified (drop ≥ 0), либо отброшен rollback'ом.
Holdout-гейт кода (блок принимается iff holdout CE не хуже) —
другой функционал; ветка ACCEPT входит в теорему только как
гипотеза, не как доказанный факт. -/

section WarmUp

variable {B : Type}

/-- Warm-up: `n` шагов обучения параметров НОВОГО блока при
замороженном trunk. Носитель минимален: `obj b` — train-objective
модели `trunk ⊕ block(b)`; `θ : ℕ → B` — траектория warm-up
(`θ 0` — identity-старт); `drop t` — сертифицированный спад
шага `t`. **Телескоп warm-up**: каждый шаг даёт `obj (θ (t+1)) ≤ obj (θ t)
− drop t` ⇒ после `n` шагов `obj ≤ obj (θ 0) − Σ drop`. -/
theorem warmup_telescope (obj : B → ℝ) (θ : ℕ → B) (drop : ℕ → ℝ)
    (hstep : ∀ t, obj (θ (t + 1)) ≤ obj (θ t) - drop t) (n : ℕ) :
    obj (θ n) ≤ obj (θ 0) - ∑ t ∈ Finset.range n, drop t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hstep n
      linarith

/-- **`warmup_safe`**: (h0) identity-старт `obj (θ 0) = fOld`
(функция старой модели сохранена на шаге 0 —
`function_preserving_growth`), (h1) каждый шаг certified
(`drop t ≥ 0`) ⇒ train-objective после warm-up НЕ ХУЖЕ старой
модели: `obj (θ n) ≤ fOld`. Индукция по шагам (`warmup_telescope`). -/
theorem warmup_safe (obj : B → ℝ) (θ : ℕ → B) (drop : ℕ → ℝ)
    (fOld : ℝ)
    (h0 : obj (θ 0) = fOld)
    (hstep : ∀ t, obj (θ (t + 1)) ≤ obj (θ t) - drop t)
    (hdrop : ∀ t, 0 ≤ drop t) (n : ℕ) :
    obj (θ n) ≤ fOld := by
  have h := warmup_telescope obj θ drop hstep n
  have hs : 0 ≤ ∑ t ∈ Finset.range n, drop t :=
    Finset.sum_nonneg fun t _ => hdrop t
  rw [h0] at h
  linarith

/-- **Строгий вариант**: если КАЖДЫЙ шаг дал drop ≥ `dMin`, то
`obj (θ n) ≤ fOld − n·dMin` — рост не просто безопасен, а
монотонно улучшает train-objective с гарантированной скоростью. -/
theorem warmup_strict (obj : B → ℝ) (θ : ℕ → B) (drop : ℕ → ℝ)
    (fOld dMin : ℝ)
    (h0 : obj (θ 0) = fOld)
    (hstep : ∀ t, obj (θ (t + 1)) ≤ obj (θ t) - drop t)
    (hmin : ∀ t, dMin ≤ drop t) (n : ℕ) :
    obj (θ n) ≤ fOld - (n : ℝ) * dMin := by
  have h := warmup_telescope obj θ drop hstep n
  have hs : (n : ℝ) * dMin ≤ ∑ t ∈ Finset.range n, drop t := by
    calc (n : ℝ) * dMin = ∑ _t ∈ Finset.range n, dMin := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      _ ≤ _ := Finset.sum_le_sum fun t _ => hmin t
  rw [h0] at h
  linarith

/-- **Негатив (без h1)**: без certified-шагов заключение `warmup_safe`
ЛОЖНО — один шаг warm-up с `obj (θ 1) = 1 > 0 = obj (θ 0)`
(identity-старт, но шаг не сертифицирован: objective вырос). -/
theorem uncertified_step_can_worsen :
    ∃ (obj : ℝ → ℝ) (θ : ℕ → ℝ), θ 0 = 0 ∧ obj (θ 0) = 0
      ∧ 0 < obj (θ 1) := by
  refine ⟨id, fun t => if t = 0 then 0 else 1, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num

/-- **Композиция с rollback-гейтом кода** (gate _maybe_grow модели
hagi/unified.py: блок принят iff holdout CE не хуже, иначе точный
blocks.pop). Итоговое состояние = `guardedStep gate (θ n) (θ 0)`:
* ACCEPT — train-objective ≤ fOld (`warmup_safe`, h0/h1);
* REJECT — точный rollback к pre-step (`rollback_state_params`) ⇒
  train-objective = fOld точно.
⇒ при ЛЮБОМ вердикте гейта рост НИКОГДА не ухудшает train-objective.
Честно: holdout-неравенство код ИЗМЕРЯЕТ; ветка ACCEPT входит здесь
как посылка `haccept` (гипотеза гейта), а не как теорема. -/
theorem post_warmup_growth_safe (obj : B → ℝ) (θ : ℕ → B)
    (drop : ℕ → ℝ) (fOld : ℝ)
    (h0 : obj (θ 0) = fOld)
    (hstep : ∀ t, obj (θ (t + 1)) ≤ obj (θ t) - drop t)
    (hdrop : ∀ t, 0 ≤ drop t) (n : ℕ) (gate : Bool)
    (haccept : gate = true → obj (θ n) ≤ fOld) :
    obj ((Hagi.Theory.RollbackGate.guardedStep gate
      ⟨θ 0, (), 0⟩ ⟨θ n, (), 0⟩).params) ≤ fOld := by
  by_cases hg : gate = true
  · rw [hg]
    simp [Hagi.Theory.RollbackGate.guardedStep]
    exact haccept hg
  · rw [Hagi.Theory.RollbackGate.rollback_state_params gate _ _ (by simpa using hg), h0]

/-- Сертифицированная ветка ACCEPT: при h0/h1 посылка `haccept`
гейта ВЫПОЛНЕНА (`warmup_safe`) — т.е. если holdout-гейт кода
принял блок, train-objective ≤ fOld; если отверг — rollback
даёт равенство. Итог: при h0/h1 рост не ухудшает train-objective
независимо от решения гейта. -/
theorem post_warmup_growth_safe_of_certified (obj : B → ℝ)
    (θ : ℕ → B) (drop : ℕ → ℝ) (fOld : ℝ)
    (h0 : obj (θ 0) = fOld)
    (hstep : ∀ t, obj (θ (t + 1)) ≤ obj (θ t) - drop t)
    (hdrop : ∀ t, 0 ≤ drop t) (n : ℕ) (gate : Bool) :
    obj ((Hagi.Theory.RollbackGate.guardedStep gate
      ⟨θ 0, (), 0⟩ ⟨θ n, (), 0⟩).params) ≤ fOld :=
  post_warmup_growth_safe obj θ drop fOld h0 hstep hdrop n gate
    fun _ => warmup_safe obj θ drop fOld h0 hstep hdrop n

/-! ### Контракт certified-шага ⇒ h1 (C644)

h1 из `warmup_safe` («каждый шаг certified») — гипотеза, пока шаги
делает голый Adam (unified.py:423-431 @ca52eb4). Носитель шага,
который её ЗАКРЫВАЕТ: _certified_finite_step (hagi/lm.py:826
@ca52eb4). Контракт кода: направление −∇ (batch CE), eta из JVP,
до 13 проб с половением eta; COMMIT iff drop > 1e-12, где
drop = −upper, upper = finite_displacement_ce_upper (lm.py:235,
лемма о диапазоне: CE(z+d) − CE(z) ≤ ⟨softmax z − onehot, d⟩ +
range(d)²/8 — без предположения линейности); иначе точный rollback
к snapshot и HOLD (возврат 0.0). Форма ниже абстрактная: obj —
той же batch-CE, на которой выдан сертификат. -/

/-- Порог приёма шага (число кода lm.py:872 @ca52eb4). -/
def stepEps : ℝ := 1e-12

/-- **`CertifiedFiniteStep`** — контракт ОДНОГО вызова
_certified_finite_step: либо COMMIT — `drop` выше порога `stepEps`
и `obj θ' ≤ obj θ − drop` (сертификат конечного смещения логитов),
либо HOLD — параметры восстановлены точно (`θ' = θ`) и возвращён
`drop = 0`. Никакого третьего исхода код не имеет. -/
def CertifiedFiniteStep (obj : B → ℝ) (θ θ' : B) (drop : ℝ) : Prop :=
  (stepEps < drop ∧ obj θ' ≤ obj θ - drop) ∨ (θ' = θ ∧ drop = 0)

/-- **`warmup_h1_of_certified_steps`**: если КАЖДЫЙ шаг t траектории
произведён certified-шагом (`CertifiedFiniteStep`), то h1 из
`warmup_safe` ВЫПОЛНЕНА: `obj (θ (t+1)) ≤ obj (θ t) − drop t` и
`0 ≤ drop t`. COMMIT-ветка даёт оба неравенства (drop > stepEps > 0),
HOLD-ветка — равенство `obj (θ (t+1)) = obj (θ t)` при drop = 0. -/
theorem warmup_h1_of_certified_steps (obj : B → ℝ) (θ : ℕ → B)
    (drop : ℕ → ℝ)
    (hcert : ∀ t, CertifiedFiniteStep obj (θ t) (θ (t + 1)) (drop t)) :
    (∀ t, obj (θ (t + 1)) ≤ obj (θ t) - drop t) ∧ (∀ t, 0 ≤ drop t) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rcases hcert t with ⟨hpos, hle⟩ | ⟨heq, h0⟩
    · exact hle
    · rw [heq, h0]; linarith
  · rcases hcert t with ⟨hpos, _⟩ | ⟨_, h0⟩
    · have hE : (0:ℝ) < stepEps := by unfold stepEps; norm_num
      linarith
    · rw [h0]

/-- **`warmup_safe_of_certified_steps`** — композиция с C642: при
identity-старте (h0) certified-траектория даёт `obj (θ n) ≤ fOld`
(`warmup_safe` с hstep/hdrop из `warmup_h1_of_certified_steps`). -/
theorem warmup_safe_of_certified_steps (obj : B → ℝ) (θ : ℕ → B)
    (drop : ℕ → ℝ) (fOld : ℝ) (n : ℕ)
    (h0 : obj (θ 0) = fOld)
    (hcert : ∀ t, CertifiedFiniteStep obj (θ t) (θ (t + 1)) (drop t)) :
    obj (θ n) ≤ fOld := by
  obtain ⟨hstep, hdrop⟩ := warmup_h1_of_certified_steps obj θ drop hcert
  exact warmup_safe obj θ drop fOld h0 hstep hdrop n

/-- **`post_warmup_growth_safe_of_certified_steps`** — та же
композиция через rollback-гейт _maybe_grow: при любом вердикте гейта
train-objective ≤ fOld (`post_warmup_growth_safe_of_certified`). -/
theorem post_warmup_growth_safe_of_certified_steps (obj : B → ℝ)
    (θ : ℕ → B) (drop : ℕ → ℝ) (fOld : ℝ) (n : ℕ) (gate : Bool)
    (h0 : obj (θ 0) = fOld)
    (hcert : ∀ t, CertifiedFiniteStep obj (θ t) (θ (t + 1)) (drop t)) :
    obj ((Hagi.Theory.RollbackGate.guardedStep gate
      ⟨θ 0, (), 0⟩ ⟨θ n, (), 0⟩).params) ≤ fOld := by
  obtain ⟨hstep, hdrop⟩ := warmup_h1_of_certified_steps obj θ drop hcert
  exact post_warmup_growth_safe_of_certified obj θ drop fOld h0 hstep hdrop n gate

/-- **Негатив (без сертификата)**: шаг из негатива C642
(identity-старт, `obj (θ 1) = 1 > 0`) НЕ удовлетворяет контракту
`CertifiedFiniteStep` ни при каком drop — т.е. контракт отсекает
шаг, портящий objective, а не просто его игнорирует. -/
theorem uncertified_step_not_certified (drop : ℝ) :
    ¬ CertifiedFiniteStep id 0 1 drop := by
  rintro (⟨hpos, hle⟩ | ⟨heq, _⟩)
  · have : (0:ℝ) < stepEps := by unfold stepEps; norm_num
    simp only [id_eq] at hle
    linarith
  · exact absurd heq (by norm_num)

/-- **Негатив (per-batch)**: сертификат шага — на batch-CE СВОЕГО
минибатча (WAVE 239, lm.py:1002-1005: «per-batch bounds do NOT
 telescope»). Для ДРУГОГО функционала тот же шаг даёт рост:obj_b
упал на 1/2, а obj вырос на 1. Значит `hcert` с ОДНИМ obj —
реальное ограничение: телескоп C642 законен только если все шаги
сертифицированы на одном и том же функционале. -/
theorem batch_drop_not_global :
    ∃ (objB obj : ℝ → ℝ) (θ θ' : ℝ) (d : ℝ),
      0 < d ∧ objB θ' ≤ objB θ - d ∧ obj θ < obj θ' := by
  refine ⟨fun x => -x, id, 0, 1, 1 / 2, by norm_num, ?_, ?_⟩
  · norm_num
  · simp only [id_eq]; norm_num

/-! ### Certified-шаг на параметрах БЛОКА (C646)

`_certified_finite_step` пишет только в trunk. Вопрос-гейт C645:
зависит ли range-лемма CE (`finite_displacement_ce_upper`, lm.py:235)
от носителя параметров? НЕТ: лемма — о ЛОГИТАХ, `d` — смещение
логитов. В каноне это `Hagi.Energy.lse_shift_upper` на абстрактных
`x y : V → ℝ` (носитель θ не входит). Ниже — развёртка на абстрактный
носитель `B`: `L : B → V → ℝ` — «логиты(параметры)», в частности
`L b = lmLogits (m с блоком b) x t` при замороженном trunk
(`lmLogits_grow_identity` — точка старта: у identity-блока L = старые
логиты). Код-side: Δz = block-only JVP — реализация, не теорема. -/

variable {K : Type} [Fintype K] [Nonempty K] {B : Type}

/-- **`certified_step_block_of_range`**: для ЛЮБОГО отображения
`L : B → K → ℝ` (логиты как функция параметров — блока, trunk'а,
всей модели) и смещения логитов `d = L b' − L b`:
CE_t(L b') − CE_t(L b) ≤ ⟨softmax (L b) − onehot_t, d⟩ + range(d)²/8.
Носитель параметров не входит — это `lse_shift_upper` при
`x = L b`, `y = L b'`. -/
theorem certified_step_block_of_range (L : B → K → ℝ) (b b' : B) (t : K)
    (r : ℝ) (hr : ∀ u v, (L b' u - L b u) - (L b' v - L b v) ≤ r) :
    Hagi.ceOneHot t (L b') ≤ Hagi.ceOneHot t (L b)
      + (∑ v, Hagi.Energy.smax (L b) v * (L b' v - L b v) - (L b' t - L b t))
      + r ^ 2 / 8 := by
  have h := Hagi.Energy.lse_shift_upper (V := K) (L b) (L b') r hr
  unfold Hagi.ceOneHot Hagi.lse
  linarith

/-- **`block_step_certified_of_range_bound`** — COMMIT-ветка контракта
`CertifiedFiniteStep` для objective на параметрах блока `obj_b b =
CE_t (L b)`: если range смещения логитов ≤ r, то
`obj_b b' ≤ obj_b b − drop`, где `drop = −(⟨softmax z − onehot, d⟩ + r²/8)`;
при `drop > stepEps` пара `(b', drop)` проходит контракт. Т.е.
`warmup_h1_of_certified_steps` применим к блоку наравне с trunk —
сертификат требует только range(Δz), а не носителя θ. -/
theorem block_step_certified_of_range_bound (L : B → K → ℝ) (b b' : B)
    (t : K) (r : ℝ)
    (hr : ∀ u v, (L b' u - L b u) - (L b' v - L b v) ≤ r) (drop : ℝ)
    (hdrop : ∑ v, Hagi.Energy.smax (L b) v * (L b' v - L b v) - (L b' t - L b t)
        + r ^ 2 / 8 = -drop) :
    Hagi.ceOneHot t (L b') ≤ Hagi.ceOneHot t (L b) - drop := by
  have h := certified_step_block_of_range L b b' t r hr
  calc Hagi.ceOneHot t (L b') ≤ Hagi.ceOneHot t (L b)
        + (∑ v, Hagi.Energy.smax (L b) v * (L b' v - L b v) - (L b' t - L b t))
        + r ^ 2 / 8 := h
    _ = Hagi.ceOneHot t (L b) - drop := by linarith [hdrop.le]

/-- COMMIT-ветка: когда upper < −stepEps (т.е. drop > stepEps), шаг по
блоку удовлетворяет `CertifiedFiniteStep` на `obj_b = CE_t ∘ L`. -/
theorem block_step_commit_of_range_bound (L : B → K → ℝ) (b b' : B) (t : K)
    (r : ℝ) (hr : ∀ u v, (L b' u - L b u) - (L b' v - L b v) ≤ r)
    (hpos : stepEps < -(∑ v, Hagi.Energy.smax (L b) v * (L b' v - L b v)
        - (L b' t - L b t) + r ^ 2 / 8)) :
    CertifiedFiniteStep (fun c => Hagi.ceOneHot t (L c)) b b'
      (-(∑ v, Hagi.Energy.smax (L b) v * (L b' v - L b v)
        - (L b' t - L b t) + r ^ 2 / 8)) := by
  refine Or.inl ⟨hpos, ?_⟩
  exact block_step_certified_of_range_bound L b b' t r hr _ (by ring)

/-- **Негатив (граница range нарушена)**: аналог `batch_drop_not_global` —
сертификат по bound'у `r = 1/2` недоступен, если посылка о range ложна:
шаг с range(Δz) = 1 > 1/2 РАСТЁТ по objective (log 2 → log (1 + e)),
и потому контракт `CertifiedFiniteStep` не выполнен ни при каком drop. -/

theorem block_range_bound_violated_not_certified :
    ∃ (L : Bool → Bool → ℝ),
      (¬ ∀ u v, (L true u - L false u) - (L true v - L false v) ≤ 1 / 2)
        ∧ ∀ drop, ¬ CertifiedFiniteStep
          (fun c => Hagi.ceOneHot false (L c)) false true drop := by
  have hexp : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hlog : Real.log 2 < Real.log (1 + Real.exp 1) :=
    Real.log_lt_log (by positivity) (by ring_nf at hexp ⊢; linarith [hexp])
  refine ⟨fun c v => if c && v then 1 else 0, ?_, ?_⟩
  · intro h
    have := h true false
    norm_num at this
  · intro drop
    rintro (⟨hpos, hle⟩ | ⟨heq, _⟩)
    · simp only [Hagi.ceOneHot, Hagi.lse] at hle
      norm_num [Finset.sum_ite_eq, Finset.filter_eq] at hle
      unfold stepEps at hpos
      norm_num at hpos
      have hpos' : (0 : ℝ) < drop := by linarith
      rw [add_comm] at hlog
      have h2 : Real.log 2 - drop < Real.log 2 := sub_lt_self _ hpos'
      exact absurd hle (not_le.mpr (lt_trans h2 hlog))
    · exact absurd heq (by norm_num)

/-! ### Полезность первого warm-up шага (C657)

Вопрос C656: доказано лишь `obj ≤ fOld` («не хуже»). Когда блок
гарантированно даёт drop? Носитель: семейство шагов `bη η` с
ЛИНЕЙНЫМ по η смещением логитов `L (bη η) − L b = η • D` (код:
шаг с фиксированным направлением, lm.py:581 `h = h +
relu(a@W1+b1)@Wo`, Wo = 0 — JVP по Wo линеен). Тогда посылка
range-леммы выполняется с `r = η·R`, `R` — range-константа
направления `D`, а линейная часть равна `η·a`,
`a = ⟨softmax z − onehot, D⟩`. Сертификат:
`linDrop a R η = −(η·a + η²·R²/8)` — вогнутая парабола по η.
Связь `a` с `⟨g, d⟩` C655 (`a = ⟨Jᵀ(p−y), d⟩` по chain rule) НЕ
формализована: `L` нелинейна по параметрам, `a < 0` входит как
гипотеза «descent в логитах». -/

/-- Сертифицированный drop линейного по η семейства шагов:
`−(η·a + η²·R²/8)`, где `a` — линейная часть range-леммы,
`R` — range-константа направления. -/
noncomputable def linDrop (a R η : ℝ) : ℝ := -(η * a + η ^ 2 * R ^ 2 / 8)

/-- **`useful_first_step` (U1)**: парабола `linDrop` в точке
`η* = 4|a|/R² = −4a/R² (a < 0)` равна `2a²/R²` — точное значение
максимума (`useful_eta_le`); тождество верно при любом `a`. -/
theorem useful_first_step {a R : ℝ} (hR : R ≠ 0) :
    linDrop a R (-4 * a / R ^ 2) = 2 * a ^ 2 / R ^ 2 := by
  unfold linDrop; field_simp; ring

/-- Максимум строго положителен: `drop_max = 2a²/R² > 0` при
`a < 0` (ненулевой residual-сигнал) и `0 < R`. -/
theorem useful_first_step_pos {a R : ℝ} (ha : a < 0) (hR : 0 < R) :
    0 < linDrop a R (-4 * a / R ^ 2) := by
  rw [useful_first_step (Ne.symm hR.ne)]
  exact div_pos (by nlinarith) (sq_pos_of_pos hR)

/-- **`useful_eta_le`**: `drop_max = 2a²/R²` — глобальная верхняя
граница `drop η`; равенство возможно только при `η = η*`. -/
theorem useful_eta_le {a R η : ℝ} (hR : R ≠ 0) :
    linDrop a R η ≤ 2 * a ^ 2 / R ^ 2
      ∧ (linDrop a R η = 2 * a ^ 2 / R ^ 2 → η = -4 * a / R ^ 2) := by
  have hid : (R ^ 2 * η + 4 * a) ^ 2 / (8 * R ^ 2)
      = 2 * a ^ 2 / R ^ 2 - linDrop a R η := by
    unfold linDrop; field_simp; ring
  have hn : (0 : ℝ) < 8 * R ^ 2 := by positivity
  have hnn : (0 : ℝ) ≤ (R ^ 2 * η + 4 * a) ^ 2 / (8 * R ^ 2) :=
    div_nonneg (sq_nonneg _) hn.le
  refine ⟨by linarith, fun heq => ?_⟩
  have hz : (R ^ 2 * η + 4 * a) ^ 2 / (8 * R ^ 2) = 0 := by
    rw [← heq] at hid; linarith
  have hs : R ^ 2 * η + 4 * a = 0 := by
    rcases div_eq_zero_iff.mp hz with h | h
    · exact sq_eq_zero_iff.mp h
    · exact absurd h (by positivity)
  have hR2 : (R ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- **`exists_useful_eta`**: если `drop_max = 2a²/R²` превышает порог
приёма `stepEps` (эквивалент `|a| > √(stepEps·R²/2)`), существует
`η > 0` с `stepEps < drop η` — certified COMMIT. -/
theorem exists_useful_eta {a R : ℝ} (ha : a < 0) (hR : 0 < R)
    (hmax : stepEps < 2 * a ^ 2 / R ^ 2) :
    ∃ η : ℝ, 0 < η ∧ stepEps < linDrop a R η :=
  ⟨-4 * a / R ^ 2, div_pos (by linarith) (sq_pos_of_pos hR), by
    rw [useful_first_step (Ne.symm hR.ne)]; exact hmax⟩

/-- **Негатив (нет сигнала)**: при `a = 0` линейная часть исчезает,
`drop η = −η²·R²/8 ≤ 0` при любом η — COMMIT невозможен ни при
каком шаге: полезность требует ненулевого residual-сигнала. -/
theorem no_signal_no_drop (R η : ℝ) : linDrop 0 R η ≤ 0 := by
  unfold linDrop
  have : 0 ≤ η ^ 2 * R ^ 2 / 8 := by positivity
  linarith

/-- **`first_step_useful_certified` (U1 на носителе блока)**: для
семейства шагов `bη` с линейным смещением логитов
`L (bη η) u − L b u = η·D u` и range-константой `R`
(`D u − D v ≤ R`), при `a = ⟨softmax (L b) − onehot_t, D⟩ < 0`,
`0 < R` и `stepEps < 2a²/R²` существует `η > 0`, для которого шаг
`b → bη η` удовлетворяет контракту `CertifiedFiniteStep` на
`CE_t ∘ L` (через `block_step_commit_of_range_bound`). -/
theorem first_step_useful_certified {K : Type} [Fintype K] [Nonempty K]
    (L : B → K → ℝ) (b : B) (bη : ℝ → B) (D : K → ℝ) (t : K) (a R : ℝ)
    (hlin : ∀ η u, L (bη η) u - L b u = η * D u)
    (hR : 0 < R) (hrange : ∀ u v, D u - D v ≤ R)
    (ha : a = ∑ v, Hagi.Energy.smax (L b) v * D v - D t)
    (hdesc : a < 0) (hmax : stepEps < 2 * a ^ 2 / R ^ 2) :
    ∃ η : ℝ, 0 < η ∧ stepEps < linDrop a R η ∧
      CertifiedFiniteStep (fun c => Hagi.ceOneHot t (L c)) b (bη η)
        (linDrop a R η) := by
  obtain ⟨η, hη, hdrop⟩ := exists_useful_eta hdesc hR hmax
  have h1 : ∑ v, (Hagi.Energy.smax (L b) v * (L (bη η) v - L b v))
      = η * ∑ v, Hagi.Energy.smax (L b) v * D v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => by rw [hlin]; ring)
  have hlin' : ∑ v, Hagi.Energy.smax (L b) v * (L (bη η) v - L b v)
      - (L (bη η) t - L b t) = η * a := by
    rw [h1, hlin, ha]; ring
  have hval : linDrop a R η
      = -(∑ v, Hagi.Energy.smax (L b) v * (L (bη η) v - L b v)
          - (L (bη η) t - L b t) + (η * R) ^ 2 / 8) := by
    unfold linDrop
    rw [hlin', mul_pow]
  refine ⟨η, hη, hdrop, hval ▸ ?_⟩
  refine block_step_commit_of_range_bound L b (bη η) t (η * R) ?_ ?_
  · intro u v
    rw [hlin η u, hlin η v]
    have hmul := mul_le_mul_of_nonneg_left (hrange u v) hη.le
    nlinarith
  · rw [hlin', mul_pow]
    unfold linDrop at hdrop
    linarith

/-- **`first_step_strict_improves`**: тот же единственный полезный
первый шаг от identity-старта (`CE_t (L b) = fOld`) даёт
`CE_t (L (bη η)) < fOld` — строгое улучшение, а не «не хуже». -/
theorem first_step_strict_improves {K : Type} [Fintype K] [Nonempty K]
    (L : B → K → ℝ) (b : B) (bη : ℝ → B) (D : K → ℝ) (t : K) (a R fOld : ℝ)
    (hlin : ∀ η u, L (bη η) u - L b u = η * D u)
    (hR : 0 < R) (hrange : ∀ u v, D u - D v ≤ R)
    (ha : a = ∑ v, Hagi.Energy.smax (L b) v * D v - D t)
    (hdesc : a < 0) (hmax : stepEps < 2 * a ^ 2 / R ^ 2)
    (h0 : Hagi.ceOneHot t (L b) = fOld) :
    ∃ η : ℝ, 0 < η ∧ Hagi.ceOneHot t (L (bη η)) < fOld := by
  obtain ⟨η, hη, hdrop, hcert⟩ :=
    first_step_useful_certified L b bη D t a R hlin hR hrange ha hdesc hmax
  have hE : (0 : ℝ) < stepEps := by unfold stepEps; norm_num
  rcases hcert with ⟨-, hle⟩ | ⟨_, hz⟩
  · have hle' : Hagi.ceOneHot t (L (bη η)) ≤ Hagi.ceOneHot t (L b) - linDrop a R η := hle
    have hpos : 0 < linDrop a R η := lt_trans hE hdrop
    rw [h0] at hle'
    exact ⟨η, hη, lt_of_le_of_lt hle' (sub_lt_self fOld hpos)⟩
  · rw [hz] at hdrop; exact absurd hdrop (by unfold stepEps; norm_num)

end WarmUp


end Hagi.Theory.FunctionPreservingGrowth
