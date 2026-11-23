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
- **Существование полезного блока** не доказывается: мост —
  gate-совместимость нейтрального расширения, не теорема
  существования (тот же pin, что у BlockAdmission).
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

end WarmUp

end Hagi.Theory.FunctionPreservingGrowth
