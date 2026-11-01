# HAGI: карта доказанного (honest map)

> SSOT-документ: что ИМЕННО доказано в Lean, что условно,
> что НЕ доказано. Обновляется каждый такт.

## 1. Доказанное ядро (end-to-end, без внешних посылок)

### 1.1. CertifiedLoop — капстон (Unified/CertifiedLoop.lean)

ГЛАВНАЯ ТЕОРЕМА (`certified_loop`): цепочка шагов, каждый
из которых несёт зависимый сертификат (StepCert), даёт на
горизонте n одновременно:

1. **реальный спуск**: Σ drops ≤ obj(f 0) − obj(f n)
   (спуск выведен из исполнения, а не из показателя);
2. **качество**: покомпонентный floor FloorKept(f n);
3. **бюджет**: 0 ≤ b n и b n ≤ b 0 − Σ spends.

`gate_never_increases`: commit/hold-принцип — без
сертификата состояние сохраняется; энергия не растёт
никогда. Это доказанный безопасный anytime-цикл.

Компоненты капстона (все закрытые дефекты внешнего аудита):
- `HonestTransition` (P0-2): actualDescent — зависимое
  доказательство obj s' ≤ obj s − drop (контрпример
  «положительный сертификат при росте» невозможен по
  построению);
- `CanonicalParams` (P0-3): params — единственный носитель;
  weights = toW(params) через инъективный LawfulProj;
  активный шаг строго меняет и то, и другое;
- `LinkedQVec` (P0-4): качество — функция состояния
  (evaluate : S → Fin 5 → ℝ); контрпример: скалярный Qgen
  скрывает обрушение компоненты — покомпонентный floor
  ловит;
- `ExecutedCert` (4.4): измерение связано с исполнением
  внутри типа (link), кумулятивная честная бухгалтерия.

### 1.2. Вычислимый конвейер (замкнут, 0 sorry/axiom)

`FunctionalState` → `funStep` (jointStep + квантование) →
`funGate` (commit/hold по machineCert) → `funTrajectory`:
- fs_energy_after, fs_two_steps_productive;
- fsGate_mono, funTrajectory_mono (энергия не возрастает);
- funTrajectory_budget_le, funTrajectory_stepCount_le.

`ReferenceMachine` (квадратичный эталон): точное
равенство E(w') = (1−η)²E(w), Δ/2-квантование,
quad_gate_commit (строгое убывание при превосходстве
выигрыша над ошибкой округления).

Историческая обструкция старой GrowthState-семантики
(corePremises_two_step_decrease_nonpos) снята сменой
архитектуры (метрики-функции), теорема сохранена.

## 2. Математическое ядро (самостоятельные теоремы)

- Вероятность: Hoeffding, Azuma, Freedman (1- и 2-сторон.),
  Гиббс, Пинскер, Бретаньоль–Юбер, Fannes;
- Оптимизация: спуск по L-гладким, Momentum/AdamW/Lion/
  Muon-инварианты, MirrorDescent, SafeQP (детерм. и
  стохастич.), GradNorm-балансировка, Grokfast-мост;
- Квантование: Δ/2-граница, энергия-лифт, Landauer;
- Информация: MDL, Jensen-gap для слияния, MemoryCycle
  (novelty ∧ gain), дистилляция;
- 51 ML-примитив (BYOL, Mamba, MoE, RoPE, ...) —
  корректные определения и локальные теоремы, ждут
  интеграции в LossBundle/Optimizer-интерфейсы.

## 3. Условные результаты (НЕ end-to-end)

- MasterHAGI/Trunc, GrandSynthesis: рост capability из
  ВНЕШНИХ посылок (CorePremises как поля). Выводы
  корректны, посылки не выведены из алгоритма —
  планируемая миграция: переформулировка как следствие
  CertifiedLoop + GrowthDynamics;
- GrowthDynamics (C_{t+1} ≥ (1+α)^T): верно ПРИ
  динамических законах как посылках;
- WallClockTakeoff, ChainToCone, PerronCone: условная
  теория роста (cone-invariance из законов).

## 4. ЧТО НЕ ДОКАЗАНО (честно)

1. **Глобальная оптимальность** архитектуры/алгоритма в
   общем классе: доказан безопасный сертифицированный
   цикл (каждый commit строго улучшает), а не то, что он
   глобально оптимален среди всех алгоритмов. Оптимальность
   осмысленна только относительно класса потерь/ограничений
   (см. ReferenceMachine — там оптимальность шага точна).
2. Произвольные нейросети: спуск доказан для квадратичной
   reference-модели и L-гладкого абстрактного класса.
3. Экспоненциальный рост capability БЕЗ динамических
   посылок.
4. Связь μP/ширины и реального качества (в карантине:
   OrthoCols — тройной обмен сумм).

## 5. Воспроизводимость

CI: lake build → Freeze → AssumptionScan → TrivialLint →
DupLint → NsLint → LayerLint → DocLint → StatusLint →
ChallengeCheck → StatementDupCheck → MachineDiffTest →
AllAxiomCheck → ClosureReport → Metrics. Все PASS.
Аксиомы только стандартные (propext, Classical.choice,
Quot.sound). Известный P1-дефект: абсолютные пути в
lean-toolchain/lakefile (локальная машина).

## 6. Иерархия зависимостей (верх → низ)

CertifiedLoop
├── HonestTransition (P0-2)
├── LinkedQVec (P0-4)
├── CanonicalParams (P0-3)
└── [ExecutedCert — параллельный сертификат измерений]
FunctionalState-конвейер (вычислимый instance всех
абстрактных контрактов)
