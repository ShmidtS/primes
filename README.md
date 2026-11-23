# HAGI_v2

Формализация на Lean 4.36.0 / Mathlib математической основы
HAGI_v2 — предполагаемой архитектуры тернарной RD-канальной
причинной языковой модели, развиваемой из небольших доменных
экспертов.

Проект исследует, как объединение специализированных компонентов,
совместное обучение, сжатие и последующий рост могут описываться
как связанная система состояний, переходов и ресурсных ограничений.
Его исследовательская цель — улучшение качества обучения при
ограниченном бюджете модели, памяти и вычислений. Репозиторий
представляет формальную основу этой цели, а не сообщение о её
достижении для реальной системы.

## Общая идея

Центральный объект проекта — не один изолированный алгоритм, а
контур адаптивного обучения. В нём состояние модели связывается с
энергией или целевым функционалом, измеренными эффектами, оценками
качества, памятью, стоимостью перехода и правилами accept/hold.
Отдельные математические компоненты отвечают за подготовку данных,
выбор батча, шаг оптимизации, объединение экспертов, квантование,
консолидацию памяти и анализ траекторий.

Такой контур позволяет формулировать точные вопросы: что сохраняется
при переходе, какие ресурсы расходуются и какие свойства доказаны
на заданном носителе. Архитектурная схема здесь является объектом
математического исследования, а не описанием уже обученной
полноразмерной сети.
## Три уровня результата

1. **Математическая база.** Конечные алгебраические, вероятностные,
   информационные и энергетические утверждения, доказываемые без
   экспериментальных предпосылок.
2. **Условные сертификаты.** Свойства шага или конечной траектории,
   получаемые из явно перечисленных входных условий. Если свойство
   реального обучения задано как посылка, теорема использует его, но
   не доказывает его выполнение автоматически.
3. **Мосты между ними.** Связи отдельных условий с конкретными
   моделями и доказанными механизмами. Такие мосты имеют собственную
   область применимости и не устраняют посылки произвольной модели.
`Hagi.Unified.CertifiedLoop.certified_loop` задаёт верхнеуровневую
теорему о конечной цепочке сертифицированных переходов с общей целью,
ограничениями качества и учётом бюджета при её посылках.

Ещё один частный мост связывает конечную log-linear one-hot CE,
residual-направление и явно измеренные old/new CE с одношаговой оценкой
joint potential. Обе CE-идентификации остаются предпосылками; нулевое
направление допускается. Это не утверждение о глобальной гладкости,
универсальном строгом спуске, сходимости, обобщении или времени работы.
Условия и точная формула приведены в [разделе 3.4](ALGORITHMS.md#34-конечная-log-linear-ce-и-joint-potential),
а главный результат — в [карточке DerivAlong](STATUS.md#hagiunifiedderivalonglean).

Формализация сама по себе не доказывает достижение AGI, оптимальность
архитектуры, качество обучения или преимущество по времени и объёму
вычислений. Утверждения о held-out данных и обобщении относятся к
отдельным моделям и не следуют автоматически из сертификата одного шага.

## Математический охват

- Базовый аппарат на конечных носителях: линейная алгебра,
  спектральные конструкции, факторизация, информация и вероятность.
- Объединение и согласование экспертов, дистилляция, рекуррентные
  преобразования и геометрия архитектурных состояний.
- Тернарное квантование, энергетические оценки, нормировка и бюджеты
  памяти, ёмкости и вычислений.
- Концентрация, конечновыборочные оценки, выбор батча и свойства
  явно заданных функций потерь.
- Шаги обучения, контроллеры и их гейты, телеметрия, состояния и
  траектории, включая рост и изменение ресурсов.
- Условные связи между отдельными компонентами и интегрированными
  сертификатами состояния или конечного контура.

Точные формулировки, носители и предпосылки находятся в исходниках;
README не заменяет их математическую спецификацию.

## Структура репозитория

`Hagi.lean` — корневой модуль библиотеки и общая точка импорта.
Дерево `Hagi/` сгруппировано по математическим и системным доменам:

| Домен | Каталоги | Содержание на верхнем уровне |
| --- | --- | --- |
| База | [`Hagi/Prelude`](Hagi/Prelude), [`Hagi/Core`](Hagi/Core), [`Hagi/Numerics`](Hagi/Numerics), [`Hagi/Geometry`](Hagi/Geometry), [`Hagi/Spectral`](Hagi/Spectral), [`Hagi/StatMech`](Hagi/StatMech) | Общие определения, конечные носители, алгебраические и геометрические результаты. |
| Архитектура | [`Hagi/Architecture`](Hagi/Architecture), [`Hagi/Ensemble`](Hagi/Ensemble), [`Hagi/Sparsity`](Hagi/Sparsity) | Композиция компонентов, объединение экспертов и структурные ограничения. |
| Энергия и ресурсы | [`Hagi/Energy`](Hagi/Energy), [`Hagi/Budget`](Hagi/Budget), [`Hagi/Runtime`](Hagi/Runtime) | Квантование, энергия, ресурсный учёт и точные представления исполнения. |
| Данные и обучение | [`Hagi/Data`](Hagi/Data), [`Hagi/Information`](Hagi/Information), [`Hagi/Probability`](Hagi/Probability), [`Hagi/Learning`](Hagi/Learning), [`Hagi/Optimization`](Hagi/Optimization), [`Hagi/Model`](Hagi/Model), [`Hagi/Generalization`](Hagi/Generalization) | Модели данных, выборки и потерь, оценки, оптимизация и отдельные вопросы обобщения. |
| Переходы обучения | [`Hagi/Step`](Hagi/Step), [`Hagi/Pretraining`](Hagi/Pretraining), [`Hagi/Planning`](Hagi/Planning), [`Hagi/Contracts`](Hagi/Contracts) | Шаги, контроллеры, контракты переходов и конечные траектории. |
| Рост и динамика | [`Hagi/Growth`](Hagi/Growth), [`Hagi/Dynamics`](Hagi/Dynamics), [`Hagi/State`](Hagi/State) | Состояния роста, устойчивость, бюджеты и динамические законы. |
| Теория и канон-модули | [`Hagi/Theory`](Hagi/Theory) | 47 файлов: 10 канон-модулей v5 (Continual, Statistics, SelfEdit, Compression, MergeQuant, Softmax, SafeStep, MasterTheorem, FullPipeline, BlockLipschitz) плюс канон машины v3 `MasterTheoremV3` (C576), канон механики роста адаптеров `AdapterGrowth` (4 промаркированные секции, v6-V3), growth-семья (`AdapterBank`, `GrowSnap`, `GrowTrunkBlock`, `FunctionPreservingGrowth`), source-anchored мосты HAGI_v2 волн C530+ (`RollbackGate`, `WeightDecayLeak`, `OEComplete`, `ExactBypass`, `FactLedger`, `RangeWrap`, `AdaptiveContext`, `NegativeTransfer`, `AutoTransferGate`, `TritCodec`, `MiniHagiLoop`, `KnowledgeConsolidation` и др. — канон описаний в [ALGORITHMS §27a](ALGORITHMS.md#27a-мосты-hagi_v2-и-bench-режимы-канон-c588-v6-v4)) и bench-мосты (`MiniHagi`, `MiniHagi2`, `TrainerBenchmark`, `CertCEHoldout`, `CertSandwichBench`). |
| Интеграция | [`Hagi/System`](Hagi/System), [`Hagi/Unified`](Hagi/Unified) | Связанные состояния, измеренные эффекты, мосты и условные сертификаты. |
| Дополнительные направления | [`Hagi/Autonomy`](Hagi/Autonomy) | Маршрутизация и смежные автономные модели. |
| Примеры и сопровождение | [`Hagi/Challenge`](Hagi/Challenge), [`Hagi/Audit`](Hagi/Audit), [`Hagi/External`](Hagi/External) | Сравнительные формулировки, аудит и внешние математические связи. |
| Карантин и сертификаты | [`Hagi/Cert`](Hagi/Cert), [`Hagi/Benchmarks`](Hagi/Benchmarks), [`Hagi/Research`](Hagi/Research) | Ядро сертификации (`Hagi/Cert`), а также модули вне корневого замыкания `Hagi.lean`: демонстрационные свидетели (`Benchmarks`), исследовательские модели Omni/Percolation/Schelling/Discovery (`Research`) и архив исторических результатов Legacy (`Hagi/Research/Legacy`, C456; сборка целью `Hagi.Research`). |

Каталог `scripts/` содержит вспомогательные средства сопровождения
формализации. Математическим источником остаются файлы `Hagi/**/*.lean`.

## Канон-карта (после рефакторингов v5 W1–W8 и v6 V1–V5)

Инвариант структуры — import-DAG слоёв `scripts/LayerLint.py`
(лимита размера файла нет): модуль может импортировать только
строго нижние слои; известные исключения — сокращающийся
allowlist LAYER_EXCEPTIONS.

| Слой | Каталоги |
| --- | --- |
| 0 | `Hagi/Math`, `Hagi/Foundations`, `Hagi/Audit` |
| 1 | `Hagi/Prelude`, `Hagi/Information`, `Hagi/Core`, `Hagi/Spectral`, `Hagi/Sparsity`, `Hagi/Geometry`, `Hagi/Planning` |
| 2 | `Hagi/Cert`, `Hagi/Architecture`, `Hagi/Data`, `Hagi/Energy`, `Hagi/Probability`, `Hagi/External` |
| 3 | `Hagi/Ensemble`, `Hagi/Step`, `Hagi/Optimization`, `Hagi/Runtime`, `Hagi/System`, `Hagi/State` |
| 4 | `Hagi/Model`, `Hagi/Numerics`, `Hagi/Growth`, `Hagi/Generalization`, `Hagi/Budget` |
| 5 | `Hagi/Dynamics`, `Hagi/Deployment`, `Hagi/Pretraining`, `Hagi/Semantics`, `Hagi/Autonomy` |
| 6 | `Hagi/Unified` |
| 7 | `Hagi/Contracts`, `Hagi/Challenge`, `Hagi/Theory` |
| 8 | `Hagi/Training` |

Канон-файлы (одно понятие — один носитель; слияния v5 W1–W4):

| Семья | Канон-носитель | Что поглощено / статус |
| --- | --- | --- |
| Theory | `Hagi/Theory/{Continual, Statistics, SelfEdit, Compression, MergeQuant, Softmax, SafeStep, MasterTheorem, FullPipeline, BlockLipschitz}.lean` — 10 канонов | одно понятие описано один раз; ns слиты стабильно (C511+) |
| Model CE-спуск | `Hagi/Model/BatchCEDescent.lean` | поглощены Common/Arithmetic/Direction/SafeStep (W1); HalfEta/LogitRange/ResidualNorm/Stochastic/Fixtures — отдельные файлы |
| Model CE-шкалы | `Hagi/Model/CEGroupedScale.lean`, `CEJointScale.lean` | CEGroupedScaleBasic поглощён (W1); CEScaleChoice/CEScaleSelection слиты; CEJointScale остался отдельным каноном шкал |
| Contracts growth | `Hagi/Contracts/BatchCEGrowth.lean` | BatchCEGrowthSelection поглощён (W2) |
| Contracts EM | `Hagi/Contracts/EMTrajectory.lean` | поглощены MixtureEMTrajectory/FactorizedMixtureEM/FiniteEMTrajectory/ChangingEMTrajectory (W2); носитель `Probability/FiniteMultiEM` не тронут |
| Contracts step | `Hagi/Contracts/BatchCEStepCore.lean`, `BatchCEBestResidual.lean` | план W2 предлагал слияние — не доведено (deriv-риск), оба живые каноны |
| Theory мосты HAGI_v2 | [`ALGORITHMS.md` §27a](ALGORITHMS.md#27a-мосты-hagi_v2-и-bench-режимы-канон-c588-v6-v4) | канон описаний мостов волн C530+ (18 мостов + bench-паттерн, C588): одно описание одного моста — ровно один раз; Lean-носители — отдельные файлы `Hagi/Theory/*.lean` |
| Theory v3-машина | `Hagi/Theory/MasterTheoremV3.lean` | 5 гарантий машины v3 одним statement (C576) |
| Theory рост адаптеров | `Hagi/Theory/AdapterGrowth.lean` | механика роста адаптеров C532–C560; 4 секции промаркированы канон-заголовками (v6-V3), нарезка на файлы не делалась |
| Probability EB-радиус | `Hagi/Probability/EmpiricalBernstein.lean` | EB-радиус: σ̂-подстановка + аддитивный член поверх Freedman (C539) |
| Probability Freedman | `Hagi/Probability/Freedman.lean` | поглощены Step/TwoSided/Adaptive/FamilyConfidence (W3) |
| Probability MWU | `Hagi/Probability/MirrorHedgeMWU.lean`, `MirrorHedgeGibbs.lean` | семья MWU в двух файлах; `Optimization/MirrorHedge` — независимый потребитель (слой 3) |
| Probability logscore | `Hagi/Probability/FiniteLogScore.lean` | FiniteJointLogScore поглощён (W3) |
| Unified loop | `Hagi/Unified/CertifiedLoop.lean` | CertifiedLoopKernel поглощён (W4) |
| Numerics | `Hagi/Numerics/Numerics.lean` | SoftmaxFix/QuantSafeUpdate поглощены (W4) |
| Pretraining dust | `Hagi/Pretraining/Dust.lean` | DustAlign/DustMeasure поглощены (W4) |
| Scripts | `scripts/_shared.py` | общие helpers 5 линтеров + Freeze (W5); `bench_bridge.py` — монолит (см. границы) |
| Docs | `STATUS.md` (сжат в W6), nodoc 0 | канон-заголовки всех модулей (W6) |

Словарь перегруженных имён (одно имя в разных пространствах имён;
канон-определение — первое): `CertStep` → `Hagi.Cert` (`Hagi/Cert/Core.lean`; вариант `Hagi.Unified.HonestTransition`), `CertStepGen`/`CertStepGenBounded` → `Hagi.Cert.StepGen`, `EvalBinding` → `Hagi.Cert.EvalBinding`, `HonestTransition` → `Hagi.Unified.HonestTransition`, `MetricDirection` → `Hagi.Model.EnergyReasoning` (CRAM), `singularValues`/`Matrix` → `Hagi.External.Flywheel` (зеркало, словарь только здесь). Полное переименование — вне v5.

## Честные границы

Что сознательно не делается и почему:

- `Hagi/External/` и `upstream/` — зеркала внешних источников;
  правка воспроизводится при sync (допуск — только docstring-
  заголовки для nodoc 0, W6).
- `Hagi/Research/` и `Hagi/Research/Legacy/` — карантин: код не
  трогаем, только docstring-уровень.
- `scripts/bench_bridge.py` — монолит: 20+ режимов зафиксированы
  bench-мостами в Lean; parity-gate дороже выгоды нарезки (W5).
- Certificate-хабы (`Hagi/Cert`, cert-семьи Model/Contracts) не
  сливаем — deriv-риск (урок v4).
- Oversized-нарезка (`BatchCEBudgetGuard`, `Dynamics/GrowthBridge`,
  `System/GrowthState`, `Learning/SoftRouterMix`, `Ensemble/Hoeffding`)
  отложена: LayerLint size-лимита нет, нарезка — чистый code-risk
  без гейтовой выгоды (W7, honest-noop).
- BestResidual-цикл: `Hagi/Contracts/BatchCEBestResidual.lean` +
  residual-ось `Hagi/Model/BatchCEDescent.lean` — слияние отклонено
  (deriv-риск), оба файла — живые каноны.
- V2Bridges-слияние микс-мостов Theory (`FactLedger`,
  `RangeWrap`, `AdaptiveContext`, `OEComplete`, `ExactBypass`,
  `TritCodec`) отложено до стабилизации HAGI_v2 cadence и опроса
  внешнего sync-агента (FQN vs module import) — вариант (c)
  v6-плана; карантин мостов волн C567+. Пере-оценка C590
  (2026-11-22): волны 219–225 легли все в один день, последний
  коммит за 2.3ч до оценки — критерий «стабильность ≥12ч» не
  выполнен, sync-агент активен; ОСТАЁТСЯ ОТЛОЖЕННЫМ. Критерий
  исполнения: ≥12ч без коммитов в HAGI_v2 + неактивный
  sync-агент + повторный опрос FQN-vs-module-import.
- 22 bare `import Mathlib` — перманентные deriv-pins (C571,
  терминальное состояние): список сужаемых импортов пуст,
  сужение оставшихся запрещено deriv-риском (урок C482).
- AnytimeHoldoutStop-цикл: `Hagi/Theory/AnytimeHoldoutStop.lean` +
  потребители `Statistics`/`CertifyThenCommit`/`FullPipeline` —
  каркас anytime-остановки, не трогаем.
- Step/SafeQP-контур — свежий, вне рефакторинга.

## Документация

- **[ALGORITHMS.md](ALGORITHMS.md)** — архитектура и алгоритмы
  обучения, связь рецептов с формальными результатами и их посылками.
- **[STATUS.md](STATUS.md)** — главные доказанные результаты
  по каждому Lean-файлу Root, с существенными условиями.
- **[Hagi.lean](Hagi.lean)** — карта импортов для перехода к
  непосредственным определениям и теоремам в дереве `Hagi/`.
- **[docs/PALOMAR-CARDS.md](docs/PALOMAR-CARDS.md)**   — карточки
  двенадцати C5XX-результатов для [Palomar](https://palomar-registry.org/)
  (реестр Lean-верифицированной математики). Карточки готовы;
  отправка — внешний user-шаг: форма
  [submit.palomar-registry.org](https://submit.palomar-registry.org/)
  требует публичного GitHub-репозитория с выделенным
  Challenge/Solution comparator-проектом (см. секцию Submission
  requirements в файле карточек).

## Сборка

Версия Lean закреплена в `lean-toolchain`, зависимости и цели — в
`lakefile.toml`. Сборка корневой библиотеки:

```bash
lake build
```

### Воспроизводимость

Пины окружения (проверяются гейтом MATHLIBPIN в батарее CI):

- **Версия Lean** — файл `lean-toolchain` (локальная сборка
  `lean-4.36.0-windows`); канонический пин коммита компилятора —
  `scripts/mathlib-rev.txt`, строка 2 (`toolchain eb6cafb…`).
- **Версия Mathlib** — `scripts/mathlib-rev.txt`, строка 1
  (`56a0058…`).
- **Сборка** — `lake build` (цели по умолчанию заданы в `lakefile.toml`); полная батарея проверок — шаги
  `scripts/ci.sh`.

Оговорка (локальное окружение): зависимость `mathlib` в `lakefile.toml`
сейчас указана локальным путём (`path = "C:/Users/shmid/mathlib4"`)
— сборочная машина с предсобранной Mathlib. Для чистого клона без
этого пути замените require-блок на канонический git+rev-конфиг
из комментария в `lakefile.toml` (rev — из
`scripts/mathlib-rev.txt`) и запустите `lake build`; lake скачает
и соберёт Mathlib по пину. Прямая правка на этой машине не
проводилась (локальная сборка — рабочая).
