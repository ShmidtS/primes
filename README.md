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
| Теория | [`Hagi/Theory`](Hagi/Theory) | 49 файлов: 10 канон-модулей, мосты HAGI_v2, growth-семья и bench-мосты; карта — [ALGORITHMS §27](ALGORITHMS.md#27-каноны-theory). |
| Интеграция | [`Hagi/System`](Hagi/System), [`Hagi/Unified`](Hagi/Unified) | Связанные состояния, измеренные эффекты, мосты и условные сертификаты. |
| Дополнительные направления | [`Hagi/Autonomy`](Hagi/Autonomy) | Маршрутизация и смежные автономные модели. |
| Примеры и сопровождение | [`Hagi/Challenge`](Hagi/Challenge), [`Hagi/Audit`](Hagi/Audit), [`Hagi/External`](Hagi/External) | Сравнительные формулировки, аудит и внешние математические связи. |
| Карантин и сертификаты | [`Hagi/Cert`](Hagi/Cert), [`Hagi/Benchmarks`](Hagi/Benchmarks), [`Hagi/Research`](Hagi/Research) | Ядро сертификации (`Hagi/Cert`), а также модули вне корневого замыкания `Hagi.lean`: демонстрационные свидетели (`Benchmarks`), исследовательские модели Omni/Percolation/Schelling/Discovery (`Research`) и архив исторических результатов Legacy (`Hagi/Research/Legacy`; сборка целью `Hagi.Research`). |

Каталог `scripts/` содержит вспомогательные средства сопровождения
формализации. Математическим источником остаются файлы `Hagi/**/*.lean`.

## Канон-карта

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

Канон-файлы (одно понятие — один носитель):

| Семья | Канон-носитель | Что поглощено / статус |
| --- | --- | --- |
| Model CE-спуск | `Hagi/Model/BatchCEDescent.lean` | поглощены Common/Arithmetic/Direction/SafeStep; HalfEta/LogitRange/ResidualNorm/Stochastic/Fixtures — отдельные файлы |
| Model CE-шкалы | `Hagi/Model/CEGroupedScale.lean`, `CEJointScale.lean` | CEGroupedScaleBasic, CEScaleChoice, CEScaleSelection слиты; CEJointScale — отдельный канон шкал |
| Contracts growth | `Hagi/Contracts/BatchCEGrowth.lean` | BatchCEGrowthSelection поглощён |
| Contracts EM | `Hagi/Contracts/EMTrajectory.lean` | поглощены MixtureEMTrajectory/FactorizedMixtureEM/FiniteEMTrajectory/ChangingEMTrajectory; носитель `Probability/FiniteMultiEM` не тронут |
| Contracts step | `Hagi/Contracts/BatchCEStepCore.lean`, `BatchCEBestResidual.lean` | слияние отклонено (deriv-риск), оба живые каноны |
| Probability EB-радиус | `Hagi/Probability/EmpiricalBernstein.lean` | EB-радиус: σ̂-подстановка + аддитивный член поверх Freedman |
| Probability Freedman | `Hagi/Probability/Freedman.lean` | поглощены Step/TwoSided/Adaptive/FamilyConfidence |
| Probability MWU | `Hagi/Probability/MirrorHedgeMWU.lean`, `MirrorHedgeGibbs.lean` | семья MWU в двух файлах; `Optimization/MirrorHedge` — независимый потребитель (слой 3) |
| Probability logscore | `Hagi/Probability/FiniteLogScore.lean` | FiniteJointLogScore поглощён |
| Unified loop | `Hagi/Unified/CertifiedLoop.lean` | CertifiedLoopKernel поглощён |
| Numerics | `Hagi/Numerics/Numerics.lean` | SoftmaxFix/QuantSafeUpdate поглощены |
| Pretraining dust | `Hagi/Pretraining/Dust.lean` | DustAlign/DustMeasure поглощены |
| Scripts | `scripts/_shared.py` | общие helpers линтеров и Freeze |

Словарь перегруженных имён (одно имя в разных пространствах имён;
канон-определение — первое): `CertStep` → `Hagi.Cert` (`Hagi/Cert/Core.lean`; вариант `Hagi.Unified.HonestTransition`), `CertStepGen`/`CertStepGenBounded` → `Hagi.Cert.StepGen`, `EvalBinding` → `Hagi.Cert.EvalBinding`, `HonestTransition` → `Hagi.Unified.HonestTransition`, `MetricDirection` → `Hagi.Model.EnergyReasoning` (CRAM), `singularValues`/`Matrix` → `Hagi.External.Flywheel` (зеркало, словарь только здесь). Полное переименование не делалось.

## Честные границы

Что сознательно не делается и почему:

- `Hagi/External/` и `upstream/` — зеркала внешних источников;
  правка воспроизводится при sync (допуск — только docstring-
  заголовки).
- `Hagi/Research/` и `Hagi/Research/Legacy/` — карантин: код не
  трогаем, только docstring-уровень.
- `scripts/bench_bridge.py` — монолит: 20+ режимов зафиксированы
  bench-мостами в Lean; parity-gate дороже выгоды нарезки.
- Certificate-хабы (`Hagi/Cert`, cert-семьи Model/Contracts) не
  сливаем — deriv-риск.
- Oversized-нарезка (`BatchCEBudgetGuard`, `Dynamics/GrowthBridge`,
  `System/GrowthState`, `Learning/SoftRouterMix`, `Ensemble/Hoeffding`)
  отложена: LayerLint size-лимита нет, нарезка — чистый code-risk
  без гейтовой выгоды.
- V2Bridges-слияние микс-мостов Theory (`FactLedger`,
  `RangeWrap`, `AdaptiveContext`, `OEComplete`, `ExactBypass`,
  `TritCodec`) отложено: критерий — ≥12ч без коммитов в HAGI_v2,
  неактивный sync-агент, повторный опрос FQN-vs-module-import.
- 22 bare `import Mathlib` — перманентные deriv-pins
  (терминальное состояние): список сужаемых импортов пуст,
  сужение оставшихся запрещено deriv-риском.
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
  четырнадцати C5XX-результатов для [Palomar](https://palomar-registry.org/)
  (реестр Lean-верифицированной математики). Карточки готовы;
  отправка — внешний user-шаг: форма
  [submit.palomar-registry.org](https://submit.palomar-registry.org/)
  требует публичного GitHub-репозитория с выделенным
  Challenge/Solution comparator-проектом (см. секцию Submission
  requirements в файле карточек). Все 14 карточек внешне
  уникальны (сверка с полным дампом реестра, 1298 results —
  0 пересечений).

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
