# Refactor cycle 3 — residual survey (READ-ONLY)

Базовый коммит: 37955993 (`refactor: docs event tags tail and era index
repins`), tree clean. Freeze: `python scripts/Freeze.py` →
`PASS (8849 declarations, 0 aliased, nothing lost/changed)` (31 s;
toolchain 4.36.0 в PATH, как в `scripts/ci.sh`).

Директива: «объединяй схожие идеи и файлы; повторяй циклично». Цикл 3 =
подсчёт остатка после v7 (T1–T8) и cycle-2 (U6 pilot, U8, U9). Код не
менялся: 234 162 строки / 617 tracked-файлов — те же, что на входе.

Все числа ниже — вывод команд (`git ls-files | xargs cat | wc -l`,
`rg -c`, python-скрипты AST/re по `Hagi/**`, `docs/`, `scripts/`).

## A. Lean (`Hagi/**.lean`)

Модулей: 552 (tracked `*.lean` — 558 = 552 + `Hagi.lean` + 5
`scripts/*.lean`). Вход в задачу говорил «557→?»: по факту 552 модуля
под `Hagi/` + `Hagi.lean` + 5 скриптов = 558.

### A1. Файлы < 30 строк

| Строк | Файл | Роль |
| --- | --- | --- |
| 18 | `Hagi/Benchmarks.lean` | корень `lean_lib Hagi.Benchmarks` (`lakefile.toml` defaultTargets) |
| 20 | `Hagi/Unified/ParetoExecution.lean` | umbrella: 3 import, 0 объявлений |
| 24 | `Hagi/Contracts/BatchCETrajectory.lean` | umbrella: 12 import, 0 объявлений |
| 24 | `Hagi/Model/EnergyReasoning/Pseudolikelihood.lean` | umbrella: 4 import, 0 объявлений |

Все четыре — агрегаторы импорта, не «маленькие идеи». Слияние в
соседа = смена module-path у корня библиотеки или у точки импорта
для 3 (`Pseudolikelihood`: `Hagi.lean`, `Contracts.DataToQuality`,
`Training.StepProvider`) / 1 (`ParetoExecution`) потребителей.
Выгода ≤ 4–6 строк (docstring остаётся). Вердикт: **skip**.

### A2. Пары с общим префиксом темы

Импорт-рёбра сняты скриптом по `^import Hagi…` (DAG, без циклов).

| Пара / цепочка | Импорт | Выгода (boilerplate) | Вердикт |
| --- | --- | --- | --- |
| `AdapterBank` (230) → `AdapterGrowth` (926) → `Continual` (499) | Growth импортирует Bank; Continual импортирует оба | 4 + 7 строк | **skip**: три разных namespace (`AdapterBank`, `AdapterGrowth`, у Continual четыре: `ContinualBench/ContinualMulti/GPMRelaxed/HybridContinual`); слияние = multi-ns файл, т.е. откат направления U6. Bank отдельно импортирует `AutoTransferGate`, Growth — `MasterTheoremV3`, `MiniHagiLoop` |
| `RangeWrap` (65) ↔ `AdaptiveContext` (116) | RangeWrap импортирует AdaptiveContext | 2 строки | **skip**: разные namespace, 29 строк docstring каждая — тема общая только по имени |
| `DescentCore` (95) + `DescentCoreDiag` (136) + `DescentCoreQuad` (169) | Core импортирует Diag и Quad; Diag/Quad импортируют `QuadMachine` | 2 + 3 строки | **skip**: 23 прямых импортёров Core; Diag/Quad имеют 7/20 транзитивных потребителей сами по себе |
| `HNet` (180) + `HNet2` (92) | ни один не импортирует другой | 1 строка | **skip**: namespace `Hagi.Model.HNet2` ≠ `Hagi.Model.HNet`; identity-слияние возможно только как 2-ns файл |
| `DerivAlong` (616) + `DescentCore*` | рёбер нет | — | **skip**: unrelated по DAG |
| `RollbackGate` (239), `SelfEdit` (399), `KnowledgeConsolidation` (85) | рёбер нет, каждый импортирует только `Hagi` | — | **skip**: общий префикс только тематический (жизненный цикл модели) |
| `Compression` (946) + `SelfEdit` + `KnowledgeConsolidation` | рёбер нет | — | **skip** |
| `MasterTheorem` ↔ `MasterTheoremV3` (328) | рёбер нет; V3 импортирует только `Hagi` | — | **skip** (граница из cycle-2 сохраняется: разные import-слои, V3 — корень) |
| `Freedman` (4490) — один файл, не ×4 | — | — | **n/a**: `fd 'Freedman'` → 1 файл; «×4» — счётчик namespace-блоков до U6, не файлов |
| `EmpiricalBernstein` (341) | импортирует `Freedman`; 2 прямых импортёра | — | **n/a**: один файл |
| `MWU` + `MirrorHedgeMWU` (1640) | `MirrorHedgeMWU` импортируют `Optimization.MirrorHedge` и 5 других; отдельного `MWU.lean` нет | — | **skip/n/a** |

Итог A2: суммарная выгода всех skip-слияний < 20 строк; каждое либо
меняет module-path, либо создаёт multi-namespace файл. Build-cycle не
возникает ни для одной пары (DAG ацикличен, рёбра направлены в одну
сторону), но и identity-выгоды нет.

### A3. Docstring-вода (Theory, 48 файлов)

Docstring-строк: 5771. Паттерны-вода (`Это важно`, `важно отметить`,
`roadmap`, `TODO`, `см.` и т.п.): 22 строки. Из них 16 — `см. \`decl\``:
живые перекрёстные ссылки на теоремы (информация, не вода). Остаток
roadmap-хвостов по всему `Hagi/` — 17 строк в 12 файлах:

- `Theory/NegativeTransfer.lean:13` «Source-anchored мост волны
  HAGI_v2 (roadmap top-3)», `:512` «Новая эра (roadmap top-1)»
- `Theory/FullPipeline.lean:13`, `:220` «The roadmap gap (item 4)»
- `Theory/BlockAdmission.lean:12`, `Theory/AnytimeHoldoutStop.lean:10`,
  `Theory/ProvenTrunk.lean:9`, `Model/LMCompose.lean:10`
  «Дорожная карта (топ-N)»
- `Theory/BlockLipschitz.lean:11` «Beat (A19 G1, roadmap)»,
  `Theory/CoverageReading.lean:342` «roadmap: минимизирует ли…»
- `Data/PACBayes.lean:12,:87`, `Ensemble/Hoeffding.lean:671`,
  `Theory/Softmax.lean:74`, `Probability/ConditionalSuccess.lean:11`,
  `Research/Legacy/RecursiveGrowth.lean:146,:159` — «roadmap #N» как
  имя результата (сохранить, это адрес источника)

Это doc-правка (~12 строк), не объединение. Отдельно: `**…**`
bold-акценты — 1376 строк в 203 файлах; это стиль, не вода, и не
трогается (U2 прошёл мимо — честно фиксируем как convention).

### A4. Остаток namespace re-open (после U6 pilot, 5 файлов)

Скрипт: `namespace X` встречается > 1 раза в файле.

- 65 файлов, 167 «лишних» блоков.
- Из них single-namespace (один ns, разорван на N блоков): 25 файлов /
  58 блоков — механически joinable режимом `merge_module.py --join-ns`.
- Multi-namespace (чередование `Hagi.A`/`Hagi.B`/`Hagi`): 40 файлов /
  109 блоков — interleaved scopes (`open`/`variable`/`section` между
  блоками разные); join = перестройка файла, honest-граница U6 wave-2.

## B. docs/

12 файлов, 2982 строки; с root-md (`STATUS`, `ALGORITHMS`, `README`,
`RELATED`) — 16 файлов, 8647 строк.

| Строк | Файл |
| --- | --- |
| 3340 | `ALGORITHMS.md` |
| 2057 | `STATUS.md` |
| 1291 | `docs/paper-draft.md` (было 1334) |
| 509 | `docs/PALOMAR-CARDS.md` |
| 217 | `README.md` |
| 199 | `docs/PROPOSAL-external-plan.md` |
| 184 | `docs/PROPOSAL-adaptive-majorizer.md` |
| 141 | `docs/PROPOSAL-tight-kappa.md` |
| 128 | `docs/PROPOSAL-fisher-quant.md` |
| 124 | `docs/PROPOSAL-joint-step.md` |
| 121 | `docs/UPSTREAM-SVD.md` |
| 122 | `docs/PROPOSAL-merge-meas.md` |
| 104 | `docs/PREMISES-STATUS.md` |
| 51 | `RELATED.md` |
| 37 | `docs/CONSOLIDATION-GAPS.md` |
| 22 | `docs/PROPOSAL-index.md` |

Дословные абзацы ≥ 2 строк, общие для ≥ 2 файлов: **0**.
Дословные предложения ≥ 8 слов в ≥ 2 файлах: **4**:

- `PROPOSAL-adaptive-majorizer` ↔ `PROPOSAL-tight-kappa`: «`real_drop ≥
  certified_drop` on EVERY step of a full run.»
- `PROPOSAL-fisher-quant` / `joint-step` / `merge-meas` /
  `tight-kappa`: «## (b) Formulas and Lean anchors (primes, Freeze
  8462)» и «anchors are proved and frozen in primes (Freeze 8462,
  module …)» — **stale pin** (Freeze сейчас 8849), 4 файла.
- `ALGORITHMS.md` ↔ `STATUS.md`: «(`‖R a − R b‖ = ‖a − b‖).» — одна
  формула.

Перекрытие capitalized-токенов (≥ 20) — 15 пар; top: `STATUS` ↔
`ALGORITHMS` 193, `STATUS` ↔ `README` 79, `ALGORITHMS` ↔ `README` 55,
`PREMISES-STATUS` ↔ `STATUS` 51, `paper` ↔ `ALGORITHMS` 47. По
замыслу это разные роли (cards = statement-канон, STATUS = карта
носителей, ALGORITHMS = доказательная карта): общие токены — имена
объявлений, не абзацы. Дословного повтора нет → канон-дубли, **skip**.

paper: заголовки §3 — 18 подразделов, нумерованных по «эрам»
(3.10 Adapter era, 3.11 External absorption, 3.18 The reading era),
§4.5/4.6 — по commit-диапазонам (C560–C603, C606–C613), §4.4
«wave205», Appendix A pinned на `2d619fc8 (+T5)` (старый sha).
Слов «журнал»/«Appendix» — 0/2 (Appendix A единственный), abstract 1.
Ни один `scripts/*.py` не читает `paper-draft` (`rg -l paper-draft
scripts` → 0), так что это не machine-якоря; переименование =
doc-правка по вкусу, не объединение.

## C. scripts/

- `bench_bridge.py`: 14 635 строк (было 14 634, +1 к входу цикла), 356 функций,
  255 banner-комментариев режимов `--mode …`.
- Идентичные тела функций (AST, без docstring) между файлами: 2 —
  `rat` и `lean_step` (`bench_bridge.py:1160–1161` ↔
  `selfloop_bridge.py:135–136`, 2 строки). `selfloop_bridge` не
  импортирует `bench_bridge` (38 строк общих `argparse/json/sys/
  Fraction`); ради 2 строк тянуть импорт 14.6k-модуля — **skip**.
- Внутри `bench_bridge` идентичные формы (ids абстрагированы): 8 групп
  (`ce_grad`/`ht_grad`, `emit_bad_*`, `*_unflat`, `*_snap` ×4,
  `*_gs_basis`, `*_complement_projector`) — bench-нарезка, граница.
- Одинаковые имена функций в ≥ 3 файлах: `main` ×19 (entrypoints),
  `setUp` ×4 / `tearDown` ×3 (unittest-шаблон), `collect` ×3
  (`DupLint.collect()`, `Freeze.collect(root, semantic)`,
  `TestFreeze` helper) — разные сигнатуры/тела, совпадение только
  имени.
- `scripts/*.lean` (5): `AllAxiomCheck` 73 (2 decl), `NamePool` 14
  (0), `TrivialLint` 465 (32, ns `TrivialLint` + `SelfTest`),
  `inventory` 174 (5, ns `CanonPrivate`), + `Freeze.py` 264. Общих
  имён объявлений между ними — **0**. Каждый — отдельный CI-гейт.

## D. root

Tracked 11: `.gitignore` 18, `ALGORITHMS.md` 3340, `Hagi.lean` 514,
`LICENSE` 203, `README.md` 217, `RELATED.md` 51, `STATUS.md` 2057,
`lake-manifest.json` 127, `lakefile.toml` 199, `lean-toolchain` 1,
`stmdup_allowlist` 30. Chesterton: `stmdup_allowlist` — вход
`StatementDupCheck`; `RELATED.md` 51 — отдельная роль (внешние
источники), в docs/ не переносить. Удалять/объединять нечего.

## Вердикт

(i) Остаток, объединяемый без потери смысла: **один** кандидат —

| Волна | Scope | Выгода | Риск | Freeze |
| --- | --- | --- | --- | --- |
| W1 = U6b (single-ns) | 25 файлов, 58 лишних `namespace`-блоков | −2…−3 строки/блок ≈ −120…−175 строк | средний: scope между блоками (`open`/`variable`/`section`) — A/B `lake build` + Freeze + AllAxiomCheck на каждый файл; pilot-показатель 5/5 прошёл | identity (pilot 3574bcb9) |

Остаток W1 = 0.05–0.07 % строк репо. Если пользователь хочет
закрыть U6 полностью — это W1; иначе рекомендация: **не стоит риска**,
цикл остановить на v7 + cycle-2 (−2743 строк).

(ii) **Honest-стоп.** Дальнейшее объединение меняет смысл/scope или
ломает структуру:

- multi-ns re-open: 40 файлов / 109 блоков — interleaved scopes,
  join = перестройка файла (U6 wave-2, известная граница).
- слияние модулей A1/A2: меняет module-path либо создаёт multi-ns
  файл (< 20 строк выгоды на всё).
- docs: дословных абзацев 0; перекрытия — канон по ролям.
- bench_bridge нарезка, PROPOSAL-*/RELATED, MasterTheorem↔V3,
  `linter.style.header false` — границы cycle-2 сохраняются.

Вне директивы «объединяй», но найдено (doc-правки, −~16 строк):
stale pin «Freeze 8462» в 4 PROPOSAL-файлах; roadmap-хвосты 12
строк в 8 Theory/Model файлах; paper Appendix A sha `2d619fc8 (+T5)`.
