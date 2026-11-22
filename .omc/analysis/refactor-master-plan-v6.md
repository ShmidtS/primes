# Refactor Master Plan v6 — инкремент-survey с v5 (C585)

Base: 64aae9ae (C583) + C584 (KnowledgeConsolidation, in flight —
вставить в инвентарь после его коммита; НЕ трогать до landing).
Кредо: минимум кода максимум смысла; то же для доков.
Sources: .tmp/C585/notes-survey.md; v4 (C511), v5 (C522).

Контекст прироста: Theory 31 → 46 файлов (+15 с C584); все новые —
source-anchored мосты к HAGI_v2, собственные namespace, живые
bench-режимы (24 ссылки в bench_bridge.py).

## КОНСЕРВАТИВНОСТЬ (главное отличие v6 от v5)

Материал ГОРЯЧИЙ: биты C530+ активны, мосты синхронизируются с
HAGI_v2 (внешний агент sync-ит наши FQN и module paths). Поэтому:
- Слияния ТОЛЬКО с identity-Freeze (число деклараций байт-в-байт),
  стабильными namespace деклараций И сохранением module path
  (re-export shell либо отказ от слияния).
- Никаких слияний/переименований в файлах, которые трогали биты
  < 10 шагов назад (facts: мосты C574-C584 — карантин до окончания
  HAGI_v2 wave-цикла; RollbackGate C530 уже холоднее — кандидат).
- Каждый транш — отдельный changeset, lake build + Freeze identity
  + StatusLint/DocLint/NsLint на затронутых файлах.

## Транши V1–V5 (rank: дубли/мёртвый вес → риск)

### V1 Канон-заголовки новых Theory-мостов (docs-risk ≈ 0, выгода++)
- Убрать `set_option linter.style.header false` (6 файлов:
  OEComplete, ExactBypass, TritCodec, FactLedger, RangeWrap,
  AdaptiveContext), привести к канону: copyright-блок + `#`
  заголовок + C-бит + source-anchor (`file:line`) в первых строках.
- Единый формат докстринга моста: 1) что формализует, 2) где
  upstream-код, 3) honest-границы. Словарь-продолжение C511–C522:
  bridge-term («source-anchored мост»), rollback-семантика (канон
  RollbackGate), warm/cold-transfer, append-only ledger, Occam-окно.
- Гейт: DocLint + lake build (header lint включён обратно).

### V2 V2Bridges-слияние микс-мостов — УСЛОВНОЕ (выгода −4 файла, риск средний)
- Кандидаты: FactLedger 71 + RangeWrap 63 + AdaptiveContext 114 +
  OEComplete 120 + ExactBypass 129 + TritCodec 137 →
  Hagi/Theory/V2Bridges.lean (~630 строк, namespace каждого
  сохраняется внутри; serial-spine импорты ликвидируются).
- ОБЯЗАТЕЛЬНО: re-export shell на каждый старый module path
  (3 строки: import V2Bridges + re-export) — внешние sync-агенты
  не ломаются. Итого файлов 6 → 7 (V2Bridges + 6 shell)... что
  противоречит «минимум файлов» — поэтому честный выбор:
  (a) слияние с shell'ами: −0 файлов, −~40 строк, +LayerLint-чисто;
  (b) слияние без shell'ов: −5 файлов, ЛОМАЕТ import paths внешних
      sync-агентов — ЗАПРЕЩЕНО до подтверждения оркестратором, что
      внешний sync идёт по FQN деклараций, а не module import;
  (c) отложить (default): слияние только после стабилизации HAGI_v2
      cadence (нет новых волн 2 недели) — записать в tech-debt.
- Рекомендация: (c) сейчас, решение (a/b) — отдельным битом после
  опроса внешнего sync-агента.

### V3 AdapterGrowth нарезка секций (−0 файлов, читаемость, code-risk низкий)
- 908 строк / 4 секции: базис C532; C555 self-compressing loop;
  C556 constant cluster distillation; C558 mini-v3 reference.
- Нарезка по секциям БЕЗ переноса деклараций: под-файлы
  AdapterGrowth/{Core,SelfCompress,ClusterDistill,MiniV3}.lean либо
  только маркировка секций канон-заголовками. Precedent: v5-W7.
- Гейт: build + Freeze identity; при первом же deriv-фейле — откат
  (KISS, 1 fail → только docstring-маркировка).

### V4 Долги v5 (перенос невыполненного)
- STATUS.md свёртка до ~1500 + archive (v5-W6 долг, файл продолжил
  расти с новыми мостами).
- ALGORITHMS.md дедуп описаний новых режимов (mini-hagi-loop,
  adapter-transfer-auto, trit-codec — 3+ описания одного паттерна).
- W1–W4 v5-транши, если не закрыты C523–C529 (проверить
  refactor-*-evidence.md перед исполнением; НЕ предполагать).

### V5 README + карта (финал)
- README canon-map: LayerLint-карта + список Theory-семей
  (growth-семья: AdapterGrowth/AdapterBank/GrowSnap/GrowTrunkBlock/
  FunctionPreservingGrowth; bridges-семья: см. V2; bench-семья:
  MiniHagi/MiniHagi2/MiniHagiLoop/FullPipeline).
- Honest-границы + статус V1–V4.

## Honest-границы v6
- External/, upstream/, Research/Legacy — неизменно (v5).
- bench_bridge.py монолит — неизменно (v5-W5 вердикт, подтверждён).
- Certificate-хабы, Step/SafeQP-контур — не трогаем.
- KnowledgeConsolidation (C584) — карантин до его landing + 10 бит.
- Все мосты волн HAGI_v2 (C567+, AdapterBank/NegativeTransfer/
  TritCodec/FactLedger/RangeWrap/AdaptiveContext/AutoTransferGate/
  MasterTheoremV3) — только докстринги (V1), код не трогаем.

## Гейты каждого транша
1. `lake build` exit 0 (PATH lean-toolchains 4.36.0).
2. Freeze identity (свежий build обязателен — текущие olean stale).
3. StatusLint / DocLint / NsLint / DupLint по затронутым файлам.
4. Atomic commit `refactor(Vx): <summary>`.
5. 3 fails → STOP, откат, tech-debt запись.
