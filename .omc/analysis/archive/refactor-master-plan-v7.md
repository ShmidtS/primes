# Refactor Master Plan v7 — survey (C637)

Кредо: минимум символов — максимум смысла; циклично по каждой
строке. Base: HEAD 606e899f (C636), tree clean, Freeze 8849.
Precedents: v4 (C511), v5 (C522), v6 (C585) — v4–v6 файлы удалены
в `c442e69a cleanup`; читаны через `git show`. Директива после
C590: «identity где возможно; CHANGED только с honest bake».

## 0. Sizes (tracked, `git ls-files | xargs wc -l`): 236 905

| Слой | Строк | Файлов | Примечание |
| --- | ---: | ---: | --- |
| Hagi (Lean всего) | 202 988 | 557 модулей | ReachLint: 557 |
| — Hagi/Theory | 19 694 | 53 | README говорит «47» — устарело |
| — Hagi/Contracts | 18 398 | 35 | |
| — Hagi/Research (+Legacy) | 10 911 | 39 | карантин |
| scripts | 21 179 | 38 | bench_bridge 15 016 (71%) |
| docs | 3 079 | 12 | paper 1 399, cards 508 |
| Root docs (STATUS/ALGORITHMS/README/RELATED) | 6 190 | 4 | |
| .omc/analysis (tracked) | 1 634 | 10 | period-c591…c633 |
| upstream, Challenge, прочее | ~370 | | вне scope |

Монолиты (top): bench_bridge.py 15 016 · ALGORITHMS.md 3 423 ·
STATUS.md 2 487 · BatchCEGrowth 2 920 · Freedman 4 490 ·
paper-draft 1 399 · AdapterGrowth 926.

Базовые линты (read-only прогон C637, `.tmp/C637/logs/`):
STATUSLINT/DOCLINT/LAYERLINT/DUPLINT/STMDUP/REACHLINT — PASS,
NSLINT PASS (25 vs baseline 31). TrivialLint/Freeze/AllAxiom —
требуют lake; на survey не запускались (Lean не тронут).

## A. Lean-слой: таблица кандидат-объединений

| # | Файлы | Что общего | Выгода | Риск / freeze |
| --- | --- | --- | --- | --- |
| L1 | `MasterTheoremV31` 105 + `V32` 99 + `V33` 109 (each 1 theorem + 1 `#print axioms`) | одна «лестница» конъюнкций: v33 ⊃ v32 ⊃ v31 дословно (клозы (1)–(10) — проекции `have hV32`); module docstring каждой версии повторяет карту клозов предыдущих | −2 файла, −~120 строк (3 docstring-карты → 1 + список версий); 1 `#print axioms` | identity при сохранении трёх ns-блоков дословно (R1); смена ns на `MasterTheoremV3.v33` была бы CHANGED — не делаем. Потребители: только Hagi.lean (4 import) |
| L2 | `CoverageReading` 551 + `WindowTradeoff` 204 | одна тема «чтение окнами»: covStarts/covStartsStep/hier → cost(w) поверх hier_total. WindowTradeoff — единственный импортер CoverageReading и не импортируется никем (кроме Hagi.lean) | −1 файл; убирает 4× `end namespace`/`namespace` re-open в CoverageReading (−12 пустых строк + 4 заголовка docstring-модуля → один) | identity (ns сохраняется блоками; Freeze ключует по FQN, R1). WindowTradeoff ≤ 12 шагов назад (C623/C628) — код не меняется, только перенос |
| L3 | `NegativeTransfer` 501 (3 секции Quad/SmoothNL/Schedule) + `GrowthGate` 189 | GrowthGate = 4-я секция Schedule (nl_drop_step_eq/nl_drop_total/nl_drop_optimal — одна линия «γ* = 1/L»); imports только NegativeTransfer | −1 файл, −1 copyright+module-docstring; GrowthGate `linter.style.header false` уходит | C632 (5 шагов) — ГОРЯЧИЙ. Freeze identity при сохранении ns. Рекомендация: отложить до T8 либо только docstring-слияние |
| L4 | `NegativeTransfer` внутренняя структура | section-заголовки «C592», «C606» — события, не темы; 3 `example`-witness (nlDrop числа) внутри Schedule | заголовки по смыслу (`## Drop и оптимальный шаг`), examples → 1 (нужны для DocLint-чисел? проверить) | identity; ~−15 строк |
| L5 | `AdapterGrowth` 926, 11 секций | 5 заголовков секций начинаются с C-метки (C533/C535/C536/C544/C560) | переименовать в смысловые; docstring-карта (C587) пересчитать | identity; 0 строк, чистый смысл |
| L6 | docstrings Lean: 1 973 строк с `\bC\d{3}\b` (2 219 меток), 25 файлов с «roadmap», 14 строк со `.tmp/`-ссылками на игнорируемые (несуществующие после cleanup) файлы | событийные метки вместо причины | `.tmp/`-ссылки — мёртвые якоря → −14 строк или замена на «witness: git show <sha>»; roadmap-фразы («Roadmap C620 top-2») → удалить (−29 строк/фраз) | identity (комментарии); DocLint gate |
| L7 | `MasterTheorem` 688: 3 module-docstring блока (MasterTheorem, MasterBudget, VerticalCapstone в ns `Hagi.Unified`) + `set_option linter.style.header false` ×1 | merge-артефакт C383 | −2 повторных copyright/`set_option` | identity; низкий приоритет |

Не-кандидаты (подтверждено, Chesterton): Certificate-хабы, External/,
upstream/, Research — границы v5/v6 действуют; V2Bridges (6 микро-
мостов) — отложено до подтверждения FQN-vs-module-import у внешнего
sync-агента HAGI_v2 (критерий ≥12ч без коммитов — не выполнен,
C634/C635/C636 коммитили в течение часа).

Семантические повторы (не буквальные — STMDUP 0): docstring
`hagi_master_v31/v32/v33` перечисляют одни и те же клозы (1)–(8)
трижды; карты клозов дублируются в STATUS (C600/C614/C622),
paper §3.17–3.20 и cards. Канон должен быть один — см. D2.

**R1 — решён (код Freeze.py:135 `index()`)**: lock ключуется по
FQN + statement-hash + kind, НЕ по module path. Значит перенос
целого namespace-блока в другой файл при сохранении ns и statement
= **identity** (сырой `python scripts/Freeze.py` PASS, без
`--update`). CHANGED возникает только если меняется сам statement
(FQN делегата при смене ns) — поэтому во всех волнах ns-блоки
сохраняются дословно. External-check (READ-ONLY): `rg
'MasterTheoremV3|CoverageReading|WindowTradeoff' C:/HAGI_v2` → 1
hit, комментарий `hagi/lm.py:999` (не import) → module-path этих
файлов внешне не импортируется; T1/T2 не ломают sync.

## B. Docs-слой

| # | Объект | Факт (числа) | Решение |
| --- | --- | --- | --- |
| D1 | STATUS.md 2 487 | строки 1–1740 — канон-карточки по файлам; 1814–2487 (673 строки, 27%) — событийный журнал: «Freeze N → N+k» ×26, «17 гейтов PASS» ×19, `.tmp/`-ссылки ×33, roadmap-фразы; заголовки «## C609 …», «## C611 …» — по витку, не по файлу (CoverageReading описан 4 раза: 1994, 2060, 2143, 2213; NegativeTransfer 3 раза: 1919, 2098, +C609) | T4: переставить в канон-карточки «по файлу» (одна секция CoverageReading с 4 подпунктами), выбросить freeze-дельты/гейт-счётчики/tmp-пути (это в period-файлах .omc). Оценка −400…−500 строк. «Архив»-заголовок строк 1–5 уже указывает на git — сохранить |
| D2 | Пересечения имён деклараций: STATUS↔ALGORITHMS 169, STATUS↔paper 92, cards↔paper 27, cards↔STATUS 36 | ALGORITHMS §27a (таблица 18 мостов C521–C584) = краткая версия тех же карточек STATUS 1741–1990; STATUS-карточки C598–C635 не имеют аналога в §27a (разрыв) | ONE canonical: **ALGORITHMS §27a — таблица мостов** (что/где, 1 строка на мост), **STATUS — карточка по файлу** (statement-уровень + honest pin), **cards — внешняя формулировка** (без C-меток), **paper — нарратив** (ссылки на FQN, без повторных карт клозов). Из paper §3.17/3.18/3.20 убрать повторные перечисления клозов (1)–(8) → одна таблица в §3.17, v3.2/v3.3 — только дельта. −~120 строк paper |
| D3 | README 230 | канон-карта содержит историю рефакторингов: «W1–W8», «v6-V3», «пере-оценка C590 … волны 219–225 легли в один день», «47 файлов» (факт 53), «тринадцать/четырнадцать» cards (cards:15 говорит «тринадцати», их 14) | T3: канон-карта → только текущее состояние (канон-носитель | что поглощено), история волн — одна строка со ссылкой на git log. −~40 строк; счётчики исправить либо убрать (числа в README = Goodhart-риск: каждый виток их старит) |
| D4 | ALGORITHMS 3 423 | §11–§23 — заголовки с C-метками («## 12. … (C230)»), 229 C-меток; §24–26 «Итоги фазы C263–C291» и т.п. — событийные | §24–26 (≈80 строк) — журналы фаз → в .omc period-файлы (уже tracked) или удалить; C-метки из заголовков §9 subsections (C300, C307…) — убрать, C-метки в теле оставить только где ссылаются на реальный источник (commit) |
| D5 | `.omc/analysis/period-*.md` 10 файлов 1 634 строк | tracked, событийные, с `.tmp/`-ссылками; дублируют commit one-liners (`git log`) | кандидаты на удаление (git-история хранит то же); решение — user. Если оставить: не трогать (история) |
| D6 | `.tmp/`-ссылки в docs: STATUS 33, ALGORITHMS 12, paper 42, cards 2, Lean 14 | `.tmp/*` в .gitignore и очищен `c442e69a` → 100% мёртвые якоря | заменить на «git show <sha>:<path>» только там, где witness несёт смысл (paper-source-комментарии), остальные удалить. paper: HTML-комментарии `<!-- source: … .tmp/C600/receipt.md -->` — 42 |
| D7 | paper 1 399 | §3.5 стоит после §3.9 (нумерация сломана: 3.4 → 3.6 … 3.9 → 3.5 → 3.10); заголовки несут C-метки; Appendix A «verified at HEAD 977c930b» — устарел | T5: перенумеровать §3.x по порядку; C-метки из заголовков → в конец заголовка убрать, оставить в тексте |

Не-цель: RELATED, PREMISES-STATUS (103, компакт), CONSOLIDATION-GAPS
(36), PROPOSAL-* (исторические — оставить как есть).

## C. Scripts

| # | Объект | Факт | Решение / выгода |
| --- | --- | --- | --- |
| S1 | bench_bridge.py 15 016, 358 функций, `main` 1 341 (dispatch 40 режимов + 400-строчный `help=`), 48 `emit_*` функций = 1 940 строк | v5-W5 вердикт «монолит сохраняется» стоит; с тех пор добавлен `_mini_report` (C598+, уже вынесен). AST-аудит: 28 блоков пар-стейтментов, общих для ≥5 функций семейства mini-hagi2/3/4/5 + grow-snap + adapter-{grow,snap-grow,rank-adaptive,merge}: канон Phase-A (`pts = mh_load_dataset…`, `hold = … i % 5 == 4`, `MH2_A_STEPS` loop, fd-градиент `q[k] + MH2_H`, `raw.append({"phase": "A-trunk2"…})`) — 63 строки × 8–9 копий; `emit_lean_*`/`emit_bad_*` пары 34 шт с одинаковым хвостом `with open(path…) print(written)` ×8 | T6a: `_phaseA_corpus()` + `_fd_snap_step()` helpers (2 функции, ~−250 строк, golden-diff: stdout до/после для 9 режимов байт-в-байт). T6b: `_write_json(path, obj)` (−~60 строк). `help=` → dict `{mode: text}` + `argparse.SUPPRESS` + `--help-modes` (−~350 строк) — опционально, меняет CLI-help (не вывод режимов) |
| S2 | `emit_*` Lean-генераторы | 48 функций пишут witness-lean; по структуре — `header + params + body + tail` | НЕ объединять в T-волнах: каждый emit — parity-gate конкретного режима (C5xx-мосты в Lean). Вне scope, honest-noop (подтверждает v5-W5) |
| S3 | lint-скрипты | `_shared.py` уже есть (lean_files, strip_comments, DECL_RE, prefixes). Остались клоны: import-regex ×6 (LayerLint, ReachLint, Metrics ×1, ClosureReport, triviality?), DECL_RE ×3 (StatusLint, Freeze, DocLint `DECL`, AssumptionScan `DECL`), NS_RE ×2 (NsLint, Metrics) | T7: в `_shared.py`: `IMPORT_RE`, `DECL_RE` (уже есть — StatusLint/Freeze/AssumptionScan переключить; их regex чуть шире — `alias`/`inductive`/`@[]` — объединить по самому широкому, прогнать все линты → вывод идентичен), `NS_RE`. −~25 строк, 1 источник. YAGNI-гейт: только идентичный вывод |
| S4 | Test*.py (4 файла, 1 252 строки) | пары script+test — оставляем | — |

Golden-гейт для S1: для каждого затронутого режима `python
scripts/bench_bridge.py --mode X …` (параметры из STATUS-карточки)
→ sha256 stdout/файлов до == после. 1 fail → откат волны.

## D. План-волновка v7 (T1..T8) — 1 волна = 1 коммит

Freeze-правило: identity = `python scripts/Freeze.py` PASS без
`--update` (lock 8849 строк не меняется; Freeze ключует по FQN +
statement-hash, module-path не в lock — R1). CHANGED допустим только
через `--update` после review + слово `bake:` в commit-msg с
причиной; в v7 ни одна волна этого не планирует. Механика
переноса — `scripts/merge_module.py` (TestMergeModule: Lean modes
=2, прецедент v5 W1–W4). Гейты каждой волны: `lake build` exit 0 → Freeze →
StatusLint/DocLint/NsLint/DupLint/StatementDupCheck/LayerLint →
`ci.sh` целиком в конце каждой Lean-волны. 3 fail → STOP, откат,
запись в план.

| Волна | Scope | Freeze | Docs-side | Выгода |
| --- | --- | --- | --- | --- |
| T1 | L1: MasterTheorem V31+V32+V33 → `MasterTheoremV3.lean` (один файл, namespace-блоки `Hagi.Theory.MasterTheoremV3/V31/V32/V33` сохранены, одна карта клозов + дельты версий, один `#print axioms` на версию — оставить 4, они дешёвые); Hagi.lean −3 import | identity (R1) | STATUS: 3 карточки → 1; ALGORITHMS §27 строка; README строка; paper §3.17/3.18/3.20 → дельты (D2) | −2 файла, −~120 Lean, −~120 paper |
| T2 | L2: CoverageReading + WindowTradeoff → `CoverageReading.lean`; убрать 4× namespace re-open (одна `namespace …`), один module-docstring + 4 секции | identity (ns-блоки сохранены) | STATUS: 4 карточки CoverageReading + 2 WindowTradeoff → 1 секция по файлу с подпунктами | −1 файл, −~40 строк |
| T3 | L4+L5+L6: docstring-чистка Lean (C-метки/roadmap/.tmp в 25+14 строках; section-заголовки NegativeTransfer/AdapterGrowth по смыслу) | identity | — | −~60 строк, смысл вместо меток |
| T4 | D3 README + D4 ALGORITHMS (canon-карта без истории; §24–26 → период-файлы; счётчики) | identity | StatusLint (пути `](Hagi/…)`) | −~120 строк |
| T5 | D1+D2 STATUS: перестановка журнала 1814–2487 в карточки по файлу, удаление freeze-дельт/tmp; paper §3 перенумерация, карты клозов → одна | identity | StatusLint | −400…−500 STATUS, −~120 paper |
| T6 | S1 bench_bridge: `_phaseA_corpus`, `_fd_snap_step`, `_write_json`; help-dict | python-only | golden-diff 9 режимов + 8 emit | −~360 строк |
| T7 | S3 `_shared.py` import/ns regex | python-only | вывод 7 линтов идентичен | −~25 строк |
| T8 | L3 GrowthGate → NegativeTransfer секция (после остывания ≥10 шагов) + L7 MasterTheorem header dedup | identity | STATUS/README строки | −1 файл, −~15 строк |

Порядок T1→T2 выбран по «наименьшая Lean-площадь первой» и чтобы
T1 сразу ответил на R1 (механика Freeze при переносе). T6/T7
независимы от Lean — можно параллелить с T4/T5 (Dunbar: ≤2
агента на docs + 1 на scripts). T8 — явный отложенный кандидат;
если HAGI_v2 sync активен — остаётся honest-noop.

## Honest-границы v7

- Lean-код (statement/proof bodies) не меняется ни в одной волне:
  только перенос целых блоков и docstrings. Исключение — ноль.
- Внешний sync-агент HAGI_v2: module-import vs FQN — не подтверждено
  → V2Bridges не сливаем; T1/T2 меняют module-пути (файлы
  исчезают) — ПО ЭТОЙ ЖЕ ПРИЧИНЕ требуют проверки: если sync
  импортирует `Hagi.Theory.MasterTheoremV33`, T1 ломает его.
  Действие до T1: `rg 'MasterTheoremV3|CoverageReading|WindowTradeoff'
  C:/HAGI_v2` (READ-ONLY) — 0 hits → зелёный свет; иначе shell-файлы
  (3 строки import+re-export, вариант v6-V2a).
- bench_bridge: нарезка на модули — нет (parity-gate), только
  helpers с golden-diff.
- period-*.md, PROPOSAL-*, RELATED — решение об удалении за user.
- Числа в README («47 файлов», «14 карточек») — убрать счётчики,
  не обновлять (каждый виток старит; Goodhart).

## Гейты (чек-лист волны)

1. `lake build` exit 0 (PATH lean-toolchains/lean-4.36.0-windows/bin).
2. `python scripts/Freeze.py` → PASS identity | bake-свидетель.
3. StatusLint / DocLint / NsLint / DupLint / StatementDupCheck / LayerLint / ReachLint.
4. `bash scripts/ci.sh` → CI: PASS (конец каждой Lean-волны).
5. golden-diff (T6/T7).
6. Atomic commit `refactor(v7 Tn): <summary>`; `.tmp/C6xx/receipt.md`.
