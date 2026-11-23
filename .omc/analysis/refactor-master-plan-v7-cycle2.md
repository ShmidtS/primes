# Refactor Master Plan v7 — cycle 2 survey (V7-AUDIT)

Кредо прежнее: минимум символов — максимум смысла; циклично по
каждой строке. Base: HEAD ddaeb456 (T8), tree clean, Freeze 8849.
Вход: v7 survey 7e83a52a (этот файл, §0–D заменены — история в git).

## 0. Итог v7 (числа; полный аудит — `.tmp/V7-AUDIT/`)

Гейты: `bash scripts/ci.sh` → CI: PASS (5m05s, lean-4.36.0 на PATH;
lean-4.35.0 из default PATH даёт «incompatible header» — среда, не
код). Freeze identity 8849. pytest Test*.py 63 passed. Bench 9
golden-режимов (mini-hagi2/3/4/5, grow-snap, adapter-grow/-snap-grow/
-rank-adaptive/-merge): exit-коды 9/9 = T6; stdout 6/9 байт-в-байт,
3/9 (adapter-snap-grow/-rank-adaptive/-merge) идентичны по модулю
`elapsed_s` — тот же класс, что T6 фиксировал. Все 37 конфигураций
capture.py: exit = T6 after.

| Слой | 606e899f | HEAD | Δ | Прогноз v7 |
| --- | ---: | ---: | ---: | --- |
| Hagi/Theory | 19 694 | 19 562 | −132 | −~215 (L1 −120, L2 −40, L3 −15, L6 −60) |
| Hagi (остальной Lean) | 183 294 | 183 284 | −10 | 0 (T3 docstrings) |
| scripts | 21 179 | 20 808 | −371 | −~385 (T6 −360, T7 −25) |
| docs | 3 079 | 3 014 | −65 | −~120 paper |
| Root docs | 6 190 | 5 685 | −505 | −~520…620 (D1 −400…500, D3 −40, D4 −80) |
| .omc/analysis | 1 634 | 1 782 | +148 | — (v7 survey) |
| Прочее | 1 835 | 1 830 | −5 | |
| **TOTAL** | **236 905** | **235 965** | **−940** | −~1 240…1 340 |

Факт −940 из −1 240…1 340: LeanTheory переносы дали меньше (карты
клозов сохранены как дельты, не удалены), paper −65 вместо −120
(карты клозов сжаты, C-метки в тексте остались), bench −382 (точно).
Файлов 632 → 628 (−5 Lean, +1 .omc).

Мёртвые ссылки (tracked, вне .tmp):
- `.tmp/` — Lean 0 (было 14), STATUS 0 (33), paper 0 (42); остаток
  docs 14 (ALGORITHMS 5, PROPOSAL-* 8, cards 2) + bench_bridge 16
  (8 — runtime-пути снапшота/вывода, живые; 8 — «research .tmp/C5xx»
  witness-ссылки в комментариях) + selfloop_bridge 1.
- Имена удалённых файлов (WindowTradeoff / GrowthGate / V31–33):
  0 stale file-path; 15 файлов упоминают — все это сохранённые FQN
  namespace (`Hagi.Theory.WindowTradeoff` и т.п., Freeze identity) или
  period-история. Не ссылки на файлы.
- `file:line` якоря в STATUS/paper/cards/ALGORITHMS/README: 151
  существует, 0 битых внутри primes (2 «missing» в
  CONSOLIDATION-GAPS:24-25 — пути HAGI_v2 `scripts/restore_domains.py`,
  `hagi/unified.py` — внешний репо, вне проверки).
- md-ссылки: 349 ok, 2 битые (README): `STATUS.md#hagiunifiedderivalonglean`
  (карточки DerivAlong нет — файл упомянут только внутри карточки
  CEHeldout); `](Hagi/Prelude)` ×2 (каталог удалён C348).

Дубли-индикаторы: `^## <file>` в STATUS — 146 файлов, 0 повторов
(было: CoverageReading ×4, NegativeTransfer ×3). Пересечения имён
деклараций: STATUS↔ALGO 205 (169), STATUS↔paper 116 (92),
cards↔paper 50 (27), cards↔STATUS 58 (36) — **выросли** (T5 перенёс
журнал в карточки → больше имён в каноне, это не дублирование, а
покрытие; cards↔paper +23 — §4.x paper и cards реально пересеклись
после T5 clause-map). ≥3 docs из {STATUS, ALGO, paper, cards}: 60;
все 4: 15.

## A. Lean — что осталось

| # | Объект | Факт | Выгода | Риск |
| --- | --- | --- | --- | --- |
| L8 | AdapterGrowth карта секций (:59-77) | артефакт T3: `2. ** ** self-compressing…`, `** **` ×4 — удалённые C-метки оставили пустые bold; «маркеры `## C-bit:`» больше не существуют; «четыре macro-секции» vs список из 5 | −8 строк, 0 артефактов | 0 (комментарии) |
| L9 | MasterTheoremV3.lean:14-15 | `/-!` `/-!` подряд (T1 merge) | −1 строка | 0 |
| L10 | MasterTheorem.lean 688 | T8-«header dedup» сделал обёртки `## …(ns … preserved)`; остались 2-й/3-й copyright (:418 SafeStep, :469 GainDecomposition, :8 BlockLipschitz — pair), 3 module-docstring. Объединение с V3 симметрично: V3 импортирует AdapterGrowth/MiniHagiLoop/NegativeTransfer/GrowSnap/CoverageReading, MasterTheorem — Cert/Model/State/Step/Unified (Training ×3 импортирует MasterTheorem, V3 — никто). Разные слои-зависимости → НЕ сливать (honest-noop) | −12 (только copyright/`/-!`-повторы в 3 файлах) | 0 |
| L11 | **172 избыточных `namespace`-открытия в 40 файлах** (тот же ns открыт >1 раза: InfoCore 12, Freedman 8, MirrorHedge 7, SafeQP 6, GrowthBridge 5, EndpointContraction 5; по каталогам Step 21, Probability 17, Model 16, Math 12, Budget 12, Dynamics 11). Сигнатура merge-артефакта v4–v6: `end Ns` → `/-! ## X (ns … preserved) -/` → copyright → `/-! # X` → `namespace Ns` | −4…6 строк × ~120 (не все пары смежные) ≈ −500 | identity (R1), но между блоками могут стоять `open`/`section`/`variable` с областью до `end` — склейка меняет scope → каждый файл индивидуально; нужен merge_module.py-режим «join same-ns» (сейчас его нет — 725 строк, TestMergeModule 20 тестов) |
| L12 | docstring-остатки (grep по Hagi, только docstrings/комментарии): «Roadmap top-N / Дорожная карта» 24 строки / 20 файлов; `R5xx` review-метки 143 / 20; `A19`/`P5` 141 / 22; `waveNNN` 15 / 7; `THEORY_ALIGNMENT` 9 / 3; «цикл NNN» 98 / 40; C-метки 112 строк (было 1 973 — T3 снял 94%); `(the statement)`, «route 1», «previous session» — единичные (AdaptiveMajorizer :733-736 «Pin: tight… is future work» — а tight уже доказан в том же файле: **устаревшее утверждение**) | −~150 строк чистой воды; AdaptiveMajorizer :733 — фикс | 0 (DocLint) |
| L13 | `set_option linter.style.header false` | 267 файлов | это convention, не долг — не трогаем | — |
| L14 | Theory-файлы <40 строк | 4 (ParetoExecution 19, BatchCETrajectory 23, Pseudolikelihood 23, FiniteFamilyConfidenceEmpirical 29) — это umbrella-родители каталогов (`X.lean` + `X/`), не кандидаты | — | — |

Выборка 10 Theory-файлов (seed 7: AdaptiveMajorizer, AnytimeHoldoutStop,
BlockAdmission, CertCEHoldout, GaugeQuotient, HadamardIncoherence,
KnowledgeConsolidation, MiniHagiLoop, OnlinePL, SafeStep; комментарии
построчно в `.tmp/V7-AUDIT/theory10-comments.txt`, 1 426 строк):
воды нет по смыслу (honest pins несут ограничения теорем), но
остались: (a) «Roadmap top-N» преамбулы (5/10), (b) «R537/R538» в
заголовках docstrings GaugeQuotient, (c) `(the statement)` /
«(C435-паттерн…)» / «C390-pin» скобки, (d) AdaptiveMajorizer :733
устаревший pin. Verdict: T3 сделал главное; остаток — L12.

Не-кандидаты (подтверждено): Research/Legacy/Benchmarks (карантин),
External/, upstream/, Certificate-хабы, V2Bridges (HAGI_v2 sync
внешне не подтверждён), emit_*-генераторы bench (parity-gate).

## B. Docs

| # | Объект | Факт | Решение |
| --- | --- | --- | --- |
| D8 | README битые ссылки | `STATUS.md#hagiunifiedderivalonglean` (нет карточки — DerivAlong лежит в списке под `## Hagi/Unified/`), `Hagi/Prelude` ×2 (каталог удалён C348) | fix: якорь → `#hagiunified`, Prelude → `Hagi/Math` |
| D9 | paper C-метки | 301 строка / 401 метка (после T5); заголовки §4.1–4.7 несут `(C500)`, `(C495/C502)`, `(C560–C603)`…; abstract «Draft v0.8 (C629)», «С v0.7 (C617)», «index at HEAD e40aa426 (C559)» — журнал версий в abstract; Appendix A «verified at 2d619fc8 (+T5)» — устарел (HEAD ddaeb456) | заголовки без меток; abstract-журнал → одна строка «история: git log»; Appendix A pin → HEAD cycle-2. −~40 строк |
| D10 | STATUS C-метки | 32 заголовка `## <file> (C5xx: …)`; 191 строка / 239 меток; `## History (C538–C635)` (4 строки — уже только указатель, ок) | заголовки: тема вместо C-списка (`## Hagi/Theory/NegativeTransfer.lean (negative transfer, smooth, schedule, growth gate)`); C-метки из тел карточек — где ссылаются на period-файл (это адрес в .omc) — оставить |
| D11 | ALGORITHMS §24–26 | «Итоги фазы C263–C291 / C313–C317 / C324–C331» — 34 строки, событийные (D4 сказал «→ period или удалить», не сделано) | удалить (git log хранит); §27 канон остаётся |
| D12 | `.omc/analysis` period-* | 10 файлов 1 634 строки (c591–c633), tracked, событийные; перекрываются `git log` по one-liner'ам, но несут per-beat разбор, которого нет в commit-msg. `.tmp/`-ссылок 12 (мёртвые). | **решение user**: (i) оставить как есть (история), (ii) сжать в `era-index.md` ≤150 строк (по period: диапазон, freeze-дельта, 3 главных факта) и удалить исходники (git хранит), (iii) untrack (перенести в `.tmp/`). Рекомендация (ii): −1 480 строк, сохраняет навигацию. Honest: сжатие = пересказ → потери деталей (ACE-паттерн против) — поэтому только если user согласен |
| D13 | docs/PROPOSAL-* (6 файлов 772 строки) | исторические предложения (C466–C541), все реализованы или закрыты; 8 `.tmp/`-witness; PROPOSAL-index на них указывает; paper ссылается только на external-plan | не-цель (v7 вердикт стоит). PROPOSAL-index 21 строка — живой индекс |
| D14 | docs/PREMISES-STATUS 103, CONSOLIDATION-GAPS 36 | компактные, живые (paper ссылается) | не трогаем |
| D15 | PALOMAR-CARDS 508 | 23 C-метки (T5 чистил) — cards = внешняя формулировка «без C-меток» (D2) | добить: 23 → 0, −~5 строк |
| D16 | spec_manifest.toml (root, 53) | 0 потребителей (rg по tracked); сам файл: «historical R237 snapshot (not current SSOT)», числа 1639/966/1585 при Freeze 8849; последний коммит 5a2dccfc «annotate stale…» | Chesterton: это R237-record, intent — сохранить снапшот. Но он в root и не нужен ничему → удалить (git хранит) или перенести в `.omc/analysis/r237-spec-snapshot.toml`. Решение user |
| D17 | RELATED.md 50 | живой (LinkedProjects.lean:6 ссылается), 1 потребитель | не трогаем |
| D18 | ALGORITHMS `.tmp/` ×5, PROPOSAL ×8 | `.tmp/C216…C311` — мёртвые (cleanup c442e69) | ALGORITHMS: убрать пути, оставить «witness: git show <sha>»; PROPOSAL — с D13 |

Root-файлы из директивы: `hagi_neural_computer.py`,
`run_nc_3seeds.py`, `REPLACEMENT` — **не существуют и никогда не
были tracked** (`git log --diff-filter=D` пусто): в primes это
примеры, не факты. Chesterton-проверка неприменима.

## C. Scripts

| # | Объект | Факт | Решение |
| --- | --- | --- | --- |
| S5 | bench_bridge 14 634 | T6 helpers `_load_corpus/_phaseA_corpus/_phaseA_train/_finalize_traj/_write_text/_traj_steps`; `main` dispatch 40 режимов; `help=` literal 400 строк; 16 `.tmp/` (8 runtime, 8 witness-комментарии) | тот же вердикт v5-W5/S2: монолит = parity-gate. Wave help-dict — меняет CLI-help = поведение, honest-noop. Witness-комментарии → `git show` |
| S6 | lint-скрипты | `_shared.py` 96 строк; остались near-clones: `NS_RE` NsLint vs Metrics (Metrics через HAGI_MODULE), `IMPORT` ReachLint (`^\s*import`) vs Metrics `IMPORT_RE` (`^import`) — не байт-идентичны (T7 research) | honest-noop (YAGNI-гейт «вывод идентичен» не проходит) |
| S7 | scripts/*.lean 5 | AllAxiomCheck 73, GenTheoremIndex 100, NamePool 14, TrivialLint 465, inventory 174 — каждый = отдельный CI-гейт; GenTheoremIndex.py+lean (290) **0 потребителей** вне себя (paper: «индекс не генерировался с C559») | Chesterton: это generator paper-index; либо перегенерировать индекс (paper Appendix), либо честно пометить. Решение user |

## D. План cycle-2 (U1..U8) — 1 волна = 1 commit

Правила те же: Freeze identity (`python scripts/Freeze.py` PASS без
`--update`); Lean-код не меняется; каждый U-коммит → gates §E.

| Волна | Scope | Слой | Выгода | Риск |
| --- | --- | --- | --- | --- |
| U1 | L8+L9+L12-a: AdapterGrowth карта (убрать `** **`, переписать карту по фактическим 11 секциям), V3 `/-!`-pair, AdaptiveMajorizer :733 stale pin; README битые ссылки (D8) | Lean doc + README | −~15 строк, 0 артефактов, md-ссылки 351/351 | 0 |
| U2 | L12: docstring-вода Lean — «Roadmap top-N»/«Дорожная карта» 24, `R5xx` в заголовках, `waveNNN` 15, `THEORY_ALIGNMENT` 9, «(the statement)» | Lean doc | −~100 строк | DocLint; C-метки в docstrings, являющиеся адресом period-файла — оставить |
| U3 | D9+D10+D15: paper C-метки из заголовков + abstract-журнал + Appendix pin; STATUS заголовки по смыслу; cards 23 → 0 | docs | −~70 строк | StatusLint; paper anchors (anchors.py 151 → перегнать) |
| U4 | D11+D18: ALGORITHMS §24–26 удалить, `.tmp/` → `git show` | docs | −~40 строк | StatusLint |
| U5 | L10-copyright: 3 файла со 2-м copyright (SafeStep :418, GainDecomposition :469, BlockLipschitz :8) — убрать повтор + `/-! … preserved` обёртку | Lean doc | −12 строк, 3 файла чистых | 0 |
| U6 | L11 pilot: join same-ns в 5 файлах top (InfoCore 12, Freedman 8, MirrorHedge 7, SafeQP 6, GrowthBridge 5) через новый режим `merge_module.py --join-ns` + тест | Lean **+ script** | −~120 строк; при успехе → U6b ещё 35 файлов (−~380) | средний: scope `open`/`section`/`variable` между блоками — каждый файл A/B (build + Freeze + AllAxiom); 3 fail → STOP, honest-noop на остальные |
| U7 | bench witness-комментарии `.tmp/C5xx` ×8 → `git show <sha>` | scripts | −0 строк, 0 мёртвых якорей | 0 (комментарии; py_compile + golden) |
| U8 | reserved: D12/D16/D17/S7 — **решение user** (period → era-index; spec_manifest; GenTheoremIndex) | — | −1 480 / −53 / −290 | зависит от решения |

Ожидание cycle-2: −~350 строк гарантированно (U1–U5, U7), до −850 с
U6, до −2 600 с U8. Honest-граница: U6 — единственная волна с
реальным Lean-риском (не код, но структура файлов); всё остальное —
комментарии и docs.

## Честно НЕ трогаем

- Lean-код (statement/proof bodies) — ноль изменений, как в v7.
- MasterTheorem ↔ V3 слияние — разные импорт-слои, V3 никто не
  импортирует из Training; слияние бесполезно и меняет module-path.
- bench_bridge нарезка, emit_*-генераторы, help-dict.
- PROPOSAL-*, PREMISES-STATUS, CONSOLIDATION-GAPS, RELATED.md,
  UPSTREAM-SVD, `set_option linter.style.header false` (267 — convention).
- Research/Legacy/Benchmarks/External/, upstream/, Certificate-хабы,
  V2Bridges (HAGI_v2 sync не подтверждён).
- Числа-счётчики в README — не обновляем (Goodhart).

## E. Гейты волны cycle-2

1. `lake build` exit 0 (lean-4.36.0 первым в PATH; LAKE_JOBS=8).
2. `python scripts/Freeze.py` → PASS identity 8849.
3. `bash scripts/ci.sh` → CI: PASS (Lean-волны U1/U2/U5/U6).
4. anchors.py: file:line 0 битых; mdanchors.py: 0 битых.
5. U6: A/B `lake build` + Freeze + AllAxiomCheck на каждый файл.
6. Atomic commit `docs: refactor v7 cycle 2 (Un): <summary>`.
