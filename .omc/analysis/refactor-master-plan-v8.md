# Refactor Master Plan v8 — survey (V8-SURVEY, READ-ONLY)

Кредо директивы v8: минимум кода — максимум смысла (то же для
docs/докстрингов/комментариев); чистая универсальная система;
объединить нужное, изолировать ложное. Base: HEAD 3ba95ac3, tree
clean. Freeze: `python scripts/Freeze.py` (lean-4.36.0 на PATH) →
`PASS (9043 declarations, 0 aliased, nothing lost/changed)` (35 s,
`.tmp/V8-SURVEY/freeze.log`). Precedents: v7 (T1–T8), cycle 2 (U6–U9),
cycle 3 — читаны; их honest-границы (bench-монолит, period-файлы и
PROPOSAL — «решение user», Research/Legacy карантин) здесь
пере-оценены по новым фактам, а не повторены.

Директива «Freeze первым» выполнена доsurvey-чисел: 9043 —
опорное число; всякое другое число freeze в docs (кроме журнала
дельт) — кандидат в «ложное».

## 0. Sizes (tracked, `git ls-files | xargs wc -l`): 240 555 строк / 634 файлов

| Слой | 0b28a7a7 (конец v7-c2) | HEAD | Δ |
| --- | ---: | ---: | ---: |
| STATUS.md | 2 059 (после T5) | 3 316 | +1 257 — журнал вернулся |
| ALGORITHMS.md | 3 423 | 3 339 | −84 |
| README.md | 230 | 216 | −14 |
| docs/*.md | 3 014 | 4 206 | +1 192 (paper +777, cards +204, PROPOSAL +337) |
| Hagi/Theory | 19 562 | 27 591 | +8 029 (10 новых/растущих файлов) |
| scripts/bench_bridge.py | 14 634 | 14 968 | +334 |
| .omc/analysis | 1 782 | 2 456 | +674 (7 period-файлов) |
| **весь diff 0b28a7a7..HEAD** | | | +7 545 / −60, 32 файла |

Монолиты: bench_bridge 14 968 · ALGORITHMS 3 339 · STATUS 3 316 ·
Freedman 4 490 · paper 1 984 · BatchCEGrowth 2 920 · NadyaOptimal
1 222 · AdaptiveMajorizer 1 539 · FunctionPreservingGrowth (FPG) 996.

Базовые линты docs-слоя (read-only): StatusLint/DocLint/NsLint/
DupLint/StatementDupCheck/LayerLint/ReachLint — **не запускались**
(требуют `lake env`; survey — только Freeze). Первый шаг X1 —
прогнать и зафиксировать baseline.

## 1. ИЗОЛЯЦИЯ ЛОЖНОГО — таблица (26 строк)

Метод: `rg` по `lm|unified|selfmodel|archiver\.py:N(-M)(@sha)?` в
STATUS/paper/cards/ALGORITHMS/README/Hagi; сверка с `git -C
C:/HAGI_v2 show HEAD:<path> | sed -n Np`. HAGI_v2 HEAD = f5b7b50
(wave262); pinned sha в primes: ca52eb4 (48 упом., 9 коммитов позади
HEAD), b3740e0 (23, 7 позади), bab8aff (10, 6), 1ae924e (8, 10),
e9a96fc (7, 8). Drift ca52eb4→HEAD: lm.py +100/−50, unified.py
+303/−53, archiver.py новый, selfmodel.py 0.

Вердикт по якорям (важно, против гипотезы задачи): **все**
проверенные `file:line` либо pinned `@sha`, либо совпадают с HEAD
HAGI_v2 (spot-check 46 якорей: строка-начало диапазона содержит
заявленный def/комментар). «lm.py:826→:831» — не сдвиг, а два
разных якоря: 826 = def `_certified_finite_step` (C643, pin
@ca52eb4), 831 = blank перед `_rope_logits_from_params` (C646) —
второй лишён смысла (пустая строка). Ложное — не сдвиг строк, а
**устаревшие статусы и числа**:

| # | path:line | Что ложно | Исправление |
| --- | --- | --- | --- |
| F1 | STATUS.md:2887–2939 (C657) | Honest pin (1) «связь `a<0` с C655 … НЕ формализована» — закрыт C663 (линейный носитель) и C665 (нелинейный); pin (2) «линейность по η — гипотеза» — снят C665 на уровне дифференциала | заменить pins на «закрыто C663/C65; остаток: certified-величина drop для нелинейного (C665 (1))» — 1 строка вместо 7 |
| F2 | STATUS.md:3211–3245 (C663) | «Нелинейный носитель — открыт, нужен HasFDerivAt» — закрыт C665 | «закрыто C665 (строгое убывание для малого η)» |
| F3 | STATUS.md:3097–3155 (C665) | Honest (2) «производная по W1 …» — проверить vs C667/C666; если не закрыт — оставить, это единственный живой pin | статус-аудит в X1 |
| F4 | STATUS.md:2844–2885 (C655) | «⟨g,d⟩ ≥ 0 — код-факт только на первом шаге» — после C663 это теорема (`chain_linear`) для линейного носителя | сослаться на C663 FQN, убрать «только код-факт» |
| F5 | STATUS.md:2139,2214,2285,2336,2387,2436,2472,2526 | «17 гейтов PASS» ×8 + «Freeze N→M» ×26 — счётчики-события (Goodhart), не свойство файла | удалить (журнал → era-index; −~60 строк) |
| F6 | STATUS.md:41 ×`.tmp/` | `.tmp/*` в .gitignore — мёртвые якоря (C657/traj.log, gates.log, …) | удалить; witness, где несёт смысл, → `git show <sha>` |
| F7 | docs/paper-draft.md:4,22,49,1182,1578,1818,1977 | «freeze 8967 at the C664 HEAD» ×7 — сейчас 9043; в paper 3.21 описаны мосты C651–C657, которых нет в §0-карте | одно число (убрать из 7 мест), §0-карта дополнить C660–C667 либо §3.21 → дельта к §3.20 |
| F8 | docs/paper-draft.md §3.18 → §3.20 | заголовок §3.19 отсутствует (нумерация 3.18 → 3.20) | перенумеровать (C648-эра удалила §3.19?) |
| F9 | README.md:91 | «Hagi/Theory: 49 файлов» — факт 52 | убрать счётчик (v7 D3 уже требовал) |
| F10 | docs/PALOMAR-CARDS.md:1,15 | «C5XX-теория», «семнадцати результатов C5XX-витков» — Cards 15–17 = C657/C653-эры (C6XX) | «C5XX–C6XX» |
| F11 | .omc/analysis/era-index.md:1,249 | «C591–C664»; последняя эра C662–C664 (freeze 8967) — нет C665–C667 (9043) | дописать эру C665–C667 (3 строки) |
| F12 | .omc/analysis/era-index.md:4–5 | «Per-beat разбор удалённых period-*-analysis.md» — 7 period-файлов снова tracked (691 строк) | удалить period-файлы (утверждение станет истинным) — DECISION D2 |
| F13 | STATUS.md:2480 | якорь `lm.py:831` — пустая строка в HAGI_v2 HEAD | `lm.py:832` (`_rope_logits_from_params`) |
| F14 | STATUS.md:1260 (paper) `lm.py:349`, STATUS:2850 | якорь на пустую строку | уточнить до 348/350 по смыслу |
| F15 | STATUS.md:2395–2397 (C643) | «`:793` в задаче — не строка def» — спор с постановкой задачи, не свойство файла | удалить 2 строки |
| F16 | STATUS.md:3004 | «Freeze: 9043 = 9003 + 40» — число-событие; после X-волн устареет | в era-index (1 строка) |
| F17 | STATUS.md:2069–2075 | «History (C538–C635)» указывает на `git show b3939aa5`, но за ним снова 1 248 строк журнала C638–C667 | сам заголовок истинен, тело — нет → X2 |
| F18 | ALGORITHMS.md:3321 | «лестница v3→v3.4: 5/8/10/11/14 клозов» — согласуется с Lean (5 ns), истинно; v31–v33 внутри файла потребляются лестницей (v34→v33) | оставить (D1 = noop) |
| F19 | STATUS.md:58,141,268,279,392,408,765,807 … `## Hagi/<Dir>/` ×≥15 дублей заголовков | одна директория — несколько секций вразброс (Model ×13) | объединить в X2 (canonical by dir → by file) |
| F20 | Hagi/Theory/FPG:269,383,473,562,697,789 — section-заголовки «(C642)…(C665)» | событийные метки в заголовках (v7 L5-класс) | смысловые заголовки, C-метку — в конец docstring |
| F21 | lakefile.toml:4 | `defaultTargets` включает `Hagi.Research` — карантин собирается по умолчанию, README:147 говорит «карантин: код не трогаем» | DECISION D3: исключить из defaultTargets (CLAUDE-гейт ci.sh?) |
| F22 | STATUS.md:1993 | «C551–C635: режимы без Lean-ряда» — после C654 (certified-warmup-sim) заголовок устарел | «C551–C654» |
| F23 | scripts/bench_bridge.py: +`cw_softmax`,`cw_ce`,`finite_displacement_ce_upper` | дубли lse/CE-хелперов Phase-A (T6 выделял `_phaseA_corpus`) | X5: переиспользовать существующие (golden-diff) |
| F24 | docs/PROPOSAL-certified-warmup.md (204) + PROPOSAL-holdout-size.md (133) | предложения уже формализованы (C657/C660/C663/C665) — статус «proposal» ложен | пометить `status: implemented (Cxxx)` шапкой, DECISION D4 |
| F25 | STATUS.md:2941–3008 (C667) + 3009–3096 (C666) | C667 — width-рост описан и в C666-карте (строки 10 идей) — двойное изложение | одна карточка по файлу NadyaOptimal, C667 — подпункт WidthGrowth |
| F26 | STATUS.md:2577–2701 (C651) | «bridges: repair forgetting и window order» — window order затем переделан bab8aff (wave258b, C664 «exact для порядка»); C651-версия — historical | пометить «superseded by C664» |

Класс (d) Research/Legacy карантин: помечен честно (README:147,
lakefile globs `Hagi.Research`), кроме F21 (default target).

Honest-проверка классификации: якоря HAGI_v2 — в основном
истинны; главный источник «ложного» — **устаревшие статусы**
(F1–F4, F24, F26) и **счётчики** (F5, F7, F9, F10, F16).

## 2. ОБЪЕДИНЕНИЕ НУЖНОГО — топ-5

| # | Объект | Факт (числа) | Решение | Выгода |
| --- | --- | --- | --- | --- |
| M1 | STATUS.md журнал 2060–3316 | 1 248 строк, 19 `## Cxxx`-заголовков, не по файлу; freeze-дельты ×26, `.tmp` ×41, C-метки 308 всего | канон-карточки по файлу (11 файлов: NadyaOptimal, FPG, AdaptiveMajorizer, CoverageReading, BatchCEDescentMgdaCode, BatchGlobalTelescope, RepairForgetting, ArchiverCodeLength, AdamDirection, HoldoutGateTwoWay, RollbackGate) + C654 → секция bench; era-index — 1 строка/эру | −800…−1 000 строк STATUS |
| M2 | MasterTheoremV3.lean 449 (v3, v31–v34 = 5 ns) | внешних потребителей v31–v33: **0** (RepairForgetting/BatchGlobalTelescope берут `master_theorem_v3`); но внутренняя цепочка v34→v33→v32→v31 (:434/:328/:253) — v34 доказан делегированием | honest-noop: это лестница доказательства, не дубль; сжимать только docstring-карты клозов (X6) | −~40 docstring |
| M3 | «Два вида роста»: FPG 996 (Depth-рост + WarmUp C642–C665) + Nadya WidthGrowth (Nadya:217–1056, 840 строк) | DAG: FPG imports LMCompose, BlockAdmission, RollbackGate, AdamDirection, BlockLipschitz; Nadya imports TritCodec, ExactBypass, ArchiverCodeLength, Statistics; общий граф ацикличен; в `Hagi/Growth/` 16 файлов, ни один не импортирует FPG/Nadya | **не объединять** в Growth.lean (1736-строчный монолит, 2 разных носителя: CertifiedBlock vs WParams) — вместо: Nadya WidthGrowth (840) → отдельный модуль `Hagi/Theory/WidthGrowth.lean`, Nadya → 380 строк (BitAlloc/Schedules/LCB/Bypass); consumer-check: 0 импортеров Nadya кроме Hagi.lean | 0 строк, −1 тема-мешок; рисков мало |
| M4 | paper §0 карта (45–122, 28 строк таблицы) + §3.20 (926–1176, 251) + §3.21 (1177–1324, 148) + §4.8 (1574–1611, 10 строк) | якоря пересекаются: §0∩§3.20 = 6, §0∩§4.8 = 8 из 10, §3.20∩§4.8 = 6, §3.21∩§4.8 = 1 | одна карта в §0 (полная: C638–C667), §3.20/3.21 → дельты-нарратив (−~150), §4.8 удалить (−38) | −~200 paper |
| M5 | era-index (265) vs 7 period-файлов (691) | era-index уже заявляет period «удалёнными»; era-index не покрывает C665–C667 | период-файлы удалить, era-index +3 эры; era-index C648-секция (173–184) дубль эры C646–C648 (185–198) | −691, −12 |

Non-цели (Chesterton, подтверждено): bench-монолит (14 968, 20+ режимов parity-gate); V2Bridges; External/upstream; PROPOSAL-* как исторические (кроме F24); Freedman 4 490 / BatchCEGrowth 2 920 — вне Theory-фокуса v8.

- Lean docstrings: Nadya 196 docblock-строк (16%) — **не вода**: каждый привязан к строке Надя.txt; FPG 380 (38%), AdaptiveMajorizer 277 (18%), CoverageReading 230 (30%), NegativeTransfer 262 (38%) — кандидаты на сжатие только событийные заголовки (F20) и дубли карт клозов |
- Nadya gap 286 = `structure WParams` с docstring на поле — это смысл, не вода.
- Nadya «вода» — опровергнуто: 66 decl на 1 222 строк (5,4/100), docblock 196 строк (16%), каждый pinned к строке Надя.txt.

## 3. План-волновка v8 (X1..X9) — 1 волна = 1 коммит

Freeze-правило: identity = `python scripts/Freeze.py` PASS без
`--update` (9043; lock ключует по FQN + statement-hash, R1 из v7).
CHANGED только в D1 (если решено) — отдельным коммитом, `--update`, `bake:` в
сообщении. Перенос ns-блока в другой файл — `scripts/merge_module.py`.

| Волна | Scope | Freeze | Выгода | Риск |
| --- | --- | --- | --- | --- |
| X1 | Ложное, docs-only: F1–F4 (статусы honest-карточек), F5–F7, F9–F11, F13–F16, F22, F26 | identity | −~120; 0 ложных статусов | низкий |
| X2 | STATUS 2060–3316 → карточки по файлу (M1), F19, F25 | identity | −800…−1 000 | средний: StatusLint baseline до/после |
| X3 | Удалить 7 period-файлов, era-index +C665–C667, −дубль C648 (M5); PROPOSAL-status (F24) | identity | −~690 | низкий: сначала `rg period-c6` (ссылки) |
| X4 | paper: §0 полная карта, §3.20/3.21 → дельты, §4.8 удалить, §3.19 (M4, F8); README F9; cards F10; ALGORITHMS §27 | identity | −~200 paper | низкий |
| X5 | Nadya WidthGrowth (217–1056, 840) → `Hagi/Theory/WidthGrowth.lean`, ns сохранён (M3) | identity | 0 строк; 2 темы в 2 файлах | низкий: 0 импортеров кроме Hagi.lean; lake build + ci.sh |
| X6 | Lean docstrings: F20 + C-метки в заголовках 12 файлов; карты клозов v3 → одна + дельты | identity | −~60 | низкий: DocLint |
| X7 | D1: v31–v33 → только если переписывать proof v34 | **CHANGED** | −~175 Lean | высокий: v34 доказан через v33 (:434) |
| X8 | bench: `cw_*` → существующие lse/CE-хелперы (F23) | python | −~20 | средний: golden-diff warmup-sim |
| X9 | D3: `Hagi.Research` из defaultTargets | config | 0; карантин вне дефолта | средний: ci.sh +1 строка |

Прогноз итога (D1 = noop): −1 900…−2 100 строк.
Порядок X1→X4 — «сначала ложное, потом объединение»: X2/X4
опираются на истинные статусы из X1. X5/X6 — Lean-identity волны; X7 — CHANGED,
по умолчанию не выполняется (D1 = noop).

Гейты волны: `lake build` exit 0 (Lean-волны) → Freeze →
StatusLint/DocLint/NsLint/DupLint/StatementDupCheck/LayerLint →
`bash scripts/ci.sh` (конец Lean-волн) → golden-diff (X8). 3 fail →
STOP, откат, запись в план. Коммит `refactor(v8 Xn): <summary>`.

## 4. DECISION-пункты (оркестратору)

- **D1 — v31–v33 удалить?** Факты: внешних потребителей 0; docs ~15
  упоминаний; v33 = v34 без клозов 12–14 (проекции `have hV33` в
  v34 — **факт: потребляет.** `hagi_master_v34` доказан через
  `have hV33 := …MasterTheoremV33.hagi_master_v33` (V3.lean:434),
  v33 — через v32 (:328), v32 — через v31 (:253). Удаление любого
  звена ломает доказательство следующего ⇒ нужна переписка proof
  body v34 (не перенос), −196 строк lock-записей → CHANGED.
  Рекомендация: **honest-noop** (лестница = структура доказательства,
  не дублирование); X7 отменяется, если D1 = noop.
- **D2 — period-файлы (691):** удалять в X3 (era-index это уже
  заявляет). В v7 было «решение user» — теперь era-index сам
  объявляет их удалёнными, противоречие надо снять.
- **D3 — Research в defaultTargets:** карантин собирается по
  умолчанию (lakefile:4), README:147 называет его карантином.
  Исключить только с явным `lake build Hagi.Research` в ci.sh,
  иначе Research выпадет из CI (Chesterton: globs C240 — целевой
  паттерн). Решение — оркестратор.
- **D4 — PROPOSAL-certified-warmup / holdout-size:** реализованы
  (C657/C660/C663/C665); пометить `implemented` или удалить.
  Рекомендация: пометить (история предложений — смысл).
- **D5 — F3 (C665 pin (2), W1-производная):** статус не проверен
  против C666/C667 — аудит в X1, не факт.
