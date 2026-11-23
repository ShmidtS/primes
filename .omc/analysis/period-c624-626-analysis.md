# Phase analysis: C624–C626 — чтение-эра закрыта: Card 13, bench cost-regime (2026-11-23)

Series HEAD 7d7ff186e4331cf8533dd973458b865cec760f4a (C626; `git log`
проверен: d3e0da84 C624 → c8715f3b C625 → 7d7ff186 C626; tree clean).
Виток C627 — docs-виток фазового анализа (прецедент C599/C603/C612/
C616/C620/C624): READ-ONLY, один docs-commit. Серия C624–C626 =
аналитический виток, закрывающий теорию чтения (C624) + внешний рычаг
(Card 13) + первый bench-виток, где теория меняет поведение (cost-regime).
Freeze 8841 на всей серии (identity: C625 docs-only, C626 не трогал
Lean-дерево — FREEZE: PASS identity по receipt C626). Roadmap C624
top-3 приземлены: top-1 (Card 13) и top-2 (bench --cost-regime) —
за один виток каждое; top-3 (paper v0.8 vs внешний push) — остаётся
user-шагом по определению (publication gate).

## Commit one-liners (C624–C626)

- C624 d3e0da84 `docs: phase analysis c620-c623 reading theory` —
  160 строк: фазовый анализ C620–C623; closed-цикл чтения из 4
  вопросов (покрытие → иерархия → оптимум → ширина); метрики;
  HAGI_v2 recheck (wave241 без изменений); roadmap ≥5, top-3:
  Card 13, bench --cost-regime, paper-решение. READ-ONLY, freeze
  identity 8841.
- C625 c8715f3b `docs: palomar card 13 near const window cost` —
  docs/PALOMAR-CARDS.md (+50) + README (+2/−2... фактически 2 файла,
  +50/−2): Card 13 «Linear window cost makes total budget nearly
  width-independent» по канону Cards 1–12. Statement — Lean-дословно
  `windowCost_linear_near_const` (побайтовая diff-сверка против
  WindowTradeoff.lean), опорные якоря :55/:77/:86/:102/:113
  rg-верифицированы; числа из receipt C623; w*-формула режима (c)
  честно помечена как STATUS-набросок, не Lean-клоз. Boy Scout:
  рассинхрон header-счётчика «одиннадцати»→«тринадцати» исправлен.
  DocLint PASS (556 files). Freeze identity 8841.
- C626 7d7ff186 `feat: bench cost regime w rule` — bench_bridge.py
  (+171) + StatusLint.py (+1) + STATUS.md (+30): `cost_regime_w`
  — python-двойник теорем WindowTradeoff с fail-closed asserts
  (коридор linear, near-const неравенство, оптимальность fixed
  w_max, argmin mixed); CLI `--cost-regime {fixed,linear,mixed}` +
  `--cw-a/--cw-c/--cw-alpha/--cw-wmax` в режиме generate-hier
  (обратная совместимость без флага); witness-сверка с Lean #eval
  C623 дословная (6250/1563/391 чтения; 100000/100032/100096
  linear-cost); mixed w* честно помечен не-теоремой в docstring/
  rule/STATUS. Гейты 17/17, pytest 43, freeze identity 8841.

## (а) Чтение-эра закрыта: теория → карточки → bench синхронны

Серия C624–C626 закрыла эру чтения как полный цикл из трёх
синхронных поверхностей:

1. **Теория (C618–C623)** — certified: покрытие (iff), иерархия
   (total = ⌈n/w⌉ не зависит от B), floor (Card 12 + клоз 11 v3.3),
   ширина (3 режима + near-const + w*-набросок). Анализ C624
   зафиксировал: внутри модели totalCost(w) = ⌈n/w⌉·c(w)
   структурных вопросов не осталось.
2. **Внешние карточки (C621, C625)** — Card 12 (floor) и Card 13
   (near-const): statement дословно из Lean, якоря rg, числа из
   receipt'ов. Реестр 13 карточек; единственный не-теоремный
   элемент во всём реестре — w*-формула режима (c) — честно
   помечен в Card 13 как STATUS-набросок.
3. **Bench (C626)** — теория впервые изменила bench-поведение, а
   не только freeze: выбор w по правилу режима (fixed → w_max
   certified; linear → свободно + коридор certified; mixed →
   телеметрия по Real-наброску с честной пометкой). Witness-сверка
   Lean #eval ↔ python assert — дословная.

Итог: три поверхности (Lean, карточки, bench) несут ОДНО и ТО ЖЕ
содержание без дрейфа — statement'ы копируются побайтово, числа
берутся из receipt'ов, не-теоремные элементы одинаково помечены
везде. Честность серии консервативна: единственный серый элемент
(w*) виден во всех трёх поверхностях с одинаковой пометкой.

## (б) Метрики серии

| Метрика | C623 | C624 | C625 | C626 |
|---|---|---|---|---|
| Freeze | 8841 | 8841 | 8841 | **8841 (identity)** |
| Δ freeze | +5 | 0 | 0 | 0 |
| Тип | feat | docs | docs | feat (scripts) |
| Streak | 173 | 174 | 175 | 176 |
| Гейты | 17/17 | RO | Doc+Freeze | 17/17 + pytest 43 |

- Freeze 8841 стабилен всю серию: C626 — feat без Lean-дерева
  (python-двойник теорем, не новый Lean-код). Growth-витков не
  было — серия «внешний рычаг + применение», не расширение канона.
- Гейты 17/17 на C626 (полный прогон, включая MachineDiff 2000
  конфигов / 1923 certified); pytest-батарея C626 = 43 (против 63
  в C622/C623 по receipt'ам — разные выборки батареи, фиксируется
  по receipt C626, не пересчитывалась).
- Streak 176 → C627 (docs) → 177 по механике +1/виток.
- Roadmap-execution: top-3 C624 приземлены 2/3 немедленно;
  top-3 (paper) — осознанно user-шаг; четвёртый виток подряд
  с полным приземлением исполняемой части top-3.

## (в) HAGI_v2 recheck — волны после 241

Прямой аудит C:/HAGI_v2 на момент C627 (git log + status):

- HEAD 41b6e89 wave241 — БЕЗ ИЗМЕНЕНИЙ с C620 (тот же коммит:
  self-critique from accepted laws; a04dc37 P0 target-leak fix;
  ce68e21 wave240). Дерево чистое, волн 242+ нет.
- invention_multi.py по-прежнему отсутствует как файл (импорт-
  ссылка `from hagi.invention_multi import invent_multi` в
  pipeline.py:199 — вывод C612/C616/C620/C624 в силе).
- Влияние на серию: none — freeze 8841 не затронут; серия
  corpus-free. Corpus-live срезы не нужны (нет нового
  certified-критерия; снапшот-политика C608 — единственный якорь,
  YAGNI).

## (г) Roadmap ≥5 к цели «max качество, min объём, min вычисления»

1. **Certified rank / adapter-ёмкость — когда расти** (theory,
   med-high): теория чтения закрыта; следующий структурный
   фронт — из честных остатков premise_registry (C619). Правило
   роста по аналогии с transfer-гейтом: рост (√n-ранг?)
   оправдан iff certified-выигрыш, а не ожидание ёмкости.
   Кандидат на первый Lean-виток новой эры.
2. **Paper v0.8** (docs/user, med): v0.7 не знает Card 13,
   v3.3-канон, w-режимы, bench cost-regime. §3.19 v3.3 + §4.8
   floor/w-режимы + bench-ссылка; либо внешний push v0.7 как
   есть. Publication gate — user-шаг; подготовка черновика
   v0.8 — agent-шаг.
3. **mixed-w* в Lean — догнать честность** (theory, med):
   w* = (a/(c·(α−1)))^(1/α) — единственный элемент серии,
   помеченный не-теоремой. Теорема о внутреннем оптимуме при
   c(w) = a + c·w^α (Real/NNReal-арифметика, минимум totalCost)
   закроет последний серый элемент; python-argmin C626 станет
   certified-обоснованным. Мотивация — честность, не рост freeze.
4. **PALOMAR-ниша recheck** (docs, low): с Card 13 реестр = 13
   карточек; recheck появившихся пересечений (появился ли
   comparator по reading-window cost) перед paper-решением.
   Дёшево, снижает риск publication-gate.
5. **New frontier: memory-consolidation certified** (theory,
   high): волны 225+ C584 — что осталось неформализованным в
   консолидации памяти; карта неформализованного — вход для
   следующей эры после rank/adapter.

Top-3 на следующий виток: (1) paper v0.8 подготовка (накопленные
Cards 12–13 + v3.3 + w-rule готовы к тексту; единственный рычаг,
закрывающий эру внешне), (2) mixed-w* в Lean (закрыть последний
не-теоремный элемент серии — честность реестра 13 карточек),
(3) PALOMAR-ниша recheck (дешёвый риск-редьюсер перед
publication gate).

## Honest limits (процедурные)

- READ-ONLY виток C627: lake не запускался; freeze 8841 /
  гейты 17/17 — по receipt'ам .tmp/C624–C626 (прецедент
  docs-витков C599/C603/C612/C616/C620/C624).
- Аудит HAGI_v2 (§в) — по git log/status; deep-чтение диффов
  wave240/241 не выполнялось; вывод опирается на неизменность
  HEAD с C620.
- Числа (6250/1563/391; 100000/100032/100096; freeze 8841;
  pytest 43; DocLint 556) — цитаты receipt'ов C624–C626, не
  перевычисление.
- mixed w* — Real-набросок STATUS.md C623; в C626 используется
  как телеметрия (Fraction-argmin по окрестности корня), не
  глобальный certified-выбор.
- Streak 177 для C627 — по механике +1/виток (docs-витки —
  посадки, прецедент C580/C583/C594/C599/C603/C612/C616/C620/
  C624).
