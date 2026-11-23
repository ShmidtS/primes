# Phase analysis: C612–C615 — v3.2-канон: применение иерархии, метатеория 10 клозов, карточки (2026-11-23)

Series HEAD dff310527ee5bcd0bd3b2b9939d832bee4992df9 (C615; `git log`
проверен: d1bea6a2 C612 → 819ae31f C613 → 609726d1 C614 → dff31052
C615; tree clean). Виток C616 — docs-виток фазового анализа
(прецедент C599/C603/C612): READ-ONLY, один docs-commit. Серия
C612–C615 = один analysis-виток + одно применение (generate-hier)
+ одна метатеория (v3.2) + один docs-виток (карточки). Freeze
8822 → **8823** (только C614: +hagi_master_v32; C612/C613/C615
identity). Все три «применения» C612-roadmap top-3 (Card 9–11,
generate-hier, v3.2) приземлены за один виток каждое — без
переносов и откатов.

## Commit one-liners (C612–C615)

- C612 d1bea6a2 `docs: phase analysis c606-c611 formula era` —
  188 строк: commit-обзор C606–C611, метрики (freeze 8814→8822,
  streak 156–161), corpus-политика как переносимый паттерн,
  HAGI_v2 recheck (wave239, invention_multi.py приземлён),
  roadmap ≥5 + top-3. READ-ONLY, lake не запускался. Freeze
  identity 8822.
- C613 819ae31f `feat: generate hier bench mode` — bench_bridge.py
  (+141/−1): `hier_span(n, w=64, m=64)` — python-двойник hierStarts
  (B = w(m−1) = 4032, s = w, re-use `_cov_step_starts`), режим
  `--mode generate-hier` (corpus-free) с честным verdict adaptive-
  span рядом. Свежий Lean #eval (HierEval.lean, rc=0): n=8128 →
  3 блока / [63,63,1] / peak 63 — python-числа совпадают с Lean
  дословно. Таблица до n=100000: 25 блоков, 24×63+51, total 1563,
  peak 63 (adaptive-span = INFEASIBLE — контраст прочитан). 17
  гейтов PASS, freeze identity 8822, pytest 43.
- C614 609726d1 `feat: master theorem v32` —
  Hagi/Theory/MasterTheoremV32.lean (+99): `hagi_master_v32` —
  10 клозов: (1)–(8) развёртка v3.1 в statement + делегат одним
  `have hV31`; (9) `nlDrop (1/L) L G = G²/(2L)` ← nl_drop_optimal
  (C606); (10) hier-покрытие любого n ← hier_covers_any_n (C611).
  Ноль новых доказательств, ноль новых гипотез сверх v31+hier.
  Найдено отладкой: «делегат целиком как применение теоремы в
  statement» — ill-typed (proof term ≠ Prop); корректно —
  развёртка клозов в statement, делегат в proof. Freeze
  8822→8823. Axioms = 3 (propext, Classical.choice, Quot.sound).
  Witness trajMT32.lean: применения (9) L=2,G=1 → drop 1/4 и (10)
  n=8128. pytest-батарея выросла 43→63.
- C615 dff31052 `docs: palomar cards 9-11` — docs/PALOMAR-CARDS.md
  (+95): Card 9 (γ*=1/L perfect-square gap), Card 10 (hier
  coverage any n, peak ≤ m), Card 11 (adaptive-span iff: s ≤ w
  необходимость + бюджет (n−w)/s+2 ≤ m + граница n ≤ 4032, снятая
  Card 10). Statements Lean-дословно, якоря file:line
  верифицированы rg; индексы «восьми» → «одиннадцати» в README +
  intro. Freeze identity 8823.

## (а) v3.2-канон: машина (8) + шаг + чтение; применения синхронны

Главный итог серии — канон hagi_master_v32 как единственная
точка входа в результаты проекта:

- **Структура 10 клозов** = 8 «машинных» клозов v3.1 (C600) +
  клоз-шаг (9, γ*=1/L) + клоз-чтение (10, покрытие любого n).
  Симметрия: по одному клозу на каждую формулу-эру C606/C611 —
  метатеория догнала теорию без новой поверхности.
- **Применения синхронны**: расстояние «теорема → bench-режим»
  ≤2 бита после v3.2 — generate-hier (C613) потребовал только
  hier_span-двойник + re-use `_cov_step_starts`; режимы
  (auto-LR C609, generate-hier C613) читают certified-формулы
  напрямую. Паттерн «теорема → режим» (прецедент C609) теперь
  дважды подтверждён.
- **Честность состава**: ноль новых доказательств в v3.2 (только
  делегаты), ноль новых гипотез, AllAxiomCheck = 3 — консолидация
  не добавила поверхности (max качество / min объём).
- **Двойники с дословной сверкой**: python hier_span проверен
  pinned-assert'ом против Lean #eval ([63,63,1]/63) — паттерн
  «двойник + pinned Lean-число» закреплён как стандарт для
  будущих bench-режимов.

## (б) Метрики серии

| Метрика | C611 | C612 | C613 | C614 | C615 |
|---|---|---|---|---|---|
| Freeze | 8822 | 8822 | 8822 | **8823** | 8823 |
| Δ freeze | +4 | 0 | 0 | +1 | 0 |
| Тип | feat | docs | feat | feat | docs |
| Streak | 161 | 162 | 163 | 164 | 165 |
| Гейты | 17/17 | n/a (RO) | 17/17 | 17/17 | Doc+Freeze+git |

- Freeze за серию: +1 (только hagi_master_v32); ноль новых
  аксиом. Выражение «freeze растёт только на консолидацию» —
  серия-минимум с C591.
- Гейты 17/17 на каждый Lean-виток (MachineDiff 2000 configs,
  StatementDup 0 groups, AssumptionScan без дрейфа).
- pytest-батарея: 43 → 63 passed (C613→C614) — рост на режимах.
- Streak 162→165; C616 (docs) → 166 по механике +1/виток.
- Roadmap-execution: top-3 C612 приземлены 3/3 (Card 9–11,
  generate-hier, v3.2) — впервые все top-3 за одну серию.

## (в) HAGI_v2 recheck — волны после 239

Прямой аудит C:/HAGI_v2 на момент C616 (git log + status):

- **HEAD ce68e21 wave240** (`feat(wave240): self-critique loop +
  mega law library (user directive)`) — после wave239 волна
  self-critique + mega law library (scripts/self_critique.py,
  seed_laws_mega.py). Дерево HAGI_v2 чистое.
- **Движущаяся мишень вернулась**: wave240 добавляет mega law
  library — корпус снова меняется по user-directive. Снапшот-
  политика C608 остаётся единственным якорем детерминизма;
  вычислять новые срезы corpus-live по wave240 не нужно, пока
  нет нового certified-критерия (YAGNI: snapshot регенерируется
  one-liner'ом по требованию).
- **invention_multi.py по-прежнему отсутствует** — вывод C612
  в силе.
- Влияние на серию: none — freeze 8823 не затронут; wave240-контент
  не входит в снапшот C608 и не читается bench-режимами серии
  (generate-hier corpus-free, v3.2 — чистая теория).

## (г) PALOMAR upstream: ничего из нашего не поглощено

Прямой fetch (C616, сохранено .tmp/C616/palomar_*.json):
статический HTML требует JS, но llms.txt раскрывает machine-API
`https://data.palomar-registry.org/api/v1/results` (CC0, CORS \*).
Запросы по нашим именам и темам:

- `hier_covers`, `covStartsStep`, `nlDrop`, `adaptive span`,
  `optimal step size`, `window coverage hierarchy` — **0 записей**
  каждая.
- Реестр: 1293 results / 983 projects; последние регистрации
  (2026-11-22) — комбинаторика/базы Шаудера/экспандеры: наша
  ниша (certified-ML-механика: оптимальный шаг, покрытие окон)
  там не представлена.

Вывод: карточки 9–11 не поглощены upstream; более того, прямых
аналогов по именам/темам в реестре нет — Cards 9–11 остаются
единственной формализацией этих утверждений. Отправка в PALOMAR —
user-шаг (CONTRIBUTING на github.com/PalomarRegistry/PalomarPolicy);
техническая готовность полная (statements Lean-дословно, якоря
file:line, pinned Mathlib fc4f59e5).

## (д) Roadmap ≥5 к цели «max качество, min объём, min вычисления»

1. **Оптимальный rank / adapter-ёмкость certified** (theory→feat,
   high): когда добавлять adapter? Аналогия transfer-гейта (C601):
   certified-порог ёмкости по следу H̄ — кандидат на замену
   measured-эвристики выбора ранга. Сначала map: какие
   существующие клозы v3.2 связывают rank и certified bound.
2. **Empirical-разрядки PARTIAL→PROVEN** (feat, med): 5 частичных
   результатов из C605 всё ещё PARTIAL — аудиту по прецеденту
   C598/C602 (дефект → негатив → iff → fail-closed); каждый —
   либо полный клоз, либо честный негатив с witnesses.
3. **PALOMAR upstream-push** (user-шаг, подготовка done): §(г) —
   ничего не поглощено, ниша пуста, statements готовы. Осталось
   только оформление submission (user-решение).
4. **Paper v0.7** (docs, med): v0.6 (C604) не включает v3.2,
   карточки 9–11, generate-hier (n→100000), auto-LR-числа. Секция
   v0.7: «v3.2-канон: 10 клозов + применения» — поверхность
   заморожена, писать дёшево.
5. **Иерархия глубины 3+ / оптимальность B** (theory, med-high):
   теория: оптимален ли B = w(m−1)? Минимизация total окон
   (сейчас total = Σ per-block, растёт ~n/B; глубина 3+ даст
   total ~ log). Кандидат-клоз (11) для v3.3 по прецеденту C614
   (развёртка + делегат).

Top-3 на следующий виток: (1) paper v0.7 (v3.2-канон + карточки —
поверхность заморожена, максимальный внешний рычаг при минимальной
цене), (2) иерархия глубины 3+ / оптимальность B (единственный
открытый теоретический вопрос канона; клоз-кандидат готов),
(3) empirical-разрядки PARTIAL→PROVEN (5 штук из C605 — закрытие
старейшего долга проекта).

## Honest limits (процедурные)

- READ-ONLY виток C616: lake не запускался; freeze 8823 / гейты
  17/17 — по receipt'ам .tmp/C612–C615 (прецедент docs-витков
  C599/C603/C612).
- Аудит HAGI_v2 (§в) — по git log/status на момент C616;
  deep-чтение диффов wave240 не выполнялось.
- PALOMAR-запросы (§г) — по точным именам и 2-3-словным темам;
  семантически близкие записи под другими именами не
  исключены (реестр 1293 записи, просмотрена только выдача
  поиска и 25 последних).
- Числа «n=100000, 25 блоков, peak 63», «drop 1/4», «pytest 63»,
  «[63,63,1]» — цитаты receipt'ов C612–C615.
- Streak 166 для C616 — по механике +1/виток (docs-витки —
  посадки, прецедент C580/C583/C594/C599/C603/C612).
