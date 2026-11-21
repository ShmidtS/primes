# Phase analysis: C530–C533 — адаптерная эра: rollback-bridge, paper v0.2, adapter-growth, adapter×snap composite (2026-11-21)

Series HEAD fcf5f6b8ece4d0fdf145eaee52de1bd5545ce889 (C533;
`git log` проверен: 22576dab C530 → 99d3f73f C531 →
fedc69ea C532 → fcf5f6b8 C533; tree clean). Виток закрыл
roadmap-пункты C511–C519 анализа: rollback-gate мост (пункт 2),
paper-числа (пункт 3) — и ОТКРЫЛ третью ось роста: адаптеры.
Composite C533 доказал прогоном минимальный объём (8 параметров/
уровень против 21 у full-блока) И минимальные вычисления (сброс
знаменателей snap'ом на каждом уровне) одновременно — таблица
трёх механизмов роста теперь в STATUS.md.

## Commit one-liners (C530–C533)

- C530 22576dab `feat:` rollback gate bridge from hagi v2 —
  Hagi/Theory/RollbackGate.lean (239 строк): certified-rollback
  из admitted-state при measured-регрессии на old-domain sample;
  закрывает разрыв «wave199 implementation опережает proof»
  (roadmap-пункт 2 из C511–C519 анализа). Freeze 8595→8615
  (+20, 0 aliased); index 536 модулей.
- C531 99d3f73f `docs:` paper draft numbers c506 c530 —
  docs/paper-draft.md +161 строк: числа C506–C530 в текст
  (grow-кривая, rollback, 536 modules / 12772 theorems).
  Freeze PASS 8615/0 aliased (bake C530 — lock gitignored).
- C532 fedc69ea `feat:` certified adapter growth —
  Hagi/Theory/AdapterGrowth.lean (190 строк) + bench
  `--mode adapter-grow` (394 строки): LoRA-класс адаптеры
  r=1 поверх frozen trunk, certified; измерено ×2.96 прогресса
  на параметр против identity-блока. Freeze 8615→8626 (+11,
  0 aliased); index 537.
- C533 fcf5f6b8 `feat:` adapter snap composite grow —
  `adapter_snap_bound` (Lipschitz-ℓ¹/ℓ∞ форма для h = B·A·x) +
  `adapter_snap_cycle_sound` (делегат к grow_snap_cycle_sound,
  intentional pin); bench `--mode adapter-snap-grow`: 8 уровней,
  64 параметра суммарно, admission ТОЧНО obj-инвариантен на
  каждом уровне, snap q/2^40, cumulative bound ≈ 2.98e-13
  (запас ~13 порядков), глубина 10 certified, ~4 c. Freeze
  8626→8628 (+2); STATUS.md таблица трёх механизмов.

## (а) Адаптерная эра: итог

- **Третья ось роста certified.** До витка рост корпуса шёл
  двумя механизмами (identity/fiber-блок C521, exact-путь).
  C532 добавил адаптерный путь: 8 параметров/уровень (r=1,
  A и B по 4) против 21 у full-блока при БОЛЬШЕМ прогрессе —
  квази-оптимальная ось для цели «max качество, min объём».
- **Composite = Pareto-фронт по обеим целям.** Адаптер без
  снапа (C532) компаундит знаменатели по уровням (вычисления);
  блок со снапом (C521) сбрасывает знаменатели, но платит 21
  параметр. C533 объединил: 8 параметров/уровень И сброс
  знаменателей — доказано прогоном (bench-adapter-snap-grow.json),
  не утверждением. Таблица 3 механизмов в STATUS.md — выбор
  механизма теперь data-driven, а не taste-driven.
- **Rollback-мост замкнул цикл theory↔HAGI_v2.** Wave199
  (rollback инкумбента при >25% CE-регрессии) был кодом без
  теоремы; теперь теорема есть и в корпусе, и bench-мост
  (admission с ТОЧНОЙ инвариантностью в C533) потребляет её
  паттерн. Двусторонняя синхронизация canon ↔ HAGI_v2.

## (б) Метрики витка (замер HEAD fcf5f6b8, READ-ONLY)

- **Freeze verify**: PASS, 8628 declarations (8595 → 8628,
  +33 за виток: 20 rollback + 11 adapter + 2 composite),
  0 aliased, 0 потеряно (receipts C530–C533).
- **Index regen**: 537 modules (536→537 в C532), theorems
  12772 (C531 замер), дрейф закрыт на каждой посадке.
- **Streak посадок**: C519 = 62 → C533 = **76** подряд
  (нумерация сплошная C520–C533, freeze PASS на каждой;
  счёт по нумерации, не отдельным чек-файлам).
- **Гейты** (receipts): lake build PASS (19341→19343 jobs);
  TestFreeze, TestMergeModule, LayerLint, NsLint, DocLint,
  DupLint, StatusLint, TrivialLint, ReachLint, STMDUP
  (9 intentional pins), ChallengeCheck 2/2, MachineDiffTest
  (2000 configs), AssumptionScan+Test, PremiseRegistry+Test,
  TestAllAxiomCheck (allowed: propext, Quot.sound,
  Classical.choice) — все PASS.

## (в) Re-check HAGI_v2 (READ-ONLY, C:\HAGI_v2)

`git log --since='2026-11-21 19:58'` (время посадки C530):
**пусто** — новый код во внешнем агенте с C530 НЕ появлялся.
Последний их коммит — wave204 (b3508ab, 18:53): audit-bundle-v2
P0/P1 фиксы (verify_all coverage, PAIRED regression gate,
certified_argmax ties, RoPE position-encoding fix).

Кандидаты-мосты в Lean (непокрытое из ранее замеченного):
(1) **matched-null wave197** — Monte-Carlo matched null для
ложного «изобретения» (false INVENTED 8/8 → 0/8); в primes
теоремы нет. Остался единственный открытый bridge-кандидат
из списка C511–C519 (rollback закрыт C530, hybrid_select
синхронизирован wave198).
(2) Из wave204: PAIRED incumbent-vs-challenger gate на
фиксированных old-domain окнах — родственно rollback-gate
C530, возможен как уточняющая посылка (same-window pairing),
но мост-кандидат спекулятивен до появления теоретического
вопроса.

## (г) Roadmap ≥5 rank к цели «max качество, min объём, min вычисления»

1. **r-адаптивность** — выбор r per-level по measured прогрессу
   (r=1 vs r=2 certified-переключение). Бьёт в измеренный
   Pareto-фронт C533: если r=1 исчерпывает прогресс на уровне,
   certified-переход на r=2 сохраняет гарантии composite.
   Прямое расширение AdapterGrowth-канона.
2. **Adapter+continual** — GPM/A-GEM на адаптерных параметрах:
   забывание при адаптерном continual (frozen trunk не
   забывает по построению; вопрос — только конфликт градиентов
   между адаптерами). Связка с Continual-каноном T1.
3. **Merge-адаптеров («Матрёшка-компрессия»)** — SVD-компрессия
   стека адаптеров в один: 8 уровней × (4+4) → один r-k
   адаптер с certified err-bound. Прямая связка с upstream
   SVD C507 (TruncatedSVDTail) — переиспользует готовый
   tail-bound корпус.
4. **Paper: adapter-секция + отправка** (user-шаг) — вставить
   таблицу трёх механизмов + ×2.96/параметр + 13 порядков
   запаса в docs/paper-draft.md; upstream/svd PR-ready.
5. **Паломар-карточки** — режимы: когда r=1 stalls; глубина
   компаундирования знаменателей без снапа (C532 curve).

Top-3 на следующий виток: (1) r-адаптивность (расширение
свежего канона, наименьший риск), (2) merge-адаптеров через
SVD C507 (максимальная связность), (3) paper adapter-секция
(user, дёшево, повышает отдачу чисел).

## Honest limits (процедурные)

- Freeze/streak/гейты — по receipts `.tmp/C53*/receipt.md`
  и STATUS.md, READ-ONLY (lake не запускался — виток
  аналитический по определению задачи).
- Streak 76 выведен из сплошной нумерации C519=62 → C533;
  отдельного чек-файла streak нет.
- ×2.96 прогресс/параметр и 13 порядков запаса — bench-числа
  canonical-шкалы (regress-*.json), не Lean-теорема о
  превосходстве адаптера; превосходство — эмпирический факт
  на измеренном прогоне.
- HAGI_v2 re-check — READ-ONLY по git log; поведение wave204
  проверено их собственными тестами (94 green), не primes-
  гейтами.
- Roadmap-пункты 1–3 — проекты, не результаты; certified-
  переключение r и SVD-merge адаптеров не сертифицированы.
