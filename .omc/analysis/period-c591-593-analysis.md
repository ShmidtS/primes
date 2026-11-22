# Phase analysis: C591–C593 — фронтир-эра: certified-оптимумы параметров машины (2026-11-22)

Series HEAD 0e8c65e024b8d0bfa0d80b1dcf473763bc535b6c (C593; `git log`
проверен: 9d29c12e C591 → 8ee33d9e C592 → 0e8c65e0 C593; tree clean).
Виток C594 — docs-виток фазового анализа (прецедент C583/C580):
READ-ONLY, один docs-commit. Серия C591–C593 = integrity-защита после
внешнего cleanup + ровно два feat-витка, закрывшие top-2 roadmap-долга
из C583 (нелинейный transfer → C592; snap-грид оптимальность → C593).
Freeze 8775 → **8803** (receipt C593: «FREEZE: PASS (8803 = 8785+18
new, 0 aliased)»; C591 identity 8775, C592 8785).

## Commit one-liners (C591–C593)

- C591 9d29c12e `refactor:` post cleanup integrity and bench dedup —
  внешний cleanup c442e69 удалил .omc/analysis-файлы (включая
  period-c506-508); 8 битых ссылок починено (ALGORITHMS/STATUS/
  paper-draft/PROPOSAL: git-show-указатели на историю), bench-дедуп
  −57 строк (общие `_holds`/`_mini_report` для mini-hagi/grow-snap
  семейства, byte-identical вывод сохранён golden-ами). Freeze
  identity 8775, все гейты PASS.
- C592 8ee33d9e `feat:` smooth objective transfer bound —
  NegativeTransfer.lean (+217): L-smooth нелинейный transfer.
  CERTIFIED SUFFICIENT (не iff): `smooth_obj_transfer_bound`,
  `sufficient_negative_transfer`, кирпичи nl_step_mono/lower.
  G-граница градиента — честный binder вдоль траектории; негатив-
  инстанс n=2 доказал достаточность ≠ необходимость. Freeze
  8775 → 8785 (+10).
- C593 0e8c65e0 `feat:` snap grid optimal k — GrowSnap.lean (+249):
  точная формула k* = ⌈log₂(Ld/ε)⌉−1 (`snap_k_eq_ceil`), ДОКАЗАННАЯ
  минимальность (`snap_k_min`, `snap_k_lt_violates`), консолидация
  `snap_optimal_k` (k* доставляет минимум certified-бюджета бит
  `snap_bits_err_tradeoff`). ℚ-зеркало-инстансы I1/I2/граница
  равенства. Freeze 8785 → **8803** (+18), гейты PASS
  (TestAssumptionScan / TestFreeze / TestPremiseRegistry).

## (а) Фронтир-эра: от «формализуем эмпирику» к «certified-оптимумам параметров машины»

Виток меняет тип результата серии. Мостовая эра (C574–C582)
формализовала ИМЕЮЩЕЕСЯ поведение HAGI_v2; machine-эра (C584–C590)
собрала guarantees в master-theorem v3; C592–C593 выводят параметры
машины на certified-оптимумы:

- **k-выбор снапа** (C593): раньше фиксированный GS_K=40 в
  bench_bridge.py; теперь k*(L,d,ε) — certified-минимум бит-бюджета
  при выполнении ε-бюджета ошибки. Машина сама знает свой оптимум.
- **Transfer-решение** (C592): двухуровневая теория — ТОЧНАЯ iff для
  квадратичных (C572) + КОНСЕРВАТИВНАЯ sufficient для L-smooth
  произвольных; таблица применения зафиксирована в STATUS. Warm/cold
  — теперь certified-decision, не эвристика.
- **Целостность как актив** (C591): внешний cleanup НЕ уронил серию —
  битые ссылки пойманы DocLint-культурой витока, починены
  git-show-указателями (ссылка на историю вместо мёртвого файла).
  Паттерн «cleanup-tolerant documentation» закреплён.

## (б) Метрики серии

| Метрика | C590 | C591 | C592 | C593 |
|---|---|---|---|---|
| Freeze | 8775 | 8775 (identity) | 8785 | **8803** |
| Δ freeze | — | 0 | +10 | +18 |
| Тип | — | refactor/integrity | feat | feat |
| Streak | 138 | 139 | 140 | 141 |

- Freeze 8768 (C582) → 8803 (C593): +35 за витки C584–C593, ноль
  новых аксиом (TestAllAxiom regression в гейтах каждого feat).
- Theorems: `rg -c 'theorem ' Hagi` = 6587 определений по файлам
  (generated/theorem-index.md — SSOT, обновлён гейтом C593).
- Bench-дедуп C591: −57 строк при byte-identical golden-выводе —
  доказательство, что целостность и объём не конфликтуют.

## (в) HAGI_v2 recheck — волны 226–232: эмпирика ПЕРЕГНАЛА roadmap

Прямой аудит /c/HAGI_v2 (git log, bc0d9b5 HEAD):

- **wave226** (bb251a2): снятие truncation вывода (ask 60→400,
  consolidate 200→600, memory 512→2048) — user-directive фикс.
- **wave228** (b7f7f64): model-driven length — модель сама решает
  длину генерации (entropy collapse / repetition / terminator);
  full-input reading coverage-окнами. Верифицировано живьём.
- **wave229-URGENT** (8d34dc1): RoPE long-context 96 байт,
  full-disk training. **RISK**: tests/ УДАЛЕНЫ по директиве user —
  волна держится на ручных live-проверках, regression-сети НЕТ.
- **wave230-231** (39611dd): line-by-line audit fixes — P0: attention
  pairwise (был uniform через broadcast — тихий баг!), contiguous
  tail holdout + embargo (random split УТЕКАЛ val в train). Честно:
  cert honest None (Adam+rollback не certified).
- **wave232** (bc0d9b5): **C592 sufficient-transfer gate ИНТЕГРИРОВАН
  upstream** — warm-start свежего домена iff ce ≤ 0.5 (measured
  proxy для start-gap); попутно найден мёртвый warm-start (детект
  fresh-adapter никогда не срабатывал). Roadmap-пункт C594-эры
  (auto-sufficient-transfer) частично выполнен SAМИМ HAGI_v2.
- **memory-consolidation (wave225 → C584)**: стабилен, ревизий волны
  нет; KnowledgeConsolidation.lean соответствует (consolidate/
  remember/learn_from_dialog мост без дрейфа).

Вывод: формализация и имплементация впервые пошли ВСТРЕЧУ друг
другу в одном такте (C592 theory 18:13 → wave232 integration 18:46 —
33 минуты). Round-trip theory→code завершён.

## (г) Roadmap ≥5 к цели «max качество, min объём, min вычисления»

1. **Авто-k* в bench** (feat, low-med): применить C593 — заменить
   ручной GS_K=40 в bench_bridge.py:5838 на snapK(L,d,ε); гейт —
   golden-вывод не меняется там, где k*=40 совпадает, и меняется
   с certified-обоснованием там, где не совпадает. Закрывает
   theory→bench loop C593 так же, как wave232 закрыл C592.
2. **Certified proxy-замена в wave232-гейте** (feat, med): ce ≤ 0.5 —
   measured proxy; заменить на честный start-gap измеритель с
   certified sufficient-порогом из `sufficient_negative_transfer`
   (нужна G-оценка градиента — уже binder в theory).
3. **Wave226/228 мосты** (research, med): model-driven length
   (условия остановки генерации) и untruncated output (coverage-
   окна full-input reading) — если stopping-условия формализуемы
   как certified-предикаты. Кандидат fresh-minimal-scope паттерна.
4. **External push** (user-шаг): paper Appendix A (master-theorem v3
   + auto-gate + FactLedger) готов; добавить C592/C593 (двухуровневый
   transfer + k*) — окно wave213 всё ещё открыто, стоимость нулевая.
5. **Метатеория-2** (research, med-high): v3.1 = master-theorem +
   auto-gates + k*-оптимум + двухуровневый transfer в ОДИН statement
   — консолидация C558+C576+C592+C593 этажом выше.

Top-3 на следующий виток: (1) авто-k* в bench (дешёвый feat, прямой
loop-закрытель), (2) certified-порог в wave232-гейте (следующий шаг
навстречу theory/code), (3) wave226/228 source-аудит формализуемости
(stopping-предикаты) перед следующим feat.

## Honest limits (процедурные)

- READ-ONLY виток C594: lake не запускался; freeze 8803 / гейты —
  по receipt'ам `.tmp/C591–C593` (прецедент docs-витков
  C583/C580/C578/C575).
- Аудит HAGI_v2 (в) — по commit-messages волны 226–232, без
  deep-чтения диффов; wave229 RISK (удалённые tests) — по
  commit-message самой волны.
- Streak 141 для C594 — по механике +1/виток (docs-витки считаются
  посадками, прецедент C580/C583).
- Таблица transfer-границ C572/C592 — цитата STATUS.md, сверка с
  NegativeTransfer.lean сделана grep-ом сигнатур, не построчно.
