# Phase analysis: C606–C611 — formula-driven эра: γ*=1/L, null-ce, snapshot-политика, иерархия (2026-11-23)

Series HEAD dd0e1ea2c31be7470fea13c856de0dd42ab4c8b0 (C611; `git log`
проверен: 9ac23393 C606 → 0da35ab7 C607 → d71a06bb C608 → c60f69bf
C609 → 76354a17 C610 → dd0e1ea2 C611; tree clean). Виток C612 —
docs-виток фазового анализа (прецедент C599/C603): READ-ONLY, один
docs-commit. Серия C606–C611 = один theory-виток (γ*=1/L) + виток
техдолга (null-ce) + три витка corpus/data-политики (snapshot,
auto-LR, fallback) + один theory-виток (иерархия). Freeze 8814 →
**8822** (C606: 8814+4 Schedule; C607–C610 identity 8818; C611:
8818+4 hier).

## Commit one-liners (C606–C611)

- C606 9ac23393 `feat: optimal step size certified` —
  NegativeTransfer.lean секция Schedule (+78): `nlDrop γ L G`,
  `nl_drop_bound` (descent-лемма), `nl_drop_le_optimal` (полный
  квадрат (G²/2L)(1−Lγ)² ≥ 0 — глобальный максимум на всём ℝ),
  `nl_drop_optimal`: γ* = 1/L, max drop G²/(2L). Кандидат
  «γ* = 2/(3L)» ОТКЛОНЁН (ошибка черновика) — вершина выведена
  дважды (производная + полный квадрат). Источники: MIT 6.7220
  L12 Farina 2025, Cambridge DAMTP lecture3. Freeze 8814→8818.
- C607 0da35ab7 `fix: corpus null ce tolerance` —
  bench_bridge.py: `_validate_ledger_schema(structural=True)`
  фильтрует null-ce записи (схема wave236k PARTIAL_LAW) вместо
  per-entry abort; 18 режимов оживли 3→0; cs-путь (TypeError
  F(None)) закрыт тем же фильтром; телеметрия corpus_ce_skipped.
  Честные ABORT сохранены (N-пины, домены) — fail-closed не
  ослаблен. Freeze identity 8818.
- C608 d71a06bb `feat: corpus snapshot pinning default` —
  SNAPSHOT_LEDGER: снапшот live-корпуса HAGI_v2 (35 ключей: 34
  ns_* + law_alphabet), выбран по критерию grow-snap PASS
  certified bound; git-show fallback невозможен (checkpoints/
  untracked в HAGI_v2). Default = deterministic snapshot;
  `--live-corpus` opt-in с DRIFT-телеметрией; wave238 chat_law
  ломает certified bound принципиально (data property) — на live
  fail-closed ABORT ожидаем. Drift между прогонами закрыт.
- C609 c60f69bf `feat: auto lr from optimal step` — применение
  C606: `auto_lr(dts) = 1/(2·trace(H̄))` exact Fractions в
  adapter-transfer-auto / transfer-gate-certified (было γ = 1/10
  TR_ETA); γ_auto 0.477–0.667 vs 0.1; verdicts идентичны pre;
  golden grow-snap/mini-hagi бит-идентичен; `--fixed-lr` откат.
  Телеметрия steps_drop_vs_bound (honest: bound может быть
  loose). Freeze identity 8818.
- C610 76354a17 `fix: corpus fallback policy` — трёхуровневая
  политика: default snapshot → structural-недостаточность
  (<2 домена для DOMAIN_REQ_MODES) → WARNING + LIVE-FALLBACK →
  ATG C566-редирект; `--snapshot-corpus` форс (fail-closed
  exit 3), `--live-corpus` всегда live, взаимоисключающие.
  Content-аборты (certified bound, N-пины) fallback'ом НЕ
  тронуты. StatusLint-хвост C609 (steps_drop_vs_bound не в
  RUNTIME_NAMES) закрыт. Freeze identity 8818.
- C611 dd0e1ea2 `feat: hierarchical window coverage any n` —
  CoverageReading.lean (+92): `hierBlockLen`, `hierStarts`,
  `hier_covers_any_n` — полное покрытие [0, n) БЕЗ верхней
  границы n (поблочное сведение к covStartsStep_covers C602);
  `hier_peak_window_budget` — peak ≤ m окон в блоке (peak ≠
  total — честность). Параметры s = w, B = w(m−1) = 4032:
  INFEASIBLE-граница C602 (n ≤ 4032) снята. Witness n = 8128:
  covered, per-block [63,63,1], негатив одноуровневого 127 > 64.
  Freeze 8818→8822.

## (а) Formula-driven: ноль магических констант в исполняемом контуре

Главный итог серии — каждый параметр машины теперь либо
certified-формула, либо политика с явным контрактом:

- **Теория → параметр машины**: γ* = 1/L (C606) → auto_lr (C609);
  k* = ⌈log₂(L·d/ε)⌉−1 (C593 → C597); adaptive span s =
  min(w, ⌈(n−w)/(m−2)⌉) (C602); иерархия B = w(m−1) (C611).
- **Теория → чтение**: двухуровневый transfer-гейт (C601);
  coverage-чтение (C598); hier_covers_any_n как контракт
  полного покрытия (C611).
- **Данные → политика вместо константы**: снапшот-пиннинг как
  default (детерминизм), live как opt-in с телеметрией DRIFT
  (C608); структурная недостаточность → fallback с WARNING,
  содержательная → честный ABORT (C610) — граница
  structural/content проведена по certified-семантике, не по
  удобству. Null-ce фильтруется как ИЗВЕСТНАЯ схема волны с
  перечнем пропущенных ключей в stderr (C607) — не молча.
- Паттерн серии: **замена measured-proxy на certified-формулу
  доведена до данных** — раньше (C597/C601/C602) заменялись
  пороги в коде; теперь и источник данных (корпус) стал
  версионируемым артефактом с политикой выбора.

## (б) Метрики серии

| Метрика | C605 | C606 | C607 | C608 | C609 | C610 | C611 |
|---|---|---|---|---|---|---|---|
| Freeze | 8814 | **8818** | 8818 | 8818 | 8818 | 8818 | **8822** |
| Δ freeze | — | +4 | 0 | 0 | 0 | 0 | +4 |
| Тип | feat | feat | fix | feat | feat | fix | feat |
| Lean-декларации | — | +4 | 0 | 0 | 0 | 0 | +4 |
| Streak | 155 | 156 | 157 | 158 | 159 | 160 | 161 |

- Freeze за серию: +8 (Schedule +4, Hier +4); ноль новых аксиом
  (AllAxiomCheck = 3: propext, Quot.sound, Classical.choice —
  все витки).
- Гейты: 17/17 PASS каждый виток (MachineDiffTest 2000 configs,
  Freeze-lint, AssumptionScan без дрейфа).
- Bench: 18 режимов оживлены C607 (3→0); C608 снапшот-таблица
  стабильна (drift-immune); C609 verdicts идентичны при γ_auto
  ×5–6 больше старой константы — certified-гейт держит.
- Streak 162 для C612 (docs) — по механике +1/виток.

## (в) Corpus-политика как воспроизводимый паттерн

Серия оформила трёхуровневый контракт данных (C607+C608+C610):

1. **Детерминизм — дефолт**: снапшот, пин по критерию
   certified-гейта (grow-snap PASS выбрал волну), регенерация
   one-liner'ом в docstring.
2. **Live — opt-in**: телеметрия «results may DRIFT», результаты
   не входят в золотые прогоны.
3. **Fail-closed на границе**: структурная нехватка (мало
   доменов) → fallback с WARNING; содержательная (bound, пины)
   → ABORT exit 3; известная схема волны (null-ce) → фильтр с
   перечнем; кастомный --data — вне политики (пользовательский
   выбор).

Паттерн переносим на любые внешние данные (HAGI_v2, будущие
корпуса): «пин по certified-критерию + явная телеметрия
источника + структурный/content-split деградации».

## (г) HAGI_v2 recheck — волны после 238

Прямой аудит C:/HAGI_v2 на момент C612 (git log + status):

- **HEAD b4ab6e9 wave239** (`fix(wave239): external review fixes
  — no validation leakage into refine, honest bound semantics`)
  — после wave238 (live chat + seed laws) волна внешнего ревью
  закрыта. Дерево HAGI_v2 чистое.
- **invention_multi.py больше НЕ в полёте**: файла нет в
  scripts/, untracked-остатков нет — незакрытая волна из
  C599-аудита приземлена/убрана. Roadmap-пункт «движущаяся
  мишень» (Chesterton) снят: формализуемость можно исследовать.
- **checkpoints/ по-прежнему untracked в HAGI_v2** — потому
  снапшот C608 есть единственный воспроизводимый якорь корпуса
  (политика §(в) это и компенсирует).
- Влияние на серию: none — freeze 8822 не затронут; wave238
  chat_law-контент учтён границей снапшота C608.

## (д) Roadmap ≥5 к цели «max качество, min объём, min вычисления»

1. **invention_multi формализуемость** (research, med): волна
   приземлена (§г) — аудит на certified-срезы по прецеденту
   C598/C602 (паттерн «дефект → негатив → iff → fail-closed»);
   сначала map: какие инварианты волны имеют Lean-аналоги.
2. **PALOMAR: новые карточки** (docs, low-med): все 8 карточек
   PALOMAR-CARDS.md — C5XX-эра; NOTHING из C606–C611 не
   поглощено (grep: nl_drop_optimal, hier_covers_any_n,
   covStartsStep — 0 вхождений). Кандидаты Card 9–11:
   (9) γ* = 1/L optimal single-step drop (C606, чистая
   оптимизация, MSC2020 90C25/65K05); (10) hierarchical window
   coverage for arbitrary n with peak budget (C611, комбинаторно
   streaming); (11) exact adaptive-span iff-характеризация
   (C602). Дёшево: statements уже machine-checked.
3. **Иерархия в bench** (feat, med): применение C611 —
   generate-hier режим bench (иерархические окна для n > 4032),
   A/B vs INFEASIBLE-возврату adaptive-span; телеметрия
   peak-vs-total. Замыкает паттерн «теорема → режим» как C609.
4. **Метатеория v3.2** (feat, high): консолидация клозов C611
   (иерархия) + C606 (γ*) в единый statement по прецеденту
   MasterTheoremV31 (C600): +2 клоза — schedule-оптимальность и
   hier-покрытие; paper-draft уже упоминает master_theorem_v3.2.
5. **Paper v0.7 или внешний push** (docs, med): v0.6 (C604) не
   включает γ*/auto-LR/снапшот-политику/иерархию; либо секция
   v0.7 (formula-driven data policy + coverage-any-n), либо
   PALOMAR-отправка как внешний якорь (user-шаг).

Top-3 на следующий виток: (1) PALOMAR Card 9–11 (минимальная
цена, максимальный внешний рычаг — statements готовы), (2)
generate-hier bench-режим (применение C611 по прецеденту C609:
теорема → телеметрия), (3) метатеория v3.2 (+2 клоза к
hagi_master_v31 — сжатие поверхности перед paper v0.7).

## Honest limits (процедурные)

- READ-ONLY виток C612: lake не запускался; freeze 8822 / гейты
  17/17 — по receipt'ам .tmp/C606–C611 (прецедент docs-витков
  C599/C603).
- Аудит HAGI_v2 (§г) — по git log/status на момент C612;
  deep-чтение диффов wave236l-m/239 не выполнялось.
- Числа «18 режимов», «γ_auto 0.477–0.667», «n = 8128, peak 63»,
  «35 ключей» — цитаты receipt'ов C606–C611 (pre-registered
  телеметрия bench-режимов).
- Streak 162 для C612 — по механике +1/виток (docs-витки —
  посадки, прецедент C580/C583/C594/C599/C603).
