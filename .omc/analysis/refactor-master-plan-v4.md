# Refactor Master Plan v4 — full theory re-read (C511)

Base: HEAD ee8d3a1b, freeze 8596, tree clean. Кредо: минимум
кода, максимум смысла; чистая универсальная система. Каждый
понятийный канон описан ОДИН раз; bench-мосты живут разделами
тематических канонов; имена публичных деклараций СОХРАНЯЮТСЯ
(прецедент: EFTheory «слит из пяти модулей; имена сохранены»).

## 0. Полная карта семей (49 Theory-файлов → 8 канонов)

| Канон (файл) | Поглощает | −файлов |
|---|---|---|
| CEChain.lean (канон, есть) | — (хаб, тело не трогаем) | 0 |
| SafeStep.lean | StochasticSafeStep, CompressedSafeStep (safe-часть), Confinement | 2 |
| Statistics.lean | HoldoutRisk, HoldoutWithoutReplacement (ужатый), AnytimePACBayes, AnytimeHoldoutStop, TwoDomainConfidence | 4 |
| Continual.lean | ContinualBench, ContinualMulti, GPMRelaxed, HybridContinual (+bench-мосты разделами) | 3 |
| Growth.lean | BlockAdmission, FunctionPreservingGrowth, GrowTrunkBlock (+BlockSmooth→BlockLipschitz) | 3 |
| BlockLipschitz.lean | BlockSmooth | 1 |
| Softmax.lean | RationalSoftmax, SandwichMonotone, BandTightening | 2 |
| Compression.lean | EFTheory, EF21InStep, CertTernaryJump, EF-хвост CompressedSafeStep | 2 |
| MergeQuant.lean | FisherQuant, NonlinearMerge | 1 |
| SelfEdit.lean | SelfEditGate, KnobMomentum | 1 |
| FullPipeline.lean | TrunkTrain (паттерн PhaseRoute — честный дубль) | 1 |
| MasterTheorem.lean | MasterBudget (раздел), VerticalCapstone (раздел) | 2 |
| Остаются как есть | MasterEF, ProvenTrunk, Interpretability, MDLPrune, GaugeQuotient, OnlinePL, FlowMatching, LogitGrowth, MiniHagi(2), CertCEHoldout, TrainerBenchmark, CertSandwichBench → частично расходятся по разделам канонов (см. транши) | — |

Theory: 49 → ~31 файл; строки: ~15.2k → цель ~12.5k (−18%):
главные источники — HoldoutWithoutReplacement aux (~400),
AdaptiveMajorizer tight-дубль (см. T2), BlockLipschitz/BlockSmooth
coord-dубли, CompressedSafeStep EF-хвост.

## 1. Транши (порядок = рост риска; каждый — один коммит + гейты)

### T1 «continual» (низкий риск, intra-only потребители)
- ContinualBench+ContinualMulti+GPMRelaxed+HybridContinual →
  Hagi/Theory/Continual.lean. Bench-мосты (gpm_bench_bridge,
  gpm_multi_*) — раздел `bench`. aux (cs_abs, dot_split, nrm) —
  общая секция. Порядок деклараций: aux → GPM exact → relaxed →
  hybrid → bench. Обновить: Hagi.lean (4 импорта → 1),
  ext-потребители ContinualBench (2), GPMRelaxed (2),
  HybridContinual (2) — заменить import-строки. −3 файла, −~80 строк.
- Риски deriv: минимальные (import-замены, имена сохранены);
  Freeze: те же декларации → identity ожидаема (проверить
  `python scripts/Freeze.py verify`; при алфавитном переупорядочивании
  деклараций внутри модуля возможен пересчёт id — тогда ЧЕСТНЫЙ
  `--update` bake в том же коммите, отражено в STATUS).

### T2 «descent/adaptive»
- AdaptiveMajorizer: НЕ сливать с другими (уникальная идея), но
  сжать ДУБЛЬ: base- и tight-разработки (ceAdaptiveCurv vs
  ceAdaptiveCurvTight, 8 зеркальных пар ~640 строк) — вынести
  общий каркас (exp_quad_bound как параметризованный
  majorizer-интерфейс, tight = специализация с kappa). Цель −250
  строк БЕЗ потери теорем (имена tight-вариантов сохранены как
  `:=`-синонимы или 1-строчные обёртки — уже применённый в
  корпусе приём abbrev-канона CertifiedArgmax R3).
- Confinement → раздел в SafeStep.lean? НЕТ: Confinement —
  PL-надстройка, не safe-step; решение: Confinement остаётся,
  aux-norm-факты (norm-геометрия) дедуп с OnlinePL (общая секция
  в OnlinePL, Confinement импортирует 1-строкой). −60 строк.
- Риски: AdaptiveMajorizer — доказательная дедупликация
  (перепроверка tight-теорем через новый каркас); если каркас не
  вытягивает за 3 итерации — down-scope: оставить дубль,
  зафиксировать в tech-debt.

### T3 «softmax + bench-мосты»
- RationalSoftmax+SandwichMonotone+BandTightening → Softmax.lean:
  канон exp-интервалов (все expLower/expUpper/aux-факты — ОДИН
  раз в заголовке), затем монотонности (по x, по n), затем
  certified argmax/полоса. −2 файла, −~150 строк (дедуп
  log_add_one_sub_div_pos и монотонностных aux).
- CertSandwichBench, TrainerBenchmark — остаются (разные
  bench-режимы, малы); импорты → Softmax.
- Риски: SandwichMonotone ext=2 + RationalSoftmax ext=2 —
  import-замены; Freeze — как T1.

### T4 «compression + merge-quant + model-scale» (выборочный)
- EFTheory+EF21InStep+CertTernaryJump → Compression.lean (−2,
  EFTheory уже слит — добавить instep/jump разделами).
- FisherQuant+NonlinearMerge → MergeQuant.lean (−1; дедуп
  quadLoss/quadGrad/crossCurv ≈ quadLossDiag-семьи).
- Model/CE*: только 2 слияния по заголовочному аудиту:
  CEGroupedScaleBasic (30 строк) → CEGroupedScale;
  CEScaleChoice+CEScaleSelection → CEScale.lean (−2 в Model).
  Полный re-read Model — ВНЕ этого плана (отдельный бит).
- Риски: MasterEF потребляет EF-идеи — import-замены; CompressedSafeStep
  EF-хвост (ef_crossover) переезжает в Compression — MasterEF и
  CompressedSafeStep обновляют импорты (имена сохранены).

### T5 «loop/master» (высший deriv-риск — последним)
- TrunkTrain → раздел trunk-цикла в FullPipeline (−1).
- MasterBudget → раздел бюджета в MasterTheorem (−1; MasterBudget
  ext=1 = MasterTheorem-потребитель + Hagi.lean).
- VerticalCapstone → раздел capstone в MasterTheorem (−1).
- SelfEditGate+KnobMomentum → SelfEdit.lean (−1).
- MDLPrune/Interpretability: терминирующий паттерн — 1-строчные
  ссылки на SelfEdit-канон (chain_strictMono), файлы остаются.
- Unified: CertifiedLoop+CertifiedLoopKernel → CertifiedLoop.lean
  (−1) — только если T1–T4 прошли без Freeze-bake; иначе отложить
  в v5 (фиксируется в STATUS честно).
- Cert/State: Adapters+Empirical → Cert/Core, EvalBindingCert →
  Cert/EvalBinding (−3) — опционально, тем же условием.

### T6 «docs/archive» (docs-only, нулевой код-риск)
- .omc/analysis/: git mv cycle*-results и эпохальные файлы в
  archive/{C2xx,C3xx,C4xx,C5xx}/; оставить: v3/v4-планы,
  PROPOSAL-*, paper-draft, architecture-audit-backlog.
- STATUS.md: свернуть до «текущий цикл + последние 10 + оглавление
  эпох со ссылками в archive» (6955 → ~1500 строк); ALGORITHMS.md:
  дедуп описаний (каждый алгоритм — 1 раз); README: карта
  канонов v4.

## 2. Докстринг-стратегия (канонический словарь)
- Каждое понятие описывается ОДИН раз в канон-модуле:
  safe step → SafeStep; e-process/Ville → Statistics (Anytime-
  раздел); GPM/AGeM/rank-trunc → Continual; exp-интервал/
  sandwich → Softmax; EF/telescope → Compression; adopt-gate/
  knob → SelfEdit; admission margin → Growth; master trajectory
  → MasterTheorem; bench-режим bench_bridge.py → раздел `bench`
  соответствующего канона (1-строчный докстринг: режим, вход,
  что certified).
- Остальные модули: 1-строчные ссылки `See Hagi.Theory.X` вместо
  пересказа. Запрет: копировать математическое определение между
  докстрингами (DupLint на докстринги — расширение скрипта в T6,
  опционально).

## 3. Критерии готовности
- Theory: 49 → ≤32 файлов; строки −15..18% (≥2000 строк
  сэкономлено суммарно с Model-траншем T4).
- Все имена публичных деклараций сохранены (проверка:
  `python scripts/Freeze.py verify` identity 8596+только новые
  id отсутствуют; при честном bake — явно в STATUS + receipt).
- Гейты каждого транша: lake build exit 0; DocLint, StatusLint,
  LayerLint, DupLint, NsLint, ReachLint, TrivialLint, STMDUP —
  PASS; ALLAXIOMS — только propext/Quot.sound/Classical.choice;
  ChallengeCheck 2/2; MachineDiffTest PASS.
- Каждый транш = один атомарный коммит `refactor(TN): <family>`;

## 4. Что НЕ трогаем (honest)
- Fresh/executed контур живой: Step/ (33), Runtime/CertChecker,
  bench_bridge.py (только import-имена при переездах), upstream/,
  External/Flywheel, карантин Research (Hagi/Research.lean —
  588 ссылок на Theory: слияния T1–T5 обновляют его импорты
  механически, теоремы не меняются).
- CEChain/MasterTheorem/StochasticSafeStep-тела: хабы, только
  import-актуализация.
- Model/Contracts полный re-read — вне v4 (заголовочная карта в
  .tmp/C511/notes-core-model-contracts.md — входная точка v5).
- GaugeQuotient, FlowMatching, LogitGrowth, Interpretability,
  MDLPrune, ProvenTrunk, MasterEF, OnlinePL — живые острова,
  слияние не оправдано (уникальные идеи, малые пересечения).

## 5. Риски и откаты
- deriv: канон-файлы живут в Hagi/Theory/ → import-пути
  потребителей меняются только на имя модуля, не слоя; LayerLint
  гейтит слои.
- Freeze: перемещение деклараций между модулями меняет их full
  name (`Hagi.Theory.OldX.thm` → `Hagi.Theory.NewX.thm`) —
  declarations.lock перегенерируется честным `--update` в коммите
  транша, с diff-выпиской в receipt; перед этим `verify`
  фиксирует ПОЛНЫЙ список переименованных id (никаких тихих потерь).
- 3 неудачи одного слияния (Sunk Cost) — транш откатывается,
  фиксируется в .omc/tech-debt.md, план v4 корректируется.
