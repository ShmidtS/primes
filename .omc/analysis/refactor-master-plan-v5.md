# Refactor Master Plan v5 — full repo re-read (C522)

Base: HEAD 141c7438 (C521), freeze 8595, tree clean.
Sources: .tmp/C522/notes-model-contracts.md,
notes-probability-scripts-rest.md, notes-remaining-dirs.md.
Инструменты: merge_module.py (механика слияний; namespace-прецеденты
Continual/Statistics), deadcheck.py (0 мёртвых модулей — все
zero-consumer это корневые хабы), LayerLint.py (только import-DAG;
лимита размера файла НЕТ).

Кредо v5 (как в гранд-директиве): дубли → мёртвый вес → риск →
выгода; каждое слияние intra-family, слой LayerLint не меняется,
.namespace файла сохраняется при merge (прецеденты C511+).
Верификация каждого транша: lake build + Freeze identity + DiffLint
страховка (DupLint baseline). Живой конвейер (bench_bridge,
Freeze, генераторы) не разрушать.

## Транши W1–W8 (rank: выгода/риск, по убыванию)

### W1 Model CE*-семья: канон-слияния (≈ −7 файлов, ~0 строк потерь)
- Файлы: BatchCEDescent{,Common,Arithmetic,Direction,SafeStep}.lean →
  BatchCEDescent.lean (hub+Common+оси математики);
  HalfEta/LogitRange/ResidualNorm/Stochastic/Fixtures остаются.
- CEScaleChoice 127 + CEScaleSelection 303 → CEScale.lean
  (v4-T4 обещание); CEGroupedScaleBasic 31 → CEGroupedScale 853
  (мех. поглощение); CEConfidenceScale 284 + CEJointScale 531 →
  канон CEScale-family (внутрь CEScale.lean или отдельный раздел).
- Механика: merge_module.py, layer Model=4 не меняется, ns
  сохраняется. Риски: deriv-доказательства CE-осей после
  переименованных aux — гейт lake build. Критерий: build зелёный,
  Freeze 8595 identity, −7 файлов в Model/.

### W2 Contracts: EM + growth-слияния (−4…−5 файлов)
- BatchCEGrowth 1283 + BatchCEGrowthSelection 1626 →
  BatchCEGrowth.lean; BatchCEBestResidual 77 + BatchCEStepCore 513
  → StepCore; EM-семья: MixtureEMTrajectory+FactorizedMixtureEM+
  FiniteEMTrajectory+ChangingEMTrajectory → Contracts/EMTrajectory.lean
  (все импортируют Probability/FiniteMultiEM — носитель не трогаем);
  NaturalLean 20 → ближайший по теме (поглощение micro).
- НЕ трогать: certificate-семью (v4-урок: слияние cert-хабов —
  высший deriv-риск); BatchCEBudgetGuard 2394 (oversized top-1 —
  кандидат на нарезку, но code-risk, отложен в W7-опции).

### W3 Probability: Freedman + MirrorHedge каноны (−5…−7 файлов)
- Freedman{Step,TwoSided,Adaptive,FamilyConfidence} → Freedman.lean
  (LayerLint size-лимита нет; если паранойя — 2 файла).
- MirrorHedge MWU-семья (MWU, MWUSelectedLoss, MWUSelectedGradient,
  Certificates, Gibbs) → Probability/MirrorHedge.lean;
  Optimization/MirrorHedge 1938 остаётся (слой 3, потребитель).
- FiniteLogScore 248 + FiniteJointLogScore 285 → один файл (−1).
- Гейт: grep EntropyConvexity vs Math/Info/InfoCore перед
  слиянием entropy-фактов; если дубли — канон в Math/Info (layer 0).

### W4 Micro-слияния (−3…−4 файла, низкий риск)
- Unified: CertifiedLoop 371 + CertifiedLoopKernel 496 → один
  (v4-T5 leftover).
- Numerics: SoftmaxFix + QuantSafeUpdate → Numerics.lean (опция).
- Pretraining: Dust + DustAlign + DustMeasure → Dust.lean (−2).
- State/Views 66 и подобные micro — только если merge_module
  проходит с первого прогона (KISS: 1 fail → скип, записать).

### W5 scripts/: bench_bridge решение + lint-lib вердикт
- **bench_bridge.py 7 665 — ВЕРДИКТ: монолит сохраняется.** Каждый
  из 20+ режимов зафиксирован bench-мостами в Lean (cadence
  C442–C521); модульная нарезка даёт −1.5–2k строк, но parity-gate
  по 20+ режимам дороже выгоды. Разрешённый минимум: извлечение
  3–4 общих helpers (round_tern-клоны, json-запись, argparse) с
  golden-diff гейтом на затронутых режимах; 3 fails → откат в ноль
  и запись в tech-debt.
- _lintlib.py для 5 линтеров — НЕ делать (YAGNI: линтеры стабильны,
  дубли парсеров ~30–50 строк, пары script+test).

### W6 Docs: докстринг-словарь + STATUS/ALGORITHMS (docs-risk ≈ 0)
- Добить 8 nodoc до 0 (Budget/WeightedExpAlloc, External/Flywheel/
  SVD, Optimization/Momentum+RobbinsMonro, Probability/ChernoffCGF
  +EntropyConvexity+MomentBounds, Research/Legacy/AdvanceWitness,
  Unified/ParetoExecution).
- Докстринг-словарь (продолжение C511–C519): safe-step (канон
  Theory/SafeStep, прочие 1-строчные ссылки), merge/split/inject
  (Architecture), transfer-pattern (Model/Transfer — 1 раз),
  certificate-термины (Cert + Contracts), MWU/MirrorHedge,
  Freedman-семья, EM (Probability carrier vs Contracts trajectory).
- STATUS.md 7 003 → свернуть до ~1 500 + STATUS-archive.md
  (v4-T6 долг); ALGORITHMS.md 3 380 — дедуп описаний.

### W7 Опции (только после W1–W4 зелёных; каждый отдельным changeset)
- Oversized-нарезка разделами (без переноса деклараций):
  BatchCEBudgetGuard 2 394, Dynamics/GrowthBridge 1 450,
  System/GrowthState 1 234, Learning/SoftRouterMix 1 287,
  Ensemble/Hoeffding 944.
- Перегрузки имён (singularValues×9, Matrix×7…) — только словарь
  в докстрингах; полное переименование вне v5.

### W8 README + карта (финал)
- README canon-map: актуальная layer-карта LayerLint (сейчас
  прокомментирована в скрипте и не отражена в README), статус
  траншей W1–W7, honest-границы.

## Honest-границы v5 (что НЕ делаем и почему)
- External/ (Flywheel, MemT) и upstream/ — upstream-зеркала,
  правка запрещена (воспроизводится при sync).
- Research/ + Research/Legacy/ — карантин; замеры/выноски только
  docstring-уровня, код не трогаем.
- bench_bridge.py — монолит (см. W5); нарезка вне v5.
- Certificate-хабы (Model+Contracts cert-семья) — не сливаем
  (v4-урок deriv-риска).
- Step/SafeQP-контур — свежий, не трогаем.
- Island-монолиты (FannesPinsker, GibbsCore, EnergyReasoning,
  Audit) — не трогаем.

## Каждому траншу — чек-лист гейтов
1. `lake build` exit 0.
2. Freeze identity 8595 (`python scripts/Freeze.py` — identity
   unchanged).
3. DupLint/StatusLint/DocLint/NsLint по затронутым файлам.
4. Freeze-лог в `.tmp/C522/` (или траншевой `.tmp/Wx/`).
5. Atomic commit `refactor(Wx): <family> module consolidation`.
