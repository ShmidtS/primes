# Analysis of proved: C470–C472 period (2026-11-20, 3 commits, виток «мажорантная триада»: proven trunk + tight κ + Fisher-кривизна)

Series HEAD 1b29f8f88936c628cf54e48445afb595b3829aa3 (C472). Все 3
receipts terminal (`C470..C472_LANDED_RECEIPT_COMPLETE`, логи в
`.tmp/C470..C472`). Этот бит (C473) — READ-ONLY анализ + этот док +
freeze verify + index regen. Freeze verify на этом бите: **PASS,
8394 declarations, 41 aliased, nothing lost/changed** (совпадает с
C472-замером; «191 new» — против устаревшего declarations.lock, тот
же артефакт, что в C464/C469). Index regen (C473): exit 0, **558
modules / 12432 theorems / 4617 defs / 1188 noncomputable**;
статусы: Proven 477, Conditional 26 (к C469: +2 модуля —
ProvenTrunk + FisherQuant; +62 theorems, +11 defs, Proven
475→477; AdaptiveMajorizer расширен в существующем файле).
Axiom-профиль: propext / Classical.choice / Quot.sound (OK, без
дрейфа, TestAllAxiomCheck REGRESSION PASS в C472). Streak: **17
посадок подряд** (C456–C472 terminal receipts + аналитические
биты C460/C464/C469/C473), freeze PASS на каждом.

## Commit one-liners (C470–C472)

- C470 fb389f07 `feat:` fully proven lm trunk witness —
  Hagi/Theory/ProvenTrunk.lean (221 строк, layer 7):
  `provenBlocks = [certifiedRMSNorm, certifiedMLP, certifiedConvAtt]`
  на одном носителе, trunkLip выведен механикой
  blocksLip_eq_trunkLip, применён (без новой индукции), полный
  LM-lip headLip·trunkLip, причинность бесплатно. Числовой witness:
  V=Fin 4, Π = 6·9·2 = **108**. Структурных premises НЕТ — только
  data-параметры (g+G, ε>0, W₁/W₂, headLip).
- C471 29581e40 `feat:` tight kappa bound for variance majorizer —
  Hagi/Theory/AdaptiveMajorizer.lean (+644, только добавление):
  ТОЧНАЯ κ(R) = (e^R−1−R)/R², series-free, тройной-MVT
  (N(x)=e^x(x−2)+x+2 ≥ 0; κ монотонна; e^y ≤ 1+y+κ(R)y²). 18 новых
  деклараций; kappa_le_expR — новая константа доминирует C462
  всегда; порог dominance ослаблен R²/(8e^R) → R²/(8κ(R)).
  Выигрыш e^R/κ(R): 2.77× (R=0.5) … 11.24× (R=3).
- C472 1b29f8f8 `feat:` fisher curvature quantization bound —
  Hagi/Theory/FisherQuant.lean (411 строк, layer 7): ТОЧНАЯ
  second-order идентичность quadLoss, Gershgorin-диагонализация
  δᵀHδ ≤ Σcⱼδⱼ² (наивная диагональ ЛОЖНА — контрпример в
  research.md), fisher_quant_loss_bound(_opt) при g=0:
  ΔL ≤ ½Σcⱼεⱼ², fisher_beats_lipschitz + fisher_tolerance_mono
  (анизотропный выигрыш), изотропный pin — выигрыша нет (честно).

## (a) Матрица аудитов P/G (замер C473, READ-ONLY)

| Пункт | Статус | Основание |
|---|---|---|
| P1 adaptive majorizer | **ЗАКРЫТ** | C462 (Var-мажоранта) + C471 tight κ(R): порог ослаблен, константа точна |
| P2 Fisher-квантование | **ЗАКРЫТ** | C472 FisherQuant: кривизна вместо lip·ε_q, Gershgorin-диагонализация |
| P3 EF21-in-step | **ОТКРЫТ в цикле** | EF21-контрактивность в корпусе (EF21Quantizer, ErrorFeedback), но bench_bridge.py = train→tern-quantize→finetune — EF21-quantize ВНУТРИ шага в bench-цикле отсутствует (проверено rg по scripts/bench_bridge.py) |
| P4 функция-сохраняющий рост | ЗАКРЫТ | C450 (identityBlock) |
| P5 Hadamard-условие | **ОТКРЫТ (негатив запинен)** | hadamard_not_universally_incoherent — пин-негатив в корпусе (HadamardSpread/TernaryBridge docstring-pins); проверяемого условия когерентности в цикле НЕТ |
| G1 lip/causal блоков | ЗАКРЫТ (C465+C470) | атомы с выведенными константами + склейка в ствол Π=108; честный остаток — x-зависимый attention без value-bound (пин) |
| G2 ствол-мажоранта | **ЧАСТИЧНО** | ProvenTrunk-lip есть (мажоранта ствола), но JOINT trunk+head descent (композиция ProvenTrunk + adaptive majorizer как единая теорема спуска) — открыт |
| G3 Fisher | ЗАКРЫТ | = P2 (C472) |
| G4 adaptive | ЗАКРЫТ | = P1 (C462+C471) |
| G5 merge вне линейного | **ОТКРЫТ** | линеаризационный остаток: merge-теоремы покрывают линейный режим, нелинейный остаток не формализован и не измерен |
| G6 сквозная certify-then-commit | ЗАКРЫТ | C463 |

Итог: **из 11 пунктов (P1–P5, G1–G6, с G3=P2 и G4=P1 — 9 сущностных)
закрыто 6 сущностных** (P1, P2, P4, G1, G6, и частично G2).
Остаток: **P3 (EF21-in-step в bench), P5 (проверяемое
Hadamard-условие), G2-хвост (joint descent), G5 (merge вне
линейного)** — 4 пункта, из них P3 и G5 — измеримые в bench-цикле.

## (b) Метрики (C473, ground truth)

- **Freeze**: PASS, **8394 declarations** (8377 C471 → 8394 C472 =
  +17 FisherQuant; на C473 без изменений — READ-ONLY бит), 41
  aliased, ничего не потеряно/не изменено.
- **Index regen**: exit 0, **558 modules / 12432 theorems / 4617
  defs / 1188 noncomputable**; Proven 477 (+2 за виток:
  ProvenTrunk, FisherQuant), Conditional 26. Axiom-профиль
  стабилен.
- **Streak**: 17 посадок (C456–C472) + аналитические биты, freeze
  PASS на каждом.
- **Ф6-замер (fd/wc, C473)**: **38** файлов >1000 строк (37 на
  C469; +1 — AdaptiveMajorizer 644+… нет, под порогом; рост от
  Theory-добавлений витка) — ЦЕЛЬ А19 НЕ ДОСТИГНУТА по порогу
  <1000; инвариант «новые файлы ≤1500» соблюдён.
- **Heartbeats**: 25 `maxHeartbeats`-override в 16 файлах (замер
  C448-класс, перепроверен rg C473: 25/16) — к цели ≤400k далеко
  (топ 3×16M).
- **Bare imports**: 32 (последний полный аудит; транш 3 не начат).
- **Живая петля**: experiments/ отсутствует, selfloop_result.json
  не обновлялся (Nov 15) — внешний блокер сохраняется.

## (c) Целевая триада — статус после витка

- **Качество**: главный выигрыш витка. Tight κ ×2.77–11.24 (C471) —
  точная константа descent-мажоранты; Fisher-анизотропия (C472) —
  толерантность плоских координат c_max/c_min в ε-пространстве;
  ProvenTrunk Π=108 — первый полностью выведенный ствол,
  структурных premises ноль. Качественные гарантии теперь
  числовые, не интерфейсные.
- **Объём**: нейтрально-положительно: +2 модуля без мегафайлов
  (новые ≤644), Ф6-счёт 38 (+1) — хвост не растёт от Theory-линии,
  но и не сокращается; prune/tree-движения в этом витке не было.
- **Вычисления**: НОВОЕ — курируемый шаг η* = A/(2C) растёт как
  √(e^R/κ(R)) ≈ R при больших R (C471) и Fisher-бит-аллокация —
  чувствительным координатам больше бит (C472, монотонность
  формальна, оптимальность consumed из C389-механики). Это
  переносимая вычислительная премия порта C466.

## (d) Roadmap (≥6, ranked к цели — закрыть остаток P/G)

1. **P3: EF21-in-step в bench-цикле** — добавить EF21-quantize
   внутрь certified-шага bench_bridge.py (сейчас
   train→tern-quantize→finetune; EF21-контрактивность уже в
   корпусе — нужен bridge + сравнение с post-hoc). Измеримо сразу,
   закрывает P3.
2. **G5: merge вне линейного** — линеаризационная премиса как
   ИЗМЕРЯЕМАЯ: quantified residual (неединственность/офф-диагональ
   масса) в bench-цикле + честный pin нелинейного остатка.
   Измеримо, закрывает G5 в honest-форме.
3. **G2-хвост: joint trunk+head descent** — композиция ProvenTrunk
   (Π) + adaptive majorizer (κ) как единая теорема спуска LM;
   все ингредиенты доказаны, осталась склейка (аналог рецепта C470).
4. **Selfloop полный лог** — внешний блокер (experiments/
   отсутствует; проверять каждый виток). Разрядка waste→risk
   калибровки premise-форм C463 ждёт этот файл.
5. **A19-остатки гигиены** — imports транш 3 (32), heartbeats
   (25 override, топ 16M → ≤400k), Ф6 (38 файлов >1000). Дешёвые
   биты между крупными; держат rebuild-время.
6. **Без-возвратный holdout** (C435-пин) — неизвлекаемый
   holdout-канал для risk-ε C463; закрывает последнюю дыру
   доверия (d)-канала.

Top-3 на следующий виток: (1) P3 EF21-in-step в bench-цикле,
(2) G5 линеаризационный остаток как измеряемая, (3) G2 joint
trunk+head descent.

## Honest limits

- Матрица P/G: G2 закрыт лишь наполовину (мажоранта ствола есть,
  joint descent — нет); счёт «6 из 9» считает G2 частично.
- P5 закрыт только негативом: доказать ПОЛОЖИТЕЛЬНОЕ Hadamard-
  условие нельзя (контрпример есть), речь может быть только о
  проверяемом условии когерентности — дизайн не начат.
- Tightness κ: отрицательная сторона (exp_quad_neg) осталась на
  старой константе; κ(R) ≥ 1/2 — только нижняя грань.
- Fisher: чистая ½Σcⱼεⱼ² верна только у стационарной точки (g=0 —
  явная посылка); first-order член неустраним.
- Ф6-счёт 38 — замер fd/wc C473; Ф4/imports 32 — из прошлого
  аудита, не перемерялись (READ-ONLY бит).
- Freeze «191 new» vs нулевая нетто-дельта: declarations.lock
  устарел; при следующем bake обновить lock (тот же пин, что C464).
