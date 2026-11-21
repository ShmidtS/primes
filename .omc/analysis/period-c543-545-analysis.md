# Phase analysis: C543–C545 — эра доставки (delivery era) (2026-11-22)

Series HEAD 0105ed05a5ac5249430b37599703e79e4c836379 (C545;
`git log` проверен: 9f1b6762 C542 → 4da9a53b C543 → 82523562
C544 → 0105ed05 C545; tree clean). Виток закрыл roadmap-пункты
1–3 из C536–C541 анализа (port-proposal, адаптер×continual,
P3 interval-сертификат) и тем самым ПОЛНОСТЬЮ закрыл карту
внешнего плана C537: все формализуемые пункты поглощены и
доставлены потребителю. Freeze 8688.

## Commit one-liners (C543–C545)

- C543 4da9a53b `docs:` external plan port proposal —
  docs/PROPOSAL-external-plan.md (+196): P4/P1/P6/P8 теоремы
  C538–C541 → точные код-фиксы HAGI_v2 (gpu.py wd-проекция,
  EB-валидация, hash-consing, exact-bypass) с байт-точными
  Lean signatures и честными предупреждениями. Docs-only,
  freeze identity 8666.
- C544 82523562 `feat:` adapter continual isolation —
  Hagi/Theory/AdapterGrowth.lean (+148, ContinualIsolation) +
  scripts/bench_bridge.py (+320, --mode adapter-continual):
  структурная изоляция per-task адаптеров ⇒ forgetA = 0 ТОЧНО
  (adapter_per_task_sound, индукция без проекций/бюджетов);
  композиция с WeightDecayLeak (trunk_update_needs_projection).
  Bench (CONFLICT PIN): ISO 0 EXACT vs SHARED +0.233 vs
  TRUNK-NEG +5.576. Freeze 8666→8672 (+6).
- C545 0105ed05 `feat:` polar express interval certificate —
  Hagi/Optimization/PolarExpressCert.lean (+428): P3 внешнего
  плана — рационализованная 3-шаговая композиция p=ax+bx³+cx⁵
  переводит спектральный бокс [1/1000,1] ТОЧНЫМИ рациональными
  границами → финал [9/512, 1049/1024] ≈ [0.0176, 1.0244];
  метод: точные диапазоны монотонных кусков (Q(x²)-анализ:
  вершина/хорда/корни) + 1/1024-зазоры; негатив-контрпример
  (3,−5,1) — сертификат не vacuous. Freeze 8672→8688 (+16).

## (а) Внешний план полностью поглощён: 5/5 + доставка

- **Все формализуемые пункты карты C537 закрыты.** P4 wd-leak
  (C538), P1 EB 27.49× (C539), P6 OE 343→4 (C540), P8 zero-CE
  (C541), P3 polar-cert (C545 — единственный med-кандидат из
  «отклонённых» доожат как последний содержательный). Отклонённые
  P2/P5/P7 остаются эмпирикой/interval-работой вне ядра (P5 —
  см. roadmap).
- **Port-proposal доставлен (C543)** — инверсия моста завершена
  не только производством теории, но и её упаковкой для внешнего
  агента: 4 секции код-фикс↔FQN-теорема + honest-предупреждения.
  Прецедент PROPOSAL-*.md C466 соблюдён, PROPOSAL-index #6.
- **P3 с honest-коррекцией заявки.** Внешняя заявка
  [0.9564,0.9806] НЕ воспроизводится на полном старте [1/1000,1]
  (малые σ остаются малыми: p(0.001)≈0.004); сертифицирован
  честный финал [0.0176,1.0244] — верх в 2.5% от 1, взрыва нет.
  Матричный CosSim/−40% FLOP — честно за скобками (скалярный
  спектральный факт + поточечный перенос). Это второй случай
  после EB (41.5× vs 27.49×), когда primes-сертификат
  КОРРЕКТИРУЕТ внешнюю заявку, а не подтверждает её дословно:
  мост работает как фильтр, а не рупор.

## (б) Третья continual-стратегия: сравнительная таблица

| Стратегия | Механизм | Сертифицировано | Цена |
|-----------|----------|-----------------|------|
| Проекционная (GPM/A-GEM, Continual + C538) | P⊥-проекция шага на защищённом подпространстве | gpm_multi_zero_forgetting; wd-проекция ⇒ сохранение | проекция каждый шаг, потребность знать protected-базис |
| Гибрид (адаптер+trunk, C533/C536 линия) | общий trunk растёт/сжимается, адаптеры доучивают | merge-certified (Матрёшка, bound 6.6e-8) | trunk-конфликт между задачами остаётся (TRUNK-NEG плечо C544) |
| Структурная изоляция (C544, ISO) | per-task адаптеры, task i не трогает s i | adapter_per_task_sound: forgetA = 0 ТОЧНО, без проекций | r=1 × задачи параметров; B-прогресс только через свой адаптер |

- Bench-калибровка (107 live pts, CONFLICT PIN task B): ISO
  forgetA = 0 EXACT (bit-exact assert) vs SHARED +0.233 vs
  TRUNK-NEG +5.576 — три стратегии на одном trunk/данных/eta.
- Замечание: изоляция — единственная стратегия с ТОЧНЫМ нулем
  (структурно, не ε-гарантия); проекционная — единственная,
  допускающая trunk-обучение; выбор = trade-off «нулевой
  forgetting vs пластичность trunk». trunk_update_needs_projection
  (C544 × C538) формализует границу: без проекции trunk-шаг
  ОБЯЗАН ломать защищённый выход.

## (в) Метрики витка (замер HEAD 0105ed05, READ-ONLY)

- **Freeze verify**: PASS, 8688 declarations (8666 → 8688,
  +22 за C544–C545: 6 ContinualIsolation + 16 PolarExpressCert;
  C543 — identity), 0 aliased, 0 потеряно (receipts).
- **Index**: 541 modules (C544 ReachLint 540; C545 +
  Optimization/PolarExpressCert → 541).
- **Streak посадок**: C541 = 84 → C545 = **88** (C542–C545
  сплошная нумерация, freeze PASS на каждой; выведено из
  нумерации, отдельного streak-файла нет — honest note
  прецедента сохраняется).
- **Гейты** (receipts): lake build PASS (19353 jobs), Freeze,
  TestFreeze, TestMergeModule (20), LayerLint, NsLint, DocLint,
  DupLint, StatusLint, TrivialLint, ReachLint, STMDUP,
  MachineDiffTest, AssumptionScan+Test, PremiseRegistry+Test,
  AllAxiomCheck (+regression), ChallengeCheck 2/2, MathlibPin
  fc4f59e5 — все PASS, allowlist не тронуты; аксиомы по-прежнему
  только propext/Quot.sound/Classical.choice.

## (г) Re-check HAGI_v2 (READ-ONLY, C:\HAGI_v2)

`git log --since='2026-11-22 01:00'` (посадка C543 01:02):
**пусто** — внешний агент port-proposal ещё НЕ применял, новых
мостов из внешнего кода нет. Последний их коммит — wave204
(b3508ab, 21.11): RoPE-фикс, PAIRED regression gate,
certified_argmax ties. Тишина второго витка подряд после wave204.
Кандидат на реакцию: применение PROPOSAL-external-plan.md —
тогда recheck обязан проверить их фиксы против наших посылок
(EB σ̂-runtime, OE полнота относительно проб, gate exact p=0).

## (д) Roadmap ≥5 rank к цели «max качество, min объём, min вычисления»

1. **HAGI_v2 recheck на port-proposal** (quick, дёшево) — если
   внешний агент применил proposal: сверить их фиксы с Lean-
   посылками (σ̂, проба-полнота, p=0-edge); если нет — пустой
   recheck, идти дальше (не блокер).
2. **Мини-HAGI: полный цикл в одном прогоне** (feat, high
   value) — сборка микро-саморазвивающейся системы из ГОТОВЫХ
   certified-блоков: exact-bypass (C541) + адаптеры
   (grow/merge/ISO C532–C536/C544) + snap (C521) + OE-поиск
   (C540) + EB-гейты (C539). Не новые теоремы, а композиция
   канона — проверка, что блоки СОВМЕСТИМЫ в одном loop
   (bench_bridge --mode mini-hagi). Это переход от «теорем о
   компонентах» к «теореме о системе».
3. **Paper-обновление** (writing) — вставить в docs/paper-draft.md
   эру доставки: внешние числа (−75% Матрёшка, EB 27.49×,
   OE 343→4, ISO 0 EXACT vs 0.233/5.576, polar [0.0176,1.0244]
   с honest-коррекцией заявки) + инверсию моста как narrative.
4. **P5 TIES-merge теорема** (med) — последний med-кандидат
   карты C537: sign-majority + row-norm при disjoint-поддержках;
   связка MergePrice/AlignedMerge; внешняя U-кривая H_leaf*=8
   как калибровка.
5. **Palomar-карточки для новых теорем** (quick) —
   PolarExpressCert и ContinualIsolation в карточный индекс
   паломар-формата, если инфраструктура карточек жива (иначе
   YAGNI-отказ с формулировкой).

Top-3 на следующий виток: (1) мини-HAGI full-loop (главный
шаг к системной теореме), (2) HAGI_v2 recheck (дёшево, обязано
по процедуре), (3) paper-обновление (закрепляет эру доставки).

## Honest limits (процедурные)

- Freeze/streak/гейты — по receipts `.tmp/C54*/receipt.md`,
  READ-ONLY (lake не запускался — виток аналитический).
- Streak 88 выведен из сплошной нумерации C541=84 → C545;
  отдельного чек-файла streak нет.
- Числа 0.233/5.576/0-EXACT, [0.0176,1.0244] — bench/
  Lean-сертификаты canonical-шкалы; сравнение стратегий —
  на одном CONFLICT PIN-плече, не универсальный benchmark.
- HAGI_v2 re-check — READ-ONLY по git log; применение
  port-proposal внешним агентом не проверялось runtime'ом.
- Roadmap 2–5 — проекты, не результаты; мини-HAGI-совместимость
  компонентов не сертифицирована до реализации.
