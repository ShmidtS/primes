# Phase analysis: C484–C489 — реальная-данные эра конвейера (2026-11-21)

Series HEAD e060e4d7ae23fe45bcf2dafd1c09f99bb0076169 (C489;
`git log` проверен: db280c24 C484 → 25483406 C485 → 47b194e0 C486
→ 54b75a4a C487 → 185d0e14 C488 → e060e4d7 C489). Виток C484–C489
закрыл roadmap C486 ЦЕЛИКОМ (все 4 пункта: без-возвратный holdout,
большой continual, selfloop-intake-подготовка частично, рациональный
softmax) и перевёл certified-конвейер из «механика на игрушках» в
«статистика + continual + certified-CE на живом корпусе».

## Commit one-liners (C484–C489)

- C484 db280c24 `feat:` real dataset certified trunk bench —
  `--mode real-train`: 185 точек unified_ledger (READ-ONLY),
  trunk MSE 0.14823 → 0.12507 (точные Fractions), Hoeffding-мост
  теория↔данные.
- C485 25483406 `feat:` continual bench with gpm zero forgetting —
  ContinualBench.lean (freeze-пин), 2 задачи GPM: забывание 0 vs
  0.038 naive; gpm_bench_bridge — паттерн моста Lean↔bench.
- C486 47b194e0 `docs:` phase analysis c484-c485 — READ-ONLY бит:
  freeze verify 8471 PASS, index regen 564→565 modules (дрейф
  пойман), streak 28; roadmap ≥6 сформулирован.
- C487 54b75a4a `feat:` holdout concentration without replacement —
  HoldoutWithoutReplacement.lean (1340 строк, 56 декл): ГЛАВНАЯ
  holdout_wr_concentration — без-возвратная концентрация через
  freedmanD_tail_low (C438) + последовательностную машину
  (азума-тождество Дуба, телескоп-дисперсия σ̂²k(2N−k)/N); bench
  N=185/k=37/δ=0.05: ε_WR 0.23547 vs ε_Hoe 0.22327 — честный
  негатив: fpc-выигрыш на реальных данных НЕ достигнут
  (V'+ε = 0.278 > 1/4), (d) остаётся условной теоремой;
  gap_le_wr_bound — фактический гэп ≤ границы (держит).
- C488 185d0e14 `feat:` multi-task continual gpm accumulation —
  ContinualMulti.lean: T=3 задачи, GPM-НАКОПЛЕНИЕ базиса
  GS(входы 1..t), rank-трек 0→2→3→4 (206 входов задачи 3 дали
  лишь +1 — rank < Σ входов честно виден); gpm_multi_zero_
  forgetting (индукция по t) — ВСЯ прошлая диагональ матрицы
  забывания нулевая (точные Fractions); naive-контроль:
  0.0467/0.0266/0.2317.
- C489 e060e4d7 `feat:` certified rational softmax intervals —
  RationalSoftmax.lean (7 decl): expLower_le_exp /
  exp_le_expUpper ((1+x/n)^n ≤ e^x ≤ (1−x/m)^(−m), Fraction-
  friendly, выведено из Real.add_one_le_exp); rationalSoftmaxCert
  — sandwich lo v/∑hi ≤ softDef z v ≤ hi v/∑lo; certCE_le +
  certCE_gap (width-декомпозиция log((hi·∑hi)/(lo·∑lo)));
  sanity PASS (exact Fractions, .tmp/C489/sanity-softmax.log).

## (a) Реальная-данные эра: что закрыто, что осталось из суррогатов

Закрыто (living corpus 185→206 точек, READ-only, точные Fractions
всюду, где считает скрипт):

1. **Certified-обучение на живом сигнале** (C484) — trunk-лосс
   падает на реальных данных, границы предсказывают holdout.
2. **Полная статистика стоп-решений** (C487) — with-replacement
   Hoeffding (C435/C484) дополнен без-возвратной variance-
   adaptive концентрацией (Serfling-пин C435 закрыт честной
   формой); Ville-anytime уже в арсенале (C438-семейство).
3. **Continual-масштаб** (C488) — 2 задачи → 3+ с накоплением
   подпространств; zero-forgetting certified на любой длине
   последовательности; ранг-рост как измеримая метрика.
4. **Certified CE на пороге** (C489) — двусторонние рациональные
   exp-интервалы → softmax-sandwich → CE-мост: statement-слой
   готов, суррогатам C442/C481 предъявлена доказанная замена.

Осталось из суррогатов (честные пины, из receipts):

- **Bernoulli-монотонность** ((1+x/n)^n ↑ по n) — НЕ доказана
  (C489-пин): рост точности с n, m документирован, не
  сертифицирован.
- **C442 z²/Σz² и C481 L1-rms суррогаты не переписаны** — C489
  дал consumption-ready statements; bench-wiring cert-ce/trunk
  в scripts/bench_bridge.py — будущий бит.
- **fpc-применимость** — без-возвратная граница формально
  сильнее, но условие (d) на реальных данных не выполнено
  (C487-негатив): применимость C442 z²-суррогата к конкретным
  σ̂²-режимам корпуса остаётся эмпирической телеметрией.

## (б) Целевая триада-статус

- **Качество**: real MSE 0.148→0.125 (trunk) + certified-границы,
  holdout-статистика both flavors, zero-forgetting continual.
- **Объём**: тернарная сетка + EF21 + prune — арсенал прежних эр;
  continual-накопление C488 — новый объёмный рычаг (rank-трек).
- **Вычисления**: GPM-проекция стоит честной цены — задача B(3):
  loss после своей фазы GPM 0.348821 vs naive 0.176194
  (≈2× медленнее учиться через 1-мерное дополнение при rank 3→4);
  плата за всю нулевую диагональ забывания — зафиксирована
  числом, не риторикой.

## (в) Метрики витка (замер C490, READ-ONLY)

- **Freeze verify (HEAD e060e4d7)**: PASS, 8536 declarations,
  0 aliased, nothing lost/changed (.tmp/C489/gate-freeze-
  verify.log; 8471 на C486 → +65: C487 +56, C488 +2, C489 +7).
- **Index regen (C490)**: exit 0, дрейф пойман и закоммичен в
  этом бите: закоммиченный индекс (C486) 565/12530/4678/484-
  Proven; фактический **568 modules / 12694 theorems / 4691 defs
  / 1201 noncomputable, Proven 487** (+HoldoutWithoutReplacement,
  +ContinualMulti, +RationalSoftmax). Число 11778 из receipt C489
  — это ALLAXIOMS-счёт теорем (другой обход), НЕ дрейф индекса.
  Axiom-профиль: propext / Classical.choice / Quot.sound, без
  дрейфа. Паттерн дрейфа в feat-битах — 4-й раз подряд
  (C478, C479–482, C484–485, теперь C487–C489).
- **Streak посадок**: 28 (по C486) + C487 + C488 + C489 = **31**,
  freeze PASS на каждом; с посадкой C490 → 32 подряд (число 33
  из плана не подтверждается подсчётом по битам — фиксируем 31/32,
  а не подгоняем).
- **Bare imports**: **63** файла — без изменений, транш-4 не тронут.

## (г) Roadmap СЛЕДУЮЩЕЙ ЭПОХИ (ранжировано к цели: certified-цикл ≈ реальный цикл)

1. **cert-ce/trunk bench-wiring на рациональном softmax-sandwich**
   (C489 → потребление): замена суррогата C442 в bench-конвейере
   на rationalSoftmaxCert/certCE_le — первый certified-CE на
   реальных данных. Rank 1: statement-слой готов и sanity-PASS,
   объём минимальный, бьёт прямо в честный остаток (а).
2. **Полный LM-bench в одном прогоне** — trunk (C481) + grow
   (C444) + continual (C488) на ОДНОМ сплите живого корпуса
   (мини-HAGI на реальных данных): единая таблица
   качество/объём/вычисления триады. Rank 2: все компоненты
   существуют и прогонялись порознь — недостаёт только
   компоновки и единого отчёта.
3. **Selfloop полный лог (внешний recheck)** — experiments/
   selfloop-цикл с внешним лог-файлом как intake; проверяемость
   вне репо. Rank 3: внешний блокер, подготовка intake-формата
   внутренняя и дешёвая (пин с C486 №2).
4. **Bernoulli-монотонность + точная p̂-стратификация** — закрытие
   C489-пина (n-монотонность интервала) и стратификация p̂ по
   корпусу для conditional (d)-применимости. Rank 4: теоретическая
   гигиена после Rank 1.
5. **Imports финал (63 bare) + КРЕДО-остатки** — deriv-pin
   механика, компаунд-ускорение. Rank 5: гигиена.
6. **Паломар/Mathlib-upstream SVD-пакет** — внешний вклад
   (rank/SVD-машину continual-эры как Mathlib PR). Rank 6:
   внешний цикл, зависит от стабильности API C488.

Top-3 на следующий виток: (1) cert-ce bench-wiring,
(2) единый LM-bench прогон, (3) selfloop intake.

## Honest limits

- C487 негатив — не поражение, а граница применимости: σ̂² ≈ 0.0237
  на реальном корпусе не даёт fpc-кредита; телеметрия по будущим
  снапшотам корпуса покажет, типичен ли этот режим.
- C488 zero-forgetting — certified для GPM-машины (проекция +
  admission по измеренному drop); скорость обучения задачи B
  падает ≈2× — оптимум rank/скорости не сертифицирован.
- C489 — statement-слой без bench-потребления; ширина интервала
  при n=m=10 (gap 0.348 на sanity) велика — практичная точность
  потребует больших n, m (монотонность — пин, см. (г)-4).
- Freeze/index в (в): freeze — из C489-гейтов (HEAD тот же);
  index regen выполнен в этом бите C490 (READ-ONLY для кода,
  индекс + анализ — единственный диф).
