
### Цикл 53 (empirical closure): две явные модели выведены
- `scalarQuadraticKl`, `forgetting_kl_quadratic_unit_fisher` и
  `tldr_two_tier_safety_unit_fisher`: получена собственная кривизна
  identity map, не переданная как эмпирическая гипотеза.
  Сохранённые внешние условия — невязка dW² и нулевой kernel
  адаптера B. Произвольная F/распределительная KL не закрыта.
- `mopd_kl_scaling_warning_fivefold`: в fixed 5x модели исходная
  scaling-посылка выполняется rfl, остаётся только экономическое
  ограничение 5·Dbase·ε ≤ 1. Универсальный масштаб НЕ выводится.
- Политика Freeze: исходные theorem statements сохранены без
  переписывания binder сигнатур. Поэтому AssumptionScan остаётся
  137: это честное class closure, а не числовая имитация cleaning.
- Четыре #print axioms и численные probes прошли, узкие targets
  обоих модулей собираются. PolicyCompatibility нормализован
  CRLF→LF для git diff --check; Freeze подтвердил 4167 declarations,
  ни одного lost/aliased/изменённого старого результата.
- Независимый review: LGTM по моделям и binder closure. Его
  единственное Low-замечание — случайный draft-счётчик `935/137?` —
  исправлено. Проверенный registry: 45 файлов/137 вхождений.
- Полный CI повторно PASS (4167 declarations). Оставшиеся общие
  premise interfaces не объявляются аналитически закрытыми.

### Цикл 52 (HB state-to-spectrum): исходная пара замкнута
- `hb_pair_second_order_complex`: точная комплексная форма старого
  скалярного вывода, free coefficient β+η(1−β) сохранён и НЕ
  спутан с канонической линейной рекуррентой с free coefficient β.
- `hb_pair_l2_initial_gap_bound`: производная по координате вторая
  рекуррента передаётся в cycle-51 root-gap bound. Заявленное
  вычисление стартует с first-order error/velocity, а НЕ с
  условия второго порядка с произвольными коэффициентами.
- `hb_pair_orthonormal_initial_gap_bound`: базисная норма и e/v
  представления подключены напрямую, нет свободного spectral-existence
  вывода или κ-оптимальности в формулировке.
- Probe выбран η=0,β=2, поэтому е=((2^n+1)/2),
  v=2^n/2: первичные равенства ядра исполнимы, roots 2,1 и gap 1
  численно подтверждены. Это НЕ стабильный обучающий экземпляр
  и не демонстрация сходимости, а только честный sanity probe.
- Production diff сфокусирован в 88 additive lines; узкая сборка
  и все три `#print axioms` дали разрешённую стандартную тройку.
  AssumptionScan остаётся 137: lock не «закрыт» через новые мосты.
- Независимый review: LGTM по коэффициентам, преобразованиям Complex
  и норме базиса. По его замечанию описание probe дополнено явным
  отказом от claim устойчивости/сходимости: beta=rho=2 и темп 2^n.
- Полный CI: PASS; Freeze=4163 declarations, 418 модулей.
  Дальше — действительное аналитическое закрытие premise binders,
  а не расширение HB-примитивов без уменьшения empirical классов.

### Цикл 51 (HB coefficient root-gap): A/B больше не свободный вход
- `hb_distinct_root_coefficient_sum_bound`: треугольные границы
  числителей A/B, затем монотонность деления по нижней границе gap;
  направление деления проверено kernel-сборкой.
- `hb_two_root_l2_initial_gap_bound`: явные A/B из начальных e₀,e₁
  подставлены в weighted L2 ряд. Базисный перенос и κ-связь исходной
  пары НЕ выдаются за закрытые этой теоремой.
- Положительная нижняя gap делает именно знаменатель ∥λ₁−λ₂∥
  ненулевым; Jordan-режим с одним корнем этой гипотезе не отвечает.
- Одномодальный probe: A=B=1/2 как проверка явных коэффициентов,
  векторная ошибка ограничена 7·2^n; axioms чисты у обеих сущностей.
  Коэффициент консервативен, его оптимальность не заявляется.
- Независимый refute-first review: LGTM. Направление деления,
  согласованность A/B и восстановление e₀,e₁ отдельно проверены;
  отмечен рост консерватизма при малом gap, а НЕ ошибка оценки.
- Полный CI: PASS; Freeze=4160 declarations, 418 модулей,
  0 sorry, AssumptionScan=137, все ALLAXIOMS/CHALLENGE чисты.

### Цикл 50 (HB weighted L2): убран uniform-only rate
- `hb_two_root_l2_weighted_bound`: индивидуальные ρ_i стоят
  непосредственно внутри квадратичной суммы. Знаковый край rho
  не требует новой гипотезы, поскольку общий sqrt-фактор не выносится.
- `hb_two_root_orthonormal_weighted_bound` переносит сумму в
  исходное пространство с полным ортонормированным базисом.
- Двухмодовый probe получает sqrt((2^n)^2+((1/2)^n)^2),
  а не только более грубый sqrt(2)·2^n. Empty probe также прошёл.
- Дополнительного hrho нет; hnorm1/2 сохраняют точные модальные
  ограничения, initial data по-прежнему передаются по модам.
  Достижимость верхней оценки не объявляется.
- Независимый review повторно скомпилировал probes и дал LGTM;
  математических контрпримеров или doc-caveat не найдено.
- Полный CI: PASS; Freeze=4158 declarations, 418 модулей.
  Оставшийся параметрический шаг — оценка C_i через root gap.

### Цикл 49 (HB vector L2 assembly): координаты → пространство
- `hb_two_root_l2_bound` доказывает сборку finite modes с
  общим коэффициентом sqrt(sum((‖A_i‖+‖B_i‖)^2)).
  Суммируются квадраты, sqrt((ρ^n)^2)=ρ^n использует данное ρ≥0.
- `hb_two_root_orthonormal_bound` переносит результат через
  `OrthonormalBasis`: сохранение нормы не теряет базисный коэффициент.
- Self-adjoint existence НЕ подменено двумя lines of proof:
  корни и начальные данные передаются в модальных координатах.
  Spectrum API найден для следующего этапа, но не скрыт в ложной
  универсальной теореме оптимизации.
- Двухмодовый probe использует реальный EuclideanSpace.basisFun,
  корни 2,1 и 1,0; результат sqrt(2)*2^n исполнен успешно.
  Все новые declaration axioms: только стандартная тройка.
- Независимый refute-first review: LGTM по algebra/geometry.
  Единственное замечание низкой severity устранено: базис полный,
  не произвольное неполное ортонормированное семейство.
- Полный CI: PASS; Freeze=4156 declarations, 418 модулей,
  AssumptionScan=137, все аксиоматические проверки чисты.
- Открытый следующий результат: модально-зависимые ρ_i внутри
  sqrt-суммы и усиление коэффициента через root separation/κ.

### Цикл 48 (HB positive discriminant): полный скалярный спектр
- Реализованы `hb_two_root_norm_cap`, `hb_real_root_pm`,
  `hb_real_root_pm_norm` и `hb_real_two_root_norm_bound`.
- Математическое следствие: для D≥0 оба вещественных корня
  подчинены одной верхней экспоненте `((|t|+√D)/2)^n`;
  между D>0 и D≤0 больше нет неформального смешивания темпов.
- Triangle-оценка НЕ объявлена точным max modulus; исходная
  двухкорневая форма остаётся доступной для более точных оценок.
- Корни 1,2 проверены исполняемым probe, база 2^n получена
  из теоремы. Аксиомы всех четырёх новых declarations чисты.
- Итоговая теорема траектории не требует D≥0 отдельно:
  граница корректна при любом sqrt (неотрицательном по определению)
  и переданных корнях; квадратная корневая формула D≥0 требует.
- Независимый refute-first review: LGTM по алгебре всех четырёх
  теорем. По замечаниям низкой severity уточнены docstrings:
  различность корней не требуется, при D=0 Jordan-слагаемое отдельно,
  оценка sqrt-выражения при D<0 не утверждает существование корня.
- Полный `bash scripts/ci.sh`: PASS, включая CHALLENGE и ALLAXIOMS;
  Freeze=4154 declarations, 418 модулей, 0 sorry.
- Незавершено: сборка ортонормированных режимов векторного
  оператора и оценка коэффициента через число обусловленности.
  Новых неформализованных скалярных second-order случаев нет.

### Аудит-3 (Tech Debt Management): верификация фактов и Фаза 4.2
- Утверждение «QuadMachine — скаляр f(x)=ax²» — ЛОЖНО: quadE/quadCert/
  quadStepCert работают над k → ℝ (произвольная размерность, Fintype k);
  тернарный квантователь qTern также k-мерный (TernaryExact).
- «MasterHAGI*/GrandSynthesis — мёртвый Gen-1 код, effort-1 удаление» —
  НЕВЕРНО по effort: MasterHAGI потребляется 12 модулями; GrandSynthesis
  несёт реальную takeoff-математику (де-паден в 2dc3a31). Удаление —
  зависимостная хирургия, требует отдельного решения.
- «изолированные острова неравенств не участвуют в цикле роста» — ЧАСТИЧНО
  устранено РАНЕЕ (quant_energy_bridge, PinskerTV-мосты) и в этом проходе:
- Фаза 4.2 ВЫПОЛНЕНА конструктивно: Hagi/Unified/TernaryWitness.lean —
  СОСТАВНОЙ многомерный свидетель, связывающий острова:
  quantOpt_energy_bound: тернарно-квантованный оптимум многомерной
  квадратичной цели имеет энергию ≤ k·s²/8 (выведено из пошаговой
  дисторсии qTern_error_in, НЕ постулировано);
  quant_jump_honest: для любого состояния с энергией выше потолка прыжок
  к квантованному оптимуму — HonestTransition с выведенным дропом
  (riskSpend/budgetSpend = 0: прыжок без ресурсных трат — модельный
  сценарий). Аксиомы: только [propext, Classical.choice, Quot.sound].
- TD-6 (удаление Freeze/линтеров) и TD-1 (удаление Gen-1), TD-2 (429→20
  файлов) — конфликтуют с действующими протоколами (Freeze-дисциплина,
  merge-before-delete, §1.3 запрет массовых переименований); не выполнены
  без явного решения пользователя.

### Аудит-4 (P0-5, P0-2): статус по коду
- P0-5 (многократная продуктивная траектория): УДОВЛЕТВОРЕН РАНЕЕ
  кодом — Examples/QuadLoopWitness.quad_loop_horizon: произвольный
  горизонт n, на КАЖДОМ шаге дроп = ¾·E(w_t) ВЫВЕДЕН из точного
  тождества quadE_half текущего состояния (эффекты state-dependent —
  именно тот тип свидетеля, который требует §5.2 аудита;
  two-step-inconsistensia Nonvacuity относится к СТАЦИОНАРНЫМ
  эффектам, а не к пересчитываемым).
- P0-2 (grad привязан к функции потерь): ДОБАВЛЕНО
  (DescentCoreQuad.quad_eta_identity / quad_eta_descent): для
  квадратичного носителя градиент — ИСТИННЫЙ градиент quadE
  (quadGrad), точное тождество E(w−η∇E) = (1−η)²·E(w), спуск
  выводится ИЗ ОДНОГО диапазона 0 < η < 2 (измеримый выбор шага),
  без h_emp/hcond-посылок на спуск.
- P0-1/3/4 (StageEffects, протокол измерений качества, развязка
  gain/energy/capability) и P1–P3 — открытые крупные блоки;
  планы аудита-4 совместимы с фазами A–D действующего плана.
- Воспроизводимость (§10 аудита-4): подтверждено — lakefile.toml и
  lean-toolchain несут локальные абсолютные пути Windows;
  BUILD_REPROD.md описывает ручную замену; полная портируемость —
  отдельная инфраструктурная задача.

## Аудит #6 (RCDL-синтез, 2026-11-02)

Верификация фактов аудита:
- D1 «чужеродная библиотека Primes/ (2.2k строк)» — ОПРОВЕРГНУТО:
  каталог Primes/ в репозитории отсутствует (ls корня: только
  Hagi/, Challenge/, audit/, scripts/). Аддитивной комбинаторики
  в сборке нет.
- «dual identity уже доказан» — ОПРОВЕРГНУТО: дуального тождества
  RCDL в репо не было; формализовано теперь (RCDL.dual_apply).
- «HonestTransition/certified_loop тавтологичен» — ПОДТВЕРЖДЕНО
  частично: телескоп — честная индукция; не-тавтологичная часть
  (реальный GD-спуск) теперь в ToyTrajectory (honest_step_cert,
  traj_energy_explicit).
- MasterHAGI*/GrandSynthesis deprecated — уже зафиксировано ранее.

Выполнено (цикл 5, коммит ниже):
- Hagi/Learning/RCDL.lean: dual_apply (дуальность слой↔attention),
  expw/weightedSoftmax/gauge_shift (gauge-инвариантность со
  сдвигом значений; посылка ненулевого знаменателя — честная).
Осталось из синтеза: negative-weight gauge-выбор b_t (теорема
существования сдвига с ⟨g, s+b⟩ > 0); FOOF/Mesa-мост;
Hadamard-проекторы Π_m для изоляции доменов (частично есть в
Spectral-модулях).

## Исследовательские циклы 9–13 (2026-11-02, после аудита #6)

- Цикл 9 (FOOF): regCov/foofW + foof_normal_eq (W*C = VXᵀ) +
  foof_step_identity (W*−W₀ = (V−W₀X)XᵀC⁻¹ − λW₀C⁻¹) — мост
  Mesa/FOOF: second-order preconditioning одним шагом.
- Цикл 10 (RegCovPD): regCov_quad (точное тождество vᵀCv =
  ‖Xᵀv‖²+λ‖v‖²), regCov_posDef, regCov_det_unit — посылка
  обратимости FOOF стала теоремой при λ>0.
- Цикл 11 (TernaryPert): cs_dotProduct, frob_submul (‖Ex‖ ≤
  ‖E‖_F‖x‖), ternary_layer_pert (ошибка квантования слоя ≤
  √(mr/4)‖x‖) — критика «нет сквозной ошибки квантования»
  закрыта на уровне слоя.
- Цикл 12 (PertTelescope): outNorm_triangle, pert_comp_pair,
  lip_composition, pert_telescope (‖comp e x − comp p x‖ ≤
  nδLⁿ) — полная сквозная оценка квантованной сети.
- Цикл 13 (FOOFUnique): foof_normal_unique, foofW_unique —
  единственность аналитического оптимума Mesa/FOOF.

Примечание процесса: в черновиках циклов 9–13 несколько раз
проскакивали sorry-заглушки — все заменены до коммита, все
коммиты прошли sorry-гейт (rg=0). Ловушка Mathlib-снапшота:
one_le_pow_of_one_le' ведёт к unbundled-версии (MulLeftMono ℝ не
синтезируется) — 1≤Lⁿ доказывается локальной индукцией.

## TD-07 исправен (цикл 14, 2026-11-02)

scOf больше не сбрасывает риск: riskCost := c.riskSpend,
hRiskNonneg := c.hriskSpend_nn (реальный расход риска в
контракте). tc_step_of_stepcert и tc_consequence
переформулированы честно: итог ослаблён на Σ riskSpend
(раньше «Σ riskCost = 0» — скрытая потеря информации о риске).

## TD-04 верифицирован и закрыт (цикл 17, 2026-11-02)

Проверка аудита: «6 вариаций одного Water-Filling» —
ПРЕУВЕЛИЧЕНО. Реальный дубликат один: totalErrorFin
(WaterFilling) vs totalError (BitAlloc) — оба Σ c/2^b;
WaterFilling уже импортирует BitAlloc и делегирует (мост
доказывался inline rfl). Добавлен публичный мост
totalErrorFin_eq_totalError как API (merge-before-delete).
Остальные модули — РАЗНЫЕ модели, не дубликаты:
WaterFillingMoE (genMean/effectiveCapacity), RankBudget
(экспоненциальный ранг-остаток), BatchCap (SFO-стоимость),
KVWater (KV-остаток с каппой).

## Аудит #7 (Claude/ChatGPT, 2026-11-04) — верификация и ответ

Верифицированные факты:
- TrainState.evaluate = S.qual, trainStep_evaluate_unchanged —
  ПОДТВЕРЖДЕНО (дизайн-решение: качество через канал
  measureQuality; известен с аудита #1).
- Локальный mathlib-путь в lakefile — ПОДТВЕРЖДЕНО (открытая
  инфраструктурная задача, аудит-4 §10; MATHLIBPIN-гейт в CI
  фиксирует commit 56a00585).
- Раздутость Unified (64 файла) — ПОДТВЕРЖДЕНО частично;
  LayerLint контролирует направления зависимостей.

Ответ P0-2/P0-3 (цикл 19, коммит ниже): TrainingTransition —
каноническая модель, где качество ВЫЧИСЛЯЕТСЯ из весов
(taskQual_is_computed, rfl), градиентный шаг реально убывает
суммарную энергию (taskStep_identity — точное тождество
E' = E − (2η−Tη²)/2·‖g‖²; taskStep_energy_descent), и
quality_changes_with_weights ОПРОВЕРГАЕТ инвариант
«trainStep не меняет качество» — в канонической модели
одно-задачный случай строго убывает.

Преувеличения аудита отклонены: «409 файлов/4.8МБ» включает
скрипты; DupLint/TrivialLint/AP-check уже в CI и PASS.

## Аудит #8 (2026-11-05) — верификация и немедленные исправления

ПОДТВЕРЖДЕНО и ИСПРАВЛЕНО (коммит ниже):
- «StatMech/Hopfield/{Concentration,LowerBound,CharPatterns}
  вне импорт-замыкания Hagi.lean, lake build их не собирает» —
  ДА: wiring-чек циклов 28–30 ошибся подстроками
  (GibbsConcentration дал ложный PASS для Concentration;
  LowerBound/CharPatterns/SubMemory не были добавлены).
  Исправлено: импорты добавлены, создан scripts/ReachLint.py
  (гейт достижимости всех 414 модулей из корня), встроен в
  ci.sh первым шагом — повторение невозможно.
- «OptimalConfig: доказана алгебра, но не сходимость со
  скоростью ρ; ни одна hb_* не используется» — ДА. Начато
  закрытие: Hagi/Optimization/HBRate.lean —
  hb_discriminant_interval ((1−√β)²≤ημ≤(1+√β)² ⇒ D≤0),
  hb_root_modulus (корни λ²−tλ+β: |λ|²=β при D≤0 — через
  разбор re/im, без виеты), hb_cfg_rate (β=ρ², η=(1−ρ)²,
  мода μ=1: |λ|²=ρ²). Историческая добавка «каждый шаг
  умножает ошибку моды ≤ ρ» была неверна: кратный корень
  даёт Jordan-фактор; она исправлена в коде циклом 43.
  Расширение на спектральный интервал мод — следующая
  итерация (hb_discriminant_interval применяется покомодно).

ПОДТВЕРЖДЕНО частично (пункты плана, требуют поэтапной
работы, не одной итерации): плоские сертификаты GrowthState
(energy — поле), TaskState-остров, 8 состояний, >10
сертификатов, h_emp-посылки (инвентаризированы
AssumptionScan), параллельные API ожиданий, OptimalConfig-структура
не используется как структура (функции cfg* используются).

ОТКЛОНЕНО: «HadamardParseval не в замыкании» —
Learning/Hadamard* подключены корректно (ReachLint PASS
подтверждает все 414 модулей); «Freeze 4127 не видит новые
модули» — Freeze сканирует файлы, числа корректны.

## Исследование → формализация → анализ, цикл 42 (2026-11-05)

- **Исследование.** ask.sciencemadereadable.com по large-step
  logistic GD: Wu et al. (`10.48550/arxiv.2402.15926`) и Meng
  et al. (`10.48550/arxiv.2406.05033`) подтверждают потенциал
  больших шагов, но также осцилляции/циклы вне нашей модели.
  Альтернативы CertStep-мостов и HB-траектории отложены:
  точный scalar спуск даёт новый алгоритм без новых посылок.
- **Формализация.** `logitCE_strictAnti`, `descent_step_strict`,
  `logitStepCertExact`, `logitStepCertExact'` и
  `logit_exact_drop_dominates` в `Unified/LogitCert.lean`.
  Любой η > 0 допустим только для scalar one-example CE;
  drop равен фактической разности CE, поэтому на исходном
  диапазоне 0 < η ≤ 2 старая оценка доминируется без
  изменения её frozen-формулировки.
- **Независимый refute-first аудит.** PASS с границей:
  доминирование сохраняет η ≤ 2; контрпример w=0, η=10 даёт
  oldBound=1.25 > exactDrop≈0.68643. Двухпримерная сумма
  `logitCE w + logitCE (-w)` опровергает универсальный
  large-step перенос. В коде кванторы остаются scalar.
- **Проверка.** `lake build Hagi.Unified.LogitCert` PASS;
  `#print axioms` для пяти declarations — только propext,
  Classical.choice, Quot.sound; Freeze 4131, DupLint/NsLint/
  DocLint/LayerLint/STMDUP/AssumptionScan/StatusLint/ReachLint
  и regex-TrivialLint PASS. Полный `bash scripts/ci.sh` —
  CI: PASS (включая CHALLENGE, MACHINEDIFF и ALLAXIOMS).
  `sorry/custom axiom`: 0.
- **Что следует.** Точный drop максимален среди допустимых
  `actualDescent`-сертификатов того же перехода: больший drop
  нарушил бы определение. Это улучшение сертификата, не доказанное
  ускорение общей логистической сходимости.
- **Retro.** Сначала проверять точную монотонность исполнения,
  и только затем гладкостную оценку: кап из descent lemma не
  всегда является ограничением реального алгоритма. Отдельный
  ревьюер обязателен: именно он остановил ложное снятие η ≤ 2
  из теоремы доминирования.
- **Следующий frontier.** HB: от модулей корней к траектории;
  кратный корень требует Jordan-член `(t+1)·ρ^t`. Затем
  многопараметрический LogitCert с нормой входа или measured
  commit/hold вместо незаконного переноса scalar-аргумента.

## Исследование → формализация → анализ, цикл 43 (2026-11-05)

- **Исследование.** Heavy-ball trajectory по научным источникам:
  Badithela–Seiler (`10.23919/acc.2019.8814459`) и Dang et al.
  (`10.48550/arxiv.2401.06738`). Полный спектр сравнён с bounded
  critical case; выбран кратный корень как самый сильный пробел.
  `no reference:` общего Lean resolver линейных рекуррент нет;
  найдены только частные ArithmeticGeometric/Fibonacci.
- **Обнаруженный дефект.** Из herr/hvel старой пары следует
  `e(n+2)=(1+β−η)e(n+1)−(β+η(1−β))e_n`, а НЕ свободный
  коэффициент β. Пример η=2, β=0, e₀=1, v₀=0 даёт e₂=−1
  вместо ошибочного 1. Plan-review ошибочно принял β; прямое
  алгебраическое раскрытие и контрпример отменили его verdict.
  Старые statements не изменены; canonical model и старая
  pair-модель теперь явно разведены в документации.
- **Формализация.** `hb_pair_second_order` фиксирует настоящую
  pair-динамику; `hb_repeated_root_form_solves` — witness;
  `hb_repeated_root_closed_form` — формула `(C+D·n)ρ^n`;
  `hb_critical_trajectory_bound` — явная Jordan-оценка.
  Старые root-only комментарии о pure ρ^n исправлены; никакого
  утверждения полного спектра или векторной сходимости нет.
- **Проверка.** `lake build Hagi.Optimization.HBRate` PASS;
  `#print axioms` четырёх declarations — только propext,
  Classical.choice, Quot.sound; Freeze 4135, DupLint/DocLint/
  STMDUP/LayerLint/AssumptionScan PASS; полный
  `bash scripts/ci.sh` — CI: PASS, включая ALLAXIOMS;
  `sorry/custom axiom`: 0.
- **Refute-first итерация.** Независимый финальный аудит нашёл
  завышенную фразу «в обе стороны» при ρ=0, старый claim
  «скорость достигается» и неиспользуемый `_h1 : ρ < 1`.
  Исправлены docstrings и новая сигнатура: оценка теперь
  верна при любом ρ > 0; ρ < 1 остаётся лишь условием
  затухания в алгоритме.
- **Что следует.** Spectral radius не есть per-step factor:
  `e_n=nρ^n` даёт отношение `((n+1)/n)ρ > ρ` и не ограничено
  никакой `Kρ^n`. Поэтому вычислительный stop принимает только
  явный RHS `( |e₀|+|D|n )ρ^n ≤ ε`, а не чистую экспоненту.
- **Retro.** Динамику надо исключать из исполнения алгеброй
  до вызова готовой спектральной теоремы; reviewer disagreement
  разрешается контрпримером, а не большинством или уверенностью.
- **Следующий frontier.** Различные корни внутренней моды:
  `e_n=Aλ₁^n+Bλ₂^n`, затем общая оценка внутри spectral
  window и векторная сборка по ортонормированным модам.

## Исследование → формализация → анализ, цикл 44 (2026-11-05)

- **Исследование.** Следующий frontier из 43: различные корни
  `Aλ₁^n+Bλ₂^n` без незаконного деления и без претензии
  векторной сходимости. Научная рамка та же HB-линия;
  `no reference:` общий MathLib resolver не найден.
- **Формализация.** `hb_two_root_form_solves`,
  `hb_two_root_closed_form`, `hb_distinct_root_init`,
  `hb_distinct_root_explicit`, `hb_two_root_norm_bound`,
  `hb_two_root_common_norm_bound`,
  `hb_two_root_spectral_norm_bound`. Различность требуется
  только для явных коэффициентов; нулевой корень допустим.
  Корневые модули через `hb_root_modulus` замыкаются в
  `(‖A‖+‖B‖)·(√β)^n` для двухкорневого разложения.
- **Проверка.** `lake build Hagi.Optimization.HBRate` PASS;
  все семь #print axioms — только propext/Classical.choice/
  Quot.sound; Freeze 4142, DocLint/DupLint/STMDUP/LayerLint/
  AssumptionScan PASS. Untracked probe инстанциировал
  вещественные 2/3, нулевые 0/1 и комплексные i/−i случаи.
  Полный `bash scripts/ci.sh` — CI: PASS, включая ALLAXIOMS.
- **Что следует.** При различных корнях Jordan-фактора нет;
  при кратном он обязателен и доказан в 43. Критический и
  осцилляторный D≤0 случаи закрыты; D>0 требует отдельной
  оценки по большему модулю вещественных корней.
- **Retro.** Общие формулы сначала доказываются без
  различности/диагонализуемости; ненулевой знаменатель и
  Jordan-случай выделяются ровно там, где математически нужны.
- **Следующий frontier.** Сначала D>0 и max-модуль двух
  вещественных корней, затем векторная сборка коэффициентов
  по ортонормированным модам; недопустимо обещать единый
        `(‖A‖+‖B‖)` без конечной суммы по спектру.

## Исследование → формализация → анализ, цикл 45 (assumptions)

- **Запрос.** Проверить аналитический вывод всех записей
  `scripts/assumptions.lock`. Полная 45-файловая матрица:
  `audit/assumption_closure.md`.
- **Новое доказательство.** `pl_stop_certificate_quadratic`
  выводит PL-форму для `E(w)=μ(w−a)²/2,L*=0`: обе части
  совпадают, `h_emp_pl` в канонической модели не нужен.
- **Исправленный overclaim.** `EmpiricalPremises.holds` не
  выводит `hsmooth`: theorem принимает `hsmooth` явно;
  `premises_lip_witness` доказывает только неотрицательность.
  Module/function docstrings приведены к фактическим типам;
  заодно удалён phantom `h_emp_smooth` lock-entry из комментария,
  не бывший binder (138 → 137 identifiers).
- **Граница.** PPT/stationary dist, noise independence,
  martingale variance, Landauer physics, Qgen/fit и synthetic
  telemetry — внешние модельные данные. Доказательных
  counterexamples к их универсальному выводу не добавляем;
  по типам они исходные параметры. Переименование premise
  не засчитывается как закрытие.
- **Проверка.** Узкая сборка Grow PASS; Freeze 4143,
  DocLint/STMDUP PASS. Полный `bash scripts/ci.sh` — CI: PASS,
  включая AssumptionScan 137 (5 proved + 132 premise binders)
  и ALLAXIOMS.
- **Следующий frontier.** Подключить операциональные
  инстансы к `CertStep`, оставив физические и вероятностные
  исходные значения именованными trust boundaries.

## Исследование → формализация → анализ, цикл 46 (CertStep)

- **Результат.** Три операциональные модели сведены к ядру
  `CertStep`: `logitStepCertExactCore`, `ncMinimalStepCert`,
  `trainStepMinimalCert`. Их drop вычислен из точного
  исполнения; новых `h_emp_*` — ноль.
- **Граница успеха.** Это закрытие операциональных инстансов,
  не удаление внешних premise из общих классов. Stage smoothness
  по-прежнему требует модели E; probability/physics/telemetry
  остаются внешними. AssumptionScan не изменился: 137.
- **Проверка.** Три узкие сборки PASS, `#print axioms` всех
  новых declarations — только propext/Classical.choice/
  Quot.sound; Freeze 4146, DocLint/AssumptionScan PASS.
  Полный `bash scripts/ci.sh` — CI: PASS.
- **Следующий frontier.** Замкнуть computed growth/merge
  instances на общий HonestTransition, затем унифицировать
  StepCert-expansion без дублирования старых телескопов.

## Исследование → формализация → анализ, цикл 47

- **Computed growth.** `GrowthComputedCert.next/stepCert`
  превращает `growthQuad_step` в CertStep с drop
  `(1−(1−η)²)·E`; nonzero-веса и `0<η<2` достаточны.
- **Merge.** `mergeOperationalCertStep` даёт drop=`jensenGap`;
  `mergeStrictCertStep` выводит строгость из existing
  `jensenGap_pos_witness`, не из premise. Это фактические
  инстансы `grow/merge`, а не универсальные эмпирические законы.
- **Проверка.** Два target-таргета PASS, #print axioms четырёх
  declarations standard; Freeze 4150, 418 модулей,
  DocLint/STMDUP/LayerLint/AssumptionScan PASS;
  полный `bash scripts/ci.sh` — CI: PASS.
- **Следующий frontier.** Продолжить operational closure
  по классам, где уже есть точные переходы; внешние модели
  не объявлять доказанными "для полноты".
