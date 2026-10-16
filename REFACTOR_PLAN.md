# REFACTOR_PLAN — код-уровневый аудит формализации HAGI

Метод: только код (`rg` по `namespace/theorem/def`, спорки через
environment-скрипт: `sorryAx`-содержащих деклараций — **0 из 788 041**
констант окружения модуля `Hagi`; BUILD + LINT/DOCLINT/LAYERLINT/
FREEZE/STATUSLINT — PASS на коммите 26834c5). Докстринги/комментарии
не использовались; всё ниже — сигнатуры и структура импортов.

## 0. Что фактически доказано (правда-карта по коду)

Проверяемые классы результатов (все — с каноническими аксиомами
[propext, Classical.choice, Quot.sound], sorryAx = 0):

1. **Концентрационный стек (L2, Probability)**: Azuma, Freedman
   (`Freedman.lean`), `finite_freedman`, history-Freedman:
   односторонняя фиксированная (`history_additive_freedman`),
   равнопороговая anytime-максимальная
   (`history_additive_freedman_maximal`, ×(T+1)),
   двусторонняя (`history_additive_freedman_two_sided`, ×2(T+1)),
   пороговая лестница (`anytime_freedman_thresholds`, R541),
   двусторонняя пороговая (`anytime_freedman_thresholds_two_sided`,
   R542), MarkovFreedman, AdaptiveSuccess.
   → Наиболее полный и самосогласованный стек репозитория.
2. **Фаннес-стек (L1+L6)**: `DiscreteFannes` (shannon/tvHalf/
   binEntropy), `FannesComplete.fannes_unconditional` (безусловная
   граница, R532), Nernst-композиция (`NernstFannes`, R539:
   S(p) ≤ t·log d + (1+t)h₂(t/(1+t)) при t = масса вне v*).
3. **Термодинамика (L2–L4)**: GibbsCooling (концентрация Гиббса,
   свободная энергия → E*), TopLevel.risk_budget_termination (R529),
   теpмо-конденсация: ThermoPrune.condensation_budget/
   thermo_prune_certificate, ThermoCondensation.
   condensation_epsilon_to_gap/thermo_condensation_full,
   AnytimeCondensation.anytime_condensation.
4. **Капстоуны (L6, Unified)**: `grand_synthesis` + `grand_synthesis_weak`
   (R540: пункты 2/4 выведены из пошаговых посылок),
   MasterHAGI/MasterHAGICoupled, ArchitectureTheorem.
5. **Свидетели nonvacuity**: Nonvacuity (S₀/S₁), HAGICertWitness
   (17 полей), `masterhagi_productive_witness` (R370, X = ℝ, K = Fin 1),
   `corePremises_trajectory_productive` (R369).
6. **Сертификация эмпирики (L2)**: CertifiedEstimator (Hoeffding-
   маршрут: prodE-факторизация mgf, hoeffding_tail/mean_tail/
   two_sided, certified_premise) + R517-лестница
   (union_bound_finite, max_bound_*, anytime_subgauss_*,
   anytime_safe_threshold).
7. **Гauge/интерпретируемость (L6)**: GaugeQuotient (R537/538:
   U(1)-действие, инвариантность r_G, relativeEquilibrium,
   rate-inheritance через Function.Commute), RecursiveClean,
   ModelComparison (MDL), CausalEffect, InterpretiveGrowth,
   NernstFannes.

## 1. Фальсификации (критический разбор по коду) и их статус

Ф1. **Гипотезы-передачи в капстоуне**: `grand_synthesis` принимал
    пункт 2 (`hrisk_bound`) и пункт 4 (`hqvec`) как плоские посылки —
    конъюнкция доказывает только то, что в неё вложили.
    Статус: **закрыто частично (R540)** — `grand_synthesis_weak`
    выводит 2/4 из `G t ≤ risk t` и монотонности; старый
    `grand_synthesis` с плоскими посылками остался в файле.
    Остаток: пометить deprecated или удалить (аргументы дублируются).
Ф2. **Бюджетная «неповышаемость»**: `budget T ≤ budget 0` выводится
    из `0 ≤ spend t` тривиальной арифметикой — это не теорема о
    модели, а свойство определения. Остаток: в мерже убрать из
    конъюнкций капстоунов (следствие hspend, а не содержательное
    утверждение).
Ф3. **`h_emp_*`-посылки (499 вхождений, 59 файлов)**: γ, ρ, β-константы
    входят как гипотезы. Мост certification есть только для
    парных маржинов (`certified_premise`); `h_emp_grow/smooth/lip` —
    не сертифицируются ничем. Остаток: либо модель выпуклости/
    липшицевости измерений (+ выборочная сертификация), либо
    явная ярлыковка «empirical axiom» в типе посылки (structure
    Premise с полем source : | measured | derived).
Ф4. **Дубли определений = риск расхождения**:
    - shannon: `DiscreteFannes.shannon` vs `DistillRecursion.shannonEntropy`;
    - tvDist: `PPT.tvDist` (mu/pi) vs `FannesSmooth.tvDist` (p/q);
    - tvHalf: `DiscreteFannes.tvHalf`;
    - ожидание: pmfMean (PMF) / prodE (произведение) / historyAdditive-
      семейство — три несвязанных исчисления ожиданий, мосты пишутся
      каждый раз заново (historyLaw_past_mean, prodE-факторизации).
    Это главный источник хрупкости: одно и то же неравенство
    доказывается в двух исчислениях независимо.
Ф5. **Anytime-лестница дублирована на двух базах**: CertifiedEstimator
    R517 (subGauss-CGF, q-форма) и history-Freedman (pmfMean-форма)
    имеют параллельные union-bound/exponent-каскады
    (max_bound_union vs pmfMean_event_union; anytime_subgauss_exp vs
    anytime_freedman_thresholds). Связка через общую абстракцию
    «вероятностная мера + событие» отсутствует.
Ф6. **Takeoff-семейство раздроблено**: 8+ файлов с собственными
    takeoff (Foundations/ConeTakeoff, GrowthDynamics, TakeoffCounted,
    Growth/TakeoffElasticity, T3Ignition, Dynamics/WallClockTakeoff,
    Probability/ConditionalSuccess, Unified/ArchitectureTheorem) —
    общая конусная алгебра (γk-геометрия) не вынесена в ядро;
    каждый файл переносит свои k·C₀ ≤ D₀-посылки.

## 2. План рефакторинга (фазы, приоритет: устранение дублей →
   сертификация посылок → упрощение капстоуна)

### Фаза A. Единый слой меры/ожидания (критично, разблокирует B–D)
A1. Ввести `Hagi/Measure/`: канонический
    `Expectation (μ : Finset-вес) (f) := ∑ v, μ v * f v` +
    `Prob (μ) (s) := ∑ v ∈ s, μ v`; леммы: mono, compl, union,
    linearity, Markov, Chebyshev — по одному разу.
A2. Мосты-дефиниции (не переименование с ломкой freeze):
    `pmfMean p f := Expectation (fun a => (p a).toReal) f`,
    `prodE p f := Expectation (prodDens p) f`;
    historyAdditive/counter — через общий SumFunctional.
A3. Перевод key-лемм: union_bound_finite и prodPq_mono/compl/
    union_le переписываются через A1 и становятся единственными
    (вместо параллельных q-форм и pmfMean-форм).
Критерий приёмки: FreedmanTwoSided/HistoryFreedman/CertifiedEstimator
собираются на одной базе; `rg "Finset.filter.*univ"` в Probability
падает до мостов.

### Фаза B. Энтропийное ядро (Information)
B1. Один модуль `Hagi/Information/Entropy.lean`:
    negMulLog, shannon := ∑ negMulLog, tvHalf, binEntropy +
    (fannes_upper, fannes_lower, superadditivity) — переносится
    из DiscreteFannes/FannesComplete (R532 ядро остаётся, но в
    Information-слое; L6-файлы импортируют его).
B2. DistillRecursion.shannonEntropy → переопределение через ядро
    (`shannonEntropy p := shannon p`) + lemma-мосты; PPT.tvDist и
    FannesSmooth.tvDist unify через tvHalf (знаковые суммы идентичны).
Критерий: `def shannon|def tvDist|def tvHalf` по одному разу
(grep-мосты разрешены).

### Фаза C. Takeoff/конус-ядро (Foundations)
C1. `Hagi/Foundations/Cone.lean`: запись ConeParams (k, γ, ρ, cbeta,
    dend-условия hdyn/hrhogk/hbeta'/hcone0) + теоремы-шаги
    (cone-preserving step, takeoff-by-induction
    C 0·(1+γk)^T ≤ C T — одна индукция для всех).
C2. Потребители (8 файлов из §1.Ф6) — только переупаковка гипотез
    в ConeParams + один вызов; без изменения заявлений могу сломать
    freeze — тогда через alias-мосты (`theorem takeoff_X ... :=
    Cone.takeoff _ params`).
Критерий: индукция-взлёт в коде ровно одна.

### Фаза D. Конденсационный кластер (Ensemble+Budget)
D1. Уже сгруппирован по namespace (R543); осталось unify посылок:
    condensation_budget (δ-девиация) → condensation_epsilon_to_gap
    (ε-бюджет) → anytime_condensation (α-уровень) — построить
    единый конвейер-теорему `condensation_pipeline : ε-budget →
    α-anytime-сертификат` в Budget,Consumers оstdaются частные
    шаги как леммы.
Критерий: цепочка вызовов линейна, нет копий одинаковых промежуточных
неравенств.

### Фаза E. Капстоун-гигиена (Unified)
E1. grand_synthesis (плоская) — удалить или пометить
    `@[deprecated grand_synthesis_weak]` (Ф1-остаток).
E2. Бюджетную тривиальность (Ф2) вынести из конъюнкций в отдельную
    лемму `budget_nonincreasing_of_nonneg_spend`.
E3. MasterHAGI/MasterHAGICoupled/ArchitectureTheorem — сверить
    пересекающиеся 17-полевые структуры сертификации; общий
    `TraitBundle` + проекции (если дубль полей >50%).
E4. h_emp_*-посылки: type-level маркер (Ф3) —
    `structure MeasuredConst (name : String)`/или класс, чтобы
    несертифицированные константы были видимы в типах заявлений
    (честность поверх freeze).

### Фаза F. Namespace-миграция (завершение фазы 7)
F1. Flat-остаток: Finish/Core/RealF3* уже сведён к Hagi.RealF3 (R544);
    Flywheel-файлы (Matrix.*, CourantFischer, WeylInequality,
    Kronecker*) — решение: НЕ мигрировать (внешняя математика,
    реиспользуемый стиль), зафиксировать в STATUS как конвенцию.
F2. Audit/EqualBudget, Exactness, Optimality → Hagi.Audit.* — уже
    директория-согласованы.

### Фаза G. Тонкие места/риски
- FREEZE: переименования = alias-записи; каждой фазе — отдельный
  коммит ( была проверена механика на R543/544: PASS без потерь).
- Не мигрировать Flywheel-ns (внешняя математика, Chesterton).
- Каждый шаг фаз A–E гоняет CI: build + LINT + DOCLINT + LAYERLINT
  + FREEZE + STATUSLINT, numstat-проверка по одному файлу,
  EOL-байтовый канон (в repo смешанные CRLF/LF, namespace-строки
  в старых файлах — LF).

## 3. Что исследовать дальше (после рефакторинга)
1. Сертификация h_emp_grow/smooth/lip: выпуклость/липшицевость
   измерений + выборочный Hoeffding (CertifiedEstimator готов как
   исполнитель).
2. Диагамма-пик Ω(n≈7.257) для континуального максимума —
   единственный недоказанный количественный калибр термостата.
3. Anytime-Freedman ↔ budget-телескоп: связать q-форму
   anytime_safe_threshold с CE-бюджетом (сейчас — два островка).

## 4. Верификация внешнего аудита (проверка по коду, HEAD e77dc61)

Внешний аудит (разбор ~230 файлов) проверен построчно. Вердикт:
часть тенденций подтверждена, ключевые P0-пункты — устарели или
неверны.

| Утверждение аудита | Код | Вердикт |
|---|---|---|
| «Нет канонического kldiv, каждый слой свой» | klDef в Prelude.Info;
 kldiv (Energy), kldiv (Variational), klDiv (Distill), KLdiv (DField)
 — ВСЕ через rfl-мосты к klDef (R297-стиль) | УСТАРЕЛО:
 дубли сглажены бриджами, отдельный файл не нужен |
| «Audit/ — ghost, удалить, риск низкий» | 22 декларации в 4
 файлах; внешних импортеров нет, но удаление = FREEZE LOST |
 ВЕРНО о ghost-статусе; УДАЛЕНИЕ опасно — нужен перенос
 деклараций или alias-план |
| «Удалить 185 export-блоков, низкий риск» | 185 файлов с
 export-блоками; short-name потребители по всему дереву |
 ОТКЛОНЕНО в P0-форме: это равноцатная перестройка ~300
 файлов; делать постепенно, по каталогам (с exists-проверкой
 build), не массово |
| «ProjectionMoments в Step» | файла нет ни в Step, ни где-либо |
 НЕВЕРНО (фантом) |
| «Growth=26, Step=25 файлов» | фактические: Growth=35, Step=42,
 Budget=21, Dynamics=9 | НЕВЕРНО количественно; тезис о
 перегрузке Step/Budget подтверждён, но масштаб больше |
| «ThermoCondensation → Ensemble» | R543: ThermoPrune уже в
 Ensemble; ThermoCondensation/AnytimeCondensation в Budget.
 Перенос философски оправдан, но направление слоёв
 Budget←Ensemble сохранится | Принято частично: аргумент
 семантический, не ломающий слои |
| «joint_stage_linked нарушает направления» | joint_stage в
 Foundations (L0/1), joint_stage_linked в Step (L3): Step
 импортирует Foundations — направление ЛЕГАЛЬНО по LayerLint |
 НЕВЕРНО (ложно-положительная cycle-тревога) |
| «5 формализаций энтропии не связаны» | Shannon/tv/kldiv имеют
 rfl/Prelude-мосты (R297, R547 shannonEntropy_eq_shannon);
 спец-формы (Spectral/LogDet/State) — РАЗНЫЕ объекты, а не
 дубли одного | УСТАРЕЛО/умозрительно |
| «h_emp_* нужно в Contract-слой» | 499 вхождений, 59 файлов;
 сертификация: CertifiedEstimator + certified_premise готовы |
 ПОДТВЕРЖДЕНО по сути, соответствует нашему Ф3/фазе E4;
 реализация — через типы (structure), не только через файлы |

### Скорректированные приоритеты (поверх фаз A–G)
1. Audit: перенос 22 деклараций в тематические каталоги, затем
   удаление каталога (FREEZE-safe: переехавшие имена = renamed).
2. Export-блоки: поэтапный отказ, каталог за каталогом, build-gate
   после каждого (не P0-массово).
3. Contract-слой: типизация h_emp_* (Е4) — приоритет HIGH, но
   поверх существующих мостов сертификации, без ломки заявлений.
