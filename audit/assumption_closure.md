# Аналитическое закрытие `scripts/assumptions.lock`

Статус: аудит всех 45 файлов, исследовательский цикл 45.
Актуализация цикла 55: после исправления comment-regex в registry
остаётся 38 файлов с h_emp_ упоминаниями вне комментариев,113 identifiers
(5 доказанных имён + 108 premise names); 24 legacy-различия —
комментарные вхождения, НЕ новые математические доказательства.
Критерий: «закрыто» означает только Lean-доказательство,
не переименование binder, запись в record или вывод premise
из равносильного premise. Общая условная теория и
аналитический инстанс различаются. Исправление сканера само
по себе также не закрывает математическое условие.

## Уже выведено аналитически существующими теоремами

| Класс | Закрытие Lean |
| --- | --- |
| `smooth` | `smooth_from_lipschitz_gradient`, `joint_emp_smooth_derived`, `core_premises_joint_operational`, `conj8_h_emp_smooth_derived`; scalar logit: `logitCE_descent_lemma`, `joint_stage_logitCE`. |
| `lip` | `lip_energy_from_gradient`, `lip_energy_quantization`, `compress_energy_bridge`, `core_premises_compress_operational`, `conj13_h_emp_lip_derived`; vector: `gridQ_energy_bound`. |
| `dist` | `gridQ_error`, `gridQVec_error`, `qTern_error_in`, `witness_quantErr_bounded`, `core_premises_operational_scalar_v2`. |
| `grow` | `growEnergy_derived`, `grow_premise_derived`, `grow_gain_from_mirror`, `core_premises_grow_operational`. |
| `merge` | `merge_energy_bridge`, `core_premises_merge_operational`, `h_emp_merge_of_bridge`, `merge_premise_derived`. |
| STE residual | `ste_residual_of_tern`. |
| PL quadratic | `pl_stop_certificate_quadratic` (цикл 45, точная модель `E(w)=μ(w−a)²/2`). |
| Perron named results | `h_emp_dyn_explicit`, `h_emp_dyn_linear_growth`, `h_emp_gain_geometric`, `h_emp_takeoff_exponential`, `h_emp_merge_of_bridge` — это уже доказанные декларации, не premise binders. |
| Canonical primitives | `lse/softmaxP`, `entropyProduction`, `entropy/tvHalf`, `entryCount`, `entDef/klDef/tvDef`, `softmaxW` — определения с canon-мостами, а не измеряемые недоказанные теоремы. |

## Все 45 файлов и их настоящая граница

| Файл | Аналитический статус |
| --- | --- |
| Autonomy/Insight | Fixed unit-Fisher модель замкнута в цикле 53 без `h_emp_second`; произвольная F/Hessian и kernel premise остаются исходными данными. |
| Discovery/PPT | `MeasuredSet`/stationary distribution are sampler semantics; доказательство конечной суммы выведено, distribution/meas остаются исходными данными. |
| Energy/Landauer | Physical dissipation/memory/write/credit/cooling premises are trust boundaries, not analytic statements. |
| Energy/STEStep | Закрыто каноническим `ste_residual_of_tern`; общий `ste_step_residual` остаётся условной треугольной леммой. |
| Ensemble/PolicyCompatibility | Точный `Dpolicy=5Dbase` инстанс выведен в цикле 53; произвольное scaling equality не выводится. |
| Examples/EdgeTests | `h_emp_takeoff_exponential` уже доказан и применяется, не premise. |
| Examples/Nonvacuity | Merge и quant distortion выведены; idle ledger witnesses не являются физическим выводом. |
| Foundations/PerronCone | Четыре h_emp-имени уже доказаны; остальные `h_emp_dyn` — модельная динамика. |
| Foundations/StageCalculus | Условные арифметические wrappers; аналитические модели закрыты DerivAlong/Nonvacuity, но произвольные E не определены. |
| Generalization/ModeState | Произвольная probe/dyn telemetry — внешняя; canonical hold-модель цикла 56 выводит fit и нулевые risk/probe эффекты без h_emp binder из computed весов. |
| Growth/GainRenewal | `frontier_scaling` — модель реинвестиции, derived takeoff не устраняет premise. |
| Growth/Grow | Каноническая quadratic PL закрыта циклом 45; общий PL остаётся классом функций. |
| Growth/SeedOnly | Lipschitz dispersion/recurrence — исходные модели, не выводятся. |
| Growth/Takeoff | Step/dyn/cone — исходная динамика, доказаны только следствия и точные инстансы. |
| Model/ConsolidationMirror | Grow выведен `core_premises_grow_operational`. |
| Model/Memory | Physical memory write premise остаётся. |
| Model/ReferenceMachine | Quantization distortion модель уже выведена; measured dist остаётся ledger premise только в generic wrappers. |
| Model/SoftmaxStep | Smoothness выведена из производной logitCE; generic doc premise не скрыт. |
| Pretraining/ProbeError | Канонические ортопроектор (54) и translated quadratic (57) модели выведены из точной алгебры/норм; общий gA/gF attention-gradient mismatch остаётся предпосылкой, h_emp_dyn не выведен. |
| Pretraining/SyntheticPretrain | Measured synthetic-task gates/transfer остаются исходными данными. |
| Probability/ConditionalSuccess | `[0,1]`, meas, p — исходные; independence — stochastic premise, не выводится из них. |
| Probability/Freedman | Conditional variance bound остаётся martingale input. |
| Runtime/TernaryExact | Quantization доказан; gradient lip остаётся вариантом energy model. |
| Step/AdaptiveSafeQP | Noise measurable/zero/independence/bounds — probabilistic model inputs. |
| Step/Compound | Consumption/gap/decay — исходная динамика. |
| Step/ProjectionDescent | Projection выведен; smoothness класса E остаётся до DerivAlong model. |
| Step/SafeQPStep | Trust-region arithmetic выведен; общая smoothness модель сохраняется. |
| Step/StochasticSafeQP | Те же stochastic premises. |
| System/GrowthComputed | Canonical computed energy/grow выведен `growEnergy_derived`. |
| System/GrowthState | Переходная арифметика доказана; measured stage effects закрываются только операциональными инстансами. |
| Unified/AdvanceWitness | Memory physics остаётся. |
| Unified/AnytimeMartingale | Те же stochastic premises. |
| Unified/ArchitectureTheorem | Cone/dyn — исходная динамика семейства состояний. |
| Unified/Assumptions | Cone/step/dyn/noise cap — исходная динамика и idle witnesses. |
| Unified/CommitGate | Компьютерный gate уходит от premise; generic `h_emp_grow` мостится canonical instance. |
| Unified/CorePremisesDerived | Smooth/lip/dist выведены; grow/merge/G подключаются отдельными инстансами. |
| Unified/DerivAlong | Основной аналитический smooth/lip/dist мост уже закрыт. |
| Unified/DescentCore | Objective descentLemma исходный; quad/logit инстансы закрыты. |
| Unified/EmpiricalPremises | `holds` не выводит smooth; `premises_give_smooth` требует hsmooth — это НЕ закрытие, misleading docstrings подлежат исправлению. |
| Unified/GrowthBridge | ConditionalSuccess independence/measurability — external. |
| Unified/MasterHAGI | Составной conditional capstone; только stage bridges выведены. |
| Unified/MasterHAGITrunc | Cone dynamics external, Perron consequences доказаны. |
| Unified/RecursiveGrowth | Macro arithmetic доказан; stage premises не удалены без модели. |
| Unified/StateTakeoff | Cone dynamics external, доказаны последствия. |
| Unified/TopLevel | Quant energy модель выведена в EFTheory; noise/smoothness остаются классами моделей. |

## Что нельзя закрыть без новых определений или измерений

- Независимость, measurability, martingale variance и точное
  распределение sampler не следуют из чистой арифметики.
- `cUnit` Landauer, memory write, cooling dissipation и
  operational credit — физические/аппаратные данные.
- Qgen, fit, synthetic-task gates — данные оценки, а не
  следствия energy/KL без конкретной функции измерения.
- Общие `PL`, `second`, `attsmooth`, cone-dyn и scaling — это
  семейства моделей. Они закрываются доказанными инстансами,
  но не исчезают истинно при произвольных функциях.

Следующий механический шаг: не удалять общие conditional lemmas;
подключать новые операциональные инстансы к каноническому
`CertStep`. Ложное обещание `EmpiricalPremises.holds ⇒ smooth`
исправлено в цикле 45: отдельная smoothness-модель обязательна.

## Цикл 46 — исполнение замкнуто в CertStep

- `logitStepCertExactCore` — scalar CE с произвольным η>0;
  фактический drop из `descent_step_strict`.
- `ncMinimalStepCert` — drop=`u.gain` из `ncCertStep_energy`.
- `trainStepMinimalCert` — точный drop из `trainStep_actualDescent`
  с sufficient-step positivity; никакой smoothness-гипотезы.
- Все три ядра имеют только стандартные Lean-аксиомы;
  AssumptionScan не получил новых premise binders (137).

## Цикл 47 — computed growth/merge

- `GrowthComputedCert.next/stepCert` замыкают реальное
  обновление весов в `CertStep`: drop=`(1−(1−η)²)·E`.
- `mergeOperationalCertStep` использует настоящий Jensen gap
  как drop, а `mergeStrictCertStep` доказывает его ненулевость.
- Никаких `h_emp_*` в ядрах; общие ledger-формы не удаляются.

## Цикл 53 — fixed unit-Fisher и fivefold-policy

- Скалярная модель `scalarQuadraticKl` полностью вычислима по
  dW²/2, а единичная F превращается в identity linear map.
  `forgetting_kl_quadratic_unit_fisher` выводит curvature premise,
  `tldr_two_tier_safety_unit_fisher` выводит двухуровневую безопасность
  в той же модели. Это НЕ вывод произвольной распределительной KL.
- `mopd_kl_scaling_warning_fivefold` устанавливает Dpolicy=5·Dbase
  по построению; прежний `h_emp_scaling` инстанцируется rfl.
  Общий масштаб политики не определяется этой теоремой.
- Frozen-ограничение: общие исходные теоремы сохранены. Registry
  остаётся 45 файлов/137 вхождений: это НЕ удаление premise binders.
  Убран один новый-unused-instance warning через Finite r + Fintype
  ofFinite в доказательстве; типовые условия оригинала не менялись.

## Цикл 54 — Lipschitz условие через ортопроекцию
- `projected_gradient_lipschitz` выводит гладкость модели L·P
  из нерасширяемости ортогональной проекции. Наличие самой проекции
  оформлено `HasOrthogonalProjection`, а НЕ новой норм-посылкой.
- `cut_signal_attention_quant_projection` подставляет этот bound
  в общий Cut-треугольник без `h_emp_attsmooth`. Обе gradient-карты
  специально выбраны одной L·P моделью; arbitrary full/clamped
  gradient mismatch и обучаемая softmax mask здесь не закрываются.
- Identity-projection probe (K=⊤, L=3) проходит, и all-new proofs
  используют стандартную тройку аксиом. Старые сигнатуры сохранены.
  Registry остаётся 45 файлов/137 вхождений: классical closure
  отличается от численного удаления общего premise binder.

## Цикл 56 — computed-transition generalization
- `computedGenStep` определяет обновление compressed weights и
  energy через каноническую growth-квадратику. Параметры и probing
  сценарии явная модель сохраняет, не постулируя стороннюю fit.
- `generalization_safe_step_computed` использует это вычисление
  для h_emp_fit и нулевого risk/probe regression в существующем
  safe-step. Canonical hcanon остаётся явным условием модели.
- Переход НЕ выводит h_emp_dynи не доказывает постоянство произвольных
  наблюдаемых generalization metrics. Это отдельная область данных.
- Два пространственных weights [2,4] переходят в [1,2] при η=1/2;
  energy computed равна 5/2, probe выполнен через lake env lean.
  Аксиомы трёх новых declarations — только стандартная тройка.

## Цикл 57 — quadratic FD error и Lipschitz
- `probeQuadraticEnergy` и `probeQuadraticGrad` задают translated
  quadratic модель, где центр произвольного X выбирается явно.
- `fd_probe_error_quadratic` выводит hmodel через exact norm expansion;
  остаток абсолютного значения неотрицателен только при hL≥0, interval
  работает при hσ>0. Коэффициент L/2 сохранён при делении σ.
- `probeQuadraticGrad_lipschitz` закрывает h_emp_attsmooth для общего
  quadratic поля; arbitrary gA/gF и Fréchet-класс не подменяется моделью.
  Probe: значения a=1,L=2,σ=1/2,x=1,v=2 дают error=bound=2.
  Композиция с old Cut theorem доказана в test-side Lean probe, аксиомы
  чисты, registry 38/113 без force deleting старых условий.

## Цикл 58 — exact central quadratic probe
- `centralQuadraticProbe` вычисляет центральную разность для той же
  canonical translated energy. Никакого forward remainder или
  external `hmodel` premise не берём для symmetric cancellation.
- `centralQuadraticProbe_exact` даёт точное algebraic gradient inner
  при σ>0. Любой L допустим, поэтому нет ложного nonnegative-состояния
  в предположениях и нет stochastic global unbiasedness claim.
  Нет также утверждения о сокращении вычислений relative to forward
  или реализации оптимального σ selection.
- Пример a=1,L=2,x=0,v=1,σ=1/4 компилируется и даёт -2.
  Стандартная тройка аксиом проверена у обеих declarations.
  По-прежнему не удаляем общие условные теоремы; registry 38/113.

## Цикл 59 — accuracy comparison для quadratic probe
- `forwardQuadraticProbe` делает вычисление forward разности явным,
  а `forwardQuadraticProbe_error` даёт точный abs error, не только upper.
- В том же canonical поле `quadratic_central_error_lt_forward_error`
  выводит строгую нулевую ошибку central против положительной forward.
  Необходимы L>0, σ>0, v≠0: они не отброшены и в них вход признан.
- Также не доказывается существование более дешёвого вычисления,
  оптимального σ или несмещённости оценки для нелинейной модели.
- Конкретный probe получил forward -3/2 и значение центрального probe -2,
  что дало 0<1/2. Аксиомы чисты, frozen forms не менялись,
  регистр остаётся 38 файлов и 113 identifiers.

## Цикл 60 — explicit optimum для probe cost
- Оптимизирована арифметическая функция aσ²+b/σ, а не абстрактное
  утверждение «лучший learning algorithm для любых данных».
- Нет `h_emp`: доказаны положительность, точное cube-root coefficient
  relation, global min и strict comparison при другом положительном σ.
- Корень взят из Real.rpow_inv_natCast_pow, а не сымитирован численно.
  Regressed wrong factor был исправлен до commit по counterexample,
  exact Fraction и числовому Lean probe при a=2,b=4.
- Чтобы применить этот min к реальному training/probe, ещё нужно
  вывести a и b из конкретной модели и гарантировать измерительный
  noise/roundoff bound. Эти границы пока НЕ выводятся из новой cost.
- Мотивирующий scientific source: Tung et al. 2026,
  https://jes-tm.org/index.php/jestm/article/view/449.
- AssumptionScan 38/113: ничего не переименовано в proof и не удалено
  из registry для имитации общего решения.

## Цикл 61 — directional cubic noise модель и exact optimal step
- Граница aσ²+b/σ теперь получает вычисленные коэффициенты:
  a=(|c|/6)‖v‖^6, b=δ из абсолютных measurement perturbations.
- Старое чисто алгебраическое optimum применено к доказанной модели
  через `noisyCentralCubicProbe_optimal_bound`; root не принят как
  измеренный и/или эмпирический параметр.
- Моделируется не arbitrary loss, а F_v=(c/6)inner(x-a,v)^3 и её
  выбранное algebraic field. Central error раскрывается полиномиально.
- Гипотезы |eps±|≤δ остаются локальной явной bounded-noise моделью,
  не переименованным универсальным h_emp-зоключением. Они не закрывают
  ArbitraryMeasurement/estimator/physics-предпосылки registry.
- Доказательство выводит минимум cost bound, не fictitious strict actual
  error ordering при любой отдельной perturbation. Если c=0 или v=0,
  root-условия сами запрещают фиктивную положительную оптимальность.
- Probe в R даёт точные 1/4, 1, 1, 3 и 5, отдельные eps дают 2.
  AssumptionScan 38/113 остаётся неизменным, как и замороженные формы.

## Цикл 62 — Fréchet grounding для уже выбранных моделей
- `probeQuadraticEnergy_hasFDerivAt` и `probeCubicEnergy_hasFDerivAt`
  полностью в типе HasFDerivAt: derivative operator bundled continuous
  linear map `innerSL ℝ (chosenGradient)`, не meta-утверждение об имени.
- L и c остаются произвольными вещественными числами, including zero;
  c,v не имеют искусственно внесённых ограничений из optimization domain.
- Quadratic использует существующий reference `HasFDerivAt.norm_sq`;
  Cubic — цепочку `HasDerivAt.comp_hasFDerivAt` с inner-coordinate.
- Это вывод derivative только в x: fixed v не является дополнительно
  дифференцируемым мультиаргументом без отдельной теоремы.
- Registry не уменьшается формальным headline: general hmodel, loss,
  stochastic noise и physics/rounding сохраняют свои trust boundaries.
  AssumptionScan 38/113, старые доказательные интерфейсы не тронуты.
- Library source: Mathlib `Analysis/InnerProductSpace/Calculus.lean`,
  `hasStrictFDerivAt_norm_sq` и `HasFDerivAt.norm_sq`.

## Цикл 63 — computed endpoint quantization и σ-bound
- Один абстрактный class noise ∀|ε±|≤δ получил рабочий вычислимый
  представитель: dense nearest grid с computed ε±=Q(F±)-F±.
- Их absolute caps δ=grid/2 выводятся из nearest integer library lemma,
  не полагаются на новое empirical binder и не регулируют old statements.
- Оптимальный σ выбирается в данной fixed-grid model. Сетку, число бит,
  архитектуру и runtime cost случайной/физической модели НЕ оптимизируем.
- Старое qTern остаётся separate saturating-format theory со range split;
  новая dense model без saturation не претендует на generic IQ coverage.
- Нет завершающего floating-processor theorem: расчет после двух округленных
  значений — exact real subtraction/division, что явно stated в source.
- Nonzero gradient probe фиксирует ошибку 5/4 с measured value 2 и
  gradient 3/4. Дельта-cost selected 3≤5 при comparison σ=2.
- AssumptionScan по-прежнему 38/113; только designated model closed.

## Цикл 64 — bounded saturation для ternary cubic probe
- Недопустимая прямая подстановка переменного saturation cap в
  unbounded cube-root optimum заменена на корректную bounded domain
  optimization: min(r,σmax) с доказательством обеих веток.
- Существующий actual `qTern` подключён напрямую. Его cap для обоих
  range cases = max(level/2,|value|-level), не переписывает old defs
  и не предполагает in-range покрытия всех значений energy.
- `ternaryCubicStepBudget` математически вычисляется через рост energy
  при |t|≤σmax и два знака сдвига. Этот бюджет upper bound, не
  следование из стохастических moments всех измерений.
- Actual signed offsets Q(F)-F, including positive saturation and
  negative small endpoint, соединяются с уже доказанной cubic/noise cost.
  Существующая genuine derivative исходной энергии не смешивается с
  неформализованной производной кусочного quantized protocol.
- Оптимальность ограничена fixed level, fixed σmax, и interval (0,σmax].
  Победить global actual error или оптимизировать memory/level/runtime
  этот proof не утверждает; h_emp registry не сокращён силой названий.
- Скалярный probe: q=1 и q=0, offsets=-19/8 и 1/8, error=1/4.
  Cost at clipped root=39/8, other within-region cost=8. Lean проверено.
- Импорт по слоям: общий optimizer в Pretraining, ternary bridge в
  Unified (соответствует layer order и без исключений LayerLint).

## Цикл 65 — alphabet representation и minimum block width
- Что существовало: base-3 pack upper bound и injectivity. Это НЕ
  повторно доказано другим polynomial in Runtime module.
- Что добавлено: явный semantic mapping between actual qTern states and
  finite ternary codes, typed byte wrapper, natural digits decoder and
  concrete sample-point reconstruction.
- Decoder возвращает quantized values, не original unrounded samples;
  поэтому не возникает ложного restoration theorem for arbitrary reals.
- Битовая минимальность: 7-bit Fin payloads не допускают ни одного
  arbitrary injective encoder five-place alphabet (card=243>128).
  Для одного trit аналогично two states<3. Это fixed code alphabet,
  не document о оптимальности heap, storage or entropy of all model files.
- Level parameter shared across group and explicitly not counted in
  eight-bit block payload. Maximum packed value=242; 243 exact states.
  No policy заявления trailing bytes 243..255 или memory overhead.
- Pointwise theorem `packedTernarySamples_decode_point` передаёт каждую
  quantized sample обратно с общим level. Numerics payload 68 и
  5-place [1,0,0,1,-1] проверены, no noise distribution or stochastic bounds.
- Frozen theorem statements/API and registry 38/113 are unchanged.
