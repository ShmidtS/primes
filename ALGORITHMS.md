# ALGORITHMS.md — алгоритмы HAGI, выведенные из доказанных теорем

Каждый алгоритм — прямое следствие машинно-верифицированной
формализации Lean 4.35.0 / Mathlib (Hagi/; после R1/P1-D:
6168 Freeze declarations, 0 sorry; аксиомы только
propext/Classical.choice/Quot.sound).
Ссылки: `Hagi/<Каталог>/<Модуль>.lean`. Измеряемые посылки
помечены `h_emp_` и никогда не скрыты.
Ниже нового блока сохранены исторические записи циклов;
их локальные счётчики не заменяют текущий snapshot из STATUS.md.

## Physical join: spectral projector → SafeQP

Это consolidation carrier/consumer, а не новый алгоритм обучения:

- Orthogonal projector, exact residual/tail energy и rank+quantization
  triangle теперь находятся в `Hagi/Step/SafeQP.lean`, рядом со своим
  consumer `spectral_safeQP_target`. Их FQNs в `Hagi.Spectral`,
  statements, proof bodies и FiniteDimensional premises не изменены.
- Старый StepCore module import path удалён, а не замаскирован forwarding
  модулем: внешний потребитель использует SafeQP или root `Hagi`.
  Все 12 существующих `Hagi` reexports проверены компилятором после join.
- Полный Root census сохранил 17+14 OWNER identities (включая
  structure/generated records), 1213 IR records и 38 CONSUMER rows.
  Для всех 31 declarations совпадают baseline type/body hashes; для 22
  теорем получены только стандартные три аксиомы. Четыре auxiliary
  записи без доступного kernel ConstantInfo сохранены с явным
  unavailable metadata, без выдумывания их тел.
- Имеется ровно 10 фактических owner-qualified range transitions;
  private rename map пуст. Итоговые counters не изменились:
  12074 Root constants, 9052 ALLAXIOMS, 6168 Freeze и 313 intrinsic.
- Физический corpus: 493 non-root modules, 139319 строк и 621 internal
  non-root edge. Уменьшение числа source модулей не означает меньшую
  сеть, меньше параметров или вычислений; новых гарантий оптимального
  обучения, runtime, FLOPs или model quality этот join не даёт.

## R1/P1-D: consolidation без нового обучающего правила

Этот пакет убирает повторные доказательства, не меняя математические
носители или training rules:

- Два сохранённых public имени стали настоящими compatibility aliases:
  `minimumNormBatchCEProblem_value_le_zero` →
  `minimumNormBatchParetoProblem_value_nonpos` и
  `asymmetric_cost_feasible` → `identityMinimumNormBatchStep_cost_feasible`.
  Проверены `AliasInfo.plain`, одинаковые elaborated types и canonical
  targets. Ложно удалить public API или просто исключить дубликат
  из линтера не разрешалось.
- `posterior_congr_of_model_eq` в `FiniteBayes` доказывает, что posterior
  при равенстве двух моделей не зависит от выбора доказательств положительной
  evidence. Обе positive-evidence premises и равенство моделей остаются
  явными; они не упакованы в class и не скрыты. Два старых private EM
  helper-а заменены этим общим proofs-sharing result в трёх вызовах.
- Удалённый guarded-logit duplicate равен сохранённому same-file
  `logitProblem_stay_step` по elaborated statement. Его шесть consumers
  используют именно этот retained proof; для доступа к private declaration
  не создан новый публичный wrapper.
- Census: 12076 → 12074 Root constants, 9054 → 9052 ALLAXIOMS,
  6170 → 6168 Freeze. Все 1213 extra/IR entries и 38 отслеживаемых
  consumer rows сохранены. Изменены ровно 11 retained bodies:
  2 alias + 3 posterior + 6 guarded. Четыре observed asymmetric-cost
  consumer bodies не изменились, а generated и ordinary-definition
  bodies не получили допуск на изменение.
- Итог — уменьшение повторного формального кода при сохранении API и
  statements. Он не является минимизацией весов, сокращением FLOPs,
  новым optimum обучения или runtime-измерением.

## Supported importance selection: C191–C200

### Observable error and allocation

Для конечного batch и supported PMF p обозначим estimator математически
(без введения нового Lean-имени): `Z_b(a) = if a = b then ℓ a / (p a).toReal else 0`.
Здесь и ниже support означает `p b ≠ 0 ∨ target b = 0`;
zero mass допустим только при zero target.

- `pmfMean_selectedLoss` и `pmfMean_selectedLoss_support` доказывают
  finite first-order unbiasedness на этом carrier. Для скалярного loss
  `pmfMean_selectedLoss_variance` даёт Var(Z_b) = ℓ_b²(1/p_b − 1).
  Это variance явного estimator, а не generalization error.
- При L = Σ|ℓ| > 0 используется `selectedLoss_optimalPropensity`:
  q_b = |ℓ_b|/L. Теорема
  `selectedLoss_optimalPropensity_mse_le` — supported optimum;
  `selectedLoss_optimalPropensity_eq_of_mse_eq` — единственность
  supported minimizer при L > 0. Случай L = 0 не объявляется unique.
- `selectedLoss_optimalPropensity_mse_eq_zero_iff_single_nonzero`
  характеризует zero MSE одной активной loss-координатой.
  `selectedLoss_optimalPropensity_mse_lt_uniform_iff` характеризует
  строгое улучшение против uniform неодинаковостью модулей потерь.
  Разложение/оценка требуют support включая предлагаемую q.

### Vector gradients and arithmetic means

Для Euclidean gradients g_b пусть G = Σg_b и L = Σ‖g_b‖.
C197 для supported p доказывает

```text
selectedGradientMSE p g = Σ_b ‖g_b‖²/(p b).toReal − ‖G‖².
```

При L > 0 norm-proportional q_b = ‖g_b‖/L даёт L² − ‖G‖²
(`selectedGradientMSE_optimalPropensity_le`). Строгое сравнение
с uniform дано `selectedGradientMSE_optimalPropensity_lt_uniform_iff`.
Единый полный gradient target — заранее выбранный G, а не произвольный
runtime center и не обучаемый оптимизатор.

C198 переносит это на arithmetic mean: estimator
`(card B * p_b)⁻¹ • g_b`; положительная cardinality и support заданы
явно, MSE масштабируется как `(card B)⁻²`.
См. `selectedMeanGradientMSE_optimalPropensity_le` и
`selectedMeanGradientMSE_optimalPropensity_lt_uniform_iff`.

Если фактические norm неизвестны, но известны ‖g_b‖ ≤ a_b и
Σ|a_b| > 0, C200 даёт upper-envelope allocation с гарантией
MSE ≤ (Σ|a|)² − ‖G‖² и точным mean scaling. Это
`selectedGradientMSE_upperBoundPropensity_le` и
`selectedMeanGradientMSE_upperBoundPropensity_le`.
Surrogate upper bound не выдаётся за фактический optimal gradient norm.

### Bridge to actual batch CE

C199 (`Model/BatchCEDescent.lean`) связывает эти формулы с настоящим
`BatchCEDescent.batchResidualGradient`, а не с energy surrogate:

- `mean_batchResidualGradient` — raw mean identity;
- `selectedMeanGradientMSE_batchResidual_eq_pmfMean` — точная
  MSE representation для CE residual gradients при
  `0 < Fintype.card (Fin B)`; support для этой identity не требуется;
- `pmfMean_selectedMean_batchResidualGradient` — coordinatewise
  first-order unbiasedness при одновременных positive cardinality и
  raw-gradient support.

Пустой batch totalization не называется PMF или unbiased estimator.
Численный witness C199: два класса, один feature, θ = 0, labels 0/1;
raw gradients [−1/2], [1], mean 1/4, optimal mean MSE 1/2 против
uniform 9/16. C200 Euclidean witness даёт raw 5/2 ≤ 7 и
mean 5/8 ≤ 7/4. Это математические finite-model примеры, не benchmark.

C201 solidifies the feature-only alternative as four public results in
`Hagi.Model.BatchCEDescent`. Put `F_b = featureNormSum (X_b)`; this is a sum
of Euclidean ℓ² norms of input-feature rows on the WithLp carrier. It must
not be confused with `Hagi.Model.CEGroupedScale.featureAbsSum`, whose mass
is entrywise ℓ¹. The actual residual transpose satisfies
`‖batchResidualGradient X θ y‖ ≤ featureNormSum X`: residual coordinates
have absolute value at most one, so no second-order oracle is used.

With `hF : 0 < Σ_b |F_b|`, define the PMF
`q = selectedLoss_optimalPropensity (fun b => F_b) hF`; in real weights,
`q_b = |F_b| / Σ_a |F_a|`. Then every sample has `q_b ≠ 0` or a zero actual
raw-gradient target. The estimator `(n*q_b)⁻¹ • g_b` has exact coordinatewise
pmfMean equal to `meanResidualTranspose X θ y` through
`pmfMean_featureNormSum_optimalPropensity`. Positive mass proves positive
batch cardinality; an empty batch cannot satisfy hF. Zero feature mass implies
zero raw gradient, but the converse is false: opposing residual rows cancel.
No nonzero target at zero propensity is admitted through totalized division.

`selectedMeanGradientMSE_featureNormSum_le` is exactly the C200
upper-envelope theorem instantiated with this feature bound. Its right-hand
side is B⁻² · ((Σ_b |F_b|)² − ‖Σ_b g_b‖²), where B is the batch cardinality.
Thus the feature bound controls the supported arithmetic-mean estimator
without knowing the individual gradients before choosing q.
The feature policy is not called the actual gradient-oracle Neyman optimum.
The same real two-class CE example as above has `F_0 = 1`, `F_1 = 2`,
`q = [1/3, 2/3]`; its mean is `1/4`, its exact selected mean MSE is `1/2`,
and its separately calculated upper envelope is `35/16`. Those two MSE
numbers are not equated. The Root census also preserves all 12,074 old
OWNER records and adds exactly four public plus six private declarations.

Still not derived: sampling-history/RNG execution, held-out
CE/generalization, convergence/regret of an optimal training algorithm,
minimum memory, physical FLOP/runtime improvement or a universal optimal
architecture. The earlier `.tmp/C201SupportProbe.lean` resulted in these four
public declarations; the unsuccessful Frobenius/sqrt2 alternative is not
production evidence.

## Analytic finite-carrier closures (цикл 78)

- Reuse `signR`/`HC`; `rademacherLaw` is a true finite product of fair
  Bernoulli distributions. Projection measurability, zero means,
  `rademacher_projection_independent`, and norm≤1 for unit vectors
  discharge the four FIXED-minibatch SafeQP noise inputs on this carrier
  without a duplicate independence engine. Sigma=1; only j-independence
  for fixed i,d, not across experts/time or an arbitrary minibatch.
- Actual-consumer probe supplies these four proofs to
  `minibatch_inner_concentration` for both nonzero coordinate directions.
  No hidden X-measurable-space, runtime independence or physical guarantee.
- Finite normalized `pi` plus identity sampling constructs a genuine PMF
  and exact singleton masses. `discovery_prob_stationary_identity` turns
  the old fiber/distribution premises into proved model facts; it is not
  a stationarity theorem for a runtime chain or an empirical hmass.
- Full componentwise refinement plus `∀i, 0≤w i` and `sum w=1`
  proves the formerly separate weighted lower gap and upper band in
  `corePremises_of_full_refinement_normalized`, while preserving h1..h13
  and the older general constructor. Upper-only telemetry is insufficient:
  nonzero uniform weights with 0→−1 remain a concrete counterexample.
- Freeze=4357 (+13): 11 DustMeasure declarations, PPTCanonical and
  normalization. Modules=431. Actual empirical registry remains 201/37;
  all arbitrary settings stay conditional rather than disappear.
- Independent refute-first review: LGTM; full `bash scripts/ci.sh`: PASS. Nondegenerate signs, nonzero unit
  vectors, normalized scalarization and actual consumer shapes verified.

## Audited executable discrete selection (цикл 77)

- Generic `auditedFilter` preserves List.filter and counts logical guard
  calls exactly input length. `auditedArgmin` reuses List.argAux/argmin;
  `auditedArgmin_fst` establishes exact same candidate and first-on-tie.
- `auditedArgmin_snd` computes admitted length−1, hence zero on empty.
  It counts pair-relation calls, NOT native instructions/FLOPs/time,
  arbitrary cost evaluations or all `step` calls under short-circuit.
- `DiscreteProgram` uses its actual successor and evaluates integer quality
  there. Its A : Type matches the old resourceCost action carrier. The
  Bool guard and Nat resource data are declared model inputs, not
  physical safety or byte/time measurements.
- `finiteSelection` returns None iff every input-list guard fails;
  eligible listed actions attain minimum Prod.Lex (memory, operations).
  No arbitrary action fallback or all-Fintype minimum from a partial list.
- `selectionReport_guardCalls` and `selectionReport_comparisons` derive from this
  fold structure. No optimal-search claim follows from exact counting.
- Integer-to-real point adapter `toController` preserves step/memory/ops;
  `admissionGuard_iff_qualityEligible` lifts integer floor in both
  directions without sign assumptions. It does not execute raw ℝ CE.
- With hcomplete covering ALL actions,
  `finiteSelection_cost_eq_minimumResource` compares old and executable
  costs: equal via two opposite inequalities; concrete actions may differ.
- Fin2: qfloor1 leads to actual increment, selection/successor=1;
  qfloor0 chooses cheap stay 0; M=0/C=0 strict upgrades and empty list all
  yield none. Guards 2 / comparisons 0 (strict) versus 1 (baseline).
- Fin3: upgrade 1 has cost (100,0), upgrade 2 has (1,100), floor=1.
  Choice=2 demonstrates memory-first despite more operation units.
  Negative qfloor=-1 cast and equality to the old min are checked.
- Two modules, +29 declarations = 4344; empirical 201/37 unchanged,
  structural 9175/415 (+10). Full root CI / axioms / final independent
  refute-first review all PASS. Exhaustive scan is not global architecture
  minimum, nor proof that branch-and-bound/A* are always preferable.

## Exact admissibility margin (цикл 76)

- `estimatedMaxValue` computes the estimated objective of the REAL
  successor chosen by the existing ParetoExecution engine. It does not
  re-enumerate a global arch or add a per-radius minimizer.
- `estimatedMaxValue_upper` dominates estimate of actual successor for
  EACH original feasible candidate through existing max lemma and
  withEstimatedValue membership equivalence. Original caps still bind.
- `robust_eligible_iff_radius_le_margin`: ∃ conservative eligible
  action iff eps≤estimatedMaxValue−qfloor. Boundary is INCLUDED.
  Forward: chosen value(conservative)→max; backward: max's witness.
- `no_robust_eligible_above_margin` means no action whatsoever qualifies
  at eps>max−floor. h_stay only ensures original feasible nonempty,
  not nonempty at all eps. No fallback or sampled-noise guarantee
  appears in the proof.
- Distinguish scalar estimated admissibility margin from full RRF:
  Goberna 2021 and Liers 2021 consider restricted MIP/conic programs,
  not this abstract arbitrary model. Rho≠stochastic confidence and
  maxEstimate≠actual task performance/minimum computation/search cost.
- Exact Fin2 boundary: p.step a 0=a, scores 0,1; caps 1,1.
  Maximum=1, epsilon=1 has witness, epsilon=2 empty for every action.
  Scalar CE: max estimate equals actual gradient successor estimate
  whenever the real h_eta/h0/h1 conditions hold (no replacement baseline).
- +4 declarations to 4315, 427 modules; empirical 201/37 unchanged;
  structural 9165/413 (+7). Fresh focused probes and corpus CI PASS.

## Robust-certified cost sensitivity (цикл 75)

- `robustEligible_mono_epsilon`: при eps1≤eps2 каждый действительно
  eligible при eps2 vходит в меньший класс eps1. Элемент feasibility
  не меняется; меняется лишь qfloor+eps на est(actual successor).
- `robustMinimumResource_cost_mono` использует предыдущий cost-min
  непосредственно на выбранном большим radius действии после его
  transfer в small семейство. Противопоставлять два argmin-ядра не нужно.
- `robustMinimumResource_memory_mono` выводит неубывание первой memory
  координаты из Prod.Lex порядка. Строгость и монотонность operations
  отдельно НЕ выводятся. Уровень — class-certified costs, не hardware.
- Два witness (small и large) обязательны: eps может стать слишком
  большим и класс становится пустым. Ни выбора по призрачному witness,
  ни fallback/forbidden. Истинная качественная гарантия продолжает
  требовать herr из cycle 74; сам cost lemma её не создаёт.
- Fin3 witness: score=a.val/2, actual p.step a s=a,
[... 701 chars omitted ...][... 319 chars omitted ...] -> 4311; empirical 201/37 unchanged,
  structural +8 до 9158/412. Это только interface occurrences,
  не новые закрытые empirical premises или hardware bounds.

## Bounded-error guaranteed-floor minimum (цикл 74)

- `robustMinimumResource` переиспользует `minimumResource` на
  `withEstimatedValue`, требуя `qfloor+eps ≤ estimate(p.step a s)`.
  На самом деле безопасный step, p.safe и оба ресурсных cap неизменны.
- `robustMinimumResource_actual_quality_ge`: из `|true-estimate|≤eps`
  через анализ absolute bound и ресурсный eligible spec выводится actual floor
  `qfloor ≤ true(p.step selected s)`. Это алгебра, не IID confidence.
- `robustMinimumResource_cost_min` минимизирует `(memory,operations)`
  в `Prod.Lex` ТОЛЬКО на lower-bound-certified class. Неутверждение
  минимума над всеми истинно-qualified candidates — важный инвариант:
  cheap true-positive без достаточного pessimistic margin исключается.
- При `estimate=p.value`, `eps=0` получен прежний exact min selector
  `robustMinimumResource_zero_exact` после нормализации qfloor+0 и
  record update; нового selection engine/cost objective нет.
- Flat probe: true=0, estimate=−1/2, eps=1/2, actual floor 0 достижен,
  но lower-certified class ПУСТ. Ни witness, ни fallback для empty
  family не выдумываются. При floor −1 класс уже непуст и верен.
- Scalar logit CE: estimator error exactly 1/2, floor = true upgraded
  objective − 1. Выбран настоящий gradient upgrade (action 1).
  Но identity (cost 0) тоже истинно проходит этот floor при eta=1,w=0,
  поскольку CE0=log 2 ≤ 1 и CE upgrade≥0. Честного всегда cheaper
  learning claim нет даже здесь. Multi-step/stochastic optimum не дан.
- Sources: a priori bounded uncertainties и set membership / minimax
  estimator literature `.tmp/cycle74-research.txt`. Robust identification
  class tradeoffs описаны Маззаро et al. 2001; требуемые bounds не могут
  быть выведены из abstract как confidence для нашей p-задачи.
- +6 declarations, Freeze=4308, empirical 201/37 unchanged,
  structural 9150/411 (incl elaborated choice pointer, not unknowns).

## Quality floor at minimum declared resources (цикл 73)

- `qualityEligible` не принимает metadata эффектов: это старое `feasible`
  И `qfloor ≤ p.value (p.step a s)` на действительном successor.
  Feasibility сохраняет исходную model safety и оба cap величин.
- `resourceCost = toLex (memory, operations)` тип `ℕ×ₗℕ` задаёт
  memory-first порядок, operations разрешает только равную память.
  Произвольного weighted scalarization разных unit нет.
- `exists_minimum_resource` фильтрует finite `Finset.univ` и вызывает
  существующий `Finset.exists_min_image`. `minimumResource` лишь
  `Classical.choose` witness при поданной eligible точке, не optimizer.
- `minimumResource_next_quality_ge` относится к выбранному successor;
  `minimumResource_cost_min` сравнивает КАЖДЫЙ eligible competitor.
  Пустое eligible-семейство не скрывается fallback-ом.
- В `Fin 2` и `0<eta`, строгий `-logitCE(actual update)` floor
  отсекает identity и выбирает реальный gradient update, cost=(1,2).
  Базовый `-logitCE w` floor выбирает identity: это НЕ обучение.
  При M=C=0 strict-upgrade eligible set пуст, обмануть caps нельзя.
- Research: HardCoRe-NAS (Nayman et al., ICML 2021),
  Constraint Guided Model Quantization (Van Baelen, Karsmakers, 2024),
  DnnSAT (Gao et al., ICSE 2021), HyperPower (Stamoulis et al., 2018).
  `.tmp/cycle73-research.txt` хранит точные abstract ссылки. Они
  контекст конкретных constrained models, НЕ доказательства теорем.
- +9 declarations; Freeze=4302, empirical 201/37 unchanged,
  structural 9141/410 (7 named eligible witnesses).
  Точный finite-class minimizer не означает минимум FLOPs hardware,
  global architecture optimum, search complexity или task quality.

## Scalar logit-CE policy and budgeted trajectory (цикл 72)

- `logitProblem`: state=real margin, objective=`-logitCE`, actions
  identity и точное вычисление `w+eta/(1+exp w)`. Safe = настоящий
  CE non-increase, выведенный из `descent_step_strict` при eta>0.
  Generic optimality of eta не утверждается.
- При двух feasible-кандидатах `logit_selectedNext` исполняет update,
  поскольку false baseline противоречит строгому уменьшению CE.
  Model memory/operations caps остаются явными, не физическими байтами
  или минимальным числом FLOPs.
- `logitEstimate = −logitCE−1/2` имеет ошибку ровно 1/2. Сдвиг
  пессимистичен и детерминирован; это НЕ IID-калибровка и НЕ широкий
  estimator guarantee. `logit_robustNext` сохраняет действительный
  update; без бюджета — возвращает прежний state.
- `logitTrajCert` переносит настоящие поля `logitStepCertExact` на
  зависимую точку `w(t+1)`. Все каналы качества 0≤logitCE, risk=0,
  реальный budgetSpend=eta; per-step hrec не заменён эффектами-ad-hoc.
- `logit_budget_loop` использует `certified_loop`, `_all`, `_strict`.
  Итог включает CE sum telescopes, все intermediate floors,
  budget residual 0≤b_n и b_n≤b0−Σeta, strict decline при n≥1.
  Индукция `logit_budget_nonneg` выводит 0 от фактических budget bounds.
- `logit_quadratic_bound` вызывает готовый `logitCE_trajectory_bound`.
  `logit_budget_loop` и его quadratic certificate требуют eta≤2;
  базовый exact drop допускает любой eta>0. Нельзя переносить
  scalar monotonicity
  на broader large-step logistic models после oscillation literature.
- Probe: at eta=1 initial update 0→1/2 exactly; selected/robust steps
  совпадают с ним. For T=3 at b0=10 and eta=1, actual b3=7, Σspend=3.
  +27 declarations; Freeze=4293, empirical 201/37, structural 9134/409.

## Bounded-estimation Pareto policy (цикл 71)

- `withEstimatedValue` подменяет только objective estimation;
  actual successor, model-safe и оба раздельных resource cost неизменны.
  `robustNext_eq` возвращает настоящий successor допустимого действия исходной
  модели, а не отдельный желаемый эффект.
- `robust_quality_lower`: если на каждом actual successor известна
  absolute error≤eps, то для любого feasible other выполнено
  `q(other) − 2eps ≤ q(robustNext)`. Доказательство — max по estimate
  плюс две применённые error bounds. Порог положительного gain не нужен
  для этой аппроксимации, но и exact argmax не выводится.
- `robust_quality_gap` исключает улучшение истинного качества другого
  кандидата БОЛЬШЕ чем на 2eps. Вблизи границы возможен другой actual
  argmax, как и говорят существующие ambiguity-counterexamples.
- Memory/operation caps не искажаются оценкой. Единственный допустимый
  baseline даёт exact identity даже с испорченным estimator, НО при
  допустимом upgrade утверждать non-decrease по true value нельзя:
  нужна отдельная safety certificate или достаточный gap.
- Невырожденный estimator 28−2·energy даёт baseline/upgrade
  estimate=-32/−26 при true=-30/−27; eps=2, отличающиеся nonzero errors
  2 и 1, estimated gap 6>4. Robust выбирает реальный advance energy=27.
  Resource units и focal-point energy safety не расширяются на physical
  system или полный размер/вычислительную стоимость архитектуры.
- Пять meaning-carrying results/declarations и три supporting declarations;
  всего +8, 4266. empirical premise registry: 201/37;
  structural(+10) происходит от явных h_stay/herr/etc и proof helpers.
  Нет скрытого independent-Noise, IID или universal-training доказательства.

## Finite Pareto execution policy (цикл 70)

- `ControllerProblem` задаёт objective `ControllerProblem.value`, настоящий переход `step : A → S → S`,
  model-safe predicate и раздельные модельные memory/operation counts.
  Feasible set строится через `Hagi.Growth.safeCandidates` с обоими caps.
- Селекция максимизирует nested Prod.Lex score
  `(value(next a s), −memory(a), −operations(a))`. Следствия — quality
  optimum в feasible-set, все equality coordinates у competitor,
  который не хуже во всех трёх целях, memory и operation bounds.
- Baseline-takeoff конфликт не переносится: `stageFamily` принимает
  пер-цикловый `StageInput` и вычисляет `advance`. Следовательно,
  `stageFamily_capability` содержит текущий growGain, а не copied effects.
- При единственном feasible действии выбирается baseline; при
  `step stay s=s` returned state точно равен s. Probe при generous caps
  выбирает реальный upgrade (idx1), при zero caps — baseline (idx0).
  Это минимальная служба выбора, не novelty claim на universal training.
- Explicit priority quality→memory→compute является выбранным правилом,
  не универсальным скалярным оптимумом. Value=-energy лишь surrogate probe.
  Resource 0/1/2 units не включают heap, metadata, padding или machine
  ABI; cost of enumerating candidates не доказан минимальным.
- Empirical registry=201/37, structural=9065. Proposition `ControllerProblem.safe` остаётся
  model-conditional: его наличие в record не заменяет actual certificate.
  Модель не является executable finite-word optimizer; no-op здесь
  честная остановка, а не learning improvement.

## Барьер fixed-effects и следующий контроллер (цикл 69)

`Hagi.Examples.state_capability_two_step_inconsistent` применяет существующий
`full_cycle_two_step_growth_inconsistent` к ТОЧНЫМ предпосылкам
state-level takeoff с дополнительным условием `2 ≤ T`. Вторая точка
конуса выводится через `frontier_cone_inductive` только при t=0. Значит,
полный цикл, копирующий старые StageEffects, несовместен с совпадающими
нижней/верхней geometric rates и положительными alpha, C₀.

- Старый `Hagi.Unified.state_capability_takeoff` не удалён и не изменён;
  новая отрицательная специализация явно показывает его границу при T≥2.
- Наличие имени h_exec не доказывает actual computation. Для исполняемого
  контроллера нужен successor state, фактические сертификаты перехода,
  свежий measurement каждого цикла и no-op fallback с таким же контрактом.
- `Hagi.Model.StageSemantics` уже предлагает другой, реализуемый класс:
  `StageInput` привязан к конкретному циклу. Новая теорема НЕ выводит
  его оптимальность; она исключает другой, несовместимый fixed-effects
  класс. Слои сохранены: Examples→Unified, а не наоборот.
- Registry получил 201 occurrence: ровно пять h_emp-параметров этой
  отрицательной специализации добавлены к former 196. Это не аналитическое
  замыкание. Mathematical implication отделён от physical fidelity.
- Scientific retrieval: Haroon и Fleming, Certified Safety Curation
  (`10.48550/arxiv.2609.12014`) прямо различают сертификацию training
  set и policy, а cost report и cost bound. Поэтому следующий Pareto
  controller обязан различать certified transition, actual quality,
  память и computation; отказ/no-op не равен оптимальному обучению.



## Инвентарь модельных предпосылок (цикл 68)
Следующие алгоритмические специализации должны потреблять
`assumptions.lock` как индекс фактических ∀-параметров, а не Markdown.
Его создаёт `AssumptionBinders.lean` после штатного root build.

- В inventory v2 каждое входное условие снабжено module,
  FQ declaration, ordinal и type. Старые текстовые 38/113 заменены
  фактическими 196 binders семейства h_emp в 36 модулях и 42 label-семействах.
  Упоминания в docstrings или body приложений не маскируются под binders.
- Одинаковое label в двух declarations — разные occurrence. Одна
  repeatable модельная посылка НЕ становится несколькими новыми
  физическими неизвестными. Registry это НЕ digest доказанности или
  полное число всех теоретических препятствий.
- Дополнительный інвентарь h-prefix hypotheses: 9020 form parameters
  in 407 modules. Сюда входят обычные mathematical conditions, не только
  external measurements. Unnamed classes, records and other identifiers
  outside this explicit naming convention remain separately reviewable.
- Whole-identifier execution marker фиксирует 41 name-candidate от
  восьми labels, а не четыре damaged fragments старого regex. Для
  genuine execution controller нужны actual successor functions и effects,
  а не только имя аргумента вроде h_exec.
- Information domain: 5 canonical, 7 legacy plus separate matrix
  spectral entropy. `entryCount` — index-counter и исключён из primitives.
- Четырнадцать regression/provenance tests PASS. Поиск типа и primitive
  object fail closed при ошибках загрузки; предыдущий text-scan не
  является fallback. Physics, stochastic dynamics, telemetry и optimality
  не выводятся из изобретённого inventory автоматически.

Эта запись не новый training algorithm, а инфраструктура для выведения
следующих конкретных fixed-model closures без иллюзорного их численного
уменьшения. Поддерживается работа Cycle 66–67 над budget/CE ядрами.

---

## Каноническое CE/KL-ядро (цикл 67)

- `ceDef q p = −Σ q·log p` — единый объект нижнего Prelude.
  `Data.crossEntropy` и `Data.CE` являются aliases к нему;
  `crossEntropy_eq_ceDef`, `CE_eq_ceDef` фиксируют мосты rfl.
  `ceDef_self` отождествляет CE q q с `entDef q`.
- `klDef_eq_ceDef_sub` выводит точное
  `klDef q p = ceDef q p − ceDef q q` при `∀v,pv ≠ 0` и произвольном q.
  Если qv=0, внести вклад 0 в обе стороны можно явно; иначе применяется
  `Real.log_div`. Сохранённые `kl_eq_ce_gap`, `kl_excess_cross_entropy`
  получают результат от ядра, сохраняя прежние hq/hp и порядок аргументов.
- Для ансамбля на Fin 2 с q=[0,1],p=[1,2] обе части identity дают
  log(1/2). На Fin 1 при q=2,p=0 identity НЕ верна: klDef равен 0,
  а CE gap равен 2·log 2. Поэтому условие p≠0 не выбрасывается.
- Старые дубликаты алгебры не оставлены параллельно канону. Top-k,
  DistillRecursion и ArchitectureTheorem перенесены на alias-aware
  unfolds; утверждения consumers и import DAG сохранены.
- Результат не отождествляет total real KL при unsupported inputs с
  extended ENNReal KL.   Неординарность, stochastic training, expressivity и
  global optimal architecture этим рефакторингом не доказываются.
  Nonnegativity KL самостоятельно сохраняет свои conditions.
- Пять новых declarations; family cross-entropy имеет один shared body.
  Полный Root build и probes прошли, только стандартные axioms.

---

## Непрерывная экспоненциальная аллокация (цикл 66)

Для конечного НЕПУСТОГО множества индексов с `c_i > 0`,
`κ_i > 0`, w_i > 0 минимизируем именно
`Σ_i c_i·exp(−κ_i·r_i)` при `Σ_i w_i·r_i = B`, где `B,r_i ∈ ℝ`.
w_i — только стоимость в бюджете, НЕ множитель residual.

- `weightedExpBudget`: `A = Σ w_i/κ_i > 0`
  (`weightedExpBudget_pos`).
- `weightedExpLogCoeff`:
  `C = Σ (w_i/κ_i)·log(c_i·κ_i/w_i)`.
- `weightedExpPrice`: `λ = exp((C−B)/A)`.
- `weightedExpAllocation`:
  `r*_i = (log(c_i·κ_i/w_i) − (C−B)/A)/κ_i`.
- `weightedExpAllocation_budget` доказывает точное выполнение
  равенства бюджета; `weightedExpAllocation_marginal` — условие
  `c_i·κ_i·exp(−κ_i·r*_i) = λ·w_i`.
- `weightedExpAllocation_optimal` доказывает глобальный минимум
  суррогатного residual среди ВСЕХ допустимых вещественных r.
  Tangent-теорема не перекопирована: доказательство вызывает
  существующую `rankResidual_equalized` при стоимости w_i+0.

Это оптимум непрерывной выбранной модели, не integer-rank/bits,
активная nonnegative truncation, размер памяти, hardware latency
или оптимальность нейросети. Scientific-выдача по общему термину
water filling была отклонена как нерелевантная rank-доказательству.
Нетривиальный двумерный witness выдал `r*=(4/3,2/3)` при
`c=(2,1), κ=(1,2), w=(1,1), B=2`; другая допустимая `(0,2)` строго
хуже. Строгость получена из `(1−x)²(x+2)>0` для `x=exp(−4/3)∈(0,1)`.

---

## 0. Главный цикл: certified loop (Gen-3, канонический)

Единый сертифицированный цикл обучения. Плоские капстоуны
поколения Gen-1 (`MasterHAGI*`, `grand_synthesis`)
`@[deprecated]`; Gen-1-семантика копируемых эффектов
доказуемо противоречива на T = 2

```
loop t = 0..n:
  1. ИЗМЕРИТЬ        obj (энергия), M.evaluate (качество),
                     spend (стоимость) из состояния
  2. СЕРТИФИЦИРОВАТЬ StepCert на переходе s→s':
        trans   : HonestTransition — спуск зависим от
                  исполнения: obj s' ≤ obj s − drop, drop > 0
        quality : FloorKept M s' floor — покомпонентный
                  пол качества (НЕ скалярный Qgen:
                  `qgen_hides` — контрпример)
        budget  : b' ≤ b − spend, 0 ≤ spend
  3. COMMIT/HOLD     без сертификата — hold
                     (`gate_never_increases`: энергия
                     не растёт НИКОГДА)
  4. СТОП            бюджет исчерпан / floor достигнут
```

- Итог горизонта (`certified_loop`, Unified/CertifiedLoop):
  Σdrops ≤ obj₀ − objₙ ∧ FloorKept ∧ 0 ≤ bₙ ≤ b₀ − Σspends.
- Строгость (`certified_loop_strict`): при n ≥ 1 спуск
  строгий, objₙ < obj₀.
- Весь горизонт (`certified_loop_all`): floor держится на
  КАЖДОМ промежуточном состоянии.
- Не-вакуозность (`quad_loop_horizon`): исполняемая
  машина (квадратичная, полушаг η = 1/2 — энергия × 1/4
  за шаг) инстанцирует сертификаты на любом горизонте
  (`quad_witness_T3`, `quad_witness_T10`).
- Закрепление: `master_hagi_challenge_v3` — comparator-гейт
  CI (пин типа StepCert, аксиомы чистые).
- Операциональные ядра `CertStep` (цикл 46):
  `logitStepCertExactCore` (scalar large-step CE),
  `ncMinimalStepCert` (энергия = gain нейрокомпьютера),
  `trainStepMinimalCert` (точный drop TrainState).
  Цикл 47 добавляет `GrowthComputedCert.stepCert` и
  `mergeStrictCertStep` (не нулевой Jensen gap).
  Исполнение даёт drop и actual без `h_emp_*`; полы, риск
  и бюджет подключаются как расширения, не подмена ядра.

## 1. Выбор действия: argmax Γ/K

- Теоремы: `ratio_dominance`, `budget_allocation_dominance`,
  `argmax_pair_certified` (Budget/CertifiedArgmax).
- Алгоритм:

```
for i in ACTIONS:                     # merge/joint/grow/
                                       # internalize/prune
    Γ_i = сертифицированный прирост:
        merge:   G = JensenGap ≥ 0    # MergeBridge
        joint:   η‖d*‖²/2             # safeQP_descent
        grow:    growGain (h_emp_)
        prune:   экономия − δ²/4
    K_i = измеренная стоимость
choose argmax Γ_i/K_i                  # доминирует любую разбивку
```

- Контрпример-предостережение: `tie_ambiguity` — при малых
  зазорах argmax противоречив; порог задаётся certified-полем.
- Запрет: не выбирать по standalone CE — `selection_hurts`.

## 2. Безопасный шаг: SafeQP (без learning rate)

- Теоремы: `safeQP_exists_unique`, `safeQP_descent`,
  `safeqp_inactive`, `safeqpEtaMax` (Step/ProjectionDescent,
  Step/MetricSafeQP).

```
d* = proj_C(g₀),  C = {d : ⟨g_i, d⟩ ≥ −ε_i}   # старые домены
η* ≤ safeqpEtaMax = min(1/L, ...)              # аналитический
если g₀ ∈ C:  шаг неактивен (d* = g₀)
```

- Гарантия спуска (joint_stage):
  E′ ≤ E − η⟨g₀,d*⟩ + Lη²‖d*‖²/2 ≤ E − η‖d*‖²/2
  при η ≤ 1/L и ‖d*‖² ≤ ⟨g₀,d*⟩.
- Оптимальный η (R347, StageCalculus):
  `quadratic_bound_max` — безусловный потолок модельного
  спуска inner²/(2L·dnorm²) при η* = inner/(L·dnorm²);
  `eta_star_exceeds_cap` — при certified descent η* > 1/L,
  кап активен; `joint_stage_cap_optimal` — на допустимом
  интервале оптимален η = 1/L, спуск dnorm²/(2L);
  `cap_cost_factor` — цена капа = фактор inner/dnorm² > 1.
  Правило: η = 1/L всегда (не настраивать); усилие — не в
  η-тюнинге, а в росте dnorm² (quality of direction).
- LR↔batch эквивалентность (`lr_batch_equivalence`,
  StochasticSafeQP; Smith et al. 1711.00489): шумовой бюджет
  шага η·noiseEps ∝ ησ/√m инвариантен при (η, m) → (kη, k²m).
  Правило планировщика: вместо снижения LR в k раз —
  увеличение batch в k² раз; сертификаты
  `stochastic_safeQP_feasibility` сохраняются на том же δ,
  а последовательных обновлений на ту же кривую — в k раз
  меньше (больше параллелизма). 

## 2b. Сжатые шаги: sign/Lion/SAM (Unified/SignDescent)

Компрессия шага с сертификатом чистого спуска. Ключевой
факт: НЕмасштабированный sign-шаг НЕ выровнен (норма
знакового вектора = число ненулевых координат, может
превышать ℓ₁-норму градиента) — масштаб обязателен.

```
s = ‖g‖₁ / n                            # signScale
шаг = x − η·s·sign(g)                   # η ≤ 1/L
```

- SignSGD: `sign_scaled_aligned` — выровненность
  (nrm2 ≤ inprod при s = ‖g‖₁/n); `sign_descent` — чистое
  убывание η(1−Lη/2)·s²·nnz (Bernstein 1802.04434: связь
  signSGD с нормализованным SGD).
- Lion (момент m): `scaled_sign_aligned_of_coherence` при
  согласованности момента с градиентом
  (‖m‖₁/n·nnz(m) ≤ ⟨g, sign(m)⟩); `lion_descent` — чистое
  убывание (Chen 2302.06675).
- Оптимальность знака: `sign_is_pointwise_max` — знак
  максимизирует ⟨g, v⟩ на всём ℓ∞-кубе |v i| ≤ 1 (векторное
  ядро спектральной оптимальности Muon;
  `muon_alignment_optimal` — матричная форма).
- SAM: `sam_descent_bridge` — спуск δ по worst-neighbor
  цели переносится на истинный лосс как δ − sharp (острота
  samW − L); плоский случай `sam_descent_flat` — чистый
  спуск (Foret 2010.01412). Правило: SAM-спуск честен
  ровно настолько, насколько найденный минимум плоский.
- Правило для сжатых машин: сначала SafeQP-направление
  (η = 1/L), затем компрессия шага до знаков с масштабом
  s = ‖g‖₁/n — сертификат спуска сохраняется формально.

## 2c. Точный large-step сертификат scalar logit CE

- `logitCE_strictAnti`: функция `log(1+exp(−w))` строго
  убывает на всём ℝ; `descent_step_strict`: при любом η > 0
  шаг `w′ = w + η/(1+exp(w))` строго уменьшает CE.
- Алгоритм (`logitStepCertExact`, `logitStepCertExact'`):
  вычислить новый вес и положить сертифицированный drop равным
  ТОЧНОМУ `logitCE w − logitCE w′ > 0`; бюджет требует
  η ≤ budget, полы следуют из `logitCE_nonneg`. Кап η ≤ 2
  не нужен для положительности точного drop в этой scalar
  one-example модели; на исходном диапазоне 0 < η ≤ 2
  точный спуск не меньше старой оценки
  (`logit_exact_drop_dominates`).
- Граница применимости: это не теорема о large-step GD для
  общей логистической регрессии; там возможны осцилляции и
  циклы (Wu et al., DOI `10.48550/arxiv.2402.15926`;
  Meng et al., DOI `10.48550/arxiv.2406.05033`). Расширение
  на несколько примеров/параметров требует нового доказательства,
  агрессивные шаги вне scalar-модели — только через measured
  commit/hold, не через эту теорему.

## 3. Гейт слияния: реальный CE-зазор

- Теорема (Unified/MergeBridge): CE(t, mid) = mean CE −
  jensenGap(z₁,z₂), jensenGap ≥ 0 — выводится из Core-lse
  теории, не постулируется.
- Правило: сливать пару, если jensenGap ≥ порога; экономия
  экспертов без роста CE гарантирована теоремой.
- Строгость (R356, `jensenGap_pos_witness`): при реальном
  несогласии экспертов (z₁=(0,0) vs z₂=(a,−a), a≠0) зазор
  строго положителен: ½log(cosh a) > log(cosh(a/2)) —
  слияние расходящихся экспертов строго лучше среднего,
  не-idle свидетель.

## 4. Квантование: тернарная сетка + мост потери

- Тернарное округление: |w − qTern| ≤ s/2 (Energy/Ternary).
- Мост в потерю (QuantBridge):
  - `quant_loss_bridge`: ‖(Ŵ−W)x‖ ≤ D·√(d_in·d_out)·‖x‖;
  - `quant_frob_loss`: ΔE ≤ κ_F·D·√(d_in·d_out);
  - `compress_chain_cost`: |ℓ(W)−ℓ(W″)| ≤ κ_F·(δ₁+δ₂);
  - `frob_minkowski`: норма-Минковского + Коши–Буняковский.
- Compress-стадия (compress_stage): E′ − E ≤ κ·s·qerr при
  qerr ≤ 1/2 — из этих канонов.

## 5. Спектральный отбор (Flywheel-порт)

- `eckart_young_frobenius`: усечение SVD оптимально по
  Фробениусу; Weyl-стабильность; `mdlJ_first_order`,
  `mdl_rank_ce` — MDL-ранг первого порядка.
- Правило: ранг k выбирать по MDL-критерию; потеря
  контролируется сертификатом Эккарта–Юнга.

## 6. Бюджет битов: water-filling

- `transfer_exact`: маржинальный обмен битами точен;
  `two_layer_equalize`: балансировка = water-filling;
  фактор-2 жадного инварианта (`stable_factor_two`).
- Сертификат поколения (distill_quant_composite):
  S_n + n·g ≤ E₀ + δ_n + totalError.

## 7. Концентрация и anytime-валидность

- Хёфдинг (MGF), Азума: P[ΣX ≤ −Δ] ≤ exp(−Δ²/2n).
- Freedman (`freedman_tail_low`):
  P[ΣX ≤ −Δ] ≤ exp(−Δ²/(2(V+bΔ/3))) — адаптивно к
  дисперсии; при V ≪ n сильнее Азумы.
- Мартингальные успехи: `adaptive_success_freedman`,
  anytime-формы (AnytimeValid) — доверительные границы
  валидны при произвольной остановке.

## 7b. Grokking-расписание (R366, Recurrence)

- `grokking_threshold_time`: остаточная динамика
  r(t+1) = r(t) − ηλ·r(t) достигает порога ε к моменту
  T = ln(r₀/ε)/(η·λ) — время генерализации управляется
  ПРОИЗВЕДЕНИЕМ learning rate × weight decay (формальное
  ядро спектральной теории grokking, arXiv:2609.26679).
- Правило планировщика: для целевого времени генерализации T*
  выбирать η·λ ≥ ln(r₀/ε)/T*; при фиксированном η (кап 1/L,
  R347) это задаёт weight decay λ — ещё один гиперпараметр
  выведен, а не настроен. Фазовая геометрия: слишком большое
  λ (ηλ > 1) — расходимость (условие ηλ ≤ 1 в теореме).

## 7c. Heavy Ball: точная критическая траектория (цикл 43)

- `hb_pair_second_order`: старая пара `(e,v)` имеет свободный
  коэффициент `β + η·(1−β)`, а не `β`; характеристический
  многочлен canonical second-order модели нельзя неявно
  применять к этой паре.
- Для canonical критической рекурренты при `ρ ≠ 0`
  алгоритм вычисляет `C = e₀`, `D = e₁/ρ − e₀`; тогда
  `e_n = (C+D·n)·ρ^n` (`hb_repeated_root_closed_form`,
  обратный witness — `hb_repeated_root_form_solves`).
  Сама оценка `hb_critical_trajectory_bound` верна при
  `ρ > 0`; для затухания дополнительно требуется `ρ < 1`.
- Сертифицированный runtime-stop при `0 < ρ < 1`:
  принимать шаг n только при вычисленном `(|e₀|+|D|·n)·ρ^n ≤ ε`; тогда
  `|e_n| ≤ ε` следует из `hb_critical_trajectory_bound`.
  Чистая оценка `Cρ^n` запрещена: кратный корень даёт
  Jordan-фактор n. Внутренние моды с различными корнями —
  следующий алгоритмический frontier, не эта теорема.

## 7d. Heavy Ball: различные корни и двухкорневой темп

- `hb_two_root_closed_form`: если λ₁,λ₂ — корни одного
  характеристического многочлена и начальные данные
  разложены как `e₀=A+B`, `e₁=Aλ₁+Bλ₂`, алгоритм
  ошибки вычисляется как `e_n=Aλ₁^n+Bλ₂^n`; обратный
  witness — `hb_two_root_form_solves`.
- При `λ₁≠λ₂` (`hb_distinct_root_init`,
  `hb_distinct_root_explicit`):
  `A=(e₁−λ₂e₀)/(λ₁−λ₂)`,
  `B=(λ₁e₀−e₁)/(λ₁−λ₂)`.
  Знаменатель проверяется только разностью корней;
  нулевой корень допустим.
- Темп вычисления (`hb_two_root_norm_bound`,
  `hb_two_root_spectral_norm_bound`): для β>0 и
  `t²−4β ≤ 0`, `‖e_n‖ ≤ (‖A‖+‖B‖)·(√β)^n`.
  Это замыкает внутреннюю scalar-моду без Jordan-фактора;
  кратный корень обслуживается отдельно по 7c.
- Runtime: принимать n, если вычисленный RHS не превышает ε.
  Полный спектр по ортонормированным модам и коэффициент,
  зависящий от обусловленности, — следующий шаг, не
  содержание этих скалярных теорем.

## 7e. Аналитическое закрытие предпосылок

- `pl_stop_certificate_quadratic`: для квадратичной цели
  `E(w)=μ(w−a)²/2` с `L*=0` PL-форма выполняется точно;
  stop certificate вызывается без `h_emp_pl`.
- `audit/assumption_closure.md` фиксирует все 45 файлов lock:
  существующие smooth/lip/dist/grow/merge выводы и настоящие
  trust boundaries (independence, physics, telemetry).
- `forgetting_kl_quadratic_unit_fisher` и
  `tldr_two_tier_safety_unit_fisher`: скалярная модель задаёт
  KL как dW²/2, единичная F и её inner-product равенство
  доказываются, а h_emp_second здесь не нужен. Это не универсальная
  вероятностная KL-формула для всех распределений.
- `mopd_kl_scaling_warning_fivefold`: в явной fivefold-модели
  coэффициент политики равен пяти по построению, поэтому достаточный
  ε-budget выводится без h_emp_scaling. Произвольный λ отдельно
  измеряется/моделируется и этой теорией не закрывается.
- `projected_gradient_lipschitz` и
  `cut_signal_attention_quant_projection`: для scaled projected
  gradient достаточно нормы ортопроектора ≤1, поэтому здесь
  `h_emp_attsmooth` вывести можно. Выбирать retained subspace,
  измерять clamp/probe radii и передать границу в Cut-треугольник.
  Это строго явная модель общего P для двух карт, не доказательство
  адаптивного softmax attention и не оптимальность выбора маски.
- `quadratic_central_error_lt_forward_error` (цикл 59): если
  L>0 и direction ненулевое, для того же σ центральная разность
  строго точнее по абсолютной ошибке, чем `forwardQuadraticProbe`.
  Выбирать central только явно допуская quadratic модель и
  counting evals отдельно, не обещая бесплатную универсальную оценку.
- `probeOptimalStep` и `probeCost_le_optimal` (цикл 60): минимум
  явной арифметической границы aσ²+b/σ достигается при
  `(b/(2a))^(1/3)` для a,b>0; `probeCost_lt_optimal` исключает любой
  другой положительный σ. Использовать только после доказанной
  модели остатка/noise: формула не распознаёт HAGI loss автоматически
  и не считается доказательством floating или stochastic guarantees.
- `noisyCentralCubicProbe_optimal_bound` (цикл 61): в явной directional
  cubic/noise модели выведены коэффициенты `(|c|/6)‖v‖⁶` и `δ`;
  оптимальный шаг цикла 60 уменьшает доказанную upper bound до минимума.
  Обе погрешности измерений должны быть ограничены δ. Сравнивается
  error(opt) с cost(σ), а не случайная actual error одного σ с другой.
  Не заявлять полные floating/statistical/Frechet-гарантии.
- `probeQuadraticEnergy_hasFDerivAt` и
  `probeCubicEnergy_hasFDerivAt` (цикл 62): обе algebraic fields теперь
  доказаны настоящими Fréchet-производными по x на своих явных носителях.
  Предыдущие cost ошибки относятся к настоящим направленным derivatives,
  а не только к произвольно выбранным field. Это не перенос на arbitrary loss
  или на изменяемое направление v, и не floating-gradient утверждение.
- `probeGridRound_abs_error_le` (цикл 63): half-step bound выводится
  для dense lattice, отличной от saturating ternary format. Используйте
  это отдельное семейство модели для выводимой precision границы.
- `gridCentralCubicProbe_optimal_bound`: вместо abstract ε caps округление
  уже реализовано на двух endpoint values. Применять best σ только при
  фиксированном grid>0, c,v≠0, без расширения на finite-word. Cost bound
  не означает strict ordering фактических ошибок или оптимальную сетку.
- `boundedProbeOptimalStep` и `probeCost_le_boundedOptimal` (цикл 64):
  при положительных coefficients и σmax выбирают min globalRoot,σmax,
  доказывая минимум cost на `(0,σmax]`. Нельзя применять вне этой области.
- `ternaryRoundCap_abs_error_le` и `ternaryCubicStepBudget` вычисляют
  actual saturation error из qTern in/out branches и cubic energy growth.
  `ternaryCentralCubicProbe_optimal_bound` минимизирует только вычисленную
  guarantee для fixed level + σmax, не оптимизирует разряд/память сам по себе.
- `ternaryValueDecode_encode` (цикл 65): semantic codec превращает state
  `qTern` в trit и обратно. Он сохраняет quantizer value, а не raw value.
- `ternaryByteBlock_injective` и `ternaryBlockDecode_encode`: существующая
  base-3 упаковка получает typed BitVec 8 и обратный decoder по координатам.
- `ternaryBlock_seven_bit_impossible` показывает минимум 8 битов для
  пяти-place uniform alphabet block. Не объявлять этот блок оптимальным
  форматом всей модели: level metadata и runtime overhead вне него.
- `centralQuadraticProbe_exact` (цикл 58): в том же translated
  quadratic классе центральный probe вместо одностороннего вычисления
  возвращает ⟨g(x),v⟩ точно при σ>0. Использовать его для точной
  directional оценки, но не обещать оптимальный σ или меньше evals.
- `fd_probe_error_quadratic` (цикл 57): для выбранного
  `probeQuadraticEnergy` вычислять forward-difference ошибку как
  (L/2)σ‖v‖² из самой энергии, без отдельной hmodel-матрицы.
- `probeQuadraticGrad_lipschitz`: общий для двух карты quadratic
  поле сохраняет Lipschitz по L с общим центром; это источник
  h_emp_attsmooth для Cut-инстанса, но не всего нелинейного attention.
- `computedGenStep` и `generalization_safe_step_computed` (цикл 56):
  для canonical energy=growthQuad weights вычислить веса и energy
  одним шагом. Probe/risk поля остаются неизменными именно этой
  hold-моделью, поэтому fit/G/risk доказаны без эмпирических wrappers;
  возможные новые оценки probe отдельно исследуются, не предполагаются
  неизменными автоматически или устанавливаются в фиктивную константу.
- `scripts/AssumptionScan.py` после цикла 55 исключает comments из
  premise-registry: действительный legacy count 137 содержал 24
  комментарных вхождения, реальный список locks 113. Классы закрывают
  только proofs; само сокращение реестра не считается новой теоремой.
- Общие conditional lemmas сохраняются только как интерфейс
  классов функций. Запрещено выдавать `EmpiricalPremises.holds`
  за доказательство гладкости: `premises_give_smooth` требует
  явной smoothness-модели; документация исправлена соответственно.

## 7h. Heavy Ball: вещественные корни и доминирующий темп

- `hb_two_root_norm_cap`: по отдельности полученные границы
  модулей λ₁ и λ₂ дают одну экспоненциальную оценку без
  требования одинаковых модулей. Нулевой и отрицательный
  корни допустимы.
- `hb_real_root_pm`: при D=t²−4β≥0 использовать
  явные корни `(t±√D)/2`; `hb_real_root_pm_norm`
  оценивает их общим знаменателем `r=(|t|+√D)/2`.
- `hb_real_two_root_norm_bound`: полная двухкорневая
  траектория удовлетворяет `‖e_n‖≤(‖A‖+‖B‖)r^n`.
  Это честная triangle-верхняя оценка, не обещающая точный
  max modulus. При D≤0 сохранять более точную оценку
  `r=√β` из 7d, при кратном корне — Jordan-форму 7c.
- Runtime: вычислить r, затем принимать n, если коэффициент
  начальных данных умноженный на r^n не превышает допуск.
  Векторный оператор пока оценивать только после разложения
  по модам; следствие о κ вне доказанного скалярного API.

## 7i. Heavy Ball: L²-сборка ортонормированных мод

- `hb_two_root_l2_bound`: координатно заданные корни и стартовые
  коэффициенты дают общую оценку векторной ошибки
  `‖e_n‖ ≤ sqrt(sum((‖A_i‖+‖B_i‖)^2))·ρ^n`.
  Используется Euclidean L²-норма, не сумма модальных амплитуд.
- `hb_two_root_orthonormal_bound`: тот же результат в исходном
  векторном пространстве через изометрию ортонормированного базиса.
  Алгоритм считает модальные коэффициенты и общий допуск ρ,
  затем использует глобальный L²-бюджет для runtime-stop.
- Вещественные корни берутся из 7h, комплексные — из 7d;
  кратные корни отдельно обслуживаются Jordan-формой 7c.
- Это НЕ автоматическая теорема спектрального существования и
  НЕ универсальный rate для stochastic/nonconvex HB. Цель —
  далее ограничить коэффициент через root separation и κ.
  Контекст по ограничениям SHB: Dang et al., 2401.06738.

## 7j. Heavy Ball: точный взвешенный L²-stop

- `hb_two_root_l2_weighted_bound`: каждая мода имеет свой тип
  затухания ρ_i; вычисляемая оценка векторной ошибки —
  `sqrt(sum(((‖A_i‖+‖B_i‖)·ρ_i^n)^2))`.
- `hb_two_root_orthonormal_weighted_bound`: та же сумма переносится
  через базисную изометрию в исходное векторное пространство.
  Общая оценка из 7i остаётся дешёвым uniform-вариантом, не заменой
  точной взвешенной формулы.
- Runtime: накапливать квадраты C_i²·ρ_i^(2n), взять sqrt
  и остановиться, когда полученная сумма не превышает допуск ε.
  Равенство и оптимальность именно этой upper-bound не утверждаются.
  Следующий вычислительный шаг — direct bound C_i через root gap
  и параметры состояния/κ, а не только через данные A_i/B_i.

## 7k. Heavy Ball: модальный префактор от начальных ошибок

- `hb_distinct_root_coefficient_sum_bound` выводит оценку
  `‖A‖+‖B‖ ≤ 2(‖e₁‖+ρ‖e₀‖)/gap`, где gap — нижняя граница
  модуля разности корней. Нулевой знаменатель исключён положительным
  gap, а не отдельным необъяснённым признаком различности.
- `hb_two_root_l2_initial_gap_bound` восстанавливает модальные A/B
  из e₀,e₁ и включает соответствующую вычислимую оценку в
  точную взвешенную L²-сумму из 7j.
- Runtime: вычислить gap_i и квадратичную сумму префакторов;
  малый gap автоматически увеличивает допуск, поэтому правило не
  скрывает численную чувствительность Vandermonde-разложения.
- Это консервативная начальная norm-bound, НЕ доказанная оптимальная
  κ-формула. Осталось связать gap с curvature/pair параметрами
  исходной HB-динамики и завершить базисный переход этой версии.

## 7l. Heavy Ball: исходная пара и runtime-certification

- `hb_pair_second_order_complex` исключает velocity из реальной
  пары, установленной прежним scalar proof: получается
  `t=1+β−η`, `c=β+η(1−β)` для λ²−tλ+c.
- `hb_pair_l2_initial_gap_bound` строит взвешенный L²-bound с
  префактором от начальных ошибок/root gap непосредственно от
  первопорядкового состояния. Это НЕ замена c на коэффициент β
  canonical-квадратики.
- `hb_pair_orthonormal_initial_gap_bound`: в произвольном полном
  ортонормированном базисе использовать компонентные velocity/error
  измерения, корни/tolerance и базисную изометрию; A/B заполняются
  алгоритмически из e₀,e₁ и не вводятся как свободные данные.
- Runtime-stop обязан явно проверять root norm и positive gap;
  если модальные темпы <1, возникает вычислимый допуск затухания,
  а если ≥1 — только растущая верхняя оценка. Probe из этого
  цикла относится ко второму случаю и не моделирует training success.
  Оптимальная κ-конфигурация и глобальная сходимость доказаны
  этими тремя мостами НЕ будут; это точная модельная связь.

## 8. Мета-закон роста: конус и насыщение

- Конус (frontier_cone_inductive):
  F(t+1) ≥ ρF(t) + γC(t) ⟹ C₀(1+γk)^T ≤ C_T.
- Насыщение (pl_gap_lower_trunc):
  C_T ≤ C* − (1−σ)^T·(C*−C₀).
- Совместимость (`cert_horizon_bound`): логарифмический
  горизонт — взлёт и потолок совместимы только если
  (1+γk)^(T−1) ≤ σC*/((γk+σ)C₀); явная форма (R349,
  `cert_horizon_log_bound`): T ≤ 1 + [ln(σC*) −
  ln((γk+σ)C₀)]/ln(1+γk) — чем сильнее конус, тем короче
  совместимый горизонт.
- На состоянии: `StateBinding` — C(t) = (S t).capability,
  G(t) = growGain; конус на реальной траектории состояний.
- Каскад: `sustained_takeoff_trunc`, `growth_dichotomy`,
  `elasticity_chain`, `saturation_limit`.

## 9. Капстоун: HAGI-синтез на семействе доменов

- `HAGICert` (ArchitectureTheorem, Fin I — произвольное
  семейство доменов):

```
взлёт:   C₀(1+γk)^T ≤ C_T
потолок: C_T ≤ C* − (1−σ)^T(C*−C₀)
риск:    ∀ домен i:
         Σₜ risk(t,i) ≤ T·best(i) + R + ε₀/(1−ρₑ)
```

  (`hagi_synthesis`; риск-часть — `universality_longhorizon`.)
- Свидетели не-вакуозности: `trunc_nonvacuous`,
  `certifiedHAGI_nonvacuous`, `coupledHAGI_nonvacuous`,
  `masterhagi_growth_witness`, `cert_horizon_witness` —
  все структуры предпосылок населены конкретными
  траекториями.

## 10. Интернализация инсайтов и инсайт-канал

- `ce_gap_kl_identity`: KL-зазор как сертифицированный
  прирост; `forgetting_kl_bound` — забывание ограничено.
- `liveness_two_axis`: цикл не замерзает, пока жива любая
  ось (консенсус/новизна); заморозка = честный стоп.

## 11. Контроллерные гейты (Runtime/ControllerGates)

- Variance gate: logitRange(f) масштабируется линейно при
  делении температуры; R²/8-граница контрактуется
  квадратично; перелёт R ≥ R̄ чинится точно τ = R/R̄
  (`variance_gate_contract`, `variance_gate_normalize`).
- Trust region: шаг (R/‖x‖)•x имеет норму ровно R и
  ближайший к x в шаре (`trust_region_proj_norm`,
  `trust_region_nearest`).
- Динамический роутинг: инжекция 1/√(2L) на ветвь даёт
  суммарную дисперсию v/2 независимо от глубины пути.

## 12. Направляющие константы (вместо гиперпараметров)

- η: аналитический `safeqpEtaMax` (не гиперпараметр);
- порог слияния: jensenGap-гейт (измеренный, не настроечный);
- ранг: MDL-критерий первого порядка;
- τ variance gate: R/R̄ (точный ремонт перелёта);
- горизонт: `cert_horizon_bound` (логарифмическая стыковка
  γk-взлёта и σ-насыщения);
- бюджет битов: water-filling `two_layer_equalize`.

## 13. Термостатный контроллер (Growth/Thermostat,
Probability/GibbsConcentration)

Отжиг T_t = T₀·α^t (0 < α < 1) как управляющий контур
селектора; все величины сходятся к пределам без настройки
гиперпараметров.

- Монотонность: `thermostat_monotone` — T_{t+1} ≤ T_t;
  `thermostat_tendsto_zero` — T_t → 0.
- Полярный Ньютон: `newton_step_descent` — итерация
  x ↦ (x+2)/3(x) монотонно спускается при x ≥ 1 и зажата
  1 ≤ newtonIter x₀ ≤ x₀ (`newton_iter_bracket`).
- Сертификат состояния: `hagi_certified_state` —
  ∃N ∀t≥N: stop ∧ gate ∧ концентрация ∧ ∃ε-репрезен-
  тативная точка (R412+R413).
- ЧЕТЫРЕ ЧИСТОТЫ вдоль отжига:
  - метрика: `certified_state_tv_tendsto` — TV → 0;
  - энергия: `certified_state_energy_tendsto` —
    ⟨E⟩_t → E*;
  - свободная энергия: `certified_state_free_energy_-
    tendsto` — F_t → E*;
  - энтропия (Нернст): `certified_state_entropy_tendsto` —
    S_t → 0;
  - избыток: `certified_state_excess_tendsto` —
    ⟨E⟩−F → 0.
- Lp-вертикаль (R498–R508, Probability/ExpChord): кирпичи `exp_chord`/`log_chord` (двухточечные хорды e^{rx} и ln), `amgm_weighted`, `young_two`, `hoelder_finite`/`hoelder_weighted`, `minkowski_finite`/`minkowski_weighted`, `lp_one_le_card`, `lp_mean_le_rms`. Моментная вертикаль R492–497 (Popoviciu/Chebyshev/Cantelli/Bhatia–Davis, Probability/MomentBounds): хвостовые критерии ранней остановки охлаждения (Var_{p_T}(E) ≤ ε_var ⟹ стоп-гейт термостата); Lp-нормы — сертифицированные границы для merge/регуляризации.

- Термостатный контракт (R510–512, GibbsFluctuations): гейт Var_{p_T}(E) ≤ ε Certified при T ≤ δ/ln(Δ²(n−1)/ε); сходимость Var→0 вдоль T_n=δ/(n+1); явное число шагов n+1 ≥ ln(Δ²(n−1)/ε) — охлаждение останавливается не раньше сертификата и не позже необходимого.
- Калориметрия: `certified_state_excess` —
  ⟨E⟩−F ≤ (Δ+T₀)·C·θ.
- Admission-гейт памяти: `admission_margin_sound` —
  ε_cert-запас = сертификат soundness: истинный выигрыш
  покрывает стоимость + риск.

## 14. Hedge-селектор и regret (Probability/MWU)

Мультипликативные веса как универсальный селектор;
температура = обратный learning rate (η = 1/T).

- Одношаговое зажатие потенциала: `mwu_potential_squeeze`
  — ηℓ_min ≤ −ln Z′ ≤ 2η⟨ℓ⟩ (hedge-ядро без рядов:
  (1+2x)(1−x) ≥ 1 ⟹ e^{−2x} ≤ 1−x).
- Телескоп: `mwu_uniform_squeeze` — потенциал кумулятивных
  потерь зажат с двух сторон при uniform-старте.
- √-балансировка: `mwu_sqrt_bound` — −ln W ≤
  2√(η⟨L⟩·ln n) при η⟨L⟩ ≤ ln n (равновесное геометри-
  ческое среднее R443-пары; классическая regret-структура).
- Гиббс = hedge: `gibbs_hedge_squeeze` — при η = 1/T
  (1/T)E_min ≤ −ln((1/n)Σe^{−E/T}) ≤ 2(1/T)⟨E⟩.
- Репрезентативность: `mwu_representative` — выборка из
  hedge-распределения e^{−ηL} репрезентативна (мост
  Хёфдинг ↔ MWU; полный граф мостов: 4 вертикали,
  все 6 пар).

## 15. PAC-Bayes мост (Probability/GibbsConcentration)

Тождество Катони замыкает термодинамику и PAC-Bayes.

- Log-декомпозиция веса: `gibbs_weight_log_decomp` —
  ln(ρ_v·n) = ln n − ln Z − E_v/T (вес = сложение
  случайности, нормировки и энергии).
- KL-тождество Катони: `gibbs_katoni_kl` —
  KL(ρ‖unif) = −ln Z − ⟨E⟩/T + ln n; вместе с
  R422 (KL = ln n − S) даёт F = ⟨E⟩ − T·S — гиббсовская
  свободная энергия выведена из PAC-Bayes.

## 16. Ядро теории информации
(Probability/GibbsConcentration)

- Второй закон в общем виде: `finite_kl_nonneg` —
  KL(ρ‖γ) ≥ 0 для любых распределений (ln u ≤ u−1
  почленно с u := γ/ρ).
- Log-sum: `log_sum_ineq` (+ `_on` на подмножествах) —
  A·ln(A/B) ≤ Σa·ln(a/b) (нормализация + R447).
- Обработка данных: `kl_data_processing` —
  KL(Tρ‖Tγ) ≤ KL(ρ‖γ) для любого сжатия T
  (fiber-разложение + log-sum по слоям).
- Выпуклость: дуга R454–R457 — вогнутость ln →
  выпуклость x·ln x → скалярная x·ln(x/y) →
  KL по первому аргументу.
- Арифметика совместных: `kl_product_additive`
  (KL аддитивен на произведении), `entropy_subadditive`
  (S(joint) ≤ S₁+S₂), `entropy_chain` (цепное правило
  Шеннона), `joint_entropy_ge_marginal` (условная
  энтропия ≥ 0), `mutual_info_nonneg` (I ≥ 0).
- Равновесие: `gibbs_free_energy_identity` —
  F = ⟨E⟩ − T·S на Гиббс-мере.

## 17. Active-Inference вертикаль
(RAG arXiv 2607.13612)

- Прокси-дихотомия: `proxy_cert_preserved` /
  `proxy_cert_lost` — нижняя оценка энтропии
  сохраняет surprise-сертификат по построению,
  верхняя строго теряет; `gibbs_cert_bridge` — мост
  к Гиббс-равновесию (R462).
- Зазор суррогат/истина: `gap_decomposition` +
  `gapII_nonpos` + `gap_graceful` — три источника
  (miscalibration/bias/slack), смещение ≤ 0 для
  нижних прокси, линейная деградация.
- Компаундинг: `compounding_bound` / `compounding_sq`
  — e_H ≤ L^H·e₀ и e_H² ≤ (L²)^H·e₀²; MPC
  horizon-one обнуляет.
- EFE-потолок: `efe_ceiling` — G = P − I ≤ P;
  state-epistemic gap = взаимная информация.
- Амортизированная политика:
  `amortized_policy_bound` — суррогатный argmin при
  равномерном зазоре c исполняет в 2c от оптимума.

## 18. Pinsker-семейство и TV-дуальность
(Probability/GibbsConcentration)

- Капстоун MWU: `mwu_regret_regimes` —
  −ln((1/n)Σe^{−ηℓ}) ≤ max(2√(η⟨ℓ⟩·lnn), 2η⟨ℓ⟩);
  η = √(lnn/⟨ℓ⟩) даёт классический 2√(⟨ℓ⟩·lnn).
- Верхнее TV: `tv_le_pos_part_kl` — TV ≤ Σ_{q<p}
  p·ln(p/q). МАТАН-ЛОВЛЯ: линейное KL ≥ TV неверно
  (контрпример 0.368 < 0.4 — Пинскер требует √).
- Бхаттачарья: `bhattacharyya_cauchy` — BC ≤ 1
  (Коши-сумм); `one_minus_bc_le_half_kl` —
  1−BC ≤ KL/2 (per-v t−1 ≤ t·ln t).
- Пинскер: `pinsker_sqrt_kl` — TV ≤ √(KL)
  (тождество |p−q| = |√p−√q|(√p+√q) + Коши);
  `neg_log_bc_le_half_kl` — BC ≥ e^{−KL/2};
  `tv_le_sqrt_one_minus_exp` — Бретаньоль–Юбер
  TV ≤ √(1−e^{−KL}) (точнее при большом KL).
- Дуальность: `tv_dual_abs` — |E_p f − E_q f| ≤ TV
  для любой 0 ≤ f ≤ 1 (расщепление + f → 1−f).
- Совместная выпуклость: `kl_joint_convex` —
  классическое замыкание ядра инфо-теории.

## 19. Дониер-Варадхан и Cramér-вертикаль
(Probability/GibbsConcentration)

- ДВ-нижняя грань: `kl_variational_lower` —
  KL ≥ E_p f − ln E_q e^{f} (софтмакс-наклон
  r = q·e^f/Z + R447); точность:
  `kl_dv_attained` (f := ln(p/q), Z = 1);
  наклон-констант: `kl_chernoff_tilt`.
- Cramér-вертикаль (2401.01148, NeurIPS 2024):
  `cramer_tilt_kl` (пороговая форма),
  `cramer_sup_le_kl` (sup-форма через csSup_le),
  `cramer_cgf` (CGF-форма с центрированием),
  `subgauss_dev_kl` (λ*-подстановка, (E−μ)²/2σ² ≤
  KL — без дифф-исчисления).
- События и масштаб: `markov_finite` (t·p({g≥t}) ≤
  E_p g), `chernoff_event` (p({g≥t}) ≤ e^{−λt}·
  E_p e^{λg}), `exp_tilt_interpol` (интерполяция
  через R454 — 3 случая), `mean_shift_tv`
  (|E_p g − E_q g| ≤ (b−a)·TV через R473),
  Hellinger: `hellinger_sq_eq_one_minus_bc`,
  `hellinger_le_half_kl`.

## Честные границы (что НЕ выведено)

- Специализированные carriers имеют выводы для отдельных
  `h_emp_grow`, `h_emp_smooth`, `h_emp_lip`; произвольные
  stage-теоремы остаются условными. Их merge/compress-предпосылки
  также зависят от конкретного носителя и модели.
- Из списка AssumptionScan нельзя автоматически удалять premise:
  нужен derivation оставшегося binders и анализ всех callers.
- γ-дефицит mixer.gain→0 — не закрыт (контрпримерная зона).
- Плоские капстоуны (`MasterHAGI*`, `grand_synthesis`)
  депрекнуты и НЕ заменены выводом — их содержание
  поглощается условным `certified_loop`; полный вывод
  всех посылок из физики — открытый фронт.
- Closure gap: 286 library-листьев (оптимизаторы,
  attention-экономия, alignment) доказаны автономно, но
  не инстанцируют StepCert/DescentCore.Objective — их
  интеграция в certified loop открыта.
- Сертификатный веер: 8 представлений перехода не сведены
  к канонической цепочке Execution → Measurement →
  StepCert → CertifiedLoop.
- Полная Fannes-граница; anytime-Freedman (M∧V-форма).
- Lean↔Runtime property-тесты — требуют torch-рантайма.
