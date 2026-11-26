# Алгоритмы архитектуры и обучения

Цель — конечный проверяемый по шагам рецепт: качество на заданных данных, явная
цена представления и ресурсные ограничения. Это не универсальный рецепт
оптимальной сети. Различаем три уровня: операция над моделью, конечный
математический сертификат, измеряемая посылка внешнего цикла. Стоимость всегда
относится к указанной модели, а не к железу.

## Рецепт

Один цикл обучения и раздел, который доказывает каждый шаг.

| Шаг | Действие | Доказательство |
| --- | --- | --- |
| 0 | `W = C + R`: общее ядро + маршрутизируемые остатки; budgets и суммарная ошибка `‖W-S‖ ≤ e_shared+e_spectral+e_rank+e_quant+e_routing` | §1 |
| 0 | разрядность и начальный HNet ratio — только внутри их declared models | §6, §7 |
| 1 | выбрать batch; propensity `q_b ∝ abs(ℓ_b)` minimizes MSE unbiased estimator of `ḡ` | §4 |
| 2 | `D̄ = -ḡ`, `Ā = ‖ḡ‖²`, `R'²` = range-based `batchLogitRangeSquare`, `η = 4Ā/R'²` | §3.2, §3.9 |
| 3 | альтернативы при per-sample guard: `D̄=0` → hold; certified `D` или min-norm `segmentMinNorm`; QP: `safeqpEtaMax` | §3.2, §3.3 |
| 4 | собрать proposed successor; измерить CE каждого sample, риск opRisk, цену opCost | §9 |
| 5 | принять только если guard активен (`0 ≤ opCost ≤ budget`, samplewise CE не растёт, `0 ≤ opRisk`), иначе hold | §3.6, §9 |
| 6 | строгий сертификат принятого шага (`StepCert`, drop `2Ā²/R'²`), BF16-гард `4·eps < 2Ā²/R'²` | §3.7, §12 |
| 7 | записать шаг в каноническое ядро (`CertStep` / `HoldStep`, δ-ресурс, буферы оптимизатора); телескоп по траектории | §11 |
| 8 | оптимизатор-обёртка только по доказанному контракту (sign/Lion/SAM/HeavyBall, EF21-Muon) | §5, §13 |
| 9 | квантовать принятое представление (ternary/grid, per-block scale, residual VQ); сложить все error terms | §6, §15 |
| 10 | выбирать архитектуру по `finiteSelection` (исполняемый) или `minimumResource` (контракт); оценивать на новых данных anytime-конфиденсом, не на том же CE-чеке | §8, §14 |
| 11 | символьная голова (Венна/ANF) — точное исполнение и CE-выбор маски под гвардом | §17 |
| 12 | конфликт переменных — energy-контур: осадить латент `z`, заморозить, жадный спуск по полю L_i под гвардом `2ε`, стоп по разделению валидности | §18–§26 |

Граница результата — §10; карта теории — §27.

Группы разделов: архитектура и представление (§1, §6–§8, §15); loss и
сертифицированный шаг (§2, §3, §11, §12); данные и batch (§4, §14);
оптимизаторы (§5, §13); квантование и память (§6, §15); исполнение и runtime
(§9, §16); energy-based reasoning (§18–§26); теория (§27).

## 1. Архитектура: общее ядро и маршрутизируемые остатки

Исходные объекты — конечное непустое семейство экспертов Wᵢ, общее ядро `C` и
остатки Rᵢ. Требуем точной декомпозиции `W = C + R`; тогда вызов
[`factorizedEval`](Hagi/Architecture/FactorizedMerge.lean) возвращает исходного
эксперта по [`routed_eval_exact`](Hagi/Architecture/FactorizedMerge.lean).
Храним один `C` и отдельные малые остатки, а не копию всей сети на route.

Для усредненного [`fullMerge`](Hagi/Architecture/FactorizedMerge.lean) имеем
`fullMerge W = C + meanResidual R`. Если остатки приближены с ошибкой `δ_i`,
ошибка merge не превосходит среднего `δ_i`
([`factorized_error_bound`](Hagi/Architecture/FactorizedMerge.lean)).
Усреднение параметров не равно среднему логитов.

Для logits zₐ при `N > 0` —
[`ensemble_ce_le_mean_general`](Hagi/Math/Info/InfoCore.lean):

```
CE(t, v ↦ (∑a z_a(v))/N) ≤ (∑a CE(t,z_a))/N.
```

Это только pointwise CE-мажоранта среднего логита. Для смеси матриц при
фиксированном router — [`merged_output_exact`](Hagi/Ensemble/MergePrice.lean);
при смене `w` на `w'` добавляется drift-budget из
[`routing_drift_bound`](Hagi/Ensemble/MergePrice.lean).

Перед spectral/rank/ternary сжатием складываем ошибки, а не «экономию качества»
([`unified_error_budget`](Hagi/Architecture/FactorizedMerge.lean)):

```
‖W-S‖ ≤ e_shared + e_spectral + e_rank + e_quant + e_routing.
```

Если `0<R̄≤logitRange f`, берём `τ=logitRange f/R̄`:
[`variance_gate_normalize`](Hagi/Runtime/ControllerGates.lean) даёт
`logitRange(f/τ)=R̄`, а
[`variance_gate_contract`](Hagi/Runtime/ControllerGates.lean) контрактует
`R²/8`. Это масштабирование logits-контракта, не доказанное снижение CE и не
температура физического router.

Форму выбираем по счётным условиям:

- shared core + residuals: при `2 ≤ N` и `N(r(V+d)) ≤ (N-1)(Vd)`
  [`factorized_budget`](Hagi/Architecture/FactorizedMerge.lean) даёт
  `Vd + N(r(V+d)) ≤ N(Vd)`;
- block-diagonal + rank-`r` mixer: при `h > 0`, `2 ≤ N`, `3r < (N-1)h`
  структурированное представление меньше dense по
  [`block_lowrank_lt_dense_iff`](Hagi/Budget/JointCost.lean);
- одна активная конфигурация, `2 ≤ N`, `c+r ≤ d`: счётная модель
  multiply-add даёт `(c+r)d`, и
  [`active_beats_dense_family`](Hagi/Budget/JointCost.lean) сравнивает её с
  `N d²`. Это declared operation count, не wall-clock.

Точность всех пяти error terms проверяем на модели; из неравенств параметров не
следует равенство качества или ускорение обучения.

## 2. Предиктор и loss: конечная log-linear one-hot CE

Непустой конечный vocabulary `V`, размерность `d`, `X : Matrix V (Fin d) ℝ`, `θ
: EuclideanSpace ℝ (Fin d)`. По [`ceLogits`](Hagi/Model/CEDescent.lean) и
[`ceOneHot`](Hagi/Core/Concat.lean):

```
z(v) = ceLogits X θ v = (X *ᵥ θ.ofLp)(v),
lse z = Real.log (∑v exp(z(v))),
ℓ_t(θ) = ceOneHot t z = lse z - z(t).
```

Остаток и raw gradient ([`ceResidual`](Hagi/Model/CEDescent.lean),
[`residualTranspose`](Hagi/Model/CEDescent.lean)):

```
r(v) = softmax(z)(v) - (if v=t then 1 else 0),
g_j = residualTranspose X θ t j = ∑v r(v) X(v,j).
```

[`fderiv_ceOneHot_mulVec`](Hagi/Model/CEGradient.lean) доказывает directional
Fréchet form именно этой log-linear CE. Для другого logit map нужен его
настоящий Jacobian.

Loss выбирается на supplied finite examples; held-out качество из формулы не
следует. При усреднении параметров midpoint-CE оценивается только pointwise
([`ceOneHot_mean_ceLogits_le`](Hagi/Model/CEHeldout.lean)).

Для `[Fintype V]`, `[Nonempty V]` и явного `[DecidableEq V]` с `p = Pi.single t
1`, `q = Hagi.Prelude.softDef z` связь с канонической информационной семантикой
точная ([`ceOneHot_eq_ceDef_pi_single`](Hagi/Math/Info/InfoCore.lean),
[`ceOneHot_eq_klDef_pi_single`](Hagi/Math/Info/InfoCore.lean)):

```
ceOneHot t z = Hagi.Prelude.ceDef p q = Hagi.Prelude.klDef p q.
```

[`KLSupported_pi_single_softDef`](Hagi/Math/Info/InfoCore.lean) доказывает
условие поддержки `q v ≠ 0 ∨ p v = 0`: нули one-hot вне цели допускаются,
поэтому применимы результаты о неотрицательности KL. Это точечное соответствие
для one-hot, не утверждение о произвольной дистилляции, оптимальности обучения
или held-out качестве.

## 3. Направление и сертифицированный размер шага

### 3.1 Базовый одношаговый safe CE update

Для одного примера `D = ceDirection X θ t = -g` и

```
A = ceAlignment X θ t = ∑j g_j²,
R = ceStepRange X θ t = 2∑v |ceLogits X D v|,
eta = safeStepSize X θ t = if R=0 then 0 else 4A/R²,
θ' = θ + eta • D.
```

При `eta ≥ 0` [`ceOneHot_next_le`](Hagi/Model/CEDescent.lean) даёт

```
CE(θ') ≤ CE(θ) - eta A + (eta R)²/8.
```

При `R>0` выбранный шаг минимизирует этот quadratic majorizer;
[`ceOneHot_safeStep_le_residual`](Hagi/Model/CEDescent.lean) даёт `CE(θ') ≤
CE(θ) -2A²/R²`, строгость —
[`ceOneHot_safeStep_lt`](Hagi/Model/CEDescent.lean). При `R=0` шаг равен нулю и
сохраняет logits. Глобального минимизатора CE или сходимости параметров шаг не
объявляет.

### 3.2 Общее направление для arithmetic-mean batch

На `X : Fin B → Matrix V (Fin d) ℝ`, `y : Fin B → V` не усредняем отдельные
`safeStepSize`, а вычисляем один вектор:

```
ḡ_j = meanResidualTranspose X θ y j = (∑b g_b,j)/B,
D̄ = batchMeanDirection X θ y = -ḡ,
Ā = batchAlignment X θ y = ∑j ḡ_j²,
Q̄ = batchRangeSquare X θ y = (∑b (dirRange X_b D̄)²)/B,
eta_b = batchSafeStep X θ y = if Q̄=0 then 0 else 4Ā/Q̄,
θ' = batchNextParameters X θ y = θ + eta_b • D̄.
```

[`batchLoss_alongNext_le_batchMajorizer`](Hagi/Model/BatchCEDescent.lean) даёт
majorizer `L(θ) -eta Ā + eta² Q̄/8`; при `Q̄>0`
[`batchLoss_safeStep_le_residual`](Hagi/Model/BatchCEDescent.lean) даёт `L(θ')
≤ L(θ) -2Ā²/Q̄`, а [`batchLoss_safeStep_lt`](Hagi/Model/BatchCEDescent.lean) —
строгий спуск mean-CE. Противоположные градиенты могут дать `D̄=0`; тогда
корректен hold.

Supplied направление `D`: непустой batch и `dirAction X_b θ y_b D < 0` для
каждого `b`; лишь тогда
[`batchDirectionSafeEta`](Hagi/Model/BatchCEDescent.lean) положителен.
[`batchDirectionNextParameters`](Hagi/Model/BatchCEDescent.lean) иначе не
меняет параметры. Локальный margin каждого примера фиксирует
[`ceOneHot_batchDirectionNextParameters_le_margin`](Hagi/Model/BatchCEDescent.lean).

Запас на фиксированном batch. Для фактической guarded-траектории `θ_t =
coreParameters (fixedBatchState X y S opCost opRisk write t)` при непустом `V`
и `K = rangeCurvature X`
([`batchRangeSquare_le_rangeCurvature_mul_alignment`](Hagi/Contracts/BatchCEAlignmentBudget.lean)):
`Q̄_t ≤ K·Ā_t`. Отсюда

```
[`fixedBatch_sum_alignment_le_initial`](Hagi/Contracts/BatchCEAlignmentBudget.lean)  — каждая конечная сумма,
[`fixedBatch_alignment_summable`](Hagi/Contracts/BatchCEAlignmentBudget.lean)        — суммируемость,
[`fixedBatch_tsum_alignment_le_initial`](Hagi/Contracts/BatchCEAlignmentBudget.lean):
∑t, Ā_t ≤ ((K + 1) / 2) * batchCEObjective X y S.
```

[`fixedBatch_meanGradient_tendsto_zero`](Hagi/Contracts/BatchCEAlignmentBudget.lean)
и
[`fixedBatch_meanDirection_tendsto_zero`](Hagi/Contracts/BatchCEAlignmentBudget.lean):
`WithLp.toLp 2 (meanResidualTranspose X θ_t y)` и `batchMeanDirection X θ_t y`
стремятся к нулю (непустота `V` нужна только в ветке `B+1`, где следует из `y
0`; при `B=0` скрытого witness нет). Среднее Чезаро ограничено отдельной
мажорантой
[`fixedAlignmentCesaro_le`](Hagi/Contracts/BatchCEAlignmentBudget.lean) при
непустом `V`; это не rate для отдельного `Ā_t`.

Доказан предел только общего среднего градиента на фиксированном batch.
Отдельные residual gradients при смешанных целях могут оставаться ненулевыми;
сходимость параметров, логитов, CE к оптимуму и held-out качество не
утверждаются.

### 3.3 Min-norm/MGDA и SafeQP

Per-sample guard: минимальная по норме точка convex hull raw gradients.
[`batchGradientMinimizer`](Hagi/Model/BatchCEDescent.lean) корректен, но
содержит `Classical.choose` — не native solver. Для двух градиентов явный
[`segmentMinNorm`](Hagi/Step/ProjectionDescent.lean): при `u=g1-g0≠0`, `τ=min 1
(max 0 (-⟪g0,u⟫/‖u‖²))`, `ω=g0+τu`;
[`segmentMinNorm_norm_le`](Hagi/Step/ProjectionDescent.lean) — минимальность,
[`batchGradientMinimizer_pair`](Hagi/Model/BatchCEDescent.lean) — связь с общим
случаем. Исполняемый/spec-статус — §16.

SafeQP на real inner-product `X` с `[FiniteDimensional ℝ X]` и конечном
непустом `K`: ближайшая к `g0` точка `{d | ∀i, ⟪g_i,d⟫ ≥ -eps_i}`, `eps_i≥0`.
Существование и единственность —
[`safeQP_exists_unique`](Hagi/Step/SafeQP.lean), alignment —
[`safeQP_descent`](Hagi/Step/ProjectionDescent.lean); исполняемым QP это не
называется. При quadratic-модели `∀i, dL_i ≤ -eta*⟪g_i,d⟫ + L_i*eta^2*‖d‖²/2`
шаг ограничен [`safeqpEtaMax`](Hagi/Step/SafeQPStep.lean):

```
eta ≤ min 1 (⨅i 2(eps_i+⟪g_i,d⟫)/(L_i‖d‖²)),
```

при `d≠0`, `L_i>0`, `eps_i≥0`, `0≤eta`; тогда
[`safeqp_eta_max`](Hagi/Step/SafeQPStep.lean) даёт `dL_i≤eps_i`. Если известна
только норма шага, при `0<R≤‖x‖` — точная проекция `(R/‖x‖)•x`
([`trust_region_nearest`](Hagi/Runtime/ControllerGates.lean)); замена всех
ограничений QP не объявляется.

### 3.4 Конечная log-linear CE и joint potential

Для состояния `S` на `EuclideanSpace ℝ (Fin d)`, конечного непустого `V`, `X :
Matrix V (Fin d) ℝ` и цели `t`:

```
D = ceDirection X S.params t,
A = featureAbsSum X,
R = ceStepRange X S.params t.
```

Теорема
[`potential_joint_of_ceLinear_residualDirection`](Hagi/Unified/DerivAlong.lean)
имеет ровно следующие содержательные посылки:

```
hstep  : S.stepDir = -ceDirection X S.params t,
hgrad  : S.grad = S.stepDir,
hL     : 0 < S.sp.L,
hLdef  : S.sp.L = featureAbsSum X ^ 2,
heta   : S.sp.eta ≤ 1 / S.sp.L,
heta0  : 0 ≤ S.sp.eta,
hCEold : S.energy = ceOneHot t (ceLogits X S.params),
hCEnew : S.effects.jointEnergy =
  ceOneHot t (ceLogits X (joint S).params).
```

hCEnew — явная идентификация measured post-energy, не следствие операции
joint. Заключение для потенциала Φ:

```
Φ(joint S) - Φ S ≤ -gainJoint S + riskJoint S.
```

Из hstep: `(joint S).params = ceNextParameters X S.params t S.sp.eta = S.params
-S.sp.eta • S.stepDir`; с hgrad `⟪S.grad,S.stepDir⟫ = ‖S.stepDir‖² =
ceAlignment X S.params t`. Одношаговая CE-мажоранта и singleton range bound:

```
CE(next) ≤ CE(old) - eta*ceAlignment + (eta*R)²/8,
R² ≤ 4*A²*‖D‖²,
(eta*R)²/8 ≤ A²*eta²*‖D‖²/2.
```

Так hLdef выбирает допустимую, вообще говоря грубую кривизну `A²`, а
[`potential_joint`](Hagi/System/GrowthState.lean) завершает вывод. Деления на
направление нет, посылка `D≠0` не требуется. Это не утверждение о
глобальной/оптимальной smoothness и не результат о сходимости или PL.

Контроль: `X=I₂`, `t=0`, нулевые параметры, `eta=1/4`, `A=2`, `L=4`:

```
D = [+1/2,-1/2],       stepDir = grad = [-1/2,+1/2],
‖D‖² = 1/2,            R = 2,
4A²‖D‖² = 8,           new joint logits = [+1/8,-1/8],
gainJoint = eta*‖stepDir‖²/2 = 1/16.
```

Фактическое уменьшение CE равно `softplus(0)-softplus(-1/4) ≥ 1/16`; при
`riskJoint=0` не менее `1/16` и уменьшение потенциала (ни одно из них не
равно `1/16` в точности). Отдельный [`safeStepSize`](Hagi/Model/CEDescent.lean)
здесь был бы `1/2`, но не удовлетворяет окну `eta≤1/L=1/4`. При
повторяющихся строках возможен `D=0` при тех же `A`, `L`, eta — gain нулевой,
при нулевом риске только невозрастание потенциала. Universal strict progress,
сходимость, generalization, held-out качество и выигрыш времени/FLOPs не
утверждаются.
### 3.5 Identity features: предел средней вероятности

`X : Fin B → Matrix (Fin n) (Fin n) ℝ`, `y : Fin B → Fin n`, `0 < B`, `hX : ∀
b, X b = 1`, траектория `θ_t` из §3.2. Непосредственно применяется
[`Hagi.Contracts.BatchCEAlignmentBudget.fixedBatch_meanGradient_tendsto_zero`](Hagi/Contracts/BatchCEAlignmentBudget.lean).
`meanPrediction X θ` усредняет вероятности `softDef (ceLogits (X b) θ)`, а
`empiricalTarget y` — векторы `(Pi.single (y b) 1 : Fin n → ℝ)`; при
identity-умножении

```
meanPrediction X θ v − empiricalTarget y v = meanResidualTranspose X θ y v.
```

Средние тотализированы и при `B=0`, но вероятностная интерпретация и public
limit theorems требуют `0 < B`. Следствие
[`Hagi.Contracts.IdentityMomentConvergence.fixedBatch_meanPrediction_tendsto_empiricalTarget`](Hagi/Contracts/IdentityMomentConvergence.lean):
`meanPrediction X θ_t → empiricalTarget y` в finite-product topology. Для `B=1`
теорема `fixedBatch_meanPrediction_tendsto_empiricalTarget_batch_one` даёт
`softDef (ceLogits (X 0) θ_t) → Pi.single (y 0) 1`.

Counterexample: два identity features, смешанные метки `[0,1]`, нулевые
параметры — mean prediction и empirical target равны `(1/2,1/2)`, mean residual
нулевой, но оба individual `ceDirection` ненулевые;
`mixed_batchLoss_before_eq_log_two` даёт CE=`log 2`. Marginal matching не
означает нулевую CE или правильность individual predictions. Произвольные
affine/full-rank features, сходимость параметров и held-out качество не
доказаны.

### 3.6 Guarded Pareto CE: адаптер к StepContract

`T = budgetedParetoBatchTrainStep X y S opCost opRisk write`, посылка
`0≤opRisk`. Адаптер
[`budgetedParetoStepContract`](Hagi/Contracts/BudgetedParetoStepContract.lean)
возвращает [`StepContract`](Hagi/Unified/StepContract.lean):

```
decrease    = batchCEObjective X y S - batchCEObjective X y T,
riskCost    = T.saf.risk - S.saf.risk,
budgetSpend = S.res.budget - T.res.budget.
```

Это фактическая CE как функция параметров и данных. Структура требует
nonnegative `StepContract.decrease`, `StepContract.riskCost` и
`StepContract.budgetSpend`; strict progress не требуется.

При активном guard проверяем `0≤opCost≤S.res.budget` и samplewise CE
non-regression на вычисленном successor: среднее CE не возрастает, расход равен
`opCost≥0`, `StepContract.riskCost=opRisk≥0`. Guard риск не проверяет, поэтому
`0≤opRisk` необходима даже при `B=0`, `V=Empty`. При отказе guard возвращается
целое `S`, все три дельты обнуляются — hold остаётся допустимым шагом.

Контроль: двухэлементный same-label mean-CE drop
[`sameZeroInitialMeanDrop_pos`](Hagi/Contracts/BatchCETrajectory/FixedBatch.lean)
даёт положительный `StepContract.decrease`; при бюджете `2`, `opCost=1/2`,
`opRisk=1/4`: остаток `3/2`, `budgetSpend=1/2`, `riskCost=1/4`. При `opCost=-1`
или `opCost=3` — hold. На смешанном batch асимметричный CE veto возвращает `S`,
все дельты нулевые. `budgetSpend≥0` — не утверждение о nonnegative новом
бюджете для произвольного `S` (отдельный инвариант). Адаптер не выбирает
оптимальное действие и не доказывает индивидуальный mixed-batch CE descent,
сходимость, generalization или экономию FLOP/time.

### 3.7 Accepted-only Pareto CE: строгий StepCert

Тот же `T`; второй guard не добавляется. Требуются положительный
[`batchRangeSquare`](Hagi/Model/BatchCEDescent.lean), `0≤opRisk`, opRisk не
выше riskLim, исходный `FloorHeld S floor` и полная активность guard:
nonnegative affordable cost и samplewise CE non-regression на каноническом
`batchTrainStep`.

[`budgetedParetoStepCert`](Hagi/Contracts/BudgetedParetoStepCert.lean) через
уже доказанный `batchTrainStepCert` и равенство активной ветки переносит его на
guarded successor `T`. Результат —
[`StepCert`](Hagi/Unified/CertifiedLoop.lean):

- `StepCert.budgetSpend = opCost`, `StepCert.riskSpend = opRisk`;
  `Hagi.Unified.HonestTransition.HonestTransition.objectiveDrop > 0` и
  `Hagi.Unified.HonestTransition.HonestTransition.actualDescent` — строгий
  спуск arithmetic-mean CE на supplied batch;
- `Hagi.Unified.CertifiedLoop.StepCert.hdec` связывает новый бюджет с
  `S.res.budget − opCost`,
  `Hagi.Unified.HonestTransition.HonestTransition.budgetBound` даёт его
  неотрицательность;
- quality floor сохраняется на `T` (stored quality не меняется; это не новое
  измерение held-out качества).

Посылки `Nonempty V` нет: положительный range доказывает `0<B`, метка первого
элемента строит локальный witness. При `B=0` такой range невозможен, фиктивный
`y 0` не создаётся. Поля `Hagi.Unified.CertifiedLoop.StepCert.trans`, hdec,
quality переносятся через canonical accepted equality, а не через opaque
cast.

Контроль: ровно два same-label примера `Fin 2` — `objectiveDrop > 0`, бюджет
`2→3/2`, `budgetSpend=1/2`, риск `0→1/4`, `riskSpend=1/4`. При `opCost=3`
affordability ложна; строгого сертификата нет — hold из §3.6 остаётся
nonnegative `StepContract`.

Strictness относится к среднему CE, не к каждому sample. riskLim ограничивает
opRisk одного шага, не накопленный риск. CE→0, параметрическая сходимость,
generalization, гарантия для нелинейного backbone и экономия FLOP/time не
следуют.

### 3.8 Range-based safe step: диапазон смещения логитов вместо суммы по словарю

Базовый сертификат §3.1 мажорирует сдвиг CE через `ceStepRange = 2∑|d v|`.
Вторая константа — [`ceStepLogitRange`](Hagi/Model/CEDescent.lean), диапазон
того же смещения `d = ceDirection X θ t`:

```
R' = sup_v d v − inf_v d v,
```

через `sup' d + sup' (−d)` над конечным словарём. Леммы (все в
Hagi/Model/CEDescent.lean):

| Имя | Факт |
| --- | --- |
| [`ceStepLogitRange_nonneg`](Hagi/Model/CEDescent.lean) | `0 ≤ R'` |
| [`ceDirectionLogit_sub_le`](Hagi/Model/CEDescent.lean) | поточечная оценка разности логитов через две sup'-грани |
| [`ce_logitDisplacement_range`](Hagi/Model/CEDescent.lean) | перенос на весь directional logit displacement |
| [`ceStepLogitRange_le_ceStepRange`](Hagi/Model/CEDescent.lean) | `R' ≤ R = 2∑|d|` |
| [`ceAlignment_pos_of_logitRange_pos`](Hagi/Model/CEDescent.lean) | `R' > 0 ⟹ A > 0` |

Главный шаг — [`ceOneHot_next_le_rangeMajorizer`](Hagi/Model/CEDescent.lean):
для любого `0 ≤ η`

```
CE(θ + η·dir) ≤ CE(θ) − η·A + (η·R')²/8,
```

Острота квадратичного члена та же (`r²/8` из `lse_shift_upper`), но аргумент —
диапазон, а не сумма по словарю.
[`ceRangeMajorizer`](Hagi/Model/CEDescent.lean) — мажоранта `CE − ηA +
(ηR')²/8`; certified step [`ceRangeSafeStep`](Hagi/Model/CEDescent.lean) =
`4A/R'²` при `R' > 0`, иначе `0`
([`ceRangeSafeStep_nonneg`](Hagi/Model/CEDescent.lean),
[`ceRangeSafeStep_pos_of_logitRange_pos`](Hagi/Model/CEDescent.lean));
[`ceRangeMajorizer_safeStep_eq`](Hagi/Model/CEDescent.lean) — значение
мажоранты на шаге. Итог
([`ceOneHot_rangeSafeStep_le_residual`](Hagi/Model/CEDescent.lean)):

```
CE(θ') ≤ CE(θ) − 2A²/R'²,
```

строго при `R' > 0` ([`ceOneHot_rangeSafeStep_lt`](Hagi/Model/CEDescent.lean)).

Соотношение со старым сертификатом — сосуществование, не замена:
[`ceRangeSafeStep_ge_safeStepSize`](Hagi/Model/CEDescent.lean) — при `0 < R'`
новый шаг не меньше старого; [`ceRange_residual_ge`](Hagi/Model/CEDescent.lean)
— residual `2A²/R'²` не меньше `2A²/R²`. Так как `R' ≤ R`, выигрыш в размере
шага — до `V²`. Вырождение:
[`ceStepLogitRange_eq_zero_of_eq_zero`](Hagi/Model/CEDescent.lean) —
тождественно нулевые directional logits влекут `R' = 0`; если `R' = 0`, то `d`
константен, и из `Σ_v ceResidual v = 0` alignment `A` и старый шаг `4A/R` тоже
нулевые. Итак `0 < R'` эквивалентно `0 < R`: ни один режим старого сертификата
не теряется.

Числовые контроли (identity two-class, `#eval`-равенства):
[`identityTwoClass_logitRange_test`](Hagi/Model/CEDescent.lean) — `R = 2`
против `R' = 1`;
[`identityTwoClass_rangeSafeStep_test`](Hagi/Model/CEDescent.lean) — шаг `1/2`
против `2`;
[`identityTwoClass_step_comparison_test`](Hagi/Model/CEDescent.lean) — `1/2 <
2`; [`identityTwoClass_residual_comparison_test`](Hagi/Model/CEDescent.lean) —
residual `1/8` против `1/2`.

Область — только certified-descent: одношаговая верхняя оценка CE и размер
шага. Wall-clock ускорение, сходимость итерации, CE→0, generalization,
нелинейный backbone и оптимальность шага не утверждаются.

### 3.9 Batch mirror: range-based safe step для arithmetic-mean batch loss

Сертификат §3.2 использует `batchRangeSquare` — среднее квадратов `dirRange`
(словарная сумма модулей). Здесь — диапазон смещения логитов; механика §3.8 та
же, ниже только batch-специфика (Hagi/Model/BatchCEDescentLogitRange.lean).

```
R' = sup_v ceLogits X D v − inf_v ceLogits X D v          -- dirLogitRange, произвольное D
CE(θ + η·D) ≤ CE(θ) + η·dirAction X θ t D + (η·R')²/8    -- ceOneHot_alongNext_le_logitRange
L(θ + η·D) ≤ L(θ) − η·A + η²·R̄'²/8                       -- batchLogitMajorizer, A = batchAlignment
eta = batchLogitSafeStep = if R̄'²=0 then 0 else 4A/R̄'²
L(θ') ≤ L(θ) − 2·A²/R̄'²                                  -- batchLoss_logitSafeStep_le_residual
```

`R̄'² = batchLogitRangeSquare` — среднее квадратов `dirLogitRange`.
Позитивность: `batchLogitRangeSquare_nonneg`,
`batch_pos_of_logitRangeSquare_pos`,
`batchAlignment_pos_of_logitRangeSquare_pos`; шаг —
`batchLogitSafeStep_nonneg`, `batchLogitSafeStep_pos_of_logitRangeSquare_pos`;
update — `batchLogitNextParameters`; значение мажоранты на шаге —
`batchLogitMajorizer_logitSafeStep_eq`; строгий спуск —
`batchLoss_logitSafeStep_lt`. Словарные аналоги: `dirLogitRange_nonneg`,
`dirLogitRange_le_dirRange`, `dirLogit_sub_le`,
`dir_logitDisplacement_logitRange`; сосуществование —
`batchLogitRangeSquare_le_batchRangeSquare` и
`batchLogitSafeStep_ge_batchSafeStep`; при `R̄'² = 0` шаг тотально нулевой
(`dirLogitRange_eq_zero_of_forall_eq_zero`).

Контроль (V=2, `!![1, 1; -1, 1]`, направление `single 0 1`, logits `(1, −1)`):
`dirRange = 4`, `dirLogitRange = 2`; range-square `16` против `4` — шаг и
residual выигрывают до `4×`. Область — как в §3.8.

### 3.10 Gated CE: норма градиента и траекторный запас

Для одноцелевого CE с tanh-гейтингом (`gatedForward`) градиент —
транспонированный остаток через sech²-якобиан
([`gatedGrad`](Hagi/Contracts/GatedCEGradientNorm.lean) `= -gatedDirection`,
покоординатно `gatedResidualTranspose`;
[`gatedGrad_ofLp`](Hagi/Contracts/GatedCEGradientNorm.lean)); производная
действует как скалярное произведение с `gatedGrad`
([`fderiv_gatedCE_apply_inner`](Hagi/Contracts/GatedCEGradientNorm.lean)), и
`‖gatedGrad‖² = gatedAlignment`
([`norm_gatedGrad_sq`](Hagi/Contracts/GatedCEGradientNorm.lean)) — без
предположений сверх `Fintype V`.

Безопасный шаг `η = A/(2C)` с `C(X) = 1 + 2Q + (2U)²/8` имеет точное падение
`A²/(4C)`, поэтому траекторный запас — четвёртая степень нормы градиента
([`gated_grad_sum_fourth_le_uniform`](Hagi/Contracts/GatedCEGradientNorm.lean)):

```
∑s∈[0,T) ‖∇L(θs)‖⁴ ≤ 4·C(X)·L₀.
```

Квадратичная форма `∑‖∇L‖² ≤ const·L₀` этим не доказана: нужна новая оценка
`gatedCurvature ≤ κ(X)·gatedAlignment`. Эмпирических посылок нет; цель `t` —
фиксированная one-hot.

## 4. Выбор примеров: supported inverse-propensity MSE

### 4.1 Supported inverse-propensity

Для фиксированных `g_b : EuclideanSpace ℝ I` на непустом `B` выбираем PMF `q`
только при `q_b ≠ 0 ∨ g_b = 0` для всех `b`. Один draw оценивает arithmetic
mean как `(B q_b)⁻¹ • g_b`.
[`pmfMean_selectedMean_batchResidualGradient`](Hagi/Model/BatchCEDescentResidualNorm.lean)
— coordinatewise unbiasedness;
[`selectedMeanGradientMSE_eq_sum`](Hagi/Probability/MirrorHedgeMWU.lean) —
точный squared-error объект (не covariance/independence claim).

Если `0 < ∑b |ℓ_b|`, строим `q_b = |ℓ_b|/∑i |ℓ_i|`
([`selectedLoss_optimalPropensity`](Hagi/Probability/MirrorHedgeMWU.lean)).
[`selectedLoss_optimalPropensity_mse`](Hagi/Probability/MirrorHedgeMWU.lean):

```
MSE = (∑|ℓ|)² - ∑ℓ²,
```

[`selectedLoss_optimalPropensity_mse_le`](Hagi/Probability/MirrorHedgeMWU.lean)
— минимум среди всех supported конкурентов. Для `ℓ_b=‖g_b‖` —
[`selectedGradientMSE_optimalPropensity_le`](Hagi/Probability/MirrorHedgeMWU.lean);
масштаб arithmetic mean добавляет ровно `B⁻²`
([`selectedMeanGradientMSE_optimalPropensity_le`](Hagi/Probability/MirrorHedgeMWU.lean)).

Если gradient norms не вычислены заранее — feature-only `F_b = featureNormSum
X_b` (сумма Euclidean row norms):
[`norm_batchResidualGradient_le_featureNormSum`](Hagi/Model/BatchCEDescentResidualNorm.lean)
даёт `‖g_b‖≤F_b`;
[`pmfMean_featureNormSum_optimalPropensity`](Hagi/Model/BatchCEDescentResidualNorm.lean)
сохраняет unbiasedness;
[`selectedMeanGradientMSE_featureNormSum_le`](Hagi/Model/BatchCEDescentResidualNorm.lean):

```
MSE ≤ B⁻² ((∑F)² - ‖∑g‖²).
```

Это upper envelope, не Neyman oracle по фактическим градиентам. RNG runtime,
generalization, меньший FLOP count и улучшенный loss не обещаются.

### 4.2 Стохастический minibatch R'-шаг

Один обратный-propensity шаг по сырому CE residual-градиенту
(Hagi/Model/BatchCEDescentStochastic.lean):

```
stochasticStepDraw X θ y q b   = (B·q b)⁻¹ • batchResidualGradient
batchLoss_expectedStochasticStep_le:
  E_q[L(θ − η·ĝ)] ≤ L(θ) − η·‖m‖² + (η²/8)·cfc·E_q[‖ĝ‖²]
  (посылки: 0 < B, 0 ≤ η, покоординатная несмещённость)
pmfMean_normSq_stochasticStepDraw_eq:
  E[‖ĝ‖²] = selectedMeanGradientMSE q g + ‖m‖²              (точная bias-variance)
batchLoss_expectedStochasticStep_featureNormSum_le:
  E[L] ≤ L − η·‖m‖² + (η²/8)·cfc·(Σ|featureNormSum|)²/B²
batchLoss_expectedStochasticStep_featureNormSum_lt:
  0 < η ∧ η·cfc·V̂ < 8·‖m‖² ⇒ E[L] < L
```

Член спуска — несмещённость + линейность; кривизна — глобальный (все η ≥ 0)
Böhning-мажоратор §3.9 без window-посылок; дисперсия — §4.1. Константа cfc —
batch-сумма `4·∑ featureAbsSum²` (консервативно против поточечной суммы). Это
одношаговый statement об ожидании; Ville и концентрация сюда не входят.

## 5. Оптимизатор: выбирать по доказанному контракту

Основной путь — `batchNextParameters`; sign/Lion/SAM/HeavyBall не заменяют его
CE-сертификат.

- Нормализованный sign: при непустом `k` полагаем
  `s = signScale g = (∑|g_i|)/card k`, `D_i=s·sgn1(g_i)`. Если `J : Objective`
  содержит `0<L` и descentLemma, то
  [`sign_scaled_aligned`](Hagi/Unified/SignDescent.lean) доказывает
  alignment; при `0<eta≤1/L` [`sign_descent`](Hagi/Unified/SignDescent.lean)
  даёт `f(x-etaD) ≤ f(x)-eta(1-L eta/2)‖D‖²`. Без нормализации вывода нет.
- Lion: [`lion_step_norm_bound`](Hagi/Optimization/OptimizerVariants.lean)
  ограничивает сырой `eta·sign(m)` лишь `eta²·d` в squared norm. Для спуска
  нужна coherence градиента с моментом; тогда
  [`lion_descent`](Hagi/Unified/SignDescent.lean) с той же `signScale`.
- SAM: `samW` — sup loss на ρ-ball, не готовый update. При `ρ≥0` и
  ограниченности сверху образов `J.f` на сдвинутых ρ-ball-семействах для `x`
  и `x'` new point принимается только при оценке локальной остроты sharp и
  доказанном SAM-drop δ; [`sam_descent_bridge`](Hagi/Unified/SignDescent.lean)
  даёт `f(x') ≤ f(x) -(delta-sharp)`. Отдельного adversarial optimizer нет.
- HeavyBall — только квадратичная модальная модель. Для `0<μ≤L`:
  `β=((√L-√μ)/(√L+√μ))²`, `eta=4/(√L+√μ)²`;
  [`hb_general_window`](Hagi/Optimization/MomentumHB.lean) покрывает
  `μ≤λ≤L`. Для характеристических корней и Jordan-оценки дополнительно
  `0<μ<L` (тогда `0<β<1`, `ρ=√β>0`) и root/recurrence-посылки:
  [`hb_spectral_mode`](Hagi/Optimization/MomentumHB.lean) даёт `|root|²=β`.
  Это не траекторный `Cβ^(t/2)` результат: при кратном корне есть
  Jordan-фактор
  [`hb_critical_trajectory_bound`](Hagi/Optimization/MomentumHB.lean),
  а второй коэффициент фактической пары HeavyBall — `β+eta(1-β)`
  ([`hb_pair_second_order`](Hagi/Optimization/MomentumHB.lean)).
- Percolation path optimizer (вероятностный путь): цель `f : V → ℝ`, ядро
  `K : V → PMF V`, старт `a`, горизонт `T`. Шаги: (1) `K` не ведёт вверх —
  [`descentOrStayKernel`](Hagi/Optimization/PercolationPath.lean), всякое
  убывание поддержано —
  [`descentKernelFullSupport`](Hagi/Optimization/PercolationPath.lean);
  (2) траектория спуска длины `T` —
  [`descentPath`](Hagi/Optimization/PercolationPath.lean) (для итерации
  step-отображения —
  [`descentPath_of_iterate`](Hagi/Optimization/PercolationPath.lean));
  (3)
  [`descentPath_apply_pos_of_full_support`](Hagi/Optimization/PercolationPath.lean).
  Гарантия: `0 < historyLaw (PMF.pure a) (fun _ => K) T T ω` для
  поставленной траектории `ω` с `f b < f a`
  ([`descentPath_drop`](Hagi/Optimization/PercolationPath.lean)). Для
  решётки открытых сайтов —
  [`crosses_pos`](Hagi/Optimization/PercolationPath.lean):
  пересечение по открытым сайтам ⇒ положительная масса точной истории. Это
  масса траектории, не вероятность попадания и не порог перколяции;
  кода-потребителя в HAGI_v2 нет.

## 6. Квантование и распределение памяти/битов

### 6.1 Grid и ternary представление

Для `Δ>0` [`gridQ`](Hagi/Energy/Quantizer.lean) имеет вид `Δ round(x/Δ)` и
pointwise error `≤Δ/2`; покоординатно
[`gridQVec_norm_sq`](Hagi/Energy/Quantizer.lean):

```
∑i(w_i-gridQVec Δ w_i)² ≤ card(k)(Δ/2)².
```

Для `s>0` и ternary `qTern s x = s roundTern(x/s)` обязателен saturation
([`ternary_split_le`](Hagi/Runtime/TernaryExact.lean)):

```
Σ(w-qTern s w)² ≤ n(s/2)² + satTail s w.
```

[`quant_energy_bridge_saturation`](Hagi/Runtime/TernaryExact.lean) переводит
это в energy bound лишь при `0≤κ` и отдельной `h_emp_lip: dE ≤ κ*√(∑i(w_i-qTern
s w_i)²)`. [`tritEncode_injective`](Hagi/Energy/Ternary.lean) и
[`tritEncode_lt`](Hagi/Energy/Ternary.lean) — injective five-trits byte block;
[`packedTernarySamples_decode_point`](Hagi/Runtime/TernaryExact.lean)
возвращает quantized, не raw values. Это формат, не гарантия ABI/heap size.

При фиксированном pattern `q`, `0<∑q_i²`, оптимальный масштаб `s₀=(∑q_i
x_i)/(∑q_i²)` ([`lsScale_optimal`](Hagi/Energy/Ternary.lean)) минимизирует
squared reconstruction error среди real scales; это не minimax-scale и не
оптимизация pattern.

### 6.2 Per-block scale и bit-reallocation

Блоки по пять весов: `blockPenalty` — минимум двух доказанных score;
минимизируем по 255 codes в каждом блоке.
[`selectedGroupScales_total_le`](Hagi/Model/CEGroupedScale.lean) — exact
minimum суммарного declared certificate;
[`ceOneHot_joint_le_blockPenalties`](Hagi/Model/CEGroupedScale.lean):

```
CE(joint selected) ≤ CE(raw) + ∑g blockPenalty_g.
```

При `G>0`
[`localEvaluationCount_le_jointCandidateCount`](Hagi/Model/CEGroupedScale.lean)
сравнивает `255G` logical score calls с `255^G` assignments;
[`decodeStep_packedBlocks`](Hagi/Model/CEGroupedScale.lean) связывает payload с
выбранными параметрами. Счёт — не время/FLOPs/память ABI.

Исполняемый селектор —
[`selectedGroupScalesExec`](Hagi/Model/CEGroupedScale.lean): foldl-argmin по
`List.finRange 255` с seed `knownSampleScale`. Мосты:
`selectedGroupScalesExec_cost_eq` (`blockPenalty (exec g) = blockPenalty
(selectedGroupScales g)`), `selectedGroupScalesExec_score_le` (минимальность
над 255-семейством), `selectedGroupScalesExec_total_le` (суррогатная сумма).
Сравнение на ℝ классическое, def noncomputable — исполняется алгоритм (конечный
fold), не оператор выбора.

Перенос бита. При `e_l(b)=layerError c_l b=c_l/2^b` перенос одного бита из `k`
в `j` меняет ошибку на `e_k-e_j/2`
([`transfer_exact`](Hagi/Budget/BitAlloc.lean)). Делаем перенос, если `j≠k`,
`2e_k<e_j`, `f_k>0`: ошибка строго падает
([`imbalance_yields_gain`](Hagi/Budget/BitAlloc.lean));
[`no_infinite_improving_chain`](Hagi/Budget/BitAllocTermination.lean) запрещает
бесконечную цепь при фиксированном бюджете. При `∀i, 0≤c_i` и отсутствии
строгого улучшения для всех `j≠k` с `0<f_k`
[`stable_factor_two`](Hagi/Budget/BitAlloc.lean) для donor `f_k≠0` даёт
`layerError(c_j)(f_j) ≤ 2*layerError(c_k)(f_k)`. Полный continuous clamped
n-layer алгоритм отсюда не выводим.

Continuous certificate: если `c_i>0`, `∑f=∑g=B`, `n>0` и `c_i/2^{f_i}`
одинаково для всех `i`, то
[`water_filling_inner_optimum`](Hagi/Budget/BitAlloc.lean) даёт `totalErrorCont
c f ≤ totalErrorCont c g`. Применяем только при уже найденном equalizing `f`.

### 6.3 BF16: логический носитель и guarded delta-read

[`Hagi.Runtime.BF16Delta.Code`](Hagi/Runtime/BF16Delta.lean): знак, raw
exponent `0..254` и fraction описывают все конечные BF16-коды; `decode`
отображает их точно в `ℚ`, включая signed zeros и subnormals. Это не packed
16-bit layout.

Guard `Hagi.Runtime.BF16Delta.SamePositiveNormalBinade`: неотрицательные знаки,
равные raw exponents, ненулевой exponent. Тогда
[`Hagi.Runtime.BF16Delta.exists_sameBinade_difference`](Hagi/Runtime/BF16Delta.lean)
строит точную разность в `Code`, включая zero, negative и subnormal cases.
Посылки nearest нужны для самого бэкенда (`exists_IsNearest` не задаёт
executable RNE или tie rule). Рецепт для исходного и нового кодов:

- delta с посылкой
  `Hagi.Runtime.BF16Delta.IsNearest (decode new -decode anchor) delta`;
- при guard readback с посылкой
  `Hagi.Runtime.BF16Delta.IsNearest (decode delta + decode anchor) readback`;
  вне guard использовать `decode new` независимо от readback;
- [`Hagi.Runtime.BF16Delta.guardedRead_nearest_returns_new`](Hagi/Runtime/BF16Delta.lean)
  возвращает `decode new`.

FTZ при subnormal delta может нарушить nearest-посылку. Вне guard
[`Hagi.Runtime.BF16Delta.extreme_nearest_delta_loses_update`](Hagi/Runtime/BF16Delta.lean):
для anchor `2^127` и new `129/128` nearest delta равна `-anchor`, а
reconstruction — нуль; `(new-anchor)+anchor` нельзя подставлять вместо
fallback. Не доказаны packed storage, FTZ, физическая экономия памяти/времени,
улучшение обучения и held-out CE. BF16-гард шага — §12.2.

### 6.4 Certified low-rank замена и градиентное горлышко

Любая замена `B` с `rank B ≤ k` оставляет Frobenius-ошибку не меньше
квадратичного хвоста сингулярных чисел —
[`eckart_young_lower_bound`](Hagi/External/Flywheel/EckartYoungLower.lean)
(нижняя граница к
[`eckart_young_frobenius`](Hagi/External/Flywheel/FrobeniusNorm.lean)). Бюджет
e_rank — фундаментальный предел, а не артефакт алгоритма. Прямоугольная форма —
§15.5.

Для знаковых матриц обновлений (отрицательная диагональ, неотрицательная
внедиагональ)
[`neg_diag_pos_off_diag_injective`](Hagi/External/Flywheel/NegDiagRank.lean):
при строго отрицательных строчных суммах оператор инъективен. Слабая версия
(суммы `≤ 0`) ложна — лапласиан на двух вершинах убивает константный вектор;
строчные суммы ровно ноль (softmax минус эмпирические частоты) требуют
лапласианной формулировки ранга и не утверждаются.

Носитель строки логит-градиента — softmax минус эмпирическое распределение
следующего токена — [`logitGrad`](Hagi/Contracts/LogitGrad.lean): обобщение
`ceResidual` с one-hot на суб-вероятностные `N`. Строчные факты: суммы ноль при
вероятностных `N` (`logitGrad_row_sum_zero`), строго положительное смещение вне
one-hot цели (`logitGrad_pos_off_target`), строго отрицательное в цели при
нетривиальном словаре (`logitGrad_neg_at_target`; посылка `∃ w ≠ t c`),
абсолютная строчная масса `≤ 2` для суб-вероятностных `N`
(`abs_logitGrad_row_le_two`), `smax_lt_one`.

Сборка — [`gradient_bottleneck_bound`](Hagi/Contracts/GradientBottleneck.lean):
всякое достижимое логит-обновление `Δ` с `rank Δ ≤ k` оставляет
Frobenius-остаток не меньше квадратичного хвоста сингулярных чисел `logitGradM`
за `k`. Посылки:

| Посылка | Роль |
| --- | --- |
| `hΔ : Δ.rank ≤ k` | достижимость: ранг обновления ограничен |
| `∃ w ≠ t c` (только neg-at-target) | нетривиальный словарь |
| суб-вероятность `N` (0 ≤ N, ∑ ≤ 1) | только для |row| ≤ 2 |

«Голова ранга D ⇒ достижимые обновления ранга ≤ 2D» — посылка, не вывод. При `k
≥ n` хвост пуст и оценка тривиальна.

### 6.5 Динамика маршрутизации: odds-ratchet, deadlock, анти-лок-ин

Ratchet — точное обновление шансов softmax
([`softDef_odds`](Hagi/Model/Routing.lean)): `a⁺j/a⁺k = (aj/ak)·exp(Δsj−Δsk)`.
Его локальная эксплуатация — [`odds_ratchet`](Hagi/Model/Routing.lean): сдвиг
скоров, пропорциональный строке внимания (Δs = c·a, c > 0), за один шаг строго
увеличивает шансы более внимательного ключа (фактор `exp(c(aj−ak)) > 1`). На
стороне значений — точное V-шаговое тождество `ratchet_advantage_step`: `A⁺j =
Aj + η·aj·‖δ‖²` (монотонная форма `ratchet_advantage_mono`). Утверждается
только один шаг; итерируемый экспоненциальный рост — нет.

Deadlock-свидетель [`deadlock_witness`](Hagi/Model/Routing.lean): 3-ключевой
softmax (скоры = логарифмы рационального вектора внимания, `exp∘log`
сокращается точно) даёт полезному ключу внимание ровно ε = 1/10; его вклад в
градиент запроса (член a·A•k) имеет норму ≤ ε·M.

Анти-лок-ин `ewNorm_survivor_lower` (Hagi/Optimization/MirrorHedge.lean): при
неотрицательных потерях и η ≥ 0 нормированный вес любого ключа ≥
(1/K)·exp(−η·Σℓ) — роутер не может навсегда shut out ключ с ограниченными
потерями. Посылки слабее регрет-стороны (`hsurv_derived` требует ℓ ∈ [0,1];
регрет при ℓ ≥ 0 не утверждается).

Не утверждается: скор-стороннее тождество `Δs = η‖δ‖²·x_iᵀ(x_j−x_i)` и первый
порядок `sign(Δa) = sign(a−Σa²)`; монитор эффективного ранга/энтропии роутера.

### 6.6 Мост Хadamard-некогерентности ↔ тернарной квантизации

Мотивация — QuIP# (Thm 4.1); μ-некогерентность — всегда ПОСЫЛКА. Адамар не
подавляет ∞-норм универсально:
[`hadamard_not_universally_incoherent`](Hagi/Contracts/HadamardTernaryBridge.lean)
— при `k = 1`, `x = (2, 2)` `‖Hx‖∞ = ‖x‖₂ = 2√2`, координата `2√2 > 3/2`
насыщает тернарную сетку при `s = 1`.

- [`hadamard_satTail_zero_of_l2_bound`](Hagi/Contracts/HadamardTernaryBridge.lean):
  при `‖x‖₂ ≤ s·√d` (d = 2^k, s > 0) и посылке `‖Hx‖∞ ≤ μ·‖x‖₂/√d` с
  `0 ≤ μ ≤ 1` каждая координата `Hx` лежит в `|y| ≤ 3s/2`, хвост
  насыщения `satTail` зануляется.
- [`hadamard_quant_error_le_of_l2_bound`](Hagi/Contracts/HadamardTernaryBridge.lean):
  тогда суммарная квадратичная ошибка ≤ `d·(s/2)²` — чистое
  полу-шаговое округление.
- [`hadamard_logits_invariance_mulVec`](Hagi/Contracts/HadamardTernaryBridge.lean):
  до квантования логиты инвариантны точно:
  `(W·Hᵀ) *ᵥ (H *ᵥ x) = W *ᵥ x`; после квантования тождество приближённое.
- [`blockPenalty_le_of_all_ternInRange`](Hagi/Contracts/HadamardTernaryBridge.lean)
  и
  [`hadamard_ce_blockPenalty_reduction`](Hagi/Contracts/HadamardTernaryBridge.lean):
  если сырые веса блока — Адамар-образ некогерентного источника и все в
  диапазоне, хвост в `groupStructuralPenalty` исчезает, и `blockPenalty`
  (потребитель из CEGroupedScale) ≤ `2·featureAbsSum·√5·lvl/2`.

Post-quantization логит-гарантий нет.

### 6.7 MDL: счёт блоков состояния

`Hagi/Step/MDLThreeCurrency.lean`: `cstateBlocks` — счёт 16-бит упакованных
блоков (инстанс `DyadicTernary dyadicBlock`); учётная лемма
`double_counting_identification_forced`: коллапс двойного учёта `cst = L_pred`
возможен только при явном проверяемом равенстве «счёт блоков = функция потерь»
(λ_M ≠ 0). Валюты разделены структурно: block count ≠ data code length.

## 7. HNet: стартовый ratio из continuous cost-модели

Для `a,b,T,r>0` обозначим `C(r)=aTr+bT²/r²`: локальная pooling-цена плюс
latent-attention price. [`hier_attn_saving`](Hagi/Model/HNet.lean) даёт только
алгебраическое `c(T/r)²=cT²/r²`; физического FLOP-claim нет.

Выбираем [`hnetOptRatio`](Hagi/Model/HNet.lean): `s = (2bT/a)^((3:ℝ)⁻¹)`.
[`hnet_opt_ratio`](Hagi/Model/HNet.lean) доказывает `C(s)≤C(r)` для каждого
`r>0`, [`hnet_opt_ratio_unique`](Hagi/Model/HNet.lean) — равенство цен возможно
только при `r=s`. Доказательство: `s³=2bT/a`, `aTs³=2bT²` и

```
C(r)-C(s) = bT²(r-s)²(2r+s)/(r²s³).
```

`s` — стартовое continuous соотношение для этой cost-модели; нет Nat rounding,
learned chunking, runtime argmin и гарантии training quality.

### 7.1 Finite capped lossless chunks

Для конечного `xs : List α` выбираем `capacity width : ℕ` с fit
`xs.length ≤ capacity * width` и вызываем
[`cappedChunks`](Hagi/Model/AdaptiveChunking.lean), либо берём Nat-ёмкость
`⌊L / r⌋₊` в `floorCappedChunks L r width xs`. Успешный outcome фиксируем
равенством `hsuccess : cappedChunks capacity width xs = some chunks` (или его
floor-аналогом) — оно нужно для границ, сохранения и стоимости.

- `List.splitLengths` применяется к `List.replicate capacity width`, удаляются
  только пустые padding-чанки; последний chunk может быть короче width.
- При нарушении fit — none; пустой вход даёт `some []`; для непустого `xs`
  равенство flatten исключает `chunks = []` (отказ — не zero-cost разбиение).
- [`length_cappedChunks_le`](Hagi/Model/AdaptiveChunking.lean):
  `chunks.length ≤ capacity`;
  [`flatten_cappedChunks`](Hagi/Model/AdaptiveChunking.lean):
  `chunks.flatten = xs`;
  [`ne_nil_of_mem_cappedChunks`](Hagi/Model/AdaptiveChunking.lean): пустых
  членов нет.
- При `0 ≤ L`, `0 < r`: `floorCappedChunks_length_le`:
  `(chunks.length : ℝ) ≤ L / r`; `floorCappedChunks_flatten`:
  `chunks.flatten = xs`.
- Стоимость (конечное `k`, `c : k → ℝ`, `∀ l, 0 ≤ c l`, одна константа
  `M := fun _ => (chunks.length : ℝ)` на всех уровнях):

```
adaptiveCost c M ≤ ∑ l, c l * (⌊L / r⌋₊ : ℝ) ^ 2,   -- floorCappedChunks_cost_le_floor
adaptiveCost c M ≤ ∑ l, c l * (L / r) ^ 2.          -- floorCappedChunks_adaptive_le_static
```

Это детерминированное fixed-width разбиение, не learned/adaptive per-level
router; из неравенств `adaptiveCost` не следуют FLOPs, RAM, wall-time,
training/held-out CE или оптимальная архитектура.

### 7.2 Boundary-driven lossless chunks

Для `boundary : α → Bool` конструктор
[`boundaryChunks`](Hagi/Model/AdaptiveChunking.lean):

```
boundaryChunks boundary xs = xs.splitBy (fun _ next => !boundary next)
```

`true` на следующем токене начинает новый chunk перед ним; `false`
продолжает прежний. Первый токен сам создаёт первый непустой chunk без
запроса флага. Примеры: пустой вход → `[]`, счёт 0; `fun _ => false` на
`[0,1,2]` → `[[0,1,2]]`; `fun _ => true` на `[0,1,2]` → `[[0],[1],[2]]`;
`n % 2 == 1` на `[0,1,2,3,4]` → `[[0],[1,2],[3,4]]`; `n == 0` на `[0,1,2]` →
`[[0,1,2]]`; `fun _ => true` на `[0]` → `[[0]]`.

- [`length_boundaryChunks`](Hagi/Model/AdaptiveChunking.lean):

```
(boundaryChunks boundary xs).length =
  match xs with | [] => 0 | _ :: tail => tail.countP boundary + 1
```

- [`flatten_boundaryChunks`](Hagi/Model/AdaptiveChunking.lean): `xs`
  сохраняется;
  [`ne_nil_of_mem_boundaryChunks`](Hagi/Model/AdaptiveChunking.lean): пустых
  групп нет;
  [`length_boundaryChunks_le`](Hagi/Model/AdaptiveChunking.lean): число групп
  ≤ длина входа.
- Capacity guard [`cappedBoundaryChunks`](Hagi/Model/AdaptiveChunking.lean):
  `some (boundaryChunks boundary xs)`, если счёт ≤ capacity, иначе none.
  [`cappedBoundaryChunks_eq_some_iff`](Hagi/Model/AdaptiveChunking.lean):

```
cappedBoundaryChunks capacity boundary xs = some chunks ↔
  chunks = boundaryChunks boundary xs ∧ chunks.length ≤ capacity
```

  Подменить результат другим разбиением или превратить отказ в пустой успех
  нельзя. Пустой вход даёт `some []` даже при capacity 0; непустой при
  capacity 0 отвергается.
- [`floorBoundaryChunks`](Hagi/Model/AdaptiveChunking.lean) использует
  `⌊L / r⌋₊`. Из hSuccess, `0 ≤ L`, `0 < r`:
  [`floorBoundaryChunks_length_le`](Hagi/Model/AdaptiveChunking.lean) даёт
  `(chunks.length : ℝ) ≤ L / r`;
  [`floorBoundaryChunks_flatten`](Hagi/Model/AdaptiveChunking.lean) сохраняет
  вход;
  [`floorBoundaryChunks_adaptive_le_static`](Hagi/Model/AdaptiveChunking.lean):
  `adaptiveCost c (fun _ => (chunks.length : ℝ)) ≤ ∑ l, c l * (L / r) ^ 2`;
  [`floorBoundaryChunks_adaptive_lt_of_strict`](Hagi/Model/AdaptiveChunking.lean):
  `<` лишь при выбранном `c l₀ > 0` и фактическом
  `hstrict : (chunks.length : ℝ) < L / r`. Пример: `Fin 1`, `c 0 = 1`, `L = 4`,
  `r = 1`, `floorBoundaryChunks 4 1 (fun _ => false) [0,1,2] = some [[0,1,2]]`:
  счёт 1 даёт `1 < 16`.

Здесь детерминированный конечный token-functor, не learned/causal/online/
дифференцируемый router; capacity — предел числа групп, не байтовая ёмкость.

### 7.3 Previous/current tags с проекцией стирания

Предикат на парах θ : α × α → Bool и
[`adjacentPairs`](Hagi/Model/AdaptiveChunking.lean):

```
adjacentPairs [] = []
adjacentPairs (a :: rest) = (a,a) :: (a :: rest).zip rest
```

- После первой пары поля означают `(previous,current)`; восстановление —
  `Prod.snd`: [`map_snd_adjacentPairs`](Hagi/Model/AdaptiveChunking.lean) даёт
  `(adjacentPairs xs).map Prod.snd = xs`;
  [`length_adjacentPairs`](Hagi/Model/AdaptiveChunking.lean) — равенство
  длин. Первый `(a,a)` — dummy seed для одного тега на значение; его флаг
  компаратором не вызывается (`Prod.fst` неверен: на `[0,1]` даёт `[0,0]`).
- Маршрут — §7.2 `boundaryChunks θ (adjacentPairs xs)`;
  [`length_adjacentBoundary_projection_exact`](Hagi/Model/AdaptiveChunking.lean)
  переносит точный счёт.
- Проекция `chunks.map (List.map Prod.snd)`:
  [`flatten_map_snd_adjacentBoundary`](Hagi/Model/AdaptiveChunking.lean) — все
  значения в порядке;
  [`ne_nil_of_mem_adjacentBoundary_projection`](Hagi/Model/AdaptiveChunking.lean)
  — члены непусты;
  [`length_adjacentBoundary_projection`](Hagi/Model/AdaptiveChunking.lean) —
  проекция сохраняет route count.
- Capacity `cappedBoundaryChunks capacity θ (adjacentPairs xs)`; из
  `hSuccess : … = some chunks`:
  [`flatten_cappedAdjacent_projection`](Hagi/Model/AdaptiveChunking.lean),
  [`length_cappedAdjacent_projection_le`](Hagi/Model/AdaptiveChunking.lean)
  (count ≤ capacity),
  [`ne_nil_of_mem_cappedAdjacent_projection`](Hagi/Model/AdaptiveChunking.lean).
  При отказе — none.
- Floor `floorBoundaryChunks L r θ (adjacentPairs xs)`:
  [`floorAdjacent_projection_flatten`](Hagi/Model/AdaptiveChunking.lean);
  [`floorAdjacent_projection_length_le`](Hagi/Model/AdaptiveChunking.lean)
  (`0 ≤ L`, `0 < r`) даёт
  `((chunks.map (List.map Prod.snd)).length : ℝ) ≤ L / r`;
  [`floorAdjacent_projection_adaptive_le_static`](Hagi/Model/AdaptiveChunking.lean)
  — стоимость `≤ ∑ l, c l * (L / r) ^ 2`;
  [`floorAdjacent_projection_adaptive_lt_of_strict`](Hagi/Model/AdaptiveChunking.lean)
  — `<` при `l₀ : k`, `0 < c l₀` и фактическом `< L / r`;
  [`ne_nil_of_mem_floorAdjacent_projection`](Hagi/Model/AdaptiveChunking.lean).

Проверочная θ: `θ p = !(p.1 + 1 == p.2)`. На `[0,1,3,4,10]` даёт
`[[0,1],[3,4],[10]]`; на `[0,1,1,2,10,11,11]` — `[[0,1],[1,2],[10,11],[11]]`
(решение зависит от пары). θ — supplied predicate; через параметры модели он
не обучается.

Отношение к H-Net: [paper v2, equation (4)](https://arxiv.org/html/2507.07955v2#S2.E4)
использует `Q(current)/K(previous)`, `p₁ = 1`, нестрогий порог `≥ 0.5`;
[pinned code](https://github.com/goombalab/hnet/blob/3673fe1217ebeb0d1438c7c71d58d32bdd190ec2/hnet/modules/dc.py)
— `Q(previous)/K(current)`, строгий `> 0.5`, normalization epsilon. Эти
семантики не подменяются generic θ. Lossless здесь — только стирание значений
из paired chunks; head selection H-Net этим восстановлением не является. Не
доказаны learned/differentiable/causal router, encoder, Q/K projection,
BF16-семантика, runtime, training/held-out качество; логический count — не
physical cost.

### 7.4 Head-position recovery над boundary route

[`boundaryHeads`](Hagi/Model/AdaptiveChunking.lean):

```
boundaryHeads boundary xs = (boundaryChunks boundary xs).map List.head?
```

Head-токен каждого chunk маршрута §7.2 (capacity/floor-варианты не
переносятся).

- [`length_boundaryHeads`](Hagi/Model/AdaptiveChunking.lean): число heads =
  числу chunks (`0` для пустого, `1 + tail.countP boundary` иначе).
- [`isSome_of_mem_boundaryHeads`](Hagi/Model/AdaptiveChunking.lean): каждый
  head — реальный токен;
  [`mem_of_mem_boundaryHeads`](Hagi/Model/AdaptiveChunking.lean): head лежит во
  входе.
- [`boundaryHeads_head?_cons`](Hagi/Model/AdaptiveChunking.lean): для
  `a :: rest` `head? = some (some a)` — первый head всегда первый токен
  независимо от `boundary a`.
- [`boundary_of_mem_boundaryHeads_tail`](Hagi/Model/AdaptiveChunking.lean):
  каждый не-первый head лежит на границе (`boundary x = true`). Chunk-start
  mask восстанавливается из heads; других стартов маршрут не создаёт. Это
  структурный аналог forced first head H-Net (`p₁ = 1`), следствие
  `List.splitBy`, не learned prior.
- На paired route §7.3:
  [`boundaryHeads_adjacent_first`](Hagi/Model/AdaptiveChunking.lean) — первый
  head это dummy seed `(a,a)`;
  [`theta_of_mem_adjacentHeads_tail`](Hagi/Model/AdaptiveChunking.lean) —
  каждый не-первый head удовлетворяет `θ p = true`.

Пример: `boundary = (· == 1)`, `[0,1,2]` → chunks `[[0],[1,2]]`, heads
`[some 0, some 1]`. Nodup не заявляется: `[1,1]` → heads `[some 1, some 1]`.
Private-помощник `head_boundary_of_mem_tail` в API не входит. Полная
head-mask equivalence, Nodup, learned sparsity, runtime и качество не
доказаны.

## 8. Конечный выбор архитектуры и качества оценки

Кандидат — действие с настоящим `step`, model safety, памятью и числом
операций; это контур выбора, не neural layer.

Минимизация ресурсов при quality floor.
[`minimumResource`](Hagi/Unified/ParetoExecution/Controller.lean) выбирает
`(memory,operations)` memory-first Lex внутри eligible finite семейства;
[`minimumResource_next_quality_ge`](Hagi/Unified/ParetoExecution/Controller.lean)
проверяет floor на successor. Пустое семейство witness не имеет. Оба селектора
используют `Classical.choose`.

Исполняемый guard —
[`finiteSelection`](Hagi/Unified/ParetoExecution/Controller.lean): фильтр
action list по Bool admission и `List.argmin resourceCost`.
[`finiteSelection_none_iff`](Hagi/Unified/ParetoExecution/Controller.lean) —
ничего не выбирает только если все guards false;
[`selectionReport_guardCalls`](Hagi/Unified/ParetoExecution/Controller.lean)
считает logical guard calls;
[`finiteSelection_cost_eq_minimumResource`](Hagi/Unified/ParetoExecution/Controller.lean)
— при полном списке стоимость равна математическому минимуму в integer-cast
модели. Это не вычисление raw CE на ℝ.

При ошибке оценки ≤ eps на всех successors — conservative floor `floor + eps` и
[`robustMinimumResource`](Hagi/Unified/ParetoExecution/Controller.lean):
[`robustMinimumResource_actual_quality_ge`](Hagi/Unified/ParetoExecution/Controller.lean)
даёт истинный floor, cost-min — только среди certified family. Для
[`argmax_select_certified`](Hagi/Cert/CertifiedArgmax.lean) на конечном `I`
требуем `0≤eps`, `∀k, |GammaHat k-Gamma k|≤eps`, `∀k, GammaHat k≤GammaHat sel`
и gap `2eps<GammaHat sel-GammaHat k` для всех `sel≠k`; без разрыва истинный
argmax не объявляется. Для ratio `Gamma/K` — ещё `K>0` и `∑a
alloc_a*K(idx_a)≤B`;
[`budget_allocation_dominance`](Hagi/Dynamics/ProductiveTransition.lean)
действует при доказанном максимуме ratio, `Gamma≥0` и nonnegative allocations.

Graph filter (опционально):
[`withStructuralConstraint`](Hagi/Research/SchellingCandidateSelection.lean) —
local compatible quota и top-to-bottom reachability; finite Schelling
admission, не динамика сходимости.

Decoded finite codebook: фиксируем `e`, decoder, `X`, конечный nonempty `V`,
`IsProbSys p`, `0<n`, `0<eps`.
[`codebook_raw_selected_population_mean_gap_lower_confidence`](Hagi/Model/CEHeldout.lean)
— lower confidence для raw-CE gap с множителем `61965^G` и радиусом
`eps/ceBound X`. Это fixed-family finite-product оценка, не
representative-IID/deployment guarantee. Множитель `61965^G` вакуозен при
умеренных G: [`unionConfFactor`](Hagi/Model/CEHeldout.lean),
[`union_confidence_vacuous`](Hagi/Model/CEHeldout.lean); любая
anytime-конфиденс `1−δ ∈ [0,1)` доминирует
([`anytime_confidence_dominates_vacuous`](Hagi/Model/CEHeldout.lean)). G-free
замена — time-uniform машина §14 (`anytime_catoni`,
`stitching_eprocess_anytime`); супермартингалность Hoeffding-процесса на
normalized-CE — отдельный мост.

Subgaussian risk gate на конечном nonempty `V`: `∀v, 0<q v`, `∑v qv=1`, `T>0`,
`0<σ²`, `0<α<1` и subgaussian CGF для centering-значений при всех `t` и всех
`c>0`; [`anytime_safe_threshold`](Hagi/Probability/CertifiedEstimator.lean) —
порог `μ+sqrt(2σ²log(T/α))`: вероятность хотя бы одного достижения порога в T
значениях ≤ α.

### 8.1 Префиксная Freedman-confidence для банка raw CE

Конечный банк кодов `i : Fin m`, codebook equivalence `e`, матрица `X`,
горизонт `T`. Для `a`, `b` и ядра `K`:

```
F_i(k,a,b) = CE(b.2, ceLogits X (decodeJoint e (a.1 i))),
μ_i(k,a)   = E_(b∼K(k,a)) F_i(k,a,b),
g_i        = F_i − μ_i,
v_i(k,a)   = E_(b∼K(k,a)) (g_i(k,a,b))².
```

Из `0 ≤ F_i ≤ ceBound X` получаем `|g_i| ≤ ceBound X`; центрирование `E g_i =
0` — определение. При `r > 0`, `V ≥ 0` и одном `historyLaw initial K T T` на
весь банк
[`raw_bank_freedman_maximal_confidence`](Hagi/Model/CEMarkovConfidence.lean)
даёт нижнюю границу `1 − 2*m*(T+1)*exp(−r²/(4*(V + ceBound X*r)))` для

```
∀ i, ∀ j ≤ T, historyCounter v_i T j ≤ V → |historyAdditive g_i T j| < r.
```

Это одновременная оценка всех префиксов (per-member Freedman + union bound);
коэффициент не оптимален, при неположительной границе результат неинформативен.
При `m=0` событие вакуумно. Это вероятностный аудит на заданном ядре, не
arbitrary stopping time и не strict `StepCert`.

На зафиксированной истории — baseline `b`, селектор `σ ω`, prefix `τ ω ≤ T`
(`σ`, `τ` — функции всей history; адаптированность/causality не следуют). A_i,
M_i, g_i — суммы raw CE, conditional PMF mean и residual до `τ ω`. Если prefix
confidence-событие выполнено, обе границы counter для `b` и `σ ω` выполнены и
`2*r < A_b − A_(σ ω)`, то
[`raw_bank_selected_prefix_conditional_ce_gap_pos_of_good`](Hagi/Model/CEMarkovConfidence.lean)
даёт `0 < M_b − M_(σ ω)`. Одно центрирование сохраняет весь observed gap,
поэтому слабого радиуса нет. При `τ ω = 0` premise `2r < 0` несовместима с `0 <
r`: нулевой prefix — не улучшение. Безусловной границы ожидаемого риска и
оптимальности селектора нет.


## 9. Исполнение: guards, router и охлаждение

Для `inputFor(S)` сначала вычисляем proposed successor, затем commit.
[`guardedBatchTrainStep`](Hagi/Contracts/BatchCEBudgetGuard.lean) принимает его
только при `0≤opCost≤budget` и неувеличении CE каждого supplied sample; иначе
возвращает `S`
([`batchSampleCE_guardedBatchTrainStep_le`](Hagi/Contracts/BatchCEBudgetGuard.lean)).
Post-energy не принимается автоматически: оно проверяется на настоящем
successor.

В общем состоянии [`joint`](Hagi/System/GrowthState.lean) обновляет `params :=
params -sp.eta • stepDir`; [`potential_joint`](Hagi/System/GrowthState.lean)
требует `0<L`, `0≤eta≤1/L`, alignment, явной `h_emp_smooth` и measured
`effects.jointEnergy`; только тогда `Φ(joint S)-Φ(S) ≤ -gainJoint S + riskJoint
S`. `gainJoint=eta‖stepDir‖²/2`, `riskJoint=effects.jointRisk`; protected risk
не заменяется gain. Для длинного цикла — commit/hold
[`gate_never_increases`](Hagi/Unified/CertifiedLoop.lean) с доказанным
implication для принятого successor.

Router: bounded-loss Hedge — [`ewWeight`](Hagi/Optimization/MirrorHedge.lean)
(`w_{t+1,i}=w_{t,i}exp(-eta l_{t,i})`),
[`ewNorm`](Hagi/Optimization/MirrorHedge.lean). При `0<eta≤1`, `0≤l_{t,i}≤1`
[`router_regret_bound`](Hagi/Optimization/MirrorHedge.lean): для любого
эксперта

```
A_T-L_T(i) ≤ log(card ι)/eta + eta T/2.
```

Это regret bounded-router, не снижение CE backbone.

Gibbs router `softDef(-L/T)` при `T>0`:
[`gibbs_mixture_quality`](Hagi/Probability/GibbsCore.lean): `∑w_iL_i ≤ m + T
log(card ι)` для finite minimum `m`. Охлаждение `T_t=T0 α^t`, `0<α<1`; для
`0<T0,δ`, `0<θ<1` stop bound относительно `exp(-δ/T_t)` —
[`thermostat_stop`](Hagi/Growth/Thermostat.lean). Только на конечной energy
family.

### 9.1 Перенос спуска через стек FastArch3

Спуск головы (посылка hdrop) переносится через стек с явной утечкой
(механика каскада §15.3). Общая форма: при Lc-липшицевой потере головы
`L(x+dx) ≤ L(x) − δ + Lc·λ·‖dx‖`, строго при `Lc·λ·‖dx‖ < δ`.

- **Residual-блок** `x + f x` ([`resStep`](Hagi/Model/BackboneTransfer.lean)):
  f μ-липшицева ⇒ `residual_transfer_descent`, `residual_transfer_descent_strict`.
- **Стек residual-блоков** (`Hagi/Core/ErrorProp.lean`): λ = `∏(1+μᵢ) − 1`;
  `resStack_leak_le`, `resStack_transfer_descent`. Дифференцируемость не
  требуется.
- **Attention-блок** (Hagi/Model/AttentionTransfer.lean): `attnBranch`
  p v x = ∑ i, p i • v i x (веса — фиксированное распределение вероятностей,
  посылка для QKᵀ); `attn_branch_damped` (демпфирование ошибок softmax
  `Hagi.Core.attention_error_damped`); `attn_branch_lipschitz` (равномерное
  μatt value-карт); pre-norm μn ⇒ λ = `μn·μatt`: `attention_block_transfer`;
  `attention_stack_transfer_descent` (якорь μ_att=0.3, μ_res=0.2:
  (1.3)(1.2)−1 = 0.56).
- **RoPE** ([`rope_pair_inner`](Hagi/Model/RoPETransfer.lean)): вращение —
  изометрия (`rot_norm`, транспорт `toEuc` с `‖toEuc x‖² = pairInner x x`,
  `rope_isometry`: `‖R a − R b‖ = ‖a − b‖`); λ не меняется:
  `rope_block_transfer`, `attnRopeGain_eq`,
  `attention_rope_stack_transfer_descent`. Якорь d=2, θ≡π/3 на (3,4)|(0,0):
  норма 5 сохранена. Матричная ортогональность (RᵀR=I) и операторная норма
  не заявлены.
- **RMSNorm** (Hagi/Model/RMSNormTransfer.lean): носитель `rnVec` (без
  ε-пола, без веса g); чистый носитель не липшицев глобально
  (`rnEuc_not_lipschitz_with`, n ≥ 2); на `r ≤ ‖z‖` — `rn_lipschitz_region` с
  μn(r) = 2√n/r; ε-полный вариант глобально (2/√ε)-липшицев
  (`rnEpsEuc_lipschitz`); `attention_block_transfer_rmsnorm`,
  `attention_stack_transfer_rmsnorm_eps`. Якорь (n=4): ‖rnEuc (3,4,0,0)‖ = 2.
- **GDN** (Hagi/Model/GDNTransfer.lean): mHC state mixing `x ↦ M *ᵥ x`, M
  дважды стохастическая ⇒ `gdnMix_lipschitz` (LipschitzWith 1); гейт —
  посылка μg: `gdn_block_transfer`, `gdn_stack_transfer_descent` (+ `_strict`);
  `hybrid_stack_transfer_descent` (+ `_strict`) — стек attention- и
  GDN-блоков (`HybBlock`, att | gdn) с λ = `∏(1+μᵢ) − 1` (якорь att 3/10,
  gdn 2/10 ⇒ утечка 14/25). Sinkhorn, GDN2 memory update и RAM state-сжатия
  не заявлены.
- **FastArch3-сборка** (Hagi/Model/FastArch3Transfer.lean): SoftmaxHead поверх
  гибридного стека (attention + RoPE + RMSNorm + GDN); `FA3Block`
  (att a R | gdn g), `FastArch3Spec` (blocks + `HeadConfig`),
  `fa3BlockList`/`fa3Stack`/`fa3Gain`, `fa3BlockList_lipschitz`, `fa3Objective`,
  `fastarch3_transfer_descent` (+ `_strict`): спуск головы δ + Lc-липшицева
  потеря головы (P7) + гард `Lc·(∏(1+μᵢ)−1)·‖dx‖ < δ` ⇒ end-to-end objective
  строго убывает. Посылки P1–P9 — таблица в docstring модуля. P5 и P7
  разряжены per-instance: `gdnGateTanh_lipschitz` (tanh-гейт, μg = 1,
  `1/cosh² ≤ 1`) и `fastarch3_head_Lc` (ident-logit headCE, Lc = 2, транспорт
  sup-норма → евклидова через `euclid_coord_abs_sub_le`). Якорь: att 1.4·0.4 =
  0.56, gdn 0.2 ⇒ утечка 0.872; drop 0.5 > 0.5·0.872·1.

Граница: certified descent для FastArch3-SHAPED модели под premises — не
утверждение об обученных весах или Python runtime; softmax-map не разряжен
(P1); полный forward/backward certificate не заявлен.

### 9.2 RAM-протокол и выравнивание lag-1

Мотивация (не Lean-посылка): рассинхрон ключа GDN ~50% против ~99.6%.

- GDN lag-1 (`Hagi/Model/GDNBridge.lean`): контракт `k_{t−1}→v_t` —
  `gdn_lag1_read_miss` (чтение по другому адресу возвращает старую строку),
  `gdn_lag1_alignment` (hit = записанное значение через `gdn_ram_roundtrip`).
- RAM store/load (`Hagi/Model/RamProtocol.lean`): `ramStore`/`ramLoad` на
  GDNRAM-носителе — `ram_store_load_roundtrip` и `ram_store_isolation`
  (запись в один слот не трогает другие). `stutterNorm` — схлопывание
  подряд идущих дубликатов: идемпотентность, длина не растёт, первый/последний
  сохраняются; `ram_load_stutter_head` — первое чтение заикающегося потока
  равно первому чтению нормализованного. Полная эквивалентность потоков
  чанкинга не заявлена.

Рецепт: для GDN-RAM — lag-1 выравнивание ключа.

## 10. Сборка рецепта и граница результата

Порядок одного цикла:

1. задать experts/core/residual, проверить parameter и routing budgets;
2. выбрать initial HNet ratio и разрядность только в их declared models;
3. вычислить current residual gradients и supported propensity;
4. взять общий `D̄`, вычислить `Ā,Q̄,eta_b`, иначе certified `D` или явный
   min-norm;
5. сформировать proposed successor, измерить каждую sample CE, риск и цену;
6. принять только guarded/resource-certified successor, иначе hold;
7. упаковать принятое представление, сложить все error terms, затем оценивать
   выбор на новых данных fixed codebook, не на том же CE-чеке.

Карта «действие → раздел» — таблица в начале документа. Минимизируются
отдельно: supplied-batch CE, selected-estimator MSE, quantization/certification
error, declared resources, HNet cost. Доказанной совместной или глобально
оптимальной архитектуры/тренировки, held-out преимущества, physical FLOP/time
saving нет: исполняемые определения, finite certificates и явные измеряемые
предпосылки не смешиваются.

## 11. Каноническое ядро сертификации (Hagi/Cert/Core.lean)

Источник — `Hagi/Cert/Core.lean`, `Hagi/Cert/StepGen.lean`,
`Hagi/Cert/Empirical.lean`, `Hagi/Cert/Adapters.lean`, `Hagi/State/Views.lean`,
`Hagi/Training/StepProvider.lean`; ядро не зависит от остальной библиотеки.

### 11.1 CertStep, HoldStep и телескоп

- `SystemMetrics S TaskId` — objective, risk, budget (S → ℝ) и task-тег;
- `StepObligations TaskId` — obligations с floor;
- `FloorsKept` — `∀ t, obl.floor t ≤ M.objective s`;
- `CertStep` — прогресс: `0 < drop`,
  `objective s' ≤ objective s − drop`, точные законы потребления
  `budget s' = budget s − budgetSpend`, `risk s' = risk s − riskSpend` с
  `0 ≤ budget s'`, `0 ≤ risk s'`, плюс floorsKept; производные оценки
  `CertStep.budgetBound` и `CertStep.riskBound`;
- `HoldStep` (`s' = s`, floors kept) всегда доступен через `HoldStep.id`;
  `TransitionStep` = progress | hold.

Композиция и телескоп:

```
CertStep.trans h₁ h₂        -- тот же obl: drop'ы и spend'ы складываются
CertStep.trans' h₁ h₂ h_fl  -- obl₂ ⊵ obl₁ поточечно
trajectory_telescope n t steps :
  M.objective (t n) ≤ M.objective (t 0) − ∑ j ∈ Finset.range n, (steps j).drop
```

`FloorsKept` — независимое поле: descent связывает objective одного состояния с
другим, floors — отдельные обязательства; держится посылкой каждого шага и
переносится композицией.

Обобщение — `Hagi.Cert.CertStepGen`: произвольный индекс задач TaskId,
остаток риска как поле с законом расщепления и свёрнутый δ-канал. Ядро
`CertStep` вкладывается (`Hagi.Cert.certStep_to_gen`); интерфейсный слой —
`Hagi/Training/StepProvider.lean`. Мост `HonestTransition` в полное ядро:
toKernelCertStep (остаток риска 0) и обобщённый
`Hagi.Unified.HonestTransition.HonestTransition.toCertStepGen` (остаток риска —
свободный параметр). Адаптеры над `Cert.Core`: `descentCertStep`,
`holdTransition`, `protectedRisk_le_of_riskRem`. Дублирование имени `CertStep`
с `Hagi.Unified.HonestTransition.CertStep` — известный долг.

### 11.2 Четвёртый ресурс δ и эмпирические посылки

`CertStepDelta` (Hagi/Cert/Core.lean) — пошаговый бюджет вероятности ложного
коммита списывается равенством `deltaLevel s' = deltaLevel s − delta` с
неотрицательным остатком:

```
CertStepDelta.deltaBound h   : h.delta ≤ deltaLevel s
CertStepDelta.trans h₁ h₂    : drop'ы, spend'ы и δ складываются
delta_telescope n t L h0 steps :
  ∑ j ∈ Finset.range n, (steps j).delta ≤ L (t 0)
```

Посылка `h0 : 0 ≤ deltaLevel (t 0)` явная. Перенос поля внутрь `CertStep` не
сделан.

`Empirical P` (Hagi/Cert/Empirical.lean) — типизированная обёртка эмпирических
посылок: measuredLaw, tolerance (+ `0 ≤ tolerance`), modelRef, premise.
Конструкция требует предъявить `P`; `Empirical.out` возвращает ровно
предъявленное. Заместительного пути для голых `h_emp_*` нет.

### 11.3 Состояние с буферами оптимизатора

Hold, восстанавливающий веса, но не откатывающий буферы оптимизатора (m, v, t),
держит stale momentum. Носитель `StateWithOptimizer S O` = core + opt
(Hagi/Cert/Core.lean):

```
StateWithOptimizer.ext_iff        : p = q ↔ core = core ∧ opt = opt
HoldStep.optimizer_state_fixed h  : hold ⇒ q.opt = p.opt (точно)
HoldStep.project_core o₀ hobj h   : lift на core-метрики при
                                    оптимизатор-независимом objective
```

`HoldStep.hold : s' = s` на этом носителе покрывает буферы ровно: шаг,
сохраняющий веса, но прокатывающий momentum, `HoldStep` здесь построить нельзя.
Посылка hobj (objective может зависеть от буферов) явная.

### 11.4 View TrainState

`toSystemMetrics` (Hagi/State/Views.lean) подаёт канонический `TrainState` в
ядро: objective = energy, risk = riskOf, budget = budgetOf, `TaskId = Unit`;
спецификации — rfl. Телескоп единственного потребителя —
`Hagi/Training/Ctv2Telescope.lean`. Структурная конверсия носителей остаётся
открытой.

## 12. Острый range-шаг в потребителях и BF16-гард

### 12.1 Сертифицированный drop и curvature-мосты

Константы `ceStepLogitRange` (§3.8) и `batchLogitRangeSquare` (§3.9) подключены
к потребителям аддитивными мостами; старые утверждения не меняются:

```
batchLogitCertifiedDrop                        : if R'=0 then 0 else 2·A²/R'
batchLogitCertifiedDrop_nonneg                 : 0 ≤ drop'
batchCertifiedDrop_le_batchLogitCertifiedDrop  : 0 < R' → drop ≤ drop'
batchLogitRangeSquare_le_rangeCurvature_mul_alignment : R' ≤ K·A (без посылок)
alignment_le_scaled_logitCertifiedDrop         : 0 < R' → 2·A/(K+1) ≤ drop'
ceStepLogitRange_sq_le_featureMass_sq_norm_sq  : R'ᵢ² ≤ 4·(Σ|X|)²·‖D‖²
ceStepLogitQuad_le_engine                      : (η·R'ᵢ)²/8 ≤ (Σ|X|)²·η²·‖D‖²/2
jointEnergy_le_ceLinear_logitRange             : jointEnergy ≤ E − η·⟪g,d⟫ + (η·R'ᵢ)²/8
```

Провода:

- `Hagi/Contracts/BatchCEBudgetGuard.lean` — острый residual
  `batchLogitCertifiedDrop` и мост «старый ≤ новый»;
- `Hagi/Contracts/BatchCEAlignmentBudget.lean` — та же константа `K`
  контролирует и острую `R'` (безусловно), а `2/(K+1)` сертифицирует острый
  drop при `0 < R'`. Константа `(K+1)/2` телескопа §3.2 не сужается: из
  `R' ≤ R` более острая curvature-константа не выводится;
- `Hagi/Unified/DerivAlong.lean` — острая по-примерная квадратура и
  точечная мажоранта для jointEnergy с relation-леммой к engine-члену;
- `Hagi/Contracts/BudgetedParetoStepContract.lean` и
  `Hagi/Contracts/BudgetedParetoStepCert.lean` — не переключены: их дельты
  привязаны к `budgetedParetoBatchTrainStep`, чей η идёт от `batchSafeStep`;
  переключение — новая пара train-step и репликация guard-веток. Моста
  `drop ≤ drop'` между разными исполненными шагами нет.

Посылка `0 < batchLogitRangeSquare` в мостах несущая. Вырождение:
`batchAlignment_pos_of_logitRangeSquare_pos`
(Hagi/Model/BatchCEDescentLogitRange.lean) — `0 < R' ⇒ 0 < A` без посылок.

### 12.2 BF16-гард для batch-шага

Сертифицированный спуск — `2·batchAlignment²/batchLogitRangeSquare`
(`batchLoss_logitSafeStep_le_residual`). BF16-гард — посылка, не вывод: если
логитный апдейт проходит через BF16 с равномерной ошибкой

```
|ceLogits (X b) θbf v − ceLogits (X b) (batchLogitNextParameters X θ y) v| ≤ eps
```

и `4·eps < 2·A²/R'`, то θbf строго уменьшает истинный `batchCEObjective` на `Δ
= 2·A²/R' − 2·eps > 0`:

```
batchLoss_le_of_logitPerturbation : per-logit eps → потеря сдвигается ≤ 2·eps
bf16_guarded_ceRange_descent_le   : gate → batchLoss θbf ≤ batchLoss θ − (drop − 2·eps)
bf16_guarded_ceRange_descent      : gate → ∃ Δ > 0, batchLoss θbf ≤ batchLoss θ − Δ
```

Средний штраф `2·eps` — 2-липшиевость one-hot CE
(`CEQuantized.ceOneHot_le_of_abs_sub_le`); gate держит 2× запас. Режим `eps =
0` (`bf16_exact_binade_ceRange_descent`) требует точного равенства логитов
посылкой: на уровне кодов разность представима точно
(`BF16Delta.exists_sameBinade_difference`), но перенос ℚ→ℝ автоматически не
мостится. Универсального утверждения о bf16-округлении нет (контрпример:
θbf=(1,2) на identity-признаках строго увеличивает потерю).

ℚ→ℝ мост с производным eps (Hagi/Runtime/BF16Delta.lean,
Hagi/Contracts/BatchRangeBF16Cert.lean):

```
abs_sub_le_of_isNearest_normal (BF16Delta):
  x ≠ 0, 2⁻¹²⁶ ≤ |x| ≤ 2¹²⁷, IsNearest x c ⇒ |decode c − x| ≤ 2⁻⁸·|x|
bf16_logitPerturbation_of_nearestNormalCodes (Cert):
  рациональные логиты в нормальном диапазоне через nearest-коды
  ⇒ пертурбация ≤ (2⁻⁸:ℝ)·M
bf16_guarded_ceRange_descent_of_nearestNormalCodes (Cert):
  4·(2⁻⁸·M) < certified drop ⇒ строгий спуск
bf16_nearestRoundTrip_relativeError_gt (BF16Delta):
  2⁻⁸·|129/128| < |0 − 129/128| — round-trip теряет весь малый апдейт
```

`2⁻⁸` выведена из носителя (fraction : Fin 128 ⇒ 8 значащих бит ⇒ ulp-пол
`2⁻⁷`, пол-ulp `2⁻⁸`). Рациональность целевых логитов — явная посылка; нужен
FP32-мастер весов.

### 12.3 Переход в Cert/Core

`batchCEMetrics`: objective = истинный batchLoss на EuclideanSpace-носителе
параметров, risk/budget = остатки с полярностью «риск-остаток = лимит −
защищённый риск» (задаётся вызывающей стороной).
`batchCE_bf16_transitionStep_progress` — progress-ветка (gate активен,
«риск-остаток − операционный риск» ≥ 0, drop = `2·A²/R' − 2·eps`);
`batchCE_transitionStep_hold` — hold-ветка через `HoldStep.id`. Операционный
риск остаётся символическим до появления consumer'а.


## 13. Средне-скоростной optimizer-стек: EF21-Muon

Coherence curriculum с EF21-Muon телом и тернарной проекцией через EF21 Markov
feedback. Формальный слой:

```
IsContractive C α                    : ‖C u − u‖₂ ≤ (1−α)‖u‖₂
ef21_update_norm_le                  : ‖v + C(g−v) − g‖ ≤ (1−α)‖g−v‖
ef21_lyapunov_descent                : η ≤ 1/(2L) → f' ≤ f − (η/2)(1−2Lη)‖g‖² + (η/2)(1+2Lη)δ²
ef21_pl_linear_rate                  : gate c₂cδ < 2μc₁, cap → ρ = 1−2μc₁+c₂cδ ∈ [0,1)
doublyStochastic_sq_le               : DS M → ‖Mx‖₂ ≤ ‖x‖₂
rowStochastic_opNorm_le_one          : ‖M‖_op ≤ 1 (ℓ∞-инстанс ErrorProp)
mhc_stack_no_growth                  : DS-стек + нулевой residual → ‖propagate L δ₀‖ ≤ ‖δ₀‖
one_sub_nsStep                       : 1 − t(3−t²)/2 = (1−t)²(t+2)/2
nsIter_dist_sq                       : 1 − φ(iter) ≤ (3/2)(1−iter)²
```

Инстансы контракта: identity (α=1), zero (α=0), scaling `u ↦ c•u` (α=c ∈
[0,1]). `Hagi/Optimization/EF21Quantizer.lean`: TopK (fixed-support) и
тернарный лифт `qTernVec` — α=0-инстансы (`topK_contractive`,
`qTernVec_contractive_zero`); для α ∈ (0,1] контрактивность опровергнута явными
свидетелями (`topK_not_contractive_pos`, `qTernVec_not_contractive`: u=s/2
округляется в 0, ‖Q u−u‖=‖u‖). Аддитивный контракт `IsInexactCompressor C α ε`
(‖C u−u‖₂ ≤ (1−α)‖u‖₂+ε) переносится через Markov-обновление
(`ef21_update_norm_le_inexact`) и даёт одношаговый спуск Ляпунова
`ef21_inexact_descent`; инстансы `topK_inexact`, `qTernVec_inexact` (ε=0),
полушаговый бюджет `‖Q u−u‖₂ ≤ √n·s/2` при in-range (`qTernVec_error_inrange`).
Premise-only: относительная контрактивность c<1 и saturation-tail инстанс (в
energy-форме — `ternary_split_le`, §6.1).

Newton-Schulz/Muon: скалярный сертификат `one_sub_nsStep`/`nsIter_dist_sq`
относится к сингулярным значениям в (0,√3);
`Hagi/Step/NewtonSchulzMatrix.lean`: `nsMatrixStep_diagonal_contraction`
(диагональное подпространство, sup-норма), `nsMatrixStep_orth` (ортогональная
эквивариантность), `ns_contraction_svd`, `muon_step_bound_ns_svd`
(спектрально-нормовая контракция при SVD-посылке), `nsSpectralNorm_orth_inv`.
Без SVD-посылки `hP` в `Hagi/Step/Muon.lean` остаётся гипотезой. mHC: Sinkhorn
не требуется — M дважды стохастическая посылкой.

## 14. Anytime-сшивание e-процессов, гейт-конвейер и аудит-леджер

### 14.1 Сшивание e-процессов

`Hagi/Unified/StitchingEProcess.lean`:

```
stitching_master_supermartingale   : Σ wᵏ•Eᵏ — супермартингал (Finset-индукция)
stitching_master_initial_mass      : μ[M₀] = Σ wᵏ·μ[Eᵏ₀]
stitching_eprocess_anytime         : Σw ≤ 1, μ[Eᵏ₀] ≤ 1 → Pr[∃t≤n, Mₜ ≥ 1/δ] ≤ δ
                                     (равномерно по n; через ville_anytime_false_alarm)
stitching_master_mono              : поточечная монотонность master'а (w ≥ 0)
```

Посылка hE0 — нормировка `μ[E i 0] ≤ 1` каждого эксперта.
`stitching_alarm_superset` — statement мощности drift-детекции (в одну сторону;
мотивация: 6% → 63% при ≤5% FPR).

Счётное сшивание `Hagi/Unified/CountableStitching.lean`:

```
stitchedMasterCountable        : M t = ∑' k, w k · E k t (tsum на ℕ)
stitching_countable_initial_mass : μ[M₀] = ∑' w k · μ[E k 0]
stitching_countable_ville      : Summable w, ∑'w ≤ 1, точечная суммируемость смеси,
                                  μ[E k 0] ≤ 1 → Pr[∃t ≤ n, Mₜ ≥ 1/δ] ≤ δ ∀n
stitching_countable_geometric_weights : ∑' (1/2)^(k+1) = 1
```

Маршрут: монотонные конечные префиксы + непрерывность меры снизу; строгий
level-c аларм ⊆ возрастающее объединение конечных префиксных алармов. Посылка
`Summable w` load-bearing. Счётный супермартингальный closure и новые
concentration-утверждения не добавляются.

Эмпирическая дисперсия Фридмана: при бюджете предсказуемой дисперсии `V ≤ c²`
эмпирический экспонент `exp(−r²/(4(V+B·r)))` (форма §8.1) не превосходит
фиксированный c²-экспонент (`freedman_exp_empirical_le_fixed`; положительность
знаменателей — явные посылки hd1/hd2); аддитивная форма
`freedman_empirical_confidence_ge_fixed` (рамка `1 − 2m(T+1)·exp`).

### 14.2 Gate pipeline

`Hagi/Contracts/GatePipeline.lean` — конвейер «измерение → Hoeffding-граница →
δ-расписание → этажи → решение»:

```
hoeffding_pm1_two_sided      : [−1,1]·X, допуск η → P(|ΣX−Σμ| ≥ nη) ≤ 2e^{−nη²/2}
gate_delta_schedule_sum_le   : K ≤ шести → Σ_{k<K} 6/(π²k²) ≤ 1
gate_pipeline_false_commit   : P(Bad k) ≤ β k, Σβ ≤ δ → P(нет ложного commit) ≥ 1 − δ
gate_pipeline_budget         : β k = δ·6/(π²(k+1)²)/(1+m) по (1+m) этажам — Σ ≤ δ
gate_anytime_valid           : (∀t, F t ⊆ {δ⁻¹ ≤ M_t}) → μ.real{∃t≤n, F t} ≤ δ ∀n
gate_fixed_radius_unusable   : n=512, δ=1/20, k=10, m=8: 2e^{−256r²} ≤ β ⇒ r > 0.14
```

Свежесть потока = `IsProbSys p`; вложение anytime-события — явная посылка.
Рекомендация: anytime-гейт (`gate_anytime_valid`) с адаптивным n и эмпирической
дисперсией Фридмана вместо фиксированного n — фиксированный радиус на n = 512
несовместим с допуском 1/20.

### 14.3 Audit ledger

`Hagi/Contracts/AuditLedger.lean` — мост протокола HoeffdingAudit: реестр
аудита как машина состояний над срезами тестов; концентрационная математика не
новая.

```
AuditStream                  : полуинтервал [lo,hi) на ℕ с курсором
AuditLedger (σ,ι)            : δtotal, streams, floors (taskId → floor), spent (α per task),
                               rejected, finalTest/Lo/Hi + инварианты streamsDisjoint,
                               spentNonneg, spentTotal (Σ spent ≤ δtotal), finalIsolated
audit_consume_alpha_exact    : трата α уменьшает remaining ровно на α
audit_consume_alpha_valid    : Σ spent' = Σ spent + α ≤ δtotal, остаток ≥ 0
audit_streams_disjoint       : продвижение курсора не ломает непересечение
audit_rejected_consumed      : индекс ниже курсора отвергнутого потока не входит
                               в свежий срез никакого потока
audit_false_harm_bounded     : P(Bad t) ≤ spent t ⇒ P(нет ложного вреда старым задачам) ≥ 1 − δtotal
audit_alpha_spends_radius    : 2e^{−2nε²} ≤ spent t ⇒ хвост покрыт бюджетом
final_test_untouched         : flag=false ⇒ ни один поток не покрывает индекс финального теста
audit_touch_final_flips / audit_touch_final_breaks : касание финального теста переключает флаг
```

Границы: floors/current gain — поля (теорема о «выигрыше» потребовала бы полной
семантики гейта); семантика метрик — на стороне измерения.

## 15. Каскадные границы ошибки и ранговые бюджеты

### 15.1 Прямоугольный bottleneck и space decoupling

Мосты Hagi/Contracts/GradientBottleneck.lean и
Hagi/Architecture/FactorRank.lean:

```
coSelQ_mul_selP / emb_rank_eq      : row-embedding — изометрия ранга
frobenius_selP_eq                  : ‖selP·C‖_F = ‖C‖_F
eckart_young_lower_bound_rect      : rank B ≤ k → tail_rect(A,k) ≤ ‖A−B‖²_F
gradient_bottleneck_bound_rect     : прямоугольный (Ctxt×Voc) градиентный bottleneck
factor_update_rank_le              : rank(A·Bᵀ) ≤ r
projI_add_projR / projI_idem / projR_idem : P_I = UUᵀ, P_R = I−UUᵀ, P_I+P_R = 1
spaceDecoupling_zero_drift         : UᵀΔ = 0 → I-координаты нетронуты точно
exists_orth_direction              : c < d → ∃ v ≠ 0, Uᵀv = 0
spaceDecoupling_capacity           : P_R·v = v ≠ 0 — ёмкость R-направлений реальна
```

При `k = 0` bound вырождается в `‖A‖² ≤ ‖A−B‖²`; rank(Δ) ≤ 2D из ранга головы —
посылка.

### 15.2 Прямоугольная спектральная идентификация Eckart–Young

`Hagi/Contracts/GradientBottleneckIdentification.lean` — хвост встроенной
квадратной матрицы равен спектру прямоугольных `singularValues`:

```
selP_conjTranspose_mul_selP        : inj injective → (selP inj)ᴴ·selP inj = 1
embedded_gram_eq                   : (selP inj·A)ᴴ·(selP inj·A) = Aᴴ·A
embedded_eigenvalues₀_eq           : eigenvalues₀ встроенного Gram = eigenvalues₀ Aᴴ·A
embedded_singularValues_eq_rect    : singularValues₀ (selP inj·A) = Rectangular.singularValues A
                                     на Fin(min #m #n)
singularValues_pos_of_lt_rank_rect : k < rank A → σₖ > 0
rectangularTail / tail_sum_sq_truncatedSingularValues_tail_eq
                                   : хвост-сумма §15.1 = Σ (истинный прямоугольный хвост)²
eckart_young_lower_bound_rect_true_tail : rank B ≤ k → Σ tail_rect(A,k)² ≤ ‖A−B‖²_F
gradient_bottleneck_bound_rect_true_tail : consumer для logitGradRectM
```

Носитель — матричный/`eigenvalues₀`; мост к `LinearMap.singularValues` Mathlib
не закреплён.

### 15.3 Cascade leak bound для projected adapters

`Hagi/Core/ErrorProp.lean` + `Hagi/Architecture/CascadeLeak.lean`, носитель
`propagate`:

```
propagate_sub (ErrorProp, additive):
  propagate L a − propagate L b = propagateLin L (a − b)
cascadeGain L = ∏_m ‖J_m‖
propagateLin_norm_le: ‖propagateLin L δ‖ ≤ cascadeGain L · ‖δ‖
cascadeGain_le_one:   (∀ p ∈ L, ‖p.1‖ ≤ 1) → cascadeGain L ≤ 1

cascade_leak_bound:
  ‖propagate S (x + w • ε) − propagate S x‖ ≤ |w| · cascadeGain S · ‖ε‖
cascade_leak_bound_op:
  ε = ΔR *ᵥ (projR U *ᵥ x) ⇒
  ‖net(W + w·Δ_R, x) − net(W, x)‖ ≤ |w| · L_stack · ‖ΔR‖ · ‖P_R x‖
cascade_leak_bound_contractive: (∀ ‖p.1‖ ≤ 1) ⇒ gain выпадает
cascade_leak_router_linear: leak(w) = w • leak(1)  (ТОЧНО)
cascade_leak_eq_empty: S = [] ⇒ равенство
tailDiag_mulVec_norm_le:
  ‖tailDiag m r s *ᵥ y‖ ≤ sqrt(rhoTail m s r · ∑ s j²) · ‖y‖
cascade_leak_bound_rhoTail:
  leak ≤ |w| · L_stack · sqrt(rhoTail · ∑ s j²) · ‖P_R x‖
readback_noise_witness (0 < c ⇒ ∃ n ≠ 0, Uᵀ *ᵥ n ≠ 0)
```

Утечка линейна по router-весу `w`; проекция P_R сама по себе границу не
обнуляет — убивают утечку только router (`w → 0`) или rank-capture (`rhoTail →
0`). Isolation в одну сторону: `Uᵀ * A_orth = 0` (`fiberSplitOrtho`) защищает
инъекцию (`fiber_injection_preserves_cortex`), но не readback `Uᵀ h`
(`readback_noise_witness`); защита readback требует гейтинга или посылки `Uᵀ *ᵥ
Δ = 0` из `spaceDecoupling_zero_drift`.

### 15.4 Isotropic-Frobenius sensitivities и SafeQP drift

`Hagi/Architecture/IsoFrobCascade.lean` + `Hagi/Budget/IsoFrobAlloc.lean` +
`Hagi/Step/SafeQPStep.lean`:

```
columnEnergy_basis (ТОЧНО, без вероятности):
  ∑ i ‖J *ᵥ e_i‖² = frobSq J
isoFrobEnergy J = frobSq J / d
isoFrobEnergy_eq_basis_avg:  iso = базисное среднее
isoFrobEnergy_le_opNorm_sq:  frobSq J / d ≤ ‖J‖²
propagateLin_frobEnergy_le:
  ‖propagateLin S δ‖₂² ≤ (∏ frobSq J_l) · ‖δ‖₂²
propagateLin_isoEnergy_le:
  ≤ d^|S| · ∏(frobSq_l / d) · ‖δ‖²
isoCascadeEnergy_le_cascadeGain_sq:
  isoCascadeEnergy S ≤ cascadeGain S²

frobSq_add_smul:  frobSq (M + η•W) = frobSq M + 2η·frobInner M W + η² · frobSq W  (ТОЧНО)
frobSq_smul:      frobSq (η•W) = η² frobSq W
safeqp_linear_test_insufficient:
  ∀ tol ∃ η: линейный тест (g = 0 ⇒ ⟪g,d⟫ = 0 ≥ −tol) проходит,
  а точный drift η²·frobSq W > tol
safeqp_second_order_acceptance:
  (L/2)·η²·‖d‖² − eps ≤ η·⟪g,d⟫ ∧ descent-лемма ⇒ dL ≤ eps
safeqp_precond_conflict_free:
  d = (QᵀQ) *ᵥ g ⇒ ⟪g,d⟫ = ‖Q*gᵥg‖² ≥ 0

isoFrobSensitivity Jtail hScale j = isoFrobEnergy (Jtail j) * hScale j
weightedExpAllocation_isoFrob_optimal:
  c := isoFrobSensitivity ⇒ closed-form экспоненциальная аллокация оптимальна
  (транспорт weightedExpAllocation_optimal)
```

Изотропное среднее не превышает worst-case усиление `cascadeGain`; для
linfty-op-нормы обратное `frobSq ≥ d‖J‖²` ложно. Мотивация (не Lean-посылка):
спектральные произведения `∏‖J_k‖` переоценивают ранние слои и голодают
поздние; изотропно-фробениусова калибровка дала MSE 2.2e-5 против 2.5e-5
uniform. Линейного приёмного теста для билинейных шагов недостаточно.

### 15.5 Product-of-quantized-factors: ResidualVQ

Мотивация (не Lean-посылка): одностадийное 3.2-бит `q(A)·q(B)` роняет
нелинейные адаптеры до ~50%; двухстадийный ResidualVQ возвращает 94%+.
`Hagi/Budget/ResidualVQ.lean`:

- Точное разложение
  `(A+EA)(B+EB) − AB = EA·B + A·EB + EA·EB` (`quantProd_decompose`).
- `frobSq_mul_le`: `frobSq(A·B) ≤ frobSq A · frobSq B` (прямоугольная
  субмультипликативность, носитель `Hagi.Core.frobSq`).
- `quantProd_frob_bound`; относительная форма `quantProd_relError` и
  `_sq`: при пофакторных относительных ошибках e, f ошибка произведения
  подчиняется `(e + f + e·f)²`; `quantProd_crossTerm_amplifies`: при равных e
  экспонента ≥ 2e. Произведение никогда не квантуется «дешевле» суммы
  ошибок факторов.
- Двухстадийная композиция: `W − (R1+R2) = (W−R1) − R2` точно
  (`residualTwoStage_exact`); ошибка после второй стадии ≤ ε2
  (`residualTwoStage_error_le`) и аддитивный сертификат ≤ ε1 + ε2
  (`residualTwoStage_error_le_add`); BF16-head мост на сетке 2⁻⁸: итог
  ≤ ε1 + 2⁻⁸·ε1 (`residualHeadBudget`).

Рецепт: биты на фактор — по закону `(e+f+ef)²`; произведение — только через
резидуальную вторую стадию (аддитивная, не мультипликативная композиция
ошибки).

## 16. Исполняемый путь против spec-селекторов

Критерий изоляции — `Classical.choose`/existence-witness в `def`, а не флаг
noncomputable: над ℝ почти каждая замкнутая формула помечена noncomputable лишь
потому, что ℝ классический. Choose-селекторы — математические selection
contracts, потребляемые только теоремами.

Исполняемый путь:

- шаг: [`batchLogitSafeStep`](Hagi/Model/BatchCEDescentLogitRange.lean) —
  `if R'=0 then 0 else 4A/R'²`;
- направление (B=2): [`segmentMinNorm`](Hagi/Step/ProjectionDescent.lean) —
  `g0+τ(g1−g0)`; связь с общим случаем —
  [`batchGradientMinimizer_pair`](Hagi/Model/BatchCEDescent.lean);
- bound шага QP: [`safeqpEtaMax`](Hagi/Step/SafeQPStep.lean);
- дискретный выбор:
  [`finiteSelection`](Hagi/Unified/ParetoExecution/Controller.lean)
  (Bool `admissionGuard` + `List.argmin`), мост
  [`finiteSelection_cost_eq_minimumResource`](Hagi/Unified/ParetoExecution/Controller.lean);
- кодек: `dyadicPayload`/`dyadicBlock` (BitVec 16) и packed-decode теоремы;
- поблочный scale-селектор `selectedGroupScalesExec` (§6.2).

Spec-only селекторы (исполняемых потребителей нет):

- [`batchGradientMinimizer`](Hagi/Model/BatchCEDescent.lean) —
  existence-witness минимальной нормы над convex hull;
- [`safeQP_exists_unique`](Hagi/Step/SafeQP.lean) — теорема (premise-form);
- [`minimumResource`](Hagi/Unified/ParetoExecution/Controller.lean) и
  [`robustMinimumResource`](Hagi/Unified/ParetoExecution/Controller.lean) —
  noncomputable selection contracts; robust-вариант исполняется как
  `finiteSelection` с консервативным floor `qfloor+eps`;
- [`selectedGroupScales`](Hagi/Model/CEGroupedScale.lean) и
  [`selectedCoupledScales`](Hagi/Model/CEJointScale.lean) — точные конечные
  селекторы над dyadic-кодами.

Оба scale-селектора — разрешимо-конечный поиск (255 кодов/блок, `Fin 255`), а
не выбор по неразрешимому предикату. Проблема joint-селектора
`selectedCoupledScales` (255^G присваиваний, `jointCandidateCount`) —
стоимость, а не конструктивность; исполняемая форма — поблочный суррогат
`selectedGroupScalesExec` с мостом `selectedGroupScalesExec_cost_eq`, 255·G
logical score calls, `localEvaluationCount_le_jointCandidateCount`.

## 17. Нейро-символьный точный слой: булева голова Венна и ANF

Все 16 булевых функций двух переменных — маски `Fin 4 → Bool` на решётке Венна
(4 атома-конъюнкции); слой реализуется 4 ReLU-нейронами + линейной головой с
{0,1}-весами.

- [`Hagi/Data/BoolVenn.lean`](Hagi/Data/BoolVenn.lean): `venn_universal`
  (каждая `Bool → Bool → Bool` — маска, 64 случая), `rank_histogram` (ранги
  `1-4-6-4-1`), `de_morgan`/`de_morgan_involution` (инволюция дополнения
  маски на тех же входах; вариант с отрицанием входов ложен), `hasse_edges`
  (ровно 32 ориентированных ребра).
- [`Hagi/Model/Logic/VennHead.lean`](Hagi/Model/Logic/VennHead.lean):
  `vAtoms_sum_one` (атомы one-hot на {−1,+1}-входах); `vennHead_exact` —
  64-случайный мост голова↔таблица истинности; `venn_certified` —
  композиция с `Hagi.Cert.CertifiedArgmax.certified_argmax_strict`: логит-пара
  `![f, 1−f]` с eps-зазором ровно 1, сертифицированный argmax-индекс равен
  значению истинности при `2ε < 1`; `venn_mask_ternary` — `Hagi.Runtime.qTern`
  (масштаб 1) тождественен на {0,1}: штраф квантования весов головы ровно 0.

Граница: точность для логики двух переменных, а не «решение логики вообще»;
реальный масштаб mask-линейных голов — `n ≤ 4-5` входов; bf16-точность малых
целых не композится с `Hagi/Runtime/BF16Delta.lean` без нового API.

### 17.1 CE-обученный выбор маски под сертифицированным гвардом

[`Hagi/Contracts/LogicChoiceCert.lean`](Hagi/Contracts/LogicChoiceCert.lean):
выбор маски как CE-задача. 16 масок — классы (`Fintype (Fin 4 → Bool)`);
лог-линейная голова по атомным признакам `choiceFeatures v j =
vAtoms·maskReal`; при единичных параметрах логит класса v равен выходу
`vennHead (cand v)` (`choiceFeatures_logit_ones`). Спуск — машина §3.9
(`batchLoss_logitSafeStep_le_residual`) на choice-batch; `choiceCEMetrics` +
`choiceCE_transitionStep_progress`: спуск choice-CE с certified drop `2·A²/R'`,
floors тривиальны (`batchLoss_nonneg`), исполнение точно (`vennHead_exact`).
Витнес `choice_certified_behavior`: батч из двух кандидатов (const-false, AND),
`R' = 1/4` точно.

Сертификат покрывает спуск CHOICE-CE и точное исполнение выбранной маски. Он не
сертифицирует, что выбранная функция правильная: голова может верно спускать CE
и выбрать неверную маску («exact ≠ true»).

### 17.2 Спецификации процессора Венна

- **Упаковка**
  ([`Hagi/Runtime/VennPacking.lean`](Hagi/Runtime/VennPacking.lean)):
  16×4 {0,1}-матрица = 64 трита (`vennTrits_count`, `vennTritRow` —
  `ternaryValueEncode` на уровне 1). Flat 5-тритные блоки `ternaryByteBlock`
  → `tritsBytes 64 = 13` байт (`flatVennBytes`); 12 байт невозможно
  (`flatVenn_twelve_byte_impossible`, 3^64 > 2^96). Построчно — 4 трита на
  строку: `rowByte_injective`, `rowBytes_card = 16`. Dyadic с масштабом на
  блок (`dyadicBlock : BitVec 16`) → 26 байт (`dyadicVennBytes`); общий
  масштаб — 13 payload + 1 байт масштаба (`scaleCode_byte`,
  `sharedScaleVennBytes`) = 14 байт. Счёты — формула ⌈n/5⌉ на конкретном
  размере; потоковый кодировщик не инстанцирован.
- **Роль H₄** ([`Hagi/Data/BoolVenn.lean`](Hagi/Data/BoolVenn.lean)):
  маска↔таблица
  истинности на 4 атомах — тождество (`mask_truth_table_identity`,
  `atomIdx_atomBools`); `vennWalsh` (= `Core.sylvester` порядка 4) —
  преобразование спектра: `vennWalsh_sq` (H·H = 4•1),
  `vennWalsh_mul_transpose`,
  `(1/2)•vennWalshReal` ортонормален (`vennWalshOrthonormal`).
- **CE-пол 16 классов на single-atom батчах** (там же): softmax-вероятность
  любой маски ≤ 1/8 (`qAtom_le` — 8 масок делят сторону атома), значит
  средний CE ≥ log 8 при любых θ и m (`singleAtomCE_floor`), инфимум ровно
  log 8 (`singleAtomCE_align`: log 8 + log(1+e^{-t}), `singleAtomCE_tight`).
  Против adversary-маски любая параметризация платит ≥ log 16
  (`singleAtomCE_minimax`, `qAtom_worst_le ≤ 1/16`): minimax равен log 16,
  log 8 — пол на маску. Вопреки полу `sign(θ>0)` восстанавливает все 16
  масок (`sign_recover`). Скоуп — только лог-линейная single-atom голова.
- **Композиция Хассе ADD4/SUB4**
  ([`Hagi/Model/Logic/VennHead.lean`](Hagi/Model/Logic/VennHead.lean)):
  двухканальная голова `venn2Head`: sum = XOR (`xorMask`, ранг 2), carry = AND
  (`andMask`, ранг 1), borrow = ¬x∧y (`borrowMask`, ранг 1);
  `venn2_adder_correct` ((2·AND+XOR) % 4 = (x+y) % 4), `venn2_suber_correct`
  (мод-4 вычитание), `venn2_adder_real` (2·carry+sum = x+y). Трёхвходовой
  полный сумматор вне двухпеременной решётки.
- **ANF/Möbius ядро**
  ([`Hagi/Data/AnfTransform.lean`](Hagi/Data/AnfTransform.lean)):
  `anfTransform` (бабочка на `(Fin n → Bool) → Bool`) — инволюция
  (`anf_inversion`); коэффициент = чётность по подкубу (`anf_subcube`,
  `c_S = ⊕_{x ⊆ S} f(x)` в ZMod 2); roundtrip `anf_eval_eq` (все n); якоря
  Fin 2 XOR/AND (`anfFin2_xor/and`, `anfFin2_xor_coeffs`).
- **Композиция compose3** (там же): `anfCompose`
  (f(g(x),h(x))); `anfCompose_coeff`, `anfCompose_eval`; `stencil_guard_sound`
  — S-опорные g,h дают S-опорную композицию для любого f (no-false-coverage
  контекст-абстенции); якорь Fin 2 OR∘(AND,XOR) (`anfFin2_compose`,
  `anfFin2_compose_spot`). Collision abstention и диапазоны здесь не заявлены.
- **Dispatch с collision abstention** (там же): `dispatchOrAbstain` —
  применим ровно один → его значение; ни одного → default; оба → при
  разногласии `Option.none`. `inRange` (точное совпадение множества позиций
  контекста и `AnfCand.argRanges`; чтение-подмножество отвергнуто),
  `dispatch_sound`/`dispatch_sound_default`, `abstain_sound` (коллизия ⇒
  абстенция), `guard_disjoint_no_collision` (непересекающиеся непустые
  диапазоны не коллизуют); якоря `anfFin2_dispatch_abstain/ok`.
  `dispatchPriority` — значение первого применимого по приоритету:
  `dispatchPriority_sound`, `dispatchPriority_shadow` (поздний кандидат не
  определяет результат), `dispatchPriority_agree_sound`; якоря
  `anfFin2_priority_shadow`, `anfFin2_priority_agree`. Обе семантики
  сосуществуют (`dispatch_two_eq_priority`). Списки статические; сквозная
  эквивалентность Python V3 не заявлена.


## 18. Энергетический контур: парная энергия, mean-field свободная энергия и PL

Третий вычислительный контур HAGI (нейро-стек | символьная Венн/ANF-голова |
energy-движок, разрешающий конфликты переменных минимизацией свободной
энергии). Взаимодействие — ordered-pair сумма `Σ_i Σ_{j≠i} K i j (x i) (x j)`,
фактор 1/2 снаружи; симметрия K не предполагается. Одна конвенция в H и F,
поэтому вершинное тождество
([`pairwise_energy_onehot`](Hagi/Energy/PairwiseCategorical.lean)) не требует
диагональной поправки: `F(δ_x) = H(x)` точно при любом β.

Знаковая конвенция: CRAM использует exp(−E/T) (низкая энергия = высокий логит:
`conditionalLogit … = −H(y^{i←a})`); классический Hopfield — exp(β·E) с H = −E.
Мост только через явный sign-адаптер; не утверждается.

- Точная декомпозиция
  ([`meanfield_decomposition`](Hagi/Energy/PairwiseCategorical.lean)):
  `F(p) = E_{∏p_i}[H] + (1/β)ΣΣ p log p` — свободная энергия есть ожидание
  энергии на продукт-маргиналах плюс энтропийная надбавка.
- Псевдоправдоподобие
  ([`pseudolikelihood_eq_conditional_ce`](Hagi/Model/EnergyReasoning/Pseudolikelihood/Core.lean)):
  `J = (1/|ι|)Σ_i −log q_i(y_i)` почленно равна средней условной CE
  `ceDef (Pi.single (y i) 1) (softDef z_i)` на каноническом Prelude-стержне
  — к PL применим инструментарий CEDescent/CEGradient по построению;
  `pseudolikelihood_nonneg` — J ≥ 0.
- Mean-field мост
  ([`meanField_coordinate_update_eq_singleCell`](Hagi/Energy/EnergyCoordinateStep.lean)):
  обновление ровно одной координаты i продукта-веря p меняет полную
  `meanFieldFreeEnergy` ровно на одно-клеточную разность
  `SC(hz, 0, q) − SC(hz, 0, p i)` — чистая линейность, без вероятностных
  посылок. Локальное поле:
  `meanFieldField B K p i a = B i a + (1/2)·Σ_{j≠i} Σ_b (K i j a b + K j i b
  a)·p j b`
  (1/2 снаружи ordered-двойного счёта; при симметричной K — классическое
  `L_i(a)`). Числовой якорь Fin 2 × Bool с асимметричной K: hz true = 6,
  hz false = 3/2, дельта полной энергии = дельте одно-клеточной = 4.5.
- Следствия: `meanField_coordinate_gibbs_nonincreasing` — при β > 0 гиббсовское
  обновление не увеличивает полную энергию (дельта = (1/β)·KL ≥ 0 по
  `coordinate_kl_nonneg`); `meanField_coordinate_strict_drop_of_ne` — при
  `p i ≠ q_i` строгое убывание через `kl_pos_of_ne` (q ≥ 0, p > 0, q ≠ p ⟹
  klDef q p > 0).

Граница: фон заморожен (hz на до-обновлённом p); только одно-координатный шаг;
сходимость не утверждается.

## 19. CRAM-динамика: дискретное ядро и непрерывная функция Ляпунова

### 19.1 Одноклеточное дискретное ядро

[`single_cell_move_energy_delta`](Hagi/Energy/SingleCellDescent.lean): точная
дельта переноса одной клетки. Общая форма (без симметрии K) — разность
симметризованных полей; при симметричной K сворачивается в `L_i(a) − L_i(b)` с
`L_i(a) = B_i(a) + Σ_{j≠i} K_ij(a, y_j)` — все партиционные члены без клетки i
сокращаются точно. Жадность (`greedy_single_cell_nonincreasing`,
`strict_drop_of_positive_margin`) не увеличивает энергию. Три определения —
IsCoordinateMinimum / IsGlobalMinimum / IsValidSolution — не смешиваются
(доказана только импликация global → coordinate; обратные зазоры — witness на
Fin 2 × Bool).

Координатный KL-сертификат
([`coordinate_kl_identity`](Hagi/Energy/EnergyCoordinateStep.lean)): `F_i(p) −
F_i(q_i) = (1/β)·KL(p‖q_i)`, `q_i = softDef(−β·h_i)` — точный монотонный
сертификат мягких координатных обновлений; безопасная дискретная альтернатива
шагам Эйлера.

### 19.2 Непрерывная функция Ляпунова

[`cram_energy_hasDerivAt`](Hagi/Energy/EnergyFlow.lean): алгебраический слой
(softmax-Legendre, градиент logsumexp = p, дисперсионная форма гессиана
`uᵀ(diag p − ppᵀ)u = Σ p u² − (Σ p u)²`, калибровочное направление H1 = 0) и
теорема: при поставленной дифференцируемой кривой v(t), удовлетворяющей CRAM
ODE `u = −(1/τ)(v + localMeanField p)` поточечно, производная энергии равна
`−τβ·Σᵢ Var_{pᵢ}(uᵢ) ≤ 0` (`cram_continuous_energy_nonincreasing`). Имя —
невозрастание, не сходимость; существование ODE-решения и дискретные шаги
Эйлера не покрываются.

### 19.3 Sparse local field

([Hagi/Model/EnergyReasoning/Pseudolikelihood.lean, SparseField]) Соседство
`N : ι → Finset ι`; носитель связи `couplingSupportedOn N K` (j ∉ N i → K i j a
b = 0); `sparseLocalField N B K y i a = B i a + ∑_{j ∈ N i} K i j a (y j)`.

- `sparse_neighbours_subset`: без само-соседств `N i ⊆ univ \ {i}`
  (посылка load-bearing).
- `sparse_localField_eq_dense`: при носителе связи и без само-соседств
  sparse-поле равно плотному `localField`.
- `sparse_update_energy_delta_eq`: при симметричном K дельта одноклеточного
  хода плотной `pairwiseEnergy` равна разности sparse-полей.
- Счёт: `localField_dense_work` / `localField_sparse_work`
  (`card·(card α)²` и `Σ_{j∈N i} card α²`; work-model определения);
  `localField_op_count_le`; `localField_op_count_lt` (строго при собственном
  подмножестве соседей и `0 < card α` — посылка необходима);
  `neighbour_card_le`.
- `sparse_support_of_symmetric`: симметричный K + носитель ⇒ транспонированная
  сторона тоже нулевая.

Якорь: Fin 4, клетка 0 с соседями {1,3}: sparse = dense; работа `2·4 = 8 < 12 =
3·4`. Счёт — ℕ-произведения без O-нотаций; что произвольный K допускает малое N
— не теорема.

### 19.4 Числовая устойчивость: гварды под шумом полей

([Hagi/Model/EnergyReasoning/Pseudolikelihood.lean, NumericalRobustness])

- `guarded_energy_delta_error`: из `|L̂_i(a) − L_i(a)| ≤ ε` следует
  `|Δ̂ − Δ| ≤ 2ε`, где `Δ = E(y^{i←a}) − E(y) = L_i(a) − L_i(y_i)` при
  симметричной K. 2ε точна (две оценки поля); без симметрии дельта есть
  разность симметризованного поля, и посылки только на localField мало.
- `guarded_energy_delta`: `2ε < L̂(y_i) − L̂(a)` ⇒ истинная энергия строго
  убывает. Отвержение информации не несёт (истинная маржа 2, вычисленная 0,
  ε = 1); stall ниже пола 2ε возможен.
- `guarded_greedy_strict_drop`: композиция с
  `strict_drop_of_positive_margin` в two-phase frozen-z постановке (шов
  `localField_visibleBiasWithZ`).
- `latent_update_degree_zero_exact_after_one`,
  `latent_update_degree_zero_one_step_is_fixed`: при пустых окрестностях
  обновление константно и точное за один шаг (случай Δ = 0 не скрыт —
  `latent_iterate_err_bound` требует `0 < Δ`).
- BF16-инстанциация ε: `Hagi.Runtime.BF16Delta.abs_sub_le_of_isNearest_normal`
  даёт ε = 2⁻⁸·max_b |L i b|; гвард принимает при марже > 2⁻⁷·max_b|L i b|.
  Ниже нормального диапазона посылка не заявляется.

### 19.5 Терминация жадного поиска и фокусная политика

([Hagi/Model/EnergyReasoning/Pseudolikelihood.lean, GreedyTermination])

- `greedy_strict_search_terminates`: на конечном пространстве строго
  улучшающаяся траектория имеет длину ≤ `Fintype.card (Set.image H univ)`
  (значения вдоль траектории попарно различны). Бесконечной строго убывающей
  цепи нет; rate/сложность не заявляются.
- `greedy_search_terminal_is_coordinate_minimum`: состояние без строго
  положительной локально-полевой маржи любого хода — координатный минимум.
  Координатный минимум ≠ глобальный ≠ валидное решение (§23).
- Негативный аудит: `focusedDisagreementWeight` (вес ячейки = её несогласие
  `Σ_a max 0 (L_i(y_i) − L_i(a))`) нарушает посылку INVARIANCE §22:
  `concrete_focus_policy_violates_invariance` — на фикстуре Fin 2 × Bool
  после жадного хода ячейки 0 вес ячейки 0 падает 3 → 0. Стационарность
  практического фокусного сэмплера не сертифицирована.

## 20. Латентное энергетическое поле: выпуклость, сжатие и неподвижная точка

Латентная квадратичная энергия Maze-Hard на конечном графе-носителе
([`latent_hessian_diag_dominant`](Hagi/Model/EnergyReasoning/Pseudolikelihood/Core.lean)).

Конвенция: сосед-суммовая форма `E_z = (m/2)·Σz² − (1/2)·Σ_i z_i·(Σ_{j∈N i}
z_j) − z_G`; при симметричной смежности равна реберной. Якорь path-фикстура Fin
4 (m = 3, G = 0): `z* = 21/55`-решётка.

- Диагональное доминирование: `((m−Δ)/2)·Σw² ≤ Q(w)` — через
  `2|w_i||w_j| ≤ w_i²+w_j²`; колонная часть ограничена Δ только через
  симметрию графа. При `m = Δ` форма полуопределена (Fin 2 loop-граф), при
  `m < Δ` принимает отрицательные значения.
- Строгая выпуклость и единственность
  ([`latent_strict_convex`](Hagi/Model/EnergyReasoning/Pseudolikelihood.lean),
  `latent_unique_min`): Bregman-chord тождество
  `Q(λa+(1−λ)b) = λQ(a)+(1−λ)Q(b) − λ(1−λ)Q(a−b)`; неподвижная точка
  обновления ⟺ нулевой градиент (`latent_fixed_iff_grad`).
- ℓ∞-сжатие: обновление `z^{t+1}_i = (Σ_{j∈N i} z^t_j + 1[i=G])/m` —
  сжатие с фактором Δ/m < 1 (`latent_update_contraction`); существование
  минимизатора — Банах (`latent_update_fixed_exists`).
- Геометрическая оценка `‖z^k − z*‖ ≤ (Δ/m)^k·‖z^0 − z*‖`
  (`latent_iterate_err_bound`; реюз
  [`inexact_contraction_bound`](Hagi/Optimization/InexactContraction.lean)
  при ε = 0; `0 < Δ` — явная посылка). Толерансная форма
  `latent_settle_tolerance` задаёт горизонт осаждения ε_z фазы 1.
- Двухфазный протокол `visible_descent_frozen_z`: фаза 1 — осадить z до
  ε_z; фаза 2 — заморозить z в константный bias `visibleBiasWithZ B zc` и
  запустить видимый CRAM-спуск §19.1 дословно. Совместные (z, p)-обновления
  запрещены: z-ход меняет bias посреди спуска, дельта-тождество перестаёт
  ограничивать полное изменение энергии.

### 20.1 Носитель и достижимость неподвижной точки z*

([Hagi/Model/EnergyReasoning/Pseudolikelihood.lean, LatentSupport];
переносчик [LatentEnergy](Hagi/Model/EnergyReasoning/Pseudolikelihood.lean), m
> Δ, симметричная смежность.) Инъекция цели положительна (`1[i = G]`, знак +).

- `latent_fixed_nonneg`: любая неподвижная точка неотрицательна — выводится
  (в аргмин-индексе `m·z i = Σ_{N i} z j + 1[i=G] ≥ card(N i)·z i`).
- `latent_fixed_goal_pos`: `1/m ≤ z* G`; `latent_fixed_ge_of_neighbour`:
  `i ∈ N j ⇒ z* j / m ≤ z* i`.
- `latent_fixed_pos_of_reachable`: `LatentPath N G i k` ⇒
  `(1/m)^(k+1) ≤ z* i > 0`.
- `latent_fixed_upper_bound`: `z* i ≤ 1/(m − Δ)`. Per-distance decay-оценка не
  заявляется (требует структуры графа сверх ограниченности степени).
- `latent_fixed_zero_off_closed`: на C', замкнутом по соседям и без цели,
  `z* = 0` (заплатка снова неподвижная точка; `latent_fixed_unique` возвращает
  её на z*).
- Якоря: `zstar4 = ![21/55, 8/55, 3/55, 1/55]` (Fin 4, m=3, G=0):
  `(1/3)^4 = 1/81 ≤ 1/55`, `21/55 ≤ 1 = 1/(3−2)`; `emptyN2/zstar2` (Fin 2):
  `z* = ![1/3, 0]`, нуль на C' = {1}.

## 21. PL → локально-полевая CE с β и свободными клетками

[`conditionalLogit_eq_neg_localField_add_const`](Hagi/Model/EnergyReasoning/Pseudolikelihood/CRAM.lean):
PL обучает ровно CE на −β·L_i по свободным клеткам.

- Носитель: `CRAMProblem` (allowed / givens / hgiven / hnonempty; поле названо
  givens); `freeCells = {i : givens i = none}`.
- Сокращение: при симметричной K дельта-тождество §19.1 читается как
  константа `−H(y^{i←a}) = −L_i(a) + C_i(y)`, `C_i(y) = L_i(y_i) − H(y)`.
  Якорь Fin 2 × Bool: LF_0(t)=3, LF_0(f)=0, H(t,t)=5, H(f,t)=2.
- Shift-инвариантность: приватные `softDef_add_const` / `ceOneHot_add_const`.
  `conditionalDist_eq_localField_softmax` —
  `softDef(−β·H-варианта) = softDef(−β·L_i)` для любого β;
  `pseudolikelihood_eq_local_CE_beta` — J_PL = среднее по свободным клеткам
  `ceOneHot (y i)(−β·L_i)`.
- Градиент (premise-form + chain rule): `pseudolikelihood_local_field_gradient`
  — при `HasFDerivAt Lmap Lmap' θ` производная локальной CE =
  `Σ_v (q_v − 1[v=t])·(−β·Lmap' h v)` (существующий
  `CEGradient.fderiv_ceOneHot_comp_apply` на (−β)•Lmap);
  `pseudolikelihood_freeCell_B_gradient` — B входит в L_i аффинно, fderiv
  J_PL по B в направлении h =
  `(1/|F|)·Σ_{i∈F}Σ_a (q_i(a) − 1[a=y_i])·(−β·h i a)`.
- Параметризация: `symmetrizeCoupling` `(K̃+K̃ᵀ)/2` удовлетворяет hK
  (`symmetric_parameterization_preserves_hK`).

Граница: K-градиент не утверждается (K входит в L_i через литералы соседей
y_j); сходимости/десцента нет — формула, не сертификат обучения; идентичности
свободных клеток — беспремизная алгебра; hK — реальная посылка.

## 22. Heat-bath ядро Гиббс-поиска: обратимость, стационарность, смешивание

([Hagi/Model/EnergyReasoning/Pseudolikelihood/Core.lean])

### 22.1 Ядро и обратимость

Вес значения a в ячейке i — softmax `heatbathWeight B K T y i a = softDef (fun
c => −L_i(c)/T) a`; ядро `heatbathKernel B K T i y z` равно весу `z i`, если z
отличается от y только в ячейке i, иначе 0. Ядро не зажимает клампы само.

- `heatbath_detailed_balance`: при симметричном K и T ≠ 0 ядро обратимо
  относительно плотности Больцмана `exp(−E(y)/T)` (дельта-тождество §19.1 +
  инвариантность localField вне движимой клетки). Якорь Fin 2 × Bool: вес
  хода в худшее значение `exp(−3)/(1+exp(−3))`.
- `heatbathKernel_rowsum` — строки суммы 1 без посылок;
  `heatbath_stationary` — обратимость + стохастичность ⇒ стационарность
  (`reversible_stationary`). Стационарность ≠ монотонность: при T > 0 вес
  худшего значения строго положителен, ядро может поднять энергию.
- `focused_mixture_stationary`: `Q = Σ_i w(y)_i·Q_i` сохраняет меру при двух
  посылках — SUPPORT (каждое Q_i двигает только свою ячейку) и INVARIANCE
  (`w(y^{i←a})_i = w(y)_i`; зависимость от других ячеек можно).
  Безусловная «state-dependent mixture preserves stationarity» ложна
  (контрпример flip-vs-stay на двух состояниях). Следствие
  `focused_heatbath_mixture_stationary`: для heat-bath family остаются hK,
  T ≠ 0, INVARIANCE, `Σ_i w(y)_i = 1`.
- `focused_mixture_preserves_givens`: веса выбора, обнулённые на данных
  ячейках, ⇒ ненулевой переход смеси сохраняет каждое данное значение.

### 22.2 Doeblin-миноризация и геометрическое смешивание

([Hagi/Model/EnergyReasoning/Pseudolikelihood.lean, HeatBathMixing])
`doeblinMinorized K c := 0 < c ∧ ∀ x y, c ≤ K x y`; `vecMul`/`hbChain` —
pushforward и n-шаговая цепь.

- `tv_pair_contraction`: row-stochastic ядро с entrywise-полом c сжимает
  любую пару равномассовых векторов: `TV(μK, νK) ≤ (1 − |S|·c)·TV(μ, ν)`
  (стационарность не нужна; константа острая; слабые следствия
  `tv_contraction_stationary_sharp`, `tv_contraction_stationary`).
- `heatbathWeight_floor`: при разбросе полей `|L_i(a) − L_i(b)| ≤ M`, T > 0
  каждый вес ≥ `exp(−M/T)/card α`.
- `heatbath_doeblin_floor`: при разбросе полей и носителе (каждая цель —
  одноячеечный ход) ядро миноризовано с `c = exp(−M/T)/card α`;
  `heatbath_doeblin_floor_subsingleton` — носитель-посылка бесплатна при
  `card ι ≤ 1`.
- `stationaryDensity` — нормированная Болцмановская; `heatbath_tv_contraction`:
  `TV(μK, π̂) ≤ (1 − c)·TV(μ, π̂)` (острая — `heatbath_tv_contraction_sharp`).
- `heatbath_mixing`: `TV(μKⁿ, π̂) ≤ (1 − c)ⁿ`; `heatbath_mixing_time`: n ≥
  `log e / log(1 − c)` шагов достаточно для TV ≤ e.

Границы: entrywise-пол для `card ι ≥ 2` без посылки носителя ложен;
ирредуцибильность/апериодичность не заявлены; фокусная смесь вне области
(нарушение INVARIANCE, §19.5); spectral gap / cutoff не заявлены.

## 23. Сертифицированная остановка и разделение валидности

([Hagi/Model/EnergyReasoning/Pseudolikelihood/Core.lean])

- Два сертификата: `EnergyStop` (y, E(y) ≤ τ) — событие эффективности
  (порог — эвристика); `ValidityCertificate` (y, preserves_givens +
  satisfies_constraints) — продакшн-сертификат.
- `stopping_sound_of_separation`: посылка «∀ y', E(y') ≤ τ ⇒ валиден»
  переносит `EnergyStop` в `ValidityCertificate` — вся нагрузка на посылке
  (форма certified-gate, как 2ε-зазоры certified-argmax). Свидетель провала:
  нуль-энергетическая невалидная доска (Fin 2 × Bool).

### 23.1 Разделение для penalty-энергий: раскраска графов

([Hagi/Model/EnergyReasoning/Pseudolikelihood.lean, ValiditySeparation])

- Ядро `energy_threshold_lt_min_penalty_implies_valid`: если энергия —
  конечная сумма неотрицательных штрафов, каждый ненулевой ≥ pmin > 0, а
  нулевые дают валидность, то `энергия < pmin ⇒ валидность`. Судоку/n-ферзей
  покрываются абстрактно в premise-form.
- Реализация: `coloringCoupling` — `K_ij(a,b) = 1[(i,j) ∈ edges ∧ a = b]`;
  энергия конфликтов есть `pairwiseEnergy` с этим K; `coloringField` — унарный
  штраф нарушения прецветки (givens).
- `graph_coloring_zero_energy_iff_valid`: нулевая энергия (B = 0) ⇔
  правильная раскраска (hnodiag: без диагональных рёбер).
- `graph_coloring_separation`: энергия ≤ τ < 1 ⇒ givens сохранены (pmin = 1)
  и раскраска правильная (каждое нарушенное ребро даёт оба упорядоченных
  индикатора — ровно 1; family-optimal порог). `graph_coloring_stop_sep_valid`:
  `EnergyStop` при τ < 1 производит `ValidityCertificate` через
  `stopping_sound_of_separation` с доказанной посылкой;
  `graph_coloring_stop_proper` — бинарный спутник (унарный слот C
  сертификата не выражает рёберные ограничения).

Выученные энергии такой сепарации не имеют; приём вывода learned-сэмплера
только через независимый валидатор (маршрут `CRAMAcceptedSolution`). τ < 1
требует симметрии hsym множества рёбер. Фикстура Fin 3 (треугольник): 3 цвета —
энергия 0, 2 — нет, монохром — энергия ≠ 0.

## 24. Типизированные CRAM-переходы в каноническое Cert-ядро

([CramContracts](Hagi/Model/EnergyReasoning/Pseudolikelihood.lean)) —
premise-form контракты над `CRAMState` с точными ресурсными законами (budget' =
budget − cost, неотрицательный остаток).

- Полярность: `MetricDirection` (UtilityFloor | LossCeiling) с kept /
  improves; `MetricDirection.kept_lossCeiling_neg` — потолок потерь c ⇔ пол
  полезности −c для NEGATированной цели; kept_floor_forwards безусловен,
  kept_floor_iff требует `Nonempty TaskId`.
- Носитель `CRAMState`: problem, board, latent Option, searchBudget ℕ,
  computeBudget ℝ, riskRem, deltaRem; компонентная ext_iff.
- Обучение `CRAMTrainStep`: measured-drop на цели freeCellPseudolikelihood
  (`J(newB) ≤ J(oldB) − drop`, drop ≥ 0; градиентного доказательства нет) +
  ресурсные законы; majorizer-вход measured_of_majorizer.
- Энергодесцент `CRAMEnergyDescentStep`: строго положительная локально-полевая
  маржа (margin_pos), strictDrop переиспользует
  `strict_drop_of_positive_margin`; маржа списывается из riskRem;
  toLossCeilingDrop.
- Эксплорация `CRAMExplorationStep`: легальный переход (положительная масса
  ядра), row-stochastic премиза, клампы сохранены, поиск потребляется
  строго. Десцент не утверждается.
- Продукция `CRAMAcceptedSolution`: `ValidityCertificate` согласован с доской;
  энерго-граница опциональна.
- Мост в ядро `CRAMEnergyDescentStep.toKernelCertStep`: при явных премизах
  чтения метрик (objective = энергия доски, budget = computeBudget, risk =
  riskRem) десцент-шаг есть канонический `Hagi.Cert.CertStep`; телескоп §11.1
  применим к CRAM-траекториям. Hold — полное равенство состояния
  (cram_state_components фиксирует все 7 компонент).

## 25. Attention-связь латента с видимым полем

([AttentionCoupling](Hagi/Model/EnergyReasoning/Pseudolikelihood.lean)) Связь
latent→visible через внимание (аддитивный маршрут `visibleBiasWithZ` — §20, оба
существуют).

- `L_ij(a,b) = κ_ij·w_ij·f(a,b) + κ_ji·w_ji·f(b,a)`, где w =
  `attentionWeights s` — softmax-веса `α_ij = exp(s_ij)/Σ_k exp(s_ik)` при
  замороженном z в скорах s (дифференцируемость по z не заявляется);
  неотрицательность, ≤ 1, сумма по строке = 1 при `[Nonempty ι]`.
- Симметрия по построению `attention_coupling_symmetric`: `L_ij(a,b) =
  L_ji(b,a)`
  без посылки симметрии на κ или w (приём «верхнего треугольника»: оба
  направленных ребра в каждом L_ij). Якорь Fin 3 с намеренно асимметричным κ
  (`κa3 i j = (i+2j)/4+1`).
- `attention_coupling_bounded`: `0 ≤ κ ≤ κmax`, `w ∈ [0,1]`, `|f| ≤ fmax` ⇒
  `|L_ij(a,b)| ≤ 2·κmax·fmax`; константа 2 точная.
- Подключение: `attentionK` — ядро K(z) при замороженном z;
  `attention_K_symmetric` — hK-посылка §19.1 дословно;
  `frozen_z_field_with_attention` — локальное поле для K(z) определено, и ход
  в минимизатор локального поля не увеличивает `pairwiseEnergy B (attentionK κ
  (attentionWeights s) f`.
  Совместной (z,y)-теоремы нет.
- `attention_coupling_field_diff`: `|w1 − w2| ≤ δ` ⇒ возмущение локального
  поля ≤ `|S_i|·2κmax·fmax·δ` (S_i = univ \ {i}).
- `latent_error_couples_field` (premise-form): `‖z − z*‖ ≤ η` + softmax-Липшиц
  `|w(z) − w(z*)| ≤ L_sm·η` ⇒ поле K(z) внутри `|S_i|·2κmax·fmax·L_sm·η` от
  поля K(z*). Лемма Липшица для этого носителя не заявляется.
- `latent_attention_guarded_drop`: при `ε := |S_i|·2κmax·fmax·L_sm·η`
  вычисленная маржа `2ε < L̂(y_i) − L̂(a)` на полях K(z) ⇒ строгий спуск
  истинной энергии `pairwiseEnergy B (attentionK κ w2 f)` — рецепт 2ε-гварда
  §19.4.

Полная семантика Maze-Hard (носитель z*, достижимость, совместные
(z,y)-обновления) остаётся открытой.

## 26. Чередующиеся (z,y)-раунды

([Hagi/Model/EnergyReasoning/Pseudolikelihood.lean])

Joint latent-visible спуск — чередующиеся раунды z-фаза → y-фаза с потолками на
раунд. Альтернативы отклонены: small-gain деградирует в неравенство слэка
(z* не зависит от y, движущейся латентной цели нет); Lyapunov
`E_vis + c·‖z−z*‖²` требует запрещённой дифференцируемости по z.

- `alternating_round_nonincreasing`: премиза z-фазы
  (`hsoft : |w(z_t) − w(z*)| ≤ L_sm·η`, η — потолок оседания
  `latent_settle_tolerance`) + числовая ошибка полей ε (§19.4) + составной
  гвард `2·(ε + |S_i|·2κmax·fmax·L_sm·η) < вычисленная маржа` ⇒ строгий спуск
  видимой энергии на истинном ядре замороженного z*:
  `pairwiseEnergy B (attentionK κ w2 f)`. Композиция `guarded_energy_delta` с
  `latent_error_couples_field`.
- `alternating_zphase_one_step_error`: `‖latentUpdate z − z*‖ ≤ (Δ/m)·‖z −
  z*‖`;
  потолки раундов `η_t ≤ q·η_{t−1}`. Суммируемость η_t сама не доказывается.
- `alternating_round_slack_summable`: слэк с геометрическим затуханием
  (посылка `slack (t+1) ≤ (Δ/m)·slack t`) имеет все частичные суммы ≤
  `slack 0 · m/(m−Δ)`. Затухание — гипотеза.
- `alternating_trajectory_bound`: `E (y N) ≤ E (y 0) − Σ_{t<N} d t`;
  `alternating_trajectory_descent_budget`: при `Emin ≤ E (y t)` суммарный
  спад ≤ `E (y 0) − Emin` (пол — гипотеза).
- `alternating_rounds_converge`: на конечном пространстве строго убывающие
  раунды терминистируют (длина ≤ мощности образа энергии; аргумент
  ранжирования §19.5). Только конечная/строгая версия: аналитическая
  сходимость остаётся открытой.

Якоря: частичная сумма `(1/2)^t ≤ 2`; телескоп `10−t`: финал `7 ≤ 10−3`. Всё —
premise-form: неточность z-фазы и числовая ошибка — гипотезы; безусловной
совместной (z,y)-теоремы нет. Числовой якорь Fin 2/Bool — энергия `0 → −2`
через теорему раунда.

## 27. Каноны Theory

Семейные теории живут в канон-модулях: одно понятие описано ровно один раз,
исторические пространства имён сохранены внутри одного файла. Отдельные файлы —
либо теорема-мост, либо bench-носитель.

| Канон-модуль | Семейство (что доказывает) |
| --- | --- |
| [`Hagi/Theory/Continual.lean`](Hagi/Theory/Continual.lean) | GPM continual: exact zero forgetting, multi-task accumulation, rank-trunc/A-GEM trade-off, hybrid selection. |
| [`Hagi/Theory/Statistics.lean`](Hagi/Theory/Statistics.lean) | Holdout/anytime: honest finite-population holdout, anytime e-process (Catoni×Ville), two-domain transport, without-replacement kernel. |
| [`Hagi/Theory/SelfEdit.lean`](Hagi/Theory/SelfEdit.lean) | Adopt-gate (strict monotone + finiteness ⇒ termination) и momentum-knob над тем же гейтом. |
| [`Hagi/Theory/Compression.lean`](Hagi/Theory/Compression.lean) | EF-телескоп, EF21 in-step quantized loop, certified ternary jump. |
| [`Hagi/Theory/MergeQuant.lean`](Hagi/Theory/MergeQuant.lean) | Fisher-квантование (water-filling, anisotropy) + измеряемый merge-гейт. |
| [`Hagi/Theory/Softmax.lean`](Hagi/Theory/Softmax.lean) | Рациональный exp-сэндвич, certified softmax/CE, monotonicity + certified prediction, band tightening. |
| [`Hagi/Theory/SafeStep.lean`](Hagi/Theory/SafeStep.lean) | Центральный стохастический safe step с Freedman-радиусом: accept/refuse-дихотомия. |
| [`Hagi/Theory/MasterTheorem.lean`](Hagi/Theory/MasterTheorem.lean) | Сборная траекторная теорема certified-or-refuse + бюджет/whp-каналы. |
| [`Hagi/Theory/FullPipeline.lean`](Hagi/Theory/FullPipeline.lean) | Единый шестифазный certified-цикл на одной цели. |
| [`Hagi/Theory/BlockLipschitz.lean`](Hagi/Theory/BlockLipschitz.lean) | Выведенные lip/causal константы реальных атомов (RMSNorm, MLP, attention). |

Statement-канон результатов с карточками (оптимальный шаг γ* = 1/L,
иерархические окна, reading floor, growth gate) —
[docs/PALOMAR-CARDS.md](docs/PALOMAR-CARDS.md), карточки 9–14; Lean-носители —
[`CoverageReading`](Hagi/Theory/CoverageReading.lean),
[`growthGate`](Hagi/Theory/NegativeTransfer.lean) (namespace
`Hagi.Theory.GrowthGate`).

Отдельные мосты: [`MasterEF`](Hagi/Theory/MasterEF.lean) (endpoint-only
EF-штраф), [`CEChain`](Hagi/Theory/CEChain.lean) (унифицированная CE-цепочка),
[`BlockAdmission`](Hagi/Theory/BlockAdmission.lean) /
[`FunctionPreservingGrowth`](Hagi/Theory/FunctionPreservingGrowth.lean) /
[`GrowTrunkBlock`](Hagi/Theory/GrowTrunkBlock.lean) /
[`ProvenTrunk`](Hagi/Theory/ProvenTrunk.lean) (рост ствола),
[`HadamardIncoherence`](Hagi/Theory/HadamardIncoherence.lean),
[`AdaptiveMajorizer`](Hagi/Theory/AdaptiveMajorizer.lean),
[`AnytimeHoldoutStop`](Hagi/Theory/AnytimeHoldoutStop.lean),
[`CertifyThenCommit`](Hagi/Theory/CertifyThenCommit.lean),
[`OnlinePL`](Hagi/Theory/OnlinePL.lean),
[`MDLPrune`](Hagi/Theory/MDLPrune.lean),
[`FlowMatching`](Hagi/Theory/FlowMatching.lean),
[`Interpretability`](Hagi/Theory/Interpretability.lean),
[`GaugeQuotient`](Hagi/Theory/GaugeQuotient.lean),
[`LogitGrowth`](Hagi/Theory/LogitGrowth.lean). Bench-мосты:
[`CertCEHoldout`](Hagi/Theory/CertCEHoldout.lean),
[`CertSandwichBench`](Hagi/Theory/CertSandwichBench.lean),
[`MiniHagi`](Hagi/Theory/MiniHagi.lean),
[`MiniHagi2`](Hagi/Theory/MiniHagi2.lean),
[`TrainerBenchmark`](Hagi/Theory/TrainerBenchmark.lean).

### 27a. Мосты HAGI_v2 и bench-режимы

| Мост | Суть (одно описание — ровно один раз) |
| --- | --- |
| [`GrowSnap`](Hagi/Theory/GrowSnap.lean) | snap-политика grow: сброс знаменателей на границе уровня. |
| [`RollbackGate`](Hagi/Theory/RollbackGate.lean) | exact pre-step rollback: no-commit probe на копии. |
| [`WeightDecayLeak`](Hagi/Theory/WeightDecayLeak.lean) | projected decay сохраняет GPM-память точно, naive — строгая утечка теоремой. |
| [`EmpiricalBernstein`](Hagi/Probability/EmpiricalBernstein.lean) | EB-радиус: σ̂-подстановка + аддитивный член поверх Freedman. |
| [`OEComplete`](Hagi/Theory/OEComplete.lean) | OE-дедупликация поиска не теряет решение (полнота относительно проб). |
| [`ExactBypass`](Hagi/Theory/ExactBypass.lean) | p = 1 ⇒ CE-вклад покрытия 0 ровно; гейт отвергает p = 0. |
| [`MiniHagiLoop`](Hagi/Theory/MiniHagiLoop.lean) | full_loop_sound — композиционная обёртка certified-цикла; итеративная версия — только coverage-монотонность. |
| [`AdapterGrowth`](Hagi/Theory/AdapterGrowth.lean) | механика роста адаптеров (snap-цикл, rank-adaptive, SVD-merge, self-compress, distill); карта секций — module docstring. |
| [`AdapterBank`](Hagi/Theory/AdapterBank.lean) | изоляция слотов банка точно; warm-transfer = копия + forgetA=0. |
| [`NegativeTransfer`](Hagi/Theory/NegativeTransfer.lean) | точная iff-граница warm хуже cold (квадратичный мир); бюджет не размывает. |
| [`Softmax` (Softmax.lean)](Hagi/Theory/Softmax.lean) | суммарная p̂-анти-монотонность: держится ровно при фиксированном числителе одной банки; контрпример-теорема при смешении. |
| [`TritCodec`](Hagi/Theory/TritCodec.lean) | биекция 5 тритов ↔ байт (3^5 = 243 ≤ 2^8), roundtrip + инъективность. |
| [`MasterTheoremV3`](Hagi/Theory/MasterTheoremV3.lean) | лестница v3 → v3.5 одним файлом: конъюнкция делегатов; v3.5 = + контракт `OptimizerPremises` и оптимизаторный блок. |
| [`AutoTransferGate`](Hagi/Theory/AutoTransferGate.lean) | probe-A/B гейт warm/cold = точная граница NegativeTransfer в H-метрике. |
| [`FactLedger`](Hagi/Theory/FactLedger.lean) | append-only факт-леджер: preserves + monotone; dedup опущен. |
| [`RangeWrap`](Hagi/Theory/RangeWrap.lean) | замкнутость mod-wrap в [lo, lo+m) (Int.emod). |
| [`AdaptiveContext`](Hagi/Theory/AdaptiveContext.lean) | self-CE elbow: наименьший W с CE ≤ best·(1+tol). |
| [`KnowledgeConsolidation`](Hagi/Theory/KnowledgeConsolidation.lean) | remember/consolidate: append-only память, graceful degradation. |

Канон bench-паттерна (режимы `scripts/bench_bridge.py`, единый скелет:
append-блок + choice + dispatch, certified snap-GD с drop>0 COMMIT / HOLD,
forgetA=0 bit-exact asserts, drift-детект на замороженной копии корпуса,
EB-телеметрия, негативы wrong-const/HOLD, witness-lean, аксиомы только
propext/Quot.sound/Classical.choice): mini-hagi-loop, mini-hagi-loop2,
universal-loop, universal-loop-nl, self-compress-loop, distill, mini-hagi-v3,
adapter-transfer, adapter-transfer-auto, band-check, adapter-snap-grow,
adapter-rank-adaptive, adapter-merge. Измеренные вердикты и witness-пути —
карточки STATUS.md.

