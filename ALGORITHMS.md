# Алгоритмы архитектуры и обучения

Цель — конечный, проверяемый по шагам рецепт: качество на заданных данных,
явная цена представления и ресурсные ограничения. Это не универсальный
рецепт оптимальной сети. Различаем три уровня: операция над моделью,
конечный математический сертификат, измеряемая посылка внешнего цикла.
Стоимость ниже всегда относится к указанной модели, а не к железу.

## 1. Архитектура: общее ядро и маршрутизируемые остатки

Исходные объекты — конечное непустое семейство экспертов Wᵢ, общее ядро
`C` и остатки Rᵢ. Сначала требуем точной декомпозиции `W = C + R`;
тогда вызов [`factorizedEval`](Hagi/Architecture/FactorizedMerge.lean)
возвращает исходного эксперта по [`routed_eval_exact`](Hagi/Architecture/FactorizedMerge.lean).
Храним один `C` и отдельные малые остатки, а не копию всей сети на route.

Для усредненного [`fullMerge`](Hagi/Architecture/FactorizedMerge.lean)
имеем `fullMerge W = C + meanResidual R`. Если остатки приближены с ошибкой
`δ_i`, то ошибка merge не превосходит среднего `δ_i`; см.
[`factorized_error_bound`](Hagi/Architecture/FactorizedMerge.lean).
Не отождествляем усреднение параметров со средним логитов.

Для logits zₐ при `N > 0` отдельно используем
[`ensemble_ce_le_mean_general`](Hagi/Core/Concat.lean):

```
CE(t, v ↦ (∑a z_a(v))/N) ≤ (∑a CE(t,z_a))/N.
```

Это только pointwise CE-мажоранта среднего логита. Для смеси матриц при
фиксированном router применяем [`merged_output_exact`](Hagi/Ensemble/MergeMixture.lean);
при смене `w` на `w'` добавляем явный drift-budget из
[`routing_drift_bound`](Hagi/Ensemble/MergeMixture.lean).

Перед spectral/rank/ternary сжатием суммируем не «экономию качества», а сумму
ошибок из [`unified_error_budget`](Hagi/Architecture/FactorizedMerge.lean):

```
‖W-S‖ ≤ e_shared + e_spectral + e_rank + e_quant + e_routing.
```

Если `0<R̄≤logitRange f`, берём `τ=logitRange f/R̄`:
[`variance_gate_normalize`](Hagi/Runtime/ControllerGates.lean)
даёт `logitRange(f/τ)=R̄`, а [`variance_gate_contract`](Hagi/Runtime/ControllerGates.lean)
контрактует `R²/8`. Это масштабирование logits-контракта, а не доказанное
снижение CE или доказанная температура физического router.

Выбираем форму по конкретным счётным условиям:

- shared core + residuals: если `2 ≤ N` и
  `N(r(V+d)) ≤ (N-1)(Vd)`, [`factorized_budget`](Hagi/Architecture/FactorizedMerge.lean)
  даёт `Vd + N(r(V+d)) ≤ N(Vd)`;
- block-diagonal + rank-`r` mixer: если `h > 0`, `2 ≤ N` и
  `3r < (N-1)h`, то структурированное представление меньше dense по
  [`block_lowrank_lt_dense_iff`](Hagi/Budget/JointCost.lean);
- если активна одна конфигурация и `2 ≤ N`, `c+r ≤ d`, счётная модель multiply-add
  имеет счёт `(c+r)d`; [`active_beats_dense_family`](Hagi/Budget/ActiveCompute.lean)
  сравнивает её с `N d²`. Это declared operation count, не wall-clock.

Точность всех пяти error terms проверяем на модели; из неравенств параметров
не следует равенство качества или ускорение обучения.

## 2. Предиктор и loss: конечная log-linear one-hot CE

Берём непустой конечный vocabulary `V`, размерность `d`, матрицу
`X : Matrix V (Fin d) ℝ` и `θ : EuclideanSpace ℝ (Fin d)`.
По [`ceLogits`](Hagi/Model/CEDescent.lean) и
[`ceOneHot`](Hagi/Core/Concat.lean):

```
z(v) = ceLogits X θ v = (X *ᵥ θ.ofLp)(v),
lse z = Real.log (∑v exp(z(v))),
ℓ_t(θ) = ceOneHot t z = lse z - z(t).
```

Остаток и raw gradient задаются [`ceResidual`](Hagi/Model/CEDescent.lean)
и [`residualTranspose`](Hagi/Model/CEDescent.lean):

```
r(v) = softmax(z)(v) - (if v=t then 1 else 0),
g_j = residualTranspose X θ t j = ∑v r(v) X(v,j).
```

[`fderiv_ceOneHot_mulVec`](Hagi/Model/CEGradient.lean)
доказывает directional Fréchet form именно этой log-linear CE. Это не
лицензия подставлять тот же gradient в неуточненную нелинейную сеть:
для другого logit map используется его настоящий Jacobian или другая модель.

Loss выбирается на supplied finite examples; held-out качества из этой
формулы не следует. При усреднении параметров midpoint-CE снова оценивается
только pointwise, как в [`ceOneHot_mean_ceLogits_le`](Hagi/Model/CEHeldout.lean).

Для `[Fintype V]`, `[Nonempty V]` и явного `[DecidableEq V]` имеем
`p = Pi.single t 1`, `q = Hagi.Prelude.softDef z`.
Связь с канонической информационной семантикой точная:
[`ceOneHot_eq_ceDef_pi_single`](Hagi/Core/Concat.lean),
[`ceOneHot_eq_klDef_pi_single`](Hagi/Core/Concat.lean):

```
ceOneHot t z = Hagi.Prelude.ceDef p q = Hagi.Prelude.klDef p q.
```

Масса one-hot равна единице; softmax строго положителен и нормирован.
[`KLSupported_pi_single_softDef`](Hagi/Core/Concat.lean) доказывает условие
поддержки `q v ≠ 0 ∨ p v = 0`: нули one-hot вне цели допускаются.
Поэтому к этому случаю применимы существующие результаты о неотрицательности
KL. Это точечное соответствие для one-hot, а не утверждение о произвольной
дистилляции, оптимальности обучения, вычислениях или held-out качестве.

## 3. Направление и сертифицированный размер шага

### 3.1 Базовый одношаговый safe CE update

Для одного примера кладём направление `D = ceDirection X θ t = -g`
и обозначения:

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

При `R>0` выбранный шаг минимизирует этот quadratic majorizer и
[`ceOneHot_safeStep_le_residual`](Hagi/Model/CEDescent.lean)
даёт `CE(θ') ≤ CE(θ) - 2A²/R²`; строгость —
[`ceOneHot_safeStep_lt`](Hagi/Model/CEDescent.lean). При `R=0`
центральная ветка равна нулю и сохраняет logits. Глобального минимизатора CE
или сходимости параметров этот шаг не объявляет.

### 3.2 Общее направление для arithmetic-mean batch

На `X : Fin B → Matrix V (Fin d) ℝ`, `y : Fin B → V`
не усредняем отдельные `safeStepSize`. Вычисляем один вектор:

```
ḡ_j = meanResidualTranspose X θ y j = (∑b g_b,j)/B,
D̄ = batchMeanDirection X θ y = -ḡ,
Ā = batchAlignment X θ y = ∑j ḡ_j²,
Q̄ = batchRangeSquare X θ y = (∑b (dirRange X_b D̄)²)/B,
eta_b = batchSafeStep X θ y = if Q̄=0 then 0 else 4Ā/Q̄,
θ' = batchNextParameters X θ y = θ + eta_b • D̄.
```

[`batchLoss_alongNext_le_batchMajorizer`](Hagi/Model/BatchCEDescent.lean)
даёт общий majorizer `L(θ) - eta Ā + eta² Q̄/8`.
При `Q̄>0` [`batchLoss_safeStep_le_residual`](Hagi/Model/BatchCEDescent.lean)
даёт `L(θ') ≤ L(θ) - 2Ā²/Q̄`, а [`batchLoss_safeStep_lt`](Hagi/Model/BatchCEDescent.lean)
— strict mean-CE descent. Смешанные противоположные градиенты могут дать
`D̄=0`; тогда корректен hold, а не шаг по одному target.

Для supplied `D` дополнительно требуем непустой batch и
`dirAction X_b θ y_b D < 0` для каждого `b`; лишь тогда
[`batchDirectionSafeEta`](Hagi/Model/BatchCEDescent.lean)
положителен. [`batchDirectionNextParameters`](Hagi/Model/BatchCEDescent.lean)
иначе оставляет параметры без изменения. Локальный margin каждого примера
фиксируется [`ceOneHot_batchDirectionNextParameters_le_margin`](Hagi/Model/BatchCEDescent.lean).

Для фиксированных `X,y` и фактической guarded-траектории
`θ_t = coreParameters (fixedBatchState X y S opCost opRisk write t)`
при непустом `V` имеется конечный запас squared mean residuals.
С `K = rangeCurvature X`, [`batchRangeSquare_le_rangeCurvature_mul_alignment`](Hagi/Contracts/BatchCEAlignmentBudget.lean)
даёт `Q̄_t ≤ K·Ā_t`. Отсюда
[`fixedBatch_sum_alignment_le_initial`](Hagi/Contracts/BatchCEAlignmentBudget.lean)
ограничивает каждую конечную сумму, а
[`fixedBatch_alignment_summable`](Hagi/Contracts/BatchCEAlignmentBudget.lean) и
[`fixedBatch_tsum_alignment_le_initial`](Hagi/Contracts/BatchCEAlignmentBudget.lean) —
суммируемость и полный запас:

```
∑t, Ā_t ≤ ((K + 1) / 2) * batchCEObjective X y S.
```

Важно не ограничиваться средним за префикс или minimizer-observer.
[`fixedBatch_meanGradient_tendsto_zero`](Hagi/Contracts/BatchCEAlignmentBudget.lean)
доказывает, что `WithLp.toLp 2 (meanResidualTranspose X θ_t y)` стремится к нулю
на последнем итерате; [`fixedBatch_meanDirection_tendsto_zero`](Hagi/Contracts/BatchCEAlignmentBudget.lean)
даёт тот же предел для `batchMeanDirection X θ_t y = -ḡ_t`.
Эти последние две теоремы допускают пустой batch, помещая непустоту
`V` только в ветку `B+1`, где она следует из `y 0`; скрытого witness
при `B=0` нет. Условия для конечного запаса и среднего Чезаро
[`fixedAlignmentCesaro_le`](Hagi/Contracts/BatchCEAlignmentBudget.lean) сохраняются:
это отдельная мажоранта при непустом `V`, не rate для отдельного `Ā_t`.

Это доказанный предел только общего среднего градиента и направления
на фиксированном batch. Отдельные residual gradients при смешанных
целях могут оставаться ненулевыми; сходимость параметров,
индивидуальных логитов, CE к оптимуму или held-out качества не утверждается.

### 3.3 Min-norm/MGDA и SafeQP

Если нужен per-sample guard, альтернатива — минимальная по норме точка
convex hull raw gradients. [`batchGradientMinimizer`](Hagi/Model/BatchCEDescent.lean)
корректен математически, но содержит Classical.choose: это не native solver.
Для двух gradientов есть явный [`segmentMinNorm`](Hagi/Step/ProjectionDescent.lean):
при `u=g1-g0≠0`, `τ=min 1 (max 0 (-⟪g0,u⟫/‖u‖²))`,
`ω=g0+τu`; [`segmentMinNorm_norm_le`](Hagi/Step/ProjectionDescent.lean)
подтверждает минимальность. [`batchGradientMinimizer_pair`](Hagi/Model/BatchCEDescent.lean)
связывает её с общим случаем.

На real inner-product пространстве `X` с `[FiniteDimensional ℝ X]` и конечном
индексе nonempty `K` общий SafeQP выбирает ближайшую к `g0` точку из
`{d | ∀i, ⟪g_i,d⟫ ≥ -eps_i}` при `eps_i≥0`;
существование и единственность — [`safeQP_exists_unique`](Hagi/Step/SafeQP.lean),
alignment — [`safeQP_descent`](Hagi/Step/ProjectionDescent.lean).
Опять, существование проекции не называется исполняемым QP.

Для заданной quadratic-модели изменений требуем
`∀i, dL_i ≤ -eta*⟪g_i,d⟫ + L_i*eta^2*‖d‖²/2` и ограничиваем шаг
[`safeqpEtaMax`](Hagi/Step/SafeQPStep.lean):

```
eta ≤ min 1 (⨅i 2(eps_i+⟪g_i,d⟫)/(L_i‖d‖²)),
```

при `d≠0`, `L_i>0`, `eps_i≥0` и `0≤eta`. Тогда
[`safeqp_eta_max`](Hagi/Step/SafeQPStep.lean) даёт `dL_i≤eps_i`.
Если имеется только норма шага, при `0<R≤‖x‖` используем точную проекцию
`(R/‖x‖)•x` на ball из [`trust_region_nearest`](Hagi/Runtime/ControllerGates.lean),
но не объявляем её заменой всех ограничений QP.

### 3.4 Конечная log-linear CE и joint potential

Для состояния `S` на `EuclideanSpace ℝ (Fin d)`, конечного непустого `V`,
матрицы `X : Matrix V (Fin d) ℝ` и цели `t` положим

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

В частности, hCEnew — явная идентификация measured post-energy, а не
автоматическое следствие операции joint. Заключение для потенциала Φ:

```
Φ(joint S) - Φ S ≤ -gainJoint S + riskJoint S.
```

Из hstep получается фактическое обновление параметров:

```
(joint S).params = S.params - S.sp.eta • S.stepDir
  = ceNextParameters X S.params t S.sp.eta.
```

Вместе с hgrad это даёт
`⟪S.grad,S.stepDir⟫ = ‖S.stepDir‖² = ceAlignment X S.params t`.
Одношаговая CE-мажоранта и singleton range bound дают

```
CE(next) ≤ CE(old) - eta*ceAlignment + (eta*R)²/8,
R² ≤ 4*A²*‖D‖²,
(eta*R)²/8 ≤ A²*eta²*‖D‖²/2.
```

Так hLdef выбирает допустимую, но вообще говоря грубую кривизну `A²`,
а существующая [`potential_joint`](Hagi/System/GrowthState.lean) завершает
вывод. Деления на направление нет и посылки `D≠0` не требуется.
Это не утверждение о глобальной или оптимальной smoothness/curvature,
не новый результат о fderiv, PL или сходимости.

Для identity witness с `X=I₂`, `t=0`, нулевыми параметрами, `eta=1/4`,
`A=2`, `L=4` имеем

```
D = [+1/2,-1/2],       stepDir = grad = [-1/2,+1/2],
‖D‖² = 1/2,            R = 2,
4A²‖D‖² = 8,           new joint logits = [+1/8,-1/8],
gainJoint = eta*‖stepDir‖²/2 = 1/16.
```

Здесь старые logits равны `[0,0]`; после шага other-minus-target gap
равен `-1/4`, а target-minus-other gap равен `+1/4`. Поэтому
old CE = `softplus(0)`, new CE = `softplus(-1/4)`, и фактическое
уменьшение CE равно `softplus(0)-softplus(-1/4) ≥ 1/16`.
При `riskJoint=0` фактическое уменьшение потенциала также не меньше
`1/16`; ни одно из этих уменьшений не объявляется равным `1/16`.
Отдельный [`safeStepSize`](Hagi/Model/CEDescent.lean) здесь был бы `1/2`,
но это другая формула, не удовлетворяющая окну `eta≤1/L=1/4`.

При повторяющихся строках возможен `D=0` даже при тех же `A=2`, `L=4`,
`eta=1/4`; тогда gain равен нулю. При нулевом риске заключение даёт лишь
невозрастание потенциала. Universal strict progress, сходимость,
generalization, held-out качество и выигрыш времени/FLOPs не утверждаются.

### 3.5 Identity features: предел средней вероятности

Для `X : Fin B → Matrix (Fin n) (Fin n) ℝ`, `y : Fin B → Fin n`, `0 < B`
и условия `hX : ∀ b, X b = 1` возьмём прежнюю фактическую траекторию
`θ_t = coreParameters (fixedBatchState X y S opCost opRisk write t)`.
Непосредственно применяется
[`Hagi.Contracts.BatchCEAlignmentBudget.fixedBatch_meanGradient_tendsto_zero`](Hagi/Contracts/BatchCEAlignmentBudget.lean),
без добавления посылки предела.

`meanPrediction X θ` усредняет именно вероятности
`softDef (ceLogits (X b) θ)`, а не параметры или logits.
`empiricalTarget y` — такое же среднее `(Pi.single (y b) 1 : Fin n → ℝ)`.
Private helper доказывает строго с этим знаком:

```
meanPrediction X θ v − empiricalTarget y v = meanResidualTranspose X θ y v.
```

Identity multiplication и `B ≠ 0` из `0 < B` доказывают равенство
в каждой координате. Определения средних totalized и при `B=0`, но
вероятностная интерпретация и публичные limit theorems требуют `0 < B`.

Следствие
[`Hagi.Contracts.IdentityMomentConvergence.fixedBatch_meanPrediction_tendsto_empiricalTarget`](Hagi/Contracts/IdentityMomentConvergence.lean):
`meanPrediction X θ_t → empiricalTarget y` в finite-product topology.
Непрерывность координатной оценки на PiLp переносит предельный нуль C205
на разность, после чего добавляется постоянная empirical-координата.

Для `B=1` отдельная теорема
`fixedBatch_meanPrediction_tendsto_empiricalTarget_batch_one` даёт
`softDef (ceLogits (X 0) θ_t) → Pi.single (y 0) 1`.
Это утверждение только о предсказании для единственного supplied примера,
а не о правильности каждого individual prediction в смешанном batch.

Counterexample: два identity features и смешанные метки `[0,1]` при нулевых
параметрах уже дают одинаковые mean prediction и empirical target
`(1/2,1/2)` и нулевой mean residual, но оба individual `ceDirection`
ненулевые. `mixed_batchLoss_before_eq_log_two` даёт CE=`log 2`.
Следовательно, marginal matching не означает нулевую CE или правильность
individual predictions. Произвольные affine/full-rank features, сходимость
параметров, held-out качество и вычислительная оптимальность не доказаны.

### 3.6 Guarded Pareto CE: адаптер к StepContract

Для конечного типа `V` положим
`T = budgetedParetoBatchTrainStep X y S opCost opRisk write` и передадим
только условие `0≤opRisk`. Адаптер
[`budgetedParetoStepContract`](Hagi/Contracts/BudgetedParetoStepContract.lean)
возвращает обычный [`StepContract`](Hagi/Unified/StepContract.lean), где

```
decrease    = batchCEObjective X y S - batchCEObjective X y T,
riskCost    = T.saf.risk - S.saf.risk,
budgetSpend = S.res.budget - T.res.budget.
```

Это фактическая CE как функция параметров и данных, а не норма параметров,
saved effects или телеметрия. Структура требует именно nonnegative
`StepContract.decrease`, `StepContract.riskCost` и
`StepContract.budgetSpend`; universal strict progress не требуется.

При активном guard проверяем `0≤opCost≤S.res.budget` и samplewise CE
non-regression на реально вычисленном batch successor. Тогда арифметическое
среднее CE не возрастает, расход равен `opCost≥0`, а
`StepContract.riskCost=opRisk≥0`.
Общее условие `0≤opCost` не добавляем. Guard не проверяет риск, поэтому
посылку `0≤opRisk` опускать нельзя: она необходима даже при `B=0` и `V=Empty`.
При любом отказе guard возвращает целое `S`; все три дельты обнуляются,
и hold остаётся допустимым шагом обычной структуры.

Для положительного контроля используем прежний доказанный двухэлементный
same-label mean-CE drop
[`sameZeroInitialMeanDrop_pos`](Hagi/Contracts/BatchCETrajectory.lean):
соответствующий `StepContract.decrease` действительно положителен. При
начальном бюджете `2`, `opCost=1/2` и `opRisk=1/4` получаем остаток бюджета
`3/2`, `StepContract.budgetSpend=1/2`, новый риск `1/4` при нулевом старом и
`StepContract.riskCost=1/4`. Это контроль одного commit, а не отдельный strict StepCert.
При `opCost=-1` или недоступном `opCost=3` возникает hold. На смешанном batch
не путаем нулевой mean residual с полным hold: настоящий asymmetric CE veto
возвращает `S`, поэтому обе resource/risk дельты и CE delta равны нулю.

`StepContract.budgetSpend≥0` — это не утверждение о nonnegative новом бюджете
для произвольного `S`; следующий бюджет является отдельным инвариантом с его
посылками. Адаптер не выбирает оптимальное действие и не доказывает
индивидуальный mixed-batch CE descent, параметрическую или оптимальную
сходимость, generalization, bounded последующий risk, экономию FLOP/time.

### 3.7 Accepted-only Pareto CE: строгий StepCert

Для `T = budgetedParetoBatchTrainStep X y S opCost opRisk write` следующий
адаптер не добавляет второй guard и не смягчает существующий. Требуются
положительный [`batchRangeSquare`](Hagi/Model/BatchCEDescent.lean),
`0≤opRisk`, ограничение opRisk значением riskLim сверху,
исходный `FloorHeld S floor` и полная активность
существующего guard: nonnegative affordable cost вместе с samplewise CE
non-regression на каноническом `batchTrainStep`.

[`budgetedParetoStepCert`](Hagi/Contracts/BudgetedParetoStepCert.lean) вызывает
уже доказанный `batchTrainStepCert` и через фактическое равенство активной
ветки переносит его на действительный guarded successor `T`. Результатом
является существующий [`StepCert`](Hagi/Unified/CertifiedLoop.lean):

- `StepCert.budgetSpend` равен заданной opCost, а
  `StepCert.riskSpend` — заданной opRisk; positivity поля
  `Hagi.Unified.HonestTransition.HonestTransition.objectiveDrop` принадлежит
  переходу к `T`, а `Hagi.Unified.HonestTransition.HonestTransition.actualDescent`
  даёт строгий спуск arithmetic-mean CE на supplied batch;
- `Hagi.Unified.CertifiedLoop.StepCert.hdec` связывает действительный новый
  бюджет с `S.res.budget` минус заданная opCost, а
  `Hagi.Unified.HonestTransition.HonestTransition.budgetBound` даёт его nonnegativity;
- исходный quality floor сохраняется на `T`, поскольку stored quality
  не меняется. Это не новое измерение held-out качества.

Отдельной посылки `Nonempty V` нет. Положительный range доказывает `0<B`,
после чего поданная метка первого элемента `Fin B` строит локальный witness
vocabulary nonempty. При `B=0` такое положительное range невозможно; фиктивный
`y 0` не создаётся. Зависимые данные `Hagi.Unified.CertifiedLoop.StepCert.trans`,
`Hagi.Unified.CertifiedLoop.StepCert.hdec` и
`Hagi.Unified.CertifiedLoop.StepCert.quality` переносятся через
canonical accepted equality, а не целое record через opaque cast.

Для контроля берутся ровно два same-label примера `Fin 2`, не singleton:
`Hagi.Unified.HonestTransition.HonestTransition.objectiveDrop > 0` у реального
guarded successor, бюджет `2→3/2`,
`StepCert.budgetSpend=1/2`, риск `0→1/4`, `StepCert.riskSpend=1/4`.
При opCost=3 относительно такого бюджета affordability ложна, и получить
strict certificate не удаётся. Поэтому hold из раздела 3.6 остаётся обычным
nonnegative `StepContract`, а не источником строгого прогресса.

Strictness относится к среднему CE, а не к каждому sample: guard даёт лишь
pointwise non-regression. riskLim ограничивает opRisk одного шага, но не
накопленный риск. Не следуют также CE→0, параметрическая сходимость,
generalization, оптимальное действие, гарантия для нелинейного backbone,
новое качественное измерение или экономия FLOP/time.

### 3.8 Range-based safe step: диапазон смещения логитов вместо суммы по словарю

Базовый сертификат раздела 3.1 мажорирует сдвиг CE квадратичной
константой `ceStepRange` = `2∑|d v|` — суммой модулей directional logit
displacement по всему словарю. C216 добавляет в CE engine вторую,
более острую константу:
[`ceStepLogitRange`](Hagi/Model/CEDescent.lean) — диапазон того же
смещения `d = ceDirection X θ t`,

```
R' = sup_v d v − inf_v d v,
```

записанный как `sup' d + sup' (−d)` над конечным словарём с общим
Mathlib canonical `Finset.univ_nonempty` witness.
[`ceStepLogitRange_nonneg`](Hagi/Model/CEDescent.lean) даёт
неотрицательность;
[`ceDirectionLogit_sub_le`](Hagi/Model/CEDescent.lean) фиксирует
поточечную оценку разности логитов через две sup'-грани, а
[`ce_logitDisplacement_range`](Hagi/Model/CEDescent.lean) переносит её
на весь directional logit displacement.
[`ceStepLogitRange_le_ceStepRange`](Hagi/Model/CEDescent.lean)
доказывает `R' ≤ R = ceStepRange = 2∑|d|`: новая константа никогда не
хуже старой, а на разреженных направлениях — существенно меньше
(диапазон учитывает лишь крайние значения, а не всю сумму по словарю).

Ключевой шаг мажоранты —
[`ceOneHot_next_le_rangeMajorizer`](Hagi/Model/CEDescent.lean): для
любого `0 ≤ η`

```
CE(θ + η·dir) ≤ CE(θ) − η·A + (η·R')²/8,
```

где `A = ceAlignment X θ t`. Острота квадратичного члена та же, что у
базового сертификата (`r²/8` из `lse_shift_upper`, без изменения
sharpness-константы), но аргумент использует диапазон смещения, а не
сумму по словарю — весь вклад дальних от крайних классов сокращается
до одной константы `R'`. Отсюда
[`ceRangeMajorizer`](Hagi/Model/CEDescent.lean) — миноризирующая
квадратичная мажоранта `CE − ηA + (ηR')²/8` — и certified step
[`ceRangeSafeStep`](Hagi/Model/CEDescent.lean) = `4A/R'²` при
`R' > 0` (иначе `0`)
([`ceRangeSafeStep_nonneg`](Hagi/Model/CEDescent.lean),
[`ceRangeSafeStep_pos_of_logitRange_pos`](Hagi/Model/CEDescent.lean)).
[`ceRangeMajorizer_safeStep_eq`](Hagi/Model/CEDescent.lean) даёт
точное значение мажоранты на этом шаге, а главный результат
[`ceOneHot_rangeSafeStep_le_residual`](Hagi/Model/CEDescent.lean)
переносит оценку на фактический CE:

```
CE(θ') ≤ CE(θ) − 2A²/R'².
```

[`ceOneHot_rangeSafeStep_lt`](Hagi/Model/CEDescent.lean) усиливает до
строгого спуска при `R' > 0` (строгость даёт
[`ceAlignment_pos_of_logitRange_pos`](Hagi/Model/CEDescent.lean):
`R' > 0 ⟹ A > 0`).

Соотношение со старым сертификатом — аддитивное сосуществование, не
замена. [`ceRangeSafeStep_ge_safeStepSize`](Hagi/Model/CEDescent.lean)
доказывает: при `0 < R'` новый certified step не меньше старого
`safeStepSize` (равного `4A/R` при `R > 0`), а
[`ceRange_residual_ge`](Hagi/Model/CEDescent.lean) — что сертифицированный
residual `2A²/R'²` не меньше старого `2A²/R²`. Поскольку `R' ≤ R`,
потенциальный выигрыш в размере шага — до `V²` (отношение `R/R'`
ограничено суммой `V` членов против двух крайних). Старый сертификат
(`ceMajorizer`, `ceOneHot_next_le`, `safeStepSize` и их леммы) сохранён
без изменений: оба сертификата сосуществуют, движок не переключается
принудительно.

Вырожденный случай обработан честно, без фиктивного шага.
[`ceStepLogitRange_eq_zero_of_eq_zero`](Hagi/Model/CEDescent.lean)
даёт: тождественно нулевые directional logits влекут `R' = 0`
(`ceRangeSafeStep` тотальна и равна `0` при `R' = 0`). Рецензент
C216 доказал в Lean (теорема reviewer_degenerate_no_old_step,
`.tmp/C216/review-negative2.lean`), что режим `R' = 0` при ненулевом
старом шаге в этом движке невозможен: `R' = 0` значит `d` константен,
а поскольку `Σ_v ceResidual v = 0`, alignment `A` обязан исчезнуть,
так что и старый `safeStepSize = 4A/R` равен нулю. Следовательно,
условие `0 < R'` эквивалентно `0 < R`: новый сертификат молча не
теряет ни один режим старого, и вырождение честно даёт нулевой шаг
в обоих сертификатах.

Numeric controls (identity two-class example, measured as
`#eval`-проверенные равенства в коде модуля):
[`identityTwoClass_logitRange_test`](Hagi/Model/CEDescent.lean) —
`R = 2` против `R' = 1`;
[`identityTwoClass_rangeSafeStep_test`](Hagi/Model/CEDescent.lean) —
шаг `1/2` против `2`;
[`identityTwoClass_step_comparison_test`](Hagi/Model/CEDescent.lean) —
строгое `1/2 < 2` (4×);
[`identityTwoClass_residual_comparison_test`](Hagi/Model/CEDescent.lean)
— сертифицированный residual `1/8` против `1/2` (4×). Это закрывает
пункт P0c внешнего архитектурного аудита
(`.omc/analysis/external-architecture-audit-2026-11-12.md`).

Census (измерено, fresh,
`.tmp/C216/validation/census-report.md`, TSV SHA
`1f2f63279977e1aa634fcbbdaf36363313ad79e6b2eaf81d06fb7e6390dc5e06`,
2933930 bytes / 14131 LF / 0 CR): OWNER 12281 → 12308 (+27, ровно
namepool ADDED, включая 2 private mangled `c216_*`), IR 1264 → 1264
(+0), CONSUMER 38 без изменений (новая публичная часть не приобрела
consumers), модуль `Hagi.Model.CEDescent` OWNER 328 → 355, fingerprint
4917100471297953757 → 11502919156674973306, retained rows
byte-identical.

Область заявления — только certified-descent: одношаговая верхняя
оценка CE и размер certified step. Не утверждаются wall-clock
ускорение, скорость или факт сходимости итерации, CE→0,
generalization, поведение при нелинейном backbone, преимущества вне
семейства log-linear one-hot CE или оптимальность шага среди всех
возможных.

### 3.9 Batch mirror: range-based safe step для arithmetic-mean batch loss

Сертификат раздела 3.2 мажорирует сдвиг arithmetic-mean batch loss
через `batchRangeSquare` — среднее квадратов `dirRange` (сумма модулей
логитов по словарю) общего направления `batchMeanDirection`. C223
переносит острую константу C216 (раздел 3.8) в batch engine: вместо
суммы по словарю берётся диапазон смещения логитов. Базовый
строительный блок — [`dirLogitRange`](Hagi/Model/BatchCEDescent.lean):
для произвольного направления `D`

```
R' = sup_v ceLogits X D v − inf_v ceLogits X D v
```

(записан как `sup' + sup' (−)` с общим Mathlib canonical
`Finset.univ_nonempty` witness).
[`dirLogitRange_nonneg`](Hagi/Model/BatchCEDescent.lean) даёт
неотрицательность; [`dirLogit_sub_le`](Hagi/Model/BatchCEDescent.lean)
фиксирует поточечную оценку разности directional logits, а
[`dir_logitDisplacement_logitRange`](Hagi/Model/BatchCEDescent.lean)
переносит её на фактическое η-масштабированное смещение, питая
`lse_shift_upper` — прямой batch-аналог C216
`ce_logitDisplacement_range`.
[`dirLogitRange_le_dirRange`](Hagi/Model/BatchCEDescent.lean) доказывает
`R' ≤ R = dirRange`: острая константа никогда не хуже словарной,
а на разреженных направлениях — существенно меньше.

Per-example мажоранта —
[`ceOneHot_alongNext_le_logitRange`](Hagi/Model/BatchCEDescent.lean):
для любого `0 ≤ η`

```
CE(θ + η·D) ≤ CE(θ) + η·dirAction X θ t D + (η·R')²/8,
```

та же сборка Böhning-типа, что у `ceOneHot_alongNext_le`, но с острым
диапазоном вместо словарной суммы; острота квадратичного члена (`r²/8`)
не изменена. Batch-агрегация: [`batchLogitRangeSquare`](Hagi/Model/BatchCEDescent.lean)
= арифметическое среднее квадратов `dirLogitRange` общего направления;
[`batchLogitRangeSquare_nonneg`](Hagi/Model/BatchCEDescent.lean) —
неотрицательность,
[`batch_pos_of_logitRangeSquare_pos`](Hagi/Model/BatchCEDescent.lean)
исключает пустой батч из положительной ветви, а
[`batchAlignment_pos_of_logitRangeSquare_pos`](Hagi/Model/BatchCEDescent.lean)
даёт `0 < batchAlignment` (зеркало `batchAlignment_pos_of_rangeSquare_pos`:
нулевой alignment обнуляет общее направление, а с ним и каждый range).

Отсюда averaged majorizer
[`batchLogitMajorizer`](Hagi/Model/BatchCEDescent.lean) =
`L − η·A + η²·R'²/8` (A = `batchAlignment`), certified step
[`batchLogitSafeStep`](Hagi/Model/BatchCEDescent.lean) = `4A/R'²` при
`R'² > 0` (иначе `0`;
[`batchLogitSafeStep_nonneg`](Hagi/Model/BatchCEDescent.lean),
[`batchLogitSafeStep_pos_of_logitRangeSquare_pos`](Hagi/Model/BatchCEDescent.lean))
и общий update
[`batchLogitNextParameters`](Hagi/Model/BatchCEDescent.lean) =
`alongNext θ (batchMeanDirection) (batchLogitSafeStep)`.
Усреднение per-example оценок фиксирует
[`batchLoss_alongNext_le_batchLogitMajorizer`](Hagi/Model/BatchCEDescent.lean),
точное значение мажоранты на шаге —
[`batchLogitMajorizer_logitSafeStep_eq`](Hagi/Model/BatchCEDescent.lean),
а главный результат
[`batchLoss_logitSafeStep_le_residual`](Hagi/Model/BatchCEDescent.lean):

```
L(θ') ≤ L(θ) − 2·A²/R'².

```

[`batchLoss_logitSafeStep_lt`](Hagi/Model/BatchCEDescent.lean) усиливает
до строгого спуска arithmetic-mean batch loss при `0 < R'²`
(строгость из положительного alignment).

Соотношение со старым batch-сертификатом раздела 3.2 — аддитивное
сосуществование. [`batchLogitRangeSquare_le_batchRangeSquare`](Hagi/Model/BatchCEDescent.lean)
доказывает `R'² ≤ batchRangeSquare`, а
[`batchLogitSafeStep_ge_batchSafeStep`](Hagi/Model/BatchCEDescent.lean) —
что при `0 < R'²` новый certified step не меньше старого `batchSafeStep`.
Старый сертификат (`batchLoss_safeStep_le_residual`, `batchSafeStep`,
`batchRangeSquare` и их леммы) не изменён; движок не переключается
принудительно.

Вырожденный случай обработан честно. При `R'² = 0`
`batchLogitSafeStep` тотальна и равна `0`
([`dirLogitRange_eq_zero_of_forall_eq_zero`](Hagi/Model/BatchCEDescent.lean):
тождественно нулевые directional logits влекут нулевой range);
фиктивного шага или witness не создаётся, `batchLogitNextParameters`
совпадает с `θ`.

Numeric controls (V=2, matrix `!![1, 1; -1, 1]`, направление
`single 0 1`; logits `(1, −1)`): измерено независимой RootApi-проверкой
(`.tmp/C223/production/RootApi.lean`, norm_num/fin_cases examples,
не поставляемый код модуля): `dirRange = 4`, `dirLogitRange = 2`
(строгое `2 < 4`), т.е. на этом примере словарная range-square `16`
против острой `4` — certified step и residual выигрывают до `4×`;
отдельная generic-инстанциация прогоняет
`batchLogitSafeStep_ge_batchSafeStep` на произвольном положительном
экземпляре. Две отрицательные пробы (neg1/neg2) подтверждают,
что ослабленные/противоречивые версии не доказуемы.

Census (измерено, fresh,
`.tmp/C223/validation/census-report.md`, TSV SHA-256
`492e9386457b1915e460de938ce353b5d52683b3d4327775901211486d255081`,
2850509 bytes / 13664 LF / 0 CR): OWNER 11849 → 11878 (+29: 22
source-level объявления + 7 компиляторных `.eq_1`/`.congr_simp`),
IR 1247 без изменений, CONSUMER 38 без изменений, модуль
`Hagi.Model.BatchCEDescent` OWNER 249 → 278, root source fingerprint
14718226048161838198 → 14249654862734778222, retained rows
byte-identical; +29 OWNER == NamePool ADDED по множествам.

Область заявления — только certified-descent arithmetic-mean batch loss:
одношаговая верхняя оценка и размер certified step. Не утверждаются
wall-clock ускорение, сходимость итерации, CE→0, generalization,
поведение при нелинейном backbone, samplewise-гарантии за пределами
среднего или оптимальность шага среди всех возможных.

### 3.10 Gated CE: отождествление нормы градиента и траекторный запас

Для гейтированного одноцелевого CE (tanh-гейтинг, `gatedForward`)
градиент по параметрам — это в точности транспонированный остаток
через sech²-якобиан: [`gatedGrad`](Hagi/Contracts/GatedCEGradientNorm.lean)
= `-gatedDirection`, покоординатно `gatedResidualTranspose`
([`gatedGrad_ofLp`](Hagi/Contracts/GatedCEGradientNorm.lean)); Fréchet-
производная действует как скалярное произведение с `gatedGrad`
([`fderiv_gatedCE_apply_inner`](Hagi/Contracts/GatedCEGradientNorm.lean)),
и `‖gatedGrad‖² = gatedAlignment`
([`norm_gatedGrad_sq`](Hagi/Contracts/GatedCEGradientNorm.lean)) —
определительно, без предположений сверх `Fintype V`.

Так как исполненный безопасный шаг `η = A/(2C)` с константой кривизны
`C(X) = 1 + 2Q + (2U)²/8` имеет точное падение `A²/(4C)`,
траекторный запас — четвёртая степень нормы градиента:
[`gated_grad_sum_fourth_le_uniform`](Hagi/Contracts/GatedCEGradientNorm.lean)

```
∑s∈[0,T) ‖∇L(θs)‖⁴ ≤ 4·C(X)·L₀.
```

Квадратичная форма `∑‖∇L‖² ≤ const·L₀` этим НЕ доказана: она
потребовала бы новой оценки `gatedCurvature ≤ κ(X)·gatedAlignment`
(линейной по A падения), что — отдельная задача. Эмпирических
посылок нет; цель `t` фиксированная one-hot.

## 4. Выбор примеров: supported inverse-propensity MSE

Для фиксированных `g_b : EuclideanSpace ℝ I` на непустом B выбираем PMF `q`
только при
условии `q_b ≠ 0 ∨ g_b = 0` для всех `b`. Один draw оценивает arithmetic mean
как `(B q_b)⁻¹ • g_b`. [`pmfMean_selectedMean_batchResidualGradient`](Hagi/Model/BatchCEDescent.lean)
доказывает coordinatewise unbiasedness; [`selectedMeanGradientMSE_eq_sum`](Hagi/Probability/MWU.lean)
даёт точный squared-error объект, не covariance/independence claim.

Если `0 < ∑b |ℓ_b|`, строим
[`selectedLoss_optimalPropensity`](Hagi/Probability/MWU.lean)
с `q_b = |ℓ_b|/∑i |ℓ_i|`.
[`selectedLoss_optimalPropensity_mse`](Hagi/Probability/MWU.lean)
фиксирует

```
MSE = (∑|ℓ|)² - ∑ℓ²,
```

а [`selectedLoss_optimalPropensity_mse_le`](Hagi/Probability/MWU.lean)
— минимум среди всех supported конкурентов. Для `ℓ_b=‖g_b‖`
используем [`selectedGradientMSE_optimalPropensity_le`](Hagi/Probability/MWU.lean);
arithmetic-mean масштаб добавляет ровно `B⁻²` через
[`selectedMeanGradientMSE_optimalPropensity_le`](Hagi/Probability/MWU.lean).

Когда настоящие gradient norms не вычислены заранее, берём feature-only
`F_b = featureNormSum X_b`, сумму Euclidean row norms матрицы.
[`norm_batchResidualGradient_le_featureNormSum`](Hagi/Model/BatchCEDescent.lean)
даёт `‖g_b‖≤F_b`. При `0<∑|F_b|` поддержка выполнена,
[`pmfMean_featureNormSum_optimalPropensity`](Hagi/Model/BatchCEDescent.lean)
сохраняет unbiasedness, а [`selectedMeanGradientMSE_featureNormSum_le`](Hagi/Model/BatchCEDescent.lean)
даёт

```
MSE ≤ B⁻² ((∑F)² - ‖∑g‖²).
```

Это upper envelope, не Neyman oracle по фактическим градиентам. Не обещаем
RNG runtime, generalization, меньший FLOP count или улучшенный loss.

## 5. Оптимизатор: выбирать по доказанному контракту

Основной путь — `batchNextParameters`; sign/Lion/SAM/HeavyBall не заменяют
его доказанный CE-сертификат.

- Нормализованный sign: при `k` непустом полагаем
  `s = signScale g = (∑|g_i|)/card k`, `D_i=s·sgn1(g_i)`.
  Если `J : Objective` содержит `0<L` и descentLemma, то
  [`sign_scaled_aligned`](Hagi/Unified/SignDescent.lean) доказывает
  alignment; при `0<eta≤1/L` [`sign_descent`](Hagi/Unified/SignDescent.lean)
  даёт `f(x-etaD) ≤ f(x)-eta(1-L eta/2)‖D‖²`. Без нормализации
  такого вывода нет.
- Lion: [`lion_step_norm_bound`](Hagi/Optimization/Lion.lean)
  ограничивает сырой `eta·sign(m)` лишь `eta²·d` в squared norm. Для спуска
  дополнительно нужна coherence градиента с моментом; тогда используем
  [`lion_descent`](Hagi/Unified/SignDescent.lean) с той же `signScale`.
- SAM: `samW` — sup loss на ρ-ball, не готовый update. При `ρ≥0` и
  ограниченности сверху образов `J.f` на сдвинутых ρ-ball-семействах для `x` и `x'`
  принимаем new point только при оценке локальной остроты sharp и
  доказанном SAM-drop δ; [`sam_descent_bridge`](Hagi/Unified/SignDescent.lean)
  даёт `f(x') ≤ f(x) - (delta-sharp)`. Отдельного adversarial optimizer здесь нет.
- HeavyBall: используем только квадратичную модальную модель. Для
  `0<μ≤L` полагаем
  `β=((√L-√μ)/(√L+√μ))²`, `eta=4/(√L+√μ)²`.
  [`hb_general_window`](Hagi/Optimization/HBRate.lean) покрывает
  `μ≤λ≤L`. Для характеристических корней и Jordan-оценки дополнительно
  требуем `0<μ<L` (тогда `0<β<1`, `ρ=√β>0`) и соответствующие
  root/recurrence посылки: [`hb_spectral_mode`](Hagi/Optimization/HBRate.lean)
  даёт `|root|²=β` для заданного root-уравнения.
  Это не траекторный `Cβ^(t/2)` результат: при кратном корне есть
  Jordan-фактор [`hb_critical_trajectory_bound`](Hagi/Optimization/HBRate.lean),
  а у фактической пары HeavyBall второй коэффициент —
  `β+eta(1-β)` по [`hb_pair_second_order`](Hagi/Optimization/HBRate.lean).

## 6. Квантование и распределение памяти/битов

### 6.1 Grid и ternary представление

Для `Δ>0`, [`gridQ`](Hagi/Energy/Quantizer.lean) имеет вид
`Δ round(x/Δ)` и pointwise error `≤Δ/2`. Применяя по координатам,
[`gridQVec_norm_sq`](Hagi/Energy/Quantizer.lean) даёт

```
∑i(w_i-gridQVec Δ w_i)² ≤ card(k)(Δ/2)².
```

Для `s>0` и ternary `qTern s x = s roundTern(x/s)` обязательно учитываем saturation.
[`ternary_split_le`](Hagi/Runtime/TernaryExact.lean) даёт

```
Σ(w-qTern s w)² ≤ n(s/2)² + satTail s w.
```

[`quant_energy_bridge_saturation`](Hagi/Runtime/TernaryExact.lean)
переводит это в energy bound лишь при `0≤κ` и отдельной
`h_emp_lip: dE ≤ κ*√(∑i(w_i-qTern s w_i)²)`.
[`tritEncode_injective`](Hagi/Energy/Ternary.lean) и
[`tritEncode_lt`](Hagi/Energy/Ternary.lean) подтверждают injective
five-trits byte block; [`packedTernarySamples_decode_point`](Hagi/Runtime/TernaryCodec.lean)
возвращает quantized, не raw values. Это формат, не гарантия ABI/heap size.

При фиксированном pattern `q`, `0<∑q_i²`, выбираем
`s₀=(∑q_i x_i)/(∑q_i²)`; [`lsScale_optimal`](Hagi/Energy/Ternary.lean)
минимизирует squared reconstruction error среди всех real scales. Это не
minimax-scale и не оптимизация самого pattern.

### 6.2 Per-block scale и bit-reallocation

Для блоков по пять весов вычисляем `blockPenalty` как минимум двух
доказанных score, затем минимизируем его независимо в каждом блоке по 255
codes. [`selectedGroupScales_total_le`](Hagi/Model/CEGroupedScale.lean)
даёт exact minimum суммарного declared certificate, а
[`ceOneHot_joint_le_blockPenalties`](Hagi/Model/CEGroupedScale.lean) —

```
CE(joint selected) ≤ CE(raw) + ∑g blockPenalty_g.
```

При `G>0` [`localEvaluationCount_le_jointCandidateCount`](Hagi/Model/CEGroupedScale.lean)
сравнивает `255G` logical score calls с `255^G` assignments, а
[`decodeStep_packedBlocks`](Hagi/Model/CEGroupedScale.lean) связывает
payload с выбранными параметрами. Classical choose в exact selector не
выдаём за native поиск; счёт также не является временем/FLOPs/памятью ABI.

При `e_l(b)=layerError c_l b=c_l/2^b` перенос одного бита из `k` в `j`
меняет ошибку на `e_k-e_j/2` по [`transfer_exact`](Hagi/Budget/BitAlloc.lean).
Делаем перенос, если `j≠k`, `2e_k<e_j` и `f_k>0`: тогда ошибка строго падает по
[`imbalance_yields_gain`](Hagi/Budget/BitAlloc.lean).
[`no_infinite_improving_chain`](Hagi/Budget/BitAllocTermination.lean)
запрещает бесконечную такую цепь при фиксированном бюджете. При `∀i, 0≤c_i`
и отсутствии строгого улучшения для всех `j≠k` с `0<f_k`
[`stable_factor_two`](Hagi/Budget/BitAlloc.lean) для donor `f_k≠0` даёт
`layerError(c_j)(f_j) ≤ 2*layerError(c_k)(f_k)`.
Полный continuous clamped n-layer алгоритм отсюда не выводим.

Дополнительный continuous certificate: если `c_i>0`, `∑f=∑g=B`,
`n>0` и `c_i/2^{f_i}` одинаково для всех `i`, то
[`water_filling_inner_optimum`](Hagi/Budget/BitAlloc.lean)
доказывает `totalErrorCont c f ≤ totalErrorCont c g`.
Применяем его только при уже найденном equalizing `f`, не как конструктор.

### 6.3 BF16: guarded delta-read с безопасным re-anchor

Логический носитель — [`Hagi.Runtime.BF16Delta.Code`](Hagi/Runtime/BF16Delta.lean):
знак, raw exponent `0..254` и fraction описывают все конечные BF16-коды.
`decode` отображает их точно в `ℚ`, включая signed zeros и subnormals.
Это не упакованный 16-bit layout и не native-память.

Для guard `Hagi.Runtime.BF16Delta.SamePositiveNormalBinade` требуются
неотрицательные знаки, равные raw exponents и ненулевой exponent.
Порядок по величине не ограничен. Тогда
[`Hagi.Runtime.BF16Delta.exists_sameBinade_difference`](Hagi/Runtime/BF16Delta.lean)
строит точную разность в `Code`, включая zero, negative и subnormal cases.

Два таких кандидата должны иметь pointwise nearest-посылки для самого
бэкенда; существование `exists_IsNearest` не задаёт executable RNE или tie rule.
Для двух уже представленных кодов, исходного и нового, рецепт следующий:

- получить delta с посылкой
  `Hagi.Runtime.BF16Delta.IsNearest (decode new - decode anchor) delta`;
- при guard получить readback с посылкой
  `Hagi.Runtime.BF16Delta.IsNearest (decode delta + decode anchor) readback`;
  вне guard использовать `decode new` независимо от readback;
- применить
  [`Hagi.Runtime.BF16Delta.guardedRead_nearest_returns_new`](Hagi/Runtime/BF16Delta.lean)
  для возврата значения `decode new`.

FTZ при subnormal delta может нарушить ближайшую посылку. Вне guard
[`Hagi.Runtime.BF16Delta.extreme_nearest_delta_loses_update`](Hagi/Runtime/BF16Delta.lean)
показывает потерю ненулевого обновления: для anchor `2^127` и new `129/128`
nearest delta равна `-anchor`, а nearest reconstruction имеет значение нуля.
Поэтому идеальное `(new-anchor)+anchor` нельзя подставлять вместо fallback.

Пока не доказаны packed storage, GDN/runtime integration, поддержка FTZ,
физическая экономия памяти/времени или улучшение обучения и held-out CE.

### 6.4 Certified low-rank замена: Eckart-Young хвост и строгий ранг-признак

Бюджетная строка e_rank из декомпозиции ошибок адресуется снизу:
любая замена `B` с `rank B ≤ k` оставляет Frobenius-ошибку не меньше
квадратичного хвоста сингулярных чисел —
[`eckart_young_lower_bound`](Hagi/External/Flywheel/EckartYoungLower.lean)
(нижняя граница к оптимальности
[`eckart_young_frobenius`](Hagi/External/Flywheel/FrobeniusNorm.lean)).
Отсюда: усечение не может быть улучшено в Frobenius-норме, и бюджет
e_rank для спектрального сжатия — фундаментальный предел, а не артефакт
выбора алгоритма.

Для знаковых матриц обновлений (отрицательная диагональ,
неотрицательная внедиагональ) признак полного столбцового ранга даёт
[`neg_diag_pos_off_diag_injective`](Hagi/External/Flywheel/NegDiagRank.lean):
при СТРОГО отрицательных строчных суммах оператор инъективен. Слабая
версия (суммы `≤ 0`) ложна — лапласиан на двух вершинах убивает
константный вектор (пример в том же файле); строчные суммы ровно ноль
(softmax минус эмпирические частоты) требуют отдельной лапласианной
формулировки ранга и здесь не утверждаются.

### 6.5 Градиентный бутылочное горлышко: logitGrad и Eckart-Young сборка

Носитель строчки логит-градиента — softmax минус эмпирическое
распределение следующего токена —
[`logitGrad`](Hagi/Contracts/LogitGrad.lean): обобщает форму
ceResidual с one-hot на произвольные суб-вероятностные `N`.
Строчные факты: суммы ноль при вероятностных `N`
(`logitGrad_row_sum_zero`), строго положительное смещение вне
one-hot цели (`logitGrad_pos_off_target`), строго отрицательное в
цели при нетривиальном словаре (`logitGrad_neg_at_target`, явная
посылка `∃ w ≠ t c`: синглтон-случай даёт нулевую, не отрицательную
запись), абсолютная строчная масса `≤ 2` для суб-вероятностных `N`
(`abs_logitGrad_row_le_two`); новый строчный ингредиент —
`smax_lt_one`.

Сборка — [`gradient_bottleneck_bound`](Hagi/Contracts/
GradientBottleneck.lean): всякое достижимое логит-обновление `Δ`
посылкой `rank Δ ≤ k` оставляет Frobenius-остаток не меньше
квадратичного хвоста сингулярных чисел `logitGradM` за `k`.
Посылки (таблица):

| Посылка | Роль |
|---|---|
| `hΔ : Δ.rank ≤ k` | достижимость: ранг обновления ограничен |
| `∃ w ≠ t c` (только neg-at-target) | нетривиальный словарь (данные) |
| суб-вероятность `N` (0 ≤ N, ∑ ≤ 1) | только для |row| ≤ 2 |

Честность формы-посылки: вывод «голова ранга D ⇒ достижимые
обновления ранга ≤ 2D» (бумажная семантика §B5.4) и прямоугольный
носитель C×V отложены — лендится квадратный n×n случай; при `k ≥ n`
хвост пуст и оценка тривиальна (но верна).

### 6.6 Динамика маршрутизации: odds-ratchet, deadlock-свидетель и анти-лок-ин

Механизм ratchet — точное обновление шансов softmax
([`softDef_odds`](Hagi/Model/Routing.lean)):
`a⁺j/a⁺k = (aj/ak)·exp(Δsj−Δsk)` без приближений. Его локальная
эксплуатация — [`odds_ratchet`](Hagi/Model/Routing.lean): сдвиг
скоров, пропорциональный самой строке внимания (Δs = c·a, c > 0),
за один шаг строго увеличивает шансы более внимательного ключа
(мультипликативный фактор exp(c(aj−ak)) > 1). На стороне значений —
точное V-шаговое тождество `ratchet_advantage_step`:
`A⁺j = Aj + η·aj·‖δ‖²` — каждый посещаемый ключ набирает
преимущество (монотонная форма `ratchet_advantage_mono`).
Утверждается ТОЛЬКО один шаг; глобальный/итерируемый
экспоненциальный рост НЕ утверждается (честность по addendum A3).

Негативный pinned-challenge — deadlock-свидетель
[`deadlock_witness`](Hagi/Model/Routing.lean): точнорациональный
3-ключевой софтмакс (skоры = логарифмы рационального вектора
внимания, `exp∘log` сокращается точно: `dw_att0` = 1/10,
`dw_att1` = 9/20) даёт полезному ключу внимание ровно ε = 1/10;
его вклад в градиент запроса (точный B2-член a·A•k) имеет норму
≤ ε·M — полезный-но-игнорируемый ключ обучает запрос медленно.

Анти-лок-ин гарантия — `ewNorm_survivor_lower`
(Hagi/Autonomy/HedgeSurvivor.lean): при неотрицательных потерях и
η ≥ 0 нормированный вес любого ключа ≥ (1/K)·exp(−η·Σℓ) — вес
убывает не быстрее экспоненциально по собственной накопленной
потере, роутер не может навсегда shut out ключ с ограниченными
потерями. Посылки слабее регрет-стороны (`hsurv_derived` требует
ℓ ∈ [0,1]; здесь только ℓ ≥ 0, регрет при этом не утверждается).

Отложено (не утверждается): скор-стороннее тождество
Δs = η‖δ‖²·x_iᵀ(x_j−x_i) и первый порядок sign(Δa) = sign(a−Σa²)
(нужна second-order подстановка + B2 fderiv-машинария); монитор
эффективного ранга/энтропии роутера (addendum item 4, отдельная
lane).

### 6.7 Мост Хadamard-некогерентности ↔ тернарной квантизации

Мотивация — QuIP# (Thm 4.1), формализована математика, а не статья.
Ключевая честность: μ-некогерентность — всегда ПОСЫЛКА.
Адамар НЕ подавляет ∞-норм универсально: контрпример
[`hadamard_not_universally_incoherent`](Hagi/Contracts/HadamardTernaryBridge.lean)
при `k = 1`, `x = (2, 2)` даёт `‖Hx‖∞ = ‖x‖₂ = 2√2`
(эффективное μ = √d = √2 > 1), и координата `2√2 > 3/2`
насыщает тернарную сетку при `s = 1`.

- [`hadamard_satTail_zero_of_l2_bound`](Hagi/Contracts/HadamardTernaryBridge.lean):
  при `‖x‖₂ ≤ s·√d` (d = 2^k, s > 0) и посылке μ-некогерентности
  `‖Hx‖∞ ≤ μ·‖x‖₂/√d` с `0 ≤ μ ≤ 1` каждая координата `Hx` лежит в
  тернарном диапазоне `|y| ≤ 3s/2`, и хвост насыщения `satTail`
  зануляется.
- [`hadamard_quant_error_le_of_l2_bound`](Hagi/Contracts/HadamardTernaryBridge.lean):
  тогда суммарная квадратичная ошибка квантователя не превосходит
  `d·(s/2)²` — чистое полу-шаговое округление, без хвоста.
- [`hadamard_logits_invariance_mulVec`](Hagi/Contracts/HadamardTernaryBridge.lean):
  до квантования логиты в точности инвариантны:
  `(W·Hᵀ) *ᵥ (H *ᵥ x) = W *ᵥ x` (ассоциативность + `Hᵀ·H = 1`);
  после квантования тождество приближённое и управляется границей
  ошибки теоремы 1.
- [`blockPenalty_le_of_all_ternInRange`](Hagi/Contracts/HadamardTernaryBridge.lean)
  и [`hadamard_ce_blockPenalty_reduction`](Hagi/Contracts/HadamardTernaryBridge.lean):
  если сырые веса блока — Адамар-образ некогерентного источника, все
  веса в диапазоне, хвост в `groupStructuralPenalty` исчезает, и
  сертифицированная локальная цель `blockPenalty` (реальный
  потребитель из CEGroupedScale) оценивается чистым rounding-членом
  `2·featureAbsSum·√5·lvl/2`.

Отложено (не утверждается): никаких утверждений о подавлении
∞-норм самим Адамаром; никаких post-quantization логит-гарантий.

## 7. HNet: стартовый ratio из continuous cost-модели

Для `a,b,T,r>0` обозначим `C(r)=aTr+bT²/r²`: локальная pooling-цена плюс
latent-attention price. [`hier_attn_saving`](Hagi/Model/HNet.lean)
даёт только алгебраическое `c(T/r)²=cT²/r²`; физического FLOP-claim нет.

Выбираем [`hnetOptRatio`](Hagi/Model/HNet.lean)

```
s = (2bT/a)^((3:ℝ)⁻¹).
```

[`hnet_opt_ratio`](Hagi/Model/HNet.lean) доказывает
`C(s)≤C(r)` для каждого `r>0`, а
[`hnet_opt_ratio_unique`](Hagi/Model/HNet.lean) — что равенство
цен возможно только при `r=s`. В доказательстве используются
`s³=2bT/a`, `aTs³=2bT²` и точный gap

```
C(r)-C(s) = bT²(r-s)²(2r+s)/(r²s³).
```

Используем `s` как стартовое continuous соотношение для этой абстрактной
cost-модели. Нет Nat rounding, learned chunking, runtime argmin,
architectural/neuron-level optimality или гарантии training quality.

### 7.1 Finite capped lossless chunks

Для конечного `xs : List α` выбираем `capacity width : ℕ` с natural fit
`xs.length ≤ capacity * width` и вызываем
[`cappedChunks`](Hagi/Model/AdaptiveChunking.lean), либо берём точную
Nat-ёмкость `⌊L / r⌋₊` в `floorCappedChunks L r width xs`. Это не native
floating-point, expected или average ratio. Успешный existential outcome
фиксируем равенством `hsuccess : cappedChunks capacity width xs = some chunks`
(или его `floorCappedChunks`-аналогом): именно оно нужно и для границ, и для
сохранения, и для стоимости. Тогда `length_cappedChunks_le` даёт
`chunks.length ≤ capacity`, а `flatten_cappedChunks` — `chunks.flatten = xs`;
`ne_nil_of_mem_cappedChunks` исключает пустые члены результата.

Определение применяет `List.splitLengths` к `List.replicate capacity width`,
затем удаляет только пустые padding-чанки. Последний непустой chunk может
быть короче width. При нарушении fit получаем none: нулевые capacity или
width не принимают непустой вход, а пустой вход законно даёт `some []`.
Отказ не является успешным zero-cost разбиением; для непустого `xs`
равенство flatten не позволяет незаметно вернуть `chunks = []`.

При `0 ≤ L`, `0 < r` тот же `hsuccess` даёт
`floorCappedChunks_length_le : (chunks.length : ℝ) ≤ L / r` и
`floorCappedChunks_flatten : chunks.flatten = xs`. Для конечного `k`,
`c : k → ℝ` с `∀ l, 0 ≤ c l` подставляем в обе cost-теоремы одну и ту же
константу `M := fun _ => (chunks.length : ℝ)`:

```
adaptiveCost c M ≤ ∑ l, c l * (⌊L / r⌋₊ : ℝ) ^ 2,
adaptiveCost c M ≤ ∑ l, c l * (L / r) ^ 2.
```

Первая оценка — `floorCappedChunks_cost_le_floor`, вторая —
`floorCappedChunks_adaptive_le_static`, прямо использующая прежнюю
`adaptive_le_static`. Это не оценка произвольного per-level router.

Семантически здесь одно детерминированное fixed-width разбиение входного списка, а не learned/adaptive per-level H-Net routing, causal-поведение,
дифференцируемые границы, физическое хранение или runtime-engineering
adapter. Формальные неравенства относятся к `adaptiveCost` при указанных
nonnegativity/cap hypotheses: не следуют FLOPs, physical RAM, wall-time,
training quality, held-out CE, IEEE/RNE/BF16, оптимальная end-to-end
архитектура или глобальный HAGI. Throughput, sparsity, compression и
качество router также не доказываются.

### 7.2 Finite boundary-driven lossless chunks

Для конечной последовательности xs и выбранной функции boundary : α → Bool
конструктор [`boundaryChunks`](Hagi/Model/AdaptiveChunking.lean) задаёт

```
boundaryChunks boundary xs = xs.splitBy (fun _ next => !boundary next)
```

Значение true на следующем токене next начинает новый chunk перед этим
токеном; false продолжает прежний chunk. Первый токен сам создаёт первый
непустой chunk без запроса его флага. Поэтому даже true на первом токене не
создаёт пустой префикс или дополнительный chunk: singleton с первым true
остаётся одним singleton-chunk. [`length_boundaryChunks`](Hagi/Model/AdaptiveChunking.lean)
даёт точный счёт, включая хвост без первого токена:

```
(boundaryChunks boundary xs).length =
  match xs with
  | [] => 0
  | _ :: tail => tail.countP boundary + 1
```

[`flatten_boundaryChunks`](Hagi/Model/AdaptiveChunking.lean) сохраняет
исходную последовательность,
[`ne_nil_of_mem_boundaryChunks`](Hagi/Model/AdaptiveChunking.lean) исключает
пустые возвращённые группы, а
[`length_boundaryChunks_le`](Hagi/Model/AdaptiveChunking.lean) ограничивает
число групп длиной входа.

Проверяемые конечные примеры:

- пустой вход даёт [], счёт 0;
- sparse-флаги fun _ => false на [0,1,2] дают [[0,1,2]], счёт 1;
- dense-флаги fun _ => true на [0,1,2] дают [[0],[1],[2]], счёт 3;
- alternating boundary n := n % 2 == 1 на [0,1,2,3,4] даёт
  [[0],[1,2],[3,4]], счёт 3;
- boundary n := n == 0 на [0,1,2] игнорирует true первого токена и даёт
  [[0,1,2]], а fun _ => true на [0] даёт [[0]], не два chunk.

Capacity guard у [`cappedBoundaryChunks`](Hagi/Model/AdaptiveChunking.lean)
проверяет именно фактический счёт вычисленного разбиения:

```
if (boundaryChunks boundary xs).length ≤ capacity then
  some (boundaryChunks boundary xs)
else
  none
```

[`cappedBoundaryChunks_eq_some_iff`](Hagi/Model/AdaptiveChunking.lean)
эквивалентно связывает успех с тем же разбиением и его bound:

```
cappedBoundaryChunks capacity boundary xs = some chunks ↔
  chunks = boundaryChunks boundary xs ∧ chunks.length ≤ capacity
```

Нельзя подменить успешный результат другим разбиением или превратить отказ в
пустой успех через getD. Пустой вход законно даёт some [] даже при capacity 0.
Непустой вход имеет хотя бы одну группу и при capacity 0 отвергается; равенство
flatten также исключает some [] для непустого входа.

[`floorBoundaryChunks`](Hagi/Model/AdaptiveChunking.lean) использует точный
Nat floor ёмкости ⌊L / r⌋₊, без floating-point или физического rate. Из
фактического hSuccess, условий 0 ≤ L и 0 < r теорема
[`floorBoundaryChunks_length_le`](Hagi/Model/AdaptiveChunking.lean) получает

```
(chunks.length : ℝ) ≤ L / r
```

а [`floorBoundaryChunks_flatten`](Hagi/Model/AdaptiveChunking.lean) сохраняет
тот же вход. Прежние adaptive_le_static и adaptive_lt_of_strict не меняются.
Для конечного k и неотрицательных c обе новые cost-специализации используют
на каждом уровне один и тот же фактически возвращённый chunks.length:
[`floorBoundaryChunks_adaptive_le_static`](Hagi/Model/AdaptiveChunking.lean)
даёт

```
adaptiveCost c (fun _ => (chunks.length : ℝ)) ≤
  ∑ l, c l * (L / r) ^ 2
```

[`floorBoundaryChunks_adaptive_lt_of_strict`](Hagi/Model/AdaptiveChunking.lean)
заменяет ≤ на < только при выбранном положительном c l₀ и фактическом
hstrict : (chunks.length : ℝ) < L / r; hSuccess здесь поставляет hdom.

Конкретный strict-пример для Fin 1: l₀ = 0, c 0 = 1 > 0, L = 4, r = 1. Sparse
route выше действительно успешен:

```
floorBoundaryChunks 4 1 (fun _ => false) [0,1,2] = some [[0,1,2]]
```

Его фактический счёт 1 даёт 1 < 4, поэтому строгая специализация имеет вид
1 < 16; нестрогая при том же успешном результате даёт 1 ≤ 16. Это одна
конкретная условная специализация, а не строгое улучшение для всех входов.

Здесь детерминированный конечный token-functor, не learned, causal, online,
дифференцируемый или произвольный per-level H-Net router. Capacity — абстрактный
предел числа групп, не байтовая ёмкость или native memory footprint. Не
следуют measured model quality, RAM, FLOPs, latency/native runtime,
training/held-out CE, BF16/RNE/FTZ, глобально оптимальная архитектура HAGI или
worst-case bound из expected/average ratio.

### 7.3 Previous/current tags with plain-erasure projection

Для конечного `xs : List α` зададим supplied Boolean-предикат на парах
θ : α × α → Bool и сначала применим
[`adjacentPairs`](Hagi/Model/AdaptiveChunking.lean):

```
adjacentPairs [] = []
adjacentPairs (a :: rest) = (a,a) :: (a :: rest).zip rest
```

В каждой паре после первой поля означают именно `(previous,current)`.
Восстановление исходного значения всегда использует `Prod.snd`:
[`map_snd_adjacentPairs`](Hagi/Model/AdaptiveChunking.lean) доказывает
`(adjacentPairs xs).map Prod.snd = xs`, а
[`length_adjacentPairs`](Hagi/Model/AdaptiveChunking.lean) — равенство длин.
Первый `(a,a)` — детерминированный dummy seed для сохранения одного тега на
значение. Его флаг C213 игнорирует; это не learned prior и не forced first
flag H-Net. Равномерный `Prod.fst` здесь неверен: уже на `[0,1]` он даёт
`[0,0]`.

Дальше используем прежний C213-маршрут
`boundaryChunks θ (adjacentPairs xs)`, а не второй partition algorithm.
Его `List.splitBy`-компаратор видит флаг следующей пары: `true` начинает новый
chunk **перед current**, `false` продолжает прежний chunk. На dummy seed
компаратор не вызывается, поэтому seed не добавляет счёт.
[`length_adjacentBoundary_projection_exact`](Hagi/Model/AdaptiveChunking.lean)
переносит точный счёт C213: `0` для пустого входа и `tail.countP θ + 1` для
непустого paired tail.

Проецируем каждый фактически полученный paired chunk операцией
`chunks.map (List.map Prod.snd)`.
[`flatten_map_snd_adjacentBoundary`](Hagi/Model/AdaptiveChunking.lean)
доказывает, что flatten полного projected route возвращает все исходные
значения с сохранением порядка;
[`ne_nil_of_mem_adjacentBoundary_projection`](Hagi/Model/AdaptiveChunking.lean)
сохраняет непустоту каждого возвращённого chunk. Главное для capacity и cost
— **проекция сохраняет фактический route count**: это
[`length_adjacentBoundary_projection`](Hagi/Model/AdaptiveChunking.lean).

Capacity применяется уже к raw pair chunks через существующий
`cappedBoundaryChunks capacity θ (adjacentPairs xs)`. Из фактического успеха

```
hSuccess : cappedBoundaryChunks capacity θ (adjacentPairs xs) = some chunks
```

следуют
[`flatten_cappedAdjacent_projection`](Hagi/Model/AdaptiveChunking.lean),
[`length_cappedAdjacent_projection_le`](Hagi/Model/AdaptiveChunking.lean) и
[`ne_nil_of_mem_cappedAdjacent_projection`](Hagi/Model/AdaptiveChunking.lean):
все значения восстанавливаются, projected count ≤ capacity и каждый член
projected route непуст. При отказе Option возвращает none; не появляется
успешный empty fallback или caller-chosen count. Пустой вход может законно
дать `some []`, а непустой не может успешно потерять значения.

`floorBoundaryChunks L r θ (adjacentPairs xs)` использует точную ёмкость
Nat floor `⌊L / r⌋₊`. Его фактический hSuccess обеспечивает
[`floorAdjacent_projection_flatten`](Hagi/Model/AdaptiveChunking.lean);
[`floorAdjacent_projection_length_le`](Hagi/Model/AdaptiveChunking.lean)
дополнительно требует `0 ≤ L`, `0 < r` и даёт
`((chunks.map (List.map Prod.snd)).length : ℝ) ≤ L / r`. Это не caller-chosen
M, default empty list, expected ratio или average count.

Для конечного носителя уровней k и `∀ l, 0 ≤ c l` обе cost-теоремы
используют один и тот же фактический projected route count на всех уровнях.
При указанных hSuccess, `0 ≤ L` и `0 < r`
[`floorAdjacent_projection_adaptive_le_static`](Hagi/Model/AdaptiveChunking.lean)
даёт

```
adaptiveCost c (fun _ => ((chunks.map (List.map Prod.snd)).length : ℝ)) ≤
  ∑ l, c l * (L / r) ^ 2.
```

Строгая [`floorAdjacent_projection_adaptive_lt_of_strict`](Hagi/Model/AdaptiveChunking.lean)
сохраняет те же посылки и дополнительно требует выбранный `l₀ : k`,
`0 < c l₀` и фактическое
`((chunks.map (List.map Prod.snd)).length : ℝ) < L / r`; лишь тогда знак
сменяется на `<`. Непустоту членов успешного floor route отдельно доказывает
[`ne_nil_of_mem_floorAdjacent_projection`](Hagi/Model/AdaptiveChunking.lean).
Это неравенства объявленной модели `adaptiveCost`, а не доказательство
физической эффективности.

Проверочная локальная θ для полярности имеет вид
`θ p = !(p.1 + 1 == p.2)`. На `[0,1,3,4,10]` она даёт
`[[0,1],[3,4],[10]]`, тогда как ошибочное прямое использование successor
как cut flag даёт другое разбиение `[[0],[1,3],[4,10]]`. На повторяющихся
значениях `[0,1,1,2,10,11,11]` та же локальная θ даёт
`[[0,1],[1,2],[10,11],[11]]`: current `1` продолжает после `0`, но режет
после `1`; current `11` продолжает после `10`, но режет после `11`.
Поэтому решение зависит от пары, а не только от current. Здесь θ — supplied
local test predicate; production не объявляет отдельную per-symbol функцию
nonSuccessorCut. Фиксированный параметр θ может зависеть от данных, но не
обучается через параметры модели в этой формализации.

Отношение к первичным H-Net источникам ограничено формой adjacency.
[Paper v2, equation (4)](https://arxiv.org/html/2507.07955v2#S2.E4)
использует `Q(current)/K(previous)`, `p₁ = 1` и нестрогий порог `≥ 0.5`.
[Pinned code main 3673fe...](https://github.com/goombalab/hnet/blob/3673fe1217ebeb0d1438c7c71d58d32bdd190ec2/hnet/modules/dc.py)
использует `Q(previous)/K(current)`, строгий step-порог `> 0.5` и
normalization epsilon. Эти семантики намеренно не усредняются и не
подменяются generic θ; dummy seed также не является доказательством forced
first flag.

Lossless здесь означает только erasure значений из paired chunks. H-Net
head selection отдельно отбрасывает non-head представления и не является
этим lossless восстановлением. Для будущей head-mask equivalence первый флаг
нужно рассматривать отдельно. Не доказаны learned/differentiable/causal/
online/per-level router, encoder, Q/K projection, cosine, zero-norm, tie,
causal stability уже supplied representations, stateful packed-mask
эквивалентность, BF16/Float-семантика, runtime, минимальная память,
training/held-out качество или глобальная оптимальность HAGI. Target ratio и
ratio loss не задают actual cap; логический count сам по себе не является
physical cost.

### 7.4 Head-position recovery over the boundary route

Зададим для supplied Boolean-предиката границ boundary : α → Bool и
конечного `xs : List α` recovery-функцию
[`boundaryHeads`](Hagi/Model/AdaptiveChunking.lean):

```
boundaryHeads boundary xs = (boundaryChunks boundary xs).map List.head?
```

Она возвращает носитель `List (Option α)`: head-токен каждого фактически
полученного chunk маршрута C213. Все утверждения ниже относятся к этому
фактическому маршруту; отдельного supplied θ-маршрута здесь не строится,
а capacity/floor варианты C213 в этой секции не переносятся.

Сохранение счёта даёт
[`length_boundaryHeads`](Hagi/Model/AdaptiveChunking.lean): число heads
равно точному числу chunks `boundaryChunks`, включая `0` для пустого входа
и `1 + tail.countP boundary` для непустого. Каждый head — реальный токен:
[`isSome_of_mem_boundaryHeads`](Hagi/Model/AdaptiveChunking.lean)
доказывает `isSome = true` для каждого члена результата, опираясь на
непустоту `ne_nil_of_mem_boundaryChunks`; пустой head невозможен.
[`mem_of_mem_boundaryHeads`](Hagi/Model/AdaptiveChunking.lean)
доказывает, что каждый head-токен лежит в исходном входе: heads
восстанавливают позиции входных значений, а не порождают новые.

Первый head структурно принуждён:
[`boundaryHeads_head?_cons`](Hagi/Model/AdaptiveChunking.lean) даёт
`head? = some (some a)` для входа `a :: rest` — первый head обязан быть
первым токеном входа независимо от флага `boundary a`. Каждый не-первый
head лежит точно на границе:
[`boundary_of_mem_boundaryHeads_tail`](Hagi/Model/AdaptiveChunking.lean)
доказывает `boundary x = true` для всякого `some x` из tail результата
(служебная private-лемма `head_boundary_of_mem_tail` проходит по цепочке
`List.splitBy`). Поэтому chunk-start mask восстанавливается из самих
heads: первый head — всегда старт (принуждён), каждый следующий head —
токен с истинным boundary-флагом, и других стартов маршрут не создаёт.

Это структурный аналог forced first head H-Net v2: [paper v2, equation
(4)](https://arxiv.org/html/2507.07955v2#S2.E4) фиксирует `p₁ = 1` —
первый токен всегда head. Здесь принуждение — следствие фактического
первого непустого chunk `List.splitBy`, а не learned prior и не routing-решение;
gate-механика Q/K, cosine, порога `≥ 0.5` и normalization epsilon не
моделируется. На paired route C214 (`adjacentPairs` с dummy seed `(a,a)`)
той же теоремой переносится
[`boundaryHeads_adjacent_first`](Hagi/Model/AdaptiveChunking.lean):
первым head paired маршрута оказывается ровно dummy seed `(a,a)`. Тем
самым seed на paired route структурно играет роль forced first head; его
θ-флаг, как и в C214, в разбиение не входит. Для θ-пар то же свойство
границ даёт [`theta_of_mem_adjacentHeads_tail`](Hagi/Model/AdaptiveChunking.lean):
каждый не-первой head paired маршрута удовлетворяет `θ p = true`.

Проверочный пример. При `boundary = (· == 1)` вход `[0,1,2]` даёт chunks
`[[0],[1,2]]` и heads `[some 0, some 1]`: первый head `0` принуждён,
хотя `boundary 0 = false`; не-первой head `1` лежит на границе.

Nodup честно не заявляется. Повторяющиеся граничные токены дают
повторяющиеся heads: при `boundary = (· == 1)` вход `[1,1]` даёт chunks
`[[1],[1]]` и heads `[some 1, some 1]`. Heads — позиции первых токенов
chunks фактического маршрута, а не множество уникальных значений.

Итого здесь одна публичная функция и семь публичных теорем:
`boundaryHeads`, `length_boundaryHeads`, `isSome_of_mem_boundaryHeads`,
`mem_of_mem_boundaryHeads`, `boundaryHeads_head?_cons`,
`boundary_of_mem_boundaryHeads_tail`, `boundaryHeads_adjacent_first` и
`theta_of_mem_adjacentHeads_tail`; private-помощник `head_boundary_of_mem_tail`
в публичный API не входит.

Census-измерение C215 (fresh,
`.tmp/C215/validation/census-report.md`, TSV SHA
bcd363f63a758a5d79843363a9a65183a0440134968bc60f9dc3408a20fdb711,
2928937 bytes / 14104 LF / 0 CR): OWNER 12270 → 12281 (модуль
AdaptiveChunking 51 → 62, +11: 8 публичных, 1 private и 2
compiler-generated), IR 1261 → 1264 (+3 codegen aux), CONSUMER 38 без
изменений, consumers byte-identical, fingerprint
12672784764919925193 → 4917100471297953757; NamePool delta 11/0.
Физический размер модуля 21722 → 27244 bytes (+128 строк против C214).

Это структурные свойства детерминированного фактического маршрута, а не
learned/differentiable/causal/online router и не утверждение о качестве
routing. Forced first head здесь — структурное следствие `List.splitBy`, а не
H-Net gate `p₁ = 1`; head selection H-Net отдельно отбрасывает non-head
представления, что не является этим восстановлением. Не доказаны полная
head-mask equivalence, Nodup heads, learned sparsity, encoder, Q/K
projection, cosine, zero-norm/tie, causal stability supplied
representations, stateful packed mask, BF16/Float-семантика, runtime,
минимальная память, training/held-out качество или глобальная
оптимальность HAGI. Логический счёт heads сам по себе не является
physical cost.
## 8. Конечный выбор архитектуры и качества оценки

Кандидат — действие с настоящим `step`, model safety, памятью и числом
операций; это контур выбора, а не дополнительный neural layer.

Основной вариант — минимизация ресурсов при quality floor.
[`minimumResource`](Hagi/Unified/QualityResourceMin.lean) выбирает
`(memory,operations)` в memory-first Lex только внутри eligible finite
семейства; [`minimumResource_next_quality_ge`](Hagi/Unified/QualityResourceMin.lean)
проверяет floor на фактическом successor. Пустое семейство не имеет
такого witness. Оба Lean-selectorа используют Classical.choose: это
noncomputable finite selection contracts, не native optimizer или runner.

Для реализации дискретного guard используем
[`finiteSelection`](Hagi/Unified/ExecutableController.lean):
фильтр supplied action list по Bool admission и `List.argmin` resourceCost.
[`finiteSelection_none_iff`](Hagi/Unified/ExecutableController.lean)
не выбирает ничего, только если все входные guards false;
[`selectionReport_guardCalls`](Hagi/Unified/ExecutableController.lean)
считает лишь logical guard calls. Если list покрывает все действия,
[`finiteSelection_cost_eq_minimumResource`](Hagi/Unified/ExecutableController.lean)
сравнивает стоимость с mathematical minimum в integer-cast модели.
Это исполняемый discrete selection, не вычисление raw CE на ℝ.

При оценке значения с абсолютной ошибкой не более eps на всех successors
используем conservative floor, равный истинному floor плюс eps, и
[`robustMinimumResource`](Hagi/Unified/RobustResourceMin.lean):
[`robustMinimumResource_actual_quality_ge`](Hagi/Unified/RobustResourceMin.lean)
даёт истинный floor, но cost-min только среди certified family. На конечном `I`
для [`argmax_select_certified`](Hagi/Budget/CertifiedArgmax.lean) требуем
`0≤eps`, `∀k, |GammaHat k-Gamma k|≤eps`, estimated argmax
`∀k, GammaHat k≤GammaHat sel` и gap `2eps<GammaHat sel-GammaHat k`
для всех `sel≠k`; без разрыва не объявляем истинный argmax.
При ratio `Gamma/K` ещё требуем `K>0`, budget-feasibility
`∑a alloc_a*K(idx_a)≤B`;
[`budget_allocation_dominance`](Hagi/Dynamics/ControllerPolicy.lean)
действует лишь при доказанном максимуме ratio, `Gamma≥0` и nonnegative allocations.

Структурный graph filter опционален:
[`withStructuralConstraint`](Hagi/Contracts/SchellingCandidateSelection.lean)
добавляет local compatible quota и top-to-bottom reachability к уже
существующим safe/caps. Это finite Schelling admission, не percolation,
динамика сходимости или доказательство качества сети.

Для decoded finite codebook фиксируем `e`, decoder и `X`, конечный nonempty `V`,
`IsProbSys p`, `0<n`, `0<eps`, после чего оцениваем выбранные
baseline/candidate на новых categorical samples.
[`codebook_raw_selected_population_mean_gap_lower_confidence`](Hagi/Model/CEHeldout.lean)
даёт числовой lower confidence для raw-CE gap с множителем `61965^G` и
радиусом `eps/ceBound X`. Это fixed-family finite-product вероятностная
оценка, не representative-IID/deployment guarantee. Для отдельного
subgaussian risk gate на конечном nonempty `V` требуем `∀v, 0<q v`,
`∑v qv=1`, `T>0`, `0<σ²` и `0<α<1`, а также subgaussian CGF для centering
значений при всех `t` и всех `c>0`. [`anytime_safe_threshold`](Hagi/Probability/CertifiedEstimator.lean)
использует порог `μ+sqrt(2σ²log(T/α))`: вероятность того, что хотя бы
одно из T значений достигает порога, не превосходит α.

### 8.1 Префиксная Freedman-confidence для банка raw CE

Фиксируем конечный банк кодов `i : Fin m`, codebook equivalence `e`,
матрицу признаков `X` и горизонт `T`. Для состояния `a`, следующего
состояния `b` и заданного марковского ядра `K` полагаем

```
F_i(k,a,b) = CE(b.2, ceLogits X (decodeJoint e (a.1 i))),
μ_i(k,a)   = E_(b∼K(k,a)) F_i(k,a,b),
g_i        = F_i − μ_i,
v_i(k,a)   = E_(b∼K(k,a)) (g_i(k,a,b))².
```

Это исходная, не нормированная CE. Из `0 ≤ F_i ≤ ceBound X` получаем
`|g_i| ≤ ceBound X`; центрирование `E g_i = 0` является определением,
а не дополнительным статистическим допущением. Выбираем `r > 0`, `V ≥ 0`
и используем один `historyLaw initial K T T` для всего банка.
[`raw_bank_freedman_maximal_confidence`](Hagi/Model/CEMarkovMaximalConfidence.lean)
даёт нижнюю границу математического ожидания индикатора

```
∀ i, ∀ j ≤ T, historyCounter v_i T j ≤ V →
  |historyAdditive g_i T j| < r,
```

равную `1 − 2*m*(T+1)*exp(−r²/(4*(V + ceBound X*r)))`.
Это одновременная оценка всех ограниченных префиксов, а не только
последнего времени. Она следует из per-member Freedman и union bound:
коэффициент не объявляется оптимальным, а при величине нижней границы,
не обещающей положительную вероятность, результат просто неинформативен.
При `m=0` событие вакуумно и индикатор равен единице; искусственный член
банка не создаётся. При ненулевом counter `V=0` ничего хорошего автоматически
не обещается. Это вероятностный аудит на заданном ядре, не утверждение
о произвольном времени остановки, попутном selection, обобщении
установленной производительности, CE-обучении или strict `StepCert`. Для детерминированного accepted CE-шага
по-прежнему нужны весь его guard и его отдельные предпосылки.


На уже зафиксированной истории можно задать baseline `b`, селектор `σ ω`
и bounded prefix `τ ω ≤ T`. Здесь `σ` и `τ` — снабжённые функции всей
history, включая последующее состояние; одна эта проверка не делает их
адаптированной или causal политикой. Обозначим сумму raw CE до `τ ω` через
A_i, сумму её conditional PMF mean через M_i, а residual через g_i.
Если одновременное prefix confidence-событие выполнено, обе границы
`historyCounter v T (τ ω) ω ≤ V` для `b` и `σ ω` выполнены и
`2*r < A_b − A_(σ ω)`, то
[`raw_bank_selected_prefix_conditional_ce_gap_pos_of_good`](Hagi/Model/CEMarkovSelectedPrefix.lean)
доказывает `0 < M_b − M_(σ ω)`. Разложение `A_i = historyAdditive g_i + M_i`
и `|historyAdditive g_i| < r` делают conditional gap не меньше raw gap
минус суммарный radius `2r`; условие hobs остаётся посылкой.

Это сравнение на guarded realization, а не безусловная граница
ожидаемого риска или обещание оптимального селектора. Одно центрирование
`g = F − μ` сохраняет весь observed gap, поэтому здесь не возникает слабого
радиуса `r` или потерянного raw residual. При `τ ω = 0` premise `2r < 0`
несовместим с получаемым из good `0 < r`: нулевой prefix не является
наблюдаемым улучшением. Результат не создаёт CE-training, causal stopping,
произвольное stopping time, held-out качество, `StepCert` или ускорение;
для детерминированного commit по-прежнему необходимы полные guards.
## 9. Исполнение: guards, router и охлаждение

Для произвольного `inputFor(S)` сначала вычисляем proposed successor и
лишь потом commit. [`guardedBatchTrainStep`](Hagi/Contracts/BatchCEStepCertificate.lean)
принимает его только если `0≤opCost≤budget` и CE каждого supplied sample
не увеличивается; иначе возвращает `S`.
[`batchSampleCE_guardedBatchTrainStep_le`](Hagi/Contracts/BatchCEStepCertificate.lean)
подтверждает samplewise non-regression. Не принимаем post-energy автоматически:
оно проверяется на настоящем successor.

В более общем состоянии [`joint`](Hagi/System/GrowthState.lean)
действительно обновляет `params := params - sp.eta • stepDir`.
Но [`potential_joint`](Hagi/System/GrowthState.lean) требует
`0<L`, `0≤eta≤1/L`, alignment, явной `h_emp_smooth` и measured
`effects.jointEnergy`; только тогда

```
Φ(joint S)-Φ(S) ≤ -gainJoint S + riskJoint S.
```

`gainJoint=eta‖stepDir‖²/2`, `riskJoint=effects.jointRisk`; protected risk
не заменяется gain. Для длинного цикла используем высокоуровневый commit/hold
[`gate_never_increases`](Hagi/Unified/CertifiedLoop.lean) лишь с
доказанным implication для принятого successor, а не с желаемым результатом.

Для router экспертов отдельно допустимый bounded-loss Hedge:
[`ewWeight`](Hagi/Autonomy/HedgeSurvivor.lean) обновляет
`w_{t+1,i}=w_{t,i}exp(-eta l_{t,i})`, [`ewNorm`](Hagi/Autonomy/HedgeSurvivor.lean)
нормализует веса. Если `0<eta≤1` и `0≤l_{t,i}≤1`, то
[`router_regret_bound`](Hagi/Autonomy/Hedge.lean) даёт для любого эксперта

```
A_T-L_T(i) ≤ log(card ι)/eta + eta T/2.
```

Это regret bounded-router, не снижение CE backbone и не runtime-optimality.

Когда router задан как Gibbs `softDef(-L/T)`, положительные `T` дают
[`gibbs_mixture_quality`](Hagi/Energy/Cooling.lean):
`∑w_iL_i ≤ m + T log(card ι)` для достигнутого finite minimum `m`.
Можно охлаждать по `T_t=T0 α^t`, `0<α<1`; для `0<T0,δ`, `0<θ<1`
точной stop bound относительно `exp(-δ/T_t)` даёт
[`thermostat_stop`](Hagi/Growth/Thermostat.lean).
Используем этот закон только на конечном energy family. Адаптивную
piecewise dynamics и универсальный analytic entropy limit сюда не подставляем.

## 10. Сборка рецепта и граница результата

Порядок одного цикла:

1. задать experts/core/residual, проверить parameter и routing budgets;
2. выбрать initial HNet ratio и разрядность только в их declared models;
3. вычислить current residual gradients и supported propensity;
4. взять общий `D̄`, вычислить `Ā,Q̄,eta_b`, иначе certified `D` или
   явный min-norm;
5. сформировать proposed successor, измерить каждую sample CE, риск и цену;
6. принять только guarded/resource-certified successor, иначе hold;
7. упаковать принятое представление, сложить все error terms, затем
   оценивать выбор на новых данных fixed codebook, не на том же CE-чеке.

Минимизируются отдельно: supplied-batch CE, selected-estimator MSE,
quantization/certification error, declared resources, HNet cost.
Доказанной совместной или глобально оптимальной архитектуры/тренировки,
held-out преимущества, physical FLOP/time saving нет. Это ограниченный
research-model recipe: исполняемые определения, finite certificates и
явные измеряемые предпосылки не смешиваются.

## 11. Каноническое ядро сертификации (Hagi/Cert/Core.lean)

Тонкий интерфейс сертифицированных переходов (master plan v3, Track
S1+S2), без зависимостей от остальной библиотеки:

- `SystemMetrics S TaskId` — objective, risk, budget (S → ℝ) и task-тег;
- `StepObligations TaskId` — отдельная структура obligations с floor;
- `FloorsKept` — `∀ t, obl.floor t ≤ M.objective s`;
- `CertStep` — прогресс: `0 < drop`, `objective s' ≤ objective s − drop`,
точные законы потребления `budget s' = budget s − budgetSpend`,
`risk s' = risk s − riskSpend` с `0 ≤ budget s'`, `0 ≤ risk s'`,
плюс floorsKept; производные оценки `CertStep.budgetBound` /
`CertStep.riskBound`;
- `HoldStep` (`s' = s`, floors kept) всегда доступен через `HoldStep.id`;
  `TransitionStep` = progress | hold.

Законы композиции и телескопа:

```
CertStep.trans h₁ h₂        -- тот же obl: drop'ы и spend'ы складываются
CertStep.trans' h₁ h₂ h_fl  -- obl₂ ⊵ obl₁ поточечно: композиция против obl₁
trajectory_telescope n t steps :
  M.objective (t n) ≤ M.objective (t 0) − ∑ j ∈ Finset.range n, (steps j).drop
```

`FloorsKept` — независимое поле, не выводится из descent (descent
связывает objective одного состояния с другим, floors — разные
обязательства); держится посылкой каждого шага и переносится
композицией. Дублирование имени `CertStep` с
`Hagi.Unified.HonestTransition.CertStep` — транзиторный долг
(см. `.omc/tech-debt.md`); поглощение старой структуры — Track S3.

## 12. BF16-гард для batch-шага и переход в Cert/Core (C230)

Срез двухступенчатого gate (addendum A5): стадия 3a (pre-screen)
теперь формально заземлена. Сертифицированный спуск — точное
выражение C223 `2·batchAlignment²/batchLogitRangeSquare`
(`batchLoss_logitSafeStep_le_residual`), НЕ сокращение «2A²/R̄'²».

BF16-гард — посылка, а не вывод: если логитный апдейт проходит через
BF16-представление с равномерной по-логитной ошибкой

```
|ceLogits (X b) θbf v − ceLogits (X b) (batchLogitNextParameters X θ y) v| ≤ eps
```

и строгий gate `4·eps < 2·A²/R'` выполнен, то реальный bf16-следующий
параметр строго уменьшает истинный batchCEObjective на
`Δ = 2·A²/R' − 2·eps > 0`:

```
batchLoss_le_of_logitPerturbation : per-logit eps → потеря сдвигается ≤ 2·eps
bf16_guarded_ceRange_descent_le   : gate → batchLoss θbf ≤ batchLoss θ − (drop − 2·eps)
bf16_guarded_ceRange_descent      : gate → ∃ Δ > 0, batchLoss θbf ≤ batchLoss θ − Δ
```

Средний штраф возмущения равен `2·eps` (2-липшицевость one-hot CE,
`CEQuantized.ceOneHot_le_of_abs_sub_le`); gate держит 2× запас.
Режим `eps = 0` (`bf16_exact_binade_ceRange_descent`) — точный logit-
readback; на уровне кодов это сертифицировано
`BF16Delta.exists_sameBinade_difference` (одинаковый положительный
нормальный binade ⇒ разность представима точно), но перенос ℚ→ℝ не
мостится автоматически, поэтому eps=0-теорема берёт точное равенство
логитов посылкой. Универсального утверждения о bf16-округлении НЕТ
(контрпример: θbf=(1,2) на identity-признаках строго УВЕЛИЧИВАЕТ
потерю).

Переход в Cert/Core: `batchCEMetrics` (objective = истинный batchLoss
на EuclideanSpace-носителе параметров, risk/budget = константные
остатки; R1-полярность «риск-остаток = лимит − защищённый риск»
даётся вызывающей стороной — носитель GrowthState в карантине
Legacy), `batchCE_bf16_transitionStep_progress` (progress-ветка:
gate активен, разность «риск-остаток − операционный риск»
неотрицательна, drop = 2·A²/R' − 2·eps),
`batchCE_transitionStep_hold` (hold-ветка через `HoldStep.id`).
Генерические адаптеры — `Hagi/Cert/Adapters.lean` (слой 2, импортирует
только Cert.Core): `descentCertStep`, `holdTransition`,
`protectedRisk_le_of_riskRem` (остаток риска ядра ⇒ защищённый риск
под лимитом). Операционный риск остаётся символическим до появления
медленного consumer'а. Rewiring BatchCEAlignmentBudget
(`rangeCurvature` против более точного `batchLogitRangeSquare`) —
отложен (см. `.omc/tech-debt.md`, R2).
