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
[`ew_regret`](Hagi/Autonomy/HedgeSurvivor.lean) даёт для любого эксперта

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
