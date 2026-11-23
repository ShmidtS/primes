## Архив (исторические секции и полный журнал)

Полный дожатый журнал и не-файловые исторические секции —
git-история: `git show b3939aa5:STATUS.md`.

## Hagi/Architecture/

- **`AlignedMerge.lean`** — `frobSubord`: для вещественной матрицы `M` и вектора `w` выполняется `(M *ᵥ w) ⬝ᵥ (M *ᵥ w) ≤ frobSq M * (w ⬝ᵥ w)`.
- **`Configuration.lean`** — `config_storage_beats_dense`: при `N * r < d` и `0 < d` хранение `(N * r) * d` параметров строго дешевле `d * d`.
- **`CortexFiber.lean`** — `fiberCross`: из `Uᵀ * V = 0` следует `(U *ᵥ z) ⬝ᵥ (V *ᵥ w) = 0`.
- **`ManifoldHyperConn.lean`** — `IsRowStochastic` / `IsDoublyStochastic`: premise-form гипотезы (неотрицательные элементы, суммы строк = 1, суммы столбцов = 1); Sinkhorn-балансировка не нужна и не утверждается.
- **`FactorRank.lean`** — `nonnegFactorization M k` означает точное разложение `M = W * H` с поэлементно неотрицательными `W`, `H`; `nonnegRank M` задаёт наименьшую допустимую внутреннюю размерность.
- **`FactorizedMerge.lean`** — `factorized_error_bound`: на конечном непустом `ι`, если для каждого `i` выполнено `‖R i - (W i - C)‖ ≤ δ i`, то `‖fullMerge W - (C + meanResidual R)‖` не превосходит среднего
- **`Heterarchy.lean`** — `no_global_ranking`: обращение доминирования `a` над `b` в одном контексте и `b` над `a` в другом несовместимо ни с одним `RankingConsistent`.
- **`LiveDelta.lean`** — `block_rank_le`: ранг низкорангового блока `Aᵀ * B` не превосходит `Fintype.card r`.
- **`OrthoInjection.lean`** — `fiberSplitOrtho`: при `IsOrthoCol U` остаток проекции удовлетворяет `Uᵀ * (A - U * (Uᵀ * A)) = 0`.
- **`ResidualSplit.lean`** — `residual_gate_two_sided`: по определению `ResidualGateOn η E C P ↔ η * E - C - P > 0`.

## Hagi/Audit/Audit.lean

- `amgm_equality`: при положительных `Bn`, `t0`, `c`, `B` и `B^2 = Bn * t0 / c` выполняется `c * B + Bn * t0 / B = 2 * Real.sqrt (c * Bn * t0)`.

- `amgm_uniqueness`: при `0 < c`, `0 < B`, `0 ≤ Bn`, `0 ≤ t0` равенство в этой оценке обратно влечёт `B^2 = Bn * t0 / c`.

- `batch_T_min`: при `0 < B`, неотрицательных `Bn`, `t0`, `c` величина `(1 + Bn / B) * (t0 + c * B)` не меньше `t0 + c * Bn + 2 * Real.sqrt (c * Bn * t0)`.

## Hagi/Optimization/MirrorHedge.lean

- `hedge_step`: для вероятностного `p`, потерь `0 ≤ l i ≤ 1` и `0 ≤ eta ≤ 1` сумма `∑ i, p i * exp (-eta * l i)` не превосходит `1 - eta * ∑ i, p i * l i + eta ^ 2 / 2`.

- `hedge_telescope`: если `0 ≤ 1 + u t` для всех `t`, то `∏ t < T, (1 + u t) ≤ exp (∑ t < T, u t)`.

- `router_regret_bound`: при `0 < K`, `0 < eta` и посылке hsurv выполняется `A - Lstar ≤ Real.log K / eta + eta * T / 2`.

## Hagi/Autonomy/

- **`Insight.lean`** — `tldr_two_tier_safety`: если `B.mulVec x = 0`, то `(A * B).mulVec x = 0`; если дополнительно `kl ≤ ⟪dW, F dW⟫_ℝ / 2` и `⟪dW, F dW⟫_ℝ ≤ 2 * eps`, то `kl ≤ eps`.
- **`ParetoController.lean`** — `pareto_validity`: при `0 < omega i` для всех координат из `0 < dirTau u omega a` следует `0 < u a i`.
- **`SupervisorSafety.lean`** — `capacity_member_mono`: при положительных `A`, `N`, α, `b1`, `b2` и `b1 < b2` член `capMember A b N alpha` строго убывает по `b`.
- **`SupervisorViability.lean`** — `halving_mistake_bound`: если список примеров `L` реализуем некоторой гипотезой из конечного `H`, то `2 ^ mistakeCount H L ≤ H.card`.
- **`TTTStability.lean`** — `ttt_bibo`: из `abs W ≤ 1` следует `abs (W ^ T * x) ≤ abs x` для любого натурального `T`.

## Hagi/Budget/

- **`AnytimeCondensation.lean`** — `pointwise_upper_band`: при `0 < T`, если ни для одного `v` не существует `t < T` с `μ + u ≤ g v`, то `g v < μ + u`.
- **`BatchCap.lean`** — `sfo_global_min`: при `0 ≤ X`, `0 < c`, `0 ≤ Y` и `Y / c < s` точка `criticalS c Y` минимизирует `sfoCost X c Y` по таким `s`.
- **`BitAlloc.lean`** — `distill_chain_telescoping`: из `S k ≤ E k + delta k` для `k ≤ n` и `E (k + 1) ≤ S k` для `k < n` следует `S n ≤ E 0 + ∑ k ∈ Finset.range (n + 1), delta k`.
- **`BitAllocTermination.lean`** — `error_chain_descends`: если ошибка строго убывает на каждом соседнем шаге, то она строго убывает между любыми временами `m < k`.

## Hagi/Cert/CertifiedArgmax.lean

- `argmax_pair_certified`: при `0 ≤ eps`, `|GammaHat k - Gamma k| ≤ eps` и `2 * eps < GammaHat i - GammaHat j` следует `Gamma j < Gamma i`.

- `argmax_select_certified`: если sel максимизирует Γ̂ и отделён от каждого другого варианта больше чем на `2 * eps`, то sel максимизирует истинный Γ.

- `tie_ambiguity`: при `0 < eps` и `0 < delta < 2 * eps` существуют две разные истинные функции с противоположными максимумами, обе согласованные с одной `eps`-точной оценкой.

## Hagi/Budget/

- **`DesignOpt.lean`** — `spectral_tail_mono`: при `m ≤ m'` конечная сумма `(sigma j)^2` по индексам `j ≥ m'` не превосходит суммы по `j ≥ m`.
- **`ElementQuant.lean`** — `factor_quant_go`: если `‖dE - AB‖ = tail`, `‖AB - QAB‖ = qerr` и `tail + qerr < qdirect`, то `‖dE - QAB‖ < qdirect`.
- **`JointCost.lean`** — `nsIter_block_le`: при `2 ≤ N`, `0 < h` и `0 ≤ r ≤ h` стоимость `N * nsIter h h + 3 * nsIter r (N * h)` не превосходит `nsIter (N * h) (N * h)`.
- **`RankBudget.lean`** — `rankResidual_equalized`: при `0 < c j`, `0 < κ j`, `0 < lam`, равенстве `c j * κ j * exp (-κ j * rstar j) = lam * (m j + n j)` и одинаковой взвешенной стоимости распределений суммарный
- **`ThermoCondensation.lean`** — `inv_fact_mono`: `1 / (k + 1)! ≤ 1 / k!` для натурального `k`.
- **`TokenWeightBias.lean`** — `token_weight_decomposition`: при `0 < ∑ i, T i` токенно-взвешенное среднее `g` равно обычному среднему плюс выборочной ковариации `T` и `g`, делённой на среднее `T`.
- **`WaterFilling.lean`** — `exists_balanced_allocation`: для `0 ≤ c l` и любого натурального `B` существует натуральное распределение `f` с `∑ l, f l ≤ B`, при котором
- **`WeightedExpAlloc.lean`** — `weightedExpAllocation_budget`: на конечном непустом `ι` при `0 < κ i` и `0 < w i` построенное распределение точно удовлетворяет `∑ i, w i * weightedExpAllocation c κ w B i = B`.

## Hagi/Research/Legacy/MasterChallenge.lean

- `master_hagi_core_comparator`: при `0 ≤ lam`, `0 ≤ nu`, `0 ≤ epsQ` и `CorePremises S S' epsQ w` потенциал после перехода не превосходит исходного минус `verify.decrease`, плюс `lam * verify.riskSpend + nu * epsQ`.

- Та же теорема доказывает точное бюджетное равенство `S'.toGrowthState.budget = S.toGrowthState.budget - (verify S.toGrowthState).budgetSpend`; все условия `CorePremises` остаются посылками.

## Hagi/Cert/

- **`Core.lean`** — Каноническое ядро сертификации (master plan v3, S1+S2): `SystemMetrics` (objective/risk/budget/task как функции состояния), `StepObligations` (отдельная структура с floor), `FloorsKept`
- **`Empirical.lean`** — C245 (Phase 1, A7): `Empirical P` — типизированная обёртка эмпирических посылок (заместительный путь для голых `h_emp_*`; миграции нет, AssumptionScan остаётся): поля measuredLaw/tolerance

## Hagi/State/Views.lean

- C245 (Phase 1, A7): survey носителей состояния (TrainState — канон
спеки §4; GrowthState — legacy с GrowthStateViews (модуль слит в GrowthState); FunctionalState;
MachineProto/MeasureProto; NC-мир) + минимальный честный view:
`toSystemMetrics` (TrainState как `Hagi.Cert.SystemMetrics`:
objective = energy, risk = riskOf, budget = budgetOf, TaskId = Unit)
со спецификациями `toSystemMetrics_objective/_risk/_budget` (rfl).
Массовая унификация носителей — Phase 2/3.

## Hagi/Cert/Adapters.lean

- Генерические адаптеры между конкретными сертификатами спуска и каноническим ядром `Hagi.Cert` (импортирует только `Hagi.Cert.Core` — batch-CE-инстанциация живёт в Contracts из-за LayerLint).

- `zeroFloorObligations` и `floorsKept_zeroFloor` — тривиальные obligations (floor 0), держатся при неотрицательном objective.

- `descentCertStep`: положительный drop + реальный спуск + сохранённые уровни budget/risk (нулевой расход) + floors → канонический `CertStep`; `holdTransition`: FloorsKept → `TransitionStep` через `HoldStep.id`.

## Hagi/Challenge/MasterChallengeV3.lean

- `master_hagi_challenge_v3`: для цепочки `StepCert`, согласованных drops и spends, начального `FloorKept` и `0 ≤ b 0`, при `1 ≤ n` доказаны `obj (f n) < obj (f 0)` и `∑ t < n, drops t ≤ obj (f 0) - obj (f n)`.

- На конечном состоянии сохраняются `FloorKept`, `0 ≤ b n` и `b n ≤ b 0 - ∑ t < n, spends t`.

## Hagi/Contracts/

- **`BatchRangeBF16Cert.lean`** — BF16-гард для C223 batch-шага: certified drop — точное выражение `2·batchAlignment²/batchLogitRangeSquare`; по-логитная bf16-ошибка — ПОСЫЛКА, универсального утверждения об
- **`BatchCEAlignmentBudget.lean`** — C233 (R2): `batchLogitRangeSquare_le_rangeCurvature_mul_alignment` — без посылок, острая средняя `batchLogitRangeSquare X θ y ≤ rangeCurvature X * batchAlignment X θ y` (транзитивность
- **`BatchCEBestResidual.lean`** — `exists_alignment_le_fixedAlignmentCesaro`: при `0 < T` найдётся `t : Fin T`, чьё `batchAlignment` не превосходит среднее Чезаро за префикс.
- **`BatchCEGrowth.lean`** (вкл. BatchCEGrowthSelection и NaturalLean, слит C524) — `growthObjective_iteratedQuarantinedGrowStep_antitone`: цель `growthObjective` на точной последовательности итераций `quarantinedGrowStep` не возрастает.
- **`BatchCEBudgetGuard.lean`** — C233 (R2): `batchLogitCertifiedDrop` — острый сертифицированный residual `if batchLogitRangeSquare = 0 then 0 else 2·A²/R'` (ns `BatchCETrajectory`, `[Nonempty V]`)
- **`BatchCETrajectory.lean`** — `fixedBatchObjective_sum_certifiedDrop_le_telescope`: при непустом `V` сумма `batchCertifiedDrop` по префиксу не превосходит точную разность между начальной CE и CE после `T` фактических
- **`CEStepCertificate.lean`** — `coreParameters_ceTrainStep`: фактические параметры после `State.trainStep` совпадают с параметрами безопасного шага по категориальной CE.
- **`LogicChoiceCert.lean`** — Первый гибридный нейро-символьный сертификат (Track B7 item 3, addendum A4): выбор маски как CE-задача — 16 масок решётки Венна суть классы (`Fintype (Fin 4 → Bool)`), лог-линейная
- **`EMTrajectory.lean`** (вкл. ChangingEMTrajectory, слит C524) — `changingEMPath_nll_antitone`: при `∀ t a i, 0 < observationEvidence (c t a i).1 (c t a i).2 (y i)`, сохранении текущих пар (условие hKeep) и включении носителей текущих постериоров в
- **`GatedCEStepCertificate.lean`** — `gatedCEObjective_gatedCETrainStep_lt`: при непустом `V` и `0 < gatedAlignment X (coreParameters S) t` фактический `gatedCETrainStep` строго уменьшает целевую CE с гейтингом
- **`GatedCETrajectory.lean`** — `fixedGatedAlignment_sq_tendsto_zero_uniform`: при непустом `V` квадрат текущего `fixedGatedAlignment` для фиксированных входных данных стремится к нулю.
- **`GatedCEGradientNorm.lean`** — `gatedGrad` отождествляет градиент гейтированного одноцелевого CE с `-gatedDirection`; `gatedGrad_ofLp` даёт покоординатное равенство с `gatedResidualTranspose` без предположений сверх
- **`GatePipeline.lean`** — C264 (addendum A10, приоритет P1): ГЕЙТ-ТЕОРЕМА — пайплайн Python-гейта как он реально используется, в ОДНОМ Lean-модуле (состав: rescale → δ-расписание → union → P(false commit) ≤ δ).

## Hagi/Contracts/AuditLedger.lean

- C274 (audit E7): формальный audit ledger — Lean-мост Python
  HoeffdingAudit: alpha spending, disjoint cursors
  (proposal-independent slices как полуинтервалы [lo,hi) на ℕ),
  old-task harm, rejected consumption, repeat-task floors, final
  test untouched.

## Hagi/Contracts/GradientBottleneck.lean

- `logitGradM`: квадратный n×n комплексный матричный вид логит-градиента
  (вещественные записи коэрцированы) — носитель, требуемый Flywheel
  SVD API.

- `gradient_bottleneck_bound`: при посылке `rank Δ ≤ k` всякое достижимое
  логит-обновление `Δ` оставляет Frobenius-остаток не меньше
  квадратичного хвоста сингулярных чисел `logitGradM` за `k` — прямое
  следствие `eckart_young_lower_bound`. Вывод «голова ранга D ⇒
  ранг обновлений ≤ 2D» и нетривиальность хвоста (Prop A.5) отложены
  и не утверждаются; при `k ≥ n` оценка тривиальна.

## Hagi/Contracts/

- **`GuardedLogitTrajectory.lean`** — `guardedLogitPath_logitCE_antitone` и `guardedLogitPath_logitCE_tendsto_ciInf`: для фиксированного скалярного защищённого контроллера CE не возрастает и сходится к своей точной нижней грани.
- **`HadamardTernaryBridge.lean`** — `hadamard_satTail_zero_of_l2_bound`: при `s > 0`, `0 ≤ μ ≤ 1`, оценке `‖x‖₂ ≤ s·√(2^k)` и посылке μ-некогерентности `‖Hx‖∞ ≤ μ·‖x‖₂/√(2^k)` каждая координата ортонормального Адамара-образа
- **`LogitGrad.lean`** — `logitGrad z N c v = smax (z c) v − N c v`: строчный носитель логит-градиента CE; обобщает форму ceResidual на произвольные суб-вероятностные `N` (one-hot или частоты).

## Hagi/Contracts/IdentityMomentConvergence.lean

- `meanPrediction` при заданном θ усредняет по supplied batch отдельные
  `softDef (ceLogits ...)`; `empiricalTarget` так же усредняет
  `(Pi.single (y b) 1 : Fin n → ℝ)`. Это средние вероятностей и one-hot
  меток, а не среднее параметров или logits.

## Hagi/Contracts/BudgetedParetoStepContract.lean

- `budgetedParetoStepContract` для `[Fintype V]` и `0≤opRisk` переводит
  реальный `budgetedParetoBatchTrainStep` в обычный `StepContract`.
  Для его successor `T` поле `StepContract.decrease` равно старому минус
  новому `batchCEObjective`, `StepContract.riskCost = T.saf.risk-S.saf.risk`,
  а `StepContract.budgetSpend = S.res.budget-T.res.budget`.

## Hagi/Contracts/BudgetedParetoStepCert.lean

- `budgetedParetoStepCert` возвращает существующий `StepCert` для реального
  `T = budgetedParetoBatchTrainStep X y S opCost opRisk write`.
  Требуются положительный `batchRangeSquare`, `0≤opRisk`, `opRisk≤riskLim`,
  исходный `FloorHeld S floor` и полная активная guard-посылка: nonnegative affordable opCost и CE non-regression для каждого supplied sample на каноническом
  `batchTrainStep`. Строительство использует существующий
  `batchTrainStepCert` и accepted equality, а не новый guard или record cast.

## Hagi/Contracts/ObjectiveTrajectory.lean

- `sum_le_of_sum_two_mul_div_le`: при `0 < κ` и общей оценке `∑ t < T, 2 * f t / κ ≤ A` для каждого `T` следует `∑ t < T, f t ≤ κ * A / 2`.

- `summable_and_tsum_le_of_sum_two_mul_div_le`: при дополнительном `0 ≤ f t` последовательность `f` суммируема и `∑' t, f t ≤ κ * A / 2`.

- `exists_le_of_sum_two_mul_div_le`: при `0 < T` найдётся `t < T` с `f t ≤ κ * A / (2 * T)`; это оценка некоторого элемента префикса, а не всех поздних элементов.

## Hagi/Research/

- **`SchellingCandidateSelection.lean`** — `mem_feasible_withStructuralConstraint`: допустимость контроллера `a` в усиленной задаче эквивалентна конъюнкции исходной допустимости `a ∈ feasible p M C` и
- **`SchellingMarkovRouting.lean`** — `walkHistory_support_of_mem_feasible_withStructuralConstraint_of_adjSupported`: для ядра `K`, согласованного со смежностью допустимого графа, из каждой верхней вершины `s` существуют нижняя

## Hagi/Contracts/StepCertificate.lean

- `trainStep_actualDescent`: `energy (trainStep S u) = energy S - (2 * u.eta * (∑ i, S.model.weights i * u.grad i) - u.eta ^ 2 * (∑ i, u.grad i ^ 2))`.

- `trainStepMinimalCert`: при `0 < u.eta` и `2 * (∑ i, S.model.weights i * u.grad i) > u.eta * (∑ i, u.grad i ^ 2)` строит `CertStep` с положительным фактическим уменьшением энергии.

- `trainStepCert`: при дополнительных ограничениях риска, стоимости, исходного `FloorHeld` и бюджета строит полный `StepCert`; сохранение качества использует неизменность `evaluate` при параметрическом шаге.

## Hagi/Core/

- **`Ambig.lean`** — `lse_shift`: `lse (fun v => z v + c) = lse z + c`.
- **`Attention.lean`** — `attention_error_damped_sum`: при `0 ≤ p i` норма ошибки взвешенного выхода не превосходит `∑ i, p i * ‖e i‖`.
- **`BlockDiag.lean`** — `blockDiagonal'_mulVec_apply`: блок `k` действия `blockDiagonal' M` на стекованный вектор равен `M k *ᵥ` соответствующему срезу вектора.
- **`Concat.lean`** — `lse_mean_le_mean_lse`: для непустого `k`, `N ≠ 0` и `N` семейств логитов `lse` их поэлементного среднего не превосходит среднего отдельных `lse`.
- **`Element.lean`** — `delta_rank_le`: ранг `A * B` с внутренним типом `r` не превосходит `Fintype.card r`.
- **`ErrorProp.lean`** — `propagate_bound`: при `0 ≤ α`, `‖J_l‖ ≤ α` и `‖r_l‖ ≤ ρ` норма ошибки после `L` шагов не превосходит `α ^ L * ‖δ₀‖ + (∑ i < L, α ^ i) * ρ`.
- **`F3Root.lean`** — `root_invariance`: `(vi + u)^2 - (vj + u)^2 = (vi^2 - vj^2) + 2 * u * (vi - vj)`.
- **`FrobOuter.lean`** — `frobSq_outerSum`: для ортонормальных семейств `u`, `v` квадрат Фробениусовой нормы `outerSum s σ u v` равен `∑ i ∈ s, (σ i)^2`.
- **`Hadamard.lean`** — `hadamardReal_mul_transpose`: `hadamardReal k * (hadamardReal k)ᵀ = (2 ^ k : ℝ) • 1`.
- **`Kronecker.lean`** — `conjTranspose_kronecker_mul`: из `Aᴴ * A = 1` и `Bᴴ * B = 1` следует `(A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1`.
- **`Lift.lean`** — `parentPreservingQ_mul_transpose`: матрица `parentPreservingQ` ортогональна, то есть `Q * Qᵀ = 1`.
- **`Merge.lean`** — `head_prerotation`: при `Q * Qᵀ = 1` выполняется `(W * Qᵀ) *ᵥ (Q *ᵥ x) = W *ᵥ x`.
- **`Mix.lean`** — `mixed_invisible`: если для каждого `b` выполнено `∑ a, Q a b • W a = W b`, то `mixedLogits Q W h = plainLogits W h`.
- **`NonlinearStep0.lean`** — `perBlock_gauge_equiv`: если каждый поблочный модуль коммутирует со своим гейджем, то `PerBlockLayer` удовлетворяет `GaugeEquiv`.
- **`RealF3Ortho.lean`** — `dftPow_mul_conjTranspose`: комплексная матрица `dftPow k` унитарна, `dftPow k * (dftPow k)ᴴ = 1`.
- **`Ridge.lean`** — `ridge_optimal`: при `0 ≤ lam` всякое `w₀`, удовлетворяющее `ridgeNormalEq X y lam w₀`, является глобальным минимизатором `ridge X y lam`: для любого `w` выполняется
- **`RoPEMoments.lean`** — `rope_score_delta`: при `m ≤ n` поворотный скор равен `pairInner x (rotVec θ (n - m) y)`; `rope_translation_shift` сохраняет его при общем сдвиге позиций.
- **`RootContrast.lean`** — `filter_partition_sum`: суммы `s j^2` по индексам `j < r` и `r ≤ j` внутри `range m` вместе равны полной сумме.
- **`Select.lean`** — `meanBound_greedy`: если `newcomer ≤ mean`, то `(N * mean + newcomer) / (N + 1) ≤ mean`.

## Hagi/Data/

- **`BoolVenn.lean`** — Булевозначная решётка Венна для 16 функций двух переменных (Track B7, addendum A4): `atomIdx`/`vennBool` — маска как таблица истинности; `venn_universal` — каждая `Bool → Bool → Bool`
- **`BytePatch.lean`** — `seg_length`: длина сегмента `seg s a b` равна `b - a` в натуральной арифметике.
- **`DBridge.lean`** — `dQuad_nonneg`: при `0 ≤ pW v` и `∑ v, pW v = 1` квадрат взвешенного среднего `d` не превосходит взвешенного второго момента.
- **`DField.lean`** — `kl_product`: для строго положительных `p1`, `q1`, `p2`, `q2` и нормированных `p1`, `p2` KL продуктовых распределений равно `klDef p1 q1 + klDef p2 q2`.
- **`DataMixing.lean`** — `mixing_loss_convex`: при `0 ≤ K` функция `rho ↦ mixingLoss K c rho` выпукла на всём пространстве пропорций.
- **`Distill.lean`** — `kl_eq_ce_gap`: для строго положительных `q`, `p` выполняется `klDef q p = crossEntropy q p - crossEntropy q q`.

## Hagi/Probability/FannesPinsker.lean

- `log_sub_le_div`: при `0 < a ≤ b` выполняется `log b - log a ≤ (b - a) / a`.

- `abs_log_sub_le`: для положительных `a`, `b` справедливо `|log a - log b| ≤ |a - b| / min a b`.

- `entropy_lipschitz_smooth`: при `0 < delta ≤ 1` и `delta ≤ p v, q v ≤ 1` для всех `v` выполняется `|H(p) - H(q)| ≤ (2 / delta + 2 * log (1 / delta)) * TV(p, q)`; полная граница Фаннеса с сингулярным членом не доказывается.

## Hagi/Data/PACBayes.lean

- `log_weighted_jensen`: для строго положительной нормированной `q` и строго положительного `x` сумма `∑ i, q i * log (x i)` не превосходит `log (∑ i, q i * x i)`.

- `gibbs_variational`: для строго положительных нормированных `q`, `p` выполняется `∑ i, q i * f i ≤ ∑ i, q i * log (q i / p i) + log (∑ i, p i * exp (f i))`; вероятностный шаг PAC-Bayes здесь не доказывается.

## Hagi/Research/

- **`PPT.lean`** — `truncation_bias`: если ядро `K` не выходит из `S`, а `pi` стационарно, то существование `y₀ ∉ S` с `0 < pi y₀` невозможно.
- **`PPTCanonical.lean`** — `discovery_prob_stationary_identity`: на конечном непустом измеримом пространстве с измеримыми одноэлементными множествами для неотрицательной нормированной `pi` вероятность события

## Hagi/Dynamics/

- **`EndpointContraction.lean`** — `endpoint_bivariate_bound`: при `0 ≤ κ < 1`, `0 ≤ β` и `x (t + 1) ≤ κ * x t + β * c t` выполняется `x T ≤ κ^T * x 0 + β * ∑ i < T, κ^i * c (T - 1 - i)`.
- **`GrowthBridge.lean`** — `capability_exp_growth_floor`: при `0 < alpha`, `0 ≤ C 0`, `C (t + 1) ≥ C t * (1 + alpha)^(s t)` и `N ≤ ∑ t < T, s t` выполняется `C T ≥ C 0 * (1 + alpha)^N`.

## Hagi/Probability/GibbsCore.lean

- `partition_hot_limit`: на конечном непустом `V` сумма `∑ v, exp (-(ℓ v) / T)` при `T → +∞` стремится к `Fintype.card V`.

- `two_level_meanEnergy_strictMono`: для двухуровневой системы с `0 < ε` средняя энергия `ε / (1 + exp (ε / T))` строго возрастает при `0 < T₁ < T₂`.

- `partition_cold_limit`: если `0 ≤ ℓ v`, то при `T → 0⁺` сумма статистических весов стремится к числу состояний с `ℓ v = 0`.

## Hagi/Energy/

- **`EntropyProduction.lean`** — `exp_neg_entropyProduction`: при `0 < p x` и `0 < q x` выполняется `exp (-entropyProduction p q x) = q x / p x`.
- **`FreeEnergy.lean`** — `free_energy_gap`: при строго положительных `q`, `p` и `∑ v, q v = 1` выражение `∑ v, q v * ((-tau) * log (p v) + C) + tau * ∑ v, q v * log (q v)` равно `tau * klDef q p + C`.
- **`Landauer.lean`** — `landauer_sandwich`: для положительных нормированных wPre, wPost, `0 < cUnit` и посылок `cUnit * klDef wPost wPre ≤ dissipation` и `dissipation ≤ kappa * s * quantErr` следует

## Hagi/Energy/PairwiseCategorical.lean

- Track E1 (addendum A9, CRAM 2611.17309): дискретная парная энергия
  `pairwiseEnergy B K x = Σ B i (x i) + (1/2)·pairwiseInteractionSum K x`
  на конечных переменных/доменах; КОНВЕНЦИЯ: ordered-pair сумма
  Σ_{j≠i}, 1/2 вне её, симметрия K НЕ предполагается (пин E1).

## Hagi/Energy/

- **`SingleCellDescent.lean`** — Track E2 (addendum A9 + A9-supplement, CRAM 2611.17309): дискретное одно-клеточное ядро — точная дельта энергии переноса ОДНОЙ клетки.
- **`EnergyCoordinateStep.lean`** — Track E2: координатная минимизация как ТОЧНЫЙ KL-сертификат — безопасная дискретная альтернатива Эйлеровым шагам непрерывного потока (собственное предостережение статьи CRAM).

## Hagi/Energy/EnergyFlow.lean

- Track E2 (уточнение A9-supplement): непрерывная часть, разделённая на
  (1) алгебраические тождества и (2) supplied-trajectory теорему —
  БЕЗ какого-либо ODE-existence API.

## Hagi/Energy/

- **`PoEBound.lean`** — `poe_logZ_second_order`: для конечных `V` (непустого) и `K`, весов `w i ≥ 0` с суммой 1 и границы `R i` на размах `z i − Σₗ w l·z l` доказано
- **`PreNorm.lean`** — `var_recursion`: для вещественных `x b s` при условии перекрёстного зануления `x * b = 0` доказано точное `(x + s*b)^2 = x^2 + s^2*b^2`; общая «независимость ветвей» в утверждение не входит.
- **`Quantizer.lean`** — `gridQ_error` и `gridQ_idem`: при `Δ > 0` ближайший узел `gridQ Δ x = Δ·round(x/Δ)` отличается от `x` не более чем на `Δ/2`, а повторное квантование не меняет узел.
- **`STEStep.lean`** — `tern_distortion_round`: для нормированного `x ∈ [-1,1]` округление `tern x` имеет ошибку `|x − tern x| ≤ 1/2`.
- **`Ternary.lean`** — `tritEncode_injective`: кодирование пяти тритов в base-3 инъективно; используемое арифметическое условие — `3^5 ≤ 2^8`.

## Hagi/Ensemble/

- **`MergePrice.lean`** — `merge_price_quad`: при `M − Wi = −dev` квадратичная модель `QuadModel xs Wi M` точно равна `sigmaPrice xs dev`.
- **`GapLaw.lean`** — `twoGap_nonneg`: для строго положительного `p` с суммой 1 зазор `twoGap p d` неотрицателен; `twoGap_zero_iff` утверждает равенство нулю тогда и только тогда, когда `d u = c` для некоторой
- **`Hoeffding.lean`** — `twoGap_bounded`: для вероятностных `p`, `M > 0` и условия `|d u − d v| ≤ M` доказано `Hagi.twoGap p d ≤ M^2/4`.
- **`PolicyCompatibility.lean`** — `integration_rejects_far_teacher`: если `Dmax < Dpolicy`, то `MOPDApproved twoGap price Dpolicy Dmax` ложен независимо от величин `twoGap` и price.
- **`QFormerBridge.lean`** — `punctured_unbiased`: для неотрицательных весов `W b` с маргиналиями `Σ_{b:b i=t} W b = p` при `t=true` и `1−p` при `t=false` доказано `Σ_b W b*puncturedSum x b = p*Σ_i x i`.
- **`SigmaKernel.lean`** — `quad_form_factorization`: для `Σ = Aᵀ*A` доказано `v ⬝ᵥ (Σ.mulVec v) = (A.mulVec v) ⬝ᵥ (A.mulVec v)`; `quad_form_zero_iff` даёт равенство нулю ровно при `A.mulVec v = 0`.
- **`UniformCert.lean`** — `two_sided_good_point`: для положительных нормированных `w`, ограниченных центрированных `d k` и `2*card K*exp(−2ε²/(b−a)^2) < 1` существует `v`, для которого `|d k v| < ε` при всех `k`.

## Hagi/Research/Legacy/

- **`HAGICertWitness.lean`** — `hagicert_nonvacuous`: построены последовательности состояний и числовые параметры, для которых выполнен `HAGICert … T`. Это свидетель совместимости формального контракта на конкретных
- **`Nonvacuity.lean`** — `merge_energy_bridge`: для midpoint-логитов доказано точное `CE(mid) = (CE(z₁)+CE(z₂))/2 − jensenGap z₁ z₂`, а также неотрицательность зазора.
- **`NonvacuityHorizon.lean`** — `sat_step_laws`: при `γ ≠ 0` параметрическая траектория одновременно удовлетворяет шагу `C(t+1)=C(t)+γ*F(t)` и насыщению `C(t+1)=C(t)+σ*(Cstar−C(t))`.

## Hagi/Benchmarks/QuadLoopWitness.lean

- `quadE_qhalf`: после `t` полушагов энергия равна `quadE a (qhalf a x t) = (1/4^t)*quadE a x`.

- `quad_loop_horizon`: если `quadGrad a x ≠ 0` и `n ≥ 1`, то `quadE a (qhalf a x n) < quadE a x`; `quad_witness_T3` и `quad_witness_T10` — конкретные специализации.

## Hagi/Research/Legacy/QuadraticConcrete.lean

- `quad_core_premises`: для любых `a : ℝ` и `w : Fin 5 → ℝ` построены квадратичные состояния, удовлетворяющие `CorePremises (quadGen a) (quadGen' a) 0 w`.

- `quad_kappa_at0` даёт `‖fderiv ℝ (quadE a) 0‖ ≤ 1+|a|`; `quad_conj13` проверяет соответствующее неравенство для квантованного скалярного шага с тем же коэффициентом.

## Hagi/Benchmarks/

- **`QuadraticEndToEnd.lean`** — `qStep_descent`: при `0 < eta < 1` и `x ≠ a` шаг `qStep` строго уменьшает `qLoss a`.
- **`QuarticWitness.lean`** — `quartic_two_steps`: построенные два шага дают `qE w2 < qE w0`, сохраняют `FloorKept qMeasured w2 qFloor` и удовлетворяют явному бюджетному условию `0 ≤ 9 ∧ 9 ≤ 10−1`.

## Hagi/External/Diversity.lean

- `grad_dist_polarization`: во внутреннем пространстве доказано `‖a−b‖² = ‖a‖²+‖b‖²−2⟪a,b⟫`.

- `gittins_index_max`: на любом непустом конечном типе существует индекс, максимизирующий заданную вещественную функцию idx.

- `merge_init_head_start`: из `meanCE < logV` следует `0 < logV − meanCE`. Теорема фиксирует только этот арифметический зазор, а не эмпирическое превосходство всего обучения.

## Hagi/External/Flywheel/

- **`CoherenceCharacterization.lean`** — `trunc1_spectral_optimal_aux`: для любой матрицы `N` ранга не более 1 доказано `‖A−truncatedSVD A 1‖ ≤ ‖A−N‖` в норме соответствующего операторного инстанса.
- **`CourantFischer.lean`** — `courantFischer_maxMin_bounds`: для эрмитовой `A` и `k>0` head-подпространство достигает `rayleighInf ≥ λ_{k−1}`, а всякое `k`-мерное ненулевое подпространство имеет `rayleighInf ≤ λ_{k−1}`.
- **`EckartYoungLower.lean`** — `eckart_young_lower_bound`: для любой `B` с `rank B ≤ k` доказано `∑ i, (truncatedSingularValues_tail A k i)² ≤ ‖A−B‖²` — общая нижняя граница Эккарта–Юнга в хвостовой форме, замыкающая
- **`FrobeniusNorm.lean`** — `frobenius_norm_sq_eq_trace`: доказано `‖A‖² = Re(trace(Aᴴ*A))`; `frobenius_norm_unitary_mul` даёт инвариантность нормы при левом умножении на унитарную матрицу.
- **`MDLRank.lean`** — `mdlJ_first_order`: при `lam*c>0`, `kstar < card n`, `σ_{kstar}² ≤ lam*c` и стартовом условии `kstar=0 ∨ lam*c < σ_{kstar−1}²` выбранный `k*` минимизирует `mdlJ A lam c` по всем `k`.
- **`NegDiagRank.lean`** — `neg_diag_pos_off_diag_kernel_trivial`: если `M i i < 0`, `M i j ≥ 0` при `i ≠ j` и все строчные суммы строго отрицательны, то ядро `M *ᵥ` тривиально (max-|x| аргумент, самодостаточно).
- **`MatrixNormRelations.lean`** — `kronecker_perturbation_single_factor_B` и `…_C`: при непустых внутренних размерностях изменение одного сомножителя имеет точную норму, соответственно `‖B−B'‖*‖C‖` и `‖B‖*‖C−C'‖`.
- **`NormSupport.lean`** — `mulVec_eucl_norm_sq_le`: для комплексной матрицы квадрат евклидовой нормы `A*x` ограничен `(ΣᵢΣⱼ‖A i j‖²)*‖x‖²`; `mulVec_eucl_norm_le` — следствие без квадратов.
- **`SVD.lean`** — `hermitian_spectralRadius_eq_sup_abs_eigenvalues` и `l2_opNorm_hermitian_eq_sup_abs_eigenvalues`: для непустого конечного индекса и эрмитовой `H` спектральный радиус и операторная норма
- **`SpectralNormGap.lean`** — `outerProduct_spectral_norm_le`: спектральная норма внешнего произведения ограничена `‖u‖*‖v‖`.
- **`TruncatedSVDRank1.lean`** — `singularValues₀_eq_zero_of_rank_le_one`: если `rank A ≤ 1` и индекс `k` имеет `k.val ≥ 1`, то `singularValues₀ A k = 0`.
- **`WeylInequality.lean`** — `thompson_interlacing`: если `rank B ≤ r` и `i.val+r < card n`, элемент `singularValues₀ A` с индексом `i+r` не превосходит `singularValues₀ (A+B)` с индексом `i`.

## Hagi/External/MemT/GDN2.lean

- Обозначим `q = rowSumNorm(1−Uᵀ*U) * rowSumNorm D` и `b = rowSumNorm(Uᵀ*(diagonal ω*V))`. `gdn2_stabilizes`: при `0<q<1` и любом `ε>0` существует `T`, после которого норма памяти не превышает `b/(1−q)+ε`.

- `gdn2_forgets_initial`: разность двух траекторий с разными начальными памятями ограничена `q^t*rowSumNorm(M₁−M₂)` при любом `t`; дополнительных условий на `q` это утверждение не требует.

- `gdn2_reset_bound`: при `0<q<1` память, начатая с нуля, ограничена `b*(1−q^t)/(1−q)`.

## Hagi/Math/Foundations/Chord.lean

- `exp_chord_ab`: для `a<b` и `x∈[a,b]` доказана хордовая оценка `exp x ≤ ((b−x)/(b−a))*exp a + ((x−a)/(b−a))*exp b`; `exp_chord_r` — форма для `exp(r*x)`.

- `log_cosh_le`: для любого вещественного `M` доказано `log(cosh M) ≤ M²/2`.

## Hagi/Growth/LinearCone.lean

- `cone_exact_exponential`: при `α≥0`, `γ>0`, `ρ≥0`, `C t>0`, начальном конусе, капе `C(t+1)≤(1+α)C t`, динамике `D`, пороге на `β`, шаге `C(t+1)=C t+G t` и `γD≤G` доказано одновременно `(1+α)^T*C0 ≤ C T` и `C T ≤ (1+α)^T*C0`.

- `band_guaranteed_growth_range`: из `C(t+1)=C t+G t`, `b*(1−σ)^t≤G t` для `t<T` и `0<σ≤1` следует `C T ≥ C0 + b*(1−(1−σ)^T)/σ`.

- `time_to_target_log`: при `b≥0`, `0<σ<1`, `C0≤Cstar`, `σ*(Cstar−C0)<b` и `log(1−σ*(Cstar−C0)/b)/log(1−σ)≤T` доказано достижение `Cstar≤C T`.

## Hagi/Math/Foundations/

- **`ConeTakeoff.lean`** — `geometric_growth_from_cone`: если `γ,k≥0`, на `range T` выполнен шаг `C(t+1)=C t+γD t`, а на `range (T+1)` — конус `k*C t≤D t`, то `C0*(1+γ*k)^T ≤ C T`.
- **`GrowthBand.lean`** — `growth_band_iter`: при `0≤αmin≤αmax` и двустороннем шаге `(1+αmin)C t≤C(t+1)≤(1+αmax)C t` доказаны обе границы `(1+αmin)^T*C0≤C T≤(1+αmax)^T*C0`.
- **`Hoeffding.lean`** — `bern_mgf_bound`: для `0≤θ≤1` и любого `s` доказано `1−θ+θ*exp s ≤ exp(θ*s+s²/8)`.
- **`MesoScale.lean`** — `macro_collapse`: для неотрицательных `A,L` с оценками `A ℓ≤a0*ℓ^p`, `L ℓ≤L0*ℓ^(−q)` и `p<q` доказано `A ℓ*L ℓ → 0` при `ℓ→∞`.
- **`Ortho.lean`** — `ortho_norm_sq`: для ортонормального семейства `v` на конечном `ι` доказано `‖Σᵢ c i•v i‖²=Σᵢ(c i)²`; имеется и вариант по произвольному `Finset`.
- **`Potential.lean`** — `hagiPotential_penalty_drop`: при `epsQ≥0` и `q−epsQ≤q'` доказано `max 0 (qTarget−q') ≤ max 0 (qTarget−q)+epsQ`.
- **`QuadEta.lean`** — `quad_eta_identity`: для `quadLossAt a w = ½‖w−a‖²` градиентный шаг даёт точное `E(w−η∇E)= (1−η)²*E(w)`.
- **`Recurrence.lean`** — `recurrence_upper`: при `0≤ρ<1` и `x(t+1)≤ρ*x t+c` для `t<T` доказано `x T≤ρ^T*x0+c*(1−ρ^T)/(1−ρ)`.
- **`StageCalculus.lean`** — `compress_stage`: при `κ,s≥0`, `h_emp_dist : dnorm≤1/2` и `h_emp_lip : E3−E2pre≤κ*s*dnorm` следует `E3−E2pre≤κ*s/2`.
- **`Telescope.lean`** — `lyapunov_telescope_fin`: если `E(t+1)≤E t−eps` для всех `t<k`, то `E k≤E0−k*eps`.

## Hagi/Generalization/ModeState.lean

- `generalization_safe_step`: при `lam,nu,ε_Q≥0`, посылках `h_emp_fit`, ограничении прироста риска величиной budget и `h_emp_G : Qgen S−ε_Q≤Qgen S'` потенциал удовлетворяет `Φ'≤Φ−ε_E+lam*budget+nu*ε_Q`.

- `modeDrop_rejected`: условия `ModeDrop`, `h_emp_G` и строгое `ε_Q<ε_Qmode` несовместимы.

- `selector_skips_dominated`: при строго положительных весах скаляризации глобальный argmin не равен строго доминируемому checkpoint.

## Hagi/Geometry/SphericalSimplex.lean

- `dihedral_angle_ge_pi_div_three` и `dihedral_angle_lt_pi_div_two`: при `x≥2` выполнено `π/3≤arccos(1/x)`, а при `x>1` — `arccos(1/x)<π/2`.

- `euclid_sum_bounds`: для `n≥2` и `K=n(n+1)/2` доказано `(π/3)*K ≤ K*arccos(1/n) < (π/2)*K`.

## Hagi/Research/

- **`Ceilings.lean`** — `gain_product_bound`: норма композиции непрерывных линейных операторов не превосходит произведения норм; `gain_stack_ceiling` при `q≥0` и `‖T‖≤q` для всех слоёв даёт
- **`ChainUnification.lean`** — `training_core_is_measurement_tail`: если `E_dev=E_aligned`, `G_cap=η_p*η_o*η_s*E_dev`, а E_aligned и `α_align` ненулевые, то `η_p*η_o*η_s=α_trunc*α_safe*α_cap`.

## Hagi/Growth/

- **`FiberNecessity.lean`** — `configs_injective_on_separated` и `used_configs_lower_bound`: если разделённые задачи обслуживаются своими конфигурациями, отображение конфигураций инъективно на семействе и
- **`GainDecomposition.lean`** — `merge_is_mean`: из разложения `mergeDecomp W M dev` следует `N • M=ΣW`.
- **`GainRenewal.lean`** — `gain_renewal_recurrence`: при `γ>0`, `ρ≥0`, равенстве gain-канала по смыслу двух оценок `γD≤G≤γD` и `D(t+1)≥ρD t+inj−ξ` доказано `ρG t+γ*(inj−ξ)≤G(t+1)`.
- **`GammaDeficit.lean`** — `gamma_min_for_target`: при `α,γ,Cstar>0`, верхнем gain-законе, `D≤Dbar`, gate и существовании момента достижения `Cstar≤C t` необходимо `α*Cstar≤γ*Dbar`.
- **`Grow.lean`** — `newBound`: точно `(N*M+c)/(N+1)=M−certifiedGain N M c`; `certifiedGain_positive` при `c<M` даёт положительный прирост и строго меньшую новую границу.
- **`IntegrationOrder.lean`** — `sum_perm_invariant`: сумма конечного семейства выигрышей инвариантна относительно любой перестановки.
- **`NoiseDisentangle.lean`** — `orthogonal_noise_averaging`: для ненулевого `N`, попарно ортогональных `n i` с `‖n i‖²=σ²` среднее имеет квадрат нормы ровно `σ²/N`.
- **`PlasticityLedger.lean`** — `kl_le_log_card`: для `IsProbs P`, строго положительных `P i v` и `famMix P v` каждое `KL(P i‖famMix P)≤log(card I)`.

## Hagi/Research/

- **`RecursiveSelfDevelopment.lean`** — `opportunity_renewal`: из `ρD+βC−ξ≤D'` и `(1−ρ)D+δ_O≤βC−ξ` следует `D+δ_O≤D'`; `recursive_self_development` при `C≤C'`, `D≥0`, `δ_O>0` дополнительно даёт `D'>0`.
- **`RoundViability.lean`** — `round_exhausted`: при `devEnergy dev=0` и `GainOp` доказаны `ρD−ξ≤D'` и `η*devEnergy dev=0`; `cycle_criterion` — импликативная форма.
- **`RsiCriterion.lean`** — `rsi_step_growth`: из `ρD t+βC t−ξ t≤D(t+1)` и строгого `ξ t+(1−ρ)D t<βC t` следует `D t<D(t+1)`.

## Hagi/Growth/Saturation.lean

- `saturation_limit`: при `0<σ≤1` и нижнем PL-шаге для любого `ε>0` найдётся `T`, после которого `Cstar−ε≤C t`.

- `pl_gap_geometric_lo`: при `σ≤1`, верхнем PL-шаге и `C0≤Cstar` доказано `(1−σ)^t*(Cstar−C0)≤Cstar−C t`.

- `geometric_band_with_saturation`: при `γ,k>0`, `σ≤1`, точном cone-шаге, обеих PL-оценках, `ConeRatio` и `C0≤Cstar` доказана двусторонняя полоса `C0*(1+γ*k)^T≤C T≤Cstar−(1−σ)^T*(Cstar−C0)`.

## Hagi/Research/SeedOnly.lean

- `cycle_decay_mono`: при `s≥0`, `F>0`, `0<k<F+s` новое `F*(1−k/(F+s))` строго меньше `F` и неотрицательно; `cycle_decay_ratio` даёт точное отношение соседних приростов.

- `channel_switch`: при положительных `F,k,s,b,Cm,Cr` и `√F*(k*Cr)<b*Cm*s` индекс rank-канала строго больше movement-индекса.

- `seed_only_disp_bound`: при посылках `h_emp_lip`, `h_emp_disp_step`, `a,s≥0` и `dispP 0=0` доказано `dispL t≤Lam²*s*Σ_{i<t}a^i`.

## Hagi/Growth/

- **`SelfDevelopment.lean`** — `self_development_find`: при наличии безопасного `a₀` с `G a₀>0` существует безопасный `a'` с `0<G a'` и `G a₀≤G a'`.
- **`StateBinding.lean`** — `capability_geometric_growth_state`: при `0<α`, `0<γ`, `0≤ρ`, положительной начальной capability, начальном конусе, полевых законах шага, gain- и frontier-динамики, капе и пороге на `β`
- **`Takeoff.lean`** — `elasticity_chain`: если `(1+e t)*x t≤x(t+1)` и `1+e t>0` на `range T`, то `x0*∏_{t<T}(1+e t)≤x T`.
- **`Thermostat.lean`** — `thermostat_stop`: при `0<α<1`, `T0,δ>0`, `0<θ<1` и `t≥⌈log(δ/(T0*log(1/θ)))/log α⌉` доказано `exp(−δ/(T0*α^t))≤θ`.

## Hagi/Information/Capacity.lean

- `separated_needs_capacity`: если каждая задача из `SepSeparated good tasks` допускает подходящий ответ через некоторое состояние `S`, то `tasks.card≤card S`.

- `router_capacity_bound`: в аналогичной модели с `encode : A→Q` и `card Q≤2^B` получается `tasks.card≤2^B`. Отдельная `bits_floor` доказывает лишь неотрицательность `logb 2 (card S)` для непустого конечного `S`, а не оценку взаимной информации.

- `recoverable_avg`: при `N>0` и `0<devEnergyF dev` существует `k`, для которого `devEnergyF dev/N≤dev k ⬝ᵥ dev k`.

## Hagi/Math/Info/InfoCore.lean (moved from Hagi/Prelude/)

- `entropy_le_diagonal`: для положительно полуопределённой `A` энтропия не превосходит `Σᵢ negMulLog(Re(A i i))`; `concaveOn_entropy` доказывает вогнутость энтропии на PSD-состояниях.

- `discrete_fannes_coupling`: для вероятностных `p,q` на непустом конечном `ι` и посылки hbridge, отождествляющей энтропию неотрицательной диагонали с `shannon`, доказано `shannon p−shannon q≤tvHalf*log(card ι)+(1+tvHalf)*binEntropy(tvHalf/(1+tvHalf))`.

- Введены конечные `klDef`, `ceDef`, `entDef`, `tvDef` и `softDef`. При `p v ≠ 0` тождество `klDef_eq_ceDef_sub` выражает KL как `ceDef q p - ceDef q q`, а `ceDef_self` даёт `ceDef q q = entDef q`.

## Hagi/Learning/

- **`FOOF.lean`** — `foof_normal_eq`: при обратимости `regCov X lam` определённый `foofW V X lam` удовлетворяет `foofW*regCov=V*Xᵀ`.
- **`HRCN.lean`** — `domainTerm_gauge_shift`: при ненулевом знаменателе сдвиг значений `vs i` на `ws i • b` меняет доменный вклад ровно на `charProjR w b`.
- **`HadamardProjectors.lean`** — `charProjR_idem`: `charProjR w (charProjR w v)=charProjR w v`.
- **`RCDL.lean`** — `dual_apply`: для `dualW W0 xs vs` доказана поточечная формула `(W0*q)i+Σ_t dotProduct(xs t)q*vs t i`.
- **`SpectralBudget.lean`** — `spectral_budget`: если для каждого `w` квадрат доменной ошибки не превосходит `delta²*‖charProjR w v‖²`, `delta≥0`, то `‖v−Q‖²≤delta²*‖v‖²` в форме скалярного произведения `⬝ᵥ`.
- **`TernaryPert.lean`** — `frob_submul`: для конечной вещественной матрицы `E` выходная норма ограничена `√(frobSq E)*eunorm x`; основа — `cs_dotProduct`.
- **`ToyTrajectory.lean`** — `honest_step_cert`: при `0<eta<2`, `cost≤s.budget` и `lossS a s>0` существуют положительный drop и соответствующий `StepCertT`.
- **`TrainingTransition.lean`** — `taskStep_identity`: энергия после шага равна `taskEnergy S−(2η−T*η²)/2*Σ_j taskGrad S j²`.

## Hagi/Model/Adaptive.lean

- `switch_floor` и `switch_floor_eq_iff`: при `n>0` и `ΣP=1` выполнено `1/n≤ΣPᵢ²`, с равенством ровно при `P i=1/n` для всех `i`; неотрицательность `P` для этой квадратичной формулировки не требуется.

- `lora_kernel_preserved`: если `A*ᵥx=0`, то `(W+B*A)*ᵥx=W*ᵥx`.

- `ReZero.rezero_perturb_bound`: для `rezeroStep` доказано `‖rezeroStep x fx alpha−x‖≤|alpha|*‖fx‖`; нулевой коэффициент оставляет `x` неподвижным.

## Hagi/Model/AdaptiveChunking.lean

- На конечном носителе уровней `k` стоимость задана как
  `adaptiveCost c M = ∑ l, c l * M l ^ 2`. При `0 ≤ c l`, `0 ≤ M l`,
  `0 ≤ L`, `0 < r` и поточечном условии `M l ≤ L / r`
  `adaptive_le_static` доказывает
  `adaptiveCost c M ≤ ∑ l, c l * (L / r) ^ 2`.

- `adaptive_lt_of_strict`: при тех же условиях, если дополнительно
  `0 < c l₀` и `M l₀ < L / r`, неравенство стоимостей строгое.

## Hagi/Model/

- **`AlignmentRisk.lean`** — Для непустого конечного `V` и строго положительных нормированных `p q : V → ℝ`, `0 ≤ c` и односторонней посылки `risk ≤ c * ((1/2) * ∑ v, |p v - q v|)` `kl_budget_risk_bound` даёт
- **`Attention.lean`** — `gqa_kv_ratio`: при `1 ≤ T`, `1 ≤ d`, `n_kv < n_h` отношение стоимостей KV-кэшей равно `(n_kv : ℝ) / n_h`, а `gqa_kv_lt` делает его строго меньшим единицы. `mla_cache_saving` даёт
- **`AttentionSpend.lean`** — `hybrid_ratio`: при положительных `T n n_h d` `hybridAttnCost T w n_kv d / denseAttnCost T n n_h d = ((2*w+1 : ℝ)/n) * ((n_kv : ℝ)/n_h)`. При `2*w+1 < n` и `n_kv < n_h` отношение строго
- **`BYOL.lean`** — Для `bl u v = 1 - cosS u v` при посылке `CSCarrier u v`, то есть `|cosS u v| ≤ 1`, `bl_bounds` даёт `0 ≤ bl u v ≤ 2`; `bl_zero_at_perfect` превращает `cosS u v = 1` в `bl u v = 0`.

## Hagi/Model/BatchCEDescent.lean

- `batchMeanDirection_eq_neg_meanResidualTranspose` отождествляет среднее
  собственных отрицательных направлений с `−meanResidualTranspose X θ y`;
  `batchMeanAction_common` даёт среднее действие `−batchAlignment X θ y`.
  При `0 < batchRangeSquare X θ y` `batchLoss_safeStep_lt` строго снижает
  арифметическое среднее CE на заданном конечном батче.

## Hagi/Model/BlockNorm.lean

- Для `Blocks m = Fin 3 → Fin m → ℝ` `global_eq_mean_blocks` доказывает
  `(globalRms x)^2 = (∑ b : Fin 3, (blockRms (x b))^2) / 3`.

- `equal_blocks_global`: если `blockRms (x b₁) = blockRms (x b₂)` для
  всех блоков `b₁ b₂ : Fin 3`, то `globalNorm x = blockNorm x`.

## Hagi/Model/CEHeldout.lean (вкл. CEConfidenceScale, слит C523)

- `ceBound_mul_joint_normalizedCE` восстанавливает исходный one-hot CE
  умножением нормированной потери на положительный `ceBound X`;
  `sample_budget_normalized_eq_raw` даёт точное преобразование бюджета
  при `B ≠ 0`, `eps ≠ 0`.

## Hagi/Model/CECoupledShortcut.lean

- `shortcutScales_eq_fast_of_coupledPenalty_eq_zero`: полный кандидат
  fast с нулевым `coupledPenalty` возвращается без изменений; при
  ненулевом штрафе используется точный `selectedCoupledScales`.

- `shortcutScales_score_eq_selectedCoupled`: в обеих ветвях значение
  `coupledPenalty` равно значению на полном связанном минимизаторе; это
  равенство оценок, а не равенство выбранных кодов или исходного CE.

## Hagi/Model/CEDescent.lean

- Для конечного непустого `V` и любого `0 ≤ η`
  `ceOneHot_next_le` доказывает
  `CE(next η) ≤ CE θ - η*ceAlignment X θ t +
  (η*ceStepRange X θ t)^2/8`; направление —
  отрицательный транспонированный softmax-остаток.

## Hagi/Model/

- **`CEExpansion.lean`** — `ceLogits_expandedParameters`: новый логит равен `ceLogits X θ v + Z v * gamma`; поэтому при `gamma = 0` `ceOneHot_expandedParameters_zero` сохраняет CE при произвольной новой координате
- **`CEGradient.lean`** — На непустом конечном `V` и `EuclideanSpace ℝ (Fin d)` `fderiv_ceOneHot_mulVec` вычисляет направленную производную CE как `∑ v, (softDef (X*ᵥθ) v - oneHot t v) * (X*ᵥh) v`, то есть действие

## Hagi/Model/CEGroupedScale.lean

- Для эквивалентности `(Fin G × Fin 5) ≃ Fin (5*G)` и непустого `V`
  `ceOneHot_joint_le_blockPenalties` доказывает
  `CE(jointParameters e w scales) ≤ CE w + ∑ g, blockPenalty e X w g (scales g)`.

- `selectedGroupScales_spec`: каждый избранный код минимизирует
  `blockPenalty` среди полного конечного семейства из 255 кодов.
  При `2 ≤ G` независимый локальный поиск использует строго меньше
  математических вычислений оценки, чем полное число совместных кандидатов.

## Hagi/Model/CEJacobianMajorizer.lean

- Для непустого конечного `V`, `HasFDerivAt f J θ`,
  `A = -(fderiv CE(f) θ d)`, диапазона `(J d)u-(J d)v ≤ R` и остатка
  `‖f w-f θ-J(w-θ)‖ ≤ ρ*‖w-θ‖^2` на `closedBall θ r`
  `ceOneHot_local_line_majorize_of_jacobian_remainder` при `0 ≤ η` и
  `η*‖d‖ ≤ r` даёт
  `CE(f(θ+ηd)) ≤ CE(fθ) - η*A + η^2*(R^2/8 + 2*ρ*‖d‖^2)`.

## Hagi/Model/CEJointScale.lean

- `selectedCoupledScales_spec` минимизирует `coupledPenalty` по всему
  пространству функций `Fin G → DyadicScaleCode`;
  `selectedCoupledScales_le_selectedGroupScales_total` сравнивает этот
  минимум с суммой раздельных блочных штрафов, не упорядочивая исходный CE.

## Hagi/Model/CEMarkovConfidence.lean

- `raw_bank_freedman_confidence`: на истории пар «банк кодов — метка» с
  непустым конечным типом меток, при `0 < r`, `0 ≤ V`, вероятность того, что
  условная граница дисперсии `V` влечёт одновременное
  `|historyAdditive ...| < r` для всех `m` моделей, не менее
  `1 - 2*m*exp(-r^2/(4*(V + ceBound X*r)))`.

## Hagi/Model/

- **`CEPadding.lean`** — Для любого `d` `d ≤ paddedDimension d`, `paddedLogicalBits d = 16*((d+4)/5)`; `unpadVector (padVector w) = w`.
- **`CEQuantized.lean`** — На непустом конечном `V` `ceOneHot_le_of_abs_sub_le`: если `∀ v, |z v-y v| ≤ r`, то `ceOneHot t z ≤ ceOneHot t y + 2*r`.
- **`CEStorageBound.lean`** — `card_jointCode_le_payload`: `card (JointCode G) ≤ 2^(groupPayloadBits G)`; `log_card_jointCode_le_payload` даёт ту же границу для `log₂ card`.
- **`CertifiedTransition.lean`** — `certifiedTransition_of_advance` при `0 ≤ u.gap`, `0 ≤ u.sp.eta` и `u.sp.kappa*u.sp.s < 2*u.eff.growGain` связывает сертификат с конкретной парой `S : GrowthState X` и `advance S u`.
- **`ComputeOptimal.lean`** — При `0 < A B C` `chinchilla_optimum` задаёт `Nstar = √(A*C/B) > 0` и доказывает `chinchillaLoss A B C Nstar = 2*√(A*B/C)`, а также глобальную нижнюю границу этого значения для
- **`ConsolidationMirror.lean`** — На непустом конечном `V`, при `0 < T`, строго положительном нормированном `ρ₀`, `grow_gain_from_mirror` равен разность потерь приора и шага Гиббса
- **`CycleCertificate.lean`** — `cycle_certificate_composition`: один `CycleCertificate T C Φ B` даёт `C T = C 0 + Σ gain`, `Φ T ≤ Φ 0 - Σ drop + Σ risk` и `B T = B 0 - Σ spend`.

## Hagi/Model/EnergyReasoning/Pseudolikelihood.lean

- Track E1: псевдоправдоподобие как локальная условная CE на каноническом
  Prelude-стержне. Логиты `conditionalLogit B K y i a = −pairwiseEnergy B K
  (update y i a)` (CRAM-знак), условные `conditionalDist = softDef` от них,
  цель `pseudolikelihoodObjective = (Σ ceOneHot (y i) z_i)/|ι|`.

## Hagi/Model/

- **`DiffAttention.lean`** — `sm_shift`: `sm (fun j => x j + c) i = sm x i`; общий аддитивный сдвиг логитов не меняет softmax-веса.
- **`DistillCert.lean`** — Для `DistillCert` на `Fin n → ℝ`, с `0 < delta`, `0 ≤ lip`, `0 ≤ dist2 ≤ dbound` и `dist2^2 = ∑(teacher-student)^2`, `quant_L2` доказывает `∑(quantStudent-student)^2 ≤ n*(delta/2)^2`.
- **`GDNBridge.lean`** — `gdn_onehot_interp`: one-hot Gated DeltaNet-обновление равно `colInterp S i v g β`; записываемый столбец интерполируется между затухшим состоянием и `v` с коэффициентом `β`.

## Hagi/Model/RamProtocol.lean

- C303 (E6 — RAM induction: протокол store/load + нормализация
  заикания): `ramStore`/`ramLoad` — протокольный API поверх
  GDNRAM-носителя; `ram_store_load_roundtrip` — store→load по
  тому же адресу возвращает значение в точности (упаковка
  идеального one-hot roundtrip), `ram_store_isolation` — load по
  другому адресу не затронут записью (one-hot независимость
  слотов, режим lag-1).

## Hagi/Model/GatedCEDescent.lean

- Для непустого конечного `V` производная CE вдоль
  `gatedDirection X θ t` в нуле равна `-gatedAlignment X θ t`
  (`hasDerivAt_gatedLineObjective`).

- При `0 < gatedAlignment X θ t`
  `exists_gated_ceOneHot_descent` даёт существование `η > 0` со строгим
  локальным снижением фактического CE управляемой модели; явный размер
  шага в этой теореме не вычисляется.

## Hagi/Model/

- **`Generative.lean`** — DDPM: `alphaBar_succ` задаёт рекуррентность произведения. При `0 ≤ β i ≤ 1` `alphaBar_mono` доказывает невозрастание, а если `0 < b < 1`, `b ≤ β i ≤ 1`, то `alphaBar_exp_bound` даёт
- **`Grokfast.lean`** — `decompose`: `gLow + gHigh = g`; `amp_recompose` переписывает усиленное направление как `(1+lam)*gLow + gHigh`.
- **`HNet.lean`** — `hier_seq_shorten`: при `1 < r`, `0 < T` выполнено `0 < T/r < T`; `hier_attn_saving` даёт `c*(T/r)^2 = c*T^2/r^2`, а `hier_attn_saving_lt` при `0 < c` делает экономию строгой.
- **`HNet2.lean`** — `hier2_compression_product`: при `r1 r2 ≠ 0` `hier2Positions T r1 r2 = T/r1/r2`; при `0 ≤ T`, `1 ≤ r1`, `1 ≤ r2` `hier2_positions_le` даёт неравенство `hier2Positions ≤ T`.
- **`HypothesisCompetition.lean`** — При `0 < K`, `T ≠ 0` `dhcWeights_pos` и `dhcWeights_sum_one` доказывают строгую положительность и нормировку DHC-весов; `dhcWeights_mono` при `0 < T` сохраняет порядок активаций.

## Hagi/Model/Logic/VennHead.lean

- Точная нейро-символьная голова (Track B7): атомы Венна как
  ReLU-нейроны `vAtom` на {−1,+1}-входах — ровно один активен
  (`vAtoms_sum_one`, `vAtoms_mem`); голова `vennHead` линейна по атомам
  с {0,1}-маской (`vennHead_mem`).

- `vennHead_exact` — 64-случайный мост: на знаковых входах голова
  вычисляет значение истинности маски `Hagi.Data.BoolVenn` (16 масок ×
  4 входа).

## Hagi/Model/

- **`LabelSmoothing.lean`** — При `0 ≤ ε` на непустом конечном `K` `ls_pointwise_dist` даёт точное равенство `|lsTarget q ε i-q i| = ε*|q i-1/card K|`; для нормированной неотрицательной `q` `ls_l1_bound` ограничивает
- **`LayerNorm.lean`** — `ln_scale_invariant`: для `0 < c` `lnVec (c • x) = lnVec x`.
- **`LogitPSV.lean`** — Для непустого конечного `k` и строго положительных весов `p` с суммой `1` `logitPSV_gap_nonneg` доказывает `0 ≤ twoGap p (biasedScore base sigma ∘ eps)`.

## Hagi/Model/Losses.lean

- NT-Xent: `nt2_nonneg`, `nt2_anti`, `nt2_zero_margin` и `nt2_le_log2`
  для `nt2 m = log(1+exp(-m))` дают неотрицательность, строгое убывание
  по марже, значение `log 2` при `m=0` и верхнюю границу `log 2` при
  `0 ≤ m`.

## Hagi/Model/MachineBridge.lean

- `machine_param_bridge`: если `S.params = w` для
  `S : GrowthState (EuclideanSpace ℝ (Fin n))`, то параметры `advance`
  равны `jointStepE a w eta`; `0 < eta` входит в построение входных данных.

## Hagi/Model/

- **`MambaSSM.lean`** — `ssm_linear_cost_lt`: при `0 < c κ` и `κ < T` `c*T*κ < c*T*T`.
- **`MeasuredEffects.lean`** — Для `MS`, содержащего способность, бюджет и типизированные эффекты, `trainStep_measured` отождествляет эффекты шага с `measure S batch`, а `trainStep_budget_balance` даёт
- **`MeasurementCert.lean`** — Для `StepMeasurement`, чьё поле hband содержит `claimed ∈ [measured-delta, measured+delta]`, `claimed_pos_of_signal` из `delta < measured` получает `0 < claimed`.
- **`Memory.lean`** — `wt_saving`: для вещественных `m n` с `0 < m*n` `wtParams m n < untiedParams m n`.
- **`Mixup.lean`** — `mixLabel_dist`: при `0 ≤ lam ≤ 1` и двух неотрицательных нормированных `y₁ y₂ : K → ℝ` смесь также неотрицательна и нормирована.
- **`ModeConnectivity.lean`** — Для квадратичной `energy a` на `Fin n → ℝ` и `0 ≤ lam ≤ 1` `linear_no_barrier` ограничивает энергию линейного пути величиной `max (energy a w1) (energy a w2)`.
- **`ModelSoup.lean`** — `soup_mem`: на непустом конечном `K`, при `0 ≤ w i`, `Σw=1` и `c ≤ x i ≤ d` `c ≤ soup w x ≤ d`.
- **`ModernHopfield.lean`** — `hopfield_concentration`: при `0 ≤ Delta` и разделении `s iStar ≥ s i + Delta` для всех `i ≠ iStar` softmax-вес лучшего паттерна не менее `1/(1+(K-1)*exp(-Delta))`.
- **`MuPScaling.lean`** — `muP_width_invariant`: при `0 ≤ eta`, `0 ≤ c` и строчных нормах `≤ c` абсолютное обновление каждого выхода не превышает `eta*c*√(∑x j^2)` без множителя ширины.
- **`NeuralComputer.lean`** — Для `S : NCState`, `u : NCInput` `nc_cpu_frozen` и `nc_base_frozen` сохраняют соответственно параметры CPU и тритарную базу.

## Hagi/Model/NonlinearCE.lean

- `ceOneHot_nonlinear_descent_le`: нелинейная лемма о спуске — при
  посылках мажоризатора Якобиана (оструктуренный остаток
  `‖f w-f θ-J(w-θ)‖ ≤ ρ*‖w-θ‖^2` на шаре `r`, диапазон `(J d) ≤ R`,
  `η*‖d‖ ≤ r`) `CE(f(θ+ηd)) ≤ CE(fθ) - η*A +
  (nonlinearCurvature R ρ ‖d‖^2 / 2)*η^2`, где составная кривизна
  `nonlinearCurvature R ρ dn = R^2/4 + 4*ρ*dn` (без отброшенных
  перекрёстных членов).

## Hagi/Model/

- **`NormAct.lean`** — PreNorm: `preNorm_step_bound` ограничивает шаг суммой норм; `preNorm_depth_bound` при `‖fs t‖ ≤ B` даёт `‖x_L‖ ≤ ‖x0‖ + L*B`.
- **`Perceiver.lean`** — `perceiver_cost_ratio_lt`: при `1 ≤ n`, `2*m ≤ n` `perceiverCost n m / attnCost n < 1`.
- **`QuantizedAdvance.lean`** — `advanceQ_quantized`: для `S : GrowthState X` `(advanceQ S u q).params = q(S.params-u.sp.eta • u.stepDir)`.

## Hagi/Model/RL.lean

- GRPO: `groupAdv_sum_zero` при `0 < n` даёт нулевую сумму, а
  `groupAdv_sq_min` доказывает оптимальность среднего как baseline. При
  `0 < sigma` и явном `∑(r-mean)^2 = sigma^2*n` `groupAdv_std_unit`
  даёт `∑A_i^2 = n` для стандартизованных преимуществ.

- RLHF: `rlhf_penalty_floor` для строго положительных нормированных
  `q p` и `0 ≤ β` доказывает, что вычитание `β*klDef q p` не увеличивает
  ожидаемую награду.

## Hagi/Model/

- **`RMSNorm.lean`** — `rn_scale_invariant`: для `0 < c` `rnVec (c • x) = rnVec x`.
- **`RVCore.lean`** — `wordAdd_spec`: `(wordAdd a b).toNat = (a.toNat+b.toNat) % 2^32`; `wordSub_spec` задаёт оборачивающуюся разность по тому же модулю, а `wordAnd_spec` использует `Nat.land`.
- **`ReferenceMachine.lean`** — Для `a w : Fin n → ℝ` `jointStep_energy` даёт `energy a (jointStep a w eta) = (1-eta)^2*energy a w`; `jointStep_energy_decrease` при `0 < eta < 2`, `a ≠ w` делает спад строгим.
- **`Residual.lean`** — Для нормированного `X`, `‖f t x‖ ≤ eps` и `0 ≤ eps` `res_bounded_drift` даёт `‖resStream f x0 T-x0‖ ≤ T*eps`.
- **`Routing.lean`** — `softDef_odds`: точное обновление шансов softmax при произвольном сдвиге скоров `a⁺j/a⁺k = (aj/ak)·exp(Δsj−Δsk)` — без приближений первого порядка.

## Hagi/Model/ResidualVQ.lean

- `residual_sum_split`: `z = reconstruct R k + (z-reconstruct R k)`;
  `refine_geometric` при `0 ≤ D 0`, `0 ≤ rho k` и
  `D(k+1) ≤ rho k*D k` для `k<K` даёт
  `D K ≤ (∏k<K,rho k)*D 0`.

- `error_budget_uniform`: при `0 ≤ rho k ≤ ρ < 1`, `eps k ≤ ε`,
  `0 ≤ ε`, `D(k+1) ≤ rho k*D k+eps k` и `0 ≤ D k`
  `D K ≤ ρ^K*D 0 + ε*(1-ρ^K)/(1-ρ)`.

## Hagi/Model/

- **`Sidon.lean`** — `sidon_pair_diff_injective`: для Sidon-`S`, `t i ∈ S`, `StrictMono t`, `i<j`, `k<l` равенство `t j-t i = t l-t k` влечёт `i=k`, `j=l`.
- **`SoftmaxStep.lean`** — Для одномерной `logitCE` `logitCE_deriv` даёт производную `-1/(1+exp w)`, а `grad_lipschitz` — глобальный коэффициент `1/4`.

## Hagi/Model/SoftmaxHead.lean

- C283 parametric softmax-head core: оси CE-семейства (gated, tanh,
  packed, grouped/joint scale, padding, held-out confidence, batch
  descent) становятся конфигурацией — `LogitMap` (ident/tanh;
  `LogitMap.apply` — единственная точка рекурсии), `Reduction` с
  весами, `HeadConfig`; функционал `headCE` определён рекурсией по
  конфигурации, `headLoss` — агрегация по reduction. SSOT остаётся
  `Hagi.ceOneHot`: существующие утверждения — инстансы при
  `LogitMap.ident` (`headCE_ident` — определительное равенство);
  ни одно утверждение существующих модулей не меняется. Scale/quantizer
  ось сознательно НЕ конструктор (меняет константы штрафов, не
  функционал).

## Hagi/Model/

- **`SourceMixture.lean`** — `mixture_sum_one`: если `Σλ=1` и каждый источник нормирован, смесь нормирована; `mixture_nonneg` дополнительно требует `0 ≤ λ`, `0 ≤ p s x`.
- **`SpecDecoding.lean`** — `anchor_eq_ema`: `anchorSeq α x n = ema (1-α) x n`; `anchor_stable` при `0 ≤ α ≤ 1` и всех `x t ∈ [lo,hi]` сохраняет всю якорную траекторию в `[lo,hi]`.

## Hagi/Model/StageSemantics.lean

- `advance_energy_drop` для `S : GrowthState X` и свежего `StageInput X`
  при законах роста/слияния/совместного шага/сжатия даёт
  `compressEnergy ≤ S.energy - (growGain + gap +
  (η*⟪grad,d⟫ - L*η^2*‖d‖^2/2) - κ*s*quantErr)`;
  посылки включают `0 ≤ gap`, `0 < L`, `η ≤ 1/L`,
  `‖d‖^2 ≤ ⟪grad,d⟫` и соответствующие неравенства энергии.

## Hagi/Model/TanhCEStep.lean

- Для модели `x ↦ ![Real.tanh x, 0]` на `Fin 2`
  `ceOneHot_tanh_step_le` доказывает
  `CE(![tanh(2/33),0]) ≤ CE(![0,0]) - 1/66`; локальная оценка остатка
  имеет радиус `1` и коэффициент `2`.

- `ceOneHot_tanh_step_lt` делает спуск строгим; равенство фактического
  спада величине `1/66` не утверждается.

## Hagi/Numerics/Numerics.lean (вкл. SoftmaxFix, слит C526)

- `ce_grad_sum_zero`: для нормированной `p`
  `Σ(softDef z-p)=0`; `distill_grad_self_zero` обнуляет остаток при
  `zS=zT`.

- Если `univ.erase t` непуст, `margin_rest_sum` даёт
  `Σ_{j≠t}exp(z j-z t)=exp(-logitMargin z t)`, а `ce_loss_margin`
  переписывает CE как `log(1+exp(-logitMargin z t))`.

## Hagi/Research/

- **`ConditionalInformation.lean`** — Для строго положительной нормированной `p` на `X×(Z×Y)` и условной положительной нормированной ссылки `q : X→Y→ℝ` `conditionalMutualInformation_eq_expected_log_ratio_sub_reference_kl` равна
- **`CrossModalGap.lean`** — Для непустых конечных `X Y` и строго положительной нормированной `p : X×Y→ℝ` `crossModalGap_eq_kl` равна `klDef p (margX p * margY p)`; `crossModalGap_nonneg` доказывает неотрицательность.
- **`OmniInvariant.lean`** — На непустых конечных `Y1 Y2`, для положительной нормированной `p`, `omniStep C gIntra gCross cComp cRisk = C+gIntra+gCross-cComp-cRisk`.
- **`OmniState.lean`** — `driftTube_closed`: при `ρ ≠ 1` `driftTube ρ e d0 t = ρ^t*d0 + e*(1-ρ^t)/(1-ρ)`; `drift_limit` при `0 ≤ ρ < 1`, `0 ≤ e d0` ограничивает его `d0 + e/(1-ρ)`, а `drift_zero` убирает аддитивный

## Hagi/Optimization/

- **`OptimizerVariants.lean`** — `acc_mono`: `adagradAcc g t ≤ adagradAcc g (t+1)`.
- **`EF21Quantizer.lean`** — `IsContractive`: контракт контрактного компрессора `‖C u − u‖₂² ≤ (1−α)²‖u‖₂²` на plain-носителе `n → ℝ` (суммы квадратов явно). Доказанные инстансы: identity (α=1), нулевой компрессор

## Hagi/Optimization/AdaptiveCycle.lean

- `adaptive_cycle_expansions`: если `0 < δ`, `C(k+1)≤C k-δ` и
  `0 ≤ C j` для всех индексов, то для любого `N`
  `(N : ℝ) ≤ C 0/δ`.

## Hagi/Optimization/

- **`Checkpoint.lean`** — `ckpt_mem_floor`: для вещественных `0 < k n` `2*√n ≤ k+n/k`.
- **`ComputeScaling.lean`** — `compute_scaling_lower_bound`: при `0 < a b m n` `(√a+√b)^2/(m+n) ≤ a/m+b/n`; `compute_scaling_bound_attained` достигает равенства при `m=√a*s`, `n=√b*s`, `0 < s`.
- **`DREAM.lean`** — `dream_tau_extrapolation`: если `nu = (2*tau+1)-1/2`, то `‖dreamY s-s.x‖ = (2*tau+1/2)*‖s.x-s.xPrev‖`.
- **`DirectionPacking.lean`** — `welch_bound_core`: для единичных `u : Fin M → F` в конечномерном вещественном пространстве с `OrthonormalBasis (Fin d)`, `2 ≤ M`, `0 < d` и `|⟪u i,u k⟫| ≤ μ` для `i≠k`
- **`GraphDistanceRouting.lean`** — Если в конечном графе `G` каждая вершина достигает target, то носитель нецелевой строки ядра кратчайшего пути равен `shorterNeighborFinset`; `dist_add_one_eq_of_mem_support` доказывает
- **`InexactContraction.lean`** — `inexact_contraction_halt`: при `0 < q < 1`, `0 ≤ ε`, `x(k+1)≤q*x k+ε`, `0 < B`, `x0≤B` и `q^K < (τ-ε/(1-q))/B` доказано `x K < τ`.
- **`LRSchedule.lean`** — Для непустого конечного индекса `polyWeights C eps` неотрицательны и суммируются в `1`. При `0 < eps` и `C u < C w` теорема `polyWeights_strict_mono` даёт

## Hagi/Research/MarkovPercolation.lean

- `historyLaw_walk_support`: любой маршрут графа поддерживается однородным
  `historyLaw` для `supportedRoutingKernel`, если его первая вершина
  принадлежит носителю начального PMF.

## Hagi/Optimization/

- **`Momentum.lean`** — `momentum_floor`: при `0 < q`, `0 ≤ β δ`, `q+β<1` и `e(k+1)≤q*e k+β*e(k-1)+δ` ошибка ограничена полом `δ/(1-q-β)` плюс затухающий член с `momentumRate q β`.
- **`MomentumHB.lean`** — `hb_discriminant_interval`: при `0 < β < 1` и `(1-√β)^2 ≤ η*μ ≤ (1+√β)^2` дискриминант неположителен; `hb_root_modulus` для корня `λ²-tλ+β=0` с `0 < β` и дискриминантом `≤0` даёт
- **`NeuronAlloc.lean`** — `neuron_alloc_lower_bound`: для положительных `c i n i N` и `Σn=N` `(Σ√c i)^2/N ≤ Σ(c i/n i)`.
- **`PLConvergence.lean`** — `pl_linear_convergence`: при `0 < L`, `0 < μ ≤ L`, `Estar≤E t`, `E(t+1)≤E t-G t/(2L)` и `2μ*(E t-Estar)≤G t` `E t-Estar≤(1-μ/L)^t*(E0-Estar)`.
- **`RobbinsMonro.lean`** — `robbins_monro_decay`: при `0 ≤ x 0`, `0 ≤ η k ≤ 1`, рекурсии `x (k+1) ≤ (1-η k)*x k` и `Tendsto (fun n => ∑ k ∈ range n, η k) atTop atTop` для любого `ε > 0` найдётся `T`, после которого

## Hagi/Research/

- **`Schelling.lean`** — `localCompatibleDegree` считает соседей `w` с `k ≤ compatibility v w`, а `locallySatisfied` требует не менее `min k (G.degree v)` таких соседей. Нулевой порог и изолированная вершина
- **`SchellingPercolation.lean`** — `locallySatisfied_mono_of_le`: при `G ≤ G'` локальная удовлетворённость сохраняется только с дополнительной посылкой `k ≤ G.degree v`; без неё квота `min k degree` может вырасти при

## Hagi/Optimization/

- **`SphericalDamping.lean`** — `chordal_residual_eq`: для единичных `u v` выполнено `1 - ⟪u,v⟫ = (1/2)*‖u-v‖^2`.
- **`SubspaceGrowth.lean`** — `projResidual u v = v - ∑ i, ⟪u i,v⟫ • u i`. Для единичного попарно ортогонального семейства остаток ортогонален каждому `u i`, выполнено `projResidual_self_inner`, а `projResidual_le_norm`

## Hagi/Research/Site.lean

- На конечной решётке определены `openAt`, `openGraph`, `crossing` и равномерная по всем конфигурациям затравки вероятность `R`. `card_Ω` равен `M^(L*L)`, а `crossing_mono` и `R_monotone` доказывают монотонность по порогу на одном пространстве затравок.

- Для чётной затравки на решётке `2×2` доказаны `parity_not_crossing1` и `parity_crossing2`; `emergence_jump_witness` упаковывает этот пример, а `R_strict_jump` даёт строгое `R 2 rowTop rowBot 1 < R 2 rowTop rowBot 2`.

- Все результаты конечны; бесконечный перколяционный порог и асимптотический закон критической точности здесь не выводятся.

## Hagi/Planning/Imagination.lean

- C220 (удаление zero-consumer дубликатов): forward-thinking
  regret-утверждение удалено; родственная доказанная граница той же
  формы `A − L* ≤ log K/eta + eta*T/2` — `router_regret_bound`
  (Hagi/Optimization/MirrorHedge.lean).

- `imagination_compounding`: при пошаговой ошибке прогноза не более `ε` на `k < K` и `L`-липшицевости каждой `V k` на `k ≤ K` разность `∑ V k (oh k) - ∑ V k (o k)` не превышает `K*L*ε`. Доказана односторонняя, а не абсолютная, оценка.

- `adaptive_first_sufficient`: из `|Vhat π₁ - V π₁| ≤ ε` и `θ ≤ Vhat π₁` следует `θ - ε ≤ V π₁`. `branching_avoids_detectable_failure` использует одностороннюю ошибку `Vhat - V ≤ ε` и посылку `θ < Vhat π` для исполняемых планов; `branching_dominates_linear` затем отделяет заведомо плохой `π₁` от исполняемого `πb`.

## Hagi/Pretraining/

- **`Dust.lean`** — `hcDelta` вычисляет среднее `signR (u i) * signR (u j)` по булеву кубу как `if i = j then 1 else 0`. `esUnbiased` при `σ ≠ 0` доказывает точное равенство среднего симметричной разности
- **`ProbeError.lean`** — `fd_probe_error`: при `σ > 0` и модельной гладкости с константой `L` абсолютная ошибка прямой разности не превышает `(L/2)*σ*‖v‖^2`; `linear_probe_exact` даёт точность для аффинной функции.
- **`RobustnessLaw.lean`** — `robust_interpolation_lipschitz_floor`: интерполяция точек с `L`-липшицевой функцией влечёт `|y(i+1)-y i| ≤ L*|x(i+1)-x i|`. `no_lipschitz_interpolator_of_steep` исключает такую функцию при
- **`Speedrun.lean`** — `cePartition_move` точно вычисляет изменение суммы экспонент при сдвиге одного логита. При положительной исходной сумме `ceLogit_move_change` выражает изменение CE как целевой член
- **`SyntheticPretrain.lean`** — `time_to_capability_correct`: при достижимости порога и монотонности `C` индекс `TimeToCapability` является первым с `τ ≤ C`, до него `C < τ`, а после него порог сохраняется.

## Hagi/Probability/

- **`AdaptiveSuccess.lean`** — `adaptive_success_count_floor`: на конечном независимом произведении, для `X i v ∈ [0,1]`, общего пола `SuccessFloor p X p0`, `n > 0` и `t > 0` вероятность события
- **`Azuma.lean`** — `hoeffding_lemma_prefix` ограничивает MGF условно центрированной величины с `-c ≤ X ≤ c` через `exp (lam^2*c^2/2)`. `azuma_mgf` по префиксным условным средним даёт
- **`ThermoBridge.lean`** (BatchSNR) — `snr_realized` записывает SNR как квадрат среднего, делённый на дисперсию batchMean; `snr_linear` даёт точное `snr g B = B * snr g 1`.
- **`PMFBridge.lean`** (BernoulliFactory) — `probAccept_eq_bernPoly` доказывает равенство двух явных сумм `probAccept` и `bernPoly`; `binomWeight` содержит биномиальные веса `choose n j * p^j * (1-p)^(n-j)`.
- **`CertifiedEstimator.lean`** — Для независимых `X i ∈ [0,1]` доказаны `hoeffding_chernoff`, оптимизированный `hoeffding_tail` и `hoeffding_two_sided`: односторонний хвост суммы центрирований имеет границу
- **`ChernoffCGF.lean`** — `cgf_centering` для положительных `q` даёт `log ∑q*exp(c*g) = c*μ + log ∑q*exp(c*(g-μ))`; нормировка `q` в этой алгебраической формуле не требуется.

## Hagi/Probability/Concentration.lean

- C287 (A10): единый concentration-API для Hoeffding-семейства
  средних хвостов: `concConfidence ε n = exp(−2nε²)` — канонический
  односторонний [0,1] confidence; `concConfidenceTwoSided ε n =
  2·exp(−2nε²)`; парный радиус `concRadius δ n = sqrt(log(1/δ)/(2n))`
  с двойственностью `concRadius_valid`; `concConfidence_pm1_rescale` —
  [−1,1]-форма гейта C264 `exp(−nη²/2)` есть `concConfidence (η/2) n`
  (радиус на [−1,1] удваивается).

## Hagi/Probability/

- **`ConditionalSuccess.lean`** — `success_count_lower` и `success_count_lower_p0`: при `0 < delta < 1`, измеримости, значениях `S t ∈ [0,1]` и `iIndepFun S μ` сумма успехов с вероятностью не меньше `1-delta` ограничена
- **`EntropyConvexity.lean`** — `log_sum_ineq` для положительных `a b` даёт `sum(a)*log(sum(a)/sum(b)) ≤ ∑a*log(a/b)`; `kl_convex_first` доказывает выпуклость KL по первому аргументу при `0 < lam < 1` и положительных
- **`ExpChord.lean`** — `exp_chord` — псевдоним `Hagi.Foundations.exp_chord_r`; `hoeffding_chord_mgf` для положительного нормированного `q` и `a ≤ g ≤ b`, `a < b`, ограничивает центрированный MGF хордой между `a`
- **`FiniteBayes.lean`** — `observationEvidence_eq_sum` вычисляет свидетельство наблюдения как `∑x, p₀ x * K x y`; `posterior_apply` при `0 < observationEvidence` нормирует `p₀ x * K x y` этим свидетельством, а
- **`FiniteEM.lean`** — Центральное разложение выражает `ceDef q (jointMass model) - entDef q` как `-log evidence + KL(q, posterior)` при положительном свидетельстве наблюдения и `q.support ⊆ posterior.support`
- **`FiniteFamilyConfidence.lean`** — `finite_family_upper_confidence`: для заранее фиксированного конечного семейства и независимых `[0,1]`-выборок все истинные средние одновременно не превосходят выборочные средние плюс `eps`
- **`FiniteLogScore.lean`** (вкл. FiniteJointLogScore, слит C525) — При неотрицательных нормированных `p q` и поддержке `0 < p x → 0 < q x` доказаны `klDef_nonneg_of_support` и `klDef_eq_zero_iff_of_support`: `klDef p q ≥ 0`, а равенство нулю эквивалентно
- **`FiniteMultiEM.lean`** — `total_negativeLogEvidence_drop_eq` при положительных свидетельствах наблюдения и включениях поддержек старых апостериорных законов в новые раскладывает суммарное убывание отрицательного
- **`Freedman.lean`** (вкл. TwoSided/Step/Adaptive/FamilyConfidence, слит C525) — `freedman_lemma_prefix`: при `|X| ≤ b`, нулевом условном среднем, `∑q*X^2 ≤ sig` и `lam ≥ 0` MGF не превосходит `exp (lam^2*sig*exp(lam*b)/2)`. `freedman_mgf` итерирует эту границу по
- **`GibbsCooling.lean`** — `gibbs_concentration`: при `T > 0` и зазоре `E vstar + δ ≤ E v` для всех `v ≠ vstar` доля Гиббса минимизатора не меньше `1 - card(univ.erase vstar)*exp(-δ/T)`. C221: формулировка
- **`KLSBridge.lean`** — `gradCovBound`: для неотрицательной нормированной `q`, `C ≥ 0`, из посылки Пуанкаре для каждого направления и оценки чувствительности `(sens a x)^2 ≤ L^2*sqN a` следует
- **`LinkedFlip.lean`** — `linkedChannel_apply` представляет переход как `(ν.map (eventMask neighbors)) (x ^^^ y)`. Для `ν = pure none` канал оставляет `x` на месте, а для `pure (some a)` применяет
- **`MarkovPathSupport.lean`** — `historyLaw_support_of_path`: если начальная точка принадлежит поддержке `initial` и первые `k ≤ T` переходы принадлежат поддержкам ядер, существует полная история в поддержке
- **`MomentBounds.lean`** — Для положительного нормированного `q` и `a ≤ g ≤ b` доказаны `popoviciu_var`: `Var(g) ≤ (b-a)^2/4`, `popoviciu_abs_dev`: среднее абсолютного отклонения не превышает `(b-a)/2`, а также
- **`NoiseTemperature.lean`** — При непустом `Fin b` теорема `batchMean_unbiased` доказывает равенство среднего batchMean исходному `popMean`; `batch_variance_eq` даёт точное
- **`RankedStopRouting.lean`** — Если каждый поддерживаемый нетерминальный переход выполняет `R a b` и строго увеличивает rank, терминальные строки являются `PMF.pure a`, `rank a ≤ B` и `B ≤ T`, то
- **`SphericalAngle.lean`** — `sphericalAngle_add_two` при `n > 0` даёт `Ω(n+2) = (2π/n)*Ω n`; `sphericalAngle_even_geo` и `sphericalAngle_odd_geo` ограничивают чётную ветвь от `8` и нечётную от `9` геометрическими
- **`StationaryFlatness.lean`** — `tail_sum_identity`: для натуральнозначного `X ≤ M` на конечном вероятностном пространстве `expectNat q X = ∑_{k<M} probGe q X (k+1)`.

## Hagi/Runtime/

- **`BF16Delta.lean`** — `Code` и `decode` задают все конечные BF16-коды с точным значением в `ℚ`, включая signed zeros и subnormals. `exists_IsNearest` строит ближайший код для каждого рационального аргумента без
- **`ControllerGates.lean`** — `logitRange_scale` при `tau > 0` даёт линейное масштабирование диапазона, `variance_gate_contract` при `tau ≥ 1` — сокращение квадратичной величины `range^2/8`, а `variance_gate_normalize`
- **`TernaryExact.lean`** — `qTern_error_in` при `s > 0` ограничивает ошибку внутри диапазона через `s/2`, а `qTern_error_out` вне его даёт точное `|x - qTern s x| = |x| - s`. `ternary_split_bound` разлагает полную

## Hagi/Sparsity/SparseStep0.lean

- `sparse_step0`: для ортонормированного семейства `v`, `tol ≥ 0` и строгого условия `∑_{i∈sᶜ} c i^2 < tol^2` норма разности полной и сохранённой сумм строго меньше tol.

- Оценка не зависит от числа отброшенных индексов: вся их совместная энергия уже учтена в посылке htail.

## Hagi/Spectral/RankGrowth.lean

- `rank_orthogonal_growth`: если строки `R` линейно независимы и `OrthRows M R`, то ранг `stackRows M R` равен `M.rank + Fintype.card k`.

- `span_growth_zero_interference`: если каждая новая строка `u j` ортогональна каждой `g i`, то любой `d` из линейной оболочки `u` также ортогонален всем `g i`.

## Hagi/StatMech/Hopfield/

- **`CharPatterns.lean`** — `charEnergy_eq` доказывает `charEnergy v = dotProduct v v / 2` через полный набор характеров.
- **`Concentration.lean`** — `eunorm_spins` равен `sqrt N`, а `energy_le_frob` при `NeZero N` ограничивает энергию любой конфигурации через `frobSq J / 2`.
- **`LowerBound.lean`** — `exists_max_energy` при `N > 0` доказывает существование спиновой конфигурации с максимальной энергией; `partition_ge_witness` для любого `sigma₀` даёт `exp(beta*energy sigma₀) ≤ partition`.
- **`Model.lean`** — В конечном объёме определены спины `Fin N → Bool`, энергия `energy N K J σ`, статистическая сумма и плотность свободной энергии; термодинамический предел не вводится.
- **`SubMemory.lean`** — `subsetEnergy_eq` выражает энергию подмножества как `(∑_{w∈S} dotProduct (charProjR w v) (charProjR w v))/2`.

## Hagi/State/

- **`TrainState.lean`** — Статус файла преимущественно состоит из определений носителей: `TrainState` объединяет `ModelState`, `OptimizerState`, `MemoryState`, `ResourceState`, `SafetyState` и пятиканальный
- **`Transition.lean`** — `trainStep_quality_unchanged` и `trainStep_evaluate_unchanged` оставляют качество и его покомпонентное значение неизменными. `trainStep_energy_identity` даёт точный квадратичный закон

## Hagi/Step/

- **`ArmijoAcceptance.lean`** — `armijo_sufficient_decrease`: из направленности `⟪g,d⟫ ≤ -c1*‖d‖^2`, `c1 > 0`, `alpha > 0` и квадратичной гладкости следует `J(alpha•d) ≤ J 0 - (c1 - L*alpha/2)*alpha*‖d‖^2`.
- **`BatchBudget.lean`** — `noiseEps_sq` при `m > 0`, `sigma ≥ 0`, `0 < delta ≤ card K` вычисляет `noiseEps^2 = sigma^2*‖d‖^2*(2*log(card K/delta)/m)`.
- **`CPUFreeze.lean`** — `cpu_frozen` по определению `safeStep` возвращает нулевую CPU-компоненту обновления.
- **`CausalFilter.lean`** — `gqa_shared_score` при `Km q = Kv (g.kvOf q)` доказывает равенство оценок внимания GQA и MHA; сюръективная группировка `GQA` даёт `gqa_cache_card : card KV ≤ card Q`.
- **`Compound.lean`** — `compound_c_stabilizes` при `α > 0`, `D,J ≥ 0`, `D < G0`, `ε > 0`, измеренных оценках `c t ≤ α*G t + J`, `G t ≤ D + (G0-D)*a^t` и `a^1 ≤ ε/(α*(G0-D))` ограничивает именно `c 1` через
- **`Dominate.lean`** — `domination_decompose` раскладывает `⟪gi,d⟫` на компоненту вдоль `gs` и остаток. При положительных нормах, `‖d‖*‖gs‖/2 ≤ ⟪d,gs⟫` и `⟪gi,gs⟫ ≤ -‖gi‖*‖gs‖/4` теорема `domination_regression`
- **`FrobeniusLMO.lean`** — `sgd_stable_step`: при `G ≠ 0`, `eta > 0`, `lam > 0`, квадратичной верхней оценке и `eta < 2*⟪G,G⟫/(lam*‖G‖^2)` получается `L' < L`.
- **`GPM.lean`** — `gpm_zero_forgetting`: при `gpmOrth ΔW xs` для любого `W` и каждого старого входа `(W+ΔW)*ᵥxs k = W*ᵥxs k`.
- **`GradCentralization.lean`** — `gc_zero_sum` доказывает нулевую сумму центрированного градиента; `gc_pythagoras` даёт `∑g^2 = ∑(gc g)^2 + card V*(popMean g)^2`.
- **`GradClip.lean`** — `clip_norm_le` при `R ≥ 0` даёт `‖clip R g‖ ≤ R`; `clip_eq_of_le` оставляет `g` на месте при `‖g‖ ≤ R`, а `clip_idem` доказывает идемпотентность при `R ≥ 0`.
- **`HybridState.lean`** — `stale_momentum_bias`: если `slot = g0`, существует bias, для которого `slot = gt + bias` и `‖bias‖ = ‖g0-gt‖`; доказана только эта одношаговая алгебра.
- **`Joint.lean`** — `jointStep_conflict_regression`: при `L > 0`, `g ≠ 0`, `gc ⬝ᵥ g < 0`, двусторонней квадратичной посылке `-L*‖v‖² ≤ vᵀHc v ≤ L*‖v‖²` и `0 < lr < 2*|gc ⬝ᵥ g|/(L*‖g‖²)` приращение `quadIncr`
- **`JointPreserve.lean`** — `diversity_noncollapse` фиксирует верхнюю траекторную оценку через стартовое разнообразие и геометрическую сумму инъекций; сама по себе она не даёт положительного нижнего порога.
- **`LazyAdam.lean`** — `lazyDecay_exact` вычисляет `d`-кратную итерацию `x ↦ beta2*x` как `beta2^d*v0`; `dense_m_decay` даёт аналогичную формулу траектории момента.
- **`LiveDeltaSafe.lean`** — `safe_update_window`: при `L i > 0`, `eps i ≥ 0`, `eta ≥ 0`, `d ≠ 0`, квадратичной посылке `h_lipline` и `eta ≤ safeqpEtaMax g eps L d` доказано `dL i ≤ eps i` для всех защищаемых целей.
- **`MDLThreeCurrency.lean`** — `mdlObjective_delta` раскладывает изменение цели в изменение ошибки предсказания плюс `λ` на изменение длины описания.
- **`Muon.lean`** — `muon_step_bound` и квадратичный `muonDir_norm_sq_le`: если `‖P z‖ ≤ ‖z‖` для всех `z`, то `muonDir P g` не увеличивает норму и квадрат нормы.
- **`NCEExact.lean`** — `nce_decomposition`: при `0 < p v → 0 < q v` на поддержке `p` выполнено `log p = log q + log(p/q)`; `nce_correction_pos` доказывает положительность этой коррекции.
- **`NewtonSchulzMatrix.lean`** — `newton_polar_scalar_error` при `x > 0` даёт точное `newtonStep x - 1 = (x-1)^2/(2*x)`; одновременно `newtonStep x ≥ 1`. На ветви `x ≥ 1` доказаны `newton_step_descent` и оценка ошибки
- **`NoisyPL.lean`** — `variable_telescope`: если `0 ≤ c t ≤ c0 < 1`, `d ≥ 0`, `e 0 ≤ e₀` и `e(t+1) ≤ c t*e t + d`, то `e t ≤ (∏_{k<t}c k)*e₀ + d/(1-c0)`.
- **`PreconditionerDescent.lean`** — `preconditioned_descent`: при `L ≥ 0`, `mu > 0`, `alpha > 0`, `alpha < 2*mu/L`, коэрцитивности `mu*‖u‖² ≤ ⟪g,u⟫` и квадратичной гладкости получается оценка с множителем
- **`ProjectionDescent.lean`** — `min_dist_to_vi`: для выпуклого `C`, `ds ∈ C` и минимальности `dist ds g0` среди всех `d ∈ C` выполнено `⟪g0-ds,w-ds⟫ ≤ 0` для всех `w ∈ C`.
- **`RiemannNewtonPolar.lean`** — `radial_tangential_curvature`: при `r > 0`, глобальных `HasDerivAt φ (g x) x` и `HasDerivAt g (gg x) x` производная по `s` от `deriv (fun s' => φ (sqrt(r^2+s'^2))) s` в нуле равна `g r/r`.
- **`RobustDescent.lean`** — `biased_norm_upper` и `biased_inner_lower`: из `‖ĝ-g‖ ≤ m` следуют `‖ĝ‖ ≤ ‖g‖+m` и `(‖g‖²-m²)/2 ≤ ⟪g,ĝ⟫`.
- **`SNRWeights.lean`** — `uniform_is_mean` переписывает сумму `(1/r)*(dev i)^2` как `(∑dev i^2)/r`; условие `r > 0` в самом тождестве не требуется из-за тотализации деления Lean.

## Hagi/Step/SafeQP.lean

- Минибатч-оценка `ĝᵢ = gᵢ + m⁻¹Σⱼ ξᵢⱼ` имеет точную проекцию
  `⟪ĝᵢ,d⟫ = ⟪gᵢ,d⟫ + m⁻¹Σⱼ⟪ξᵢⱼ,d⟫`.
  При фиксированном `d ≠ 0`, `σ > 0`, `0 < δ < 1` и измеримых, центрированных,
  независимых по `j < m` проекциях с `‖ξᵢⱼ‖ ≤ σ`,
  `stochastic_safeQP_feasibility` переносит оценочные ограничения
  `−eps i ≤ ⟪ĝᵢ,d⟫` в истинные `−(eps i + noiseEps) ≤ ⟪gᵢ,d⟫`
  с вероятностью не менее `1 − δ`.

## Hagi/Step/

- **`SafeQPStep.lean`** — `safeqp_eta_max_conflict_free`: при `L i > 0`, `eps i ≥ 0`, `0 ≤ eta`, `d ≠ 0`, `⟪g i,d⟫ ≥ 0` и линейной оценке `dL i ≤ −eta⟪g i,d⟫ + L i·eta²‖d‖²/2` условие
- **`SignSGD.lean`** — `sign_inner_nonneg`: для каждого конечного `g` `Σᵢ sign(gᵢ)gᵢ = Σᵢ |gᵢ| ≥ 0`.
- **`Upgrades.lean`** — `skip_bound`: если `p = softmaxW s` — распределение и масса `δ` пропущенного множества меньше `1`, после удаления этого множества и перенормировки сумма абсолютных изменений весов не
- **`WarmupSchedule.lean`** — `warmup_eta_monotone`: при `c ≥ 0`, `ρ,Kρ > 0` и `0 < Δ' ≤ Δ` выполняется `warmupEta(Δ) ≤ warmupEta(Δ')`.
- **`WeightDecay.lean`** — `wd_norm_bound`: при `λ > 0`, `0 ≤ eta λ ≤ 1`, `‖g t‖ ≤ G` и рекуррентности `w(t+1) = (1−etaλ)w(t) − eta·g(t)` для всех `t` выполняется `‖w t‖ ≤ max(‖w 0‖,G/λ)`.

## Hagi/System/Certificates.lean

- `cycle_certificate_sound`: при `lam,nu ≥ 0`, согласованной цепочке
  сертификатов и условии
  `lam(Rgrow+Rmerge+Rjoint) + nu·epsQ ≤
    gap + eta·inner − L·eta²dnorm²/2 − κqerr`,
  конечный потенциал `E + lam·R + nu·max(0,qTarget−q)` не превышает начального.

## Hagi/System/GrowthState.lean

- Определение `joint` задаёт именно `params' = params − eta·stepDir`,
  `energy' = effects.jointEnergy`,
  `protectedRisk' = protectedRisk + effects.jointRisk` и
  `budget' = budget − effects.jointCost`; `potential S = energy + protectedRisk`.

## Hagi/System/

- **`StepCertificate.lean`** — `stepCertificate_base`: базовая часть сертификата, построенного по состоянию и `epsG ≥ 0`, совпадает с `verify S`.
- **`UnifiedStep.lean`** — `unified_step_budget`: при `Δ,Tt > 0` гиббсовы веса дают ожидаемую потерю не выше `m + Tt·log|ι|` для некоторой нижней границы `m` всех потерь, а ошибка `gridQ` композитного обновления не

## Hagi/Research/Legacy/AdvanceWitness.lean

- `certified_invariant_advance_witness`: на горизонте `2` фактические поля
  траектории удовлетворяют `CertifiedHAGIInvariant` с `alpha=1`;
  capability проходит `1→2→4`, бюджет `100→98→96`.

## Hagi/Unified/AnytimeMartingale.lean

- `merge_stage_linked`: при `w t ≥ 0` и `Σt w t = 1` взвешенная
  categorical CE среднего логита не превосходит взвешенного среднего CE
  отдельных логитов.

## Hagi/Unified/StitchingEProcess.lean

- `stitchedMaster w E = Σ i, w i • E i`; `stitching_master_supermartingale`:
  a finite family of supermartingales with nonnegative weights stitches
  into a supermartingale (Finset-induction, Mathlib canon
  Mathlib Supermartingale.add / Supermartingale.smul_nonneg; the
  empty case is gated by
  `[Nonempty k]` — the zero-process certificate needs an unavailable
  norm instance on the bare Pi type).

## Hagi/Unified/CountableStitching.lean (P4 E3)

- `stitchedMasterCountable w E t = ∑' k, w k * E k t` — счётное
  (tsum) сшивание мастером; веса на ℕ с посылкой `Summable w`
  (load-bearing: без неё junk-tsum опровергает теорему,
  контрпример w = (3/2)^k с E ≡ 2^{-k} задокументирован в шапке
  модуля).

- `stitching_countable_initial_mass`: μ[M₀] = ∑' w k · μ[E k 0] —
  счётный аналог `stitching_master_initial_mass`; tsum/integral
  interchange через Mathlib-леммы integral_tsum и
  ofReal_integral_norm_eq_lintegral_enorm (ennreal-кастинг —
  вся счётная бухгалтерия).

## Hagi/Architecture/SpaceDecoupling.lean

- `projI U = U·Uᵀ`, `projR U = 1 − U·Uᵀ`; `projI_add_projR`
  (P_I + P_R = 1 exactly), `projI_idem`/`projR_idem`
  (idempotence under `IsOrthoCol U`).

## Hagi/Research/Legacy/ArchitectureTheorem.lean

- `entropy_continuity_pinsker`: если уже доказана граница
  `|H(p)−H(q)| ≤ τ log(|V|−1) + h₂(τ)`, а также `0 ≤ τ ≤ 1/2`,
  `τ ≤ √(kl/2) ≤ 1/2`, `log(|V|−1) ≥ 0` и монотонность `binEnt`
  на данном отрезке, то получается та же граница с `√(kl/2)` вместо `τ`.

## Hagi/Research/Legacy/Assumptions.lean

- `masterhagi_trunc_of_assumptions`: пакет `Trunc S lam nu Qtarget Emin T`
  заменяет стадийные, бюджетные и нижние энергетические предпосылки;
  при отдельных SafeQP-окнах и усечённых законах роста он даёт тот же
  `CertifiedHAGIInvariant`.

## Hagi/Semantics/CanonicalParams.lean

- `advance_params_ne`: для перехода с `u.stepDir ≠ 0`
  канонические `S.params` действительно различаются; положительность шага
  закреплена типом входного перехода.

- `bridge_update`: законный инъективный проектор toW переносит это различие
  на `canonWeights`; `idProj` доказывает существование такого проектора
  на `Fin d → ℝ`.

## Hagi/Growth/CapabilityLocal.lean

- `capability_geometric_of_local`: при `alpha > 0`,
  `capability(t+1) = capability t + growGain t` и
  `alpha·capability t ≤ growGain t` для всех `t` получается
  `capability 0·(1+alpha)^T ≤ capability T`.

## Hagi/Research/Legacy/CertifiedGrowth.lean

- `certified_gainprod_takeoff`: для `[0,1]`-наблюдений, `n,eps > 0`,
  `alpha,gamma,C0 > 0`, `rho ≥ 0`, начального конуса, принятого моста
  от средних к `γD t ≤ G t` и усечённых законов
  `C(t+1)=C t+G t`, `D'`, верхнего `(1+alpha)` и β-порога
  выполняется вероятностная импликация:
  из всех margins `ΣX + 2n eps ≤ ΣY` для `t < T`
  следует `C0(1+alpha)^T ≤ C T` с нижней оценкой вероятности
  `1 − 2T·exp(−2n·eps²)`.

## Hagi/Unified/CertifiedLoop.lean

- `certified_loop`: если начальный `FloorKept` и `0 ≤ b 0` даны, а каждое
  звено — `StepCert`, то сумма `(certs t).trans.objectiveDrop` не превосходит фактического
  убывания `obj(f 0)−obj(f n)`, финальное качество удовлетворяет floor,
  `b n ≥ 0` и `b n ≤ b 0 − Σ budgetSpend`.

- `certified_loop_all` сохраняет компонентный floor на каждом `t ≤ n`;
  `certified_loop_strict` при `n ≥ 1` дополнительно даёт
  `obj(f n) < obj(f 0)`.

## Hagi/Unified/

- **`CertifiedTrajectory.lean`** — `certified_progress_honest`: при `decrease = claimed`, `Φ(t+1) ≤ Φt − decrease + riskCost`, `Φ_min ≤ Φt` для всех `t ≤ T` и заданном интервале `measured−δ ≤ claimed ≤ measured+δ`
- **`CommitGate.lean`** — `commitProductive`: активный `gate c` влечёт `commitV c < c.V`; `holdSafe` даёт точное равенство `holdV c = c.V`.

## Hagi/Research/Legacy/CorePremisesDerived.lean

- `core_premises_joint_operational` и `core_premises_compress_operational`
  выводят квадратичный joint и квантованный compress из дифференцируемости,
  ограничений производной и операциональных равенств энергий, а не из
  свободно назначенных полей.

## Hagi/Unified/CostComposition.lean

- `hybrid_cost_lt`: при `L ≥ 1`, `k < n` и `2w+1 < n`
  `hybridCost L k w < denseCost L n`.

- `hybrid_ratio_le`: при тех же условиях отношение стоимостей
  не превосходит `(k/n)·((2w+1)/n)`. Стоимости — заданные модельные формулы,
  а не измеренные аппаратные затраты.

## Hagi/Training/Ctv2Telescope.lean

- `ctv2_family_telescope`: для фактических `S(t+1)=advance(S t,u t)`,
  сертификатов `CertifiedTransitionV2`, grow/merge-оценок, `0 < L`,
  `eta ≤ 1/L`, `‖stepDir‖² ≤ inner`, квадратичного joint и
  `compressEnergy−jointEnergy ≤ κ·s·quantErr`
  получается `Σ stepDrop(u t) ≤ energy(S0) − energy(S T)`.

## Hagi/Unified/

- **`DerivAlong.lean`** — C233 (R2): `ceStepLogitRange_sq_le_featureMass_sq_norm_sq` — острая по-примерная `ceStepLogitRange² ≤ 4·featureAbsSum²·‖ceDirection‖²`; `ceStepLogitQuad_le_engine`
- **`DescentCore.lean`** — `descent_drop`: в `Objective` с `L > 0` и заданной descent-леммой, если `‖dir‖² ≤ ⟪grad x,dir⟫` и `0 < eta ≤ 1/L`, то `f(x−eta·dir) ≤ f x − eta(1−L·eta/2)‖dir‖²`.
- **`DescentCoreDiag.lean`** — `diag_descent_eq`: для `diagE a y x = ½Σᵢaᵢ(xᵢ−yᵢ)²` доказано точное разложение `E(x+d) = E x + ⟪a∘(x−y),d⟫ + ½Σᵢaᵢdᵢ²`.
- **`DescentCoreQuad.lean`** — `quad_eta_identity`: для `quadE a w = ½Σᵢ(wᵢ−aᵢ)²` и градиента `w−a` выполняется `quadE(w−eta·grad) = (1−eta)²quadE a w` (мост над `Hagi.Foundations.quad_eta_identity` из
- **`Distillation.lean`** — `soft_dial_max` и `soft_dial_zero`: `softProb x → 1` при `x→+∞` и `softProb x → 1/2` при `x→0`.

## Hagi/Theory/Compression.lean

- `ef_iterate_shadow`: при `e(t+1)=d t+e t−comp(d t+e t)`,
  рекуррентностях сжатой и полной траекторий с общим началом
  получается точное `xC n−xF n = eta·(e n−e 0)`.

- `thrComp_barrier`: квадрат нормы несжатого остатка порогового
  компрессора ограничен `|k|·τ²`.

## Hagi/Unified/EmpiricalPremises.lean

- `premises_give_smooth`: монитор `holds p`, условие
  `dnorm² ≤ inner` и отдельно принятая квадратичная модель hsmooth
  дают `E2 ≤ E1 − eta·dnorm²/2`; монитор сам модель не доказывает.

- `premises_lip_witness`: при `holds p` и `s ≥ 0` доказана только
  `0 ≤ κ·s·dnorm`, а не требуемая липшицева оценка энергии.

## Hagi/Unified/ParetoExecution.lean

- `finiteSelection_cost_eq_minimumResource`: если вычислимый список
  содержит все действия, выбранная стоимость совпадает со стоимостью
  математического минимума в cast-модели; совпадение самих действий при равных
  стоимостях не утверждается.

- `selectionReport_comparisons`: число вызовов отношения равно
  `admitted.length − 1` и не превосходит длины исходного списка.
  Это логические вызовы, не инструкции процессора или время.

- Частные результаты показывают, что фильтрованный выбор реально является
  `List.argmin` по memory-first стоимости среди допущенных элементов списка.
### Hagi.Unified.ExecutableSelection — merged into ParetoExecution

## Hagi/Training/ExecutedCert.lean

- `measured_honest` и `measured_lower`: зависимый сертификат связывает
  измерение `m`, фактический спуск `C.drop` и ошибку `d` неравенствами
  `drop−d ≤ m ≤ obj(s)−obj(step s)+d`, а `drop > 0` входит в сертификат.

- `telescope_measured`: по исполненной цепочке из `n` шагов
  `Σm ≤ obj(s)−obj(traj step s n) + Σd`, и все шаговые `(cs t).drop` положительны.

## Hagi/Semantics/FunctionalState.lean

- `fs_two_steps_productive`: при `0 < eta < 2`, `eta ≠ 1`, `a ≠ w`
  и `s.weights = w` два последовательных `funStepJoint` строго убывают
  энергию на каждом шаге. Условие `eta ≠ 1` гарантирует ненулевой остаток
  после первого шага.

- `fs_energy_after` вычисляет энергию преемника из его новых весов,
  а не копирует старое значение.

## Hagi/Theory/GaugeQuotient.lean

- `quotientResidual_gauge_invariant`: остаток
  `r_G(z) = inf_φ‖Tz−e^{iφ}z‖` не меняется при фазовом вращении.

- `relativeEquilibrium_residual_zero`: если `Tz = rot φ₀ z`, то `r_G(z)=0`;
  `relativeEquilibrium_orbit` дополнительно даёт `T^k z = rot(kφ₀) z`.

- `seq_dev_exact` при `s ≠ 1` даёт точное решение скалярной модели
  `x_t−c/(1−s) = s^t·(x₀−c/(1−s))`.

## Hagi/Research/Legacy/GrandSynthesis.lean

- `grand_synthesis_weak`: при заданных границах сертификации стадий,
  `κD t ≤ E_raw`, производственной динамике, начальном конусе
  `kC0 ≤ D0`, неотрицательных `C,D` и условиях связывания коэффициентов
  получается `C0(1+(beta⁴κ)k)^T ≤ C T`.

## Hagi/Training/GrowthComputedCert.lean

Именованных top-level theorem-деклараций нет; носители результата —
две definitions.

- `next S eta`: сохраняет все каналы `S`, кроме замены `S.weights`
  на `growthStep S.weights eta`.

- `stepCert`: при `0 < eta < 2` и `Σᵢ S.weightsᵢ² ≠ 0`
  создаёт `CertStep` с `drop = (1−(1−eta)²)growthQuad S.weights`.
  Его поля `CertStep.drop_pos` и `CertStep.actual` содержат доказательства положительности
  и фактического неравенства, но не являются отдельными top-level теоремами.
### Hagi.Unified.GuardedRobustLogit — merged into ParetoExecution

## Hagi/Unified/HonestTransition.lean

- `honest_actual_drop`: сертификат содержит строгое фактическое убывание
  `obj s' < obj s` и `objectiveDrop > 0`, а не только положительность
  числового показателя.

- `honest_telescope`: два связанных перехода дают
  `obj s2 ≤ obj s0 − (drop1+drop2)`.

## Hagi/Growth/InterpretiveGrowth.lean

- `pointEffect` и `causalEffect` неотрицательны; нулевое изменение выхода
  на всём выбранном наборе даёт нулевой эффект, а существование точки с
  положительным эффектом делает средний эффект положительным.

- `mass_split`: для неотрицательных весов сумма живой и пассивной массы
  равна полной массе.

## Hagi/Research/Legacy/LearningKernel.lean

- `grow_premise_derived`: если `LearningKernel` даёт
  `capability' ≤ energy'` и `energy' = energy−growEnergy`, а дополнительно
  `growGain ≤ capability'−capability` и `capability ≥ 0`, то
  `growEnergy ≤ energy−growGain`.

## Hagi/Unified/

- **`LinkedProjects.lean`** — `value_iteration_via_contraction`: при `0 < gamma < 1`, `eps ≥ 0` и `V(k+1)−Vstar(k+1) ≤ gamma(Vk−Vstar k)+eps` получается для всех `k`
- **`LinkedQVec.lean`** — `floor_preserved`: если начальное и каждое состояние списка удовлетворяют `FloorKept`, последнее состояние тоже сохраняет покомпонентный floor.

## Hagi/Research/Legacy/LinkedWitness.lean

- `wTraj_certified_family`: три конкретных перехода удовлетворяют
  `CertifiedTransition` при сумме стадийных рисков как пределе.

- `linkedHAGI_witness`: эта непустая траектория с `capability 1→8` и
  `budget 100→94` реализует `LinkedHAGIInvariant` на горизонте `3`
  с `alpha=1`.

## Hagi/Unified/

- **`LiveDeltaCycle.lean`** — `live_delta_cycle`: при SafeQP-окне в фактор-пространстве, `L i > 0`, `eps i ≥ 0`, `eta ≥ 0`, `d ≠ 0`, заданной линейной оценке, принятом динамическом аудите и допустимом масштабе базы
- **`Liveness.lean`** — `liveness_merge`: если `p` строго положительно и нормировано, а отклонения `d` не являются общим константным вектором, то `twoGap p d > 0`.
- **`LogitCert.lean`** — `logitCE_strictAnti`: скалярная `logitCE` строго антитонна.

## Hagi/Theory/LogitGrowth.lean

- `step_params`, `step_energy` и `step_capability`: вычисленный преемник имеет
  `params' = next(S.params,eta)`, `energy' = logitCE(params')`, а при
  `capability = −logitCE(params)` и `capability' = −logitCE(params')`.
  Так прирост capability — тот же CE-спуск, без второго учёта каналов.

## Hagi/Unified/

- **`LoopInstances.lean`** — `quadCert_hits_optimum`: на квадратичной цели шаг `x−quadGrad a x` даёт `quadE = 0`.
- **`MachineProto.lean`** — `machineProto_gap`: вычисленный `machineGap a w eta` равен `(machineProto a).loss w − (machineProto a).loss(jointStep a w eta)`, так что величина шага берётся из функции весов.

## Hagi/Research/Legacy/MasterHAGI.lean

- C304 (A12 credo quarantine): linked-вариант капстоуна
  (R362) удалён — deprecated, 0 потребителей; `MasterHAGI`/
  `MasterHAGICore` оставлены — живые потребители
  (`MasterHAGICoreOperational_v2`, nonvacuity-witness в
  `Hagi/Research/Legacy/Nonvacuity.lean`).

## Hagi/Research/Legacy/

- **`MasterHAGICoupled.lean`** — `CoupledHAGIInvariant` связывает канал capability непосредственно с состояниями и содержит отдельные неотрицательные spend/risk, векторный probe-floor и бюджетную бухгалтерию.
- **`MasterHAGITrunc.lean`** — `MasterHAGI_trunc`: сохранён (recheck: живой потребитель — capstone-мост в `Hagi/Research/Legacy/Assumptions.lean`).

## Hagi/State/MemoryCycle.lean

- `descentFold_eq_effective`: для истории пар `(v,x)` плотная свёртка
  `W₀+Σ outerProd(v,x)` точно равна эффективным весам представления
  `fromHistory W₀ hist`.

- `history_storage_cost`: число сохраняемых элементов блоков равно
  `hist.length·(|m|+|n|)`.

## Hagi/Semantics/MemorySemantics.lean

- `RamWriteCert` требует `post = Matrix.updateRow pre address value`,
  чтение по address возвращает value, посторонние адреса неизменны,
  повторная запись идемпотентна.

- `CertifiedMemoryWrite` добавляет фактический `admit c`;
  `certified_gain_margin` извлекает из него
  `lamM·Δcost + lamR·Δrisk + ε_cert ≤ gain`.

## Hagi/Unified/MicroStepCert.lean

- `microstep_cert`: из квадратичной оценки `E`, `frobDot G ΔW ≤ −ε`
  и GPM-ортогональности следует
  `E(W+ΔW) ≤ E W − ε + L/2·frobSq ΔW` и
  `(W+ΔW)x_k = W x_k` для каждого защищаемого входа.

- `microstep_net_drop`: если дополнительно `L/2·frobSq ΔW < ε`,
  энергия строго убывает при сохранении всех этих действий на входах.

## Hagi/Training/ModelComparison.lean

- `delta_pos_of_dominates`: при `λ > 0`, `ρ ≥ 0`,
  `logS−logR ≤ ρ` и `cS−cR > ρ/λ`
  разность `loglik−λ·complexity` строго положительна.

- `piR_lower_of_certified`: для индикаторов `zⱼ∈[0,1]`,
  `k ≤ N`, `N > 0` и первых `k` единиц получается `k/N ≤ piR z N`.

## Hagi/Unified/

- **`NCStepCert.lean`** — `nc_loop_horizon`: при положительных gains, допустимых риске и бюджете, покомпонентном начальном floor и `n ≥ 1` энергия траектории строго убывает, а `S.cpu` остаётся исходным.
- **`NegativeTests.lean`** — `risk_limit_respected`: любой `StepCert` даёт `riskSpend ≤ riskLim` непосредственно из своей структуры.
- **`CandidateConfig.lean`** — `CandidateConfig`: кандидатная конфигурация — все параметры вычисляются как функции целей; глобальная оптимальность НЕ доказана и не заявляется (аудит A17).

## Hagi/Dynamics/ProductiveTransition.lean

- `idle_not_productive`: при `δC,δL > 0` переход `S → S`
  не удовлетворяет предикату `Productive`.

- `ctv3_idle_contra`: `CertifiedTransitionV3` несовместим с равенством
  энергии до и после перехода; `productive_of_ctv3` получает `Productive`
  при фактическом спаде не меньше `δL > 0`.

- `budget_consumed`: при `0 ≤ e t + delta t` свойство `BudgetAlive e delta eps (T + 1)` влечёт `BudgetAlive e delta eps T`.

## Hagi/Unified/QuadMachine.lean

- `quadE_eq_energy` и `quadGrad_eq_grad`: квадратичная энергия и градиент
  вычислительной машины совпадают с соответствующими определениями
  `DescentCoreQuad`.

- `machine_one_step_zero`: на этой модели шаг с `eta=1` обнуляет энергию.

## Hagi/Unified/

- **`RateTheory.lean`** — `pl_linear`: если `κ ≥ 0`, `μ > 0`, `2κμ < 1`, `Estar ≤ obj(f t)`, `2μ(obj−Estar) ≤ gsqr`, `κ·gsqr ≤ drops` и `obj(t+1) ≤ obj t−drops`, то `obj(f n)−Estar ≤ (1−2κμ)^n(obj(f 0)−Estar)`.
- **`RecursiveClean.lean`** — `clean_neuron_of_conditions`: из структуры `CleanCertificate`, положительной внесетевой массы вне корня и непустого множества рёбер следует `branchLocality ≤ εA`, `timeConsistency = 1` и

## Hagi/Research/Legacy/RecursiveGrowth.lean

- `macro_step_decrease`: при merge-выигрыше `G ≥ 0`, `0 < L`,
  `0 ≤ eta ≤ 1/L`, `dnorm² ≤ inner`, квадратичной joint-оценке,
  `κ,s,dnormq ≥ 0`, `dnormq ≤ 1/2` и compress-Lipschitz оценке
  получается `E4 ≤ Emean − (G + eta·dnorm²/2 − κs/2)`.

- `safeqp_eps_critical`: при нижней энергии Emin,
  `E(t+1) ≤ E t−eta t·dn t²/2`, `etamin > 0`,
  `eta t ≥ etamin`, `eps > 0` и `dn t² ≥ eps²`
  горизонт удовлетворяет `n ≤ 2(E0−Emin)/(etamin·eps²)`.

## Hagi/Unified/

- **`SignComp.lean`** — `signStepCert`: на квадратичной цели, если `quadGrad a x ≠ 0`, `0 < eta ≤ 1`, начальный floor и `signCommCost k ≤ riskLim`, строится полный `StepCert` для знакового шага; поле
- **`SignDescent.lean`** — `sign_descent`: масштабированный знаковый шаг `signScale(grad)·sign(grad)` наследует `descent_drop`: при `0 < eta ≤ 1/L` `f(x−eta·dir) ≤ f x−eta(1−L eta/2)‖dir‖²`.

## Hagi/Research/Legacy/StateTakeoff.lean

- `state_capability_takeoff`: при `FullCycleRefinement`,
  `alpha,gamma > 0`, `rho ≥ 0`, положительной начальной capability,
  начальном конусе, `γD t ≤ growGain t`, производственной динамике,
  потолке `(1+alpha)` и β-пороге для `t < T`
  `capability(S0)·(1+alpha)^T ≤ capability(S T)`.

## Hagi/Unified/StepContract.lean

- `trajectory_convergence`: при
  `Φ(t+1) ≤ Φt−decrease+riskCost` и `Φ_min ≤ Φt` для всех `t ≤ T`
  получается `Σdecrease ≤ Φ0−Φ_min+ΣriskCost`.

- `chain_budget` и `chain_risk` доказывают, что составной контракт
  содержит соответственно суммы бюджетных и рисковых затрат звеньев.

## Hagi/Research/Legacy/TernaryGrad.lean

- `quantized_net_gain`: из `gamma·D ≤ Graw` и `Graw−G ≤ p`
  следует `gamma·D−p ≤ G`.

- `quantized_cone_gain`: при `kC ≤ D`, `gamma ≥ 0`,
  `gamma·D ≤ Graw`, `Graw−G ≤ p` и margin
  `p ≤ gamma(D−kC)` доказывается `gamma·k·C ≤ G`.

## Hagi/Benchmarks/

- **`TernaryProbe.lean`** — `ternaryCubicShift_abs_error_le_stepBudget`: при `level,σmax > 0` и `|t| ≤ σmax` ошибка насыщающего тернарного квантования сдвинутой кубической энергии ограничена вычисленным
- **`TernaryWitness.lean`** — `quantOpt_energy_bound`: при `s > 0` и `ternInRange s (a i)` для всех `i` энергия `quadE a (quantOpt s a)` не превосходит `|k|·s²/8`.

## Hagi/Research/Legacy/TopLevel.lean

- `quant_residual_norm` и `quant_energy_bridge`: если
  `|w i−q i| ≤ s/2`, то `Σᵢ(w i−q i)² ≤ n(s/2)²`;
  при `s,κ ≥ 0` и `dE ≤ κ√Σ(w−q)²` получается `dE ≤ κ√n·s/2`.
  Lipschitz-условие остаётся `h_emp_`-посылкой.

## Hagi/Unified/TransitionCert.lean

- `TransitionCert` содержит фактический `obj(step s) < obj s` и
  `risk(step s) ≤ risk s + riskLim`; `of_ctv3` строит его из V3-перехода
  для `energy` и `St.protectedRisk`.

- `certs_telescope`: для фактической цепочки `x(t+1)=step(x t)`
  при `T > 0` цель строго убывает, а `risk(x T) ≤ risk(x0)+T·riskLim`.

## Hagi/Theory/Statistics.lean

- Канон статистик (v4 T3): HoldoutRisk + AnytimePACBayes +
  TwoDomainConfidence + HoldoutWithoutReplacement + AnytimeHoldoutStop
  в одном модуле, исторические namespace'ы и все имена сохранены.

- `holdout_concentration`: для фиксированной до дров модели
  `f : Ω → [0,1]`, k > 0: `P[|holdoutMean − popMean| ≥ ε] ≤ 2exp(−2kε²)`;
  `selection_bias_*` — негатив: выбор модели ПОСЛЕ просмотра holdout
  ломает несмещённость.

## Hagi/Theory/MasterTheorem.lean (v4 T6: + MasterBudget, VerticalCapstone)

- Канон master-траектории (v4 T6): MasterTheorem + MasterBudget
  (бюджет как premise-канал, ns `Hagi.Theory`) + VerticalCapstone
  (ns `Hagi.Unified`) в одном модуле, имена сохранены.

## Hagi/Theory/FlowMatching.lean

- `cfmPsi`/`cfmOtField`/`cfmSigma`: OT-условный путь и замкнутый
  conditional VF (equations 20–22 статьи Flow Matching), честно
  дискретно — на конечном словаре `V`.

- `cfmSampleLoss` + `cfmSampleLoss_eq_sqDiff`: per-sample CFM loss
  === инстанциация C384 `sqDiffObjective` на паре
  (v t (ψ_t x₀), otField) — мост definitional (rfl).

## Hagi/Theory/Interpretability.lean

- `RebuildSystem`/`Rebuildable`: контракт C421 — интерпретируемость
  как description-length bound (iWSP rebuild bottleneck, arXiv
  2611.18114): сертификат = существование описания d бюджетом ≤ B,
  чей rebuild R(d) сохраняет качество в пределах ε по лоссу ℓ.

## Hagi/Cert/StepGen.lean (A10 item 2 step 1)

- `Hagi.Cert.CertStepGen` — ОБЩЕЕ ядро сертифицированного шага
  (A10 target): общий индекс задач `TaskId : Type*` (жёсткий `Fin 5`
  цикла — инстанциация, не ограничение ядра), остаток риска — ПОЛЕ
  riskRem с законом расщепления risk_split (0-пиннинг C254
  невозможен по построению), свёрнутый δ-бюджет на явном
  носителе deltaLevel.

- Мосты: `Hagi.Cert.certStep_to_gen` (каждое замороженное `CertStep`
  вложено; нулевой δ-носитель), `Hagi.Cert.CertStepGen.toCertStep`
  (проекция обратно, δ-канал отбрасывается),
  `Hagi.Cert.certStepDelta_to_gen` (свёртка C245-надстройки).

## Hagi/Contracts/GradientBottleneckIdentification.lean (E2 addendum A10)

- Мост спектральной идентификации C232: `selP_conjTranspose_mul_selP`
  (ортонормированные столбцы row-селектора) → `embedded_gram_eq`
  (Gram-матрицы встроенного и прямоугольного совпадают) →
  `embedded_eigenvalues₀_eq` (перенос спектра через
  `sort_roots_charpoly_eq_eigenvalues₀`: равные матрицы — равные
  charpoly — равные отсортированные спектры) →
  `embedded_singularValues_eq_rect` (square singularValues₀
  встроенной = Rectangular.singularValues на Fin(min)).

## Hagi/Training/StepProvider.lean (merge map A10)

- Интерфейсный слой над `Hagi.Cert.CertStepGen`: `StepProposal`
  (следующее состояние + канонический сертификат CertStepGen —
  носитель неотделим от доказательства), `StepProvider`
  (init + оракул `step : s → Option (StepProposal …)`); провайдер —
  ЗНАЧЕНИЕ (выбор провайдера — решение политики, не typeclass),
  none = сертифицированного продвижения нет (прогресс и hold
  разделены — `HoldStep`).

## Hagi/Model/BackboneTransfer.lean

- C300 (E4 first composition — residual transfer of certified
  descent): `resStep_lipschitz` — residual-шаг `(1+μ)`-липшицев при
  `μ`-липшицевой ветви `f`. `residual_transfer_le`,
  `residual_transfer_descent`,
  `residual_transfer_descent_strict`: сертифицированный спуск
  головы `δ` (C291-посылка hdrop) переносится через один
  residual-блок с утечкой `Lc·μ·‖dx‖` (паттерн C250
  entering-vector на пути обновления; `μ=0` — нулевая утечка).
  Стек: `resStack`/`stackGain` (`∏(1+μᵢ)`, паттерн `cascadeGain`
  из `Hagi.Core.ErrorProp`), `stackGain_ge_one`, `resStack_bounds`
  (взаимная индукция липшицевости и утечки), `resStack_lipschitz`,
  `resStack_leak_le` (`‖G(x+dx)−G x−dx‖ ≤ (∏(1+μᵢ)−1)·‖dx‖`,
  мультипликативная композиция), `resStack_transfer_descent`
  и `resStack_transfer_descent_strict` — перенос спуска через весь
  стек. Скалярные якоря невырожденности (μ=1/10: один блок 1/10,
  два блока 21/100 ≥ 1/5). Честная граница: attention-якобианы,
  RoPE-точность, GDN RAM-звено, RMSNorm-константы — НЕ заявлены
  (лестница продолжений в tech-debt E4-C300).

## Hagi/Model/AttentionTransfer.lean

- C307 (E4 attention rung — attention block transfer composition):
  `attnBranch` — softmax-взвешенная композиция ценностей
  `∑ i, p i • v i x` (веса premise-form: фиксированное
  вероятностное распределение инкапсулирует QK^T-структуру).
  `attn_branch_damped` — интерфейс демпфирования: отклонение
  ветви при возмущении ограничено максимальным откликом
  value-отображений (инстанция `Hagi.Core.attention_error_damped`
  с ошибками `e i = v i (x+dx) − v i x`). `attn_branch_lipschitz`
  — равномерное демпфирование value-отображений μatt даёт
  LipschitzWith μatt ветви. `attn_norm_branch_lipschitz` —
  pre-norm (посылка μn) ∘ ветвь даёт LipschitzWith (μn·μatt) —
  в точности форма блочной гипотезы C300.
  `attention_block_transfer` — один attention-блок (pre-norm +
  взвешенная ветвь + residual) удовлетворяет C300-границе утечки
  `Lc·(μn·μatt)·‖dx‖`. Стек: `AttnBlock`/`attnBlockList`/
  `attnStack`/`attnGain` (`∏(1+μnᵢ·μattᵢ)`),
  `attnBlockList_lipschitz`,
  `attention_stack_transfer_descent` и
  `attention_stack_transfer_descent_strict` — теорема C300 о
  стеке в применении к attention-блокам с композицией
  демпфирований. Скалярные якоря (μ_att=3/10, μ_res=2/10:
  (1+0.3)(1+0.2)−1 = 28/50 ≥ 1/2). Честная граница: softmax-карта
  весов (p от x через QK^T) — premise-форма; Lipschitz RMSNorm —
  посылка μn (звено 4 лестницы); изометрия RoPE на
  нормированном носителе (`rot_norm` сохраняет `pairInner`, не
  норму нормированного пространства) — СЛЕДУЮЩЕЕ звено; полный
  forward/backward FastArch3 НЕ заявлен.

## Hagi/Model/RoPETransfer.lean

- C308 (E4 rope rung — rope isometry transfer composition):
  `rope_pair_inner` — ПОЛНАЯ билинейная сохранность
  `pairInner (rotVec θ m x) (rotVec θ m y) = pairInner x y`
  (блочное 2×2-вращение ортогонально; `rot_norm` — диагональная
  специализация y = x). Транспорт носителя: `toEuc`/`fromEuc`
  переносят `Fin d → ℝ × ℝ` в `EuclideanSpace ℝ (Fin d ⊕ Fin d)`
  с точным равенством норм `‖toEuc x‖² = pairInner x x`
  (`toEuc_norm_sq`). `rope_isometry` — перенесённое вращение
  `rotEuc = toEuc ∘ rotVec ∘ fromEuc` — ИЗОМЕТРИЯ носителя
  (`‖R a − R b‖ = ‖a − b‖`). Композиция: `rope_block_transfer` /
  `rope_block_post_transfer` — пре/пост-композиция с изометрией
  сохраняет константу Липшица (μ неизменно).
  `attention_block_rope_transfer` — RoPE-обёрнутый pre-norm
  attention-блок удовлетворяет ТОЙ ЖЕ C300-границе утечки при
  неизменном μn·μatt. Стек: `attnRopeBlockList`/`attnRopeStack`/
  `attnRopeGain` = `attnGain` (`attnRopeGain_eq`: обёртка не
  меняет фактор утечки), `attnRopeBlockList_lipschitz`,
  `attention_rope_stack_transfer_descent` и `_strict` — теорема
  C300 дословно на обёрнутых блоках. Якорь: d=2, θ≡π/3, m=1 на
  ![(3,4),(0,0)] — норма 5 сохранена. Честная граница: нет
  матричной ортогональности (RᵀR=I) и операторной нормы; softmax
  и RMSNorm — premise-форма; полный FastArch3 НЕ заявлен.

## Hagi/Model/RMSNormTransfer.lean

- C309 (E4 rmsnorm rung — RMSNorm Lipschitz constant discharge):
  предпосылка `μn` из C307 разряжена в ЯВНЫЕ честные константы,
  согласованные с точным определением носителя `rnVec x i =
  x i / sqrt (ms x)` (чистая форма Zhang–Sennrich: без ε-пола,
  без аффинного веса g). Транспорт носителя: `msE`/`rnEuc`/
  `rnEpsEuc` на `EuclideanSpace ℝ (Fin n)` поточечно через
  `WithLp.ofLp`/`WithLp.toLp`, точный мост норм `norm_eq_sqrt`
  (‖x‖ = √n·√(msE x)). Честный вердикт по константам: чистый
  носитель НЕ липшицев глобально — закреплено ОТРИЦАНИЕМ
  `rnEuc_not_lipschitz_with` (n ≥ 2: направления δ•eₐ, δ•e_b
  переходят в ФИКСИРОВанные единично-RMS направления √n•eₐ,
  √n•e_b при ‖x−y‖ ~ δ√2 → 0); на области `{z | r ≤ ‖z‖}` —
  `rn_lipschitz_region` с константой μn(r) = 2√n/r (радиальная
  форма `rnEuc x = (√n/‖x‖)•x` + обратное неравенство
  треугольника); ε-полный вариант `rnEpsEuc ε x i =
  x i / sqrt (msE x + ε)` ГЛОБАЛЬНО (2/√ε)-липшицев
  (`rnEpsEuc_lipschitz`) через точное сопряжение
  (gy−gx)(gy+gx) = △msE и евклидову Коши–Шварца `msE_abs_sub_le`.
  Wiring: `residual_transfer_le_pointwise` (утечка C300 в точке
  шага из поточечной оценки отклика ветви), `attention_block_
  transfer_rmsnorm` — ТЕОРЕМА ЗВЕНА: блок C307 с разряженной μn
  (посылки области на обоих концах шага), составная константа
  Lc·((2√n/r)·μatt) явная; стек-инстанс `attention_stack_
  transfer_rmsnorm_eps` (+ `_strict`) — теорема C307 c μn(ε) =
  2/√ε через ε-полные pre-norms (`μnEps`). Якоря (n=4):
  константа области 2·√4/1 = 4; ‖rnEuc (3,4,0,0)‖ = 2
  (треугольник 3-4-5 через `rnEuc_eq` + `norm_eq_sqrt`). Честная
  граница: глобального липшица чистого носителя НЕ заявлено
  (закреплено отрицанием); аффинного веса g в носителе нет (если
  появится — константы масштабируются на max|g|); softmax-карта
  весов — premise-форма; полный FastArch3 certificate НЕ
  заявлен.

## Hagi/Model/GDNTransfer.lean

- C310 (E4 GDN rung — GDN block transfer + hybrid stack): GDN-сто-
  рона гибридного attention+GDN backbone встроена в C300 transfer
  stack, посажена HYBRID-теорема (стек из attention- и GDN-блоков
  спускается с произведением gain). Вердикт по форме GDN (pin):
  в репо три формы — (1) GDNBridge one-hot RAM-адресация (C254,
  семантика чтения/записи, не state-оператор); (2) GDN2 memory
  update `M̃' = (I−UᵀU)·D·M̃ + Uᵀ(ω⊙V)` (аффинен по памяти,
  rowSumNorm `gdn2_step_bound`, матричное пространство); (3) mHC
  STATE MIXING `x ↦ M *ᵥ x` с M дважды стохастической.
  Блок GDN здесь — форма (3): mixing-ветвь с GDN-гейтом в
  PREMISE-форме (μg-липшицев пред-гейт, зеркально пре-норм C307).
  Транспорт носителя: `gdnMix M x = toLp 2 (M *ᵥ ofLp x)` на
  `EuclideanSpace ℝ n` (как в C309). ГЛАВНАЯ лемма:
  `gdnMix_lipschitz` — `IsDoublyStochastic M ⇒ LipschitzWith 1
  (gdnMix M)` — сжатие C231 `doublyStochastic_sq_le` на разности,
  поднятая в евклидову норму мостом `EuclideanSpace.real_norm_sq_eq`
  (`gdnMix_norm_sub_le`). `gdn_branch_lipschitz` — гейт μg ∘
  mixing ⇒ μg-липшицева ветвь (форма гипотезы блока C300);
  `gdn_block_transfer` — утечка C300 `Lc·μg·‖dx‖` на одном блоке.
  Стек: `GdnBlock`/`gdnBlockList`/`gdnStack`/`gdnGain`,
  `gdn_stack_transfer_descent` (+ `_strict`), gain `∏ (1+μgᵢ)`
  (mixing 1-липшицев — роста нет). HYBRID (payoff звена):
  `HybBlock` (inductive: конструкторы att | gdn), `hybBlockList`/
  `hybStack`/`hybGain`, `hybBlockList_lipschitz` (диспетчеризация
  по конструктору: C307-адаптер для attention, C231-бэкед для
  GDN), `hybrid_stack_transfer_descent` (+ `_strict`) — теорема
  C300 на гетерогенном списке блоков, каждый со своим μᵢ
  (attention μn·μatt, GDN μg). Якоря: единичная матрица дважды
  стохастическая (невакуумность посылки mixing); числовая μ-ком-
  позиция hybrid (att 3/10, gdn 2/10 ⇒ утечка (1+3/10)(1+2/10)−1
  = 14/25); мультипликативность ≥ аддитивности. Честная граница:
  GDNBridge RAM-чтение/запись и GDN2 memory update НЕ заявлены
  как state-сжатия; нелинейный гейт — premise-форма μg; Sinkhorn
  НЕ заявлен (IsDoublyStochastic — посылка, граница C231);
  softmax — premise-форма; полный FastArch3 certificate НЕ
  заявлен.

## Hagi/Model/FastArch3Transfer.lean

- C311 (E4 FINAL rung — FastArch3 end-to-end transfer assembly):
  end-to-end FastArch3-SHAPED certified-descent теорема —
  параметрический SoftmaxHead поверх гибридного стека
  (C307 attention + C308 RoPE + C309 RMSNorm + C310 GDN), чистая
  КОМПОЗИЦИЯ уложенных носителей с явным PREMISE LEDGER. Форма:
  `FA3Block n ι` (inductive: `att a R` — attention-блок C307 с
  RoPE-обёрткой R — посылка Isometry, инстанцируется rotEuc C308,
  константа не меняется; `gdn g` — GDN-блок C310), `FastArch3Spec`
  (blocks + C283 `HeadConfig`), `fa3BlockList` (attention μn·μatt,
  GDN μg), `fa3Stack`/`fa3Gain` (∏(1+μᵢ), C300 stackGain),
  `fa3BlockList_lipschitz` (dispatch: C307-адаптер ∘ изометрия
  C308-паттерном (hR.lipschitzWith, mul_one); C310-адаптер),
  `fa3Objective` (потеря на выходе стека — полная objective
  модели), ГЛАВНАЯ `fastarch3_transfer_descent` (+ `_strict`):
  теорема C300 на списке FastArch3-блоков — сертифицированный
  спуск головы δ (посылка формы C291, инстанцируется
  `ceOneHot_next_le_param`) + Lc-липшицева потеря головы ⇒ утечка
  `Lc·(∏(1+μᵢ)−1)·‖dx‖`; гвард δ > утечки ⇒ STRICT убывание
  end-to-end objective. Якоря: rotEuc изометрия; spec-невакуум-
  ность; 2-блочный инстанс (att μn·μatt = 1.4·0.4 = 0.56, gdn
  μg = 0.2 ⇒ утечка (1.56)(1.2)−1 = 0.872; drop 0.5 > 0.436).

## Hagi/Data/AnfTransform.lean

- C301 (E5 ANF/Möbius core — Zhegalkin transform correctness):
  `anfTransform` — преобразование Жегалкина/Мёбиуса как рекурсивная
  «бабочка» на последней координате (`T f = (T f₀, T f₀ ⊕ T f₁)`,
  вычислимое, носитель `(Fin n → Bool) → Bool` — таблицы истинности
  над конечным типом, маски `Hagi.Data.BoolVenn` суть случай n=2).

## Hagi/Learning/SoftRouterMix.lean

- Аудит §7 (T): «Мягкая калиброванная смесь вместо жёстких ±10:
  CE смеси не хуже взвешенного среднего CE (Jensen)» —
  существование проверено, форма отсутствовала (равномерный
  1/N-вариант `ensemble_ce_le_mean_general` был; вероятностно-
  взвешенного роутерного — не было). Доставлена честная
  раскладка: ЛОГИТ-смесь и СМЕСЬ РАСПРЕДЕЛЕНИЙ — разные
  объекты, оба истинны по разным причинам (challenge-pin в
  докстрингах модуля).

## Hagi/Contracts/HadamardSpread.lean

- C321 — аудит A10 §9 п.5 («теорема о контракции реального
  квантайзера, средняя версия для блоков после Адамара,
  измерено ≈0.33 против худшего α≈0.106»): доставлена честная
  ДЕТЕРМИНИРОВАННАЯ формализация среднего случая — без теории
  меры, «среднее» = энергетическая предпосылка, не вероятностное
  усреднение по сфере.

## Hagi/Budget/RDAlloc.lean

- C322 — аудит §7 п.7 (slow-loop композиция RD-сжатия):
  побитное распределение + закон ошибки по стадиям +
  изо-Фробениус чувствительность + пересертификация собраны в
  ОДИН шаговый сертификат. Композиция ONLY: вся математика
  цитируется из своих носителей, новый —
  только клей и упаковка.

## Hagi/Deployment/CanaryRamp.lean

- C324 — аудит §7 p.1 по ранжированию
  `.omc/analysis/period-c313-c323-analysis.md` (canary-приёмка;
  файл удалён в c442e69, история:
  `git show c442e69^:.omc/analysis/period-c313-c323-analysis.md`):
  вес маршрута w непрерывен, канареечный разгон 0→1, утечка линейна
  по w (`cascade_leak_router_linear`), e-процесс следит за
  вредом (Ville, C264/C295 — процитированы premise-form, Unified
  слой 6 выше Deployment 5). Композиция ONLY: новый файл — клей и
  упаковка поверх C250 + C278.

## Hagi/Learning/ContinualForgetting.lean

- C327 — ранжирование item c: continual-learning forgetting
  bounds — формальный контракт контроля забывания старых задач при
  адаптации к новым (вывод — research C327).

- `auditSpendChain` + `auditSpendChain_delta_split` — цепочка из m
  принятых адаптаций (адаптация k тратит срез δₖ на задачу tsk k):
  δ-SPLIT арифметика ∑ spent = ∑ spent₀ + ∑ₖ δₖ (бухгалтерская
  лемма, которой нет в C274 — его мастер одно-снимковый).

## Hagi/Contracts/SparseInferenceCert.lean

- Audit §8 inference-сторона разреженности: sparsity-certified
  inference — спектральная маска + compute-доля, вся упаковка
  новая, все ингредиенты процитированы.

## Hagi/Contracts/ComputeToQuality.lean

- Цель GOAL «минимизация вычислений» end-to-end: total compute to
  quality = (шаги до ε) × (FLOP на шаг) — обе несущие уже
  приземлены (descent rate, FLOP-учёт), новая только
  КОМПОЗИЦИЯ на ядре C278 CertStepGen.

- `budget_telescope_gen`: недостающий четвёртый телескоп ядра —
  ТОЧНАЯ бюджетная идентичность `budget(t n) = budget(t 0) −
  Σ spends` (раньше телескопировались только drop/delta/risk).

## Hagi/Contracts/KVCacheCert.lean

- Цель: KV-cache inference certificate — расширение
  compute-сертификации на последовательный инференс:
  cached attention (новый токен attends по сохранённым
  keys/values через бегущий summary) имеет per-token work `t+1`
  против recompute-режима, который на каждом шаге ре-attend'ит
  ВСЁ прошлое; и cached выход ТОЧНО равен полной рекомпутации.

## Hagi/Contracts/DataToQuality.lean

- Цель GOAL «минимизация данных» — data-efficiency / sample-complexity
  сертификат: сколько СЭМПЛОВ сертифицируют, что выбранный energy-модель
  оптимальна по population PL-risk (дополнение compute-дуги C330).

## Hagi/Contracts/TruncatedSVDTail.lean

Rectangular spectral-tail bridge (A13 P-3): under the SVD premise
(A = U·Sigma·V^H with carrier rectangular singular values sigma),
the truncated approximant approxK satisfies
`truncated_svd_error_eq_tail`:

## Hagi/Theory/AdapterGrowth.lean (секции)

Единый файл роста адаптеров (карта секций — module docstring).

- C533 adapter snap composite: `adapter_snap_bound` (Lipschitz-оценка
  адаптера h = B·A·x), `adapter_snap_cycle_sound` (телескоп цикла:
  admission-вклад 0 ТОЧНО + certified fd-шаги + snap q/2^k). Bench
  `--mode adapter-snap-grow`: 8 уровней × 8 параметров (64 против 21
  у full-блока), obj 2.283 → ~0, snap bound ≈ 2.98e-13, глубина 10.
- C535 rank-adaptive: `rankScore`/`rankSelect` (probe-drop на
  параметр, селектор r ∈ {1,2}; паттерн hybridSelect C510),
  `rank_select_deterministic`/`rank_select_sound`. Bench: на всех
  уровнях score(r=2) ≤ score(r=1) — селектор честно берёт r=1;
  adaptive ≡ fix-r1 побитово, детерминизм повторов побитовый.
- C536 SVD-«Матрёшка»: `adapter_stack_rank_bound` (rank(Π(I+E_i)−I)
  ≤ Σ rank E_i), `cs_row` + `adapter_merge_error_bound` (Frobenius-
  хвост × Lipschitz ⇒ certified ε-окрестность merge), ссылка на
  Contracts/TruncatedSVDTail без импорта. Bench: стек 8×r=1 (64
  парам) → точный ранг ρ=2 → merge 16 параметров (−75%), возмущение
  0 до снапа; k=1 matryoshka честно unusable (деградация ~0.5).
- C555/C556/C558/C560 — секции self-compress/distill/mini-v3/
  adapter-transfer: см. единый bench-канон ниже (режимы
  bench_bridge.py) и карту секций в module docstring.

## Hagi/Theory/WeightDecayLeak.lean (weight decay leak — P4)

- Непроецируемый weight decay рушит GPM-память, проецируемый
  сохраняет ТОЧНО: `wd_compl_annihilates`/`wd_proj_preserves`
  (равенство), `naive_decay_leak` (СТРОГАЯ утечка теоремой),
  `wd_gpm_step_sound` (main: шаг в дополнении + projected decay ⇒
  W·P неизменно). Witness C538 (ℚ, P = diag(1,0)).

## Hagi/Probability/EmpiricalBernstein.lean (empirical bernstein — P1)

- EB-confidence как дополнение Freedman: σ̂-подстановка +
  аддитивный член (Maurer–Pontil стиль). `freedman_tail_two_sided`,
  `eb_radius_algebra`, `empirical_bernstein_bound` (main),
  `empirical_bernstein_mean_bound`. Контраст (witness C539):
  n_EB(наша форма) = 4267 против n_Hoeffding = 176995 (41.5×).

## Hagi/Theory/OEComplete.lean (OE search completeness — P6)

- Дедупликация наблюдательно-эквивалентных программ НЕ теряет
  решение: `oe_classes_partition` (Setoid), `oe_search_complete`
  (main: первый представитель каждого OE-класса достигается;
  полнота ОТНОСИТЕЛЬНО ПРОБ — честно), `oe_search_terminates`.
  Witness: naive 343 посещений vs OE-дедуп 4.

## Hagi/Theory/ExactBypass.lean (exact bypass zero CE — P8)

- PROVEN_EXACT символьные эксперты: p = 1 ⇒ точечный log-loss 0
  РОВНО. `ce_pointwise_of_prob_one`, `ce_covered_zero`, `ce_split`/
  `ce_total_eq_residual`, `exact_gate_sound`/
  `exact_gate_rejects_zero`, мост `ceOneHot_eq_zero_of_softmaxP_eq_one`
  (SSOT ядро). Witness: 6 покрытых + 4 остаточных, total =
  residual бит-в-бит; негатив p=0 → гейт false.

## Hagi/Theory/MiniHagiLoop.lean (self-improving loop)

- C547 `--mode mini-hagi-loop`: все certified-компоненты в одном
  прогоне (P1 bypass + P2/P3 адаптерный рост + P4 continual-изоляция
  C544 + P5 OE+EB + P6 метрики). `full_loop_sound` — КОМПОЗИЦИОННАЯ
  обёртка (конъюнкция инвариантов компонент без новых фактов).
  Прогон: 107/113 покрыто (CE-вклад 0 EXACT), forgetA = 0 EXACT,
  26 certified-шагов.
- C549 `--mode mini-hagi-loop2`: итеративный цикл — OE-поиск в
  пространстве, ВЫРОЖЕННОМ из принятых примитивов → EXACT-расширение
  → переобучение адаптера на остатке → EB-телеметрия. Сходимость
  покрытия 54.9 → 93.8% (стоп EB-гейт); негативы композиционной
  цепочки (закон 2 не находится без блока 1). Lean:
  `coverage_append_monotone`, `iterative_loop_sound` (новый факт —
  только монотонность).

## Hagi/Theory/AdapterBank.lean (adapter bank bridge from hagi v2)

- Source-anchored мост волны 210/210b (hagi/trunk_ops.py:310-345,
  unified.py:147-165, lm.py:770-777): `bankUpdate`/`warmTransfer`/
  `bankBatch`; `adapter_bank_isolation`(_obj) — обновление слота j
  не трогает слот i ТОЧНО; `warm_transfer_sound` (forgetA=0 копией +
  certified-обучаемость warm-init), `bank_composition` (индукция по
  batch). HONEST: transfer-качество — эмпирика, теоремой не
  подменено; негатив warm-хуже-cold в witness. Bench: нет (мост).

## Hagi/Theory/Softmax.lean (phat monotonicity domain characterization)

- Суммарная p̂-анти-монотонность охарактеризована ТОЧНО:
  `sum_phat_anti_mono_single_domain` (держится при фиксированном
  числителе и вложенных стенах одной банки) +
  `band_mix_counterex`/`phat_total_not_anti_mono` (ТЕОРЕМА-
  контрпример при смешении доменов). Bench: нет.

## Imports final deriv-safe (bare-import сужение)

- `import Mathlib` → точные модули в 40 файлах (bare 62 → 22).
  Batch C (deriv-risk) откачан: freeze-детект statement-drift —
  C482-урок. Остаток 22 bare = перманентные deriv-pins; список
  сужаемых импортов ПУСТ (терминальное состояние). Эффект:
  15.0s → 9.2s на файл (BlockNorm probe).

## Hagi/Theory/GrowSnap.lean (certified snap-политика и оптимальный k)

| теорема | формулировка | file:line | bench |
|---|---|---|---|
| `snap_preserves_objective_bound`, `snap_denominator_reset`, `grow_snap_cycle_sound` | C521: certified snap q/2^k на границе grow — снимает экспоненциальную стену знаменателей C506 (2366 цифр → k бит) | Hagi/Theory/GrowSnap.lean:81, :119, :145 | `--mode adapter-snap-grow` (AdapterGrowth) |
| `snap_err_bound` | ДВУСТОРОННЯЯ obj-ошибка \|obj g − obj f\| ≤ L·d·2^-(k+1) (C521-версия — односторонняя) | Hagi/Theory/GrowSnap.lean:215 | — |
| `snapAdmissible`/`snapK` (Nat.find), `snap_k_admissible`, `snap_k_min`, `snap_k_lt_violates` | k* = минимальное допустимое k: feasibility err(k*) ≤ ε; точность (любое допустимое k ≥ k*); негатив k < k* ⇒ err СТРОГО > ε | Hagi/Theory/GrowSnap.lean:190, :287, :293, :301, :308 | — |
| `snap_k_eq_ceil` | ЗАМКНУТАЯ ФОРМА: при L·d > ε k* = ⌈log₂(L·d/ε)⌉ − 1 (обе стороны из feasibility + minimality) | Hagi/Theory/GrowSnap.lean:342 | — |
| `snapBits`, `snap_bits_err_tradeoff`, `snap_optimal_k` | биты = d·(k+1); Pareto k ≤ k' ⇒ биты ↑, полуячейка ↓; DECISION-ПРАВИЛО: k* даёт certified err ≤ ε И минимальные биты | Hagi/Theory/GrowSnap.lean:185, :392, :401 | — |

Witness C593 (trajSnap.lean, rc=0, ℚ-зеркало поиска): I1 L=1,d=10,ε=2^-12
→ k*=15, биты 160, k=14 нарушает; I2 L=3,d=1,ε=2^-6 → k*=7, k=6
нарушает; I3 ГРАНИЦА РАВЕНСТВА Ld/ε=4 → k*=1, bound = ε, k=0 нарушает.

## Hagi/Theory/NegativeTransfer.lean (negative transfer, smooth, schedule, growth gate)

| теорема | формулировка | file:line | bench |
|---|---|---|---|
| `neg_transfer_char`, `warm_better_char`, `transfer_boundary` | C572: квадратичная obj, равный бюджет: warm хуже cold ⟺ 2•⟪θ,t⟫ < ‖θ‖² (ТОЧНАЯ iff). Decision: warm iff 2⟪θ,t̂⟫ > ‖θ‖² | Hagi/Theory/NegativeTransfer.lean:117, :127, :137 | `--mode transfer-gate-certified` (quad-iff уровень) |
| `neg_transfer_adversarial`, `gd_run_dist`, `warm_better_budget` | t = −c•θ ⇒ всегда T2; бюджет НЕ размывает границу | Hagi/Theory/NegativeTransfer.lean:150, :176, :191 | — |
| `smooth_obj_transfer_bound`, `sufficient_negative_transfer` | C592: L-smooth obj + GD равным бюджетом ⇒ f z − n•`nlBudget γ L G` ≤ f (nlRun n γ grad z) ≤ f z; стартовый запас > n•nlBudget ⇒ warm строго хуже. G — честный binder вдоль траектории (глобальная не выводится) | Hagi/Theory/NegativeTransfer.lean:386, :406 | `--mode transfer-gate-certified` (smooth-sufficient уровень) |
| `nlDrop`, `nl_drop_bound`, `nlDrop_le_optimal`, `nl_drop_optimal` | C606 Schedule: drop = γG² − Lγ²G²/2 ≤ G²/(2L) для любого γ, равенство при γ* = 1/L (полный квадрат). Кандидат 2/(3L) отклонён | Hagi/Theory/NegativeTransfer.lean:434, :443, :467, :481 | auto-LR γ = 1/L (C609) |
| `growthGate`, `growth_gate_stay_char` | C632 (второй namespace `Hagi.Theory.GrowthGate` в этом же файле, блок перенесён дословно): grow ⟺ potential_bound > c_add (равенство → stay: budget-приоритет меньшей ёмкости); гейт = порог, no hidden state | Hagi/Theory/NegativeTransfer.lean:574, :580 | `--mode grow-snap` / `adapter-grow`, перед каждым добавлением |
| `nl_drop_step_eq`, `nl_drop_total` | nlDrop (1/L) L x = x²/(2L); в квадратичной модели n шагов уменьшают obj ≤ n·G²/(2L) — certified-потолок выигрыша | Hagi/Theory/NegativeTransfer.lean:608, :620 | — |
| `growth_gate_sound` | MAIN (certified-stay): n·G²/(2L) ≤ c_add ⟹ любое n-шаговое дообучение выигрывает ≤ c_add — рост не окупится | Hagi/Theory/NegativeTransfer.lean:677 | `growth_gate_measure` |

Контраст: квадратичная obj → точный iff; L-smooth произвольный →
консервативная sufficient, применять когда есть G-оценка на
траектории и консервативного вердикта достаточно. Witness C592
(trajNL.lean, γ=1/5, L=2, G=2): n=1 certified (1 > 24/25); n=2 условие
НЕ выполнено (1 ≤ 48/25), но warm всё равно хуже ⇒ sufficient ≠
necessary. C606 (L=2, G=1): drop γ=0.1/0.5/0.9 → 9/100, 1/4, 9/100.

- C632 рост-гейт (блок `Hagi.Theory.GrowthGate` ниже секции Schedule):
  отличие от C535 (rankSelect по probe-score) и C577/C601 (два
  probe-прогона): ноль измерений, решение по формуле ДО probe.
  Honest: потенциал-модель квадратичная (для L-smooth потолок шире
  — nlBudget C592, гейт пересчитывается); grow = РАЗРЕШЕНИЕ, не
  обещание; sound только у stay-ветки. Witness C632 trajGate.lean:
  G=2, L=2, n=5 → bound 5; c_add=10 → stay; c_add=4 → grow.

## Hagi/Theory/TritCodec.lean (trit-кодек, 5 тритов в байте)

- Биекция wave214 pack/unpack_trits5 (3^5 = 243 ≤ 2^8):
  `tritPack`/`tritUnpack`, `tritPack_lt_243` (guard недостижим),
  `trit_roundtrip`, `tritPack_injective`. Bench: нет.

## Hagi/Theory/MasterTheoremV3.lean (метатеорема v3 → v3.3)

- `master_theorem_v3` (Hagi/Theory/MasterTheoremV3.lean:81): 5 гарантий
  машины v3 (params-бюджет, zero-forgetting, coverage-монотонность,
  obj-телескоп, transfer-граница) — конъюнкция делегатов без
  ослабления; не дублирует MasterTheorem.lean.
- `hagi_master_v33` (Hagi/Theory/MasterTheoremV3.lean:273) — certified-
  машина v3.3 ОДНОЙ теоремой; каждый клоз — делегат к доказанной
  теореме, гипотезы дословно, ноль новых доказательств:

| # | клоз | делегат | с версии |
|---|---|---|---|
| (1) | params-бюджет ≤ 2·k·dd | `self_compress_loop_sound` | v3.1 (C600) |
| (2) | zero-forgetting per-task адаптеров | `adapter_per_task_sound` | v3.1 |
| (3) | certified obj-телескоп ≤ o0 + Σ bounds | — | v3.1 |
| (4) | монотонность покрытия | `iterative_loop_sound` | v3.1 |
| (5) | точный iff-transfer (квадр) | `neg_transfer_char` | v3.1 |
| (6) | snap-грид оптимальность k* = ⌈log₂(L·d/ε)⌉−1 | `snap_optimal_k` | v3.1 |
| (7) | coverage-чтение: каждый байт прочитан окном решётки covStarts | `covStarts_covers` | v3.1 |
| (8) | smooth sufficient-transfer: f z − n·nlBudget ≤ f (nlRun n γ grad z) ≤ f z | `sufficient_negative_transfer` | v3.1 |
| (9) | guaranteed drop при γ* = 1/L равен G²/(2L) | `nl_drop_optimal` | v3.2 (C614) |
| (10) | hierarchical coverage: любой i < nB покрыт окном `hierStarts` решётки при 0 < B, 0 < s' ≤ w — ЛЮБОЕ n | `hier_covers_any_n` | v3.2 |
| (11) | reading floor: (hierStarts nB B w w).length = ⌈nB/w⌉ (0 < w, w ∣ B) = floor любого покрытия | `hier_optimal` | v3.3 (C622) |

- v3.1 `hagi_master_v31` (:135) = (1)–(8); v3.2 `hagi_master_v32`
  (:202) = v3.1 + (9)(10); v3.3 `hagi_master_v33` (:273) = v3.2 + (11).
  Witness: C600 trajMT31 (#check 8 клозов), C614 trajMT32 (клоз (9):
  L=2, G=1 → drop 1/4; (10): n=8128, B=4032), C622 trajMT33 (клоз
  (11): total 127 = ⌈8128/64⌉). Axioms: propext, Classical.choice,
  Quot.sound.

## Hagi/Theory/FactLedger.lean (fact-ledger append-only мост)

- Мост к wave219 memory_store (facts.py): `FactEntry`/`FactHistory`,
  `fact_append_preserves` (take-инвариант), `fact_lookup_monotone`.
  Честно: идемпотентности append НЕТ (как в коде), dedup-теорема
  опущена. Bench: нет.

## Hagi/Theory/RangeWrap.lean (piecewise range-affine мост)

- Мост к wave222 `_mod_affine_expr` (core.py): `rangeWrap lo c x m`,
  `rangeWrap_inrange` (замкнутость в [lo, lo+m), `Int.emod`),
  `rangeWrap_fixed_point` (c % m = 0 не двигает). Идемпотентность
  композиции честно опущена. Bench: нет.

## Hagi/Theory/AdaptiveContext.lean (adaptive-context мост)

- Мост к lm.AdaptiveContextSelector (lm.py:124): «self-CE elbow» —
  наименьший W с CE ≤ best·(1+tol). `selectW_spec`,
  `selectW_occam_minimal` (меньшие окна отклонены измерением),
  `selectW_budget_bound` (≤ maxW окон). Bench: нет.

## Hagi/Theory/KnowledgeConsolidation.lean (knowledge-consolidation мост)

- Мост к wave225 (unified.py:285-315: remember/consolidate/
  learn_from_dialog): `consolidate_prompt_empty` (graceful
  degradation), `remember_preserves_pages` (append-only, родня
  C579), `learn_from_dialog_archives` (архив до ingest). HONEST:
  top-k ранжирование НЕ монотонно — теорема опущена. Bench: нет.

## Hagi/Theory/CoverageReading.lean (чтение и стоимость окна)

| теорема | формулировка | file:line | bench |
|---|---|---|---|
| `covStarts_covers` | C598: окна k с шагом k (+ суффикс-окно) покрывают каждый байт [0, n) — полное чтение входа | Hagi/Theory/CoverageReading.lean:54 | — |
| `covStarts_trunc_uncovered_zero` | ЧЕСТНАЯ ГРАНИЦА (не позитив): усечение windows[-max_span:] при окон > m отбрасывает старт 0, байт 0 не прочитан | Hagi/Theory/CoverageReading.lean:130 | мотивация adaptive-span |
| `covStartsStep`, `covStarts_eq_step`, `covStartsStep_covers`, `covStartsStep_len_le`, `covStartsStep_adaptive_covers` | C602: старты с шагом s: покрытие ТОЧНО при 0 < s ≤ w (s > w — дыра); окон ≤ (n−w)/s + 2; при (n−w)/s+2 ≤ m покрытие полное И усечение не срабатывает | Hagi/Theory/CoverageReading.lean:171, :178, :184, :220, :233 | `--mode adaptive-span`, `adaptive_span` |
| `hierBlockLen`, `hierStarts`, `hier_covers_any_n`, `hier_peak_window_budget` | C611: 2 уровня (блоки B × `covStartsStep`): покрытие [0, n) для ЛЮБОГО n без верхней границы; peak ≤ m окон в каждом блоке (peak ≠ total). Точный бюджет s = w, B = w·(m−1) | Hagi/Theory/CoverageReading.lean:268, :273, :283, :315 | `--mode generate-hier`, `hier_span` |
| `covStartsStep_len_tiling`, `hier_blocks_sum_tiling`, `hier_total_formula`, `hier_total_min`, `hier_total_floor`, `hier_optimal` | C618: total ≤ ⌈n/B⌉·((B−w)/s+2); при s = w, w ∣ B total = ⌈n/w⌉ ТОЧНО и не зависит от B (внутреннего оптимума B* нет); информационный floor любого покрытия ≥ ⌈n/w⌉ ⇒ выбор C611 total-оптимален | Hagi/Theory/CoverageReading.lean:354, :389, :440, :462, :496, :533 | pinned assert C613 |
| `ceil_div_anti`, `windowCost_fixed_mono`, `windowCost_linear_bounds`, `windowCost_linear_near_const`, `windowCost_hier` | C623 (ns WindowTradeoff): totalCost(w) = ⌈n/w⌉·c(w). c(w)=c ⇒ монотонно невозрастает, оптимально w_max; c(w)=c·w ⇒ n ≤ w⌈n/w⌉ ≤ n+w−1, total ∈ [c·n, c·(n+w)) — НЕ зависит от w; мост к `hier_total_min` | Hagi/Theory/CoverageReading.lean:555, :577, :586, :602, :613 | `--cost-regime fixed/linear`, `cost_regime_w` |
| `mixedCost_relax_min`, `mixedCost_relax_min_eq`, `mixedCost_lower` | C628: c(w) = a + c·w²: a/w + c·w ≥ 2√(a·c) (AM-GM), равенство при w = √(a/c) — внутренний оптимум w*; дискретный ⌈n/w⌉(a+c·w²) ≥ 2n√(a·c) (равенство в общем случае недостижимо — точку берёт целый argmin bench) | Hagi/Theory/CoverageReading.lean:630, :650, :675 | `--cost-regime mixed`, α=2 |

- Правило выбора w: c(w)=c ⇒ w_max; c(w)=c·w ⇒ свободно (по
  точности); c(w)=a+c·w^α ⇒ w* = (a/(c·(α−1)))^(1/α). Общий α>1 —
  вне Lean (honest Real-sketch deriv+convexOn); чистая c·w^α
  оптимума не имеет (optimum w → min). Стоп-предикаты generate_auto
  (sentence + low confidence + 8-step repetition + entropy collapse)
  — def-eq тривиальность, опущены.
- Witness: C598 trajCov.lean 540/64 covered (9 окон), негатив 3/10
  false; C602 trajSpan.lean 540/w64/s=9 — 54 окна covered; s=17 > w=9
  (n=60) байт 9 в дыре; 1152/w64/s=17 — 65 окон > 64, усечение теряет
  байт 0, фикс s=18 — 62 окна covered. C611 trajHier.lean n=8128, B=4032,
  s=w=64: per-block [63, 63, 1], peak 63; одноуровнево 127 > 64. C618
  trajOptB.lean n=100000: total 1563 = ⌈n/w⌉ для B ∈ {64, 2048, 4032,
  4096}; s=32, B=1088 → 3033 > floor. C623 trajW.lean n=100000, w ∈
  {16, 64, 256}: чтения {6250, 1563, 391}; linear-cost {100000, 100032,
  100096}.

## scripts/bench_bridge.py (C551–C635: режимы без собственного Lean-ряда)

Все режимы: append-блок + choice + dispatch (backward-совместимо,
канон ALGORITHMS §27), certified snap-GD (drop>0 COMMIT / HOLD),
forgetA=0 bit-exact asserts, drift-детект на замороженной копии,
EB-телеметрия, негативы (wrong-const, HOLD), witness-lean rc=0,
аксиомы только propext/Quot.sound/Classical.choice.

- C551 `--mode universal-loop`: полный живой корпус 113/113 —
  покрытие 93.8% = 6 реальных констант-кластеров; линейных законов
  НЕТ (измерено); законы C549 на реальный корпус не переносятся
  (0/113). Lean: `universal_loop_corpus_mono`.
- C553 `--mode universal-loop-nl`: нелинейный язык v2 (произведения,
  min/max, пороговые): законов НЕТ (19204 кандидата, покрытие
  идентично). Новая теорема не нужна (oe_search_complete абстрагирован
  по Prog/space).
- C555 `--mode self-compress-loop`: learn→merge→learn, params ≤
  2·K·d = 32 при монотонном росте знания (CE остатка −84%), Σ merge
  bounds = 0; негативы k<ρ теряют знание (usable=false). Lean:
  `selfCompressParams`, `self_compress_params_bounded`/`_contrast`,
  `self_compress_loop_sound`.
- C556 `--mode distill`: констант-кластеры → rank-1 (`distillAdapter`,
  `constant_distill_exact`): CE кластеров 0 бит-в-бит, ветвления 113
  → 0. Контраст `symbolic_storage_cheaper`: символьное хранение
  дешевле по памяти.
- C558 `--mode mini-hagi-v3`: сборка C547–C556 (115 точек): кластеры
  108/115, params ≤ 32, forget 0. Lean: `v3_assembly_sound`.
- C560 `--mode adapter-transfer`: warm vs cold vs poisoned, равные
  бюджеты — T1 3/3 по AUC (×387 на близкой паре); poisoned хуже по
  AUC. C566 реактивно (корпус 115→122): инварианты стабильны.
- C568 `--mode band-check`: 48/48 полос на живом корпусе, негатив
  переставленной полосы 0/2. Lean: `softDef_shift`,
  `bandDescribes_of_pointwise`, `bernoulliBandDescribes`
  (Hagi/Theory/TrainerBenchmark.lean:146, :161, :176).
- C577 `--mode adapter-transfer-auto`: probe-A/B гейт (2 шага,
  rollback C530) выбирает warm/cold — T1 сохранены, adversarial →
  cold. Lean: `gate_char`, `auto_transfer_gate_sound`
  (Hagi/Theory/AutoTransferGate.lean:80, :139).
- C601 `--mode transfer-gate-certified` (bench_bridge.py:12442,
  :12450): `nl_budget` γG² + Lγ²G²/2 ДОСЛОВНО из Lean; warm допустим
  ⟺ start_gap = f(θA) − f(0) ≤ n·nlBudget; двухуровневая семантика
  quad-iff + smooth-sufficient. L = 2·trace(H̄), G — измеренный
  max ‖grad‖² (honest premise). Honest: adversarial — quad-iff
  cold, smooth-гейт допускает warm (G ≈ 0.03, бюджет 99.66 > 5.43)
  — sufficient ≠ iff. Порог точно по границе: 24/25 → warm, 25/25 →
  cold. 3 реальные пары: оба уровня warm.
- C609 auto-LR (bench_bridge.py:12170): adapter-transfer-auto и
  transfer-gate-certified переведены на γ = 1/(2·trace(H̄)) по
  `nl_drop_optimal`; старая константа 1/10 — флаг --fixed-lr.
  Телеметрия `steps_drop_vs_bound` (bound может быть loose). γ_auto
  примеры 0.477 / 0.520 / 0.667. A/B: вердикты идентичны, golden
  бит-идентичен. NOT changed: grow-семейство уже 1/L, mini-hagi,
  trunk.
- C613 `--mode generate-hier` (bench_bridge.py:13051): `hier_span` —
  двойник `hierStarts`; n = 540/4032/8128/100000 → блоков 1/1/3/25,
  total 9/63/127/1563, peak 9/63/63/63, covered; одноуровневый
  adaptive_span: OK / OK / INFEASIBLE / INFEASIBLE. Pinned: n=8128 →
  [63, 63, 1] (совпало с #eval C613 HierEval.lean).
- C626 `--cost-regime {fixed,linear,mixed}` в generate-hier
  (bench_bridge.py:13150): `cost_regime_w` — точные Fractions,
  fail-closed asserts (коридор, near-const, w_max, argmin); n =
  540/4032/8128/100000, варианты w {16, 64, 256, w_max}; сверка с
  C623 совпала дословно.
- C633 growth gate в grow-snap / adapter-grow (bench_bridge.py:5862,
  :5882): `growth_gate_measure` (G² — сумма квадратов fd-градиентов;
  L — однокоординатная выборка кривизны, honest proxy, L=0 → GROW
  fail-closed); c_add = n_new_params·λ, λ = 1/10⁴ (PIN = одна
  минимальная ячейка snap-сетки). grow-snap: 6 событий, все GROW,
  глубина 8 = golden; adapter-grow: 2 события (r=1, r=2) GROW, ranks
  [1, 2]. skipped-certified = 0 — честно.
- C635 `--gate-test` (bench_bridge.py:5952): 6 синтетик — S1..S4 STAY
  (в т.ч. равенство), G1/G2 GROW, физически проходит SKIP-ветку;
  Lean-witness gatetest.lean PASS. `--lambda-sweep`: λ=1/10⁴ → 6 GROW
  (golden); λ ≥ 1/10³ → первый гейт STAY, глубина 2; certified_stay
  λ* ≈ 10⁴¹ (GROW ⟺ λ < pb/params).

## History (C538–C635)

- Era index (C591–C633): `.omc/analysis/era-index.md`; earlier
  per-beat files — `git log`; line-level
  history: `git log --oneline -- STATUS.md` (полный дожатый журнал —
  b3939aa5).
