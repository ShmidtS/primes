## Архив (исторические секции и полный журнал)

Полный дожатый журнал и не-файловые исторические секции —
git-история: `git show b3939aa5:STATUS.md`.

## Hagi/Architecture/AlignedMerge.lean
- `frobSubord`: для вещественной матрицы `M` и вектора `w` выполняется `(M *ᵥ w) ⬝ᵥ (M *ᵥ w) ≤ frobSq M * (w ⬝ᵥ w)`.
- `misalignCross`: `(V *ᵥ r) ⬝ᵥ (W *ᵥ s)` в квадрате не превосходит `frobSq (Vᵀ * W) * (r ⬝ᵥ r) * (s ⬝ᵥ s)`.
- `mergeEnergyPerturbed`: при `IsOrthoCol V` и `IsOrthoCol W` энергия `V *ᵥ r + W *ᵥ s` не превосходит `(r ⬝ᵥ r) + (s ⬝ᵥ s) + 2 * (frobSq (Vᵀ * W)).sqrt * (r ⬝ᵥ r).sqrt * (s ⬝ᵥ s).sqrt`.

## Hagi/Architecture/Configuration.lean
- `config_storage_beats_dense`: при `N * r < d` и `0 < d` хранение `(N * r) * d` параметров строго дешевле `d * d`.
- `selector_never_flips_verdict`: при тех же условиях выигрыш по памяти сохраняется вместе с ограничением селектора `N ≤ 2 ^ B`.
- `switchable_beats_naive_dense`: из `r ≤ d` следует `N * r * d ≤ N * d * d`.

## Hagi/Architecture/CortexFiber.lean
- `fiberCross`: из `Uᵀ * V = 0` следует `(U *ᵥ z) ⬝ᵥ (V *ᵥ w) = 0`.
- `fiberPythagoras`: при `IsOrthoCol U`, `IsOrthoCol V` и `Uᵀ * V = 0` энергия суммы `U *ᵥ z + V *ᵥ w` равна `z ⬝ᵥ z + w ⬝ᵥ w`.
- `fiberParamCount`: при `r < d` выполняется `r * d < d * d`.

## Hagi/Architecture/ManifoldHyperConn.lean
- `IsRowStochastic` / `IsDoublyStochastic`: premise-form гипотезы (неотрицательные элементы, суммы строк = 1, суммы столбцов = 1); Sinkhorn-балансировка не нужна и не утверждается.
- `doublyStochastic_sq_le` (MAIN): дважды стохастическая M сжимает L2 — `Σ (Mx)ᵢ² ≤ Σ xⱼ²` — через построчный взвешенный Коши–Шварц (`Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`) и суммы столбцов; оценка точная (перстановочные матрицы дают равенство), посылка столбцовых сумм нагружена (row-stochastic-only может расширять L2).
- `rowStochastic_opNorm_le_one`: ℓ∞-операторная норма строчно-стохастической M ≤ 1 (того же scoped-инстанса, что потребляет `Hagi.Core.propagate_bound_contractive`).

## Hagi/Architecture/FactorRank.lean
- `nonnegFactorization M k` означает точное разложение `M = W * H` с поэлементно неотрицательными `W`, `H`; `nonnegRank M` задаёт наименьшую допустимую внутреннюю размерность.
- `rank_le_nonnegRank`: если существует `k` с `nonnegFactorization M k`, то `M.rank ≤ nonnegRank M`.
- `positive_measure_pos_prob`: для вероятностной меры `μ`, измеримого `F` и `0 < μ F` доказаны `0 < μ F` и `μ Fᶜ < 1`; равенство `μ Fᶜ = 0` не следует.

## Hagi/Architecture/FactorizedMerge.lean
- `factorized_error_bound`: на конечном непустом `ι`, если для каждого `i` выполнено `‖R i - (W i - C)‖ ≤ δ i`, то `‖fullMerge W - (C + meanResidual R)‖` не превосходит среднего `∑ i, (Fintype.card ι : ℝ)⁻¹ * δ i`.
- `factorized_budget`: при `2 ≤ N` и `N * (r * (V + d)) ≤ (N - 1) * (V * d)` число параметров `V * d + N * (r * (V + d))` не превосходит `N * (V * d)`.
- `unified_error_budget`: пять посылок об ошибках общей части, спектрального хвоста, ранга, квантования и маршрутизации дают `‖W - S‖ ≤ e_shared + e_spectral + e_rank + e_quant + e_routing`; ошибка маршрутизации остаётся посылкой.

## Hagi/Architecture/Heterarchy.lean
- `no_global_ranking`: обращение доминирования `a` над `b` в одном контексте и `b` над `a` в другом несовместимо ни с одним `RankingConsistent`.
- `cycle_breaks_ranking`: цикл доминирования `a → b → c → a`, даже распределённый по трём контекстам, также исключает согласованный линейный ранг.
- `disagreement_survives_configs`: при `d ≠ 0` векторы `d` и `-d` суммируются в ноль, но `‖d‖ * ‖d‖ + ‖-d‖ * ‖-d‖ > 0`.

## Hagi/Architecture/LiveDelta.lean
- `block_rank_le`: ранг низкорангового блока `Aᵀ * B` не превосходит `Fintype.card r`.
- `null_effect`: если `x ᵥ* Aᵀ = 0`, то `x ᵥ* (Aᵀ * B) = 0`.
- `blocks_cost`: стоимость списка блоков равна его длине, умноженной на `Fintype.card r * (Fintype.card m + Fintype.card n)`.

## Hagi/Architecture/OrthoInjection.lean
- `fiberSplitOrtho`: при `IsOrthoCol U` остаток проекции удовлетворяет `Uᵀ * (A - U * (Uᵀ * A)) = 0`.
- `fiberSplitEnergy`: при том же условии энергия `A *ᵥ x` в точности равна сумме энергий корковой компоненты `(Uᵀ * A) *ᵥ x` и ортогонального остатка.
- `fiber_injection_preserves_cortex`: добавление `(A - U * (Uᵀ * A)) *ᵥ x` к `h` не меняет координаты `Uᵀ *ᵥ h`.

## Hagi/Architecture/ResidualSplit.lean
- `residual_gate_two_sided`: по определению `ResidualGateOn η E C P ↔ η * E - C - P > 0`.
- `expert_residual_not_compressible`: если `ResidualSplit W Wshared Re Rq`, `Re = 0`, а другой разбор имеет вид `ResidualSplit W Wshared 0 Rq'`, то `Wshared + Rq' = W`; более общее утверждение о несжимаемости не доказывается.
- `fidelity_bound_with_fibers`: из `ResidualSplit W Wshared Re Rq` и `Wshared + Re + Rq' = W` следуют `W - (Wshared + Re) = Rq` и `W - (Wshared + Re + Rq') = 0`.

## Hagi/Audit/Audit.lean
- `amgm_equality`: при положительных `Bn`, `t0`, `c`, `B` и `B^2 = Bn * t0 / c` выполняется `c * B + Bn * t0 / B = 2 * Real.sqrt (c * Bn * t0)`.
- `amgm_uniqueness`: при `0 < c`, `0 < B`, `0 ≤ Bn`, `0 ≤ t0` равенство в этой оценке обратно влечёт `B^2 = Bn * t0 / c`.
- `batch_T_min`: при `0 < B`, неотрицательных `Bn`, `t0`, `c` величина `(1 + Bn / B) * (t0 + c * B)` не меньше `t0 + c * Bn + 2 * Real.sqrt (c * Bn * t0)`.

## Hagi/Optimization/MirrorHedge.lean
- `hedge_step`: для вероятностного `p`, потерь `0 ≤ l i ≤ 1` и `0 ≤ eta ≤ 1` сумма `∑ i, p i * exp (-eta * l i)` не превосходит `1 - eta * ∑ i, p i * l i + eta ^ 2 / 2`.
- `hedge_telescope`: если `0 ≤ 1 + u t` для всех `t`, то `∏ t < T, (1 + u t) ≤ exp (∑ t < T, u t)`.
- `router_regret_bound`: при `0 < K`, `0 < eta` и посылке hsurv выполняется `A - Lstar ≤ Real.log K / eta + eta * T / 2`.

## Hagi/Autonomy/Insight.lean
- `tldr_two_tier_safety`: если `B.mulVec x = 0`, то `(A * B).mulVec x = 0`; если дополнительно `kl ≤ ⟪dW, F dW⟫_ℝ / 2` и `⟪dW, F dW⟫_ℝ ≤ 2 * eps`, то `kl ≤ eps`.
- `forgetting_kl_quadratic_unit_fisher`: из `dW ^ 2 ≤ 2 * eps` следует `scalarQuadraticKl dW ≤ eps`.
- `tldr_two_tier_safety_unit_fisher`: объединяет нулевое действие адаптера на ядре `B` и скалярную оценку KL при `dW ^ 2 ≤ 2 * eps`.

## Hagi/Autonomy/ParetoController.lean
- `pareto_validity`: при `0 < omega i` для всех координат из `0 < dirTau u omega a` следует `0 < u a i`.
- `dir_controller_find`: если `g ≤ dirTau u omega a₀`, то существует `a'` с `g ≤ dirTau u omega a'`, максимизирующий `dirTau` по всем действиям.
- `noisy_pareto_select`: при `0 < omega i` и `|uhat a i - u a i| ≤ eps i` существует выбор `a'` с истинным уровнем не ниже `dirTau u omega a₀ - 2 * max_i (eps i / omega i)`.

## Hagi/Autonomy/SupervisorSafety.lean
- `capacity_member_mono`: при положительных `A`, `N`, α, `b1`, `b2` и `b1 < b2` член `capMember A b N alpha` строго убывает по `b`.
- `ternary_beats_binary`: при положительных `A`, `N`, α значение при `b = Real.log 3 / Real.log 2` строго меньше значения при `b = 1`.
- `no_restore_without_checkpoint`: в истории `ValidHist` наличие `SupEv.restore t id` влечёт существование `SupEv.checkpoint t' id` с `t' ≤ t`.

## Hagi/Autonomy/SupervisorViability.lean
- `halving_mistake_bound`: если список примеров `L` реализуем некоторой гипотезой из конечного `H`, то `2 ^ mistakeCount H L ≤ H.card`.
- `majority_wrong_verdict`: если строго больше половины гипотез дают на `x` ответ, отличный от `y`, то `halvingVerdict H [] x ≠ y`.
- `majority_wrong_persists`: инъективное отображение `φ : H → H'`, сохраняющее ответ на `x`, при `H'.card ≤ H.card` переносит строгое ошибочное большинство на `H'`.

## Hagi/Autonomy/TTTStability.lean
- `ttt_bibo`: из `abs W ≤ 1` следует `abs (W ^ T * x) ≤ abs x` для любого натурального `T`.
- `ttt_chain_bounded`: если `abs (W t) ≤ 1` для всех `t`, то произведение первых `T` операторов, применённое к `x`, также имеет модуль не больше `abs x`.

## Hagi/Budget/AnytimeCondensation.lean
- `pointwise_upper_band`: при `0 < T`, если ни для одного `v` не существует `t < T` с `μ + u ≤ g v`, то `g v < μ + u`.
- `anytime_condensation`: для положительной нормированной `q`, `0 < T`, `0 < σ2`, `0 < α < 1`, субгауссова ограничения hcgf и отсутствия выходов `g` и `2 * μ - g` за порог `μ + √(2 * σ2 * log (T / α))` доказано `ceOneHot t (m + (g - μ)) / 2 + ceOneHot t (m - (g - μ)) / 2 - ceOneHot t m ≤ 2 * σ2 * log (T / α)`.
- `condensation_pipeline`: сохраняет ту же оценку и показывает, что для невозрастающей последовательности val из `val L < epsL` следует `val j < epsL` при всех `j ≥ L`.

## Hagi/Budget/BatchCap.lean
- `sfo_global_min`: при `0 ≤ X`, `0 < c`, `0 ≤ Y` и `Y / c < s` точка `criticalS c Y` минимизирует `sfoCost X c Y` по таким `s`.
- `critical_batch_lower`: при `0 < Y`, `0 < Z < ε` выполняется `9 * Y ^ 2 / (4 * ε ^ 2) < (criticalS (ε - Z) Y) ^ 2`; доказана оптимизация заданной стоимостной модели.
- `optimal_split`: при положительных `A`, `C`, `B` выполняются `A / √(A * B / C) + C / √(C * B / A) = 2 * √(A * C / B)` и `√(A * B / C) * √(C * B / A) = B`.

## Hagi/Budget/BitAlloc.lean
- `distill_chain_telescoping`: из `S k ≤ E k + delta k` для `k ≤ n` и `E (k + 1) ≤ S k` для `k < n` следует `S n ≤ E 0 + ∑ k ∈ Finset.range (n + 1), delta k`.
- `harvest_budget`: при `0 ≤ rho < 1`, `0 ≤ gamma`, `0 ≤ D 0`, спаде `D (t + 1) ≤ rho * D t` и `gain t ≤ gamma * D t` сумма первых `n` выигрышей не превосходит `gamma * D 0 / (1 - rho)`.
- `stable_factor_two`: при `0 ≤ c i` отсутствие строго улучшающего перевода одной единицы бюджета влечёт `layerError (c j) (f j) ≤ 2 * layerError (c k) (f k)` для `f k ≠ 0`.

## Hagi/Budget/BitAllocTermination.lean
- `error_chain_descends`: если ошибка строго убывает на каждом соседнем шаге, то она строго убывает между любыми временами `m < k`.
- `improving_chain_injective`: такая последовательность распределений не содержит повторов.
- `no_infinite_improving_chain`: последовательности с постоянной суммой `∑ i, seq t i = B` и строго убывающей `totalError` не существует, поскольку пространство таких распределений конечно.

## Hagi/Cert/CertifiedArgmax.lean
- `argmax_pair_certified`: при `0 ≤ eps`, `|GammaHat k - Gamma k| ≤ eps` и `2 * eps < GammaHat i - GammaHat j` следует `Gamma j < Gamma i`.
- `argmax_select_certified`: если sel максимизирует Γ̂ и отделён от каждого другого варианта больше чем на `2 * eps`, то sel максимизирует истинный Γ.
- `tie_ambiguity`: при `0 < eps` и `0 < delta < 2 * eps` существуют две разные истинные функции с противоположными максимумами, обе согласованные с одной `eps`-точной оценкой.

## Hagi/Budget/DesignOpt.lean
- `spectral_tail_mono`: при `m ≤ m'` конечная сумма `(sigma j)^2` по индексам `j ≥ m'` не превосходит суммы по `j ≥ m`.
- `spectral_rank_exists`: для непустого конечного `s` и `0 < eps` существует `r`, для которого сумма хвоста по `j ≥ r` не превосходит `eps` от полной суммы квадратов.
- `shadow_price_sum_identity`: если `marg j = lam * c j` для каждого `j`, то `∑ j, marg j = lam * ∑ j, c j`; это алгебраическое тождество при заданном условии, а не общая теорема об оптимальности.

## Hagi/Budget/ElementQuant.lean
- `factor_quant_go`: если `‖dE - AB‖ = tail`, `‖AB - QAB‖ = qerr` и `tail + qerr < qdirect`, то `‖dE - QAB‖ < qdirect`.
- `ternary_factor_qerr_bound`: при `0 < s` и принадлежности всех элементов `M` диапазону `ternInRange s` сумма квадратов ошибок округления не превосходит `(card m * card r) * (s / 2) ^ 2`.
- `ternary_pair_qerr_sum`: аналогичная оценка для двух факторов `A`, `B` ограничивает сумму их квадратичных ошибок величиной `(card m * card r + card r * card n) * (s / 2) ^ 2`.

## Hagi/Budget/JointCost.lean
- `nsIter_block_le`: при `2 ≤ N`, `0 < h` и `0 ≤ r ≤ h` стоимость `N * nsIter h h + 3 * nsIter r (N * h)` не превосходит `nsIter (N * h) (N * h)`.
- `amdahl_ceiling`: при `0 < f < 1` и `0 < k` выполняется `1 / (f + (1 - f) * k) ≤ 1 / f`.
- `offdiag_pythagoras`: если `Wbd i j * Woff i j = 0` для всех индексов, то сумма квадратов `Wbd + Woff` равна сумме квадратов двух компонент отдельно.

## Hagi/Budget/RankBudget.lean
- `rankResidual_equalized`: при `0 < c j`, `0 < κ j`, `0 < lam`, равенстве `c j * κ j * exp (-κ j * rstar j) = lam * (m j + n j)` и одинаковой взвешенной стоимости распределений суммарный `rankResidual` для `r*` не больше, чем для `r`.
- `rankResidual_allocation`: при `0 < c j`, `0 < κ j`, `0 < lam`, `0 < L` доказано `(log (c j * κ j) - log L) / κ j = -(1 / κ j) * log (L / (c j * κ j))`.

## Hagi/Budget/ThermoCondensation.lean
- `inv_fact_mono`: `1 / (k + 1)! ≤ 1 / k!` для натурального `k`.
- `condensation_epsilon_to_gap`: при `0 < ε`, положительных нормированных весах экспоненциальной модели и `|d u - d v| ≤ 2 * √ε` усреднённый прирост `ceOneHot` для возмущений `m + d` и `m - d` не превосходит `ε`.
- `thermo_condensation_full`: объединяет эту оценку с сохранением неравенства `val j < epsL` для `j ≥ L`, если val не возрастает и `val L < epsL`.

## Hagi/Budget/TokenWeightBias.lean
- `token_weight_decomposition`: при `0 < ∑ i, T i` токенно-взвешенное среднее `g` равно обычному среднему плюс выборочной ковариации `T` и `g`, делённой на среднее `T`.
- `zero_bias_iff_uncorrelated`: при том же условии взвешенное среднее равно обычному тогда и только тогда, когда `∑ i, (T i - mean T) * (g i - mean g) = 0`.

## Hagi/Budget/WaterFilling.lean
- `exists_balanced_allocation`: для `0 ≤ c l` и любого натурального `B` существует натуральное распределение `f` с `∑ l, f l ≤ B`, при котором `layerError (c j) (f j) ≤ 2 * layerError (c k) (f k)` для всех `j`, `k` с `f k ≠ 0`.
- Доказательство выбирает минимум на конечном множестве распределений; оно не строит целочисленный оптимальный алгоритм и не оценивает время вычисления.
- `waterfilling_bound`: при `0 < lam`, равенстве `c i * exp (-kappa * bstar i) = lam` и одинаковых суммах `b` и `b*` остаток `kvResidual c kappa bstar` не превосходит остатка для `b`.

## Hagi/Budget/WeightedExpAlloc.lean
- `weightedExpAllocation_budget`: на конечном непустом `ι` при `0 < κ i` и `0 < w i` построенное распределение точно удовлетворяет `∑ i, w i * weightedExpAllocation c κ w B i = B`.
- `weightedExpAllocation_marginal`: при дополнительном `0 < c i` маргинальные величины `c i * κ i * exp (-κ i * allocation i)` равны `weightedExpPrice c κ w B * w i`.
- `weightedExpAllocation_optimal`: для любого вещественного `r` с тем же взвешенным бюджетом экспоненциальный остаток построенного распределения не больше остатка `r`; это непрерывная, а не целочисленная оптимальность.

## Hagi/Research/Legacy/MasterChallenge.lean
- `master_hagi_core_comparator`: при `0 ≤ lam`, `0 ≤ nu`, `0 ≤ epsQ` и `CorePremises S S' epsQ w` потенциал после перехода не превосходит исходного минус `verify.decrease`, плюс `lam * verify.riskSpend + nu * epsQ`.
- Та же теорема доказывает точное бюджетное равенство `S'.toGrowthState.budget = S.toGrowthState.budget - (verify S.toGrowthState).budgetSpend`; все условия `CorePremises` остаются посылками.

## Hagi/Cert/Core.lean
- Каноническое ядро сертификации (master plan v3, S1+S2): `SystemMetrics` (objective/risk/budget/task как функции состояния), `StepObligations` (отдельная структура с floor), `FloorsKept` — контракт нижних граней.
- `CertStep` — сертифицированный прогресс: положительный drop, спуск `objective s' ≤ objective s − drop`, точные законы потребления budget_next/risk_next с неотрицательными остатками  и floorsKept; `CertStep.budgetBound`/`CertStep.riskBound` — производные точечные оценки.
- `HoldStep` без утверждения прогресса всегда доступен (`HoldStep.id`); `TransitionStep` = `progress | hold`.

## Hagi/Cert/Empirical.lean
- C245 (Phase 1, A7): `Empirical P` — типизированная обёртка
эмпирических посылок (заместительный путь для голых `h_emp_*`;
миграции нет, AssumptionScan остаётся): поля measuredLaw/tolerance
(+ tolerance_nonneg)/modelRef/premise; `Empirical.out` распаковывает
ровно предъявленную посылку. Надёжностной класс D (addendum A7).

## Hagi/State/Views.lean
- C245 (Phase 1, A7): survey носителей состояния (TrainState — канон
спеки §4; GrowthState — legacy с GrowthStateViews (модуль слит в GrowthState, C419); FunctionalState;
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

## Hagi/Contracts/BatchRangeBF16Cert.lean
- BF16-гард для C223 batch-шага (C230): certified drop — точное выражение `2·batchAlignment²/batchLogitRangeSquare`; по-логитная bf16-ошибка — ПОСЫЛКА, универсального утверждения об округлении нет.
- `batchLoss_le_of_logitPerturbation`: равномерная по-логитная `eps`-ошибка сдвигает истинный batchLoss не более чем на `2·eps` (2-липшицевость one-hot CE, `CEQuantized.ceOneHot_le_of_abs_sub_le`).
- `bf16_guarded_ceRange_descent_le` / `bf16_guarded_ceRange_descent`: при строгом gate `4·eps < 2·A²/R'` реальный bf16-step строго уменьшает истинный batchLoss на `Δ = 2·A²/R' − 2·eps > 0`; `bf16_exact_binade_ceRange_descent` — режим `eps = 0` (точный logit-readback; на уровне кодов — `BF16Delta.exists_sameBinade_difference`).

## Hagi/Contracts/BatchCEAlignmentBudget.lean
- C233 (R2): `batchLogitRangeSquare_le_rangeCurvature_mul_alignment` — без посылок, острая средняя `batchLogitRangeSquare X θ y ≤ rangeCurvature X * batchAlignment X θ y` (транзитивность `R' ≤ R ≤ K·A`); `alignment_le_scaled_logitCertifiedDrop` — при `0 < batchLogitRangeSquare X θ y` бюджетная константа `2·A/(K+1)` сертифицирует острый residual `batchLogitCertifiedDrop` (выражение C230 bf16-gate), переносом через `batchCertifiedDrop_le_batchLogitCertifiedDrop`. Константа телескопа `(K+1)/2` не сужается (честная граница); закрывает деферрал C230 из `.omc/tech-debt.md`.
- `rangeCurvature_nonneg` и `batchRangeSquare_le_rangeCurvature_mul_alignment`: `0 ≤ rangeCurvature X` и `batchRangeSquare X θ y ≤ rangeCurvature X * batchAlignment X θ y`; граница сохраняется при тотализации пустого batch.
- `fixedBatch_sum_alignment_le_initial`, `fixedBatch_alignment_summable` и `fixedBatch_tsum_alignment_le_initial`: при непустом `V` суммы `batchAlignment` по фактической `fixedBatchState`-траектории сходятся, а конечные суммы и `∑' t, batchAlignment ...` ограничены `((rangeCurvature X + 1) / 2) * batchCEObjective X y S`.

## Hagi/Contracts/BatchCEBestResidual.lean
- `exists_alignment_le_fixedAlignmentCesaro`: при `0 < T` найдётся `t : Fin T`, чьё `batchAlignment` не превосходит среднее Чезаро за префикс.
- `exists_alignment_le_initial_div_time`: при непустом `V` найдётся такой префиксный шаг с `batchAlignment ≤ (((rangeCurvature X + 1) / 2) * batchCEObjective X y S) / T`.
- `exists_sqrt_alignment_le_sqrt_initial_div_time`: та же оценка выполняется после взятия квадратного корня из обеих сторон; это результат о лучшем элементе префикса, а не о последнем итерате.

## Hagi/Contracts/BatchCEGrowth.lean (вкл. BatchCEGrowthSelection и NaturalLean, слит C524)
- `growthObjective_iteratedQuarantinedGrowStep_antitone`: цель `growthObjective` на точной последовательности итераций `quarantinedGrowStep` не возрастает.
- `iteratedQuarantinedGrowStep_budget_nonneg`: если исходный бюджет `S0.state.res.budget` неотрицателен, неотрицательность сохраняется после любого числа таких итераций.
- `growthObjective_iteratedQuarantinedGrowStep_tendsto_ciInf`: неотрицательная антимонотонная последовательность целей сходится к своей точной нижней грани; равенство этой грани нулю или глобальному оптимуму не утверждается.

## Hagi/Contracts/BatchCEBudgetGuard.lean
- C233 (R2): `batchLogitCertifiedDrop` — острый сертифицированный residual `if batchLogitRangeSquare = 0 then 0 else 2·A²/R'` (ns `BatchCETrajectory`, `[Nonempty V]`); `batchLogitCertifiedDrop_nonneg`; `batchCertifiedDrop_le_batchLogitCertifiedDrop` — при `0 < batchLogitRangeSquare` старый residual не превосходит острый (посылка несущая: при `R' = 0 < R` старый residual положителен, острый нуль; негативные контроли `.tmp/C233/neg1.lean`, `neg2.lean`).
- `batchCEObjective_batchTrainStep_lt`: при непустом `V` и `0 < batchRangeSquare X (coreParameters S) y` фактический `batchTrainStep` строго уменьшает среднюю пакетную CE.
- `expandedHalfTrainStep_budget_nonneg`: при `0 ≤ trainingCost` и достаточном исходном бюджете для `expandedFeatureEvaluationCount + trainingCost` бюджет после шага неотрицателен.

## Hagi/Contracts/BatchCETrajectory.lean
- `fixedBatchObjective_sum_certifiedDrop_le_telescope`: при непустом `V` сумма `batchCertifiedDrop` по префиксу не превосходит точную разность между начальной CE и CE после `T` фактических шагов.
- `fixedBatchObjective_tendsto_ciInf`: последовательность значений `fixedBatchObjective` сходится к своей точной нижней грани; нулевой предел, глобальный оптимум и сходимость параметров не утверждаются.
- `evaluatedBatchMinimumNormPath_floor_kept_and_objective_lt`: при допустимой стоимости каждого шага, ненулевом `batchGradientMinimizer`, ограничениях риска, начальном `FloorKept` и `0 ≤ S.res.budget` порог качества сохраняется до `T`, а при `1 ≤ T` конечная CE строго меньше начальной.

## Hagi/Contracts/CEStepCertificate.lean
- `coreParameters_ceTrainStep`: фактические параметры после `State.trainStep` совпадают с параметрами безопасного шага по категориальной CE.
- `coreCEObjective_ceTrainStep_lt`: при непустом `V` и `0 < ceStepRange X (coreParameters S) t` выполненный `ceTrainStep` строго уменьшает категориальную CE.
- `coreCEObjective_identityCEStep_lt` и `batchCEObservation_identityCEStep_lt`: для конкретного двумерного начального состояния доказано строгое уменьшение обеих соответствующих целей; `batchCEObservation_identityInitial_eq` даёт начальному значению `Real.log 2`.

## Hagi/Contracts/LogicChoiceCert.lean
- Первый гибридный нейро-символьный сертификат (Track B7 item 3, addendum
  A4, C243): выбор маски как CE-задача — 16 масок решётки Венна суть
  классы (`Fintype (Fin 4 → Bool)`), лог-линейная голова по атомным
  признакам `choiceFeatures` (любое candidate-семейство; полный латтис —
  `ι = (Fin 4 → Bool)`, 16 классов).
- `choiceFeatures_logit_ones` — МОСТ: при единичных параметрах логит
  класса v РОВНО выходу `vennHead` маски `cand v` на тех же входах
  (скоринг выбора = точный выход логического слоя).
- Спуск — существующая C223-машина без новой математики:
  `batchLoss_logitSafeStep_le_residual` / `…_lt` на choice-batch.

## Hagi/Contracts/EMTrajectory.lean (вкл. ChangingEMTrajectory, слит C524)
- `changingEMPath_nll_antitone`: при `∀ t a i, 0 < observationEvidence (c t a i).1 (c t a i).2 (y i)`, сохранении текущих пар (условие hKeep) и включении носителей текущих постериоров в носители постериоров всех кандидатов следующего шага (условие hClose) агрегированная наблюдаемая NLL не возрастает.
- `changingEMPathDrop_budget` и `changingEMPathKLResidual_budget`: суммы уменьшений NLL и KL-постериора ограничены начальной NLL; обе величины неотрицательны и суммируемы.
- `changingEMPath_nll_tendsto_ciInf`: NLL сходится к своей неотрицательной точной нижней грани, без утверждения об оптимальности модели или сходимости параметров.

- `factorizedMixture_nll_le_old`: при конечных `I`, `X` и положительной исходной `observationEvidence` факторизованный выбор меток даёт суммарную наблюдаемую NLL не выше исходной.

- `finiteEMPath_nll_nonneg` и `finiteEMPath_nll_antitone`: для конечного замкнутого семейства с `∀ a i, 0 < observationEvidence (c a i).1 (c a i).2 (y i)` и включением носителя постериора каждого элемента base в носитель постериора каждого кандидата для всех `i` агрегированная NLL неотрицательна и не возрастает.

- `mixtureTrajectoryBank_succ`: для положительной исходной свидетельствуемости банк на шаге `t + 1` получается смешиванием текущей модели с соответствующей seed-моделью и весом `mixtureGridWeight`.

## Hagi/Contracts/GatedCEStepCertificate.lean
- `gatedCEObjective_gatedCETrainStep_lt`: при непустом `V` и `0 < gatedAlignment X (coreParameters S) t` фактический `gatedCETrainStep` строго уменьшает целевую CE с гейтингом; `gatedSafeDrop_le_gatedCETrainStep_drop` даёт лишь нижнюю оценку фактического уменьшения.
- `gatedCEPath_antitone` и `gatedCEPath_tendsto_ciInf`: при `0 < δ` и допустимом начальном решении цель на `scaledBiasBinaryPath` не возрастает и сходится к своей точной нижней грани.
- `gatedCEPath_flops_le`: при дополнительном `0 ≤ opCost` счётчик flops после `T` шагов не превосходит `S0.res.flops + (opCost / δ) * gatedCEObjective X t S0`.

## Hagi/Contracts/GatedCETrajectory.lean
- `fixedGatedAlignment_sq_tendsto_zero_uniform`: при непустом `V` квадрат текущего `fixedGatedAlignment` для фиксированных входных данных стремится к нулю.
- `fixedGatedAlignment_tendsto_zero_uniform`: сам текущий `fixedGatedAlignment` стремится к нулю.
- `fixedGatedResidualTranspose_tendsto_zero_uniform`: каждая координата текущего `gatedResidualTranspose` также стремится к нулю; это не утверждение о внешнем качестве или глобальном оптимуме.

## Hagi/Contracts/GatedCEGradientNorm.lean
- `gatedGrad` отождествляет градиент гейтированного одноцелевого CE
  с `-gatedDirection`; `gatedGrad_ofLp` даёт покоординатное равенство
  с `gatedResidualTranspose` без предположений сверх `Fintype V`.
- `fderiv_gatedCE_apply` и `fderiv_gatedCE_apply_inner` выражают
  Fréchet-производную CE как действие / вещественное скалярное
  произведение с `gatedGrad` при `[Nonempty V] [DecidableEq V]`.
- `norm_gatedGrad_sq`: `‖gatedGrad‖² = gatedAlignment` определительно.

## Hagi/Contracts/GatePipeline.lean
- C264 (addendum A10, приоритет P1): ГЕЙТ-ТЕОРЕМА — пайплайн
  Python-гейта как он реально используется, в ОДНОМ Lean-модуле
  (состав: rescale → δ-расписание → union → P(false commit) ≤ δ).
- `hoeffding_pm1_two_sided` — диапазонное шкалирование [−1,1]→[0,1]
  (Y = (X+1)/2): двусторонняя граница `2e^{−nη²/2}` в [−1,1]-единицах
  — радиус УДВАИВАЕТСЯ относительно [0,1]-шкалы.
- `gate_delta_schedule_sum_le` — честная конечная-K форма
  δ-расписания `Σ 6/(π²k²) ≤ 1` (K ≤ шести; тождество Базеля в
  пиннованном Mathlib отсутствует — поиск выполнен; S₆ = 5369/3600,
  монотонность по K, π > 3).

## Hagi/Contracts/AuditLedger.lean
- C274 (audit E7): формальный audit ledger — Lean-мост Python
  HoeffdingAudit: alpha spending, disjoint cursors
  (proposal-independent slices как полуинтервалы [lo,hi) на ℕ),
  old-task harm, rejected consumption, repeat-task floors, final
  test untouched.
- `AuditStream`/`AuditLedger` — машина состояний над срезами с
  полями-инвариантами (streamsDisjoint, spentNonneg, spentTotal,
  finalIsolated); шаги: `auditSpend`, `auditAdvance`, `auditReject`,
  `auditTouchFinal`.
- `audit_consume_alpha_exact`/`audit_consume_alpha_valid` — расход α
  уменьшает remaining ровно на α, Σ ≤ δtotal, остаток ≥ 0.

## Hagi/Contracts/GradientBottleneck.lean
- `logitGradM`: квадратный n×n комплексный матричный вид логит-градиента
  (вещественные записи коэрцированы) — носитель, требуемый Flywheel
  SVD API.
- `gradient_bottleneck_bound`: при посылке `rank Δ ≤ k` всякое достижимое
  логит-обновление `Δ` оставляет Frobenius-остаток не меньше
  квадратичного хвоста сингулярных чисел `logitGradM` за `k` — прямое
  следствие `eckart_young_lower_bound` (C226). Вывод «голова ранга D ⇒
  ранг обновлений ≤ 2D» и нетривиальность хвоста (Prop A.5) отложены
  и не утверждаются; при `k ≥ n` оценка тривиальна.
- C232 (прямоугольный): `selP inj`/`coSelQ inj` — row-embedding с
  `coSelQ_mul_selP` (Q·P = 1), `emb_rank_eq` (точное сохранение
  ранга), `frobenius_selP_eq` (изометрия Фробениуса).
  `eckart_young_lower_bound_rect`: прямоугольная EY-оценка снизу для
  B : m×n с rank ≤ k — перенос квадратной через изометрию.
  `gradient_bottleneck_bound_rect`: прямоугольный
  (контексты × словарь) bottleneck через `logitGradRectM`. Хвост —
  хвост ВСТРОЕННОЙ квадратной матрицы (Flywheel truncated-SVD
  квадратный — заметка аудита «уже прямоугольный» ошибочна);
  идентификация с прямоугольным singularValues-спектром отложена;
  при k = 0 оценка сводится к честному ‖A‖² ≤ ‖A−B‖².
  `factor_update_rank_le`: rank(A·Bᵀ) ≤ card r — близнец
  `Hagi.Architecture.block_rank_le` (ориентация Aᵀ·B).

## Hagi/Contracts/GuardedLogitTrajectory.lean
- `guardedLogitPath_logitCE_antitone` и `guardedLogitPath_logitCE_tendsto_ciInf`: для фиксированного скалярного защищённого контроллера CE не возрастает и сходится к своей точной нижней грани.
- `guardedLogitDrop_tendsto_zero` и `guardedLogitDrop_tsum_le`: уменьшения CE стремятся к нулю, а их полная сумма не превосходит начальную CE.
- `guardedLogitPath_eventually_eq`: сам путь после некоторого `N` постоянен; `guardedLogitPath_tendsto_eventual_value` доказывает сходимость к этому значению.

## Hagi/Contracts/HadamardTernaryBridge.lean
- `hadamard_satTail_zero_of_l2_bound`: при `s > 0`, `0 ≤ μ ≤ 1`, оценке `‖x‖₂ ≤ s·√(2^k)` и посылке μ-некогерентности `‖Hx‖∞ ≤ μ·‖x‖₂/√(2^k)` каждая координата ортонормального Адамара-образа лежит в `ternInRange s` и `satTail` переиндексированного образа равен нулю. μ-некогерентность — посылка, НЕ следствие структуры Адамара: `hadamard_not_universally_incoherent` пинирует контрпример (`k = 1`, `x = (2, 2)`, первая координата `2√2 > 3/2` насыщает при `s = 1`, эффективное μ = √2 > 1).
- `hadamard_quant_error_le_of_l2_bound`: при тех же посылках суммарная квадратичная ошибка `qTern` на образе не превосходит `(2^k)·(s/2)²` — чистое полу-шаговое округление без хвоста насыщения.
- `satTail_eq_zero_of_forall_ternInRange`: генерическая лемма зануления `satTail` при тотальной вхождения-в-диапазон (используется редукцией штрафа).

## Hagi/Contracts/LogitGrad.lean
- `logitGrad z N c v = smax (z c) v − N c v`: строчный носитель
  логит-градиента CE; обобщает форму ceResidual на произвольные
  суб-вероятностные `N` (one-hot или частоты).
- `logitGrad_row_sum_zero`: строчные суммы ноль при вероятностных
  строках `N`.
- `logitGrad_pos_off_target`: вне one-hot цели запись строго
  положительна; `logitGrad_neg_at_target`: в цели строго отрицательна
  при явной посылке `∃ w ≠ t c` (синглтон-словарь даёт ноль, не
  отрицательное); новый строчный ингредиент — `smax_lt_one`.

## Hagi/Contracts/IdentityMomentConvergence.lean
- `meanPrediction` при заданном θ усредняет по supplied batch отдельные
  `softDef (ceLogits ...)`; `empiricalTarget` так же усредняет
  `(Pi.single (y b) 1 : Fin n → ℝ)`. Это средние вероятностей и one-hot
  меток, а не среднее параметров или logits.
- При `∀b, X b = 1` и `0<B` разность
  `meanPrediction X θ v − empiricalTarget y v` точно равна
  `meanResidualTranspose X θ y v`. Ограничение на batch отделяет
  вероятностную интерпретацию от пустого totalized average.
- `fixedBatch_meanPrediction_tendsto_empiricalTarget`: для identity features
  и `0<B` mean prediction на фактической `fixedBatchState`-траектории
  стремится к `empiricalTarget y`. Предел mean residual напрямую даёт C205,
  без дополнительной посылки новой дополнительной посылки предела.

## Hagi/Contracts/BudgetedParetoStepContract.lean
- `budgetedParetoStepContract` для `[Fintype V]` и `0≤opRisk` переводит
  реальный `budgetedParetoBatchTrainStep` в обычный `StepContract`.
  Для его successor `T` поле `StepContract.decrease` равно старому минус
  новому `batchCEObjective`, `StepContract.riskCost = T.saf.risk-S.saf.risk`,
  а `StepContract.budgetSpend = S.res.budget-T.res.budget`.
- Активный guard обеспечивает samplewise CE non-regression и nonnegative
  affordable cost; вместе с `0≤opRisk` этого достаточно для всех трёх
  nonnegative полей. Не требуется глобального условия `0≤opCost`,
  `Nonempty V`, строгого CE drop или nonnegative старого бюджета.
  Неактивный guard возвращает целое `S`, поэтому все три дельты равны нулю.
- На genuine positive commit прежний `sameZeroInitialMeanDrop_pos` даёт
  положительное уменьшение CE: бюджет `2→3/2`,
  `StepContract.budgetSpend=1/2`, риск `0→1/4`,
  `StepContract.riskCost=1/4`. Отрицательный и неподъёмный cost дают hold.
  Guard не проверяет risk, поэтому `0≤opRisk` необходимо даже при `B=0`
  и пустом типе vocabulary, без создания фиктивного элемента или `y 0`.

## Hagi/Contracts/BudgetedParetoStepCert.lean
- `budgetedParetoStepCert` возвращает существующий `StepCert` для реального
  `T = budgetedParetoBatchTrainStep X y S opCost opRisk write`.
  Требуются положительный `batchRangeSquare`, `0≤opRisk`, `opRisk≤riskLim`,
  исходный `FloorHeld S floor` и полная активная guard-посылка: nonnegative affordable opCost и CE non-regression для каждого supplied sample на каноническом
  `batchTrainStep`. Строительство использует существующий
  `batchTrainStepCert` и accepted equality, а не новый guard или record cast.
- Поля `StepCert.budgetSpend` и `StepCert.riskSpend` задаются явно и равны
  соответственно opCost и opRisk. Положительный
  `Hagi.Unified.HonestTransition.HonestTransition.objectiveDrop` и
  `Hagi.Unified.HonestTransition.HonestTransition.actualDescent` дают строгий
  arithmetic-mean supplied-batch CE descent у настоящего guarded successor.
  `Hagi.Unified.CertifiedLoop.StepCert.hdec` ограничивает новый бюджет через
  `S.res.budget` минус opCost, а
  `Hagi.Unified.HonestTransition.HonestTransition.budgetBound` даёт nonnegative бюджет. Это abstract ledger,
  а не фактически измеренные FLOP/time или общий budget спуск после HOLD.
- Из положительного range следует `0<B`; метка первого supplied элемента
  создаёт только локальный `Nonempty V`, без отдельной class-посылки и без
  фиктивного `y 0` при пустом batch.
  `Hagi.Unified.CertifiedLoop.StepCert.trans`,
  `Hagi.Unified.CertifiedLoop.StepCert.hdec` и
  `Hagi.Unified.CertifiedLoop.StepCert.quality` переносятся по accepted equality. Старый quality floor сохраняется благодаря
  неизменности stored quality, а не предположению о его улучшении.

## Hagi/Contracts/ObjectiveTrajectory.lean
- `sum_le_of_sum_two_mul_div_le`: при `0 < κ` и общей оценке `∑ t < T, 2 * f t / κ ≤ A` для каждого `T` следует `∑ t < T, f t ≤ κ * A / 2`.
- `summable_and_tsum_le_of_sum_two_mul_div_le`: при дополнительном `0 ≤ f t` последовательность `f` суммируема и `∑' t, f t ≤ κ * A / 2`.
- `exists_le_of_sum_two_mul_div_le`: при `0 < T` найдётся `t < T` с `f t ≤ κ * A / (2 * T)`; это оценка некоторого элемента префикса, а не всех поздних элементов.

## Hagi/Research/SchellingCandidateSelection.lean
- `mem_feasible_withStructuralConstraint`: допустимость контроллера `a` в усиленной задаче эквивалентна конъюнкции исходной допустимости `a ∈ feasible p M C` и `structuralConstraint (graphOf a) compatibility k top bottom`.
- Структурные условия локальной совместимости и маршрута от каждой верхней вершины к некоторой нижней вершине конечны; физическая безопасность и качество задачи из них не выводятся.

## Hagi/Research/SchellingMarkovRouting.lean
- `walkHistory_support_of_mem_feasible_withStructuralConstraint_of_adjSupported`: для ядра `K`, согласованного со смежностью допустимого графа, из каждой верхней вершины `s` существуют нижняя вершина `t` и путь `w`, чья `walkHistory w` лежит в носителе соответствующего марковского закона.
- `walkHistory_support_of_mem_feasible_withStructuralConstraint`: доказывает ту же поддержку истории для семейства ядер `K a` при условии `supportedRoutingKernel` на каждом допустимом контроллере.
- Утверждается существование поддерживаемой истории собственного горизонта пути, а не заданная конечная маргиналь или общее время достижения.

## Hagi/Contracts/StepCertificate.lean
- `trainStep_actualDescent`: `energy (trainStep S u) = energy S - (2 * u.eta * (∑ i, S.model.weights i * u.grad i) - u.eta ^ 2 * (∑ i, u.grad i ^ 2))`.
- `trainStepMinimalCert`: при `0 < u.eta` и `2 * (∑ i, S.model.weights i * u.grad i) > u.eta * (∑ i, u.grad i ^ 2)` строит `CertStep` с положительным фактическим уменьшением энергии.
- `trainStepCert`: при дополнительных ограничениях риска, стоимости, исходного `FloorHeld` и бюджета строит полный `StepCert`; сохранение качества использует неизменность `evaluate` при параметрическом шаге.

## Hagi/Core/Ambig.lean
- `lse_shift`: `lse (fun v => z v + c) = lse z + c`.
- `consensus_no_gain`: для логитов `z₀ v + const a` CE усреднённых логитов по метке `t` равна `lse z₀ - z₀ t`, то есть сдвиги между согласованными детьми не дают дополнительного выигрыша ансамбля.

## Hagi/Core/Attention.lean
- `attention_error_damped_sum`: при `0 ≤ p i` норма ошибки взвешенного выхода не превосходит `∑ i, p i * ‖e i‖`.
- `attention_error_damped`: если дополнительно `∑ i, p i = 1`, та же ошибка не превосходит максимума `‖e i‖` по конечному индексному множеству.
- `attention_error_damped'`: при тех же вероятностных условиях и общей оценке `‖e i‖ ≤ M` ошибка не превосходит `M`.

## Hagi/Core/BlockDiag.lean
- `blockDiagonal'_mulVec_apply`: блок `k` действия `blockDiagonal' M` на стекованный вектор равен `M k *ᵥ` соответствующему срезу вектора.
- `step0_equivalence`: для блок-диагонального объединения экспертов координата `(k, i)` результата равна `(W k *ᵥ x k) i`.

## Hagi/Core/Concat.lean
- `lse_mean_le_mean_lse`: для непустого `k`, `N ≠ 0` и `N` семейств логитов `lse` их поэлементного среднего не превосходит среднего отдельных `lse`.
- `ensemble_ce_le_mean_general`: для непустого `k` и `N ≠ 0` величина `ceOneHot t` средних логитов не превосходит среднего значений `ceOneHot t` отдельных экспертов.
- `softmax_gap_mass_ratio`: если `z b + g ≤ z a`, то `softmaxP z a ≥ Real.exp g * softmaxP z b`.

## Hagi/Core/Element.lean
- `delta_rank_le`: ранг `A * B` с внутренним типом `r` не превосходит `Fintype.card r`.
- `delta_exact_rank_bound`: если `A * B = ΔE`, то `ΔE.rank ≤ Fintype.card r`; это ограничение точно представимых остатков, а не теорема наилучшего приближения.
- `params_count`: доказано точное разложение `(N + 1) * (V * d) + (N + 1) * (r * (V + d))` в стоимость базовой формы плюс `N` дополнительных таких форм.

## Hagi/Core/ErrorProp.lean
- `propagate_bound`: при `0 ≤ α`, `‖J_l‖ ≤ α` и `‖r_l‖ ≤ ρ` норма ошибки после `L` шагов не превосходит `α ^ L * ‖δ₀‖ + (∑ i < L, α ^ i) * ρ`.
- `propagate_bound_contractive`: при `‖J_l‖ ≤ 1` оценка упрощается до `‖δ_L‖ ≤ ‖δ₀‖ + L * ρ`.
- `propagate_sq_bound`: если каждый шаг квадратично сжимается с коэффициентом `α ^ 2` и новый остаток ортогонален распространённой части, то квадрат энергии ошибки ограничен `α ^ (2 * L) * (δ₀ ⬝ᵥ δ₀) + weightedResidual α L`.

## Hagi/Core/F3Root.lean
- `root_invariance`: `(vi + u)^2 - (vj + u)^2 = (vi^2 - vj^2) + 2 * u * (vi - vj)`.
- `root_no_leaf_signal`: из `a + b = c + d` следует равенство двух средних `(a + b) / 2 = (c + d) / 2`.
- `anova_split`: `(a - (a + b) / 2)^2 + (b - (a + b) / 2)^2 = (a - b)^2 / 2`.

## Hagi/Core/FrobOuter.lean
- `frobSq_outerSum`: для ортонормальных семейств `u`, `v` квадрат Фробениусовой нормы `outerSum s σ u v` равен `∑ i ∈ s, (σ i)^2`.
- `frobSq_outer_orthonormal`: частный случай полной суммы `∑ i, σ i • outer (u i) (v i)` даёт сумму всех `(σ i)^2`.
- `frobSq_trunc_tail`: ошибка удаления компонент с индексами из `s` имеет квадрат Фробениусовой нормы `∑ i ∈ sᶜ, (σ i)^2`; нижняя оптимальность среди всех матриц заданного ранга здесь не доказывается.

## Hagi/Core/Hadamard.lean
- `hadamardReal_mul_transpose`: `hadamardReal k * (hadamardReal k)ᵀ = (2 ^ k : ℝ) • 1`.
- `smul_orthonormal`: из `A * Aᵀ = d • 1` и `c * c * d = 1` следует `(c • A) * (c • A)ᵀ = 1`.
- `hadamardOrthonormal_mul_transpose`: нормированная матрица `hadamardOrthonormal k` удовлетворяет `H * Hᵀ = 1`.

## Hagi/Core/Kronecker.lean
- `conjTranspose_kronecker_mul`: из `Aᴴ * A = 1` и `Bᴴ * B = 1` следует `(A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1`.
- `kronecker_mul_transpose`: над `ℝ`, из `A * Aᵀ = 1` и `B * Bᵀ = 1` следует `(A ⊗ₖ B) * (A ⊗ₖ B)ᵀ = 1`.
- `transpose_kronecker_mul`: аналогично, из `Aᵀ * A = 1` и `Bᵀ * B = 1` следует `(A ⊗ₖ B)ᵀ * (A ⊗ₖ B) = 1`.

## Hagi/Core/Lift.lean
- `parentPreservingQ_mul_transpose`: матрица `parentPreservingQ` ортогональна, то есть `Q * Qᵀ = 1`.
- `parentPreservingQ_diag`: `parentPreservingQ *ᵥ (fun _ => x) = fun _ => x`, поэтому три одинаковые родительские ветви сохраняются точно.
- `parentPreservingQ_trace`: след матрицы равен `2`; `parentPreservingQ_cos_angle` даёт `(trace - 1) / 2 = 1 / 2`.

## Hagi/Core/Merge.lean
- `head_prerotation`: при `Q * Qᵀ = 1` выполняется `(W * Qᵀ) *ᵥ (Q *ᵥ x) = W *ᵥ x`.
- `blockCols_mulVec_sum`: действие `blockCols W₁ W₂` на суммовый вектор равно сумме действий `W₁` и `W₂` на две его компоненты.
- `mulVec_dotProduct_mulVec`: при `Q * Qᵀ = 1` скалярное произведение сохраняется: `(Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y`.

## Hagi/Core/Mix.lean
- `mixed_invisible`: если для каждого `b` выполнено `∑ a, Q a b • W a = W b`, то `mixedLogits Q W h = plainLogits W h`.
- Это достаточное условие неизменности ансамблевых логитов; обратная импликация в файле не доказывается.

## Hagi/Core/NonlinearStep0.lean
- `perBlock_gauge_equiv`: если каждый поблочный модуль коммутирует со своим гейджем, то `PerBlockLayer` удовлетворяет `GaugeEquiv`.
- `perBlock_net_blockwise`: сеть из поблочных слоёв действует на блок `i` как независимая сеть `DeepNetV` на `x i`.
- `zero_init_identity`: слой `x ↦ x + P (0 • f x)` тождественен для любого `x`.

## Hagi/Core/RealF3Ortho.lean
- `dftPow_mul_conjTranspose`: комплексная матрица `dftPow k` унитарна, `dftPow k * (dftPow k)ᴴ = 1`.
- `dftPow_entry_modulus`: каждый её элемент имеет норму `(Real.sqrt (3 ^ k : ℝ))⁻¹`.
- `reUnitMat_mul_transpose`: вещественная матрица размера `Fin 3 × Fin 2` удовлетворяет `reUnitMat * reUnitMatᵀ = 1`.

## Hagi/Core/Ridge.lean
- `ridge_optimal`: при `0 ≤ lam` всякое `w₀`, удовлетворяющее `ridgeNormalEq X y lam w₀`, является глобальным минимизатором `ridge X y lam`: для любого `w` выполняется `ridge X y lam w ≥ ridge X y lam w₀`.

## Hagi/Core/RoPEMoments.lean
- `rope_score_delta`: при `m ≤ n` поворотный скор равен `pairInner x (rotVec θ (n - m) y)`; `rope_translation_shift` сохраняет его при общем сдвиге позиций.
- `rot_norm`: поворот сохраняет соответствующее попарно-блочное скалярное произведение.
- `rope_var_bound`: если диагональные и внедиагональные `cosSum` ограничены модулем `kappa * M`, `∑ n, z n ^ 2 = 1` и `0 ≤ kappa`, то отклонение нормированного второго момента `ropeScore` от `1 / 2` не превосходит `kappa * (1 + 2 * M) / 2`.

## Hagi/Core/RootContrast.lean
- `filter_partition_sum`: суммы `s j^2` по индексам `j < r` и `r ≤ j` внутри `range m` вместе равны полной сумме.
- `highway_gain_identity`: разность остатков при добавлении контрастных координат равна захваченной энергии `∑ j ∈ (range m).filter (fun j => j < r_c), s j^2` при неизменном члене `E_root r_root`.
- `rho_partition`: если полная спектральная энергия положительна, то `rhoCaptured m s r + rhoTail m s r = 1`.

## Hagi/Core/Select.lean
- `meanBound_greedy`: если `newcomer ≤ mean`, то `(N * mean + newcomer) / (N + 1) ≤ mean`.
- `selection_hurts`: построен контрпример, в котором `ceOneHot t₁ zB < ceOneHot t₁ zC`, но `ceOneHot t₂ (ens zA zB) > ceOneHot t₂ (ens zA zC)`; отбор по одиночной CE может ухудшить ансамбль.

## Hagi/Data/BoolVenn.lean
- Булевозначная решётка Венна для 16 функций двух переменных (Track B7,
  addendum A4, C242): `atomIdx`/`vennBool` — маска как таблица истинности;
  `venn_universal` — каждая `Bool → Bool → Bool` функция есть маска
  (16×4 = 64 случая, конструктивно).
- `rank_histogram` — гистограмма рангов `1-4-6-4-1` (биномиальные C(4,r),
  16 масок, decide); `maskRank` — число активных атомов.
- `de_morgan`/`de_morgan_involution` — инволюция решётки: дополнение
  маски_negates функцию на ТЕХ ЖЕ входах (вариант с отрицанием входов
  ЛОЖЕН: индекс атома отрицанных входов есть `3-k`, опровергнуто decide
  в C229-зонде).

## Hagi/Data/BytePatch.lean
- `seg_length`: длина сегмента `seg s a b` равна `b - a` в натуральной арифметике.
- `patchBytes_nat`: при `0 < p` и `K ≤ patchCount N p` сумма длин первых `K` патчей равна `min (K * p) N`.
- `patchSeq_total_length`: при `0 < p` сумма длин всех списков `patchSeq s N p` равна `N`.

## Hagi/Data/DBridge.lean
- `dQuad_nonneg`: при `0 ≤ pW v` и `∑ v, pW v = 1` квадрат взвешенного среднего `d` не превосходит взвешенного второго момента.
- `dfield_entropy_identity`: для строго положительных распределений корпусов и строго положительных нормированных весов `divField p w` равно разности взвешенной суммы `p i * log (p i)` и выражения энтропии смеси.
- `equilibrium_bracket`: при `0 ≤ rho < 1`, `0 ≤ D + delta` и `G (t + 1) ≤ rho * G t + D + delta` выполняется `G t ≤ rho^t * G 0 + (D + delta) / (1 - rho)`.

## Hagi/Data/DField.lean
- `kl_product`: для строго положительных `p1`, `q1`, `p2`, `q2` и нормированных `p1`, `p2` KL продуктовых распределений равно `klDef p1 q1 + klDef p2 q2`.
- `KL_product_ge_marginal`: при нормировках исходных и целевых распределений `klDef p1 q1` не превосходит KL соответствующих продуктов.
- `dfield_smoothing`: при `0 ≤ p v`, `0 < u v` и `0 < alpha < 1` смесь `(1 - alpha) * p v + alpha * u v` строго положительна для каждого `v`.

## Hagi/Data/DataMixing.lean
- `mixing_loss_convex`: при `0 ≤ K` функция `rho ↦ mixingLoss K c rho` выпукла на всём пространстве пропорций.
- `chunked_sum_exact`: сумма по `range (n * w)` равна двойной сумме по `c < n`, `j < w` значений `f (c * w + j)`.
- `ce_prior_decomposition`: для строго положительных нормированных `p`, `q` сумма `p * log q` равна `∑ p * log p + ∑ p * log (q / p)`.

## Hagi/Data/Distill.lean
- `kl_eq_ce_gap`: для строго положительных `q`, `p` выполняется `klDef q p = crossEntropy q p - crossEntropy q q`.
- `teacher_generated_identity`: `crossEntropy pE pTheta = crossEntropy pE pE + klDef pE pTheta` для строго положительных распределений учителя и ученика.
- `topk_distill_budget_tv`: если `∀ v ∉ S, q v = 0` и `∑ v ∈ S, q v = 1`, `0 < Z ≤ 1`, `p` и `q` положительны на `S` и `klDef q (truncNorm p S Z) ≤ α`, то `klDef q p ≤ α + (1 - Z) / Z`.

## Hagi/Probability/FannesPinsker.lean
- `log_sub_le_div`: при `0 < a ≤ b` выполняется `log b - log a ≤ (b - a) / a`.
- `abs_log_sub_le`: для положительных `a`, `b` справедливо `|log a - log b| ≤ |a - b| / min a b`.
- `entropy_lipschitz_smooth`: при `0 < delta ≤ 1` и `delta ≤ p v, q v ≤ 1` для всех `v` выполняется `|H(p) - H(q)| ≤ (2 / delta + 2 * log (1 / delta)) * TV(p, q)`; полная граница Фаннеса с сингулярным членом не доказывается.

## Hagi/Data/PACBayes.lean
- `log_weighted_jensen`: для строго положительной нормированной `q` и строго положительного `x` сумма `∑ i, q i * log (x i)` не превосходит `log (∑ i, q i * x i)`.
- `gibbs_variational`: для строго положительных нормированных `q`, `p` выполняется `∑ i, q i * f i ≤ ∑ i, q i * log (q i / p i) + log (∑ i, p i * exp (f i))`; вероятностный шаг PAC-Bayes здесь не доказывается.

## Hagi/Research/PPT.lean
- `truncation_bias`: если ядро `K` не выходит из `S`, а `pi` стационарно, то существование `y₀ ∉ S` с `0 < pi y₀` невозможно.
- `pptMixing`: для `pptKernel K`, входного ограничения `eps ≤ K x y`, нормированных неотрицательных `mu`, `pi` и стационарной `pi` выполняется `TV(chainAt mu K n, pi) ≤ (1 - card Seq * eps)^n * TV(mu, pi)`.
- `stationary_value_ge`: при `0 ≤ V x` и неотрицательной нормированной `pi` выполняется `gamma * Pr_pi[V ≥ gamma] ≤ ∑ x, pi x * V x`.

## Hagi/Research/PPTCanonical.lean
- `discovery_prob_stationary_identity`: на конечном непустом измеримом пространстве с измеримыми одноэлементными множествами для неотрицательной нормированной `pi` вероятность события `gamma ≤ V x` при тождественном выборе из `toPMF pi` равна `∑ x ∈ goodSet V gamma, pi x`.
- Результат касается сконструированного конечного распределения и не описывает инициализацию или смешивание другой цепи.

## Hagi/Dynamics/EndpointContraction.lean
- `endpoint_bivariate_bound`: при `0 ≤ κ < 1`, `0 ≤ β` и `x (t + 1) ≤ κ * x t + β * c t` выполняется `x T ≤ κ^T * x 0 + β * ∑ i < T, κ^i * c (T - 1 - i)`.
- `endpoint_geometric_tail`: если дополнительно `0 ≤ cbar` и `c t ≤ cbar`, то `x T ≤ κ^T * x 0 + β * cbar / (1 - κ)`.
- `endpoint_depth_budget`: при `0 < κ < 1`, `0 < ε` и `x 0 / ε ≤ (1 / κ)^T` получается `x T ≤ β * cbar / (1 - κ) + ε`.

## Hagi/Dynamics/GrowthBridge.lean
- `capability_exp_growth_floor`: при `0 < alpha`, `0 ≤ C 0`, `C (t + 1) ≥ C t * (1 + alpha)^(s t)` и `N ≤ ∑ t < T, s t` выполняется `C T ≥ C 0 * (1 + alpha)^N`.
- `risk_exp_decay_counted`: при `0 < beta < 1` и `R (t + 1) ≤ R t * (1 - beta)^(s t)` получается `R T ≤ R 0 * (1 - beta)^(∑ t < T, s t)`.
- `risk_epsilon_floor`: при `0 < eps`, `0 < R0`, `eps ≤ R0`, `0 < beta < 1` и достаточно большом `N` из логарифмического условия следует `R0 * (1 - beta)^N ≤ eps`.

## Hagi/Probability/GibbsCore.lean
- `partition_hot_limit`: на конечном непустом `V` сумма `∑ v, exp (-(ℓ v) / T)` при `T → +∞` стремится к `Fintype.card V`.
- `two_level_meanEnergy_strictMono`: для двухуровневой системы с `0 < ε` средняя энергия `ε / (1 + exp (ε / T))` строго возрастает при `0 < T₁ < T₂`.
- `partition_cold_limit`: если `0 ≤ ℓ v`, то при `T → 0⁺` сумма статистических весов стремится к числу состояний с `ℓ v = 0`.

## Hagi/Energy/EntropyProduction.lean
- `exp_neg_entropyProduction`: при `0 < p x` и `0 < q x` выполняется `exp (-entropyProduction p q x) = q x / p x`.
- `ift_normalization`: для `FluctuationSetup p q` сумма `∑ x, p x * exp (-entropyProduction p q x)` равна `1`.
- `second_law`: для той же конечной положительной модели `0 ≤ ∑ x, p x * entropyProduction p q x`; это среднее равно KL между двумя распределениями траекторий.

## Hagi/Energy/FreeEnergy.lean
- `free_energy_gap`: при строго положительных `q`, `p` и `∑ v, q v = 1` выражение `∑ v, q v * ((-tau) * log (p v) + C) + tau * ∑ v, q v * log (q v)` равно `tau * klDef q p + C`.
- `geometric_pool_identity`: для строго положительных `q`, `p i`, нормированных `q` и весов `w` с `∑ i, w i = 1` сумма `∑ i, w i * klDef q (p i)` равна `klDef q (geometricPool) - log Z`, где `geometricPool v = (∏ i, (p i v)^(w i)) / Z`.

## Hagi/Energy/Landauer.lean
- `landauer_sandwich`: для положительных нормированных wPre, wPost, `0 < cUnit` и посылок `cUnit * klDef wPost wPre ≤ dissipation` и `dissipation ≤ kappa * s * quantErr` следует `klDef wPost wPre ≤ kappa * s * quantErr / cUnit`.
- `landauer_cap_certified`: при дополнительных `0 ≤ kappa`, `0 ≤ s` и `quantErr ≤ 1 / 2` верхняя граница усиливается до `klDef wPost wPre ≤ kappa * s / (2 * cUnit)`; физический смысл коэффициентов входит в `h_emp_landauer`, а не выводится.
- `first_crossing_le_lifetime`: если `θ (T * kmin) > θtarget`, то существует первый `n ≤ T` с `θ (n * kmin) > θtarget`, до которого таких пересечений нет.

## Hagi/Energy/PairwiseCategorical.lean
- Track E1 (addendum A9, CRAM 2611.17309): дискретная парная энергия
  `pairwiseEnergy B K x = Σ B i (x i) + (1/2)·pairwiseInteractionSum K x`
  на конечных переменных/доменах; КОНВЕНЦИЯ: ordered-pair сумма
  Σ_{j≠i}, 1/2 вне её, симметрия K НЕ предполагается (пин E1).
- `pairwise_energy_onehot` — (E1a) точное тождество
  `meanFieldFreeEnergy β B K (oneHotState x) = pairwiseEnergy B K x`
  при ЛЮБОМ β (энтропийный член 1·log 1 = 0): вершина продукт-симплекса
  есть сама конфигурация.
- `meanfield_decomposition` — (E1b) точная декомпозиция
  `F(p) = expectedPairwiseEnergy B K p + (1/β)·ΣΣ p i a·log (p i a)`
  (= E_{∏p_i}[H] − (1/β)·Σ H(p_i) в шенноновской форме); содержание
  продукт-меры — в определении `expectedPairwiseEnergy` (P(X_i=a,X_j=b)
  = p i a·p j b), тождество — точная перестановка сырой формы CRAM.

## Hagi/Energy/SingleCellDescent.lean
- Track E2 (addendum A9 + A9-supplement, CRAM 2611.17309): дискретное
  одно-клеточное ядро — точная дельта энергии переноса ОДНОЙ клетки.
- `localField` — локальное поле `L_i(a) = B_i(a) + Σ_{j≠i} K_ij(a, y_j)`
  (форма A9-supplement); `transposeLocalField` — транспонированный
  компаньон (без симметрии они различны).
- `single_cell_move_energy_delta` — (E2a MAIN, общая, БЕЗ симметрии):
  `E(y^{i←a}) − E(y) = (1/2)·((Ld a + Lt a) − (Ld b + Lt b)) +
  (B_i(a) − B_i(b))` — все партиционные члены без клетки i сокращаются
  ТОЧНО (чистота куплена конвенцией C260: ordered-pair, 1/2 снаружи).

## Hagi/Energy/EnergyCoordinateStep.lean
- Track E2: координатная минимизация как ТОЧНЫЙ KL-сертификат —
  безопасная дискретная альтернатива Эйлеровым шагам непрерывного
  потока (собственное предостережение статьи CRAM).
- `log_softDef` — перепаковка логарифма софтмакса
  `log (softDef z a) = z a − log (Σ exp z)`; `sum_mul_right_eq` —
  вынос константы справа из суммы.
- `singleCellFreeEnergy` — одно-переменная свободная энергия
  `F_i(p) = (1/β)·Σ p log p + Σ hz p + c` (сырая форма CRAM с
  y_{-i}-константой c, которая сокращается в любой разности).

## Hagi/Energy/EnergyFlow.lean
- Track E2 (уточнение A9-supplement): непрерывная часть, разделённая на
  (1) алгебраические тождества и (2) supplied-trajectory теорему —
  БЕЗ какого-либо ODE-existence API.
- Алгебраический слой: `quadraticVar` — дисперсионная форма
  uᵀ(diag p − ppᵀ)u = Σ p u² − (Σ p u)² (гессиан logsumexp без тяжёлой
  матричной машинерии); `quadraticVar_eq` (тождество дисперсии = Σ
  квадратов отклонений); `quadraticVar_nonneg` (PSD); `quadraticVar_const`
  (калибровочное нулевое направление H1 = 0);
  `softmax_legendre_identity` (vᵀp − β⁻¹ log Σ e^{βv} = β⁻¹ Σ p log p);
  `logsumexp_grad_along_dir` (градиент logsumexp ЕСТЬ p, направленная
  форма); `soft_curve_deriv` (ṗ = β·p·(u' − Σ p u')).
- `localMeanField` — поле на убеждениях `B_i(a) + Σ_{j≠i,b} K_ij(a,b)·p_j(b)`.

## Hagi/Energy/PoEBound.lean
- `poe_logZ_second_order`: для конечных `V` (непустого) и `K`, весов `w i ≥ 0` с суммой 1 и границы `R i` на размах `z i − Σₗ w l·z l` доказано `|log Z_w − Σᵢ w i·log Z_i| ≤ (1/8)·Σᵢ w i·(R i)²`, где `Z_w = Σ_v exp(Σᵢ w i·z i v)`.
- `poe_logZ_pairwise`: если `|z i v − z j v| ≤ D i j` для всех `i,j,v`, то та же ошибка не превышает `(1/2)·ΣᵢΣⱼ w i·w j·(D i j)²`; это отдельная оценка, а не утверждение с константой `1/8` по парным диаметрам.
- `poe_sequence_speed`: на конечной последовательности `T`, при размахе центрированных логитов на каждом токене не более `M t`, сумма модулей ошибок нормировщиков ограничена `(1/8)·Σ_t (M t)²`. Теорема говорит о численной оценке, а не о физическом времени вычисления.

## Hagi/Energy/PreNorm.lean
- `var_recursion`: для вещественных `x b s` при условии перекрёстного зануления `x * b = 0` доказано точное `(x + s*b)^2 = x^2 + s^2*b^2`; общая «независимость ветвей» в утверждение не входит.
- `constructive_scale`: при `(L:ℝ) > 0` и `v > 0` масштаб `s = 1 / √(L*v)` удовлетворяет `s^2 * v = 1/L`. Таким образом формально выравнивается второй момент вклада одной ветви.

## Hagi/Energy/Quantizer.lean
- `gridQ_error` и `gridQ_idem`: при `Δ > 0` ближайший узел `gridQ Δ x = Δ·round(x/Δ)` отличается от `x` не более чем на `Δ/2`, а повторное квантование не меняет узел.
- `gridQVec_norm_sq`: сумма квадратов покоординатных ошибок вектора на конечном `k` ограничена `card k·(Δ/2)^2`; тем самым каждая ошибка не превышает `Δ/2`.
- `quantizer_optimal_step`: для `c > 0`, `Δ > 0` доказано `c + c*log(1/c) ≤ Δ + c*log(1/Δ)`; это точное утверждение о выбранном шаге скалярного функционала.

## Hagi/Energy/STEStep.lean
- `tern_distortion_round`: для нормированного `x ∈ [-1,1]` округление `tern x` имеет ошибку `|x − tern x| ≤ 1/2`.
- `tern_scale_invariance`: при `c > 0`, `s > 0` выполнено `tern ((w*c)/(s*c)) = tern (w/s)`; инвариант относится к нормированному правилу округления, а не к RMS реальных весов или устойчивости обучения.
- `ste_step_residual`: при `gradStep ≥ 0` и явной посылке `h_emp_res : |wdelta − gradStep| ≤ s/2` следует `|wdelta| ≤ gradStep + s/2`. Отдельно `ste_residual_of_tern` при `s>0` и `gradStep/s ∈ [-1,1]` даёт `|s*tern(gradStep/s) − gradStep| ≤ s/2`.

## Hagi/Energy/Ternary.lean
- `tritEncode_injective`: кодирование пяти тритов в base-3 инъективно; используемое арифметическое условие — `3^5 ≤ 2^8`.
- `roundTern_error_scaled`: при `s > 0` и `|x| ≤ 3s/2` ошибка `|x − s*roundTern(x/s)| ≤ s/2`; `clampInt4_error` аналогично даёт ошибку `≤ 1/2` при `|x| ≤ 15/2`.
- `lsScale_optimal`: если `Σᵢ(q i)^2 > 0`, коэффициент `(Σq*x)/(Σq*q)` минимизирует `Σ(x i − s*q i)^2` по всем вещественным `s`.

## Hagi/Ensemble/MergePrice.lean
- `merge_price_quad`: при `M − Wi = −dev` квадратичная модель `QuadModel xs Wi M` точно равна `sigmaPrice xs dev`.
- `price_zero_iff_ker`: `sigmaPrice xs dev = 0` тогда и только тогда, когда `dotProduct (xs x) dev = 0` для всех `x`.
- `merge_gate_certified`: из выполненного предиката `MergeApproved` заключается `Σᵢ w i*sigmaPrice(xs i)(devs i) + κ*(n'*s)/2 < twoGap`; это распаковка сертифицированного порога, а не доказательство качества произвольного слияния.

## Hagi/Ensemble/GapLaw.lean
- `twoGap_nonneg`: для строго положительного `p` с суммой 1 зазор `twoGap p d` неотрицателен; `twoGap_zero_iff` утверждает равенство нулю тогда и только тогда, когда `d u = c` для некоторой константы `c` и всех `u`.
- `twoGap_cosh`: двойная сумма с `exp(d u − d v)` точно равна двойной сумме с `cosh(d u − d v)`.
- `pairVarEq`: при `Σp = 1` двойная взвешенная сумма `(d u − d v)^2` равна удвоенной дисперсии `Σp*d² − (Σp*d)^2`.

## Hagi/Ensemble/Hoeffding.lean
- `twoGap_bounded`: для вероятностных `p`, `M > 0` и условия `|d u − d v| ≤ M` доказано `Hagi.twoGap p d ≤ M^2/4`.
- `hoeffding_tail`: если `d v ∈ [a,b]`, `a < b`, веса `w` неотрицательны и нормированы (`∀ v, 0 ≤ w v`, `∑ v, w v = 1`) и `Σw*d = 0`, то масса точек с `ε ≤ d v` не превышает `exp(−2ε²/(b−a)^2)` при `ε ≥ 0`.
- `hoeffding_union_tail`: для конечного семейства `K` таких центрированных функций и тех же неотрицательных нормированных весов `w` масса объединения событий `∃k, ε ≤ d k v` ограничена `card K·exp(−2ε²/(b−a)^2)`.

## Hagi/Ensemble/PolicyCompatibility.lean
- `integration_rejects_far_teacher`: если `Dmax < Dpolicy`, то `MOPDApproved twoGap price Dpolicy Dmax` ложен независимо от величин `twoGap` и price.
- `mopd_kl_scaling_warning`: при эмпирической посылке `h_emp_scaling : Dpolicy = 5*Dbase`, положительных `Dbase, ε` и условии безопасности `Dpolicy*ε ≤ 1` получается `Dbase ≤ 1/(5*ε)`. Посылка масштабирования не выводится в модуле.

## Hagi/Ensemble/QFormerBridge.lean
- `punctured_unbiased`: для неотрицательных весов `W b` с маргиналиями `Σ_{b:b i=t} W b = p` при `t=true` и `1−p` при `t=false` доказано `Σ_b W b*puncturedSum x b = p*Σ_i x i`.
- `vista_bridge_zero` и `vista_residual_identity`: нулевой остаточный вход даёт `bridgeOut U A 0 = 0`, поэтому `Vres + bridgeOut U A 0 = Vres`. Теоремы о концентрации прореженной суммы в этом файле отсутствуют.

## Hagi/Ensemble/SigmaKernel.lean
- `quad_form_factorization`: для `Σ = Aᵀ*A` доказано `v ⬝ᵥ (Σ.mulVec v) = (A.mulVec v) ⬝ᵥ (A.mulVec v)`; `quad_form_zero_iff` даёт равенство нулю ровно при `A.mulVec v = 0`.
- `gn_grad_inner_ker`: если `X.mulVec d = 0`, то `(Xᵀ.mulVec r) ⬝ᵥ d = 0`; `gpm_implies_safeqp_gn` при `eps ≥ 0` превращает это в условие `−eps ≤ …`.

## Hagi/Ensemble/UniformCert.lean
- `two_sided_good_point`: для положительных нормированных `w`, ограниченных центрированных `d k` и `2*card K*exp(−2ε²/(b−a)^2) < 1` существует `v`, для которого `|d k v| < ε` при всех `k`.
- `calibrated_good_point`: при `0 < θ < 1` и `2*card K*θ < 1` тот же вывод получен с радиусом `(b−a)*√(log(1/θ)/2)`.
- `calibrated_two_sided_mass`: без дополнительного условия `2*card K*θ < 1` масса точек, одновременно удовлетворяющих этому радиусу, оценивается снизу величиной `1 − 2*card K*θ`.

## Hagi/Research/Legacy/HAGICertWitness.lean
- `hagicert_nonvacuous`: построены последовательности состояний и числовые параметры, для которых выполнен `HAGICert … T`. Это свидетель совместимости формального контракта на конкретных данных, а не оценка качества реального обучения.

## Hagi/Research/Legacy/Nonvacuity.lean
- `merge_energy_bridge`: для midpoint-логитов доказано точное `CE(mid) = (CE(z₁)+CE(z₂))/2 − jensenGap z₁ z₂`, а также неотрицательность зазора.
- `h_emp_merge_of_bridge` — доказанная теорема, а не внешняя посылка: она выводит одновременно `CE(mid) ≤ meanCE − jensenGap` и `0 ≤ jensenGap`.
- `corePremises_nonvacuous_strict`: для любого `E` существуют состояния, `epsQ,w`, удовлетворяющие `CorePremises`, с положительными gap и growGain.

## Hagi/Research/Legacy/NonvacuityHorizon.lean
- `sat_step_laws`: при `γ ≠ 0` параметрическая траектория одновременно удовлетворяет шагу `C(t+1)=C(t)+γ*F(t)` и насыщению `C(t+1)=C(t)+σ*(Cstar−C(t))`.
- `sat_cone_iff`: при `γ > 0` условие `k*satC … t ≤ satF … t` эквивалентно `γ*k*Cstar ≤ (γ*k+σ)*Δ*(1−σ)^t`.
- `witness_achieves_horizon`: при положительных `γ,k,Cstar,C0`, `0<σ<1`, `C0<Cstar`, `1≤T` и геометрическом условии для всех `t<T` доказаны оба закона шага, конус и строгое `satC 0 < satC T`.

## Hagi/Benchmarks/QuadLoopWitness.lean
- `quadE_qhalf`: после `t` полушагов энергия равна `quadE a (qhalf a x t) = (1/4^t)*quadE a x`.
- `quad_loop_horizon`: если `quadGrad a x ≠ 0` и `n ≥ 1`, то `quadE a (qhalf a x n) < quadE a x`; `quad_witness_T3` и `quad_witness_T10` — конкретные специализации.

## Hagi/Research/Legacy/QuadraticConcrete.lean
- `quad_core_premises`: для любых `a : ℝ` и `w : Fin 5 → ℝ` построены квадратичные состояния, удовлетворяющие `CorePremises (quadGen a) (quadGen' a) 0 w`.
- `quad_kappa_at0` даёт `‖fderiv ℝ (quadE a) 0‖ ≤ 1+|a|`; `quad_conj13` проверяет соответствующее неравенство для квантованного скалярного шага с тем же коэффициентом.

## Hagi/Benchmarks/QuadraticEndToEnd.lean
- `qStep_descent`: при `0 < eta < 1` и `x ≠ a` шаг `qStep` строго уменьшает `qLoss a`.
- `qIter_loss`: после `t` итераций потеря точно равна `(1−2*eta)^(2*t)*(x−a)^2`.
- `qQuant_err_bound`: при `Δ>0` и `|y−a| ≤ R` увеличение потери после `gridQ` не превышает `(Δ/2)*(2R+Δ/2)`.

## Hagi/Benchmarks/QuarticWitness.lean
- `quartic_two_steps`: построенные два шага дают `qE w2 < qE w0`, сохраняют `FloorKept qMeasured w2 qFloor` и удовлетворяют явному бюджетному условию `0 ≤ 9 ∧ 9 ≤ 10−1`.
- `quartic_drops_pos`: оба сертифицированных objectiveDrop строго положительны; `qFloor_kept` отдельно проверяет покомпонентный нижний барьер качества при `qE w ≤ qE w0`.

## Hagi/External/Diversity.lean
- `grad_dist_polarization`: во внутреннем пространстве доказано `‖a−b‖² = ‖a‖²+‖b‖²−2⟪a,b⟫`.
- `gittins_index_max`: на любом непустом конечном типе существует индекс, максимизирующий заданную вещественную функцию idx.
- `merge_init_head_start`: из `meanCE < logV` следует `0 < logV − meanCE`. Теорема фиксирует только этот арифметический зазор, а не эмпирическое превосходство всего обучения.

## Hagi/External/Flywheel/CoherenceCharacterization.lean
- `trunc1_spectral_optimal_aux`: для любой матрицы `N` ранга не более 1 доказано `‖A−truncatedSVD A 1‖ ≤ ‖A−N‖` в норме соответствующего операторного инстанса.
- `frobenius_spectral_distance_with_gap`: при `card n > 1` и `spectralGap A > 0` расстояние между SVD- и спектрально оптимальным rank-1 приближением ограничено удвоенной Frobenius-ошибкой хвоста; квадрат последней равен сумме квадратов сингулярных чисел без нулевого индекса.
- `frobenius_spectral_distance_coherence_aware`: для ненулевого `E = A−truncatedSVD A 1` доказана оценка `‖truncatedSVD A 1−spectralOptimalRank1 A‖ ≤ ‖E‖_F*(1+1/(√rank E * coherenceFactor E))`.

## Hagi/External/Flywheel/CourantFischer.lean
- `courantFischer_maxMin_bounds`: для эрмитовой `A` и `k>0` head-подпространство достигает `rayleighInf ≥ λ_{k−1}`, а всякое `k`-мерное ненулевое подпространство имеет `rayleighInf ≤ λ_{k−1}`.
- `courantFischer_minMax_bounds`: tail-подпространство даёт `rayleighSup ≤ λ_{k−1}`, а всякое подпространство размерности `n−k+1` имеет `rayleighSup ≥ λ_{k−1}`. Совместно это две вариационные формы Куранта–Фишера.

## Hagi/External/Flywheel/EckartYoungLower.lean
- `eckart_young_lower_bound`: для любой `B` с `rank B ≤ k` доказано `∑ i, (truncatedSingularValues_tail A k i)² ≤ ‖A−B‖²` — общая нижняя граница Эккарта–Юнга в хвостовой форме, замыкающая TODO из TruncatedSVDRank1.lean в полной общности.

## Hagi/External/Flywheel/FrobeniusNorm.lean
- `frobenius_norm_sq_eq_trace`: доказано `‖A‖² = Re(trace(Aᴴ*A))`; `frobenius_norm_unitary_mul` даёт инвариантность нормы при левом умножении на унитарную матрицу.
- `eckart_young_frobenius`: для любой `B` с `rank B ≤ k` доказано `‖A−truncatedSVD A k‖ ≤ ‖A−B‖`. Таким образом оптимальность усечения в Frobenius-норме формализована, несмотря на устаревшее примечание в ведущем комментарии.

## Hagi/External/Flywheel/MDLRank.lean
- `mdlJ_first_order`: при `lam*c>0`, `kstar < card n`, `σ_{kstar}² ≤ lam*c` и стартовом условии `kstar=0 ∨ lam*c < σ_{kstar−1}²` выбранный `k*` минимизирует `mdlJ A lam c` по всем `k`.
- `mdl_rank_ce`: для `kappaF ≥ 0` и kappaF-липшицева по Frobenius-норме функционала ell доказано `|ell A−ell(truncatedSVD A k)| ≤ kappaF*√(Σ tailSingularValues²)`.

## Hagi/External/Flywheel/NegDiagRank.lean
- `neg_diag_pos_off_diag_kernel_trivial`: если `M i i < 0`, `M i j ≥ 0` при `i ≠ j` и все строчные суммы строго отрицательны, то ядро `M *ᵥ` тривиально (max-|x| аргумент, самодостаточно).
- `neg_diag_pos_off_diag_injective`: при тех же посылках `mulVecLin M` инъективен. Слабая версия (суммы `≤ 0`) ложна: лапласианов пример в файле убивает константный вектор; поэтому лендится только строгая версия.

## Hagi/External/Flywheel/MatrixNormRelations.lean
- `kronecker_perturbation_single_factor_B` и `…_C`: при непустых внутренних размерностях изменение одного сомножителя имеет точную норму, соответственно `‖B−B'‖*‖C‖` и `‖B‖*‖C−C'‖`.
- `kronecker_singularValue_perturbation` — псевдоним `kronecker_sub_spectral_norm_bound`: спектральная норма разности произведений Кронекера ограничена `‖B−B'‖*‖C‖ + ‖B'‖*‖C−C'‖`.

## Hagi/External/Flywheel/NormSupport.lean
- `mulVec_eucl_norm_sq_le`: для комплексной матрицы квадрат евклидовой нормы `A*x` ограничен `(ΣᵢΣⱼ‖A i j‖²)*‖x‖²`; `mulVec_eucl_norm_le` — следствие без квадратов.
- `frobenius_norm_eq_sqrt`: Frobenius-норма прямоугольной матрицы равна `√(ΣᵢΣⱼ‖A i j‖²)`.

## Hagi/External/Flywheel/SVD.lean
- `hermitian_spectralRadius_eq_sup_abs_eigenvalues` и `l2_opNorm_hermitian_eq_sup_abs_eigenvalues`: для непустого конечного индекса и эрмитовой `H` спектральный радиус и операторная норма равны максимуму модулей собственных значений.
- `coherence_eq_norm_ratio_rect`: для ненулевой прямоугольной `E` выполнено `coherenceFactorRect E = (‖E‖_F/‖E‖₂)/√rank E`.
- `incoherent_improved_bound_rect`: если `0<α≤coherenceFactorRect E`, то `‖E‖₂ ≤ ‖E‖_F/(α*√rank E)`; требуется положительная минимальная размерность и `E≠0`.

## Hagi/External/Flywheel/SpectralNormGap.lean
- `outerProduct_spectral_norm_le`: спектральная норма внешнего произведения ограничена `‖u‖*‖v‖`.
- `spectral_le_frobenius_with_gap`: для квадратной комплексной матрицы операторная норма не превосходит Frobenius-норму; `coherence_ratio_ge_one` при `A≠0` даёт `‖A‖_F/‖A‖₂ ≥ 1`.
- `spectral_error_rank1_bound`: спектральная ошибка rank-1 усечения ограничена `√(Σᵢ (truncatedSingularValues_tail A 1 i)²)`.

## Hagi/External/Flywheel/TruncatedSVDRank1.lean
- `singularValues₀_eq_zero_of_rank_le_one`: если `rank A ≤ 1` и индекс `k` имеет `k.val ≥ 1`, то `singularValues₀ A k = 0`.
- `truncatedSVD_rank1_identity`: при `rank A ≤ 1` доказано `truncatedSVD A 1 = A`.

## Hagi/External/Flywheel/WeylInequality.lean
- `thompson_interlacing`: если `rank B ≤ r` и `i.val+r < card n`, элемент `singularValues₀ A` с индексом `i+r` не превосходит `singularValues₀ (A+B)` с индексом `i`.
- `interlacing_low_rank_subtraction`: если `rank C ≤ k` и `k ≤ j.val`, то `σ_j(A) ≤ σ_{j−k}(A−C)`; `interlacing_for_eckart_young` — индексная Nat-форма того же перехода.

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

## Hagi/Math/Foundations/ConeTakeoff.lean
- `geometric_growth_from_cone`: если `γ,k≥0`, на `range T` выполнен шаг `C(t+1)=C t+γD t`, а на `range (T+1)` — конус `k*C t≤D t`, то `C0*(1+γ*k)^T ≤ C T`.
- `frontier_cone_inductive`: при `α>0`, `γ>0`, `ρ≥0`, `C t>0`, текущем конусе, динамике `ρ*D t + β*C t − ξ t ≤ D(t+1)`, капе и условии `α/γ*((1+α)−ρ)+ξ t/C t≤β` конус сохраняется на следующем шаге; `frontier_cone_invariant` при начальном конусе `α/γ*C 0 ≤ D 0` и выполнении тех же динамики, капа и β-порога для всех `t` распространяет это на все `t`.

## Hagi/Math/Foundations/GrowthBand.lean
- `growth_band_iter`: при `0≤αmin≤αmax` и двустороннем шаге `(1+αmin)C t≤C(t+1)≤(1+αmax)C t` доказаны обе границы `(1+αmin)^T*C0≤C T≤(1+αmax)^T*C0`.
- `saturation_gap`: при `0≤σ≤1` и шаге насыщения зазор точно равен `Cstar−C T=(1−σ)^T*(Cstar−C0)`.
- `saturation_ceiling`: если дополнительно `C0≤Cstar`, то `C T≤Cstar−(1−σ)^T*(Cstar−C0)` и `C T≤Cstar`.

## Hagi/Math/Foundations/Hoeffding.lean
- `bern_mgf_bound`: для `0≤θ≤1` и любого `s` доказано `1−θ+θ*exp s ≤ exp(θ*s+s²/8)`.
- `mgf_hoeffding_ab`: для конечного непустого `V`, нормированных неотрицательных `q` и `h v∈[a,b]` выполнено `log E_q[e^h] ≤ E_q[h]+(b−a)²/8`.
- `mgf_hoeffding`: если для любых `u,v` выполнено `h u−h v≤D`, то та же верхняя оценка имеет добавку `D²/8`.

## Hagi/Math/Foundations/MesoScale.lean
- `macro_collapse`: для неотрицательных `A,L` с оценками `A ℓ≤a0*ℓ^p`, `L ℓ≤L0*ℓ^(−q)` и `p<q` доказано `A ℓ*L ℓ → 0` при `ℓ→∞`.
- `micro_collapse`: для неотрицательных `A,L` при `p>0`, `A ℓ≤a0*ℓ^p` и ограниченной `L` произведение стремится к нулю справа при `ℓ→0`.
- `meso_peak_exists`: если `EI` непрерывна на `ℓ>0`, положительна в одной точке и стремится к нулю на обоих концах, то существует глобальный максимум на положительной полуоси.

## Hagi/Math/Foundations/Ortho.lean
- `ortho_norm_sq`: для ортонормального семейства `v` на конечном `ι` доказано `‖Σᵢ c i•v i‖²=Σᵢ(c i)²`; имеется и вариант по произвольному `Finset`.
- `gating_tail_bound`: квадрат нормы разности полной суммы и суммы по `s` равен `Σ_{i∈sᶜ}(c i)²`.

## Hagi/Math/Foundations/Potential.lean
- `hagiPotential_penalty_drop`: при `epsQ≥0` и `q−epsQ≤q'` доказано `max 0 (qTarget−q') ≤ max 0 (qTarget−q)+epsQ`.
- `sum_sub_mean_zero`: для `n>0` сумма отклонений от среднего равна нулю; `sq_decomp` даёт точное `Σ(r−c)²−Σ(r−mean r)²=n*(mean r−c)²`.

## Hagi/Math/Foundations/QuadEta.lean
- `quad_eta_identity`: для `quadLossAt a w = ½‖w−a‖²` градиентный шаг даёт точное `E(w−η∇E)= (1−η)²*E(w)`.
- `quad_eta_descent`: при `0<eta<2` и `0<quadLossAt a w` новая потеря строго меньше исходной.

## Hagi/Math/Foundations/Recurrence.lean
- `recurrence_upper`: при `0≤ρ<1` и `x(t+1)≤ρ*x t+c` для `t<T` доказано `x T≤ρ^T*x0+c*(1−ρ^T)/(1−ρ)`.
- `contraction_limit`: при постоянном `δ≥0` и аналогичной рекуррентности получается `x T≤ρ^T*x0+δ/(1−ρ)`.
- `growing_batch_stabilized`: при `0<ρ<1`, `ρ=1−ηL`, `σ²≥0`, `b0>0`, `δ≥1`, `ρδ>1`, `T≥1` и заданной шумовой рекурренте доказана явная граница `E T≤ρ^T E0+(η²σ²/b0)*ρ^(T−1)/(1−(ρδ)⁻¹)`.

## Hagi/Math/Foundations/StageCalculus.lean
- `compress_stage`: при `κ,s≥0`, `h_emp_dist : dnorm≤1/2` и `h_emp_lip : E3−E2pre≤κ*s*dnorm` следует `E3−E2pre≤κ*s/2`.
- `joint_stage_cap_optimal`: при `L>0`, `dnorm²≤inner` и посылке `h_emp_smooth` для шага `1/L` доказано `E2≤E1−dnorm²/(2L)`.
- `compound_budget`: при `α≥0`, `αD+J≤ε_c` и `G_next≤D` получается `α*G_next+J≤ε_c`; `adaptive_ns_exists` при `eps≥0` и `e 100=0` лишь даёт существование `s` с `e s≤eps`.

## Hagi/Math/Foundations/Telescope.lean
- `lyapunov_telescope_fin`: если `E(t+1)≤E t−eps` для всех `t<k`, то `E k≤E0−k*eps`.
- `lyapunov_gain_noise`: из `V(t+1)≤V t−gain t+noise t` на горизонте `T` следует `V T≤V0−Σgain+Σnoise`.
- `lyapunov_termination_fin`: при нижней границе `Emin≤E t`, постоянном спуске `eps>0` получается `(k:ℝ)≤(E0−Emin)/eps`.

## Hagi/Generalization/ModeState.lean
- `generalization_safe_step`: при `lam,nu,ε_Q≥0`, посылках `h_emp_fit`, ограничении прироста риска величиной budget и `h_emp_G : Qgen S−ε_Q≤Qgen S'` потенциал удовлетворяет `Φ'≤Φ−ε_E+lam*budget+nu*ε_Q`.
- `modeDrop_rejected`: условия `ModeDrop`, `h_emp_G` и строгое `ε_Q<ε_Qmode` несовместимы.
- `selector_skips_dominated`: при строго положительных весах скаляризации глобальный argmin не равен строго доминируемому checkpoint.

## Hagi/Geometry/SphericalSimplex.lean
- `dihedral_angle_ge_pi_div_three` и `dihedral_angle_lt_pi_div_two`: при `x≥2` выполнено `π/3≤arccos(1/x)`, а при `x>1` — `arccos(1/x)<π/2`.
- `euclid_sum_bounds`: для `n≥2` и `K=n(n+1)/2` доказано `(π/3)*K ≤ K*arccos(1/n) < (π/2)*K`.

## Hagi/Research/Ceilings.lean
- `gain_product_bound`: норма композиции непрерывных линейных операторов не превосходит произведения норм; `gain_stack_ceiling` при `q≥0` и `‖T‖≤q` для всех слоёв даёт `‖stackComp Ts‖≤q^Ts.length`.
- `frozen_saturation`: для неотрицательного `V` и шага `V(t+1)≤V t−eps t` сумма `eps` на любом `Ico m T` с `m≤T` не превосходит `V m`.
- `growth_dichotomy`: при `V(t+1)≤V t−eps t+b t` либо суммы `b` неограниченно растут, либо существует `B`, для которого все `Σ_{t<T}eps t≤V0+B`.

## Hagi/Research/ChainUnification.lean
- `training_core_is_measurement_tail`: если `E_dev=E_aligned`, `G_cap=η_p*η_o*η_s*E_dev`, а E_aligned и `α_align` ненулевые, то `η_p*η_o*η_s=α_trunc*α_safe*α_cap`.
- `deficit_factorizes`: при ненулевых семи измеренных знаменателях отношение двух произведений равно произведению соответствующих семи отношений.

## Hagi/Growth/FiberNecessity.lean
- `configs_injective_on_separated` и `used_configs_lower_bound`: если разделённые задачи обслуживаются своими конфигурациями, отображение конфигураций инъективно на семействе и `tasks.card ≤ card(image cfg tasks)`.
- `fiber_params_floor`: если у каждой использованной конфигурации `rank q≥rmin`, то суммарное `Σ rank q*d` не меньше `tasks.card*rmin*d`.

## Hagi/Growth/GainDecomposition.lean
- `merge_is_mean`: из разложения `mergeDecomp W M dev` следует `N • M=ΣW`.
- `pairwise_variance_identity`: для того же разложения `ΣᵢΣⱼ‖W i−W j‖²=2N*Σ_k‖dev k‖²`.
- `anticorrelated_suppressed`: для любого `u` доказаны `⟪M,u⟫=(Σ⟪W k,u⟫)/N` и `Σ⟪dev k,u⟫=0`; это точная проекционная алгебра, а не утверждение об измеренной антикорреляции.

## Hagi/Growth/GainRenewal.lean
- `gain_renewal_recurrence`: при `γ>0`, `ρ≥0`, равенстве gain-канала по смыслу двух оценок `γD≤G≤γD` и `D(t+1)≥ρD t+inj−ξ` доказано `ρG t+γ*(inj−ξ)≤G(t+1)`.
- `gain_renewal_growth`: при `0≤ρ<1`, `ξ<inj`, `0≤ξ,inj,D0` получается `ρ^t*G0+γ*(inj−ξ)*(1−ρ^t)/(1−ρ)≤G t`; `gain_renewal_growth_one` при `ρ=1` даёт линейную нижнюю границу.
- `bounded_frontier_no_sustained_growth`: при `α,γ>0`, `G t≤γD t`, `D t≤Dbar` и gate `α*C t≤G t` для всех `t` следует `C t≤γ*Dbar/α`.

## Hagi/Growth/GammaDeficit.lean
- `gamma_min_for_target`: при `α,γ,Cstar>0`, верхнем gain-законе, `D≤Dbar`, gate и существовании момента достижения `Cstar≤C t` необходимо `α*Cstar≤γ*Dbar`.
- `gamma_deficit_no_takeoff`: если вместо этого `γ*Dbar<α*Cstar`, то для любого `T` найдётся `t≥T`, в котором сохраняется `C t≤γ*Dbar/α`.

## Hagi/Growth/Grow.lean
- `newBound`: точно `(N*M+c)/(N+1)=M−certifiedGain N M c`; `certifiedGain_positive` при `c<M` даёт положительный прирост и строго меньшую новую границу.
- `grow_epsilon_stop`: если `cstar≤c` и уже `certifiedGain N M cstar<ε`, то и `certifiedGain N M c<ε`.
- `pl_stop_certificate`: при `mu>0` и посылке `h_emp_pl : mu*(Lw−Lstar)≤gnorm²/2` следует `Lw−Lstar≤gnorm²/(2*mu)`.

## Hagi/Growth/IntegrationOrder.lean
- `sum_perm_invariant`: сумма конечного семейства выигрышей инвариантна относительно любой перестановки.
- `negative_expert_hurts_any_order`: если `g i<0`, полная сумма строго меньше суммы без `i`; `positive_selection_dominates` доказывает то же улучшение для любого `s`, содержащего `i`.

## Hagi/Growth/NoiseDisentangle.lean
- `orthogonal_noise_averaging`: для ненулевого `N`, попарно ортогональных `n i` с `‖n i‖²=σ²` среднее имеет квадрат нормы ровно `σ²/N`.
- `disagreement_convergence_floor`: при `0≤κ<1`, `σ≥0`, `Dseq 0≤D₀` и `Dseq(t+1)≤κDseq t+σ²/N` доказано `Dseq t≤κ^t D₀+(σ²/N)*(1−κ^t)/(1−κ)`.
- `fiber_merge_denoise`: residual ошибки равен `avgVec n−n i`, а его квадрат нормы точно равен `σ²*(1−1/N)` при тех же предположениях ортогональности.

## Hagi/Growth/PlasticityLedger.lean
- `kl_le_log_card`: для `IsProbs P`, строго положительных `P i v` и `famMix P v` каждое `KL(P i‖famMix P)≤log(card I)`.
- `radius_le_log_card`: при дополнительном `card I>0` радиус `plasticityRadius P≤card I*log(card I)`.
- `radius_zero_of_eq`: если все `P i` совпадают и положительны, радиус равен нулю.

## Hagi/Research/RecursiveSelfDevelopment.lean
- `opportunity_renewal`: из `ρD+βC−ξ≤D'` и `(1−ρ)D+δ_O≤βC−ξ` следует `D+δ_O≤D'`; `recursive_self_development` при `C≤C'`, `D≥0`, `δ_O>0` дополнительно даёт `D'>0`.
- `multiplicative_growth`: из `C(t+1)≥C t*exp(αS t−eps t)` для всех `t` следует `C0*exp(α*Σ_{t<T}S t−Σeps)≤C T`.
- `closed_loop_conditional_growth`: для продуктовой вероятности, `Y i v∈[0,1]`, `SuccessFloor`, `n>0`, `0<δ<1`, `C0≥0`, `eps t≥0`, `α≥0` и заданного шага `C` вероятность импликации «нижняя сумма успехов → экспоненциальная нижняя граница `C n`» не меньше `1−δ`; это не безусловное утверждение роста.

## Hagi/Research/RoundViability.lean
- `round_exhausted`: при `devEnergy dev=0` и `GainOp` доказаны `ρD−ξ≤D'` и `η*devEnergy dev=0`; `cycle_criterion` — импликативная форма.
- `round_viable`: при точном шаге `C'=C+γD`, `GainOp`, `γ*k≤ρ`, конусе, пороге на `(η_p*η_s)*devEnergy dev` и `devEnergy dev>0` следует `k*C'≤D'`.

## Hagi/Research/RsiCriterion.lean
- `rsi_step_growth`: из `ρD t+βC t−ξ t≤D(t+1)` и строгого `ξ t+(1−ρ)D t<βC t` следует `D t<D(t+1)`.
- `rsi_cone_criterion`: при `γ>0`, `C t>0`, `ρ≤1`, `D t≤α/γ*C t` и `(1−ρ)*α+γ*ξ t/C t<β*γ` получается тот же строгий рост `D`.

## Hagi/Growth/Saturation.lean
- `saturation_limit`: при `0<σ≤1` и нижнем PL-шаге для любого `ε>0` найдётся `T`, после которого `Cstar−ε≤C t`.
- `pl_gap_geometric_lo`: при `σ≤1`, верхнем PL-шаге и `C0≤Cstar` доказано `(1−σ)^t*(Cstar−C0)≤Cstar−C t`.
- `geometric_band_with_saturation`: при `γ,k>0`, `σ≤1`, точном cone-шаге, обеих PL-оценках, `ConeRatio` и `C0≤Cstar` доказана двусторонняя полоса `C0*(1+γ*k)^T≤C T≤Cstar−(1−σ)^T*(Cstar−C0)`.

## Hagi/Research/SeedOnly.lean
- `cycle_decay_mono`: при `s≥0`, `F>0`, `0<k<F+s` новое `F*(1−k/(F+s))` строго меньше `F` и неотрицательно; `cycle_decay_ratio` даёт точное отношение соседних приростов.
- `channel_switch`: при положительных `F,k,s,b,Cm,Cr` и `√F*(k*Cr)<b*Cm*s` индекс rank-канала строго больше movement-индекса.
- `seed_only_disp_bound`: при посылках `h_emp_lip`, `h_emp_disp_step`, `a,s≥0` и `dispP 0=0` доказано `dispL t≤Lam²*s*Σ_{i<t}a^i`.

## Hagi/Growth/SelfDevelopment.lean
- `self_development_find`: при наличии безопасного `a₀` с `G a₀>0` существует безопасный `a'` с `0<G a'` и `G a₀≤G a'`.
- `certified_gain_select`: если `|Ghat a−g a|≤eps` для всех `a` и `3*eps<g a₀`, найденный безопасный кандидат имеет `g a'>0` и `g a₀−2eps≤g a'`.
- `search_cost_bound`: сумма постоянных стоимостей измерений по `safeCandidates` равна `card*cMeas`; речь о математической сумме, а не о физическом времени.

## Hagi/Growth/StateBinding.lean
- `capability_geometric_growth_state`: при `0<α`, `0<γ`, `0≤ρ`, положительной начальной capability, начальном конусе, полевых законах шага, gain- и frontier-динамики, капе и пороге на `β` доказано `(S 0).capability*(1+α)^T≤(S T).capability`.
- `candidate_completeness_find`: из `0≤eps`, `CandidateComplete gen G safe eps`, безопасного `a₀` и `eps<G a₀` следует существование сгенерированного безопасного `a'` с `G a'>0` и `G a₀−eps≤G a'`.
- `usableFrontier_renewal`: из ingest-неравенства для dataField и оценки `β*capability−ξ≤r` выводится требуемая frontier-динамика.

## Hagi/Growth/Takeoff.lean
- `elasticity_chain`: если `(1+e t)*x t≤x(t+1)` и `1+e t>0` на `range T`, то `x0*∏_{t<T}(1+e t)≤x T`.
- `cone_ratio_geometric_growth`: при `γ,k>0`, шаге `C(t+1)=C t+γD t` и глобальном `ConeRatio C D k` доказано `C0*(1+γ*k)^T≤C T`.
- `frontier_decay_no_growth`: при `ρ≥0` и `D(t+1)≤ρD t` получается `D T≤ρ^T*D0`; это верхняя оценка затухания frontier, а не самостоятельный вывод отсутствия всякого роста capability.

## Hagi/Growth/Thermostat.lean
- `thermostat_stop`: при `0<α<1`, `T0,δ>0`, `0<θ<1` и `t≥⌈log(δ/(T0*log(1/θ)))/log α⌉` доказано `exp(−δ/(T0*α^t))≤θ`.
- `certified_state_excess_tendsto`: для конечного непустого `V`, глобального минимизатора `E` с энергетическим зазором `δ>0` и верхней границей `Δ` разность средней энергии Гиббса и свободной энергии при охлаждении `T0*α^t` стремится к нулю.

## Hagi/Information/Capacity.lean
- `separated_needs_capacity`: если каждая задача из `SepSeparated good tasks` допускает подходящий ответ через некоторое состояние `S`, то `tasks.card≤card S`.
- `router_capacity_bound`: в аналогичной модели с `encode : A→Q` и `card Q≤2^B` получается `tasks.card≤2^B`. Отдельная `bits_floor` доказывает лишь неотрицательность `logb 2 (card S)` для непустого конечного `S`, а не оценку взаимной информации.
- `recoverable_avg`: при `N>0` и `0<devEnergyF dev` существует `k`, для которого `devEnergyF dev/N≤dev k ⬝ᵥ dev k`.

## Hagi/Math/Info/InfoCore.lean (moved from Hagi/Prelude/, C348)
- `entropy_le_diagonal`: для положительно полуопределённой `A` энтропия не превосходит `Σᵢ negMulLog(Re(A i i))`; `concaveOn_entropy` доказывает вогнутость энтропии на PSD-состояниях.
- `discrete_fannes_coupling`: для вероятностных `p,q` на непустом конечном `ι` и посылки hbridge, отождествляющей энтропию неотрицательной диагонали с `shannon`, доказано `shannon p−shannon q≤tvHalf*log(card ι)+(1+tvHalf)*binEntropy(tvHalf/(1+tvHalf))`.
- Введены конечные `klDef`, `ceDef`, `entDef`, `tvDef` и `softDef`. При `p v ≠ 0` тождество `klDef_eq_ceDef_sub` выражает KL как `ceDef q p - ceDef q q`, а `ceDef_self` даёт `ceDef q q = entDef q`.

## Hagi/Learning/FOOF.lean
- `foof_normal_eq`: при обратимости `regCov X lam` определённый `foofW V X lam` удовлетворяет `foofW*regCov=V*Xᵀ`.
- `foof_step_identity`: при той же обратимости точно `foofW−W0=(V−W0*X)*Xᵀ*regCov⁻¹−lam • (W0*regCov⁻¹)`. Второе слагаемое является частью доказанного тождества и не опускается.
- `regCov_posDef`: при `lam>0` матрица `XXᵀ+lam*I` строго положительно определена; `regCov_transpose` подтверждает симметричность.

## Hagi/Learning/HRCN.lean
- `domainTerm_gauge_shift`: при ненулевом знаменателе сдвиг значений `vs i` на `ws i • b` меняет доменный вклад ровно на `charProjR w b`.
- `hrcn_cross_talk_zero`: для `w≠u` проекция такого изменения вклада домена `w` на характер `u` равна нулю при том же условии ненулевого знаменателя.

## Hagi/Learning/HadamardProjectors.lean
- `charProjR_idem`: `charProjR w (charProjR w v)=charProjR w v`.
- `charProjR_orthog`: при `w≠u` выполнено `charProjR w (charProjR u v)=0`; `charProjR_add` отдельно подтверждает аддитивность проектора.
- `charProjR_cross_zero`: проекции на разные характеры ортогональны относительно скалярного произведения `⬝ᵥ`; `charProjR_norm_sq` вычисляет квадрат нормы проекции через `(charRowR w ⬝ᵥ v)²/2^k`.

## Hagi/Learning/RCDL.lean
- `dual_apply`: для `dualW W0 xs vs` доказана поточечная формула `(W0*q)i+Σ_t dotProduct(xs t)q*vs t i`.
- `gauge_shift`: при ненулевом знаменателе замена `vs i` на `vs i+ws i • b` даёт `weightedSoftmax … q = weightedSoftmax … vs q + b`; выход сдвигается на `b`, а не остаётся буквально инвариантным.
- `gauge_exists`: для `g≠0` и `eps>0` существует `b`, для которого `dotProduct g (s+b)≥eps`.

## Hagi/Learning/SpectralBudget.lean
- `spectral_budget`: если для каждого `w` квадрат доменной ошибки не превосходит `delta²*‖charProjR w v‖²`, `delta≥0`, то `‖v−Q‖²≤delta²*‖v‖²` в форме скалярного произведения `⬝ᵥ`.
- `zero_energy_domain_free`: из нулевой доменной энергии следует, что любой `e` с `e⬝ᵥe≤0` равен нулю; `charProjR_sub` отдельно доказывает линейность по вычитанию.

## Hagi/Learning/TernaryPert.lean
- `frob_submul`: для конечной вещественной матрицы `E` выходная норма ограничена `√(frobSq E)*eunorm x`; основа — `cs_dotProduct`.
- `ternary_layer_pert`: если `|QR i j−R i j|≤1/2` покомпонентно, ошибка выхода ограничена `√(m*r*(1/2)^2)*eunorm x`.
- `lip_composition`: при `L≥0` и `L`-липшицевых слоях композиция имеет оценку `L^length` для нормы разности выходов.

## Hagi/Learning/ToyTrajectory.lean
- `honest_step_cert`: при `0<eta<2`, `cost≤s.budget` и `lossS a s>0` существуют положительный drop и соответствующий `StepCertT`.
- `traj_energy_explicit`: после `T` шагов энергия равна `(1−eta)^(2*T)*lossS a s`.
- `traj_total_descent`: при `lossS a s>0` и `(1−eta)^(2*T)<1` итоговое уменьшение энергии строго положительно; `budget_telescope` отдельно даёт точный расход cost за сертифицированный шаг.

## Hagi/Learning/TrainingTransition.lean
- `taskStep_identity`: энергия после шага равна `taskEnergy S−(2η−T*η²)/2*Σ_j taskGrad S j²`.
- `taskStep_energy_descent`: при `0<eta`, `T*eta<2` и ненулевой сумме квадратов градиентов суммарная энергия строго убывает.
- `quality_changes_with_weights`: в однозадачном случае при `0<eta<2` и ненулевом градиенте `taskQual` также строго уменьшается; для нескольких задач такой покомпонентный вывод здесь не делается.

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
- `cappedChunks capacity width xs` при fit `xs.length ≤ capacity * width`
  разбивает список по `List.replicate capacity width` и удаляет только пустые
  padding-чанки; короткий последний chunk допустим. Из
  `hsuccess : cappedChunks capacity width xs = some chunks` теоремы
  `length_cappedChunks_le`, `flatten_cappedChunks` и
  `ne_nil_of_mem_cappedChunks` дают соответственно `chunks.length ≤ capacity`,
  `chunks.flatten = xs` и непустоту каждого члена результата.

## Hagi/Model/AlignmentRisk.lean
- Для непустого конечного `V` и строго положительных нормированных
  `p q : V → ℝ`, `0 ≤ c` и
  односторонней посылки `risk ≤ c * ((1/2) * ∑ v, |p v - q v|)`
  `kl_budget_risk_bound` даёт `risk ≤ c * √klDef q p`.
- `kl_penalty_certifies_risk`: если дополнительно `klDef q p ≤ delta`,
  то `risk ≤ c * √delta`; при `klDef q p ≤ 0`
  `rlhf_zero_drift_zero_risk` даёт `risk ≤ 0`.

## Hagi/Model/Attention.lean
- `gqa_kv_ratio`: при `1 ≤ T`, `1 ≤ d`, `n_kv < n_h` отношение
  стоимостей KV-кэшей равно `(n_kv : ℝ) / n_h`, а `gqa_kv_lt` делает его
  строго меньшим единицы. `mla_cache_saving` даёт
  `cacheLatent n dc < cacheFull n d` при `0 < n`, `dc < d`.
- `mod_layer_cost_lt` доказывает экономию MoD-слоя при `k < n`,
  `1 ≤ d`; `mod_stack_saving` переносит строго положительную экономию на
  стек из `L ≥ 1` слоёв и даёт точную `L`-кратность послойной экономии.
- `flash_io_lt`: при `1 ≤ d`, `d * d < M`, `1 ≤ N` стоимость IO
  FlashAttention строго меньше `stdIO N d`. `swa_cost_lt` даёт
  `swaCost n w < denseAttnCost n` при `2 * w + 1 < n`.

## Hagi/Model/AttentionSpend.lean
- `hybrid_ratio`: при положительных `T n n_h d`
  `hybridAttnCost T w n_kv d / denseAttnCost T n n_h d =
  ((2*w+1 : ℝ)/n) * ((n_kv : ℝ)/n_h)`.
  При `2*w+1 < n` и `n_kv < n_h` отношение строго меньше единицы.
- `fullStack_ratio` добавляет MoD-фактор: относительная стоимость равна
  `(k/n) * ((2*w+1)/n) * (n_kv/n_h)`; `fullStack_lt` даёт строгую
  экономию при `k < n`, `2*w+1 < n`, `n_kv < n_h` и положительных `L d`.

## Hagi/Model/BYOL.lean
- Для `bl u v = 1 - cosS u v` при посылке `CSCarrier u v`, то есть
  `|cosS u v| ≤ 1`, `bl_bounds` даёт `0 ≤ bl u v ≤ 2`;
  `bl_zero_at_perfect` превращает `cosS u v = 1` в `bl u v = 0`.
- `bl_anti` — строгое убывание `1-c` по `c` при `c₂ ≤ 1`.
  `cos_scale_inv`: при `s ≠ 0`, `t ≠ 0`, `0 < s*t`, `qnorm u ≠ 0`,
  `qnorm v ≠ 0` масштабирование обоих аргументов не меняет `cosS`;
  дисперсионного антиколлапс-члена в это тождество не входит.

## Hagi/Model/BatchCEDescent.lean
- `batchMeanDirection_eq_neg_meanResidualTranspose` отождествляет среднее
  собственных отрицательных направлений с `−meanResidualTranspose X θ y`;
  `batchMeanAction_common` даёт среднее действие `−batchAlignment X θ y`.
  При `0 < batchRangeSquare X θ y` `batchLoss_safeStep_lt` строго снижает
  арифметическое среднее CE на заданном конечном батче.
- `empty_batch_convention`: на пустом батче потеря, направление,
  согласованность, квадрат диапазона и безопасный шаг равны нулю, а
  `batchNextParameters = θ`; строгий прогресс для этой ветви не
  утверждается.
- `batchGradientMinimizer_spec`: на непустом батче выбранная точка
  принадлежит выпуклой оболочке непреобразованных градиентов остатка и
  имеет минимальную норму. При `batchGradientMinimizer X θ y ≠ 0`
  `ceOneHot_batchCommonNextParameters_lt` даёт строгий спуск CE для
  каждого примера батча.

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
- `joint_raw_upper_confidence_delta`: на непустом конечном `V`, для
  фиксированных признаков и `IsProbSys p`, при `0 < n`, `0 < eps`,
  `0 < delta < 1` и
  `ceBound X^2 * log ((61965^G)/delta) / (2*eps^2) ≤ n`,
  с вероятностью не менее `1-delta` одновременно для всех кодов масштаба
  генеральный исходный CE ≤ эмпирический исходный CE + `eps`.
- `codebook_raw_selected_population_mean_gap_lower_confidence_delta` даёт
  для зависящих от выборки `baseline candidate : (Fin n → V) → JointCode G`
  нижнюю доверительную оценку генеральной разности через эмпирическую
  разность минус `2*eps`. Достаточный бюджет содержит полный
  множитель `2*61965^G` в логарифме; условия `0 < n eps delta` сохранены.

- `normalizedCE_mem_unit`: для непустого конечного `V` нормированный

## Hagi/Model/CECoupledShortcut.lean
- `shortcutScales_eq_fast_of_coupledPenalty_eq_zero`: полный кандидат
  fast с нулевым `coupledPenalty` возвращается без изменений; при
  ненулевом штрафе используется точный `selectedCoupledScales`.
- `shortcutScales_score_eq_selectedCoupled`: в обеих ветвях значение
  `coupledPenalty` равно значению на полном связанном минимизаторе; это
  равенство оценок, а не равенство выбранных кодов или исходного CE.
- `ceOneHot_joint_shortcut_le_coupledPenalty` для непустого конечного `V`
  ограничивает фактический CE
  обновления исходным CE плюс связанный штраф. Если штраф кандидата
  равен нулю, `ceOneHot_joint_shortcut_eq_of_coupledPenalty_eq_zero`
  доказывает точное равенство совместного CE и исходного CE.

## Hagi/Model/CEDescent.lean
- Для конечного непустого `V` и любого `0 ≤ η`
  `ceOneHot_next_le` доказывает
  `CE(next η) ≤ CE θ - η*ceAlignment X θ t +
  (η*ceStepRange X θ t)^2/8`; направление —
  отрицательный транспонированный softmax-остаток.
- При `0 < ceStepRange X θ t` выбранный шаг даёт точный остаток
  мажоранты `2*ceAlignment^2/ceStepRange^2` (`ceMajorizer_safeStep_eq`), а
  `ceOneHot_safeStep_le_residual` переносит эту верхнюю оценку на исходный CE.
- `ceOneHot_safeStep_lt` из положительного диапазона получает строгое
  одношаговое снижение CE. При нулевом диапазоне безопасный шаг равен нулю;
  глобальная минимизация и сходимость итерации не утверждаются.

## Hagi/Model/CEExpansion.lean
- `ceLogits_expandedParameters`: новый логит равен
  `ceLogits X θ v + Z v * gamma`; поэтому при `gamma = 0`
  `ceOneHot_expandedParameters_zero` сохраняет CE при произвольной новой
  координате `Z`.
- `hasFDerivAt_ceLogits_expandedParameters` даёт точный аффинный якобиан
  `expandedReadoutJacobian Z`, действующий как `gamma • Z`.
- Для непустого конечного `V` и признака остатка
  `Z v = oneHot t v - softDef (ceLogits X θ) v`
  `ceOneHot_expandedParameters_residual_step_le` доказывает
  `CE_expanded(Σ Z v^2) ≤ CE_original - (Σ Z v^2)^2/2`.

## Hagi/Model/CEGradient.lean
- На непустом конечном `V` и `EuclideanSpace ℝ (Fin d)`
  `fderiv_ceOneHot_mulVec` вычисляет направленную производную CE как
  `∑ v, (softDef (X*ᵥθ) v - oneHot t v) * (X*ᵥh) v`, то есть действие
  транспонированного признакового остатка.
- `fderiv_ceOneHot_comp_apply`: для любого нормированного пространства `E`
  и `HasFDerivAt g g' θ` производная композиции CE равна
  `∑ v, (softDef (g θ) v - oneHot t v) * (g' h) v`.
- `differentiableAt_ceOneHot_comp` доказывает дифференцируемость такой
  композиции из `DifferentiableAt ℝ g θ`.

## Hagi/Model/CEGroupedScale.lean
- Для эквивалентности `(Fin G × Fin 5) ≃ Fin (5*G)` и непустого `V`
  `ceOneHot_joint_le_blockPenalties` доказывает
  `CE(jointParameters e w scales) ≤ CE w + ∑ g, blockPenalty e X w g (scales g)`.
- `selectedGroupScales_spec`: каждый избранный код минимизирует
  `blockPenalty` среди полного конечного семейства из 255 кодов.
  При `2 ≤ G` независимый локальный поиск использует строго меньше
  математических вычислений оценки, чем полное число совместных кандидатов.
- При `0 < ceStepRange X θ t` и существовании назначения с суммой
  блочных штрафов меньше `2*ceAlignment^2/ceStepRange^2`
  `selectedGroupScales_strict_descent_of_exists` даёт строгое снижение
  фактического совместного CE.

- `scaleEvaluationCount_eq = 255`; `selectedScale_spec` выбирает код,

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
- `ceOneHot_joint_le_coupledPenalty` для непустого конечного `V`
  ограничивает фактический CE
  обновления исходным CE плюс связанный штраф; при нулевом штрафе
  `ceLogits_joint_eq_of_coupledPenalty_eq_zero` даёт поточечное равенство
  логитов.
- При `0 < ceStepRange` и существовании полного назначения со штрафом
  меньше `2*ceAlignment^2/ceStepRange^2`
  `selectedCoupledScales_strict_descent_of_exists` доказывает строгий
  спуск CE.

- (C453) `ScaleChoice`: общий интерфейс сертифицированного выбора из

## Hagi/Model/CEMarkovConfidence.lean
- `raw_bank_freedman_confidence`: на истории пар «банк кодов — метка» с
  непустым конечным типом меток, при `0 < r`, `0 ≤ V`, вероятность того, что
  условная граница дисперсии `V` влечёт одновременное
  `|historyAdditive ...| < r` для всех `m` моделей, не менее
  `1 - 2*m*exp(-r^2/(4*(V + ceBound X*r)))`.
- `raw_bank_selected_conditional_ce_gap_pos_of_good`: на этом «хорошем»
  событии, при границах дисперсии для исходного варианта `b` и выбранного
  `σ ω` и наблюдаемой разности исходного CE `> 2*r`, условная средняя
  разность «исходный вариант минус выбранный» строго положительна.
- `raw_bank_freedman_maximal_confidence`: для исходной (не нормированной)
  CE, вычисленной по фиксированному decodeJoint на парах «банк — метка», пусть
  `g = F − μ`, где `μ` — conditional PMF mean следующей CE, а `v` — точный
  conditional second moment `g`. При `0 < r`, `0 ≤ V`, нижняя граница
  `1 - 2*m*(T+1)*exp(-r^2/(4*(V + ceBound X*r)))` относится к индикатору
  одновременного события: для каждого `i : Fin m` и каждого префикса `j ≤ T`,
  если `historyCounter v T j ≤ V`, то `|historyAdditive g T j| < r`.
  Банк объединяется через Freedman и union bound; времена не ограничены
  одним конечным `T T` внутри события, хотя сам горизонт конечен.

## Hagi/Model/CEPadding.lean
- Для любого `d` `d ≤ paddedDimension d`,
  `paddedLogicalBits d = 16*((d+4)/5)`; `unpadVector (padVector w) = w`.
- `ceOneHot_padVector` сохраняет исходный CE для каждой метки при нулевом
  дополнении, а `ceLogits_unpadVector` отождествляет логиты ограничения
  произвольного дополненного вектора с исходными признаками.
- `ceOneHot_unpad_jointParameters` переносит совместный CE между
  дополненным и исходным носителями; `normalizedCE_unpad_mem_unit`
  доказывает принадлежность соответствующего отношения исходного CE к
  `ceBound X` интервалу `[0,1]` для непустого `V`.

## Hagi/Model/CEQuantized.lean
- На непустом конечном `V` `ceOneHot_le_of_abs_sub_le`: если `∀ v, |z v-y v| ≤ r`, то
  `ceOneHot t z ≤ ceOneHot t y + 2*r`.
- Наблюдаемый штраф ограничивает CE при любом вещественном масштабе;
  структурный штраф — при `0 < s`. Их минимум
  `ceQuantPenalty` также ограничивает фактический CE тритарного шага
  (`ceOneHot_ternary_le_ceQuantPenalty`).
- При `0 < s`, `0 < ceStepRange X θ t` и
  `ceQuantPenalty safeSuccessor s < 2*ceAlignment^2/ceStepRange^2`
  `ceOneHot_ternary_safeStep_lt` доказывает строгий спуск фактического CE.

## Hagi/Model/CEStorageBound.lean
- `card_jointCode_le_payload`: `card (JointCode G) ≤ 2^(groupPayloadBits G)`;
  `log_card_jointCode_le_payload` даёт ту же границу для `log₂ card`.
- `selectedPacked_ce_and_codebook_bits` для непустого конечного `V`
  объединяет корректное декодирование
  каждого блока, точное совместное кодирование/декодирование, оценку
  исходного CE через сумму блочных штрафов и логарифмическую границу
  логической ширины кодовой книги;
  физическая память не входит в формулировку.

## Hagi/Model/CertifiedTransition.lean
- `certifiedTransition_of_advance` при `0 ≤ u.gap`, `0 ≤ u.sp.eta` и
  `u.sp.kappa*u.sp.s < 2*u.eff.growGain` связывает сертификат с конкретной
  парой `S : GrowthState X` и `advance S u`.
- Семейство таких сертификатов телескопирует точные суммы измеренного
  прироста, защищённого риска и стоимости (`certified_trajectory_capability`,
  `certified_trajectory_risk`, `certified_trajectory_budget`), а при законах
  стадий порождает `CycleCertificate`.
- `ctv3_sound`: из `CertifiedTransitionV3 S S' u riskLim` следуют
  `S' = advance S u`, положительный `verify.decrease`, суммарные границы
  риска и бюджета и строгое `S'.energy < S.energy`.

## Hagi/Model/ComputeOptimal.lean
- При `0 < A B C` `chinchilla_optimum` задаёт
  `Nstar = √(A*C/B) > 0` и доказывает
  `chinchillaLoss A B C Nstar = 2*√(A*B/C)`, а также глобальную нижнюю
  границу этого значения для `chinchillaLoss` при всех `0 < N`.

## Hagi/Model/ConsolidationMirror.lean
- На непустом конечном `V`, при `0 < T`, строго положительном нормированном
  `ρ₀`, `grow_gain_from_mirror` равен разность потерь приора и шага Гиббса
  `T*(KL(ρ₀‖mirrorStep) + KL(mirrorStep‖ρ₀))`.
- `grow_gain_nonneg` доказывает неотрицательность этой разности;
  `core_premises_grow_operational` при `∑ρ₀*ℓ ≤ energy` превращает её в
  оценку энергии эксперта Гиббса через `energy` минус симметризованную KL.

## Hagi/Model/CycleCertificate.lean
- `cycle_certificate_composition`: один `CycleCertificate T C Φ B` даёт
  `C T = C 0 + Σ gain`,
  `Φ T ≤ Φ 0 - Σ drop + Σ risk` и `B T = B 0 - Σ spend`.
- Для `growSeq` на `GrowthState ℝ`, при `0 ≤ μ`, `0 ≤ 1+α`, `0 ≤ α` и
  неотрицательной начальной способности `honest_trajectory_global`
  доказывает точный рекуррентный рост способности, невозрастание энергии и
  точное вычитание суммы `μ*C_t` из бюджета.

## Hagi/Model/EnergyReasoning/Pseudolikelihood.lean
- Track E1: псевдоправдоподобие как локальная условная CE на каноническом
  Prelude-стержне. Логиты `conditionalLogit B K y i a = −pairwiseEnergy B K
  (update y i a)` (CRAM-знак), условные `conditionalDist = softDef` от них,
  цель `pseudolikelihoodObjective = (Σ ceOneHot (y i) z_i)/|ι|`.
- `pseudolikelihood_eq_conditional_ce` — (E1 MAIN) J равна среднему
  `ceDef (Pi.single (y i) 1) (softDef z_i)` почленно через
  `Hagi.Core.ceOneHot_eq_ceDef_pi_single`: machinery CEDescent применим
  по построению, новой CE-теории нет.
- `pseudolikelihood_nonneg` — 0 ≤ J (каждый локальный член
  lse z − z(y i) ≥ 0; |ι| > 0).

## Hagi/Model/DiffAttention.lean
- `sm_shift`: `sm (fun j => x j + c) i = sm x i`; общий аддитивный сдвиг
  логитов не меняет softmax-веса.
- `diff_range`: для `diffW` и `0 ≤ lam` доказано
  `-lam ≤ diffW x y lam i ≤ 1`.

## Hagi/Model/DistillCert.lean
- Для `DistillCert` на `Fin n → ℝ`, с `0 < delta`, `0 ≤ lip`,
  `0 ≤ dist2 ≤ dbound` и `dist2^2 = ∑(teacher-student)^2`,
  `quant_L2` доказывает
  `∑(quantStudent-student)^2 ≤ n*(delta/2)^2`.
- `consolidation_bound`: если для всех `x y`
  `|L x-L y| ≤ lip*∑(x-y)^2`, то
  `|L quantStudent-L teacher| ≤
  lip*(2*n*(delta/2)^2 + 2*dbound^2)`. Это квадратичная L²-форма,
  а не линейная оценка через `√n`.

## Hagi/Model/GDNBridge.lean
- `gdn_onehot_interp`: one-hot Gated DeltaNet-обновление равно
  `colInterp S i v g β`; записываемый столбец интерполируется между
  затухшим состоянием и `v` с коэффициентом `β`.
- `gdn_ram_roundtrip` доказывает, что чтение строки `i` после
  `ramWrite S i v` возвращает ровно `v`.
- `colUpdate_inert` сохраняет все адреса `b ≠ i`;
  `colUpdate_waw` отождествляет две записи в один адрес с последней.

## Hagi/Model/RamProtocol.lean
- C303 (E6 — RAM induction: протокол store/load + нормализация
  заикания): `ramStore`/`ramLoad` — протокольный API поверх
  GDNRAM-носителя; `ram_store_load_roundtrip` — store→load по
  тому же адресу возвращает значение в точности (упаковка
  идеального one-hot roundtrip), `ram_store_isolation` — load по
  другому адресу не затронут записью (one-hot независимость
  слотов, режим lag-1).
- Stutter-ядро Python-чанкинера: `stutterNorm` (foldr-свёртка,
  схлопывание подряд идущих дубликатов) —
  `stutterNorm_idempotent` (norm ∘ norm = norm),
  `stutterNorm_length_le` (не удлиняет),
  `stutterNorm_head?`/`stutterNorm_getLast?` (первый/последний
  сохраняются).
- Мост `ram_load_stutter_head`: первое чтение RAM по заикающейся
  последовательности адресов = первому чтению по
  нормализованной (без промежуточных записей повторы адреса не
  меняют чтение). Полная эквивалентность потоков (чанк на серию
  повторов) — НЕ заявлена, следующая ступень E6.

## Hagi/Model/GatedCEDescent.lean
- Для непустого конечного `V` производная CE вдоль
  `gatedDirection X θ t` в нуле равна `-gatedAlignment X θ t`
  (`hasDerivAt_gatedLineObjective`).
- При `0 < gatedAlignment X θ t`
  `exists_gated_ceOneHot_descent` даёт существование `η > 0` со строгим
  локальным снижением фактического CE управляемой модели; явный размер
  шага в этой теореме не вычисляется.
- `hasFDerivAt_gatedForward` задаёт точный якобиан обучаемого
  `gatedForward`, а `fderiv_ceOneHot_gatedForward` выражает производную CE
  как сумму произведений компонент softmax-остатка на
  `gatedAction X θ D v`.

## Hagi/Model/Generative.lean
- DDPM: `alphaBar_succ` задаёт рекуррентность произведения. При
  `0 ≤ β i ≤ 1` `alphaBar_mono` доказывает невозрастание, а если
  `0 < b < 1`, `b ≤ β i ≤ 1`, то `alphaBar_exp_bound` даёт
  `alphaBar β t ≤ (1-b)^t`.
- `ddpm_recover`: при `0 < ab`, `ab < 1` и равенстве прямого процесса
  для `xt` идеальный предиктор шума восстанавливает `x0` точно.
- FlowMatching: прямой путь имеет концы `x0`, `x1`, остаётся между ними
  при `0 ≤ t ≤ 1`, `x0 ≤ x1`, а `flow_const_velocity` доказывает
  `HasDerivAt (flowPath x0 x1) (x1-x0) t`.

## Hagi/Model/Grokfast.lean
- `decompose`: `gLow + gHigh = g`; `amp_recompose` переписывает усиленное
  направление как `(1+lam)*gLow + gHigh`.
- `const_grad_fix`: на постоянном сигнале `gLow = g₀`, `gHigh = 0`.
- `amp_inner_ge`: при `0 ≤ lam` и `0 ≤ g*gl`
  `g*(g+lam*gl) ≥ g*g`.

## Hagi/Model/HNet.lean
- `hier_seq_shorten`: при `1 < r`, `0 < T` выполнено
  `0 < T/r < T`; `hier_attn_saving` даёт
  `c*(T/r)^2 = c*T^2/r^2`, а `hier_attn_saving_lt` при `0 < c` делает
  экономию строгой.
- `hnet_cost_floor`: для вещественных `a b T r > 0`
  `3*((a*T*r/2)*(a*T*r/2)*(b*T^2/r^2))^((3:ℝ)⁻¹) ≤
  a*T*r + b*T^2/r^2`.
- Оптимум задан на вещественных коэффициентах:
  `hnetOptRatio a b T = (2*b*T/a)^((3:ℝ)⁻¹)`; при `a b T > 0` он
  положителен и удовлетворяет `a*T*(hnetOptRatio a b T)^3 = 2*b*T^2`.

## Hagi/Model/HNet2.lean
- `hier2_compression_product`: при `r1 r2 ≠ 0`
  `hier2Positions T r1 r2 = T/r1/r2`; при `0 ≤ T`, `1 ≤ r1`, `1 ≤ r2`
  `hier2_positions_le` даёт неравенство `hier2Positions ≤ T`.
- `hier2_beats_dense`: при `0 ≤ cm`, `0 ≤ T`, `1 ≤ r1`, `1 ≤ r2` и
  явной посылке
  `cm*(T^2/(r1*r2)) + c1*T + c2*T/r1 < cm*T^2`
  двухстадийная стоимость строго меньше `denseCost cm T`.

## Hagi/Model/HypothesisCompetition.lean
- При `0 < K`, `T ≠ 0` `dhcWeights_pos` и `dhcWeights_sum_one`
  доказывают строгую положительность и нормировку DHC-весов;
  `dhcWeights_mono` при `0 < T` сохраняет порядок активаций.
  `dhcWeights_ent_le_logK` при `T ≠ 0` ограничивает энтропию `log K`.
- `dhcStep_suppressed`: при `0 ≤ kappa`, `0 ≤ C`, `T ≠ 0`, `0 < K`
  шаг не превосходит `(1-rho)*a i + rho*s i`.
- `dhcStep_abs_bound`: при `0 ≤ rho ≤ 1`, `0 ≤ kappa`, `0 ≤ C`,
  `T ≠ 0`, `0 < K`
  `|a' i| ≤ (1-rho)*|a i| + rho*|s i| + kappa*∑|C i j|`.

## Hagi/Model/Logic/VennHead.lean
- Точная нейро-символьная голова (Track B7, C242): атомы Венна как
  ReLU-нейроны `vAtom` на {−1,+1}-входах — ровно один активен
  (`vAtoms_sum_one`, `vAtoms_mem`); голова `vennHead` линейна по атомам
  с {0,1}-маской (`vennHead_mem`).
- `vennHead_exact` — 64-случайный мост: на знаковых входах голова
  вычисляет значение истинности маски `Hagi.Data.BoolVenn` (16 масок ×
  4 входа).
- `venn_pair_win`/`venn_certified` — голова испускает логит-пару
  `![f, 1−f]` (eps-зазор ровно 1), композиция с
  `Hagi.Cert.CertifiedArgmax.certified_argmax_strict` при est = v
  (нулевая ошибка): для любого ε с 2ε < 1 сертифицированный argmax-индекс
  ЕСТЬ значение истинности булевой функции.

## Hagi/Model/LabelSmoothing.lean
- При `0 ≤ ε` на непустом конечном `K` `ls_pointwise_dist` даёт точное
  равенство
  `|lsTarget q ε i-q i| = ε*|q i-1/card K|`;
  для нормированной неотрицательной `q` `ls_l1_bound` ограничивает сумму
  этих отклонений величиной `ε*card K`.
- `ls_entropy_ge`: для строго положительной нормированной `q` и
  `0 < ε < 1` доказано `lsH q ≤ lsH (lsTarget q ε)`.

## Hagi/Model/LayerNorm.lean
- `ln_scale_invariant`: для `0 < c` `lnVec (c • x) = lnVec x`.
- При `0 < n` `variance_decomp` доказывает
  `variance x = ms x - (mean x)^2`, а `ln_sum_zero` — нулевую сумму
  координат `lnVec x`.

## Hagi/Model/LogitPSV.lean
- Для непустого конечного `k` и строго положительных весов `p` с
  суммой `1`
  `logitPSV_gap_nonneg` доказывает `0 ≤ twoGap p (biasedScore base sigma ∘ eps)`.
- При нулевом разбросе `logitPSV_gap_zero_of_no_spread` даёт нулевой
  выигрыш ансамбля;
  `logitPSV_weights_frozen` доказывает равенство всех компонент
  `frozenWeights w0`.

## Hagi/Model/Losses.lean
- NT-Xent: `nt2_nonneg`, `nt2_anti`, `nt2_zero_margin` и `nt2_le_log2`
  для `nt2 m = log(1+exp(-m))` дают неотрицательность, строгое убывание
  по марже, значение `log 2` при `m=0` и верхнюю границу `log 2` при
  `0 ≤ m`.
- GradNorm: `gnBalanced` при `gnorm ≠ 0` даёт
  `gnWeight c gnorm*gnorm = c`; `gnPos` и `gnInverse` при
  `0 < c g₁ g₂`, `g₁ < g₂` доказывают положительность и строгое убывание
  весов по норме.
- `zloss_bound` при `0 < c` и `(1/c)*(log Z)^2 ≤ B` даёт
  `|log Z| ≤ √(B*c)`; `softcap_bound` при `0 < cap` ограничен
  `|softcap cap l| ≤ cap`.

## Hagi/Model/MachineBridge.lean
- `machine_param_bridge`: если `S.params = w` для
  `S : GrowthState (EuclideanSpace ℝ (Fin n))`, то параметры `advance`
  равны `jointStepE a w eta`; `0 < eta` входит в построение входных данных.
- `machine_actual_descent_n`: при `0 < eta ≤ 1`, `S.params = w`,
  `S.energy = energyE a w`, `q = ‖compressQE Delta (jointStepE a w eta) -
  jointStepE a w eta‖` и `(1-eta)*‖w-a‖*q + q^2/2 <
  eta*(2-eta)*energyE a w` машинный шаг строго снижает энергию и даёт
  двустороннюю оценку фактического спада.
- Скалярный `machine_advance_certified` при `0 < eta ≤ 1`,
  согласовании `S.energy = energy a w`, `0 < Delta` и
  `|jointStep a w eta 0-a 0| + |compressQ Delta (jointStep a w eta) 0 -
  jointStep a w eta 0|/2 ≤ kappa*s`
  ограничивает энергию после машинного шага исходной энергией минус явное
  уменьшение с квантованием.

## Hagi/Model/MambaSSM.lean
- `ssm_linear_cost_lt`: при `0 < c κ` и `κ < T`
  `c*T*κ < c*T*T`.
- `ssm_memory_const`: при `1 ≤ d`, `0 < s`, `s*d < T`
  `d*s < d*T`.
- `ssm_state_bound`: при `0 ≤ ρ < 1`, `0 ≤ B`
  `∑ i<t, ρ^i*B ≤ B/(1-ρ)`; `mamba_disc_contract` для
  `0 ≤ Delta A` даёт `exp (-(Delta*A)) ≤ 1`.

## Hagi/Model/MeasuredEffects.lean
- Для `MS`, содержащего способность, бюджет и типизированные эффекты,
  `trainStep_measured` отождествляет эффекты шага с `measure S batch`, а
  `trainStep_budget_balance` даёт `budget' + totalCost(measure) = budget`.
- `trainStep_capability_band`: при `0 ≤ S.capability`, `0 ≤ αmin ≤ αmax`
  и измеренном приросте между `αmin*C` и `αmax*C` новая способность лежит
  между `(1+αmin)*C` и `(1+αmax)*C`.
- `ofStageEffects_roundtrip`, `totalCost_ofStageEffects` и
  `totalRisk_ofStageEffects` без потерь восстанавливают раздельные
  приросты, риски и стоимости из `StageEffects`.

## Hagi/Model/MeasurementCert.lean
- Для `StepMeasurement`, чьё поле hband содержит
  `claimed ∈ [measured-delta, measured+delta]`,
  `claimed_pos_of_signal` из `delta < measured` получает `0 < claimed`.
- `claimed_ceiling` даёт `claimed ≤ measured+delta`;
  `chain_floor` суммирует нижние границы:
  `Σ measured - Σ delta ≤ Σ claimed`.

## Hagi/Model/Memory.lean
- `wt_saving`: для вещественных `m n` с `0 < m*n`
  `wtParams m n < untiedParams m n`.
- `consolidation_no_free_lunch`: если `B < cUnit*n`, то не может
  выполняться `cUnit*n ≤ B`; это бюджетное отрицание, а не измерение
  физической памяти.
- GDNRAM: `ram_read_after_write` возвращает записанное `v` точно,
  `ram_write_independent` сохраняет строки `j ≠ i`, а
  `ram_write_idem` отождествляет повторную запись того же значения.

## Hagi/Model/Mixup.lean
- `mixLabel_dist`: при `0 ≤ lam ≤ 1` и двух неотрицательных нормированных
  `y₁ y₂ : K → ℝ` смесь также неотрицательна и нормирована.
- `mix_loss_le`: для `ConvexOn ℝ S ℓ`, `s₁ s₂ ∈ S` и `0 ≤ lam ≤ 1`
  `ℓ(mixScore lam s₁ s₂) ≤ lam*ℓ s₁ + (1-lam)*ℓ s₂`.

## Hagi/Model/ModeConnectivity.lean
- Для квадратичной `energy a` на `Fin n → ℝ` и `0 ≤ lam ≤ 1`
  `linear_no_barrier` ограничивает энергию линейного пути величиной
  `max (energy a w1) (energy a w2)`.
- `linear_midpoint_bound` даёт энергию средней точки ≤ средней энергии
  концов; `swa_average_bound` при `0 < T` распространяет это на среднее
  `T` точек: энергия среднего вектора ≤ средняя энергия.

## Hagi/Model/ModelSoup.lean
- `soup_mem`: на непустом конечном `K`, при `0 ≤ w i`, `Σw=1` и
  `c ≤ x i ≤ d`
  `c ≤ soup w x ≤ d`.
- `soup_loss_le_avg`: для `ConvexOn ℝ s f` и всех `x i ∈ s`
  `f(soup w x) ≤ ∑w i*f(x i)` при тех же весах.
- `ema_invariant`: при `0 ≤ β ≤ 1` и всех наблюдениях в `[lo,hi]`
  вся EMA-траектория остаётся в `[lo,hi]`.

## Hagi/Model/ModernHopfield.lean
- `hopfield_concentration`: при `0 ≤ Delta` и разделении
  `s iStar ≥ s i + Delta` для всех `i ≠ iStar` softmax-вес лучшего
  паттерна не менее `1/(1+(K-1)*exp(-Delta))`.
- `capacity_bound_arith`: для натуральных `d K`, `2 ≤ K` и
  `2*K*log K ≤ d` доказано
  `(K : ℝ) ≤ 2^((d : ℝ)/(2*log K))`.

## Hagi/Model/MuPScaling.lean
- `muP_width_invariant`: при `0 ≤ eta`, `0 ≤ c` и строчных нормах
  `≤ c` абсолютное обновление каждого выхода не превышает
  `eta*c*√(∑x j^2)` без множителя ширины.
- `sp_grows_with_width`: для стандартного обновления верхняя граница
  содержит дополнительный `√n`; при `0 ≤ eta c` и `1 ≤ n`
  `muP_bound_le_sp_bound` сравнивает две границы напрямую.

## Hagi/Model/NeuralComputer.lean
- Для `S : NCState`, `u : NCInput` `nc_cpu_frozen` и `nc_base_frozen`
  сохраняют соответственно параметры CPU и тритарную базу.
- `nc_mem_only_via_write`: новая память либо равна `S.mem`, либо
  `u.memWrite.2`; `nc_budget_ledger` даёт точное
  `budget' = budget - u.cost`, а `nc_risk_mono` использует
  неотрицательность `u.riskSpend`.

## Hagi/Model/NonlinearCE.lean
- `ceOneHot_nonlinear_descent_le`: нелинейная лемма о спуске — при
  посылках мажоризатора Якобиана (оструктуренный остаток
  `‖f w-f θ-J(w-θ)‖ ≤ ρ*‖w-θ‖^2` на шаре `r`, диапазон `(J d) ≤ R`,
  `η*‖d‖ ≤ r`) `CE(f(θ+ηd)) ≤ CE(fθ) - η*A +
  (nonlinearCurvature R ρ ‖d‖^2 / 2)*η^2`, где составная кривизна
  `nonlinearCurvature R ρ dn = R^2/4 + 4*ρ*dn` (без отброшенных
  перекрёстных членов).
- `ceOneHot_nonlinear_safeStep_le` / `_lt`: безопасный шаг
  `nonlinearSafeStep A L = A / L` гарантирует спуск
  `CE ≤ CE - A^2/(2*L)` (строго при `0 < A`, `0 < L`); композиционный
  градиент — существующий `fderiv_ceOneHot_comp_apply`.
- Инстанциация: tanh-голова `tanhHead x = ![Real.tanh x, 0]`
  (`ρ = 2` глобально, `R = 1`, `A = 1/2`, кривизна `33/4`, шаг
  `2/33`): `ceOneHot_tanhHead_safeStep_le` / `_lt`.

## Hagi/Model/NormAct.lean
- PreNorm: `preNorm_step_bound` ограничивает шаг суммой норм;
  `preNorm_depth_bound` при `‖fs t‖ ≤ B` даёт
  `‖x_L‖ ≤ ‖x0‖ + L*B`.
- QKNorm: `qk_logit_bound` при `ms q ≠ 0`, `ms k ≠ 0` даёт
  `|rnVec q ⬝ᵥ rnVec k| ≤ n`; `qk_no_saturation` из заданной границы
  разности логитов и ненулевого знаменателя ограничивает отношение
  вероятностей величиной `exp(2*n)`.
- SwiGLU: `0 < sig z < 1`, `|swish z| ≤ |z|` и
  `|swiglu a b| ≤ |a|*|b|`.

## Hagi/Model/Perceiver.lean
- `perceiver_cost_ratio_lt`: при `1 ≤ n`, `2*m ≤ n`
  `perceiverCost n m / attnCost n < 1`.
- При `2*m < n` `perceiver_saving_pos` даёт строго положительную экономию;
  `perceiver_saving_mono` при `2*m ≤ n` показывает её неубывание при
  замене `n` на `n+1`.

## Hagi/Model/QuantizedAdvance.lean
- `advanceQ_quantized`: для `S : GrowthState X`
  `(advanceQ S u q).params = q(S.params-u.sp.eta • u.stepDir)`.
- Если `∀x, ‖q x-x‖ ≤ hDelta`, то `advanceQ_prox` ограничивает
  расстояние между параметрами квантованного и обычного `advance` величиной
  hDelta.
- `ReferenceMachine.compressQ_eq_gridQ` отождествляет машинное квантование
  с `gridQ`;   `ReferenceMachine.compressQ_prox` при `0 < Delta` даёт поточечную ошибку
  `≤ Delta/2`.

## Hagi/Model/RL.lean
- GRPO: `groupAdv_sum_zero` при `0 < n` даёт нулевую сумму, а
  `groupAdv_sq_min` доказывает оптимальность среднего как baseline. При
  `0 < sigma` и явном `∑(r-mean)^2 = sigma^2*n` `groupAdv_std_unit`
  даёт `∑A_i^2 = n` для стандартизованных преимуществ.
- RLHF: `rlhf_penalty_floor` для строго положительных нормированных
  `q p` и `0 ≤ β` доказывает, что вычитание `β*klDef q p` не увеличивает
  ожидаемую награду.
- BestOfN: `best_of_n_mean_le_sup` при `0 < n` ограничивает среднюю
  награду максимумом; GAE `gae_weight_pos` и `gae_weight_bound` при
  `0 ≤ γ*lam`, `lam ≤ 1`, `γ ≤ 1` (а для `gae_weight_bound` также
  `0 ≤ lam`) дают неотрицательные веса и
  `(1-lam)*∑(γ*lam)^i ≤ 1` при неотрицательности указанной суммы.

## Hagi/Model/RMSNorm.lean
- `rn_scale_invariant`: для `0 < c` `rnVec (c • x) = rnVec x`.
- `rn_unit_rms`: при `ms x ≠ 0` `∑(rnVec x i)^2 = n`;
  `rms_not_centered` для `1 ≤ n` даёт сумму выхода на векторе из единиц,
  равную `n`.

## Hagi/Model/RVCore.lean
- `wordAdd_spec`: `(wordAdd a b).toNat = (a.toNat+b.toNat) % 2^32`;
  `wordSub_spec` задаёт оборачивающуюся разность по тому же модулю, а
  `wordAnd_spec` использует `Nat.land`.
- `wordAdd_carry_decomp`: полная сумма равна машинной сумме плюс
  `carry a b*2^32`; `carry ≤ 1` и `carry = 0` ровно при сумме `< 2^32`.
- `execDeterministic` доказывает согласованность произвольной бинарной
  операции с равенством аргументов;
  это не спецификация полного набора RISC-V.

## Hagi/Model/ReferenceMachine.lean
- Для `a w : Fin n → ℝ` `jointStep_energy` даёт
  `energy a (jointStep a w eta) = (1-eta)^2*energy a w`;
  `jointStep_energy_decrease` при `0 < eta < 2`, `a ≠ w` делает спад
  строгим.
- `machine_quant_err_bound` при `0 < Delta` даёт
  `quantErr Delta w ≤ √n*Delta/2`; `machine_energy_bound` ограничивает
  энергию полного шага квадратом суммы нормы после `jointStep` и этого
  бюджета квантования, делённым на `2`.
- `machine_step_floor`: при `eta = 1`, `0 < Delta`
  `energy a (machineStep a w 1 Delta) ≤ n*Delta^2/8`.

## Hagi/Model/Residual.lean
- Для нормированного `X`, `‖f t x‖ ≤ eps` и `0 ≤ eps`
  `res_bounded_drift` даёт `‖resStream f x0 T-x0‖ ≤ T*eps`.
- `cascade_exp_bound`: если `‖g t x‖ ≤ (1+delta)*‖x‖` и
  `0 ≤ delta`, то `‖cascade g x0 T‖ ≤ (1+delta)^T*‖x0‖`.
- `linear_le_exp_contrast` — точное неравенство Бернулли
  `1+T*delta ≤ (1+delta)^T`, без утверждения обучаемости произвольной сети.

## Hagi/Model/Routing.lean
- `softDef_odds`: точное обновление шансов softmax при произвольном
  сдвиге скоров `a⁺j/a⁺k = (aj/ak)·exp(Δsj−Δsk)` — без приближений
  первого порядка.
- `odds_ratchet`: один шаг ЛОКАЛЬНОГО ratchet — сдвиг скоров,
  пропорциональный самой строке внимания (Δs = c·a, c > 0), строго
  увеличивает шансы более внимательного ключа. Один шаг, точно;
  глобальных/итерируемых growth-утверждений нет.
- `ratchet_advantage_step`: точное V-шаговое тождество
  `A⁺j = Aj + η·aj·‖δ‖²` (носитель `Fin d → ℝ`, явные суммы);
  `ratchet_advantage_mono` — монотонная форма при η ≥ 0, aj ≥ 0.

## Hagi/Model/ResidualVQ.lean
- `residual_sum_split`: `z = reconstruct R k + (z-reconstruct R k)`;
  `refine_geometric` при `0 ≤ D 0`, `0 ≤ rho k` и
  `D(k+1) ≤ rho k*D k` для `k<K` даёт
  `D K ≤ (∏k<K,rho k)*D 0`.
- `error_budget_uniform`: при `0 ≤ rho k ≤ ρ < 1`, `eps k ≤ ε`,
  `0 ≤ ε`, `D(k+1) ≤ rho k*D k+eps k` и `0 ≤ D k`
  `D K ≤ ρ^K*D 0 + ε*(1-ρ^K)/(1-ρ)`.
- `lattice_stop_horizon`: для рекурсии остатка с `latQ (δ/2^k)`,
  `0 < δ τ`, `1 ≤ K` и `n*(δ/2^(K-1))^2/4 ≤ τ`
  доказано `‖resid K‖^2 ≤ τ`; `lattice_quality_per_bit` содержит точный
  масштаб `(2^(K-1))^2`.

## Hagi/Model/Sidon.lean
- `sidon_pair_diff_injective`: для Sidon-`S`, `t i ∈ S`, `StrictMono t`,
  `i<j`, `k<l` равенство `t j-t i = t l-t k` влечёт `i=k`, `j=l`.
- `sidonSet_golomb4` подтверждает Sidon-свойство `{0,1,4,6}`.
- `advance_weights_shared` доказывает лишь сохранение `S.weights`
  переходом `advance` на `GrowthState X`; полная сериализация схем этим
  утверждением не формализуется.

## Hagi/Model/SoftmaxStep.lean
- Для одномерной `logitCE` `logitCE_deriv` даёт производную
  `-1/(1+exp w)`, а `grad_lipschitz` — глобальный коэффициент `1/4`.
- `descent_step`: при `0 < eta ≤ 2`
  `logitCE(w+eta/(1+exp w)) ≤ logitCE w -
  (eta/2)*(1/(1+exp w))^2`.
- `logitCE_trajectory_bound`: для шагов `w(t+1)=w t+eta t*d t`,
  `0 < eta t ≤ 2` и `d t^2 ≤ (-logitGrad(w t))*d t` телескоп даёт
  `logitCE(w T) ≤ logitCE(w 0)-Σ eta t*d t^2/2`;
  `logitCE_total_descent_bounded` ограничивает эту сумму величиной
  `logitCE(w 0)`.

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
- Транши миграции: C284 — класс range-bound + ident-мосты
  (P-FLOOR/P-LIPSCHITZ/padding, `headCE_nonneg`,
  `headCE_le_of_abs_sub_le`, `ceOneHot_padVector_param`); C285 —
  P-AGGREGATE batch-ядро `headLoss_le_of_forall_headCE_le` +
  `batchLoss_param`/`batchLoss_nonneg_param`; C286 — C6-обёртки и
  decoded-codebook radius (`ceOneHot_decodeJoint_le_log_card_add_param`,
  `ceOneHot_decodeJoint_le_ceBound_param`); C291 — мосты
  одношагового спуска `ceOneHot_next_le_param` и
  `headLoss_uniform_next_le_param` (константы дословно из замороженных
  оригиналов).

## Hagi/Model/SourceMixture.lean
- `mixture_sum_one`: если `Σλ=1` и каждый источник нормирован, смесь
  нормирована; `mixture_nonneg` дополнительно требует `0 ≤ λ`,
  `0 ≤ p s x`.
- `successDist_norm`: при `Σπ=1`, `0 ≤ r y ≤ 1` и
  `0 < successProb π r` условное распределение успеха нормировано;
  `successDist_nonneg` даёт неотрицательность при `0 ≤ π`, `0 ≤ r` и той
  же положительной вероятности успеха.

## Hagi/Model/SpecDecoding.lean
- `anchor_eq_ema`: `anchorSeq α x n = ema (1-α) x n`;
  `anchor_stable` при `0 ≤ α ≤ 1` и всех `x t ∈ [lo,hi]` сохраняет всю
  якорную траекторию в `[lo,hi]`.
- `accept_chain_prob`: произведение `k` одинаковых вероятностей равно
  `α^k`; `speculative_expected_tokens` при `α ≠ 1` даёт
  `∑ i<k+1, α^i = (1-α^(k+1))/(1-α)`.
- `speculative_win`: при `0 < α`, `1 ≤ k` эта геометрическая сумма
  строго больше `1`.

## Hagi/Model/StageSemantics.lean
- `advance_energy_drop` для `S : GrowthState X` и свежего `StageInput X`
  при законах роста/слияния/совместного шага/сжатия даёт
  `compressEnergy ≤ S.energy - (growGain + gap +
  (η*⟪grad,d⟫ - L*η^2*‖d‖^2/2) - κ*s*quantErr)`;
  посылки включают `0 ≤ gap`, `0 < L`, `η ≤ 1/L`,
  `‖d‖^2 ≤ ⟪grad,d⟫` и соответствующие неравенства энергии.
- `cone_growth_window`: при `0 < γ`, `0 ≤ αmin ≤ αcap`,
  `C(t+1)=C t+G t`, `γD≤G`, `αmin/γ*C≤D` и `G≤αcap*C`
  `(1+αmin)*C t ≤ C(t+1) ≤ (1+αcap)*C t`.
- `trajectory_energy_telescope`: если каждый свежий цикл имеет
  `compressEnergy ≤ energy-d0`, `0 ≤ d0`, то
  `energy_t ≤ energy_0-t*d0`; `trajectory_ledgers_monotone` даёт
  невозрастание бюджета и неубывание защищённого риска.

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
- `adamw_equilibrium_magnitude`: при `0 < ε lam |θ|`,
  `lam*|θ| < 1` и `g/(|g|+ε)+lam*θ=0`
  `|g| = lam*|θ|*ε/(1-lam*|θ|)`.

- `quantized_safe_window`: при `L i,eps i,eta ≥ 0`, идеальном окне,

## Hagi/Research/ConditionalInformation.lean
- Для строго положительной нормированной `p` на `X×(Z×Y)` и условной
  положительной нормированной ссылки `q : X→Y→ℝ`
  `conditionalMutualInformation_eq_expected_log_ratio_sub_reference_kl`
  равна ожидаемому логарифмическому отношению минус явный KL несоответствия
  ссылки.
- `conditionalMutualInformation_eq_matched_log_ratio` даёт форму без этого
  поправочного члена для согласованной маргинальной ссылки.
- `conditionalMutualInformation_pair_eq_prefix_add_extension` доказывает
  конечное цепное правило: условная взаимная информация исходной пары
  равна такой величине после суммирования по `W` плюс величина расширения при дополнительном условии `(X,Z)`.

## Hagi/Research/CrossModalGap.lean
- Для непустых конечных `X Y` и строго положительной нормированной
  `p : X×Y→ℝ`
  `crossModalGap_eq_kl` равна `klDef p (margX p * margY p)`;
  `crossModalGap_nonneg` доказывает неотрицательность.
- `crossModalGap_zero_iff_indep`: разрыв равен нулю тогда и только тогда,
  когда `p(x,y)=margX p x*margY p y` для всех `x y`.

## Hagi/Research/OmniInvariant.lean
- На непустых конечных `Y1 Y2`, для положительной нормированной `p`,
  `omniStep C gIntra gCross cComp cRisk =
  C+gIntra+gCross-cComp-cRisk`.
- `omniPhi_step` при зависимой `p` и
  `eps ≤ gIntra+crossModalGap p-cComp-cRisk` не увеличивает `omniPhi`;
  строгое покрытие в `omniPhi_strict` даёт строгое уменьшение потенциала.
- `omniInvariant_preserved`: при `0 ≤ gIntra`, зависимой `p`,
  `cComp+cRisk ≤ gIntra`, покрытии `eps` и `0 ≤ budget-(cComp+cRisk)`
  одновременно доказаны невозрастание `omniPhi`, строгий рост способности,
  coverage-неравенство и неотрицательный остаток бюджета.

## Hagi/Research/OmniState.lean
- `driftTube_closed`: при `ρ ≠ 1`
  `driftTube ρ e d0 t = ρ^t*d0 + e*(1-ρ^t)/(1-ρ)`;
  `drift_limit` при `0 ≤ ρ < 1`, `0 ≤ e d0` ограничивает его
  `d0 + e/(1-ρ)`, а `drift_zero` убирает аддитивный член ошибки при `e=0`.
- `admissionChain`: если `0 < deltaNet` и
  `C s+deltaNet ≤ C(s+1)` для всех `s<t`, то `C 0+t*deltaNet ≤ C t`.
- `omniLeafCost` и `omniParamCost` дают `r*d` и `k*(r*d)` элементов;
  `sharedStateCostBound` при `0 < d`, `k*r < d` доказывает
  `∑ i<k,r*d < d*d`.

## Hagi/Optimization/OptimizerVariants.lean
- `acc_mono`: `adagradAcc g t ≤ adagradAcc g (t+1)`.
- `adagrad_step_anti`: при `0 ≤ eta` и `0 < adagradAcc g t`
  `eta/√(acc+g t^2) ≤ eta/√acc`.

## Hagi/Optimization/EF21Quantizer.lean
- `IsContractive`: контракт контрактного компрессора `‖C u − u‖₂² ≤ (1−α)²‖u‖₂²` на plain-носителе `n → ℝ` (суммы квадратов явно). Доказанные инстансы: identity (α=1), нулевой компрессор (α=0), scaling-компрессор `u ↦ c•u` (α=c, c ∈ [0,1] — недегенеративный инстанс); инстансы квантователей (TopK, qTernVec) — см. `Hagi/Optimization/EF21Quantizer.lean` (C247: α=0 доказаны, α ∈ (0,1] опровергнуты свидетелями).
- `ef21_update_norm_le`: точный одношаговый перенос сжатия Markov-обновления `v + C(g−v)`: `‖v_{t+1} − g‖₂² ≤ (1−α)²‖g − v_t‖₂²` без зазора.
- `ef21_lyapunov_descent`: одношаговый спуск значения функции (premise-form): L-гладкость + дефект выравнивания δ + дефект нормы при `η ≤ 1/(2L)` дают `f' ≤ f − (η/2)(1−2Lη)‖g‖₂² + (η/2)(1+2Lη)δ²` — константы точные (разница = `η/2·(1+Lη)(s−δ)²/2 ≥ 0`, ring-тождество).

## Hagi/Optimization/AdaptiveCycle.lean
- `adaptive_cycle_expansions`: если `0 < δ`, `C(k+1)≤C k-δ` и
  `0 ≤ C j` для всех индексов, то для любого `N`
  `(N : ℝ) ≤ C 0/δ`.
- `adaptive_hagi_contract_thermal` на конечномерном вещественном
  пространстве с `OrthonormalBasis (Fin d)` объединяет:
  `M/(1+(M-1)μ²) ≤ d` для единичных направлений при `2 ≤ M`, `0 < d`,
  `0 ≤ μ`; границу расширений; `x K < τ` для неточной рекурсии при
  заданном строгом условии на `q^K`; и существование `0 < T` с оценками
  логарифмов softmax при `s/τ ≤ ε/log card ι`, `2 ≤ card ι` и положительных
  `s τ ε`.
- `cautiousMask_abs_le`: `|cautiousMask u g| ≤ |u|`;
  `cautiousAligned`: `0 ≤ cautiousMask u g*g`.

## Hagi/Optimization/Checkpoint.lean
- `ckpt_mem_floor`: для вещественных `0 < k n`
  `2*√n ≤ k+n/k`.
- `ckpt_sqrt_opt`: при `0 < n`
  `√n+n/√n = 2*√n`, то есть нижняя граница достигается при `k=√n`.

## Hagi/Optimization/ComputeScaling.lean
- `compute_scaling_lower_bound`: при `0 < a b m n`
  `(√a+√b)^2/(m+n) ≤ a/m+b/n`;
  `compute_scaling_bound_attained` достигает равенства при
  `m=√a*s`, `n=√b*s`, `0 < s`.
- `compute_scaling_multi`: для конечного `S` и положительных `a i m i`
  `(Σ√a i)^2/(Σm i) ≤ Σ(a i/m i)`.
- `compute_scaling_multi_attained`: для `S.Nonempty` и `0 < s`
  аллокация `m i=√a i*s` обращает многоресурсную нижнюю границу в
  равенство.

## Hagi/Optimization/DREAM.lean
- `dream_tau_extrapolation`: если
  `nu = (2*tau+1)-1/2`, то
  `‖dreamY s-s.x‖ = (2*tau+1/2)*‖s.x-s.xPrev‖`.
- `dream_gd_as_plRec` отождествляет заданную рекуррентность
  `e(k+1) ≤ (1-mu*alpha)e k+sig^2*alpha^2` с `plRec`.
- `dream_gd_wsd`: при `0 < mu etaMax`, `mu*etaMax ≤ 1`,
  `0 ≤ e t` и `plRec mu sig (fun _ => etaMax) e`
  ошибка после `m+k` ограничена сжатием устойчивой фазы, геометрической
  суммой шума и добавкой `k*sig^2*etaMax^2`.

## Hagi/Optimization/DirectionPacking.lean
- `welch_bound_core`: для единичных `u : Fin M → F` в конечномерном
  вещественном пространстве с `OrthonormalBasis (Fin d)`, `2 ≤ M`,
  `0 < d` и `|⟪u i,u k⟫| ≤ μ` для `i≠k`
  `(M-d)/(M-1) ≤ d*μ^2`.
- `welch_min_dimension`: при дополнительном `0 ≤ μ`
  `M/(1+(M-1)*μ^2) ≤ d`.
- `welch_capacity_full`: для `M+1` единичных направлений,
  `1 ≤ M`, `0 < d`, `0 ≤ μ`
  `(M+1)/(1+M*μ^2) ≤ d`.

## Hagi/Optimization/GraphDistanceRouting.lean
- Если в конечном графе `G` каждая вершина достигает target, то носитель
  нецелевой строки ядра кратчайшего пути равен `shorterNeighborFinset`;
  `dist_add_one_eq_of_mem_support` доказывает
  `dist b target+1 = dist v target` для поддержанного перехода.
- `historyLaw_shortestToTarget_hitBy_card_eq_one`: при
  `card V ≤ T` внешняя мера попадания в target на горизонте `card V`
  равна `1` для любого начального PMF.
- `historyLaw_shortestToTarget_firstHit_dist_eq_one`: для чистого старта
  `s` при `dist s target ≤ T` точное первое попадание на шаге
  `dist s target` имеет внешнюю массу `1`.

## Hagi/Optimization/InexactContraction.lean
- `inexact_contraction_halt`: при `0 < q < 1`, `0 ≤ ε`,
  `x(k+1)≤q*x k+ε`, `0 < B`, `x0≤B` и
  `q^K < (τ-ε/(1-q))/B` доказано `x K < τ`.
- `anderson_floor_gain`: при `0 < θ < 1`, `0 < q < 1`, `0 ≤ ε` и
  `x(k+1)≤θ*q*x k+ε`
  `x k≤(θq)^k*x0+ε*(1-(θq)^k)/(1-θq)` и
  `ε/(1-θq)≤ε/(1-q)`.
- `anderson_halt` заменяет условие останова на
  `(θ*q)^K < (τ-ε/(1-θ*q))/B` и даёт `x K < τ`.

## Hagi/Optimization/LRSchedule.lean
- Для непустого конечного индекса `polyWeights C eps` неотрицательны и суммируются в `1`. При `0 < eps` и `C u < C w` теорема `polyWeights_strict_mono` даёт `polyWeights C eps w < polyWeights C eps u`.
- `polyDelta` образует взвешенную сумму направлений, а `polyStepUpdate` прибавляет её с коэффициентом `ℓ` к `θ`.
- `polyDelta_basis_sum`: если `dirs v j = if v = j then 1 else 0`, то при непустом конечном `n` сумма координат `polyDelta dirs C eps` равна `1`; это не утверждение о невырожденности каждой координаты или о качестве обновления.

## Hagi/Research/MarkovPercolation.lean
- `historyLaw_walk_support`: любой маршрут графа поддерживается однородным
  `historyLaw` для `supportedRoutingKernel`, если его первая вершина
  принадлежит носителю начального PMF.
- `exists_walk_history_support_of_crossing` превращает существующий
  `crossing` в пару top/bottom и поддерживаемую точную историю;
  `exists_walk_history_support_of_forall_top` требует отдельной посылки
  достижимости bottom из каждого top-старта с собственным горизонтом
  маршрута.
- `uniformNeighborKernel_support`: для локально конечного графа с
  непустыми `G.neighborFinset` носитель равномерного ядра совпадает с рёбрами.

## Hagi/Optimization/Momentum.lean
- `momentum_floor`: при `0 < q`, `0 ≤ β δ`, `q+β<1` и
  `e(k+1)≤q*e k+β*e(k-1)+δ`
  ошибка ограничена полом `δ/(1-q-β)` плюс затухающий член с
  `momentumRate q β`.
- `momentum_achievability`: при тех же условиях и `0 < ε`
  существует конечный горизонт, после которого всегда
  `e s ≤ δ/(1-q-β)+ε`.
- `momentum_schedule`: для `0 < q`, `0 ≤ bbar`, `q+bbar<1`,
  `0 ≤ e k`, `β k≤bbar` и рекурсии без `δ` при `k≥1`
  `e k≤max(e0,e1/momentumRate q bbar)*(momentumRate q bbar)^k`.

## Hagi/Optimization/MomentumHB.lean
- `hb_discriminant_interval`: при `0 < β < 1` и
  `(1-√β)^2 ≤ η*μ ≤ (1+√β)^2` дискриминант неположителен;
  `hb_root_modulus` для корня `λ²-tλ+β=0` с `0 < β` и
  дискриминантом `≤0` даёт `normSq λ = β`.
- `hb_cfg_rate`: при `0 < ρ < 1` и корне характеристического уравнения
  конфигурации `β=ρ²`, `η=(1-ρ)²` имеет место `normSq λ = ρ²`.
- `hb_repeated_root_closed_form` даёт `e n=(C+D*n)*ρ^n`;
  `hb_critical_trajectory_bound` для `0 < ρ` оценивает критическую
  скалярную моду через `(|e0|+|e1/ρ-e0|*n)*ρ^n`, сохраняя жорданов фактор.

## Hagi/Optimization/NeuronAlloc.lean
- `neuron_alloc_lower_bound`: для положительных `c i n i N` и
  `Σn=N` `(Σ√c i)^2/N ≤ Σ(c i/n i)`.
- `neuron_alloc_opt_attained`: на непустом конечном типе при
  `0 < c i`, `0 < N` аллокация `n i=√c i*N/Σ√c` обращает границу в
  равенство.
- `neuron_alloc_equal_costs`: при `0 < k`, `0 < c0 N`
  равномерная аллокация даёт `Σc0/(N/k) = k^2*c0/N`.

## Hagi/Optimization/PLConvergence.lean
- `pl_linear_convergence`: при `0 < L`, `0 < μ ≤ L`,
  `Estar≤E t`, `E(t+1)≤E t-G t/(2L)` и
  `2μ*(E t-Estar)≤G t`
  `E t-Estar≤(1-μ/L)^t*(E0-Estar)`.
- `pl_sufficient_horizon`: при тех же условиях и
  `(1-μ/L)^t*(E0-Estar)≤ε` доказывает `E t-Estar≤ε`.
- `ppoClip r lb ub = max lb (min ub r)`; доказаны монотонность по `r` и `ppoClip_fixed`: при `lb ≤ r ≤ ub` отсечка равна `r`.

## Hagi/Optimization/RobbinsMonro.lean
- `robbins_monro_decay`: при `0 ≤ x 0`, `0 ≤ η k ≤ 1`, рекурсии `x (k+1) ≤ (1-η k)*x k` и `Tendsto (fun n => ∑ k ∈ range n, η k) atTop atTop` для любого `ε > 0` найдётся `T`, после которого `x s ≤ ε`.
- `robbins_monro_abs` переносит тот же вывод на `|y s|` при рекурсии `|y (k+1)| ≤ (1-η k)*|y k|`.
- `robbins_monro_bias`: из `x (k+1) ≤ (1-η k)*x k + D*η k` и расходимости суммы шагов следует существование хвоста с `x s ≤ D + ε`. Это верхняя граница хвоста, а не равенство предела `D`.

## Hagi/Research/Schelling.lean
- `localCompatibleDegree` считает соседей `w` с `k ≤ compatibility v w`, а `locallySatisfied` требует не менее `min k (G.degree v)` таких соседей. Нулевой порог и изолированная вершина удовлетворены автоматически.
- Доказаны `localCompatibleDegree_le_degree` и, при `G.degree v ≤ k`, эквивалентность `locallySatisfied_iff_forall_of_degree_le`: удовлетворённость означает выполнение порога совместимости для каждого соседа.
- `locallySatisfied_disconnected` строит на `Fin 4` граф из двух ребер: все вершины локально удовлетворены при `k = 1`, но вершины `0` и `2` недостижимы друг из друга и выполнено `¬ disconnectedGraph.Preconnected`. Динамика переселения не формализуется.

## Hagi/Research/SchellingPercolation.lean
- `locallySatisfied_mono_of_le`: при `G ≤ G'` локальная удовлетворённость сохраняется только с дополнительной посылкой `k ≤ G.degree v`; без неё квота `min k degree` может вырасти при добавлении рёбер.
- `parity_boundary1` точно вычисляет две диагональные открытые клетки при пороге `1`: все клетки изолированы, локальная удовлетворённость при отрицательной совместимости выполнена вакуумно, а `crossing rowTop rowBot` отсутствует.
- `parity_threshold2` доказывает вложение открытых графов, наличие `crossing` при пороге `2`, неудовлетворённость всех клеток для постоянной совместимости `-1` и удовлетворённость для отдельно выбранной постоянной совместимости `1`.

## Hagi/Optimization/SphericalDamping.lean
- `chordal_residual_eq`: для единичных `u v` выполнено `1 - ⟪u,v⟫ = (1/2)*‖u-v‖^2`.
- `angular_damping_window`: при `ζ < 1` условие `|1 - η + η*ζ| < 1` эквивалентно конъюнкции `0 < η` и `η < 2/(1-ζ)`.
- Для единичных `u v` формула `normalized_mixture_inner` вычисляет внутреннее произведение нормированной смеси с `u`; при ненулевой норме смеси `mixture_normalize_unit` и `normalized_mixture_distance` дают единичную норму и хордовый остаток `1 - (α + β*⟪u,v⟫) / ‖α•u + β•v‖`.

## Hagi/Optimization/SubspaceGrowth.lean
- `projResidual u v = v - ∑ i, ⟪u i,v⟫ • u i`. Для единичного попарно ортогонального семейства остаток ортогонален каждому `u i`, выполнено `projResidual_self_inner`, а `projResidual_le_norm` даёт `‖projResidual u v‖ ≤ ‖v‖`.
- `growth_finite`: если `δ > 0`, `C (k+1) ≤ C k - δ` и все `C k ≥ 0`, то `(k : ℝ)*δ ≤ C 0`. Это ограничение на длину такой числовой траектории, а не самостоятельное доказательство остановки конкретного алгоритма.

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

## Hagi/Pretraining/Dust.lean
- `hcDelta` вычисляет среднее `signR (u i) * signR (u j)` по булеву кубу как `if i = j then 1 else 0`. `esUnbiased` при `σ ≠ 0` доказывает точное равенство среднего симметричной разности `esEst` и `quadfGrad` для квадратичной модели.
- `varianceHalving` для центрированного векторного поля даёт точное уменьшение среднего квадрата суммы двух независимых выборок вдвое; `dustNoiseHalving` переносит это на ошибку `esEst - quadfGrad`.
- В этом файле доказан случай двух выборок, а не общий закон `1/K` и не общая K-ошибка выравнивания.

- `hcVarK`: для центрированного скалярного поля и `K > 0` средний квадрат среднего по `K` независимым точкам куба равен одношаговому среднему квадрату, делённому на `K`. `dustVarK` доказывает такое же точное тождество для суммы квадратов координатной ошибки `esEst`, а `dustVarK_expQ` записывает его через `Probability.expQ`.

- `rademacherLaw` получает вероятностную меру честного булева произведения; `rademacher_expect_sign` и `rademacher_projection_mean` дают нулевые средние знака и проекции шума.

## Hagi/Pretraining/ProbeError.lean
- `fd_probe_error`: при `σ > 0` и модельной гладкости с константой `L` абсолютная ошибка прямой разности не превышает `(L/2)*σ*‖v‖^2`; `linear_probe_exact` даёт точность для аффинной функции.
- `centralQuadraticProbe_exact` восстанавливает квадратичный градиент точно, тогда как `forwardQuadraticProbe_error` для `x v : X` при `0 ≤ L` и `0 < σ` вычисляет ошибку прямой пробы как `(L/2)*σ*‖v‖^2`. Для кубической модели `centralCubicProbe_remainder` равен `(c/6)*σ^2*‖v‖^6`; `noisyCentralCubicProbe_optimal_bound` ограничивает ошибку через `probeCost` при ограниченных шумах.
- `residual_vec_bound` и `mlpResidual_bound` ограничивают норму отброшенного хвоста суммой `|φ j|*‖v j‖` по дополнению выбранного индекса.

## Hagi/Pretraining/RobustnessLaw.lean
- `robust_interpolation_lipschitz_floor`: интерполяция точек с `L`-липшицевой функцией влечёт `|y(i+1)-y i| ≤ L*|x(i+1)-x i|`. `no_lipschitz_interpolator_of_steep` исключает такую функцию при противоположном строгом неравенстве.
- Если расстояние соседних точек не превосходит `δ > 0`, а перепад меток не меньше `σ`, `lipschitz_floor_of_noisy_labels` даёт `σ/δ ≤ L`.
- При `η ≥ 0`, `η*L ≤ 1` и положительных `σ δ` теорема `noisy_interpolation_step_cap` даёт `η ≤ δ/σ`. При дополнительных `G > 0`, `T ≥ 0` и посылке `D ≤ T*(η*G)` получается `D*σ/(δ*G) ≤ T`; `robust_budget_floor` добавляет `c ≥ 0`, `T*c ≤ B` и выводит `c*(D*σ/(δ*G)) ≤ B`.

## Hagi/Pretraining/Speedrun.lean
- `cePartition_move` точно вычисляет изменение суммы экспонент при сдвиге одного логита. При положительной исходной сумме `ceLogit_move_change` выражает изменение CE как целевой член `-(if j = y then δ else 0)` плюс логарифм мультипликативного изменения нормировки.
- `head_probe_linear` — тождество `h (x + σ•d) = h x + σ•h d`; `hadamard_probe_inversion` при `c ≠ 0` и `H*Hᵀ = c•1` восстанавливает `Δ` из `g = H*ᵥΔ` как `c⁻¹ • (Hᵀ *ᵥ g)`.
- `probe_lower_bound`: для линейного `f : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ)` при `n < k` существует ненулевой вектор ядра; это не оценка стоимости физического вычисления.

## Hagi/Pretraining/SyntheticPretrain.lean
- `time_to_capability_correct`: при достижимости порога и монотонности `C` индекс `TimeToCapability` является первым с `τ ≤ C`, до него `C < τ`, а после него порог сохраняется.
- `synth_investment_dominates`: для `Cp Cs : ℕ → ℝ` со свидетельствами
  достижимости `hp : ∃ n : ℕ, τ ≤ Cp n`, `hs : ∃ n : ℕ, τ ≤ Cs n` и
  тождествами `hTp : (TimeToCapability τ Cp hp : ℝ) = Tp`,
  `hTsCast : (TimeToCapability τ Cs hs : ℝ) = Ts`; положительны τ,
  размер синтетического набора C_s и стоимость шага c_s, неотрицательно T_s
  и задана измеренная посылка synthGain τ Cp Cs hp hs * c_s > C_s;
  тогда отношение τ/(C_s + T_s*c_s) строго больше τ/(T_p*c_s).
- `task_selection_marginal`: на конечном непустом семействе с заданным условием `0 < c j` существует jmax, максимизирующий `g j / c j` среди всех кандидатов.

## Hagi/Probability/AdaptiveSuccess.lean
- `adaptive_success_count_floor`: на конечном независимом произведении, для `X i v ∈ [0,1]`, общего пола `SuccessFloor p X p0`, `n > 0` и `t > 0` вероятность события `n*p0 - t ≤ ∑ i, X i (ω i)` не меньше `1 - exp (-2*t^2/n)`.
- `adaptive_success_concentrated` при `0 < delta < 1` даёт вероятность не меньше `1-delta` для порога `n*p0 - sqrt (n*log(1/delta)/2)`.
- Пол `coordMean p X t ≥ p0` требуется по каждой координате; одинаковое распределение успехов не предполагается.

## Hagi/Probability/Azuma.lean
- `hoeffding_lemma_prefix` ограничивает MGF условно центрированной величины с `-c ≤ X ≤ c` через `exp (lam^2*c^2/2)`. `azuma_mgf` по префиксным условным средним даёт `prodE ... ≤ exp (n*lam^2*c^2/2)`.
- `azuma_tail_low`: при `c > 0`, `n > 0`, `Δ > 0` масса события `azumaSum X n ω ≤ -Δ` не превышает `exp (-Δ^2/(2*n*c^2))`; это односторонний хвост.
- `adaptive_success_azuma`: для `S t pref ∈ [0,1]` и префиксных полов `p0 ≤ ∑ v, q v * S (t+1) (snoc pref v)` вероятность `n*p0 - Δ ≤ azumaSum S n ω` не меньше `1 - exp (-Δ^2/(2*n))`.

## Hagi/Probability/ThermoBridge.lean (BatchSNR)
- `snr_realized` записывает SNR как квадрат среднего, делённый на дисперсию batchMean; `snr_linear` даёт точное `snr g B = B * snr g 1`.
- При `popMean g ≠ 0` и `0 < popVar g` теорема `snr_ge_one_iff` эквивалентно связывает `snr g B ≥ 1` и `criticalBatch g ≤ B`.
- `gain_decreasing_past_critical`: при положительных `Bstar alpha beta` и `Bstar ≤ B1 < B2` значение `gainPerCost` строго убывает от `B1` к `B2`.

- `noise_axes_coincide`: при `r^2*c = 1`, `eta0^2*B0 = 1` и `B0 ≠ 0` для каждого `t` выполнено `eta0^2*r^(2*t) = 1/(B0*c^t)`.

- `prodE_as_expQ` отождествляет ожидание `prodE (uniP b)` с `Probability.expQ` по постоянной плотности равномерного произведения.

- `stable_phase_noise` при `B0 ≠ 0` вычисляет сумму по n_w стабильных шагов как `sigma^2*n_w/B0`.

## Hagi/Probability/PMFBridge.lean (BernoulliFactory)
- `probAccept_eq_bernPoly` доказывает равенство двух явных сумм `probAccept` и `bernPoly`; `binomWeight` содержит биномиальные веса `choose n j * p^j * (1-p)^(n-j)`.
- При `0 ≤ p ≤ 1` и `0 ≤ c j ≤ 1` для `j ∈ range (n+1)` теорема `probAccept_bounds` даёт `0 ≤ probAccept n p c ≤ binomMass n p`.
- Это точные тождества и границы конечной Bernstein-конструкции; равенство `binomMass n p = 1` отдельной теоремой файла не сформулировано.

- `toPMF` строит PMF из неотрицательной функции `q` с суммой `1`, а `fromPMF` переводит массы через `ENNReal.toReal`; `toPMF_apply` даёт `ENNReal.ofReal (q v)`, `fromPMF_sum` — сумму вещественных масс, равную `1`.

## Hagi/Probability/CertifiedEstimator.lean
- Для независимых `X i ∈ [0,1]` доказаны `hoeffding_chernoff`, оптимизированный `hoeffding_tail` и `hoeffding_two_sided`: односторонний хвост суммы центрирований имеет границу `exp (-2*t^2/n)`, двусторонний для `n*eps` — `2*exp (-2*n*eps^2)` при `n > 0`.
- `certified_premise`: с вероятностью не меньше `1 - 2*exp (-2*n*eps^2)` из измеренного условия `∑X + 2*n*eps ≤ ∑Y` следует `∑coordMean p X ≤ ∑coordMean p Y`. Это вероятностная импликация на общем событии, не безусловная проверка посылки.
- `premises_union_confidence` объединяет фиксированное `S`: если каждое `A i` имеет вероятность не меньше `1-δ`, одновременное выполнение имеет нижнюю границу `1 - S.card*δ`.

## Hagi/Probability/ChernoffCGF.lean
- `cgf_centering` для положительных `q` даёт `log ∑q*exp(c*g) = c*μ + log ∑q*exp(c*(g-μ))`; нормировка `q` в этой алгебраической формуле не требуется.
- `chernoff_subgauss_tail`: при `q > 0`, `σ2 > 0`, `u > 0` и ограничении центрированного CGF через `c^2*σ2/2` масса `{μ+u ≤ g}` не превышает `exp (-u^2/(2*σ2))`. `tail_complement` отдельно нормирует дополнение хвоста при `∑q = 1`.
- `kl_dv_attained`, `cramer_cgf` и `cramer_sup_le_kl` связывают KL с вариационным функционалом и супремумом Чернова; `subgauss_dev_kl` выводит нижнюю оценку KL через квадрат сдвига среднего, делённый на `2*σ2`.

## Hagi/Probability/Concentration.lean
- C287 (A10): единый concentration-API для Hoeffding-семейства
  средних хвостов: `concConfidence ε n = exp(−2nε²)` — канонический
  односторонний [0,1] confidence; `concConfidenceTwoSided ε n =
  2·exp(−2nε²)`; парный радиус `concRadius δ n = sqrt(log(1/δ)/(2n))`
  с двойственностью `concRadius_valid`; `concConfidence_pm1_rescale` —
  [−1,1]-форма гейта C264 `exp(−nη²/2)` есть `concConfidence (η/2) n`
  (радиус на [−1,1] удваивается).
- Каноническая цепочка через API: `hoeffding_mean_tail_api`,
  `hoeffding_two_sided_api`, `cert_upper_api`.
- `hoeffdingBridge_weaker`: граница удалённого C288-моста
  `exp(−t²/(2n²))` следует из канонической `exp(−2t²/n)` —
  доказательство удаления более слабого листа.

## Hagi/Probability/ConditionalSuccess.lean
- `success_count_lower` и `success_count_lower_p0`: при `0 < delta < 1`, измеримости, значениях `S t ∈ [0,1]` и `iIndepFun S μ` сумма успехов с вероятностью не меньше `1-delta` ограничена снизу суммой средних минус `concDelta T delta`, а при поле `p0 ≤ μ[S t]` — величиной `p0*T - concDelta T delta`.
- `log_growth` добавляет поточечную посылку `log C(t+1) - log C t ≥ a*S t - eps t`, `a ≥ 0` и положительность `C`; на том же стохастическом событии получается нижняя граница логарифма роста с вычетом `∑eps`.
- `exp_growth_prob_form` превращает её в `C T ≥ C 0 * exp (a*(p0*T - concDelta T delta) - ∑eps)` с вероятностью не меньше `1-delta`. Независимость успехов остаётся явной посылкой `h_emp_indep`.

## Hagi/Probability/EntropyConvexity.lean
- `log_sum_ineq` для положительных `a b` даёт `sum(a)*log(sum(a)/sum(b)) ≤ ∑a*log(a/b)`; `kl_convex_first` доказывает выпуклость KL по первому аргументу при `0 < lam < 1` и положительных функциях на конечном носителе.
- `kl_data_processing` для произвольной конечной `T : V → W` и положительных нормированных законов ограничивает KL после агрегации по волокнам исходным KL.
- `entropy_chain` раскладывает совместный `∑ρ log ρ` через маргиналь и условные строки; отсюда `joint_entropy_ge_marginal` и `entropy_subadditive`, все при положительной нормированной `ρ`.

## Hagi/Probability/ExpChord.lean
- `exp_chord` — псевдоним `Hagi.Foundations.exp_chord_r`; `hoeffding_chord_mgf` для положительного нормированного `q` и `a ≤ g ≤ b`, `a < b`, ограничивает центрированный MGF хордой между `a` и `b`.
- `log_chord` и `amgm_weighted` дают вогнутость логарифма и взвешенное среднее при положительных `a b` и `0 < w < 1`; `young_two` доказывает `x*y ≤ x^p/p + y^q/q` для `x y ≥ 0` и сопряжённых `p > 1`, `1/p + 1/q = 1`.
- `hoelder_finite` и `hoelder_weighted` дают неравенство Гёльдера; `lp_mean_le_rms` использует нормированные неотрицательные веса, а `lyapunov_moment_mono` доказывает монотонность моментов при `0 < r < s`.

## Hagi/Probability/FiniteBayes.lean
- `observationEvidence_eq_sum` вычисляет свидетельство наблюдения как `∑x, p₀ x * K x y`; `posterior_apply` при `0 < observationEvidence` нормирует `p₀ x * K x y` этим свидетельством, а `posterior_sum_toReal` даёт сумму `1`.
- `mode_posterior_le` показывает, что `mode` максимизирует апостериорный закон; `mode_zeroOneLoss_le` минимизирует `zeroOneLoss` среди всех решений, а `mode_zeroOneLoss_le_observation` сравнивает его также с решением `y` для наблюдения того же конечного типа.
- `linkedPosterior_apply` отдельно раскрывает апостериорный закон связанного XOR-канала через `ν.map (eventMask neighbors)` и `flip x y` при положительном свидетельстве наблюдения.

- `changedCount_eq_sum` и `hammingRisk_eq_sum_coordinateLoss` разлагают число изменённых битов и его математическое ожидание по координатам, отличая эту цель от потерь всей плоскости.

## Hagi/Probability/FiniteEM.lean
- Центральное разложение выражает `ceDef q (jointMass model) - entDef q` как `-log evidence + KL(q, posterior)` при положительном свидетельстве наблюдения и `q.support ⊆ posterior.support`; при `q = posterior` оно упрощается до `-log evidence`.
- `observationEvidence_le_of_ceDef_jointMass_le`: при положительных свидетельствах наблюдения обеих моделей, включении поддержки старого апостериорного закона в новый и неравенстве ожидаемых полных кросс-энтропий новое свидетельство не меньше старого.
- `mStep_spec` для конечного непустого семейства выбирает кандидата, минимизирующего ожидаемую полную кросс-энтропию, и сохраняет требуемые положительность свидетельства и поддержку. `current_observationEvidence_le_mStep` при точном старом апостериорном законе доказывает монотонность фактического свидетельства наблюдения.

## Hagi/Probability/FiniteFamilyConfidence.lean
- `finite_family_upper_confidence`: для заранее фиксированного конечного семейства и независимых `[0,1]`-выборок все истинные средние одновременно не превосходят выборочные средние плюс `eps` с вероятностью не меньше `1 - card(ι)*exp(-2*n*eps^2)`.
- `finite_family_abs_error_confidence` даёт одновременную границу `|populationMean - empiricalMean| ≤ eps` с вероятностью не меньше `1 - 2*card(ι)*exp(-2*n*eps^2)`.
- `finite_family_selected_population_mean_gap_lower_confidence` сохраняет тот же двусторонний уровень для `baseline ω` и `candidate ω`, выбранных после наблюдения: эмпирический разрыв минус `2*eps` ограничивает разрыв истинных средних. Оценка опирается на границу вероятности объединения по всему заранее заданному семейству, а не на независимость выбранного индекса.

## Hagi/Probability/FiniteLogScore.lean (вкл. FiniteJointLogScore, слит C525)
- При неотрицательных нормированных `p q` и поддержке `0 < p x → 0 < q x` доказаны `klDef_nonneg_of_support` и `klDef_eq_zero_iff_of_support`: `klDef p q ≥ 0`, а равенство нулю эквивалентно `q = p`.
- `ceDef_self_le_of_support` даёт `ceDef p p ≤ ceDef p q`; родственные результаты характеризуют случай равенства через равенство функций на поддержке.
- `fromPMF_ceDef_self_le` и `posterior_ceDef_self_le` переносят оценку на PMF при включении поддержек, для апостериорного закона дополнительно требуя положительное свидетельство наблюдения.

## Hagi/Probability/FiniteMultiEM.lean
- `total_negativeLogEvidence_drop_eq` при положительных свидетельствах наблюдения и включениях поддержек старых апостериорных законов в новые раскладывает суммарное убывание отрицательного логарифма свидетельства в убывание полной ожидаемой кросс-энтропии плюс сумму апостериорных KL.
- `total_negativeLogEvidence_le_of_total_completeCE_le` из неравенства суммарных полных кросс-энтропий выводит невозрастание суммарного отрицательного логарифма свидетельства; отдельного улучшения по каждой единице не утверждается.
- `batchMStep_spec` выбирает один глобальный кандидат для всей индексированной семьи и минимизирует суммарную полную кросс-энтропию. `current_totalNegativeLogEvidence_le_batchMStep` при точных старых апостериорных законах доказывает итоговое невозрастание суммы.

## Hagi/Probability/Freedman.lean (вкл. TwoSided/Step/Adaptive/FamilyConfidence, слит C525)
- `freedman_lemma_prefix`: при `|X| ≤ b`, нулевом условном среднем, `∑q*X^2 ≤ sig` и `lam ≥ 0` MGF не превосходит `exp (lam^2*sig*exp(lam*b)/2)`. `freedman_mgf` итерирует эту границу по префиксам.
- `freedman_tail_low` при `b ≥ 0`, `sig > 0`, `n > 0`, `Δ > 0` ограничивает `P(azumaSum X n ≤ -Δ)` через `exp (-Δ^2/(2*(n*sig + b*Δ)))`.
- `adaptive_success_freedman`: для `S ∈ [0,1]`, префиксных полов `p0` и измеренной посылки `∑q*S^2 ≤ sig` вероятность `n*p0 - Δ ≤ azumaSum S n` не меньше `1 - exp (-Δ^2/(2*(n*sig + Δ)))`.

## Hagi/Probability/GibbsCooling.lean
- `gibbs_concentration`: при `T > 0` и зазоре `E vstar + δ ≤ E v` для всех `v ≠ vstar` доля Гиббса минимизатора не меньше `1 - card(univ.erase vstar)*exp(-δ/T)`. C221: формулировка байт-в-байт неизменна, доказательство — тонкий королларий канонического `gibbs_concentration_canon` (GibbsCore) с card-мостом и мостом `1 - x ≤ 1/(1 + x)`.
- На последовательности температур `δ/(n+1)` с `δ > 0` доказаны `gibbs_concentration_tendsto` и `gibbs_tv_tendsto`; при дополнительной верхней границе превышения `Δ` также `gibbs_expected_energy_tendsto` и `gibbs_entropy_tendsto_zero`. Свободная энергия стремится к `E vstar` по `free_energy_tendsto`.
- `free_energy_sandwich` даёт `Emin - T*log(card V) ≤ -T*log Z ≤ Emin`; `free_energy_sharp_lower` усиливает нижнюю границу через `log(1 + ((Finset.univ.erase vstar).card : ℝ)*exp(-δ/T))`.

## Hagi/Probability/KLSBridge.lean
- `gradCovBound`: для неотрицательной нормированной `q`, `C ≥ 0`, из посылки Пуанкаре для каждого направления и оценки чувствительности `(sens a x)^2 ≤ L^2*sqN a` следует `gradVar q g a ≤ C*L^2*sqN a`.
- `klsBatchNoise`: при `B > 0`, тех же посылках и нулевых попарных ковариациях центрированных проекций второй момент центрированного среднего по батчу не превосходит `C*L^2*sqN a / B`.
- `uncorrMeanVar` даёт точное разложение второго момента среднего по некоррелированным слагаемым, а `expQ_varEq` — стандартное тождество центрального второго момента.

## Hagi/Probability/LinkedFlip.lean
- `linkedChannel_apply` представляет переход как `(ν.map (eventMask neighbors)) (x ^^^ y)`. Для `ν = pure none` канал оставляет `x` на месте, а для `pure (some a)` применяет `linkedMask neighbors a`.
- При `(neighbors a).card ≤ k` размер поддержки маски и `changedCount` после инверсии битов не превосходят `k+1`; якорь включается в это число.
- `uniformPlane_bind` доказывает сохранение равномерного закона после связанного канала, а `decodeByteRows_encodeBytePlane` и `encodeBytePlane_decodeByteRows` — обратимость конечного байтового представления. Смешивание цепи и равномерность эмпирических данных не утверждаются.

## Hagi/Probability/MarkovPathSupport.lean
- `historyLaw_support_of_path`: если начальная точка принадлежит поддержке `initial` и первые `k ≤ T` переходы принадлежат поддержкам ядер, существует полная история в поддержке `historyLaw initial K T k`, совпадающая с заданной до `k`.
- `historyLaw_full_support` переносит это на весь горизонт `T`, а `historyLaw_full_apply_pos` даёт строго положительную массу такой истории.

## Hagi/Probability/MomentBounds.lean
- Для положительного нормированного `q` и `a ≤ g ≤ b` доказаны `popoviciu_var`: `Var(g) ≤ (b-a)^2/4`, `popoviciu_abs_dev`: среднее абсолютного отклонения не превышает `(b-a)/2`, а также хвосты Чебышёва и Кантелли с константами от диапазона.
- `bhatia_davis` даёт `Var(g) ≤ (b-μ)*(μ-a)`. Следствие `var_le_delta_excess` записывает `Var(g) ≤ (b-a)*(μ-a)`.
- При `a < b` обратная по смыслу оценка `excess_ge_var_over_range` даёт `Var(g)/(b-a) ≤ μ-a`; это две стороны связи дисперсии и превышения среднего, а не равенство между ними.

## Hagi/Probability/NoiseTemperature.lean
- При непустом `Fin b` теорема `batchMean_unbiased` доказывает равенство среднего batchMean исходному `popMean`; `batch_variance_eq` даёт точное `prodE (uniP b) ((batchMean - popMean)^2) = popVar / b` на равномерном независимом произведении.
- `noise_scale_separation`: при `0 < eta ≤ 1` и `theta ≥ 0` выполнено `eta*theta ≤ sqrt eta * theta`.
- `anneal_by_batch`: при `sigma ≥ 0`, `c > 1`, `B 0 > 0` и `B(t+1) = c*B t` для `t < n` сумма `∑_{t<n} sigma^2/B t` не превосходит `sigma^2*c/(B 0*(c-1))`.

## Hagi/Probability/RankedStopRouting.lean
- Если каждый поддерживаемый нетерминальный переход выполняет `R a b` и строго увеличивает rank, терминальные строки являются `PMF.pure a`, `rank a ≤ B` и `B ≤ T`, то `terminal_at_rankBudget_of_historyLaw_support` доказывает терминальность координаты `B` каждой поддерживаемой полной истории. Начальный ранг нулём не требуется.
- `historyLaw_ranked_hitBy_eq_one` усиливает это до массы `1` события `∃j ≤ L, terminal (historyIndex T j)`; `classifyRouting_some_ranked_arrived` возвращает `.Arrived` в координате `L`.
- Для общего `classifyRouting` доказаны различия режимов: `.Arrived` при корректном префиксе и терминальности, `.Hold` при `k < T`, корректном префиксе, готовой строке и нетерминальности, `.Unknown` при неготовой строке, нарушенном префиксе либо исчерпанном бюджете без терминальности.

## Hagi/Probability/SphericalAngle.lean
- `sphericalAngle_add_two` при `n > 0` даёт `Ω(n+2) = (2π/n)*Ω n`; `sphericalAngle_even_geo` и `sphericalAngle_odd_geo` ограничивают чётную ветвь от `8` и нечётную от `9` геометрическими последовательностями с множителем `π/4`.
- `sphericalAngle_tendsto_zero` доказывает `Tendsto sphericalAngle atTop (nhds 0)`.
- `sphericalAngle_seven` вычисляет `Ω 7 = 16*π^3/15`, а `Omega_7_gt_Omega_6` и `Omega_7_gt_Omega_8` доказывают строгие сравнения с соседними целыми размерностями.

## Hagi/Probability/StationaryFlatness.lean
- `tail_sum_identity`: для натуральнозначного `X ≤ M` на конечном вероятностном пространстве `expectNat q X = ∑_{k<M} probGe q X (k+1)`.
- `sum_pow2_inv_le` при `N ≥ 1` даёт `∑_{k<N} (k+1)⁻¹^2 ≤ 2 - N⁻¹` через телескопическую оценку `inv_sq_le_sub_inv`.
- `flatness_moment_bound`: если `C ≥ 0` и каждый хвост `probGe q X (k+1) ≤ C*(k+1)⁻¹^2`, то `expectNat q X ≤ 2*C`. Связь этого вывода с обобщением модели не доказывается.

## Hagi/Runtime/BF16Delta.lean
- `Code` и `decode` задают все конечные BF16-коды с точным значением в `ℚ`,
  включая signed zeros и subnormals. `exists_IsNearest` строит ближайший код
  для каждого рационального аргумента без глобальной RNE/tie-breaking функции.
- `extreme_nearest_delta_loses_update`: при двух pointwise nearest-посылках
  обновление от anchor `2^127` к `129/128` может оказаться нулевым после
  nearest delta/recovery. Поэтому наивная rounded delta-write не сертифицируется.
- `exists_sameBinade_difference`: для положительных кодов с равным ненулевым
  exponent точная разность представима в обоих порядках, включая subnormal.

## Hagi/Runtime/ControllerGates.lean
- `logitRange_scale` при `tau > 0` даёт линейное масштабирование диапазона, `variance_gate_contract` при `tau ≥ 1` — сокращение квадратичной величины `range^2/8`, а `variance_gate_normalize` при `Rbar > 0` и `Rbar ≤ range f` нормализует диапазон ровно к `R̄`.
- `trust_region_proj_norm` при `R > 0` и `R ≤ ‖x‖` даёт норму `R` для `(R/‖x‖)•x`; `trust_region_nearest` доказывает, что эта точка является ближайшей к `x` среди всех `y` с `‖y‖ ≤ R`.
- `dynamic_branch_variance` при `L > 0` и `v ≥ 0` вычисляет сумму `L` одинаковых вкладов `((sqrt(2*L))⁻¹)^2*v` как `v/2`.

## Hagi/Runtime/TernaryExact.lean
- `qTern_error_in` при `s > 0` ограничивает ошибку внутри диапазона через `s/2`, а `qTern_error_out` вне его даёт точное `|x - qTern s x| = |x| - s`. `ternary_split_bound` разлагает полную квадратичную ошибку на сумму внутри диапазона и `satTail`.
- `ternary_split_le` даёт `∑ ошибок² ≤ n*(s/2)^2 + satTail`; `quant_energy_bridge_saturation` при `κ ≥ 0` и посылке `dE ≤ κ*sqrt(∑ошибок²)` выводит `dE ≤ κ*(sqrt n*s/2 + sqrt satTail)`.
- `no_saturation_recover` при условии `ternInRange` для всех координат возвращает одновременно глобальную оценку `κ*sqrt n*s/2` и поэлементные границы `s/2`.

## Hagi/Sparsity/SparseStep0.lean
- `sparse_step0`: для ортонормированного семейства `v`, `tol ≥ 0` и строгого условия `∑_{i∈sᶜ} c i^2 < tol^2` норма разности полной и сохранённой сумм строго меньше tol.
- Оценка не зависит от числа отброшенных индексов: вся их совместная энергия уже учтена в посылке htail.

## Hagi/Spectral/RankGrowth.lean
- `rank_orthogonal_growth`: если строки `R` линейно независимы и `OrthRows M R`, то ранг `stackRows M R` равен `M.rank + Fintype.card k`.
- `span_growth_zero_interference`: если каждая новая строка `u j` ортогональна каждой `g i`, то любой `d` из линейной оболочки `u` также ортогонален всем `g i`.

## Hagi/StatMech/Hopfield/CharPatterns.lean
- `charEnergy_eq` доказывает `charEnergy v = dotProduct v v / 2` через полный набор характеров.
- `spins_dot_self` вычисляет квадрат спинового вектора как `2^k`; `charEnergy_spins_flat` поэтому даёт одно и то же значение `2^k/2` для каждой спиновой конфигурации.
- Теорем о статистической сумме или свободной энергии этого полного характерного набора в файле нет; доказан именно плоский энергетический ландшафт.

## Hagi/StatMech/Hopfield/Concentration.lean
- `eunorm_spins` равен `sqrt N`, а `energy_le_frob` при `NeZero N` ограничивает энергию любой конфигурации через `frobSq J / 2`.
- Для `beta ≥ 0` теорема `partition_le` даёт `partition ≤ 2^N * exp(beta*frobSq J/2)`.
- `freeEnergy_le` при тех же условиях ограничивает плотность свободной энергии через `log 2 + beta*frobSq J/(2*N)`.

## Hagi/StatMech/Hopfield/LowerBound.lean
- `exists_max_energy` при `N > 0` доказывает существование спиновой конфигурации с максимальной энергией; `partition_ge_witness` для любого `sigma₀` даёт `exp(beta*energy sigma₀) ≤ partition`.
- `freeEnergy_ge_max` при `NeZero N` и `beta ≥ 0` выбирает максимизатор для нижней оценки плотности свободной энергии, а `freeEnergy_sandwich` добавляет верхнюю границу Фробениуса.
- Результат существования конечного максимизатора не является утверждением об исполняемом алгоритме его поиска.

## Hagi/StatMech/Hopfield/Model.lean
- В конечном объёме определены спины `Fin N → Bool`, энергия `energy N K J σ`, статистическая сумма и плотность свободной энергии; термодинамический предел не вводится.
- `partition_pos` доказывает положительность статистической суммы при любом `β`; при `beta ≥ 0` теорема `partition_ge_univ` даёт `2^N ≤ partition N K beta J`.

## Hagi/StatMech/Hopfield/SubMemory.lean
- `subsetEnergy_eq` выражает энергию подмножества как `(∑_{w∈S} dotProduct (charProjR w v) (charProjR w v))/2`.
- `subset_plus_complement` доказывает `subsetEnergy S v + subsetEnergy Sᶜ v = dotProduct v v/2`.
- `subset_le_full` даёт `subsetEnergy S v ≤ dotProduct v v/2`; энергия перераспределяется между `S` и дополнением, а не создаётся.

## Hagi/State/TrainState.lean
- Статус файла преимущественно состоит из определений носителей: `TrainState` объединяет `ModelState`, `OptimizerState`, `MemoryState`, `ResourceState`, `SafetyState` и пятиканальный `QualityVector`. Поля фиксируют веса, адаптеры, версии, моменты, память и численные ресурсы без доказательства физической стоимости.
- `energy` — сумма квадратов весов и адаптеров, `capability` — `mem.consolidated`, `riskOf`, `budgetOf`, `costOf` проецируют соответствующие поля, а `evaluate` возвращает `S.qual` покомпонентно.
- `FloorHeld S floor` означает `∀ i, floor i ≤ evaluate S i`. Пример в источнике доказывает, что неравство суммы нижних границ с `qualityScalar` не влечёт это покомпонентное условие.

## Hagi/State/Transition.lean
- `trainStep_quality_unchanged` и `trainStep_evaluate_unchanged` оставляют качество и его покомпонентное значение неизменными. `trainStep_energy_identity` даёт точный квадратичный закон энергии; `trainStep_energy_descent` требует `eta > 0` и `2*∑weights*grad > eta*∑grad^2`.
- `guided_loss_identity` равен `(1-eta)^2*lossOf S tgt`; `guided_loss_descent` даёт строгое уменьшение при `0 < eta < 2` и положительном исходном значении функции потерь.
- `trainStep_write_semantics` обновляет выбранную строку памяти и увеличивает `mem.consolidated` на `1`. При отсутствии записи память сохраняется, а при записи по адресу `i` остальные адреса не меняются по `trainStep_foreign_address_intact`.

## Hagi/Step/ArmijoAcceptance.lean
- `armijo_sufficient_decrease`: из направленности `⟪g,d⟫ ≤ -c1*‖d‖^2`, `c1 > 0`, `alpha > 0` и квадратичной гладкости следует `J(alpha•d) ≤ J 0 - (c1 - L*alpha/2)*alpha*‖d‖^2`.
- `armijo_step_size` добавляет `L ≥ 0` и `alpha ≤ c1/L` и получает упрощённую гарантию `J(alpha•d) ≤ J 0 - (c1/2)*alpha*‖d‖^2`. Это одношаговая оценка при заданной посылке гладкости.

## Hagi/Step/BatchBudget.lean
- `noiseEps_sq` при `m > 0`, `sigma ≥ 0`, `0 < delta ≤ card K` вычисляет `noiseEps^2 = sigma^2*‖d‖^2*(2*log(card K/delta)/m)`.
- `batch_noise_floor`: при `μ > 0` и `m0^2 ≤ 2*μ*ε/3` выполнено `3*m0^2/(2*μ) ≤ ε`.
- `batch_terminal_gap` уже предполагает `hgoal : noiseEps^2 ≤ 2*μ*eps/3` и подставляет формулу шума в эту цель. Отдельной теоремы о выборе минимального `m` по заданному `eps` в файле нет.

## Hagi/Step/CPUFreeze.lean
- `cpu_frozen` по определению `safeStep` возвращает нулевую CPU-компоненту обновления.
- `norm_le` доказывает, что сумма квадратов CPU и остальных координат после обнуления не превышает исходную.
- `anchor_drift` точно равняет скалярный дрейф безопасного шага дрейфу только оставшейся компоненты: CPU-часть не вносит вклада.

## Hagi/Step/CausalFilter.lean
- `gqa_shared_score` при `Km q = Kv (g.kvOf q)` доказывает равенство оценок внимания GQA и MHA; сюръективная группировка `GQA` даёт `gqa_cache_card : card KV ≤ card Q`.
- Для скользящего окна `swa_reach_eq` равен `L*(W-1)+1`, `swa_reach_mono` монотонен при `W ≥ 2`, а `swa_cost_bound` при `1 ≤ W ≤ T` заключает сумму `min (t+1) W` между `(T-W)*W` и `T*W`.
- `causal_prefix_determined` доказывает зависимость выхода только от входа до `t`. `leak_same_step` при `w 0 ≠ 0` показывает, что изменение входа в точке `t+1` добавляет к `centeredConv` в момент `t` ровно `w 0*c`.

## Hagi/Step/Compound.lean
- `compound_c_stabilizes` при `α > 0`, `D,J ≥ 0`, `D < G0`, `ε > 0`, измеренных оценках `c t ≤ α*G t + J`, `G t ≤ D + (G0-D)*a^t` и `a^1 ≤ ε/(α*(G0-D))` ограничивает именно `c 1` через `α*D + J + ε`.
- `compound_constant_regime`: при `D,J,δ ≥ 0` и `|G t-D| ≤ δ` для `t ≥ 1` аналогичная оценка верна для каждого такого `t`. `compound_trajectory` при `0 ≤ ρ < 1`, `D ≥ 0` и рекурсии `G(t+1) ≤ ρ*G t + D` ограничивает суммарный вклад через замкнутую геометрическую траекторию.
- `compound_cumulative` из `c t ≤ C` выводит `M₀ - ∑c ≥ M₀-k*C`; `compound_budget_interval` и `compound_fold_interval` переносят бюджетные неравенства через указанные нижние и верхние концы интервалов.

## Hagi/Step/Dominate.lean
- `domination_decompose` раскладывает `⟪gi,d⟫` на компоненту вдоль `gs` и остаток. При положительных нормах, `‖d‖*‖gs‖/2 ≤ ⟪d,gs⟫` и `⟪gi,gs⟫ ≤ -‖gi‖*‖gs‖/4` теорема `domination_regression` ограничивает выровненный член указанным отрицательным выражением.
- `safe_consensus_harmless`: если `⟪gi,gs⟫ ≥ 0` и `d = c•gs` с `c ≥ 0`, то `⟪gi,d⟫ ≥ 0`; `dominated_collateral_bound` при отрицательном `⟪gi,gs⟫` и `c > 0` даёт строго отрицательный результат.
- `guard_weight_parity` при `ns > 0`, `nr > 0` доказывает `(nr/(ns+nr))*ns = (1-nr/(ns+nr))*nr`.

## Hagi/Step/FrobeniusLMO.lean
- `sgd_stable_step`: при `G ≠ 0`, `eta > 0`, `lam > 0`, квадратичной верхней оценке и `eta < 2*⟪G,G⟫/(lam*‖G‖^2)` получается `L' < L`.
- `muon_stable_step` использует `⟪G,O⟫ = sigmaSum`, `‖O‖^2 = m`, `m > 0` и `eta < 2*sigmaSum/(lam*m)` для того же строгого вывода. `muon_avg_not_max` при `m > 0`, `0 ≤ sigmaMax` и `sigmaSum ≤ m*sigmaMax` даёт `sigmaSum/m ≤ sigmaMax`.
- `lmo_lower_bound` при `‖D‖ ≤ eta` даёт `-eta*‖G‖ ≤ ⟪G,D⟫`; `lmo_attained` при `eta ≥ 0`, `G ≠ 0` показывает, что `D = -(eta/‖G‖)•G` удовлетворяет ограничению и достигает равенства.

## Hagi/Step/GPM.lean
- `gpm_zero_forgetting`: при `gpmOrth ΔW xs` для любого `W` и каждого старого входа `(W+ΔW)*ᵥxs k = W*ᵥxs k`.
- `sigma_orth_zero`: если `ΔW*ᵥxs k = 0` для всех `k`, то `ΔW * actSigma xs = 0`.
- `sigma_orth_necessary`: если для каждой строки сумма квадратов скалярных откликов равна нулю, то каждый `ΔW*ᵥxs k = 0`. Это точные матричные утверждения без переноса на глубокую сеть.

## Hagi/Step/GradCentralization.lean
- `gc_zero_sum` доказывает нулевую сумму центрированного градиента; `gc_pythagoras` даёт `∑g^2 = ∑(gc g)^2 + card V*(popMean g)^2`.
- `gc_norm_le` в квадратичной форме показывает, что центрирование не увеличивает сумму квадратов; `gc_const_zero` переводит любой постоянный градиент в нулевую функцию.

## Hagi/Step/GradClip.lean
- `clip_norm_le` при `R ≥ 0` даёт `‖clip R g‖ ≤ R`; `clip_eq_of_le` оставляет `g` на месте при `‖g‖ ≤ R`, а `clip_idem` доказывает идемпотентность при `R ≥ 0`.
- `clip_dir` при `R > 0` и `R < ‖g‖` представляет результат как `c•g` с `c > 0`.
- `clip_descent_pos`: если дополнительно `0 < ∑g i*d i`, то и после отсечения `0 < ∑clip R g i*d i`.

## Hagi/Step/HybridState.lean
- `stale_momentum_bias`: если `slot = g0`, существует bias, для которого `slot = gt + bias` и `‖bias‖ = ‖g0-gt‖`; доказана только эта одношаговая алгебра.
- `fresh_momentum_unbiased` при `slot = gt` даёт `slot = gt + bias` с `‖bias‖ = 0`.

## Hagi/Step/Joint.lean
- `jointStep_conflict_regression`: при `L > 0`, `g ≠ 0`, `gc ⬝ᵥ g < 0`, двусторонней квадратичной посылке `-L*‖v‖² ≤ vᵀHc v ≤ L*‖v‖²` и `0 < lr < 2*|gc ⬝ᵥ g|/(L*‖g‖²)` приращение `quadIncr` строго положительно.
- `jointStep_regression_bound` при верхней квадратичной посылке ограничивает приращение через `|lr|*‖gc‖*‖g‖ + (L/2)*lr^2*‖g‖^2`.
- `trustRegion_bound` при `L ≥ 0` и `sqrt(δ ⬝ᵥ δ) ≤ R` даёт `quadIncr ≤ ‖gc‖*R + (L/2)*R^2`.

## Hagi/Step/JointPreserve.lean
- `diversity_noncollapse` фиксирует верхнюю траекторную оценку через стартовое разнообразие и геометрическую сумму инъекций; сама по себе она не даёт положительного нижнего порога.
- `diversity_floor`: из `D(t+1) ≥ ρ*D t + inj - xi` и `ρ ≥ 0` следует `D T ≥ ρ^T*D 0 + (inj-xi)*∑_{i<T}ρ^i`.
- `diversity_floor_fresh` при `ρ > 0`, `D 0 ≥ 0` и `xi < inj` отбрасывает стартовый член с сохранением нижней границы. `diversity_floor_strict_pos` при `ρ ≥ 0`, `xi < inj` и `T ≠ 0` доказывает положительность `(inj-xi)*∑ρ^i`; вместе с `diversity_floor` это исключает нулевое `D T` при таких посылках.

## Hagi/Step/LazyAdam.lean
- `lazyDecay_exact` вычисляет `d`-кратную итерацию `x ↦ beta2*x` как `beta2^d*v0`; `dense_m_decay` даёт аналогичную формулу траектории момента.
- `lazyReplay_exact` — тождество распределения `beta2^d*(vstale + (1-beta2)*g^2)`, а не самостоятельное доказательство полной эквивалентности оптимизаторов. `supportSet_bound` ограничивает размер объединения трёх множеств суммой размеров.
- `lazy_moment_drift` при `0 ≤ beta1`, `|m 0| ≤ M` и рекурсии `m(t+1)=beta1*m t` даёт `|m d| ≤ |beta1^d|*M`; `lazy_momentum_bound` при `0 < beta < 1`, `c ≥ 0` ограничивает геометрическую сумму через `c*(beta/(1-beta))`.

## Hagi/Step/LiveDeltaSafe.lean
- `safe_update_window`: при `L i > 0`, `eps i ≥ 0`, `eta ≥ 0`, `d ≠ 0`, квадратичной посылке `h_lipline` и `eta ≤ safeqpEtaMax g eps L d` доказано `dL i ≤ eps i` для всех защищаемых целей.
- `updateNewest_base` сохраняет базу, `updateNewest_length` — число блоков, а `updateNewest_tail` — длину остатка списка после новейшего блока.
- `updateNewest_cost` — равенство двух вычисленных счётчиков размеров списка и матриц, а не измерение физической памяти или времени обновления.

## Hagi/Step/MDLThreeCurrency.lean
- `mdlObjective_delta` раскладывает изменение цели в изменение ошибки предсказания плюс `λ` на изменение длины описания.
- `mdlObjective_nonincreasing` при `lam ≥ 0` и невозрастании обеих частей доказывает невозрастание всей цели.
- `mdlObjective_tradeoff`: при `lam ≥ 0`, выигрыше предсказания не меньше `δ ≥ 0`, `0 < c` и кодовой добавке не более `δ-c` получается строгое улучшение с запасом `c`; `mdlObjective_lambda_zero` устраняет кодовую часть.

## Hagi/Step/Muon.lean
- `muon_step_bound` и квадратичный `muonDir_norm_sq_le`: если `‖P z‖ ≤ ‖z‖` для всех `z`, то `muonDir P g` не увеличивает норму и квадрат нормы.
- `MuonNS.ns_error_factor` даёт `1 - ns u = (u-1)^2*(u+2)/2`; на `0 < u ≤ 1` доказаны инвариант и монотонность, а на `0 < u < 1` — строгое `u < ns u < 1`.
- `MuonAlign.muon_alignment_optimal`: для `sig i ≥ 0` и комплексной `Q` с `Qᴴ*Q = 1` сумма `sig i*(Q i i).re` не превышает суммы `sig i`.

## Hagi/Step/NCEExact.lean
- `nce_decomposition`: при `0 < p v → 0 < q v` на поддержке `p` выполнено `log p = log q + log(p/q)`; `nce_correction_pos` доказывает положительность этой коррекции.
- `partEst_unbiased` при положительном нормированном `q` даёт `∑q*impW z q = partZ z`; `partEst_gap_jensen` и `jensen_log` ограничивают средний логарифм логарифмом `partZ z`.
- При положительном нормированном `q` теорема `secondMomentW_ge_sq` даёт `(partZ z)^2 ≤ secondMomentW z q`; `adaptiveK_bound` при `moment ≥ 0`, `eps > 0` и `moment/eps ≤ K` выводит `moment/K ≤ eps`.

## Hagi/Step/NewtonSchulzMatrix.lean
- `newton_polar_scalar_error` при `x > 0` даёт точное `newtonStep x - 1 = (x-1)^2/(2*x)`; одновременно `newtonStep x ≥ 1`. На ветви `x ≥ 1` доказаны `newton_step_descent` и оценка ошибки `≤ (x-1)^2/2`.
- `newton_polar_convergence` для любого `x₀ ≥ 1` и конечного `T` даёт `|newtonIter x₀ T - 1| ≤ 2*((x₀-1)/2)^(2^T)`, а `newton_iter_bracket` сохраняет `1 ≤ iter ≤ x₀`.
- Предельный результат `newton_polar_tendsto_one` доказан только при `1 ≤ x₀ < 3`. Конечная формула сама по себе не расширяет эту область сходимости на произвольный `x₀`.

## Hagi/Step/NoisyPL.lean
- `variable_telescope`: если `0 ≤ c t ≤ c0 < 1`, `d ≥ 0`, `e 0 ≤ e₀` и `e(t+1) ≤ c t*e t + d`, то `e t ≤ (∏_{k<t}c k)*e₀ + d/(1-c0)`.
- `noisy_recurrence_telescope` — постоянная версия с `0 ≤ c < 1` и границей `c^t*e₀ + d/(1-c)`.
- `noisy_pl_convergence` требует `0 < μ ≤ L`, `m ≥ 0`, `Estar ≤ e t`, заданное одношаговое убывание, PL-неравенство и `3*m^2 ≤ G t` на каждом шаге. Тогда `e t ≤ Estar + (1-μ/(16L))^t*(e 0-Estar) + 3*m^2/(2*μ)`.

## Hagi/Step/PreconditionerDescent.lean
- `preconditioned_descent`: при `L ≥ 0`, `mu > 0`, `alpha > 0`, `alpha < 2*mu/L`, коэрцитивности `mu*‖u‖² ≤ ⟪g,u⟫` и квадратичной гладкости получается оценка с множителем `alpha*(mu-L*alpha/2)*‖u‖²`.
- `preconditioned_step_size` при `alpha ≤ mu/L` упрощает её до `J(-alpha•u) ≤ J 0 - (mu/2)*alpha*‖u‖²`. Обе теоремы работают с посылкой на заданный шаг, а не с универсальным предобусловливателем.

## Hagi/Step/ProjectionDescent.lean
- `min_dist_to_vi`: для выпуклого `C`, `ds ∈ C` и минимальности `dist ds g0` среди всех `d ∈ C` выполнено `⟪g0-ds,w-ds⟫ ≤ 0` для всех `w ∈ C`.
- `safeQP_descent` добавляет `0 ∈ C` и доказывает одновременно `‖ds‖² ≤ ⟪g0,ds⟫` и `‖g0-ds‖ ≤ ‖g0‖`.
- `joint_stage_linked`: при тех же условиях проекции, `L > 0`, `0 ≤ eta ≤ 1/L` и заданной квадратичной посылке на `E2` получается `E2 ≤ E1 - eta*‖ds‖²/2`.

## Hagi/Step/RiemannNewtonPolar.lean
- `radial_tangential_curvature`: при `r > 0`, глобальных `HasDerivAt φ (g x) x` и `HasDerivAt g (gg x) x` производная по `s` от `deriv (fun s' => φ (sqrt(r^2+s'^2))) s` в нуле равна `g r/r`.
- Доказана эта тангенциальная вторая производная радиальной функции; полная матрица ковариантного гессиана и динамика итерации Ньютона здесь не формализованы.

## Hagi/Step/RobustDescent.lean
- `biased_norm_upper` и `biased_inner_lower`: из `‖ĝ-g‖ ≤ m` следуют `‖ĝ‖ ≤ ‖g‖+m` и `(‖g‖²-m²)/2 ≤ ⟪g,ĝ⟫`.
- `robust_descent_step`: при `eta ≥ 0`, `L ≥ 0` и квадратичной посылке hquad получается `J(x-eta•ĝ) ≤ J x - eta*(‖g‖²-m²)/2 + L*eta²*(‖g‖+m)²/2`.

## Hagi/Step/SNRWeights.lean
- `uniform_is_mean` переписывает сумму `(1/r)*(dev i)^2` как `(∑dev i^2)/r`; условие `r > 0` в самом тождестве не требуется из-за тотализации деления Lean.
- `focused_beats_uniform`: если `mean = (∑dev i^2)/r` и для некоторого `j` выполнено `(dev j)^2 < mean`, существуют `v i ≥ 0` с `∑v = 1`, для которых `∑v i*(dev i)^2 < (∑dev i^2)/r`.
- Доказано существование такого распределения весов, а не его построение конкретным преобразованием или улучшение траектории оптимизации.

## Hagi/Step/SafeQP.lean
- Минибатч-оценка `ĝᵢ = gᵢ + m⁻¹Σⱼ ξᵢⱼ` имеет точную проекцию
  `⟪ĝᵢ,d⟫ = ⟪gᵢ,d⟫ + m⁻¹Σⱼ⟪ξᵢⱼ,d⟫`.
  При фиксированном `d ≠ 0`, `σ > 0`, `0 < δ < 1` и измеримых, центрированных,
  независимых по `j < m` проекциях с `‖ξᵢⱼ‖ ≤ σ`,
  `stochastic_safeQP_feasibility` переносит оценочные ограничения
  `−eps i ≤ ⟪ĝᵢ,d⟫` в истинные `−(eps i + noiseEps) ≤ ⟪gᵢ,d⟫`
  с вероятностью не менее `1 − δ`.
- Здесь `noiseEps = σ‖d‖√(2 log(|K|/δ)/m)`.
  `lr_batch_equivalence` даёт точное тождество
  `(k eta)·noiseEps(m) = eta·noiseEps(k²m)` в смысле преобразования
  `(eta,m) ↦ (k·eta,k²·m)` при `k,m > 0`; это тождество шумового бюджета,
  не утверждение о времени обучения.
- `latticeNet_covers`: при `n > 0`, `D ≥ 0`, `epsDir > 0`, `D*sqrt n/epsDir + 1 ≤ M` и `‖x‖ ≤ D` существует точка сетки на расстоянии не более `ε_dir`; `latticeNet_card_le` ограничивает размер через `(2*M+1)^n`.

## Hagi/Step/SafeQPStep.lean
- `safeqp_eta_max_conflict_free`: при `L i > 0`, `eps i ≥ 0`, `0 ≤ eta`,
  `d ≠ 0`, `⟪g i,d⟫ ≥ 0` и линейной оценке
  `dL i ≤ −eta⟪g i,d⟫ + L i·eta²‖d‖²/2`
  условие `eta ≤ safeqpEtaMaxConflictFree eps L d` даёт `dL i ≤ eps i`.
- Граница `safeqpEtaMaxConflictFree` эквивалентна одновременным условиям
  `eta ≤ 1` и `eta ≤ 2·eps i/(L i·‖d‖²)` для всех `i`; при `eps i > 0`
  она строго положительна.

## Hagi/Step/SignSGD.lean
- `sign_inner_nonneg`: для каждого конечного `g`
  `Σᵢ sign(gᵢ)gᵢ = Σᵢ |gᵢ| ≥ 0`.
- `sign_inner_pos`: если хотя бы одна координата `gᵢ` ненулевая, эта сумма
  строго положительна.
- `sign_idempotent`: повторная знаковая компрессия не меняет результат;
  каждая координата принадлежит `{−1,0,1}`.

## Hagi/Step/Upgrades.lean
- `skip_bound`: если `p = softmaxW s` — распределение и масса `δ`
  пропущенного множества меньше `1`, после удаления этого множества и
  перенормировки сумма абсолютных изменений весов не превосходит `2δ`.
- `readPolicy_exists` выражает существование максимума конечного набора
  вариантов для функции выигрыша от чтения.
- `sink_cost_bound` повторяет ту же оценку `2δ` для перенормированного
  распределения после отбрасывания массы `δ`; `sink_window_substitutes`
  из `T > 0` и `T(W+S)=C` получает `W+S=C/T`.

## Hagi/Step/WarmupSchedule.lean
- `warmup_eta_monotone`: при `c ≥ 0`, `ρ,Kρ > 0` и `0 < Δ' ≤ Δ`
  выполняется `warmupEta(Δ) ≤ warmupEta(Δ')`.
- `warmup_telescope_bound`: если `0 < T`, `Δ t ≥ 0`, `eta t ≥ 0` и
  `Δ(t+1) ≤ Δt − eta t·g t²/2` для `t < T`, то существует `t < T` с
  `g t²·Σ_{j<T}eta j ≤ 2Δ0`.
- `warmup_beats_constant`: для неубывающей последовательности шагов
  `T·eta 0 ≤ Σ_{t<T}eta t`; это сравнение двух полученных границ,
  а не доказательство общего ускорения обучения.

## Hagi/Step/WeightDecay.lean
- `wd_norm_bound`: при `λ > 0`, `0 ≤ eta λ ≤ 1`, `‖g t‖ ≤ G`
  и рекуррентности `w(t+1) = (1−etaλ)w(t) − eta·g(t)`
  для всех `t` выполняется `‖w t‖ ≤ max(‖w 0‖,G/λ)`.

## Hagi/System/Certificates.lean
- `cycle_certificate_sound`: при `lam,nu ≥ 0`, согласованной цепочке
  сертификатов и условии
  `lam(Rgrow+Rmerge+Rjoint) + nu·epsQ ≤
    gap + eta·inner − L·eta²dnorm²/2 − κqerr`,
  конечный потенциал `E + lam·R + nu·max(0,qTarget−q)` не превышает начального.
- Тип `StageCycleCertChain` фиксирует совпадение начальных энергий
  последующих стадий с конечными энергиями предыдущих; условие не следует
  только из наличия полей сертификатов — нужна показанная цена hprice.

## Hagi/System/GrowthState.lean
- Определение `joint` задаёт именно `params' = params − eta·stepDir`,
  `energy' = effects.jointEnergy`,
  `protectedRisk' = protectedRisk + effects.jointRisk` и
  `budget' = budget − effects.jointCost`; `potential S = energy + protectedRisk`.
- `potential_joint`: при `0 < L`, `0 ≤ eta ≤ 1/L`,
  `‖stepDir‖² ≤ ⟪grad,stepDir⟫` и измеряемой квадратичной оценке
  `S.effects.jointEnergy` получается
  `potential(joint S) − potential S ≤ −gainJoint S + riskJoint S`.
  Аналогичные измеряемые предпосылки grow/merge и
  `0 ≤ S.gap`, `0 ≤ κ,s`, `0 ≤ quantErr ≤ 1/2`, граница `h_emp_lip` нужны для
  `growth_cycle_potential` и `certificate_sound`.
- `protected_generation_budget`: если для всех `t < T`
  `reg(t+1)−reg t ≤ epsReg` и `spend(t+1)−spend t ≤ b`, то
  `reg T−reg 0 ≤ T·epsReg` и `spend T−spend 0 ≤ T·b`.

## Hagi/System/StepCertificate.lean
- `stepCertificate_base`: базовая часть сертификата, построенного по
  состоянию и `epsG ≥ 0`, совпадает с `verify S`.
- `safe_feasible_selection_productive`: если список содержит допустимый по
  заданным `riskLim,budgetLim` кандидат с `decrease > 0`, то максимум
  `bestFeasibleDecrease` по допустимым кандидатам тоже положителен.

## Hagi/System/UnifiedStep.lean
- `unified_step_budget`: при `Δ,Tt > 0` гиббсовы веса дают ожидаемую
  потерю не выше `m + Tt·log|ι|` для некоторой нижней границы `m` всех потерь,
  а ошибка `gridQ` композитного обновления не превышает `Δ/2`.
- `unified_step_certificate` одновременно фиксирует положительную нормировку
  гиббсовых весов и ту же решётчатую ошибку для фактического композитного шага.
- `quantized_descent_telescope`: при `Δ > 0` и фактических обновлениях
  `x(t+1) = gridQ Δ (x t − γg t)` для `t < T` выполняется
  `x T ≤ x 0 − Σ_{t<T}γg t + T·Δ/2`.

## Hagi/Research/Legacy/AdvanceWitness.lean
- `certified_invariant_advance_witness`: на горизонте `2` фактические поля
  траектории удовлетворяют `CertifiedHAGIInvariant` с `alpha=1`;
  capability проходит `1→2→4`, бюджет `100→98→96`.
- `witness_step_landauer_cap` и `witness_horizon_landauer_cap`:
  при `cUnit > 0` из принятых ограничений `cUnit·F ≤ 2` и
  `cUnit·F ≤ 100` соответственно следуют `F ≤ 2/cUnit` и `F ≤ 100/cUnit`.
  Это арифметические следствия заданных цен, а не измерение памяти.

## Hagi/Unified/AnytimeMartingale.lean
- `merge_stage_linked`: при `w t ≥ 0` и `Σt w t = 1` взвешенная
  categorical CE среднего логита не превосходит взвешенного среднего CE
  отдельных логитов.
- `anytime_safety`: если `δ0 ≥ 0`, `Good t` измеримы, `ρ∈[0,1)`,
  `μ((Good t)ᶜ) ≤ δ0ρᵗ` и `δ0/(1−ρ) ≤ δ`, то вероятность
  одновременного выполнения всех `Good t` для `t ≤ T` не меньше `1−δ`.
- `anytime_safety_stochastic` применяет это к минибатч-ограничениям с
  измеримыми центрированными независимыми шумами, `δ0,ρ ∈ (0,1)` и
  `δ0/(1−ρ) ≤ δ < 1`, `δ > 0` и шумовыми поправками на каждом шаге.

## Hagi/Unified/StitchingEProcess.lean
- `stitchedMaster w E = Σ i, w i • E i`; `stitching_master_supermartingale`:
  a finite family of supermartingales with nonnegative weights stitches
  into a supermartingale (Finset-induction, Mathlib canon
  Mathlib Supermartingale.add / Supermartingale.smul_nonneg; the
  empty case is gated by
  `[Nonempty k]` — the zero-process certificate needs an unavailable
  norm instance on the bare Pi type).
- `stitching_master_initial_mass`: μ[M₀] = Σ w i · μ[E i 0]
  (integrability from `Supermartingale.integrable`).
- `stitching_eprocess_anytime` (MAIN): for weights Σ ≤ 1 and
  unit-budget experts (μ[E i 0] ≤ 1, the hE0 premise):
  μ.real{∃t ≤ n, δ⁻¹ ≤ M_t} ≤ δ uniformly in n — direct corollary of
  `ville_anytime_false_alarm` (no duplication of the Ville
  stopping-time proof). The countable family is postponed (documented):
  the 3b slow-gate commits on finitely many e-processes.

## Hagi/Unified/CountableStitching.lean (C295, P4 E3)
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
- `stitching_countable_ville` (MAIN): Summable w, ∑' w ≤ 1,
  точечная суммируемость смеси, μ[E k 0] ≤ 1 →
  μ.real{∃t ≤ n, δ⁻¹ ≤ Mₜ} ≤ δ равномерно по n — та же форма, что
  конечный `stitching_eprocess_anytime`. Маршрут редукции
  (аудит C295): существующая конструкция смешивает ВСЕ компоненты
  во ВСЕ моменты времени (без activation-schedule), поэтому
  честная редукция — монотонные конечные префиксы: строгий
  level-c аларм лежит в возрастающем объединении конечных алармов,
  каждый ограничен конечной теоремой на Fin (K+1); непрерывность
  снизу (`Monotone.measure_iUnion`) + архимедово сжатие дают порог
  δ. Конечный движок переиспользован дословно.

## Hagi/Architecture/SpaceDecoupling.lean
- `projI U = U·Uᵀ`, `projR U = 1 − U·Uᵀ`; `projI_add_projR`
  (P_I + P_R = 1 exactly), `projI_idem`/`projR_idem`
  (idempotence under `IsOrthoCol U`).
- `spaceDecoupling_zero_drift`: an update Δ with Uᵀ·Δ = 0 leaves the
  I-coordinates of any state exactly (Uᵀ(x+Δ) = Uᵀx) — the
  projection-level twin of GPM `gpm_zero_forgetting`.
- `exists_orth_direction`: for rank(I) = c < d the complement is
  nontrivial (∃ v ≠ 0, Uᵀv = 0; finrank-contradiction — an injective
  Fin d → Fin c linear map cannot exist).

## Hagi/Research/Legacy/ArchitectureTheorem.lean
- `entropy_continuity_pinsker`: если уже доказана граница
  `|H(p)−H(q)| ≤ τ log(|V|−1) + h₂(τ)`, а также `0 ≤ τ ≤ 1/2`,
  `τ ≤ √(kl/2) ≤ 1/2`, `log(|V|−1) ≥ 0` и монотонность `binEnt`
  на данном отрезке, то получается та же граница с `√(kl/2)` вместо `τ`.
- `saturation_law_forced`: двусторонние неравенства capability относительно
  одного и того же `C t + σ(Cstar−C t)` влекут точное равенство преемника
  этому выражению.
- `cert_horizon_log_bound`: при положительных `γ,k,σ,Cstar,C0`,
  `(γk+σ)C0 < σCstar`, шагах роста, насыщения и конуса
  получается `(T−1)log(1+γk) ≤ log(σCstar) − log((γk+σ)C0)`.

## Hagi/Research/Legacy/Assumptions.lean
- `masterhagi_trunc_of_assumptions`: пакет `Trunc S lam nu Qtarget Emin T`
  заменяет стадийные, бюджетные и нижние энергетические предпосылки;
  при отдельных SafeQP-окнах и усечённых законах роста он даёт тот же
  `CertifiedHAGIInvariant`.
- `premises_to_certified` при `alpha ≥ 0`, `gamma > 0`, `rho ≥ 0`,
  `C t > 0` получает инвариант из конуса
  `αC0/γ ≤ D0`, `C(t+1)=C t+G t`, `γD t ≤ G t`, производственной динамики,
  ограничений `C(t+1) ≤ (1+α)C t` и β-порога, а также из рискового,
  потенциального, бюджетного и probe-ограничений.
- `trunc_nonvacuous`: стационарная траектория показывает непустоту `Trunc`
  без утверждения о фактическом обучающем прогрессе.

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
- `capability_strict_first`: при положительной начальной capability и строгом
  условии `alpha·capability 0 < growGain 0` первый шаг строго превосходит
  `(1+alpha)·capability 0`.

## Hagi/Research/Legacy/CertifiedGrowth.lean
- `certified_gainprod_takeoff`: для `[0,1]`-наблюдений, `n,eps > 0`,
  `alpha,gamma,C0 > 0`, `rho ≥ 0`, начального конуса, принятого моста
  от средних к `γD t ≤ G t` и усечённых законов
  `C(t+1)=C t+G t`, `D'`, верхнего `(1+alpha)` и β-порога
  выполняется вероятностная импликация:
  из всех margins `ΣX + 2n eps ≤ ΣY` для `t < T`
  следует `C0(1+alpha)^T ≤ C T` с нижней оценкой вероятности
  `1 − 2T·exp(−2n·eps²)`.
- `certified_band_growth`: для `0 < σ ≤ 1`, `C(t+1)=C t+G t`
  и предложенного моста `b(1−σ)^t ≤ G t` аналогичная вероятность относится
  к выводу `C T ≥ C0 + b(1−(1−σ)^T)/σ`.

## Hagi/Unified/CertifiedLoop.lean
- `certified_loop`: если начальный `FloorKept` и `0 ≤ b 0` даны, а каждое
  звено — `StepCert`, то сумма `(certs t).trans.objectiveDrop` не превосходит фактического
  убывания `obj(f 0)−obj(f n)`, финальное качество удовлетворяет floor,
  `b n ≥ 0` и `b n ≤ b 0 − Σ budgetSpend`.
- `certified_loop_all` сохраняет компонентный floor на каждом `t ≤ n`;
  `certified_loop_strict` при `n ≥ 1` дополнительно даёт
  `obj(f n) < obj(f 0)`.
- `certified_loop_risk`: суммарный `(certs t).riskSpend` не превосходит
  `n·riskLim` по индивидуальным ограничениям звеньев.

- `certified_loop_kernel` — КАПСТОН НА ЯДРЕ: bounded-цепь

## Hagi/Unified/CertifiedTrajectory.lean
- `certified_progress_honest`: при `decrease = claimed`,
  `Φ(t+1) ≤ Φt − decrease + riskCost`, `Φ_min ≤ Φt` для всех `t ≤ T`
  и заданном интервале `measured−δ ≤ claimed ≤ measured+δ` выполняется
  `Σ(measured−δ) ≤ Φ0 − Φ_min + ΣriskCost`.
- `certified_progress_signal`: если сумма `(ms t).measured` строго больше суммы `δ`,
  то суммарный заявленный спуск положителен и ограничен той же величиной
  `Φ0 − Φ_min + ΣriskCost`.

## Hagi/Unified/CommitGate.lean
- `commitProductive`: активный `gate c` влечёт `commitV c < c.V`;
  `holdSafe` даёт точное равенство `holdV c = c.V`.
- `quant_bound_of_gridQ`: при `Δ > 0` сумма квадратов ошибок решётки
  не превосходит `|k|·Δ²/4`.

## Hagi/Research/Legacy/CorePremisesDerived.lean
- `core_premises_joint_operational` и `core_premises_compress_operational`
  выводят квадратичный joint и квантованный compress из дифференцируемости,
  ограничений производной и операциональных равенств энергий, а не из
  свободно назначенных полей.
- `MasterHAGICoreOperational_v2` для скалярного состояния доказывает
  убывание `hagiPotential` и бюджетный учёт. Кроме grow/merge,
  качественных и переходных предпосылок требуются `lam,gap ≥ 0`,
  `nu ≥ 0`, `epsQ ≥ 0`, `sp.L > 0`, `0 ≤ sp.eta ≤ 1/sp.L`, выравнивание направления,
  `0 ≤ sp.kappa,sp.s`, дифференцируемость, `L`-гладкость производной,
  её непрерывность вдоль направления, `‖∇E‖ ≤ κ`, `Δ > 0`, `Δ ≤ 1`,
  `sp.s = 1` и точные определения ошибок.
- `MasterHAGICoreOperational_v3` — тот же результат с формой посылок,
  где distortions получены из решётки при `Δ ≤ 1`; это не устранение
  остальных измеряемых grow/merge или качественных условий.

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
- `verify_family_telescope`: если дополнительно `0 ≤ eta`, `0 ≤ κ,s`
  и `quantErr ≤ 1/2` на каждом шаге, то сумма `verify(S(t+1)).decrease`
  ограничена тем же фактическим убыванием.
Секция CertUnify (файл Hagi/Unified/CertUnify.lean удалён в C245, Phase 1: контент слит в этот файл, namespace `Hagi.Unified.CertUnify` сохранён, statements байт-идентичны):
- `tc_consequence`: из цепочки `StepCert` и нижней границы
  `Φ_min ≤ obj(f t)` для всех `t ≤ n` следует
  `Σ objectiveDrop ≤ obj(f 0) − Φ_min + Σ riskSpend`.

## Hagi/Unified/DerivAlong.lean
- C233 (R2): `ceStepLogitRange_sq_le_featureMass_sq_norm_sq` — острая по-примерная `ceStepLogitRange² ≤ 4·featureAbsSum²·‖ceDirection‖²`; `ceStepLogitQuad_le_engine` — `(eta·R'ᵢ)²/8 ≤ featureAbsSum²·eta²·‖D‖²/2` (острый квадратичный член не хуже engine); `jointEnergy_le_ceLinear_logitRange` — заострённая точечная majorant `jointEnergy ≤ S.energy − eta·⟪grad,stepDir⟫ + (eta·ceStepLogitRange)²/8` на тех же посылках, что `potential_joint_of_ceLinear_residualDirection` (C216-мажоризатор `ceOneHot_next_le_rangeMajorizer`).
- `lip_energy_from_gradient`: если `E` всюду дифференцируема и
  `‖fderiv E w‖ ≤ κ`, то `|E w−E q| ≤ κ‖w−q‖` для любых `w,q`.
- `smooth_from_lipschitz_gradient`: при дифференцируемости,
  `‖fderiv E y−fderiv E x‖ ≤ L‖y−x‖` и непрерывности производной вдоль
  сегмента получается
  `E(q+dir) ≤ E q + fderiv E q dir + L‖dir‖²/2`.

## Hagi/Unified/DescentCore.lean
- `descent_drop`: в `Objective` с `L > 0` и заданной descent-леммой,
  если `‖dir‖² ≤ ⟪grad x,dir⟫` и `0 < eta ≤ 1/L`, то
  `f(x−eta·dir) ≤ f x − eta(1−L·eta/2)‖dir‖²`.

## Hagi/Unified/DescentCoreDiag.lean
- `diag_descent_eq`: для `diagE a y x = ½Σᵢaᵢ(xᵢ−yᵢ)²`
  доказано точное разложение
  `E(x+d) = E x + ⟪a∘(x−y),d⟫ + ½Σᵢaᵢdᵢ²`.
- `diag_descent_le`: если `0 ≤ a i ≤ L` для всех `i` и `L > 0`,
  то квадратичный член не превосходит `L/2·‖d‖²`, что даёт `L`-гладкость
  этой конкретной диагональной цели.

## Hagi/Unified/DescentCoreQuad.lean
- `quad_eta_identity`: для `quadE a w = ½Σᵢ(wᵢ−aᵢ)²` и градиента
  `w−a` выполняется `quadE(w−eta·grad) = (1−eta)²quadE a w`
  (мост над `Hagi.Foundations.quad_eta_identity` из
  Hagi/Math/Foundations/QuadEta.lean — та же идея на носителе Unified).
- `quad_eta_descent`: при `0 < eta < 2` и `quadE a w > 0` энергия строго
  убывает; при `eta=1` тождество даёт нулевую энергию только для этой цели.

## Hagi/Unified/Distillation.lean
- `soft_dial_max` и `soft_dial_zero`: `softProb x → 1` при `x→+∞` и
  `softProb x → 1/2` при `x→0`.
- `soft_entropy_bound`: для `0 < p < 1` двоичная энтропия не превосходит
  `log 2`.
- `attention_scale_softens`: `softProb(s/√n) → 1/2` по `n`;
  `attention_no_scale_saturates`: если `s > 0`, то `softProb(s·n) → 1`.

## Hagi/Theory/Compression.lean
- `ef_iterate_shadow`: при `e(t+1)=d t+e t−comp(d t+e t)`,
  рекуррентностях сжатой и полной траекторий с общим началом
  получается точное `xC n−xF n = eta·(e n−e 0)`.
- `thrComp_barrier`: квадрат нормы несжатого остатка порогового
  компрессора ограничен `|k|·τ²`.
- `thr_ef_quality`: для квадратичной цели, `0 < eta ≤ 1/2` и заданных
  EF-рекуррентностей энергия после `n` шагов ограничена
  `(1−2eta(1−eta/2))ⁿE0 + eta√(‖quadGrad a (quadGD a eta x0 n)‖²·|k|τ²)
    + eta²|k|τ²/2`.

## Hagi/Unified/EmpiricalPremises.lean
- `premises_give_smooth`: монитор `holds p`, условие
  `dnorm² ≤ inner` и отдельно принятая квадратичная модель hsmooth
  дают `E2 ≤ E1 − eta·dnorm²/2`; монитор сам модель не доказывает.
- `premises_lip_witness`: при `holds p` и `s ≥ 0` доказана только
  `0 ≤ κ·s·dnorm`, а не требуемая липшицева оценка энергии.
- `premises_noise_cases`: из `noiseSigma ≥ 0` следует лишь
  `noiseSigma = 0 ∨ noiseSigma > 0`.

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
### Hagi.Unified.ExecutableSelection — merged into ParetoExecution (C406)
- `auditedArgmin_fst`: инструментированный fold выбирает ровно тот же
  элемент, что `List.argmin` по заданной стоимости.
- `auditedArgmin_snd`: число сравнений равно `as.length − 1`;
  `auditedFilter_snd` насчитывает ровно один вызов составного guard
  на каждый входной элемент. Счётчики относятся к логическим вызовам.
### Hagi.Unified.ParetoLogit — merged into ParetoExecution (C404)
- `logit_budget_loop`: для рекуррентности
  `w(t+1)=w t+eta t/(1+exp(w t))`, `0 < eta t ≤ 2`,
  `b(t+1)=b t−eta t`, `0 ≤ eta t ≤ b t` и `0 ≤ b0`
  сохраняются качественные floors на всём пути, телескоп CE-спусков,
  неотрицательный и ограниченный бюджет; при `n ≥ 1` CE строго убывает.
- `logit_quadratic_bound`: при тех же рекуррентности и окне шагов
  `logitCE(w n) ≤ logitCE(w0) −
    Σ_{t<n}eta t·(1/(1+exp(w t)))²/2`.

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
- Если дополнительно `G t ≤ risk t`, `spend t,risk t ≥ 0`,
  `budget T = budget 0 − Σspend ≥ 0`, начальные качественные floors и
  покомпонентная монотонность qvec даны, то одновременно
  `C T−C0 ≤ Σrisk`, `budget T ≤ budget 0` и qfloor i ≤ qvec T i для всех i.
- `grand_synthesis` не принимает риск, q-вектор или q-floor и заключает только
  `C0(1+(beta⁴κ)k)^T ≤ C T` и `budget T ≤ budget 0`;
  `grand_synthesis_weak` дополнительно принимает локальные risk/probe условия
  и даёт соответствующие risk/qfloor выводы.

## Hagi/Training/GrowthComputedCert.lean
Именованных top-level theorem-деклараций нет; носители результата —
две definitions.
- `next S eta`: сохраняет все каналы `S`, кроме замены `S.weights`
  на `growthStep S.weights eta`.
- `stepCert`: при `0 < eta < 2` и `Σᵢ S.weightsᵢ² ≠ 0`
  создаёт `CertStep` с `drop = (1−(1−eta)²)growthQuad S.weights`.
  Его поля `CertStep.drop_pos` и `CertStep.actual` содержат доказательства положительности
  и фактического неравенства, но не являются отдельными top-level теоремами.
### Hagi.Unified.GuardedRobustLogit — merged into ParetoExecution (C404)
- `logitCE_guardedLogitNext_le`: для скалярной логистической модели
  выбранный преемник никогда не увеличивает `logitCE`; без estimated upgrade
  он равен текущему состоянию.
- `guardedLogitNext_eq_update_of_upgrade`: при `eta > 0`, ресурсных условиях
  `M ≥ 1`, `C ≥ 2` и активном guard преемник точно равен
  `w + eta/(1+exp w)`; `logitCE_guardedLogitNext_lt_of_upgrade`
  даёт его строгий спуск.
### Hagi.Unified.GuardedRobustResourceMin — merged into ParetoExecution (C404)
- `guardedMinimumResource_feasible`: при допустимом stay и односторонней
  ошибке базового действия выбранное действие остаётся в исходном `feasible`.
- `guardedMinimumResource_quality_ge_stay`: если абсолютная ошибка оценки
  на всех допустимых преемниках не превосходит `eps`, фактическое качество
  выбора не ниже качества stay.
### Hagi.Unified.GuardedRobustSelection — merged into ParetoExecution (C404)
- `guardedRobustNext_exists`: guard возвращает фактический преемник
  некоторого исходного допустимого действия; без estimated upgrade —
  именно преемник stay.
- `guardedRobustNext_quality_ge_stay`: при равномерной по допустимым
  преемникам абсолютной ошибке `≤ eps` и пороге `2eps`
  фактическое качество не убывает относительно stay.
### Hagi.Unified.GuardedRobustTrajectory — merged into ParetoExecution (C406)
- `guardedRobustPath_quality_monotone`: если stay тождествен на состояниях,
  а на каждом шаге ошибки оценки всех допустимых преемников не превосходят
  `eps t`, фактическое качество монотонно; при верхней границе `B`
  оно сходится к условному супремуму, не обязательно равному `B`.
- `guardedRobustGain_sum_range` точно телескопирует приросты;
  `guardedRobustGain_summable` и `guardedRobustGain_tendsto_zero`
  получают суммируемость и стремление приростов к нулю при тех же условиях
  и общей верхней границе качества. Сходимость параметров не утверждается.

## Hagi/Unified/HonestTransition.lean
- `honest_actual_drop`: сертификат содержит строгое фактическое убывание
  `obj s' < obj s` и `objectiveDrop > 0`, а не только положительность
  числового показателя.
- `honest_telescope`: два связанных перехода дают
  `obj s2 ≤ obj s0 − (drop1+drop2)`.
- `honest_two_steps_existent`: построен числовой свидетель двух
  последовательных положительных спусков на квадратичной цели.

## Hagi/Growth/InterpretiveGrowth.lean
- `pointEffect` и `causalEffect` неотрицательны; нулевое изменение выхода
  на всём выбранном наборе даёт нулевой эффект, а существование точки с
  положительным эффектом делает средний эффект положительным.
- `mass_split`: для неотрицательных весов сумма живой и пассивной массы
  равна полной массе.
- `passive_starves`: при `alpha > 0`, `gMax ≥ 0`, `wLive ≥ 0`,
  `G t ≤ gMax·wLive` и `alpha·C t ≤ G t` получается
  `C t ≤ gMax·wLive/alpha`; это оценка в заданной модели прироста.

## Hagi/Research/Legacy/LearningKernel.lean
- `grow_premise_derived`: если `LearningKernel` даёт
  `capability' ≤ energy'` и `energy' = energy−growEnergy`, а дополнительно
  `growGain ≤ capability'−capability` и `capability ≥ 0`, то
  `growEnergy ≤ energy−growGain`.
- `merge_premise_derived`: из `growE−gap−mergeE = slack` и `slack ≥ 0`
  следует `mergeE ≤ growE−gap`; `merge_slack_feasible` уточняет связанный
  баланс `mergeE+slack ≤ E'`.

## Hagi/Unified/LinkedProjects.lean
- `value_iteration_via_contraction`: при `0 < gamma < 1`, `eps ≥ 0` и
  `V(k+1)−Vstar(k+1) ≤ gamma(Vk−Vstar k)+eps`
  получается для всех `k`
  `Vk−Vstar k ≤ gamma^k(V0−Vstar 0) + eps(1−gamma^k)/(1−gamma)`.

## Hagi/Unified/LinkedQVec.lean
- `floor_preserved`: если начальное и каждое состояние списка удовлетворяют
  `FloorKept`, последнее состояние тоже сохраняет покомпонентный floor.
- `qgen_hides` даёт равные скалярные свёртки для разных координатных векторов,
  а `floor_catches` показывает, что покомпонентный floor их различает.

## Hagi/Research/Legacy/LinkedWitness.lean
- `wTraj_certified_family`: три конкретных перехода удовлетворяют
  `CertifiedTransition` при сумме стадийных рисков как пределе.
- `linkedHAGI_witness`: эта непустая траектория с `capability 1→8` и
  `budget 100→94` реализует `LinkedHAGIInvariant` на горизонте `3`
  с `alpha=1`.

## Hagi/Unified/LiveDeltaCycle.lean
- `live_delta_cycle`: при SafeQP-окне в фактор-пространстве,
  `L i > 0`, `eps i ≥ 0`, `eta ≥ 0`, `d ≠ 0`, заданной линейной оценке,
  принятом динамическом аудите и допустимом масштабе базы одновременно
  сохраняются `dL i ≤ eps i`, неизменные база и число блоков, аудит и
  квантованная квадратичная ошибка `≤ |m||n|(sPack/2)²`.
- `audit_violation_witness`: отклонённый аудит даёт превышение допуска хотя бы
  по одной из трёх характеристик; `audit_chain` складывает два допуска
  в удвоенные границы изменений.

## Hagi/Unified/Liveness.lean
- `liveness_merge`: если `p` строго положительно и нормировано, а отклонения
  `d` не являются общим константным вектором, то `twoGap p d > 0`.
- `liveness_data_axis`: при `rho > 0`, `D0 ≥ 0`, `0 ≤ xi < inj` и
  `D(t+1) ≥ rho·D t+inj−xi` для всех `t` получается `D T > 0` при `T ≠ 0`.
- `liveness_two_axis` объединяет оба независимых условия и вывода.

## Hagi/Unified/LogitCert.lean
- `logitCE_strictAnti`: скалярная `logitCE` строго антитонна.
- `descent_step_strict`: для любого `eta > 0`
  `logitCE(w+eta/(1+exp w)) < logitCE w`; эта конструкция относится к данной
  скалярной модели.
- `logit_exact_drop_dominates`: при `0 < eta ≤ 2`
  `(eta/2)(1/(1+exp w))²` не превосходит фактического убывания CE.

## Hagi/Theory/LogitGrowth.lean
- `step_params`, `step_energy` и `step_capability`: вычисленный преемник имеет
  `params' = next(S.params,eta)`, `energy' = logitCE(params')`, а при
  `capability = −logitCE(params)` и `capability' = −logitCE(params')`.
  Так прирост capability — тот же CE-спуск, без второго учёта каналов.
- `orbit_quality_bounded`: для согласованного начального состояния
  `capability(T)−capability(0) ≤ logitCE(S0.params)`.
- `orbit_budget_nonneg`: при `eta t > 0`, `0 ≤ budget 0` и доступности
  `eta t ≤ budget t` на каждом шаге бюджет остаётся неотрицательным до `T`.

## Hagi/Unified/LoopInstances.lean
- `quadCert_hits_optimum`: на квадратичной цели шаг `x−quadGrad a x`
  даёт `quadE = 0`.
- `quad_loop_strict`: если `quadGrad a x ≠ 0`, одношаговая траектория
  `qf a x` строго убывает по энергии. Оптимум за один шаг ограничен
  именно этой квадратичной моделью.

## Hagi/Unified/MachineProto.lean
- `machineProto_gap`: вычисленный `machineGap a w eta` равен
  `(machineProto a).loss w − (machineProto a).loss(jointStep a w eta)`,
  так что величина шага берётся из функции весов.
- `proto_loss_telescope` и `proto_progress_bound` переносят соответствующие
  потери и фактический прогресс по исполненной машиной траектории.
- `fsTraj_budget_le`: на функциональной gate-траектории бюджет не превышает
  начального; `fsTraj_count_le` ограничивает число принятых шагов
  начальным счётчиком плюс горизонт.

## Hagi/Research/Legacy/MasterHAGI.lean
- C304 (A12 credo quarantine): linked-вариант капстоуна
  (R362) удалён — deprecated, 0 потребителей; `MasterHAGI`/
  `MasterHAGICore` оставлены — живые потребители
  (`MasterHAGICoreOperational_v2`, nonvacuity-witness в
  `Hagi/Research/Legacy/Nonvacuity.lean`).
- `MasterHAGI`: при `lam ≥ 0`, `nu > 0`, `epsQ ≥ 0`, `CorePremises`,
  SafeQP-окнах, суммировании доменных рисков,
  условии `lam·riskSpend + nu·epsQ ≤ decrease`, достаточном бюджете,
  неотрицательном риске, нижней энергии и заданных производственных законах
  роста получается `CertifiedHAGIInvariant`.
- linked-вариант капстоуна удалён (C304, 0 потребителей).

## Hagi/Research/Legacy/MasterHAGICoupled.lean
- `CoupledHAGIInvariant` связывает канал capability непосредственно с
  состояниями и содержит отдельные неотрицательные spend/risk,
  векторный probe-floor и бюджетную бухгалтерию.
- `budget_no_growth`: из `B T = B0−Σspend` и `spend t ≥ 0`
  следует `B T ≤ B0`.
- `qvec_floor_implies_scalar`: при `w i ≥ 0` покомпонентный floor влечёт
  `Σw i·qfloor i ≤ Σw i·qvec T i`.

## Hagi/Research/Legacy/MasterHAGITrunc.lean
- `MasterHAGI_trunc`: сохранён (C304 recheck: живой потребитель —
  capstone-мост в `Hagi/Research/Legacy/Assumptions.lean`).
- `masterhagi_growth_witness`: при `C t=G t=D t=2^t`,
  `alpha=gamma=1`, `rho=0`, `beta=2`, `xi=0` все усечённые посылки верны
  для `T ≤ 6`.
- `cone_premises_force_exact`: при `gamma > 0` одновременные cone,
  `γD≤G`, `C'=C+G` и `C'≤(1+alpha)C` дают точное
  `C'=(1+alpha)C`; это свойство этих посылок, а не более общий вывод роста.

## Hagi/State/MemoryCycle.lean
- `descentFold_eq_effective`: для истории пар `(v,x)` плотная свёртка
  `W₀+Σ outerProd(v,x)` точно равна эффективным весам представления
  `fromHistory W₀ hist`.
- `history_storage_cost`: число сохраняемых элементов блоков равно
  `hist.length·(|m|+|n|)`.
- `admission_margin_sound`: если `|gtrue−gain| ≤ ε_cert` и запись допущена,
  то `lamM·Δcost + lamR·Δrisk ≤ gtrue`.

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

## Hagi/Unified/NCStepCert.lean
- `nc_loop_horizon`: при положительных gains, допустимых риске и бюджете,
  покомпонентном начальном floor и `n ≥ 1`
  энергия траектории строго убывает, а `S.cpu` остаётся исходным.
- `nc_trajectory_bound`: для фактических `ncAdvance`-переходов,
  `d t ≥ 0`, шагового неравенства потенциала и `Φ_min ≤ Φ`
  получается `Σd ≤ Φ(S0)−Φ_min+ΣriskSpend`.
- `nc_cpu_frozen_trajectory`: по фактической `ncAdvance`-цепочке
  `(S t).cpu` совпадает с начальным на каждом `t ≤ T`.

## Hagi/Unified/NegativeTests.lean
- `risk_limit_respected`: любой `StepCert` даёт `riskSpend ≤ riskLim`
  непосредственно из своей структуры.
- `ram_post_is_exact_write` и `ram_foreign_address_unchanged`:
  пост-состояние RAM-записи равно точному `Matrix.updateRow`, а любой адрес,
  отличный от записанного, сохраняет прежнюю строку.

## Hagi/Unified/CandidateConfig.lean
- `CandidateConfig`: кандидатная конфигурация — все параметры
  вычисляются как функции целей; глобальная оптимальность
  НЕ доказана и не заявляется (аудит A17).
- `cfg_rate`: при `rho > 0` `√cfgBeta(rho) = rho`;
  `cfg_stability` при `0 < rho < 1` даёт `0 ≤ cfgBeta < 1`,
  `0 < cfgEta ≤ 1−cfgBeta`.
- `cfg_descent`: на `TaskState k 1`, `0 < rho < 1` и ненулевой сумме
  квадратов градиента шаг `cfgEta rho` строго уменьшает энергию;
  это одношаговый результат заданной модели.

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
- `trajDropBound`: сумма фактических разностей энергии по gate-траектории
  не превосходит начальной энергии; `commitCountBound` даёт
  `commitCount ≤ T`.
### Hagi.Unified.QualityResourceMin — merged into ParetoExecution (C404)
- `minimumResource_next_quality_ge`: при непустом `qualityEligible`
  фактический преемник выбора удовлетворяет `qfloor ≤ value`.
- `minimumResource_cost_min`: ни один элемент того же конечного
  `qualityEligible` не имеет меньшей `(memory,operations)`-стоимости
  в memory-first порядке.

## Hagi/Unified/RateTheory.lean
- `pl_linear`: если `κ ≥ 0`, `μ > 0`, `2κμ < 1`,
  `Estar ≤ obj(f t)`, `2μ(obj−Estar) ≤ gsqr`,
  `κ·gsqr ≤ drops` и `obj(t+1) ≤ obj t−drops`, то
  `obj(f n)−Estar ≤ (1−2κμ)^n(obj(f 0)−Estar)`.
- `quad_gd_pl_rate`: на квадратичной цели при `0 < eta ≤ 1/2`
  энергия ограничена `(1−2eta(1−eta/2))ⁿE0`.
- `quad_gd_one_step`: при `eta=1` один градиентный шаг этой модели
  приводит к якорю и нулевой энергии; `quad_gd_pl_rate_open` также даёт
  тот же ряд при `0 < eta < 1`.

## Hagi/Unified/RecursiveClean.lean
- `clean_neuron_of_conditions`: из структуры `CleanCertificate`,
  положительной внесетевой массы вне корня и непустого множества рёбер
  следует `branchLocality ≤ εA`, `timeConsistency = 1` и `indepMass = 0`.
- `piR_le_one`: для `z j∈[0,1]` при `j<N`
  доля `piR z N` лежит в `[0,1]`.

## Hagi/Research/Legacy/RecursiveGrowth.lean
- `macro_step_decrease`: при merge-выигрыше `G ≥ 0`, `0 < L`,
  `0 ≤ eta ≤ 1/L`, `dnorm² ≤ inner`, квадратичной joint-оценке,
  `κ,s,dnormq ≥ 0`, `dnormq ≤ 1/2` и compress-Lipschitz оценке
  получается `E4 ≤ Emean − (G + eta·dnorm²/2 − κs/2)`.
- `safeqp_eps_critical`: при нижней энергии Emin,
  `E(t+1) ≤ E t−eta t·dn t²/2`, `etamin > 0`,
  `eta t ≥ etamin`, `eps > 0` и `dn t² ≥ eps²`
  горизонт удовлетворяет `n ≤ 2(E0−Emin)/(etamin·eps²)`.
- C217 (legacy quarantine, аудит P0a): модуль перенесён без
  изменения байтов из Hagi/Research/Legacy/RecursiveGrowth.lean в
  Hagi/Research/Legacy/RecursiveGrowth.lean (SHA-256
  ef6907ef5ce1c44f4b85c308148860acf799326f2ce165de15e1d56e0d6933b0,
  14644 байт / 347 строк / 0 CR) и выведен из корневого
  import-замыкания: Hagi.lean больше не импортирует его; новый
  umbrella-модуль Hagi/Legacy.lean и отдельная lean_lib
  Hagi.Legacy (defaultTargets += Hagi.Legacy) сохраняют
  собираемость и CI-покрытие. Утверждения `macro_step_decrease`
  и `safeqp_eps_critical` сохранены дословно: это карантинный
  рефакторинг, а не новое доказательство.
### Hagi.Unified.RobustCostSensitivity — merged into ParetoExecution (C404)
- `robustEligible_mono_epsilon`: при `eps1 ≤ eps2` всякий допустимый
  в большем радиусе кандидат допустим и в меньшем.
- `robustMinimumResource_cost_mono`: если заданы witnesses для обоих
  непустых классов, минимальная memory-first стоимость при `ε₁`
  не превосходит стоимости при `ε₂`.
### Hagi.Unified.RobustRadius — merged into ParetoExecution (C404)
- `robust_eligible_iff_radius_le_margin`: для конечного контроллера
  с допустимым stay существование floor-certified кандидата равносильно
  `eps ≤ estimatedMaxValue − qfloor`, включая равенство.
- `no_robust_eligible_above_margin`: при большем `eps`
  ни один кандидат не проходит эту проверку; `estimatedMaxValue_upper`
  показывает, что максимум берётся по оценкам фактических преемников.
### Hagi.Unified.RobustResourceMin — merged into ParetoExecution (C404)
- `robustMinimumResource_actual_quality_ge`: если оценка всех фактических
  преемников отличается от ценности не более чем на `eps`, выбор удовлетворяет
  истинному qfloor.
- `robustMinimumResource_cost_min`: выбор минимален только среди кандидатов,
  для которых одновременно `qualityEligible` при пороге `qfloor+eps`;
  истинно допустимый, но не сертифицированный кандидат не сравнивается.

## Hagi/Unified/SignComp.lean
- `signStepCert`: на квадратичной цели, если `quadGrad a x ≠ 0`,
  `0 < eta ≤ 1`, начальный floor и `signCommCost k ≤ riskLim`,
  строится полный `StepCert` для знакового шага; поле `signDrop_pos`
  доказывает положительный фактический drop.
- `sign_pointmass_ratio`: на точечной массе
  `nrm2(signStep)·|k|² = 1`.
- `sign_no_uniform_floor`: если `κ > 1/|k|²`, на некоторой точечной массе
  `nrm2(signStep) < κ·nrm2(quadGrad)`. Так одно коэффициентное
  выравнивание знакового шага не даёт универсальной нижней границы с `κ`.

## Hagi/Unified/SignDescent.lean
- `sign_descent`: масштабированный знаковый шаг `signScale(grad)·sign(grad)`
  наследует `descent_drop`: при `0 < eta ≤ 1/L`
  `f(x−eta·dir) ≤ f x−eta(1−L eta/2)‖dir‖²`.
- `sam_descent_bridge`: при `rho ≥ 0`, ограниченности сверху
  множеств значений, задающих `samW`, локальной остроте `samW−f x ≤ sharp`
  и спуске `samW x' ≤ samW x − delta` выполняется
  `f x' ≤ f x−(delta−sharp)`.
  `lion_descent` требует отдельной согласованности momentum с градиентом
  и `0 < eta ≤ 1/L`.

## Hagi/Research/Legacy/StateTakeoff.lean
- `state_capability_takeoff`: при `FullCycleRefinement`,
  `alpha,gamma > 0`, `rho ≥ 0`, положительной начальной capability,
  начальном конусе, `γD t ≤ growGain t`, производственной динамике,
  потолке `(1+alpha)` и β-пороге для `t < T`
  `capability(S0)·(1+alpha)^T ≤ capability(S T)`.
- Здесь шаг capability следует из `FullCycleRefinement`;
  `effects.growGain`, динамика `D` и перечисленные пороги остаются измеряемыми
  `h_emp_`-условиями.
- `corePremises_of_full_refinement_normalized`: при компонентной ошибке
  `ε_Q` и `w i ≥ 0`, `Σw i=1` полное уточнение заменяет отдельную
  скалярную Qgen-посылку, но не остальные стадийные условия.

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
- `sgn1_grid_fix`: решётка шага `1` фиксирует знаковые значения.
  `tern_grad_inner` даёт точное `Σᵢ gridQ 1(sign gᵢ)·gᵢ = Σᵢ|gᵢ|`,
  без второй ошибки квантования.

## Hagi/Benchmarks/TernaryProbe.lean
- `ternaryCubicShift_abs_error_le_stepBudget`: при `level,σmax > 0`
  и `|t| ≤ σmax` ошибка насыщающего тернарного квантования сдвинутой
  кубической энергии ограничена вычисленным `ternaryCubicStepBudget`.
- `ternaryCentralCubicProbe_cost_bound`: при `0 < σ ≤ σmax`
  погрешность центральной пробы относительно `⟪probeCubicGrad,v⟫`
  ограничена соответствующим `probeCost`.
- `ternaryCentralCubicProbe_optimal_bound`: при `c,v ≠ 0`,
  `level > 0`, `0 < σ ≤ σmax` клипнутый шаг минимизирует этот вычисленный
  верхний bound по `σ`; сравнение справа — `probeCost(σ)`, а не фактическая
  ошибка другого шага.

## Hagi/Benchmarks/TernaryWitness.lean
- `quantOpt_energy_bound`: при `s > 0` и `ternInRange s (a i)`
  для всех `i` энергия `quadE a (quantOpt s a)` не превосходит
  `|k|·s²/8`.
- `quant_jump_honest`: если исходная энергия строго больше этого потолка,
  переход к `quantOpt` имеет положительный фактический drop при нулевых
  риске и расходе. `ternaryStepCert` упаковывает тот же переход в `StepCert`.

## Hagi/Research/Legacy/TopLevel.lean
- `quant_residual_norm` и `quant_energy_bridge`: если
  `|w i−q i| ≤ s/2`, то `Σᵢ(w i−q i)² ≤ n(s/2)²`;
  при `s,κ ≥ 0` и `dE ≤ κ√Σ(w−q)²` получается `dE ≤ κ√n·s/2`.
  Lipschitz-условие остаётся `h_emp_`-посылкой.
- `noisy_cycle_step`: при `|inner_est−inner_true| ≤ m0`,
  `dnorm² ≤ inner_true`, `0 < L`, `0 ≤ eta ≤ 1/L`,
  `κ,s ≥ 0`, `|w i−q i| ≤ s/2` и заданных merge/compress оценках получается
  `E4 ≤ Emean−(G+eta·dnorm²/2−eta·m0−κ√n·s/2)`.
- `risk_budget_termination`: если связный ряд сертификатов имеет
  `decrease ≥ eps > 0`, суммарный `riskSpend ≤ R ≥ 0`,
  потенциал ограничен Emin и `T > 0`, то
  `T ≤ (Φ0−Emin+R)/eps`.

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
- `holdout_concentration` (C435): для фиксированной до дров модели
  `f : Ω → [0,1]`, k > 0: `P[|holdoutMean − popMean| ≥ ε] ≤ 2exp(−2kε²)`;
  `selection_bias_*` — негатив: выбор модели ПОСЛЕ просмотра holdout
  ломает несмещённость.
- `holdout_wr_concentration` (C487): без-возвратная форма
  `2exp(−kε²/(2(σ̂²(2N−k)/N + ε)))` — Freedman-механика с частичным
  fpc-кредитом; `wr_bound_le_with_replacement` — строже with-replacement
  при проверяемом условии `σ̂²(2N−k)/N + ε ≤ 1/4`.

## Hagi/Theory/MasterTheorem.lean (v4 T6: + MasterBudget, VerticalCapstone)
- Канон master-траектории (v4 T6): MasterTheorem + MasterBudget
  (бюджет как premise-канал, ns `Hagi.Theory`) + VerticalCapstone
  (ns `Hagi.Unified`) в одном модуле, имена сохранены.
- `accuracy_for_budget`: при `0 ≤ q < 1`, `σ ≥ 0`, `B0 > 0`,
  `c > 1`, `Estar ≥ 0` и
  `e(s+1) ≤ q·e s + σ²/(B0·c^s)` получается
  `e t ≤ Estar + q^t(e0−Estar) + σ²/(B0(1−q))`.
  Постоянный шумовой член — консервативная граница данной рекуррентности.

## Hagi/Theory/FlowMatching.lean
- `cfmPsi`/`cfmOtField`/`cfmSigma`: OT-условный путь и замкнутый
  conditional VF (equations 20–22 статьи Flow Matching), честно
  дискретно — на конечном словаре `V`.
- `cfmSampleLoss` + `cfmSampleLoss_eq_sqDiff`: per-sample CFM loss
  === инстанциация C384 `sqDiffObjective` на паре
  (v t (ψ_t x₀), otField) — мост definitional (rfl).
- `cfmLoss`/`cfmLoss_nested`/`cfm_expected_diff`: конечное
  ожидание по joint (uniform-сетка ⊗ q ⊗ p, pmfMean); закон
  полного ожидания и unbiasedness разности per-sample оценок
  (дискретный аналог роли Theorem 2; непрерывный оригинал НЕ
  формализован — pin).

## Hagi/Theory/Interpretability.lean
- `RebuildSystem`/`Rebuildable`: контракт C421 — интерпретируемость
  как description-length bound (iWSP rebuild bottleneck, arXiv
  2611.18114): сертификат = существование описания d бюджетом ≤ B,
  чей rebuild R(d) сохраняет качество в пределах ε по лоссу ℓ.
- `rebuildable_of_compressible`: мост сжатие→rebuild — короткое
  описание + ограниченное смещение параметров (dist M̃ M ≤ δ) дают
  сертификат с ε_rebuild = lip·δ, ВЫВЕДЕНО через липшицев transport
  (алгебра C389, premise-binder).
- `exists_good_not_reachable`/`exists_not_rebuildable`/
  `exists_not_exact_rebuildable`: конечный counting bound
  (pigeonhole через card_le_of_injective): бюджет-B описаний над
  конечным алфавитом достигают ≤ card Sig^B моделей; при большей
  мощности ε-good множества (premise) некоторая ε-good модель не
  является rebuild ни одного описания — interpretability-is-special
  (без kolmogorov-претензий: чистая кардинальная арифметика).

## Hagi/Cert/StepGen.lean (C278, A10 item 2 step 1)
- `Hagi.Cert.CertStepGen` — ОБЩЕЕ ядро сертифицированного шага
  (A10 target): общий индекс задач `TaskId : Type*` (жёсткий `Fin 5`
  цикла — инстанциация, не ограничение ядра), остаток риска — ПОЛЕ
  riskRem с законом расщепления risk_split (0-пиннинг C254
  невозможен по построению), свёрнутый δ-бюджет (C245) на явном
  носителе deltaLevel.
- Мосты: `Hagi.Cert.certStep_to_gen` (каждое замороженное `CertStep`
  вложено; нулевой δ-носитель), `Hagi.Cert.CertStepGen.toCertStep`
  (проекция обратно, δ-канал отбрасывается),
  `Hagi.Cert.certStepDelta_to_gen` (свёртка C245-надстройки).
- Композиция `Hagi.Cert.CertStepGen.trans` и телескопы:
  `trajectory_telescope_gen` (спуск), `delta_telescope_gen`
  (Σ δ ≤ δ₀ при δ₀ ≥ 0 — явная посылка), `risk_telescope_gen`
  (Σ трат риска ≤ r₀ при r₀ ≥ 0).

### bounded-конструктор (C344, A14 QW3)
- `Hagi.Cert.CertStepGenBounded` — ≤-вариант общего ядра: те же
  носители, но нестрогие законы списания (budget_next_le,
  risk_next_le, delta_next_le); остатки — сами пост-считывания.
- `Hagi.Cert.CertStepGenBounded.toExact` — БЕЗПОСЫЛОЧНЫЙ мост в
  точное ядро: точные траты ОПРЕДЕЛЕНЫ как разности состояний
  (равенства по построению: sub_sub_cancel / rfl / sub_add_cancel)
  — проблема hbudeq premise-форм адаптеров растворяется: точность
  приходит из определения, а не из посылки.
- Производные честности:
  `Hagi.Cert.CertStepGenBounded.budgetSpend_le_actual`,
  `Hagi.Cert.CertStepGenBounded.riskSpend_le_actual`,
  `Hagi.Cert.CertStepGenBounded.delta_le_actual` (заявленная трата
  ≤ дефинициональной — точное ядро может тратить БОЛЬШЕ).
- ≤-телескопы (уровневая форма):
  `Hagi.Cert.trajectory_telescope_gen_bounded`,
  `Hagi.Cert.budget_telescope_gen_bounded`,
  `Hagi.Cert.risk_telescope_gen_bounded`,
  `Hagi.Cert.delta_telescope_gen_bounded` (aₙ ≤ a₀ − Σ трат).
- Королларий капстон-цикла:
  `Hagi.Unified.CertifiedLoop.StepCert.toCertStepGenBounded`
  (точная бюджетная посылка hbudeq C278-адаптера больше не нужна —
  нестрогого hdec цикла достаточно) и без-hbudeq маршрут
  `Hagi.Unified.CertifiedLoop.stepCert_to_bounded_to_exact` с
  теоремами `stepCert_to_bounded_to_exact_budget` (трата —
  дефинициональная разность, rfl) и
  `stepCert_to_bounded_to_exact_budgetBound` (заявленная трата ≤
  дефинициональной). Полное поглощение S3 — следующий бит (QW4/5).


## Hagi/Contracts/GradientBottleneckIdentification.lean (C281, E2 addendum A10)
- Мост спектральной идентификации C232: `selP_conjTranspose_mul_selP`
  (ортонормированные столбцы row-селектора) → `embedded_gram_eq`
  (Gram-матрицы встроенного и прямоугольного совпадают) →
  `embedded_eigenvalues₀_eq` (перенос спектра через
  `sort_roots_charpoly_eq_eigenvalues₀`: равные матрицы — равные
  charpoly — равные отсортированные спектры) →
  `embedded_singularValues_eq_rect` (square singularValues₀
  встроенной = Rectangular.singularValues на Fin(min)).
- Хвост-идентификация: `rectangularTail` + 
  `tail_sum_sq_truncatedSingularValues_tail_eq` — хвост-сумма C232
  равна сумме квадратов ИСТИННОГО прямоугольного хвоста (за min
  вклад нулевой — eigenvalues₀_zero_beyond_min через Gram-мост).
- MAIN: `eckart_young_lower_bound_rect_true_tail` — C232-бонус с
  идентифицированным хвостом; consumer
  `gradient_bottleneck_bound_rect_true_tail` (premise-form hΔ
  сохранён).

## Hagi/Training/StepProvider.lean (C280, merge map A10)
- Интерфейсный слой над `Hagi.Cert.CertStepGen`: `StepProposal`
  (следующее состояние + канонический сертификат CertStepGen —
  носитель неотделим от доказательства), `StepProvider`
  (init + оракул `step : s → Option (StepProposal …)`); провайдер —
  ЗНАЧЕНИЕ (выбор провайдера — решение политики, не typeclass),
  none = сертифицированного продвижения нет (прогресс и hold
  разделены — `HoldStep`).
- Потребительская теорема `telescope`: при явном успехе оракула вдоль
  траектории (hsome/hnext) цель терминального состояния ограничена
  целью старта минус сумма сертифицированных drop'ов — интерфейс
  кормит телескоп ядра.
- Три инстанса не-вакуозности: `quadContractProvider` через НОВЫЙ
  адаптер `StepContract.toCertStepGen` (спуск 3/4·w² при w > 0,
  равенство), `honestQuadProvider` через
  `HonestTransition.toCertStepGen`, `cramDescentProvider`
  (premise-form оракул CRAM-спуска).

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
  и RMSNorm — premise-форма (C307); полный FastArch3 НЕ заявлен.

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
  весов — premise-форма (C307); полный FastArch3 certificate НЕ
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
  STATE MIXING `x ↦ M *ᵥ x` с M дважды стохастической (C231).
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
  (mixing 1-липшицев — роста нет, C231). HYBRID (payoff звена):
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
  softmax — premise-форма (C307); полный FastArch3 certificate НЕ
  заявлен.

## Hagi/Model/FastArch3Transfer.lean
- C311 (E4 FINAL rung — FastArch3 end-to-end transfer assembly):
  end-to-end FastArch3-SHAPED certified-descent теорема —
  параметрический SoftmaxHead (C283/C291) поверх гибридного стека
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
- PREMISE LEDGER (P1–P9, полный реестр `.tmp/C311/premise-ledger.md`,
  v2 `.tmp/C313/premise-ledger-v2.md`):
  P1 softmax weight-map simplex (C307, lived-with); P2 value
  μatt-липшицевость (C307, per-instance); P3 pre-norm μn —
  РАЗРЯЖЕНА C309 (region 2√n/r; ε-форма 2/√ε); P4 rope Isometry —
  РАЗРЯЖЕНА C308 (rotEuc); P5 GDN gate μg — РАЗРЯЖЕНА C313
  per-instance для tanh-семейства (`gdnGateTanh_lipschitz`,
  μg = 1; δ/β/σ-композиции — по-прежнему per-instance); P6
  IsDoublyStochastic (C231,
  lived-with, Sinkhorn не заявлен); P7 головная Lc-липшицевость —
  РАЗРЯЖЕНА C313 per-instance (`fastarch3_head_Lc`, ident-logit
  headCE на фиксированной метке, Lc = 2); P8 сертифицированный спуск головы δ (C291,
  per-instance); P9 реализованный шаг dx по identity-пути (C300,
  структурная посылка). Честная граница: certified descent для
  FastArch3-SHAPED модели ПОД ledgered premises — НЕ утверждение об
  обученных весах или Python runtime; полный forward/backward
  certificate не заявлен.

## Hagi/Data/AnfTransform.lean
- C301 (E5 ANF/Möbius core — Zhegalkin transform correctness):
  `anfTransform` — преобразование Жегалкина/Мёбиуса как рекурсивная
  «бабочка» на последней координате (`T f = (T f₀, T f₀ ⊕ T f₁)`,
  вычислимое, носитель `(Fin n → Bool) → Bool` — таблицы истинности
  над конечным типом, маски `Hagi.Data.BoolVenn` суть случай n=2).
- `anf_inversion` — ядро корректности: преобразование — ИНВОЛЮЦИЯ
  (`anfTransform (anfTransform f) = f` для всех n) — обращение
  Мёбиуса на булевой решётке; доказано бабочка-индукцией: ложная
  половина — IH, истинная — линейность `anf_add` + сокращение GF(2)
  `a ⊕ (a ⊕ b) = b`.
- `anf_subcube` — характеристика через таблицу истинности:
  коэффициент ANF при `S` есть чётность `f` по подкубу `x ⊆ S`
  (`c_S = ⊕_{x ⊆ S} f(x)`, в арифметике чётности `ZMod 2`,
  `anfBit`); бабочка и подкуб-сумма — одно и то же преобразование.

## Hagi/Learning/SoftRouterMix.lean
- Аудит §7 (T): «Мягкая калиброванная смесь вместо жёстких ±10:
  CE смеси не хуже взвешенного среднего CE (Jensen)» —
  существование проверено, форма отсутствовала (равномерный
  1/N-вариант `ensemble_ce_le_mean_general` был; вероятностно-
  взвешенного роутерного — не было). Доставлена честная
  раскладка: ЛОГИТ-смесь и СМЕСЬ РАСПРЕДЕЛЕНИЙ — разные
  объекты, оба истинны по разным причинам (challenge-pin в
  докстрингах модуля).
- `mixture_log_weighted_le` — взвешенная вогнутость log:
  Σwᵢ·log xᵢ ≤ log(Σwᵢxᵢ) (AM-GM, положительные xᵢ);
  `ceDist` + `mixture_ce_le_weighted_avg` — дистрибутивная
  сторона: −log(Σwᵢpᵢ(y)) ≤ Σwᵢ(−log pᵢ(y)); нужна только
  положительность pᵢ (нормализация не используется — сильнее
  симплексного).
- `lse_weighted_le` — взвешенный Дженсен для lse
  (обобщение `lse_mean_le_mean_lse` с 1/N на вероятностный
  вектор w); `soft_router_ce_bound` — логитная сторона аудита:
  ceOneHot t (Σwᵢzᵢ) ≤ Σwᵢ·ceOneHot t zᵢ. Веса — Hedge-симплекс
  роутера (посылки mirrorStep/router_regret_bound);
  регрет ограничивает ΣwᵢCEᵢ, модуль замыкает на CE смеси.

## Hagi/Contracts/HadamardSpread.lean
- C321 — аудит A10 §9 п.5 («теорема о контракции реального
  квантайзера, средняя версия для блоков после Адамара,
  измерено ≈0.33 против худшего α≈0.106»): доставлена честная
  ДЕТЕРМИНИРОВАННАЯ формализация среднего случая — без теории
  меры, «среднее» = энергетическая предпосылка, не вероятностное
  усреднение по сфере.
- `hadamard_spread_bound` — Парсеваль для ортонормального Адамара
  носителя (`Hagi.Core.hadamardOrthonormal`): энергия сохраняется
  ТОЧНО, `∑ (Hx)² = ∑ x²`; `hadamard_spread_bound_image` — то же
  через реиндекс `hadamardImage` моста C238; `hadamard_large_coord_count_le`
  — марковский счётчик: #{|Hx|>t}·t² ≤ ‖x‖² — больших координат
  мало, детерминированное ядро истории о расплёскивании.
- `hadamard_ternary_error_bound` (ГЛАВНЫЙ) — раскладка ошибки
  тернарного квантователя на образе Адамара: ∑err² ≤ 2^k·(s/2)² +
  (энергия вне диапазона) — ε_small = s/2 в точности
  `qTern_error_in` носителя (честная релаксация «0 ошибки»:
  вещественная решётка не точна); из `ternary_split_le` +
  точечного (|w|−s)² ≤ w².

## Hagi/Budget/RDAlloc.lean
- C322 — аудит §7 п.7 (slow-loop композиция RD-сжатия):
  побитное распределение + закон ошибки по стадиям +
  изо-Фробениус чувствительность + пересертификация собраны в
  ОДИН шаговый сертификат. Композиция ONLY: вся математика
  цитируется из своих носителей (C237/C252/C253/C278), новый —
  только клей и упаковка.
- `RDAlloc` — premise-form побитное распределение стадий: bᵢ ≥ 0,
  εᵢ ≥ 0, ∑bᵢ ≤ bitBudget. HONEST SCOPE: распределение только
  БЮДЖЕТНОЕ; оптимальность water-filling — C237
  (`rankResidual_equalized`, `rankResidual_allocation`,
  `weightedExpAllocation_isoFrob_optimal`), процитирована, НЕ
  перепроверяется. `rdAllocBytes` = ∑bᵢ/8 (байты), `rdAllocError`
  = ∑εᵢ (качество), обе неотрицательны. εᵢ-рецепт факторизованной
  стадии — квадратная форма закона произведения C253
  (`quantProd_relError_sq` verbatim, C326: дубликат-обёртка
  удалена).
- `rd_step_error_bound` (ГЛАВНЫЙ) — composed slow-loop ошибка
  сжатия: двухстадийный residuary конвейер Ŵ = R1+R2 с
  аддитивным законом C253 (`residualTwoStage_error_le_add`
  verbatim: ε₁ знак-посылка, ε₂ вторая невязка) через считывание
  φ с чувствительностью sens (premise-form изо-Фробениус
  Lipschitz, C252) ⟹ |φ(Ŵ)−φ(W)| ≤ sens·(ε₁+ε₂); `frobSq_neg` —
  клей направления знака (квадраты убивают знак).

## Hagi/Deployment/CanaryRamp.lean
- C324 — аудит §7 p.1 по ранжированию
  `.omc/analysis/period-c313-c323-analysis.md` (canary-приёмка):
  вес маршрута w непрерывен, канареечный разгон 0→1, утечка линейна
  по w (`cascade_leak_router_linear`, C250), e-процесс следит за
  вредом (Ville, C264/C295 — процитированы premise-form, Unified
  слой 6 выше Deployment 5). Композиция ONLY: новый файл — клей и
  упаковка поверх C250 + C278.
- `CanaryRamp` — GENERIC ramp policy premise: любая неубывающая
  последовательность весов в [0,1] (mono/nonneg/le_one). Форма
  рампы — ПОСЫЛКА: теоремы верны для любой такой
  последовательности. `linearRamp` — стандартная рампа wₜ = t/T;
  `linearRamp_canary` — [0,1]-клэмп совпадает с ней на окне j ≤ T.
- `canaryStepLeak` — КОНСТАНТНАЯ ФОРМА C250 verbatim:
  w·L_stack·‖ΔR‖·‖projR U *ᵥ x‖, L_stack = cascadeGain S (честное
  по-слойное произведение, БЕЗ предположения контрактивности);
  `canary_step_leak_bound` = `cascade_leak_bound_op` при |w| = w.

## Hagi/Learning/ContinualForgetting.lean
- C327 — ранжирование item c (C323): continual-learning forgetting
  bounds — формальный контракт контроля забывания старых задач при
  адаптации к новым (вывод — `.tmp/C327/research.md`).
- `auditSpendChain` + `auditSpendChain_delta_split` — цепочка из m
  принятых адаптаций (адаптация k тратит срез δₖ на задачу tsk k):
  δ-SPLIT арифметика ∑ spent = ∑ spent₀ + ∑ₖ δₖ (бухгалтерская
  лемма, которой нет в C274 — его мастер одно-снимковый).
- `continual_forgetting_bound` (ГЛАВНЫЙ 1) — контроль забывания:
  P(∃ старая задача ложно пострадала) ≤ ∑ spent₀ + ∑ₖ δₖ ≤ δtotal;
  мастер C264 `gate_pipeline_false_commit` при δ := ПОТРАЧЕННЫЙ
  итог (острее формы δtotal из C274) + алгебра дополнений
  (`prodPq_compl`/`prodPq_iff`). «Адаптация к новой задаче» —
  просто ещё одно аудируемое предложение: тот же аудиторский бюджет
  её покрывает.

## Hagi/Contracts/SparseInferenceCert.lean (C328)
- Audit §8 inference-сторона разреженности: sparsity-certified
  inference — спектральная маска + compute-доля, вся упаковка
  новая, все ингредиенты процитированы.
- `sparse_inference_error` (MAIN 1): маска `B` ранга-k достигает
  хвостовой ошибки (premise `hE : ‖A−B‖ ≤ (∑ rectangularTail²)^½`;
  точное равенство — усечённая спектральная маска, квадратный
  случай `frobenius_error_truncatedSVD`, прямоугольный мост
  отложен с C232/C281) ⟹ всякий sens-липшицев readout φ меняется
  не более чем на sens·(∑ хвост²)^½ (C300/C322
  Lipschitz-transfer). Направление честное: EY — оценка СНИЗУ на
  ошибку маски, функциональная граница НЕ следует из EY для
  произвольного B (ловушка направления поймана probe-итерацией,
  plan-review A1).
- Eckart-Young процитирован ДОСЛОВНО
  (`eckart_young_lower_bound_rect_true_tail` C281) — ни одна
  маска ранга-k не бьёт хвост: сертификат оптимальности посылки
  hE. (C333: делегирующий близнец sparse_mask_minimal удалён
  как дубликат C281, STMDUP-протокол; каноническое имя выше.)

## Hagi/Contracts/ComputeToQuality.lean (C330)
- Цель GOAL «минимизация вычислений» end-to-end: total compute to
  quality = (шаги до ε) × (FLOP на шаг) — обе несущие уже
  приземлены (C291 descent rate, C328 FLOP-учёт), новая только
  КОМПОЗИЦИЯ на ядре C278 CertStepGen.
- `budget_telescope_gen`: недостающий четвёртый телескоп ядра —
  ТОЧНАЯ бюджетная идентичность `budget(t n) = budget(t 0) −
  Σ spends` (раньше телескопировались только drop/delta/risk).
- `steps_to_quality` (MAIN 1): равномерный сертифицированный
  спуск d на шаг (premise-интерфейс к C291: точный safe-step drop
  2A²/R² из `ceOneHot_safeStep_le_residual` процитирован в
  docstring, КОНСТАНТ в утверждениях нет) + зазор Δ₀ ≤ n·d ⟹
  `objective(t n) ≤ ε` (C294-стиль на шагах тренировки, движок —
  `trajectory_telescope_gen`).

## Hagi/Contracts/KVCacheCert.lean (C331)
- Цель: KV-cache inference certificate — расширение
  compute-сертификации (C328/C330) на последовательный инференс:
  cached attention (новый токен attends по сохранённым
  keys/values через бегущий summary) имеет per-token work `t+1`
  против recompute-режима, который на каждом шаге ре-attend'ит
  ВСЁ прошлое; и cached выход ТОЧНО равен полной рекомпутации.
- Route (b) (выбор анализа): softmax-веса НЕ разлагаются
  аддитивно (нормализатор глобальный), но пара (den, num)
  разлагается: den = Σ e^{q·k}, num = Σ e^{q·k}·v — обычные
  суммы по списку токенов; инкремент = ровно один новый член.
  Route (a) (линейный/GDN-style additive summary, контраст
  `Hagi.External.MemT.GDN2`) упомянут в docstring, не
  формализуется здесь.
- `kv_cache_exact` (MAIN 1): cachedAttn (tokKV q toks) (q·k) v =
  tokFull q (toks ++ [(k,v)]) — ТОЧНОЕ равенство cached = full
  recompute на List-носителе; движок — `foldl_den_eq`/
  `foldl_num_eq` (foldl-аккумулятор = map-sum, индукция) +
  `tokDen_append`/`tokNum_append` (map_append+sum_append).

## Hagi/Contracts/DataToQuality.lean (C334)
- Цель GOAL «минимизация данных» — data-efficiency / sample-complexity
  сертификат: сколько СЭМПЛОВ сертифицируют, что выбранный energy-модель
  оптимальна по population PL-risk (дополнение compute-дуги C330).
- `sampleComplexity m δ η = log(m/δ)/(2η²)` + инверсия радиуса C287
  `concConfidence_le_of_sample_bound`: `n ≥ sampleComplexity m δ η ⟹
  concConfidence η n ≤ δ/m` — ТОЧНАЯ алгебра обращения канонической
  экспоненты exp(−2nε²) (exp монотонен + exp(−log x) = 1/x), никакой
  новой концентрационной математики.
- `samples_to_quality` (MAIN 1): конечный класс + margin-посылка C315
  (победитель бьёт всех на ≥ 2η эмпирически) + явное число сэмплов
  `n ≥ log(2|ι|/δ)/(2η²)` ⟹ w.p. ≥ 1−δ выбранный — population-best
  (композиция: C315 `finite_class_pl_margin_argmax` + инверсия на
  кратности объединения m = 2|ι| — константа 2 двустороннего события
  C264). `samples_to_quality_subopt`: γ-ослабление («в пределах γ от
  лучшего»), η играет роль точности γ−ε.

## Hagi/Contracts/TruncatedSVDTail.lean (C343)
Rectangular spectral-tail bridge (A13 P-3): under the SVD premise
(A = U·Sigma·V^H with carrier rectangular singular values sigma),
the truncated approximant approxK satisfies
`truncated_svd_error_eq_tail`:
||A - A_k||^2_F = sum_{i>k} sigma_i^2 (trace/rotation route),
and `sparse_premise_discharged` composes with
`Hagi.Contracts.SparseInferenceCert.sparse_inference_error`,
turning the premise-form hE into theorem-form for explicit
SVD-decomposable A. Numeric anchor (diag(3,1), k=1) deferred
honestly: carrier-index casts resist decide reduction (classical
card instances); the main theorems carry the content.



## Hagi/Theory/AdapterGrowth.lean (C533: adapter snap composite grow)

- `adapter_snap_bound`: Lipschitz-форма для адаптера h = B·A·x — при obj
  Lipschitz по ℓ¹ признакам (L) и ℓ∞-операторном факторе C = ‖B·A‖∞
  пертурбация ε входа с |ε j| ≤ 2^-(k+1) даёт
  obj (f + δ) ≤ obj f + L·n·C·2^-(k+1), δ = B·(A·ε).
- `adapter_snap_cycle_sound`: телескоп цикла admission (вклад 0 ТОЧНО) +
  certified fd-шаги (вклад ≤ 0) + q/2^k snap (вклад ≤ bound_i) —
  делегат к `grow_snap_cycle_sound` (intentional restatement pin,
  файл stmdup_allowlist рядом с declarations.lock).
- Bench `--mode adapter-snap-grow` (измерено, bench-adapter-snap-grow.json):
  8 уровней адаптеров r=1 поверх frozen trunk (глубина 2 → 10), по 8 новых
  параметров на уровень (64 суммарно против 21 у full-блока), admission с
  ТОЧНОЙ obj-инвариантностью на каждом уровне, snap q/2^40 с certified
  err-bound на каждой границе. Итог (canonical-шкала): старт ≈ 2.283,
  certified drop 2.271 (obj → ~0), cumulative snap bound ≈ 2.98e-13
  (запас ~13 порядков), maxden 13 цифр на каждом уровне, ~4 c.
- Таблица трёх механизмов роста (измерено, regress-*.json C521/C532/C533):
  identity-блок (C521 grow-snap): 21 параметр/уровень, знаменатели
  сбрасываются snap'ом; адаптер без снапа (C532 adapter-grow): 8
  параметров/уровень (r=1), прогресс ×2.96 против блока, но знаменатели
  компаундятся по уровням; adapter+snap (C533): 8 параметров/уровень И
  сброс знаменателей на каждом уровне — минимальный объём и минимальные
  вычисления одновременно, глубина 10 certified.

## Hagi/Theory/AdapterGrowth.lean (C535: rank-adaptive adapter grow)

- `rankScore` / `rankSelect`: измеримый критерий выбора ранга адаптера
  (probe-drop НА параметр) и детерминированный селектор r ∈ {1,2}
  (r=2 ⇔ score_2 СТРОГО больше; равенство → r=1, budget-приоритет);
  linorder ⇒ тотальный порядок ⇒ выбор = функция измеренного
  состояния (паттерн hybridSelect C510).
- `rank_select_deterministic`: равные измеренные состояния → равный
  выбор. `rank_select_sound`: дизъюнкция r-веток (паттерн
  hybrid_step_sound C510) — whichever ранг выбран, certified-гарантия
  ВЫБРАННОЙ ветки (objAfter r ≤ o + b_r) сохраняется без ослабления;
  probe-шаги — no-commit вычисление на копии (C530 rollback-семантика),
  в certified-цепь не входят.
- Bench `--mode adapter-rank-adaptive` (измерено, .tmp/C535/
  bench-rank-adaptive.json + bench-fix-r{1,2}.json, замороженный
  корпус): на каждом из 8 уровней probe r=1 (8 парам) и r=2 (16 парам)
  по 2 certified-механикой от одного состояния → выбор drop/params →
  commit выбранного через C533-цикл (admission B=0, 4 certified fd-шага,
  snap q/2^40, maxden 13 цифр на каждом уровне).
  Таблица adaptive vs фикс (total drop 2.2599, замороженный корпус):
  | arm          | параметры | total drop | drop/param | steps |
  |--------------|-----------|------------|------------|-------|
  | adaptive     | 64        | 2.259862   | 0.035310   | 17    |
  | fix r=1      | 64        | 2.259862   | 0.035310   | 17    |
  | fix r=2      | 128       | 2.259862   | 0.017655   | 10    |
  Измеренный вердикт: на ВСЕХ 8 уровнях score(r=2) ≤ score(r=1) —
  селектор честно выбирает r=1 (половина параметров при том же drop);
  adaptive ≡ fix-r1 побитово. r=2 даёт тот же drop при ×2 параметров
  (10 шагов против 17) — бюджетный критерий корректно отвергает его.
  Детерминизм: повторный прогон побитово идентичен (выборы и числа).

## Hagi/Theory/AdapterGrowth.lean (C536: SVD-«Матрёшка» adapter merge)

- `stackProd` / `adapter_stack_rank_bound`: суммарное возмущение
  стека L LoRA-уровней Δ = Π(I+E_i) − I имеет ранг ≤ Σ рангов E_i
  (индукция: head-шаг E·Π + (Π−1), `Matrix.rank_mul_le_left` +
  подаддитивность rank_add_le'; в этой Mathlib-версии
  Matrix.rank_add_le отсутствует — собран из
  LinearMap.rank_add_le + Submodule.finrank-неравенств).
  Следствие (bench-форма L=8, r=1, d=4): rank(Δ) ≤ min(4, 8) — merge
  ГАРАНТИРОВАНО дешевле стека независимо от данных.
- `cs_row` (строчная Коши–Шварц из abs_real_inner_le_norm) +
  `adapter_merge_error_bound`: Frobenius-хвост усечения
  Σ (Δ−Δ_k)² ≤ ε² + Σ f² ≤ B² + obj ℓ¹-Lipschitz (Lc) ⇒
  obj после замены Δ на Δ_k ≤ obj до + Lc·n·ε·B — certified
  ε-окрестность (σ_tail × Lipschitz; замыкается гипотезой hF через
  Contracts/TruncatedSVDTail.truncated_svd_error_eq_tail /
  mdl_rank_ce — ССЫЛКОЙ, без импорта Contracts в Theory).
- `adapter_merge_params`: k ≤ L ⇒ 2·k·d ≤ 2·L·d.
- Bench `--mode adapter-merge` (измерено, .tmp/C536/
  bench-adapter-merge.json, замороженный корпус): C533-стек 8
  уровней r=1 (64 парам, телеметрия матриц M_ℓ = I+B_ℓA_ℓ) →
  Δ = M_total − I → ТОЧНЫЙ rational Gaussian ранг ρ = 2 (!) →
  exact merge Δ = C·R (Gauss-Jordan, рационально ТОЧНО,
  возмущение 0 до снапа) → 16 параметров, −75% к стеку, matvec
  1 против 8; certified per-point bound (C533-формула) держится,
  фактическая деградация даже ОТРИЦАТЕЛЬНАЯ (merged-признаки
  пересчитаны из исходных trunk-признаков без промежуточных
  снапов). Матрёшка: k=1 (8 парам) — числовой deflated
  power-iteration кандидат + снап факторов q/2^20 + ТОТ ЖЕ
  точный cert-bound (C489-принцип: числа не доверяем) —
  честно unusable (деградация ~0.5): trade-off кривая
  k = {2: −75% параметров, bound certified; 1: −87.5%, большой
  bound}. Телескоп obj_merged ≤ cycle_start + Σ snap_i +
  merge_bound (assert). Детерминизм: повтор побитово идентичен.
  Регресс C533/C535: побитово (regress-c53{3,5}-mine.json).

## Hagi/Theory/WeightDecayLeak.lean (C538: weight decay leak — P4)

- P4 внешнего плана (mapping C537, top-1): непроецируемый weight
  decay рушит GPM-память (SubspaceLeak 1.945), проецируемый —
  сохраняет ТОЧНО (5.68e-15). Формализовано как проекционный
  инвариант (взгляд ортогонален Hagi/Step/WeightDecay —
  норма-шар): параллельная компонента W·P (память) при
  идемпотентном проекторе P (P*P = P; симметричность не нужна —
  слабее гипотез proj_compl_orth).
- `wd_compl_annihilates` / `wd_proj_preserves`: проецируемый
  decay W ← W − ηλ·(W − W·P) сохраняет W·P ТОЧНО (равенство,
  не bound).
- `naive_decay_parallel` / `naive_decay_norm` / `naive_decay_leak`:
  naive decay (1−ηλ)·W сжимает защищённую компоненту в ТОЧНО
  (1−ηλ) раз; при W·P ≠ 0 и 0 < ηλ < 1 — СТРОГАЯ утечка
  (негатив теоремой, не примером).
- `compl_step_preserves` / `wd_gpm_step_sound` (main): любой
  шаг в дополнении (momentum/polar-NS/EF21 — чёрный ящик,
  гипотеза ΔC·P = 0) + проецируемый decay ⇒ W·P неизменно —
  композиция GPM-механики Continual с weight decay.
- Witness .tmp/C538/trajWdLeak.lean: точные рационалы (ℚ),
  P = diag(1,0), W = [3,5], ηλ = 1/2: naive → [3/2,0],
  projected/full → [3,0], негатив naive ≠ projected = true.
  Аксиомы: только propext/Quot.sound/Classical.choice.

## Hagi/Probability/EmpiricalBernstein.lean (C539: empirical bernstein bound — P1)

- P1 внешнего плана (mapping C537, top-2): Empirical-Bernstein
  confidence как дополнение Freedman-канона (C525) — σ̂-подстановка
  вместо диапазонной R² (Hoeffding/AuditLedger) + аддитивный
  диапазонный член (стиль Maurer–Pontil 2009). В Mathlib EB нет
  (rg: пусто; PMFBridge — Bernoulli-factory полиномы, другая тема).
- `freedman_tail_two_sided`: P[|ΣX| ≥ Δ] ≤ 2exp(−Δ²/(2(nσ²+bΔ))) —
  freedman_tail_low для X и −X + prodPq_union_le (двухсторонность,
  которой нет ни в freedman_confidence, ни в hoeffding_two_sided
  для мартингалов).
- `eb_radius_algebra`: инверсия квадратики Freedman — радиус
  Δ = √(2nσ̂²L) + 2bL даёт exp(−Δ²/(2(nσ²+bΔ))) ≤ exp(−L)
  (тождество Δ² − 2L(nσ²+bΔ) = 2bL·√(2σ²nL) ≥ 0).
- `empirical_bernstein_bound` (main): P[|ΣX| < √(2nσ̂²L) + 2bL] ≥
  1 − α, L = ln(2/α) — EB-радиус с явным √-членом (σ̂) и
  аддитивным членом (b); σ̂² — измеряемая runtime-посылка
  (h_emp-стиль канона, честно: без MP λ-трюка о случайности σ̂).
- `empirical_bernstein_mean_bound`: форма плана |μ̂| <
  √(2σ̂²L/n) + 2bL/n с вероятностью ≥ 1 − α.
- Witness .tmp/C539/eb_contrast.py: ΔCE=0.04, R=11.09, σ̂=0.25,
  α=0.01 — n_Hoeffding = 176,995 (план 177006), n_EB(MP) = 6439
  (план в точности; 27.49×), n_EB(наша форма) = 4267 (41.5×).
  Аксиомы: только propext/Quot.sound/Classical.choice.

## Hagi/Theory/OEComplete.lean (C540: observational equivalence search completeness — P6)

- P6 внешнего плана (mapping C537, top-3): OE hash-consing в
  synthesize_batched_mdl (Levin priority queue + отсечение
  программ с уже виденным вектором значений на пробах; naive
  6478 узлов без решения vs Levin+OE+MITM 896) — дискретная
  теорема полноты: дедупликация НЕ теряет решения.
- `oe_classes_partition`: наблюдательная эквивалентность
  (obsV p = obsV q, вектор значений на фиксированных пробах) —
  подлинная эквивалентность/Setoid; OE-классы корректно
  разбивают пространство программ.
- `oe_search_complete` (main): если p ∈ space (глубинно-
  ограниченное пространство = явный список, конечность явная)
  со спецификационным obs-вектором, OE-дедуп поиск oeFirsts
  вернёт q с obsV q = obsV p — первый представитель каждого
  OE-класса достигается. Полнота ОТНОСИТЕЛЬНО ПРОБ (obs-
  равенство), НЕ семантическая эквивалентность — честно.
- `oe_search_terminates`: (oeFirsts space).length ≤
  space.length — дедуп-обход не длиннее полного перебора
  конечного пространства (терминация структурная).
- Witness .tmp/C540/trajOE.lean: toy-пространство (операции
  not/xor/and/id, глубина ≤ 3, 3 пробы): naive 343 посещений
  vs OE-дедуп 4 (выдача 4 obs-класса), найденный obs-вектор
  идентичен [false,true,false]; негатив (несовместимый с
  пробами target [true,false,false]) → none в обоих.
  Аксиомы: только propext/Quot.sound (def-ы — без аксиом).

## Hagi/Theory/ExactBypass.lean (C541: exact bypass zero CE — P8)

- P8 внешнего плана (mapping C537, top-4): Exact-First Residual
  Coupling — символьные эксперты с сертификатом PROVEN_EXACT
  перехватывают детерминированные паттерны (0 нейронных FLOP;
  связка z_joint = z_core + Σ g·α·φ — DerivAlong/
  CECoupledShortcut). Теорема корректности в вероятностной
  семантике: p = 1 на истинном байте ⇒ точечный log-loss
  −ln 1 = 0 РОВНО; вклад покрытия нулевой; CE линеен по
  позициям ⇒ CE_total = 0 + CE_residual (GapBuffer-разложение).
- `ce_pointwise_of_prob_one`: p = 1 → cePoint p = 0 (ядро P8).
- `ce_covered_zero`: (∀ x ∈ xs, p x = 1) → ceSum p xs = 0 —
  суммарный CE-вклад PROVEN_EXACT-покрытия нулевой.
- `ce_split` / `ce_total_eq_residual`: линейность CE по
  позициям (байты независимы) ⇒ на смешанной последовательности
  общий CE равен CE остатка.
- `exact_gate_sound` / `exact_gate_rejects_zero`: honest-гейт —
  покрытие сертифицируется только при p = 1; ошибочное покрытие
  (p = 0 на истинном байте) гейт ОТВЕРГАЕТ (бесконечный
  log-loss = отвергнутый сертификат; junk-лог не используется).
- `ceOneHot_eq_zero_of_softmaxP_eq_one`: мост к канону —
  softmaxP z t = 1 → Hagi.Core.ceOneHot t z = 0 (общий SSOT,
  композиция с CECoupledShortcut без дублирования его типов).
- Witness .tmp/C541/trajExact.lean: смешанная последовательность
  (6 покрытых p=1 + 4 остаточных p<1): вклад покрытия 0.0,
  total = residual (4.264244, бит-в-бит); негатив p=0 → гейт
  false. Аксиомы: только propext/Quot.sound/Classical.choice.

## Hagi/Theory/MiniHagiLoop.lean (C547: мини-HAGI полный self-improving loop)

- C546 roadmap top-1: ВСЕ certified-компоненты эры в ОДНОМ
  прогоне bench (`--mode mini-hagi-loop`, real unified_ledger,
  113 live pts, один трейс, один JSON): P1 exact-bypass (P8) +
  P2/P3 адаптерный рост с certified-шагами + snap (C521/C532) +
  P4 continual-изоляция (C544) + P5 OE-поиск примитивов (C540) с
  EB-гейтом (C539) + P6 метрики. PIN: цель — квантованные
  tau-цели (snap 1/2); bypass-закон = константа модального
  bucket, покрытие = точное равенство (Fraction ==), CE-вклад
  покрытых == 0 бит-в-бит (assert); EB-числа (n_EB vs
  n_Hoeffding) — float-телеметрия стоимости, решение exact.
- Теорема `full_loop_sound` — КОМПОЗИЦИОННАЯ обёртка без новых
  глубоких фактов: под фазовыми гипотезами (дословно посылки
  компонент) выводит КОНЪЮНКЦИЮ инвариантов: ceSum covered = 0
  (`exact_gate_sound`), certified-шаг спускается
  (`adapter_step_certified`), frozen-адаптер — нулевое
  забывание (`adapter_isolation_zero_forgetting`), OE-дедуп
  поиск находит obs-эквивалент (`oe_search_complete`), EB-радиус
  держит валидационное среднее
  (`empirical_bernstein_mean_bound`). LayerLint: Theory→
  Probability (прецедент FlowMatching). Аксиомы: только
  propext/Quot.sound/Classical.choice (ALLAXIOMS PASS, 11939
  теорем).
- Таблица фаз (прогон .tmp/C547/bench.log):

| фаза | компонент | результат |
|------|-----------|-----------|
| P1 exact bypass | ExactBypass | закон const 3/2: 107/113 (94.7%) покрыто, CE-вклад 0 EXACT |
| P2 adapter A | AdapterGrowth | 10 certified-шагов, CE(gapA) 4 → 0.1216 |
| P3 grow + snap | C532/C521 | фича x0·x1, нейтральный вес 0 (obj инвариант ТОЧНО), 6 шагов, CE 0.1214 |
| P4 continual ISO | C544 | адаптер B: 10 certified-шагов, forgetA = 0 EXACT; SHARED-негатив leak 1.386 |
| P5 OE + EB | OEComplete + EB | принят примитив const 2 (+5 позиций): 112/113 (99.1%); n_EB 9649 vs n_Hoeffding 10851 (eps=R/128, σ̂=0.139) |
| P6 метрики | — | 26 certified-шагов, 1 hold, 10 параметров (2 адаптера по 5) |

- Негативи (в прогоне, assert-чувствительность): неверная
  константа на покрытой позиции — ошибка 1/4 ≠ 0 (гейт
  отвергает, аналог exact_gate_rejects_zero); drop ≤ 0 — HOLD,
  состояние не меняется; shared-шаг на A — forgetA > 0.
- Witness .tmp/C547/trajFullLoop.lean: literal CertStepData
  траектории (P2/P3, P4) + #eval checkTrajectory = true ×2 +
  валид-теоремы + P1 zero-CE + негативы (norm_num) + #check
  всех 5 компонент и full_loop_sound; компилируется (witness
  rc=0, .tmp/C547/witness-check.log).

## Hagi/Theory/MiniHagiLoop.lean (C549: итеративный self-improvement loop)

Bench `--mode mini-hagi-loop2` (backward-совместимо; layered
corpus: реальные byte-фичи unified_ledger, 113 позиций,
tau-сетка 1/16 PIN). ЦИКЛ: каждая итерация = OE-поиск в
пространстве, ВЫРОЩЕННОМ из принятых примитивов (aff-семейство
появляется только с принятой константой-якорем; aff2-семейство —
только с принятым аффинным блоком) → EXACT-расширение покрытия
(монотонность bit-exact assert на каждой итерации) →
переобучение адаптера на сжимающемся остатке (certified
snap-GD, drop>0/HOLD) → EB-телеметрия. Стоп: EB-гейт (нет новых
примитивов) или бюджет (MAX_ITER=8).

- Таблица итераций (прогон .tmp/C549/bench.log):

| итер | принятые примитивы | покрытие | CE остатка | steps | params | n_EB/n_H | стоп |
|------|--------------------|----------|------------|-------|--------|----------|------|
| 1 | const 0; const 11/8 | 62/113 (54.9%) | 1504.848→1153.015 | 10 | 4 | 148/170 | — |
| 2 | p1+256·x0+32·x3 (deps p1) | 81/113 (71.7%) | 3334.1→1593.1 | 10 | 4 | 480/679 | — |
| 3 | const 25/16 | 89/113 (78.8%) | 2291.0→1671.1 | 10 | 4 | 493/679 | — |
| 4 | p3+32·x2 (deps p3) | 96/113 (85.0%) | 3053.9→2019.5 | 10 | 4 | 460/679 | — |
| 5 | const 3/2 | 101/113 (89.4%) | 2.486→0.171 | 10 | 4 | 512/679 | — |
| 6 | const 23/16 | 106/113 (93.8%) | 2.584→0.221 | 10 | 4 | 591/679 | — |
| 7 | — (нет новых) | 106/113 (93.8%) | 2.954→0.221 | 10 | 4 | 591/679 | EB-gate |

- Сходимость покрытия: 0 → 54.9 → 71.7 → 78.8 → 85.0 → 89.4 →
  93.8 → 93.8 (стоп, EB-гейт: ни одного нового примитива).
  Остаток 7 позиций — реальный tau-шум вне всех семейств.
- КОМПОЗИЦИОННАЯ ЦЕПОЧКА (негативы в прогоне): закон 2
  (256·x0+32·x3) НЕ находится без блока 1 — max константное
  покрытие L2-остатка = 1 < 5; закон 3 (p3+32·x2) НЕ находится
  без блока 2 — max level-1 покрытие L3-остатка = 0 < 5.
  Дополнительно: неверная константа err = 1/256 ≠ 0; drop ≤ 0
  шаг — HOLD, состояние не меняется.
- Lean (расширение MiniHagiLoop.lean): IterState / iterStep /
  coversPrim; coverage_append_monotone (append-only шаг
  сохраняет покрытие); iterative_loop_sound — индукция: из
  аддитивности каждой итерации покрытие st k ⊆ покрытие st n
  ∀ k ≤ n. Честный пин: новый математический факт — только
  монотонность; звук итерации = full_loop_sound (C547) без
  ослаблений.
- Witness .tmp/C549/trajLoop2.lean: literal CertStepData
  траекторий итераций 1–3 + #eval checkTrajectory = true ×3 +
  негативы (wrong-const ≠ 0 norm_num; no-progress итерация
  принимает 0 примитивов) + #check iterative_loop_sound /
  coverage_append_monotone / full_loop_sound; rc=0
  (.tmp/C549/witness-check.log).

## scripts/bench_bridge.py + Hagi/Theory/MiniHagiLoop.lean (C551: universal-loop, ПОЛНЫЙ живой корпус)

Bench `--mode universal-loop` (backward-совместимо; append-блок
+ choice + dispatch, паттерн C549). СНИМАЕТ компромисс C549
«законы корпусные»: корпус = ВСЕ живые точки ВСЕХ доменных
ключей unified_ledger (113/113, домен = ledger-ключ, без
ручного подсемплирования; smoke_gpu мёртв — без .bin), цели
РЕАЛЬНЫЕ t_i = snap(ce_i, 1/16). Механика C549: итерация =
честный OE-поиск (константы = реальные значения t; линейные
законы p + a·x_j на реальных фичах, сетка a = 1/16..256,
семейство только с принятой константой-якорем p) → EXACT-гейт
(err == 0 assert на каждой позиции, ≥5 НОВЫХ) → монотонность
покрытия bit-exact assert → PER-DOMAIN snap-GD адаптеры на
остатке (изоляция C544: forgetA = 0 — слепки параметров всех
прочих доменов сравниваются bit-exact после КАЖДОЙ фазы
обучения) → EB-телеметрия. Стоп: EB-гейт / MAX_ITER=8.

- Таблица итераций (прогон .tmp/C551/bench.log):

| итер | принятые законы | покрытие | CE остатка | steps | EB/H | стоп |
|------|-----------------|----------|------------|-------|------|------|
| 1 | const 11/8; 25/16; 13/8; 27/16 | 64/113 (56.6%) | →0.636 (mean) | 1130 | 118/170 | — |
| 2 | const 3/2 | 86/113 (76.1%) | →0.523 | 490 | 145/170 | — |
| 3 | const 23/16 | 106/113 (93.8%) | →0.284 | 186 | 581/679 | — |
| 4 | — (нет новых) | 106/113 (93.8%) | — | 20 | 581/679 | EB-gate |

- ЧЕСТНОЕ ЯДРО: покрытие 93.8% = 6 РЕАЛЬНЫХ константных
  CE-кластеров (мультиплицитет 27/22/20/…); НИ ОДНОГО
  линейного закона на реальных фичах не найдено — реальный
  корпус менее детерминирован, чем синтетический C549:
  универсальная сложность корпуса ИЗМЕРЕНА (все линейные
  кандидаты < 5 новых позиций). 106/113 доменов покрыто
  полностью, остаток 7 позиций — реальные CE-выбросы.
- УСТОЙЧИВОСТЬ ОТКРЫТИЙ vs C549 (telemetry c549_stability):
  все 3 закона C549 (const 0; snap(256x0+32x3);
  +32x2) совпадают с реальными целями на 0/113 позиций —
  синтетические законы НЕ переносятся на полный корпус
  (честный результат: слоистые цели были конструкцией).
- forgetA = 0 по ВСЕМ доменам (реальные asserts, не декларация:
  113 доменов × проверка слепков после каждой фазы); drift-детект:
  пересчёт покрытия на глубокой замороженной копии корпуса ==
  живому (106 == 106, bit-exact); негативы: wrong-const err
  1/256 ≠ 0; HOLD unchanged; 1826 certified-шагов, 134 holds.
- Lean: universal_loop_corpus_mono (union-аддитивность
  покрытия: lA ++ lB; композиция iterative_loop_sound, без
  ослаблений). Witness .tmp/C551/trajUniversal.lean: literal
  CertStepData траекторий + #eval checkTrajectory = true ×2 +
  forgetA=0-инстанс + coverage-монотонность на числах прогона +
  негативы + #check iterative_loop_sound /
  universal_loop_corpus_mono; rc=0
  (.tmp/C551/witness-check.log). Freeze 8694 (8693+1); аксиомы
  только propext / Quot.sound / Classical.choice.

## scripts/bench_bridge.py (C553: universal-loop-nl, НЕЛИНЕЙНЫЙ язык примитивов v2)

Bench `--mode universal-loop-nl` (backward-совместимо; append-блок
+ choice + dispatch). Исследование honest-находки C551: расширение
языка примитивов (v2: константы, линейные, ПРОИЗВЕДЕНИЯ x_i·x_j
(10 пар, вкл. квадраты), min/max пар, пороговые (x_j ≥ q ? cA : cB)
с рациональными q из distinct значений фичей — точные точки смены
ветви) на ПОЛНОМ живом корпусе 113.

- H-КРИТЕРИИ зафисированы ДО прогона (.tmp/C553/research.md §4),
  вердикт вычисляется КОДОМ из телеметрии: H1 = принят
  prod/mm/thr; H3 = near-miss (ровно 4 новых exact-позиции) при
  стопе; иначе H2 (язык-относительный). Приоритет H1>H3>H2.
- ВЕРДИКТ: H2 (language-relative) — НЕЛИНЕЙНЫХ законов НЕТ:
  0 принятых prod/mm/thr, 0 near-miss, 19204 кандидата
  (4 итерации × ≤8362), покрытие идентично C551 (106/113,
  93.8%, те же 6 констант). Кластеры значений цели есть,
  зависимости от фичей x — нет ни линейной, ни произведений,
  ни пороговой, ни min/max.
- GATE-FIX (найден прогоном C553, исправлен в нём же): приём
  «≥5 НОВЫХ позиций» считал позиции, уже покрытые кандидатами,
  принятыми РАНЕЕ в той же итерации (stale unc); ложный
  «закон» 11/8 + 4·x0·x0 прошёл гейт, добавив 1 позицию. Фикс:
  newi исключает covered наlive. universal-loop (C551) не
  затронут (там кандидаты одной итерации не пересекались —
  покрытие 106 у обоих).
- Якорная дисциплина: lin — только из принятых констант (как
  C551); prod/mm — zero-anchor bootstrap (const 0 — законный
  примитив; документировано); thr — пары принятых констант.
- Бюджет: усечение top-k по корреляции НЕ требуется —
  измерено явно (≤8.4k кандидатов/итерация, ≤13k pin
  ULNL_MAX_CAND; CL_D=4, все фичи). Критерий на случай роста
  CL_D (top-k по |Pearson corr|) зафиксирован в коде.
- Остальная механика C551 без изменений: per-domain snap-GD
  адаптеры (certified drop>0 / HOLD: 1933 certified, 392 HOLD),
  forgetA=0 bit-exact asserts по всем 113, drift-детект на
  замороженной копии (106==106), монотонность покрытия,
  EB-телеметрия, негативы (wrong-const 1/256 ≠ 0).
- Остаток C551 itemized: 7 точек = 4 мини-кластера
  (7/4 ×3, 2 ×2, 19/8, 31/16) — все ниже гейта ≥5; язык v2
  не закрыл ни один (residual_after_linear в bench.log).
- Lean: НОВАЯ теорема не нужна — oe_search_complete (C540)
  абстрагирован по Prog/space (проверено research §2),
  применим к языку v2. Freeze 8694 (без изменений); аксиомы
  только propext / Quot.sound / Classical.choice.
- Witness .tmp/C553/trajNL.lean: TOY-инстанс нелинейности —
  probes (x0,x1) = (0,5),(1,7),(2,11), цель x0·x1 = [0,7,22]:
  НЕГАТИВ ∀ c a : ℚ, [c, c+a, c+2a] ≠ [0,7,22] (универсальный,
  не по сетке — линейный язык не может); ПОЗИТИВ произведение
  совпадает exactly; + literal траектории полного прогона,
  #eval checkTrajectory = true, forgetA-инстанс,
  coverage-монотонность, негативы wrong-const/no-progress,
  #check oe_search_complete / iterative_loop_sound; rc=0
  (.tmp/C553/witness-check.log).

## scripts/bench_bridge.py + Hagi/Theory/AdapterGrowth.lean (C555: self-compress-loop, H2-ответ roadmap C554)

Bench `--mode self-compress-loop` (backward-совместимо; append-блок
+ choice + dispatch). H2-ответ: законов в корпусе нет (C551/C553),
рост — нейроадаптация; self-compressing цикл learn→merge→learn на
ПОЛНОМ живом корпусе 113: параметры BOUNDED при монотонном росте
знания.

- Фаза 0: констант-кластеры C551 (6 кластеров, 106/113) +
  certified fd-голова w (CL_D=4) на остатке 7 точек, заморожена.
- Итерация ℓ: ADMIT нейтрального ранг-1 уровня (B=0, assert
  obj-инвариант ТОЧНО) → LEARN certified fd-шаги (drop>0 COMMIT /
  HOLD, snap q/2^16) на ВСЕХ живых параметрах (2·K·d merged +
  2·d уровня) → MERGE: Δ_new = (I+BA)·Δ + BA точными Fractions,
  точный ранг ρ (Гаусс–Жордан), exact-факторизация (K = d = 4 ⇒
  ρ ≤ d структурно — adapter_stack_rank_bound), certified
  per-point bound (assert), деплой ранга ρ ≤ K.
- Таблица итераций (прогон .tmp/C555/bench.log): it1 40→8
  (ρ=1), it2 40→16 (ρ=2), it3 40→24 (ρ=3), it4 40→32 (ρ=4),
  it5 40→32, it6 40→32 — параметры после КАЖДОГО merge ≤
  2·K·d = 32 (assert), суммарный certified drop монотонен
  0.158→0.248→0.276→0.317→0.346→0.364, CE остатка 0.435→0.072
  (−84%), телескоп Σ merge bounds = 0 (merge exact, obj сохранён
  бит-в-бит, assert), 56 certified шагов, 0 HOLD, стоп MAX_ITER=6.
- Счёт-контраст БЕЗ merge: 2·L·d = 48 (линейный рост) против
  деплой-бюджета 32 (KISS: контраст растёт с L).
- МАТРЁШКА-НЕГАТИВЫ (агрессивное k<ρ, телеметрия, НЕ в цикле):
  k=3 деградация 5.44, k=2 — 1.22; certified bounds честно
  покрывают (usable=false) — знание стека на d=4 распределено
  по всем сингулярным направлениям; сжатие до k<d теряет
  знание, потому бюджет цикла — k=d (probe-обоснование
  .tmp/C555/research.md §7). Тот же эффект виден в C536 bench
  (matryoshka k=1: usable=false).
- Дрейф-детект: пересчёт константного покрытия на замороженной
  копии 106 == 106 (bit-exact). Негативы: wrong-const 1/256 ≠ 0;
  HOLD unchanged.
- Lean (AdapterGrowth.lean, секция C555): `selfCompressParams`
  (def 2·k·d), `self_compress_params_bounded` (делегат
  adapter_merge_params), `self_compress_params_contrast`
  (k<L, 0<d ⇒ 2·k·d < 2·L·d — без merge линейный рост),
  `self_compress_loop_sound` (телескоп obj ≤ start + Σ bounds
  — делегат grow_snap_cycle_sound (C521/C533-механика) — И
  параметр-бюджет цикла params ≤ 2·k·d при любом n). Freeze
  8698 (8694+4); аксиомы только propext / Quot.sound /
  Classical.choice.
- Witness .tmp/C555/trajSelfComp.lean: literal certified
  траектории it1/it4 + #eval checkTrajectory = true ×2 +
  params-bounded инстанс (32 ≤ 32) + счёт-контраст инстанс
  (32 < 48) + wrong-const негатив + #check C555/C536/C532
  теорем; rc=0 (.tmp/C555/witness-check.log).
- Doc-fix попутно (Boy Scout, одна строка C553-текста): сняты
  backticks с «unc» (не идентификатор) — statuslint снова PASS
  (сбой был pre-existing на HEAD 9103d775, воспроизведён git
  stash до моих правок).

## scripts/bench_bridge.py + Hagi/Theory/AdapterGrowth.lean (C556: distill, top-2 roadmap C554 — констант-кластеры в веса)

Bench `--mode distill` (backward-совместимо; append-блок + choice
+ dispatch). Top-2 ответ roadmap C554: дистилляция 6 констант-
кластеров (C551/C553, 106/113) из символьного exact-гейта в
rank-1 адаптерные веса — символьное знание живёт в нейро-слое,
exact-bypass ветвление отключается, контуры унифицируются БЕЗ
потерь CE.

- Конструкция θ(c) (AdapterGrowth.lean, секция C556):
  `distillAdapter A B x = B *ᵥ (A *ᵥ x + 1)` — rank-1 ветка с
  внутренней bias-единицей (конструктор, не вес; adapterVec C532
  константу дать НЕ может — выход содержит x). θ(c) = (A := 0,
  B := const c): выход ≡ c на ЛЮБЫХ входах ТОЧНО
  (`constant_distill_exact`), 2d параметров
  (`distill_param_count`), 0 обучающих шагов.
- Distill-условие (`distill_coverage_preserved`): t x = c на
  кластере ⇒ p = 1 (`distill_prob_one`) ⇒ ceSum = 0 —
  КОМПОЗИЦИЯ с `exact_gate_sound` C541, не копия; exact-гейт
  можно отключить — нулевой CE обеспечивают веса.
- Distill-таблица (прогон .tmp/C556/bench.log, полный живой
  корпус 113): 6 кластеров (11/8, 3/2, 13/8, 23/8, 25/16,
  27/16), покрытие 106/113; CE кластеров ДО (certified голова
  одна на всё) 0.7831 → ПОСЛЕ (adapter-путь) 0 БИТ-В-БИТ
  (assert; 6× `distill_ce_zero_*` в witness); certified init:
  выход θ(c_j) ≡ c_j assert на всех точках кластера + 4 probe;
  ветвления 113 → 0 (единый adapter-контур на весь корпус,
  residual — прежняя замороженная голова).
- ЧЕСТНЫЙ параметр-контраст (`symbolic_storage_cheaper`):
  дистиллянт 6 × 2d = 48 параметров против 6 констант-ЗНАЧЕНИЙ
  символьного хранения — символьное ДЕШЕВЛЕ по памяти (Lean-факт
  J < 2·J·d при d ≥ 2); ценность дистилляции — унификация
  контуров (0 ветвлений, единый matmul-путь, exact-bypass
  сливается с адаптерным остатком C555 в один нейро-слой), не
  экономия памяти. Timing-телеметрия честно показывает, что
  python unified-проход не быстрее gated (членство в кластерах
  через next()) — структурная выгода в ветвлениях, не в тактах
  интерпретатора.
- Негативы: wrong-const (θ(c)+1/16) err = 1/256 ≠ 0; head-only
  CE на кластерах ≠ 0 (негатив-база «до»); drift-детект frozen
  copy 106 == 106 (bit-exact).
- Freeze 8698 → 8706 (+8: distillAdapter, constant_distill_exact,
  distillProb, distill_prob_one, distill_coverage_preserved,
  distill_param_count, distill_params_total,
  symbolic_storage_cheaper); аксиомы только propext /
  Quot.sound / Classical.choice.
- Witness .tmp/C556/trajDistill.lean: 6× CE=0 инстансов,
  head-CE ≠ 0, wrong-const, параметр-контраст 6 < 48 (norm_num),
  #check всех 8 C556-теорем; rc=0
  (.tmp/C556/gates-witness-check.log).
- ВЫВОД: контуры exact-bypass и адаптерный остаток УНИФИЦИРУЕМЫ
  без потерь CE — константное символьное знание представимо
  rank-1 адаптерами точно, гейт-ветвление устранимо.

## scripts/bench_bridge.py + Hagi/Theory/AdapterGrowth.lean (C558: mini-HAGI v3 — ФИНАЛЬНАЯ СБОРКА, top-1 roadmap C557)

Bench `--mode mini-hagi-v3` (backward-совместимо; append-блок +
choice + dispatch). Референсная сборка «мини-HAGI v3»: ВСЕ
certified-компоненты C547–C556 в ОДНОМ bench-прогоне на полном
живом корпусе (снапшот заморожен на прогон — урок C535: живой
ledger растёт МЕЖДУ прогонами; в прогоне корпус был 115 точек,
против 106/113 в C556 — инварианты стабильны: 6 кластеров,
остаток 7).

- v3-таблица (фазы × метрики, прогон .tmp/C558/bench.log, ОДИН
  трейс, 115 живых точек):

| Фаза | Компонент | Итог (assert в прогоне) |
|------|-----------|-------------------------|
| P1 exact-bypass | C551 const-кластеры | 6 кластеров, покрытие 108/115, остаток 7; gate bit-exact, покрытие монотонно |
| P2 distill | C556 θ(c) rank-1 | CE кластеров = 0 БИТ-В-БИТ (по кластеру + probes); ветвления 115 → 0 |
| P3 residual head | C555 certified fd | 7/7 шагов commit (drop>0), CE остатка 3.8022 → 0.5120 |
| P4 self-compress | C555 merge-цикл | 6 итераций admit→learn→merge; params ≤ 2·K·d = 32 после КАЖДОГО merge (rank 1→…); obj 0.5120 → 0.0733, cum drop 0.4387 монотонен; телескоп obj_final ≤ obj0 + Σ bounds (exact merge ⇒ Σ = 0) |
| P5 EB-стоп | C555 EB-gate | stop = budget MAX_ITER=6 (EB-ветка активна: commit=0 ⇒ STOP); 55 certified-шагов, holds 0, forget=0 (drift-детект bit-exact), 1.87 s |

- Lean (AdapterGrowth.lean, секция C558): `v3_assembly_sound` —
  референсная теорема сборки: конъюнкция делегатов
  `distill_coverage_preserved` (дистилл-ветка: CE = 0) и
  `self_compress_loop_sound` (obj-телескоп + параметр-бюджет
  2·k·dd) БЕЗ ослабления гипотез компонент — итог: единая
  адаптерная машина с bounded-объёмом и certified-CE на каждом
  шаге. Новых глубоких фактов нет (сборка, не дубль — duplint /
  stmdup гейты в силе).
- Witness .tmp/C558/trajV3.lean: #eval checkTrajectory ×2 (P3,
  P4-ит1, числа прогона) + params-bounded 32 ≤ 32 + телескоп-
  инстанс + счёт-контраст 32 < 48 (без merge) + негативы
  wrong-const 1/256 ≠ 0, head-CE на кластерах ≠ 0 + #check
  `v3_assembly_sound` и 4 компонент; rc=0
  (.tmp/C558/gates-witness-check.log).
- Freeze 8706 → 8707 (+1: v3_assembly_sound); аксиомы только
  propext / Quot.sound / Classical.choice.
- ВЫВОД: мини-HAGI v3 = ПОЛНАЯ certified-сборка — exact-bypass,
  дистилляция, адаптерный остаток, self-compressing merge и
  EB-стой собираются в один трейс без потери ни одного
  сертификата (CE кластеров 0, forget 0, параметры bounded,
  obj-телескоп).

## scripts/bench_bridge.py + Hagi/Theory/AdapterGrowth.lean (C560: adapter-transfer, top-2 roadmap C557 — последний unexplored контур)

Bench `--mode adapter-transfer` (backward-совместимо; append-блок +
choice + dispatch). Cross-domain перенос адаптеров: warm-start
домена B копией обученного адаптера домена A vs холодный нулевой
(C532), РАВНЫЕ certified-бюджеты (K=30 snap-GD шагов, commit только
drop>0). Домены = const-кластеры snapped ce (≥5 точек; снапшот
116 точек, 6 доменов). Близость пар pre-registered ДО прогона:
dist = L1(mean_x) + |ce_A−ce_B|/range(ce); пары argmin/median/argmax
всех C(6,2)=15. forgetA=0 — реальный bit-exact assert (A frozen).

- Transfer-таблица (прогон .tmp/C560/bench.log; AUC = Σ exact
  Fraction CE-трейектории за K+1 шагов — первичная drop-скорость):

| Пара (A→B) | dist | arm | AUC | final CE_B | commits | Вердикт |
|---|---|---|---|---|---|---|
| близкая 23/16→3/2 | 0.1245 | cold | 5.8054 | 0.000263 | 26/30 | |
| | | warm | **0.0150** | 0.000332 | 12/30 | T1 |
| | | poisoned | 22.54 | 0.000204 | 29/30 | медленней |
| средняя 11/8→25/16 | 0.3300 | cold | 9.1307 | 0.065203 | 30/30 | |
| | | warm | **2.4962** | 0.067929 | 30/30 | T1 |
| | | poisoned | 25.34 | 0.062607 | 30/30 | медленней |
| далёкая 11/8→27/16 | 0.6898 | cold | 18.160 | 0.249730 | 30/30 | |
| | | warm | **9.9486** | 0.259213 | 30/30 | T1 |
| | | poisoned | 35.71 | 0.240659 | 30/30 | медленней |

- T-вердикт: 3/3 T1-positive по AUC (drop-ускорение ×387 на
  близкой паре: CE@1 0.0015 vs 1.377); честные оговорки: (а) финал
  CE у cold чуть ЛУЧШЕ на всех парах (разница 4-26e-5..0.01 —
  snap-грид: cold за 30 шагов догоняет и попадает в чуть более
  глубокую ячейку); (б) poisoned хуже по drop-скорости (AUC), но
  НЕ хуже по final CE — snap-грид стирает плохой init за 30 шагов;
  (в) T2 на далёких НЕ подтверждён — warm полезен и на далёкой
  паре (позитив-трансфер доминирует в этой постановке).
- Lean: новых деклараций НЕТ (KISS): adapter_step_certified
  сформулирован над произвольными s s' — init в statement не
  входит, warm-start получает ту же гарантию (honest-заметка
  секции C560 в AdapterGrowth.lean). Freeze 8707 (+0); аксиомы
  только propext / Quot.sound / Classical.choice.
- Witness .tmp/C560/trajTransfer.lean: 8 #eval/norm_num-теорем
  (AUC-сравнения 3 пар × {warm<cold, poisoned>cold}, шаг-1
  ускорение, forgetA=0 инстанс) + #check adapter_step_certified /
  adapter_step_hold; rc=0 (.tmp/C560/gates-witness-check.log).
- ВЫВОД: перенос адаптера A как warm-init домена B даёт
  измеренное drop-ускорение на ВСЕХ близостях (T1), forgetA=0
  сохранён, certified-гарантии init-независимы. Последний
  unexplored контур roadmap C557 закрыт (внешний спрос wave205
  удовлетворён измерением).

## scripts/bench_bridge.py (--mode mini-hagi-v3, КОД БЕЗ ИЗМЕНЕНИЙ) (C566: реактивный v3 — новый корпус волн 208–211, top-1 roadmap C565)

Проверка устойчивости знаний v3 на РАСШИРЕННОМ живом корпусе:
волны HAGI_v2 208–211 добавили 7 доменных точек (ns_0115–ns_0121,
trained_at 05:42–07:29 22.11 — все после C558 e40aa426 05:39:51).
Код не менялся (C558/C563) — честное сравнение «один код, разные
корпуса»; корпус C558 реконструирован по trained_at (ce старых
точек неизменен: diff=0 против снапшота C535; P1 на реконструкции
= телеметрии C558 108/115 — реконструкция валидирована). Прогон
на снапшот-копии .tmp/C566/corpus (md5 d29270839403e856a2eb90196606c07e
до/после — корпус заморожен на прогон, урок C535).

- v3-реактив таблица (C558 vs C566, .tmp/C558/bench.log vs
  .tmp/C566/bench.log):

| Метрика | C558 (115 точек) | C566 (122 точки) | Стабильность |
|---------|------------------|------------------|--------------|
| Корпус (live) | 115 | 122 (+7: ns_0115–0121) | рост потока |
| P1 кластеры | 6 | 6 | инвариант |
| Константы | {11/8, 23/16, 3/2, 25/16, 13/8, 27/16} | ТЕ ЖЕ | ДРЕЙФА НЕТ |
| Новые кластеры | — | 0 (нет) | EB-гейт ≥5 не сработал |
| Покрытие | 108/115 (остаток 7) | 115/122 (остаток 7) | = n−7 |
| CE кластеров (P2) | 0 бит-в-бит | 0 бит-в-бит | инвариант |
| Ветвления | 115 → 0 | 122 → 0 | инвариант |
| P3 CE остатка | 3.8022 → 0.5120 | 3.8022 → 0.5120 | те же 7 точек |
| P4 params | ≤ 32 (= бюджет) | ≤ 32 (= бюджет) | bounded |
| P4 obj-телескоп | 0.5120 → 0.0733, Σ bounds = 0 | идентичен числам C558 | инвариант |
| Certified-шаги | 55, holds 0 | 55, holds 0 | инвариант |
| forget | 0 (drift bit-exact) | 0 (drift bit-exact) | инвариант |
| Время | 1.87 s | 2.64 s | +41% на +6% данных (нелинейность loader-подсчёта байтов, известна C563) |

- РЕАКТИВНОЕ САМОРАЗВИТИЕ: все 7 новых точек легли в
  СУЩЕСТВУЮЩИЙ кластер c = 11/8 (19 → 26 позиций; ce новых точек
  1.37–1.40 → snap 11/8) — v3 подхватил живой поток тем же
  exact-гейтом БЕЗ пере-дистилляции старых кластеров (их CE
  остался 0 бит-в-бит) и БЕЗ дрейфа констант: инварианты C551/
  C558 выдержали рост корпуса 115 → 122.
- Witness .tmp/C566/trajV3react.lean (--emit-lean + C566-блок;
  rc=0, gates-witness-check.log): #eval checkTrajectory ×2 (P3,
  P4-ит1, числа прогона), params-bounded 32 ≤ 32, телескоп-инстанс,
  счёт-контраст 32 < 48, coverage-монотонность кумулятива
  [27,53,75,95,110,115] (decide) + 115 ≤ 122 + покрытие = n−7,
  forget=0 инстанс, негативы wrong-const 1/256 ≠ 0 / head-CE ≠ 0;
  #check v3_assembly_sound + 4 компонент.
- Lean: НОВЫХ теорем нет (композиция; freeze identity 8710);
  аксиомы только propext / Quot.sound / Classical.choice.
- ВЫВОД: реактивный v3 подтверждён — на расширенном корпусе
  (+7 точек живого потока) все certified-инварианты стабильны
  без единого изменения кода; новые данные абсорбируются
  существующими кластерами, знания не дрейфуют (forget=0,
  константы идентичны). Известный предел: время растёт
  суперлинейно в loader-части (цель следующей волны).

## Hagi/Theory/AdapterBank.lean (wave210/210b → Lean мост) (C567: adapter bank bridge from hagi v2, top-2 roadmap C565)

Source-anchored мост (прецедент wave199→C530): HAGI_v2 волна
210/210b реализовала bank per-domain адаптеров + warm-start перенос
БЕЗ теории; C567 формализует семантику их КОДА точно (что код
делает — и честно НЕ обещает того, чего в нём нет).

- Source-anchors (C:\HAGI_v2, read-only): hagi/trunk_ops.py:310-345
  (AdapterBank: per-domain independent adapters, ONE shared
  trunk + isolated side-branches, forgetA=0 bit-exact upstream-
  measured), trunk_ops.py:286-303 (adapter_warm_start: копия
  dst.A = src.A.copy(), source untouched by construction),
  hagi/unified.py:147-165 (wave210: fresh слот нейтрален B=0,
  certified-обучение только fresh-домена), hagi/lm.py:770-777
  (forward x + B(A x) из своего слота).
- Таблица код ↔ теорема (Hagi/Theory/AdapterBank.lean, 10 новых
  деклараций, freeze 8720 = 8710 + 13, «new fine»):
  bankUpdate = семантика get/apply/transfer (трогают один слот);
  warmTransfer = adapter_warm_start (копия слота src в dst);
  adapter_bank_isolation — обновление слота j не меняет выход
  слота i ≠ j ТОЧНО (+ obj-форма adapter_bank_isolation_obj):
  конечная форма C544 adapter_isolation_zero_forgetting (гипотеза
  s' i = s i стала структурным фактом bankUpdate);
  warm_transfer_sound — forgetA=0 (слот src не меняется при ЛЮБОМ
  src/dst, включая вырожденную копию себя) ∧ dst = копия src ∧
  certified-шаг с warm-init (adapterStep obj (bank src) cand при
  measured drop — та же гарантия adapter_step_certified, init в
  statement не входит; C560 honest-заметка AdapterGrowth поднята
  до ЯВНОЙ теоремы); warm_transfer_train_isolation — certified-
  обучение dst после переноса не трогает src (честная гипотеза
  src ≠ dst: при src = dst «обучение dst» = обучение A, как в
  коде); bank_composition — bankBatch (fold bankUpdate по N
  доменам) держит выход каждого нетронутого слота ТОЧНО —
  индукция по списку обновлений.
- HONEST (что НЕ гарантируется): transfer-качество (T1/T2 —
  bench-эмпирика C560, теоремы нет и не обещано); негатив в
  witness: warm-init может быть ХУЖЕ cold на measured obj
  (|A−5|=12 > 5 — dual-инстанс к T1-positive 3/3). Shape-mismatch
  ветка transfer→False вне модели (слоты банка гомогенные (d,r)
  по построению); ленивое get-создание слота = нейтральный
  дефолт (adapter_neutral_B, B=0 ⇒ identity); «когда переносить»
  — caller (pre-registered closeness, не теорема).
- Недублирование доказано: rg bankUpdate|warmTransfer|bankBatch
  вне AdapterBank.lean пусто; C544 — изоляция по гипотезе (здесь
  структурно), C560 — комментарий (здесь теорема); stmdup PASS.
- Witness .tmp/C567/trajBank.lean (rc=0,
  gates-witness-check.log): банк Fin 3 × (Fin 1, Fin 2), точная
  матричная арифметика: изоляция слота 0 при обновлении слота 2
  (bank0_slots_neutral: все слоты identity — B=0), forgetA=0
  после warm 0→2 + ОБУЧЕНИЯ слота 2, вырожденный перенос
  warmTransfer bank 1 1 = bank, copy-семантика dst, certified
  COMMIT с warm-init, bank_composition инстанс (batch слотов
  0,1 не трогает слот 2), негатив warm-hуже-cold; #check
  adapter_bank_isolation / adapter_bank_isolation_obj /
  warm_transfer_sound / warm_transfer_train_isolation /
  bank_composition / adapter_step_certified.
- Гейты (.tmp/C567/gates-*.log, все PASS): build (19357 jobs),
  reachlint (544 modules), trivialint, triviality, mathlibpin
  (fc4f59e5), duplint, nslint, doclint, layerlint, statuslint,
  challenge 2/2, stmdup, machinediff (2000 configs),
  assumptionscan, testasum, testfreeze, mergemodule (20 tests),
  allaxioms + testallax (только propext / Quot.sound /
  Classical.choice — #print axioms на всех 5 теоремах C567),
  premisereg, freeze (8720, 0 aliased), genindex (544 modules),
  witness-check (rc=0).
- ВЫВОД: семантика wave210/210b AdapterBank + warm-start
  формализована точно (изоляция слотов, forgetA=0 копией,
  init-независимая certified-обучаемость, N-доменная композиция);
  граница честности проведена явно: transfer-качество — эмпирика,
  теоремой не подменено.
