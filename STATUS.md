# STATUS — основные результаты по Lean-файлам

Для каждого файла указаны главные доказанные результаты, а не все вспомогательные теоремы. Существенные условия сохранены.

## Hagi.lean

Корневой модуль импортирует и повторно экспортирует библиотеку Hagi. Собственных определений или теорем он не объявляет; доказанные результаты относятся к импортированным модулям.

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

## Hagi/Architecture/FactorRank.lean

- `nonnegFactorization M k` означает точное разложение `M = W * H` с поэлементно неотрицательными `W`, `H`; `nonnegRank M` задаёт наименьшую допустимую внутреннюю размерность.
- `rank_le_nonnegRank`: если существует `k` с `nonnegFactorization M k`, то `M.rank ≤ nonnegRank M`.
- `positive_measure_pos_prob`: для вероятностной меры `μ`, измеримого `F` и `0 < μ F` доказаны `0 < μ F` и `μ Fᶜ < 1`; равенство `μ Fᶜ = 0` не следует.
- `regimeC_fractional`: из `regimeCFactor W r` следует `0 < W.rank - r ∧ W.rank - r < k - r`.

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

## Hagi/Autonomy/Hedge.lean

- `hedge_step`: для вероятностного `p`, потерь `0 ≤ l i ≤ 1` и `0 ≤ eta ≤ 1` сумма `∑ i, p i * exp (-eta * l i)` не превосходит `1 - eta * ∑ i, p i * l i + eta ^ 2 / 2`.
- `hedge_telescope`: если `0 ≤ 1 + u t` для всех `t`, то `∏ t < T, (1 + u t) ≤ exp (∑ t < T, u t)`.
- `router_regret_bound`: при `0 < K`, `0 < eta` и посылке hsurv выполняется `A - Lstar ≤ Real.log K / eta + eta * T / 2`.

## Hagi/Autonomy/HedgeSurvivor.lean

- `hsurv_derived`: для потерь `0 ≤ l t i ≤ 1` и `0 ≤ eta ≤ 1` выводится точная экспоненциальная нижняя оценка выживания через нормированные веса `ewNorm` и член `T * eta ^ 2 / 2`.
- `ewNorm_as_mirror`: вес `ewNorm l eta t i` равен соответствующему `mirrorStep` с накопленными потерями и параметром `1 / eta`.
- `ewNorm_survivor_lower` (C228, анти-лок-ин): при ℓ ≥ 0 и η ≥ 0
  `ewNorm ≥ (1/K)·exp(−η·Σ_{t<T} ℓ t i)` — вес убывает не быстрее
  экспоненциально по собственной накопленной потере, роутер не может
  навсегда shut out ключ; посылки слабее, чем у `hsurv_derived`
  (только ℓ ≥ 0, регрет-сторона при этом не утверждается).

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

## Hagi/Budget/ActiveCompute.lean

- `active_flops`: доказано арифметическое разложение `(c + r) * d = c * d + r * d`; это заданная модель стоимости, а не измерение оборудования.
- `switching_never_exceeds_dense`: при `c + r ≤ d` выполняется `(c + r) * d ≤ d * d`.
- `active_beats_dense_family`: при `c + r ≤ d` и `2 ≤ N` одновременно доказаны `N * ((c + r) * d) ≤ N * (d * d)`, `(c + r) * d ≤ d * d` и `d * d ≤ N * d * d`.

## Hagi/Budget/AnytimeCondensation.lean

- `pointwise_upper_band`: при `0 < T`, если ни для одного `v` не существует `t < T` с `μ + u ≤ g v`, то `g v < μ + u`.
- `anytime_condensation`: для положительной нормированной `q`, `0 < T`, `0 < σ2`, `0 < α < 1`, субгауссова ограничения hcgf и отсутствия выходов `g` и `2 * μ - g` за порог `μ + √(2 * σ2 * log (T / α))` доказано `ceOneHot t (m + (g - μ)) / 2 + ceOneHot t (m - (g - μ)) / 2 - ceOneHot t m ≤ 2 * σ2 * log (T / α)`.
- `condensation_pipeline`: сохраняет ту же оценку и показывает, что для невозрастающей последовательности val из `val L < epsL` следует `val j < epsL` при всех `j ≥ L`.

## Hagi/Budget/BatchCap.lean

- `sfo_global_min`: при `0 ≤ X`, `0 < c`, `0 ≤ Y` и `Y / c < s` точка `criticalS c Y` минимизирует `sfoCost X c Y` по таким `s`.
- `critical_batch_lower`: при `0 < Y`, `0 < Z < ε` выполняется `9 * Y ^ 2 / (4 * ε ^ 2) < (criticalS (ε - Z) Y) ^ 2`; доказана оптимизация заданной стоимостной модели.
- `optimal_split`: при положительных `A`, `C`, `B` выполняются `A / √(A * B / C) + C / √(C * B / A) = 2 * √(A * C / B)` и `√(A * B / C) * √(C * B / A) = B`.
- `batchCapSaturates`: при положительных `A`, `C`, `b*` и `C * bstar ^ 2 / A ≤ B` значение `batchEff A C bstar B` равно `b*`.

## Hagi/Budget/BitAlloc.lean

- `distill_chain_telescoping`: из `S k ≤ E k + delta k` для `k ≤ n` и `E (k + 1) ≤ S k` для `k < n` следует `S n ≤ E 0 + ∑ k ∈ Finset.range (n + 1), delta k`.
- `harvest_budget`: при `0 ≤ rho < 1`, `0 ≤ gamma`, `0 ≤ D 0`, спаде `D (t + 1) ≤ rho * D t` и `gain t ≤ gamma * D t` сумма первых `n` выигрышей не превосходит `gamma * D 0 / (1 - rho)`.
- `stable_factor_two`: при `0 ≤ c i` отсутствие строго улучшающего перевода одной единицы бюджета влечёт `layerError (c j) (f j) ≤ 2 * layerError (c k) (f k)` для `f k ≠ 0`.
- `water_filling_inner_optimum`: при `0 < n`, `0 < c i`, равных суммах бюджетов и выравнивании `c i / 2 ^ (f i)` распределение `f` минимизирует `totalErrorCont c` среди всех таких `g`.

## Hagi/Budget/BitAllocTermination.lean

- `error_chain_descends`: если ошибка строго убывает на каждом соседнем шаге, то она строго убывает между любыми временами `m < k`.
- `improving_chain_injective`: такая последовательность распределений не содержит повторов.
- `no_infinite_improving_chain`: последовательности с постоянной суммой `∑ i, seq t i = B` и строго убывающей `totalError` не существует, поскольку пространство таких распределений конечно.

## Hagi/Budget/CertifiedArgmax.lean

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

## Hagi/Budget/FlopsEconomy.lean

- `equal_budget_baseline`: при `0 < f_B` и `T_B * f_B = F` получается `T_B = F / f_B`.
- `pipeline_beats_baseline_iff`: для любых вещественных `Q₀`, `ΔP`, `ΔB` доказана эквивалентность `Q₀ + ΔP ≥ Q₀ + ΔB ↔ ΔP ≥ ΔB`; сравнение самих приростов остаётся исходными данными.

## Hagi/Budget/JointCost.lean

- `nsIter_block_le`: при `2 ≤ N`, `0 < h` и `0 ≤ r ≤ h` стоимость `N * nsIter h h + 3 * nsIter r (N * h)` не превосходит `nsIter (N * h) (N * h)`.
- `amdahl_ceiling`: при `0 < f < 1` и `0 < k` выполняется `1 / (f + (1 - f) * k) ≤ 1 / f`.
- `offdiag_pythagoras`: если `Wbd i j * Woff i j = 0` для всех индексов, то сумма квадратов `Wbd + Woff` равна сумме квадратов двух компонент отдельно.

## Hagi/Budget/KVWater.lean

- `waterfilling_bound`: при `0 < lam`, равенстве `c i * exp (-kappa * bstar i) = lam` и одинаковых суммах `b` и `b*` остаток `kvResidual c kappa bstar` не превосходит остатка для `b`.
- `waterfilling_inactive_clamp`: при `0 < c_i`, `0 < lam`, `0 < kappa` и `c_i ≤ lam` выражение `max 0 ((1 / kappa) * log (c_i / lam))` равно нулю.

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

## Hagi/Budget/WaterFillingMoE.lean

- `genMean_assoc`: для конечных `ι`, `κ` повторное усреднение `genMean (fun i => genMean (fun j => ce (i, j)))` равно `genMean (fun p => ce p)`.
- `marginalValue_law`: из `marg j = lam * c j` следует `∑ j, marg j = lam * ∑ j, c j`.
- `activeSet_structure`: на непустом конечном `J`, если `marg0 j > lam * c j` для всех `j`, то `lam * ∑ j, c j < ∑ j, marg0 j`.

## Hagi/Budget/WeightedExpAlloc.lean

- `weightedExpAllocation_budget`: на конечном непустом `ι` при `0 < κ i` и `0 < w i` построенное распределение точно удовлетворяет `∑ i, w i * weightedExpAllocation c κ w B i = B`.
- `weightedExpAllocation_marginal`: при дополнительном `0 < c i` маргинальные величины `c i * κ i * exp (-κ i * allocation i)` равны `weightedExpPrice c κ w B * w i`.
- `weightedExpAllocation_optimal`: для любого вещественного `r` с тем же взвешенным бюджетом экспоненциальный остаток построенного распределения не больше остатка `r`; это непрерывная, а не целочисленная оптимальность.

## Hagi/Legacy/MasterChallenge.lean

- `master_hagi_core_comparator`: при `0 ≤ lam`, `0 ≤ nu`, `0 ≤ epsQ` и `CorePremises S S' epsQ w` потенциал после перехода не превосходит исходного минус `verify.decrease`, плюс `lam * verify.riskSpend + nu * epsQ`.
- Та же теорема доказывает точное бюджетное равенство `S'.toGrowthState.budget = S.toGrowthState.budget - (verify S.toGrowthState).budgetSpend`; все условия `CorePremises` остаются посылками.

## Hagi/Cert/Core.lean

- Каноническое ядро сертификации (master plan v3, S1+S2): `SystemMetrics` (objective/risk/budget/task как функции состояния), `StepObligations` (отдельная структура с floor), `FloorsKept` — контракт нижних граней.
- `CertStep` — сертифицированный прогресс: положительный drop, спуск `objective s' ≤ objective s − drop`, точные законы потребления budget_next/risk_next с неотрицательными остатками  и floorsKept; `CertStep.budgetBound`/`CertStep.riskBound` — производные точечные оценки.
- `HoldStep` без утверждения прогресса всегда доступен (`HoldStep.id`); `TransitionStep` = `progress | hold`.
- Композиция: `CertStep.trans` (те же obligations), `CertStep.trans'` (второй шаг против поточечно сильных obligations `obl₁.floor t ≤ obl₂.floor t`); телескопы `trajectory_telescope` (по `Finset.range n`) и `trajectory_telescope_fin` ограничивают терминальный objective суммой drop'ов.

## Hagi/Challenge/MasterChallengeV3.lean

- `master_hagi_challenge_v3`: для цепочки `StepCert`, согласованных drops и spends, начального `FloorKept` и `0 ≤ b 0`, при `1 ≤ n` доказаны `obj (f n) < obj (f 0)` и `∑ t < n, drops t ≤ obj (f 0) - obj (f n)`.
- На конечном состоянии сохраняются `FloorKept`, `0 ≤ b n` и `b n ≤ b 0 - ∑ t < n, spends t`.

## Hagi/Contracts/BatchCEAlignmentBudget.lean

- `rangeCurvature_nonneg` и `batchRangeSquare_le_rangeCurvature_mul_alignment`: `0 ≤ rangeCurvature X` и `batchRangeSquare X θ y ≤ rangeCurvature X * batchAlignment X θ y`; граница сохраняется при тотализации пустого batch.
- `fixedBatch_sum_alignment_le_initial`, `fixedBatch_alignment_summable` и `fixedBatch_tsum_alignment_le_initial`: при непустом `V` суммы `batchAlignment` по фактической `fixedBatchState`-траектории сходятся, а конечные суммы и `∑' t, batchAlignment ...` ограничены `((rangeCurvature X + 1) / 2) * batchCEObjective X y S`.
- `fixedBatch_minNorm_tendsto_zero` и `fixedBatch_meanGradient_tendsto_zero`: при непустом `V` наблюдаемая точка `batchGradientMinimizer` стремится к нулю; фактический `WithLp.toLp 2 (meanResidualTranspose X (coreParameters (fixedBatchState X y S opCost opRisk write t)) y)` стремится к нулю без дополнительной посылки непустого `V`, включая случай `B = 0`.
- `fixedBatch_meanDirection_tendsto_zero`: общее направление `batchMeanDirection` на той же фактической траектории стремится к нулю, также включая пустой batch. Это не утверждение о нулевых отдельных residual gradients, сходимости параметров или оптимальности CE.
- `fixedAlignmentCesaro_nonneg`, `fixedAlignmentCesaro_le` и `fixedAlignmentCesaro_tendsto_zero`: среднее Чезаро `fixedAlignmentCesaro` неотрицательно; при непустом `V` оно не превосходит `(((rangeCurvature X + 1) / 2) * batchCEObjective X y S) / T` и стремится к нулю. Это слабее отдельного последнего итерата и не даёт held-out качества.

## Hagi/Contracts/BatchCEBestResidual.lean

- `exists_alignment_le_fixedAlignmentCesaro`: при `0 < T` найдётся `t : Fin T`, чьё `batchAlignment` не превосходит среднее Чезаро за префикс.
- `exists_alignment_le_initial_div_time`: при непустом `V` найдётся такой префиксный шаг с `batchAlignment ≤ (((rangeCurvature X + 1) / 2) * batchCEObjective X y S) / T`.
- `exists_sqrt_alignment_le_sqrt_initial_div_time`: та же оценка выполняется после взятия квадратного корня из обеих сторон; это результат о лучшем элементе префикса, а не о последнем итерате.

## Hagi/Contracts/BatchCEGrowth.lean

- `growthObjective_iteratedQuarantinedGrowStep_antitone`: цель `growthObjective` на точной последовательности итераций `quarantinedGrowStep` не возрастает.
- `iteratedQuarantinedGrowStep_budget_nonneg`: если исходный бюджет `S0.state.res.budget` неотрицателен, неотрицательность сохраняется после любого числа таких итераций.
- `growthObjective_iteratedQuarantinedGrowStep_tendsto_ciInf`: неотрицательная антимонотонная последовательность целей сходится к своей точной нижней грани; равенство этой грани нулю или глобальному оптимуму не утверждается.

## Hagi/Contracts/BatchCEGrowthSelection.lean

- `growthAdmissionPlanFold_flops` и `growthAdmissionPlanRollout_flops`: для заданной модели ресурсов сумма стартового и накопленного счётчика flops точно воспроизводится свёрткой и развёрткой плана.
- `growthAdmissionPlanSelection_flops_le_of_objective_eq_and_memory_eq`: если реализованный план допустим, а выбранный план имеет ту же цель и тот же счётчик памяти, то его flops не превосходят flops реализованного плана; требуются также заданные ограничения операций.
- Счётчики относятся к абстрактной модели кандидатов, а не к физической памяти или времени вычислений.

## Hagi/Contracts/BatchCEStepCertificate.lean

- `batchCEObjective_batchTrainStep_lt`: при непустом `V` и `0 < batchRangeSquare X (coreParameters S) y` фактический `batchTrainStep` строго уменьшает среднюю пакетную CE.
- `expandedHalfTrainStep_budget_nonneg`: при `0 ≤ trainingCost` и достаточном исходном бюджете для `expandedFeatureEvaluationCount + trainingCost` бюджет после шага неотрицателен.
- `expandedHalfTrainStep_flops_of_active`: при тех же бюджетных условиях, непустом пакете и строгом условии направления `dirAction ... < 0` счётчик flops увеличивается ровно на заданную сумму стоимости признаков и обучения.
- `floor_kept_batchMinimumNormTrainStep`: для пакета из пяти примеров начальный `FloorKept` относительно `batchCEMeasured` сохраняется после `batchMinimumNormTrainStep`.

## Hagi/Contracts/BatchCETrajectory.lean

- `fixedBatchObjective_sum_certifiedDrop_le_telescope`: при непустом `V` сумма `batchCertifiedDrop` по префиксу не превосходит точную разность между начальной CE и CE после `T` фактических шагов.
- `fixedBatchObjective_tendsto_ciInf`: последовательность значений `fixedBatchObjective` сходится к своей точной нижней грани; нулевой предел, глобальный оптимум и сходимость параметров не утверждаются.
- `evaluatedBatchMinimumNormPath_floor_kept_and_objective_lt`: при допустимой стоимости каждого шага, ненулевом `batchGradientMinimizer`, ограничениях риска, начальном `FloorKept` и `0 ≤ S.res.budget` порог качества сохраняется до `T`, а при `1 ≤ T` конечная CE строго меньше начальной.
- `evaluatedBatchMinimumNorm_twoStep_witness`: построен двумерный пример с двумя фактическими шагами, строгим уменьшением пакетной CE и сохранением заданного порога качества.

## Hagi/Contracts/CEStepCertificate.lean

- `coreParameters_ceTrainStep`: фактические параметры после `State.trainStep` совпадают с параметрами безопасного шага по категориальной CE.
- `coreCEObjective_ceTrainStep_lt`: при непустом `V` и `0 < ceStepRange X (coreParameters S) t` выполненный `ceTrainStep` строго уменьшает категориальную CE.
- `coreCEObjective_identityCEStep_lt` и `batchCEObservation_identityCEStep_lt`: для конкретного двумерного начального состояния доказано строгое уменьшение обеих соответствующих целей; `batchCEObservation_identityInitial_eq` даёт начальному значению `Real.log 2`.

## Hagi/Contracts/ChangingEMTrajectory.lean

- `changingEMPath_nll_antitone`: при `∀ t a i, 0 < observationEvidence (c t a i).1 (c t a i).2 (y i)`, сохранении текущих пар (условие hKeep) и включении носителей текущих постериоров в носители постериоров всех кандидатов следующего шага (условие hClose) агрегированная наблюдаемая NLL не возрастает.
- `changingEMPathDrop_budget` и `changingEMPathKLResidual_budget`: суммы уменьшений NLL и KL-постериора ограничены начальной NLL; обе величины неотрицательны и суммируемы.
- `changingEMPath_nll_tendsto_ciInf`: NLL сходится к своей неотрицательной точной нижней грани, без утверждения об оптимальности модели или сходимости параметров.
- `changingEMPath_drop_tsum_eq_m_add_kl`: полная сумма уменьшений равна сумме выигрышей `changingEMPathMGain` плюс сумме KL-постериора.

## Hagi/Contracts/FactorizedMixtureEM.lean

- `factorizedMixture_nll_le_old`: при конечных `I`, `X` и положительной исходной `observationEvidence` факторизованный выбор меток даёт суммарную наблюдаемую NLL не выше исходной.
- `mixtureUnitQuery_card`: число элементов `Σ _ : I, Option (Fin n)` равно `Fintype.card I * (n + 1)`.
- `mixtureVectorCandidate_card`: число векторов `I → Option (Fin n)` равно `(n + 1) ^ Fintype.card I`; это размеры абстрактных пространств кандидатов, а не затраты исполнения.

## Hagi/Contracts/FiniteEMTrajectory.lean

- `finiteEMPath_nll_nonneg` и `finiteEMPath_nll_antitone`: для конечного замкнутого семейства с `∀ a i, 0 < observationEvidence (c a i).1 (c a i).2 (y i)` и включением носителя постериора каждого элемента base в носитель постериора каждого кандидата для всех `i` агрегированная NLL неотрицательна и не возрастает.
- `finiteEMPath_nll_eventually_constant`: последовательность NLL стабилизируется после некоторого `N`.
- `finiteEMPath_nll_ciInf_attainment`: точная нижняя грань NLL достигается на некотором фактическом шаге; одновременно `finiteEMPath_nll_tendsto_ciInf` доказывает сходимость к ней.
- `finiteEMPath_succ_eq_of_nll_eq`: из `finiteEMPathNLL ... (n + 1) = finiteEMPathNLL ... n` следует `finiteEMPath ... (n + 2) = finiteEMPath ... (n + 1)`, то есть следующий канонический выбранный индекс сохраняется; глобальный оптимум и сходимость параметров не утверждаются.

## Hagi/Contracts/GatedCEStepCertificate.lean

- `gatedCEObjective_gatedCETrainStep_lt`: при непустом `V` и `0 < gatedAlignment X (coreParameters S) t` фактический `gatedCETrainStep` строго уменьшает целевую CE с гейтингом; `gatedSafeDrop_le_gatedCETrainStep_drop` даёт лишь нижнюю оценку фактического уменьшения.
- `gatedCEPath_antitone` и `gatedCEPath_tendsto_ciInf`: при `0 < δ` и допустимом начальном решении цель на `scaledBiasBinaryPath` не возрастает и сходится к своей точной нижней грани.
- `gatedCEPath_flops_le`: при дополнительном `0 ≤ opCost` счётчик flops после `T` шагов не превосходит `S0.res.flops + (opCost / δ) * gatedCEObjective X t S0`.
- `gatedCEPath_tendsto_eventual_state`: сам защищённый путь стабилизируется после некоторого индекса и сходится к этому конечному состоянию.

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
- `gated_grad_sum_fourth_le_uniform`: для канонической исполненной
  траектории `∑ s ∈ range T, ‖∇L(θₛ)‖⁴ ≤ 4·gatedCurvatureUniformBound X·L₀`
  — точная переформулировка `fixedGatedAlignment_sum_sq_le_uniform`;
  квадратичная форма `∑‖∇L‖²` этим не доказана (нужна отдельная
  оценка кривизны, линейная по alignment).

## Hagi/Contracts/GradientBottleneck.lean

- `logitGradM`: квадратный n×n комплексный матричный вид логит-градиента
  (вещественные записи коэрцированы) — носитель, требуемый Flywheel
  SVD API; прямоугольный C×V случай отложен.
- `gradient_bottleneck_bound`: при посылке `rank Δ ≤ k` всякое достижимое
  логит-обновление `Δ` оставляет Frobenius-остаток не меньше
  квадратичного хвоста сингулярных чисел `logitGradM` за `k` — прямое
  следствие `eckart_young_lower_bound` (C226). Вывод «голова ранга D ⇒
  ранг обновлений ≤ 2D» и нетривиальность хвоста (Prop A.5) отложены
  и не утверждаются; при `k ≥ n` оценка тривиальна.

## Hagi/Contracts/GuardedLogitTrajectory.lean

- `guardedLogitPath_logitCE_antitone` и `guardedLogitPath_logitCE_tendsto_ciInf`: для фиксированного скалярного защищённого контроллера CE не возрастает и сходится к своей точной нижней грани.
- `guardedLogitDrop_tendsto_zero` и `guardedLogitDrop_tsum_le`: уменьшения CE стремятся к нулю, а их полная сумма не превосходит начальную CE.
- `guardedLogitPath_eventually_eq`: сам путь после некоторого `N` постоянен; `guardedLogitPath_tendsto_eventual_value` доказывает сходимость к этому значению.
- Предельная CE не отождествляется с нулём или глобальным оптимумом; внешняя калибровка и обобщение не оцениваются.

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
- `abs_logitGrad_row_le_two`: абсолютная строчная масса ≤ 2 для
  суб-вероятностных `N` (0 ≤ N, ∑ ≤ 1).

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
- `fixedBatch_meanPrediction_tendsto_empiricalTarget_batch_one`: при `B=1`
  `softDef (ceLogits (X 0) θ_t)` стремится к
  `(Pi.single (y 0) (1:ℝ) : Fin n → ℝ)`; это результат для данного одного
  примера, не для всех индивидуальных целей mixed batch.
- Для двух identity features со смешанными метками `[0,1]` при нулевых
  параметрах marginal match `(1/2,1/2)` и нулевой mean residual
  сосуществуют с ненулевыми individual `ceDirection` и CE=`log 2` по
  `mixed_batchLoss_before_eq_log_two`. Это не доказывает нулевую CE,
  сходимость параметров, правильность individual predictions в mixed batch,
  произвольные affine X, held-out качество или runtime-выигрыш.

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
- Реальный asymmetric CE veto возвращает `S`; нулевой mean residual не
  используется как доказательство полного hold и не означает индивидуальный
  CE descent. Уменьшение задаётся CE, а не нормой параметров или saved effects.
- Это одношаговый nonnegative адаптер, включая hold, а не строгий или
  вероятностный StepCert. Nonnegative нового бюджета для произвольного `S`
  здесь отдельно не утверждается; не следуют также parameter/optimum/CE
  convergence, generalization, оптимальное действие, runtime/FLOP выигрыш.

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
- Контроль содержит два same-label примера `Fin 2`: реальный guarded
  `Hagi.Unified.HonestTransition.HonestTransition.objectiveDrop` положителен, бюджет `2→3/2`, риск `0→1/4`,
  `StepCert.budgetSpend=1/2`, `StepCert.riskSpend=1/4`.
  При opCost=3 affordability ложна и strict constructor не применяется.
  Обычный hold остаётся предметом C207 с nonnegative `StepContract`.
- Это accepted-only strict средний CE, а не strict CE каждого sample:
  guard требует лишь non-regression. per-step bound для opRisk≤riskLim, а не cumulative/final risk bound. Не следуют CE→0, сходимость параметров,
  generalization, held-out качество, оптимальность, новое качественное
  измерение, аналитическая гарантия для нелинейного backbone или runtime/FLOP
  экономия.

## Hagi/Contracts/MixtureEMTrajectory.lean

- `mixtureTrajectoryBank_succ`: для положительной исходной свидетельствуемости банк на шаге `t + 1` получается смешиванием текущей модели с соответствующей seed-моделью и весом `mixtureGridWeight`.
- `mixtureTrajectory_selected_model`: канонический путь меток выбирает в банке в точности текущую модель траектории.
- `mixtureTrajectory_close`: частная лемма доказывает включение носителя текущего постериора в носитель постериора любого следующего кандидата.
- `mixtureTrajectory_nll_antitone`: агрегированная наблюдаемая NLL полученной траектории с меняющимся семейством не возрастает; сходимость выбранной модели или параметров не утверждается.

## Hagi/Contracts/NaturalLean.lean

Авторских верхнеуровневых теорем нет. Анонимный пример проверяет на произвольном `BoundedBatchState S` равенство `smoothedGrowthYield S S = 0`: тактика default_apply применяет существующую теорему `smoothedGrowthYield_self`, не создавая нового именованного математического результата.

## Hagi/Contracts/ObjectiveTrajectory.lean

- `sum_le_of_sum_two_mul_div_le`: при `0 < κ` и общей оценке `∑ t < T, 2 * f t / κ ≤ A` для каждого `T` следует `∑ t < T, f t ≤ κ * A / 2`.
- `summable_and_tsum_le_of_sum_two_mul_div_le`: при дополнительном `0 ≤ f t` последовательность `f` суммируема и `∑' t, f t ≤ κ * A / 2`.
- `exists_le_of_sum_two_mul_div_le`: при `0 < T` найдётся `t < T` с `f t ≤ κ * A / (2 * T)`; это оценка некоторого элемента префикса, а не всех поздних элементов.

## Hagi/Contracts/SchellingCandidateSelection.lean

- `mem_feasible_withStructuralConstraint`: допустимость контроллера `a` в усиленной задаче эквивалентна конъюнкции исходной допустимости `a ∈ feasible p M C` и `structuralConstraint (graphOf a) compatibility k top bottom`.
- Структурные условия локальной совместимости и маршрута от каждой верхней вершины к некоторой нижней вершине конечны; физическая безопасность и качество задачи из них не выводятся.

## Hagi/Contracts/SchellingMarkovRouting.lean

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
- `ceOneHot_eq_ceDef_pi_single` и `ceOneHot_eq_klDef_pi_single`: для
  `[Fintype V]`, `[Nonempty V]`, `[DecidableEq V]` и `p=Pi.single t 1`,
  `q=Hagi.Prelude.softDef z` доказано
  `ceOneHot t z = Hagi.Prelude.ceDef p q = Hagi.Prelude.klDef p q`.
- `KLSupported_pi_single_softDef`: при тех же посылках one-hot имеет единичную
  массу, softmax строго положителен и нормирован, а условие поддержки
  `q v ≠ 0 ∨ p v = 0` допускает нули one-hot вне цели. Это открывает применение
  существующей неотрицательности KL, но не новый алгоритм дистилляции.

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
- `parentPreservingQ_theta`: след равен `1 + 2 * Real.cos (Real.pi / 3)`.

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

## Hagi/Data/BytePatch.lean

- `seg_length`: длина сегмента `seg s a b` равна `b - a` в натуральной арифметике.
- `patchBytes_nat`: при `0 < p` и `K ≤ patchCount N p` сумма длин первых `K` патчей равна `min (K * p) N`.
- `patchSeq_total_length`: при `0 < p` сумма длин всех списков `patchSeq s N p` равна `N`.

## Hagi/Data/CertifiedArgmax.lean

- `certified_argmax_strict`: если `|est i - v i| ≤ ε` и истинный отрыв `v imax - v i` строго больше `2 * ε` для всякого `i ≠ imax`, то `est i < est imax`.
- `certified_argmax_ambiguity`: при `0 < ε`, `0 < g ≤ ε` существуют `v`, est с погрешностью не более `ε`, для которых `v 0 > v 1`, но `est 1 > est 0`.

## Hagi/Data/DBridge.lean

- `dQuad_nonneg`: при `0 ≤ pW v` и `∑ v, pW v = 1` квадрат взвешенного среднего `d` не превосходит взвешенного второго момента.
- `dfield_entropy_identity`: для строго положительных распределений корпусов и строго положительных нормированных весов `divField p w` равно разности взвешенной суммы `p i * log (p i)` и выражения энтропии смеси.
- `equilibrium_bracket`: при `0 ≤ rho < 1`, `0 ≤ D + delta` и `G (t + 1) ≤ rho * G t + D + delta` выполняется `G t ≤ rho^t * G 0 + (D + delta) / (1 - rho)`.

## Hagi/Data/DField.lean

- `kl_product`: для строго положительных `p1`, `q1`, `p2`, `q2` и нормированных `p1`, `p2` KL продуктовых распределений равно `klDef p1 q1 + klDef p2 q2`.
- `KL_product_ge_marginal`: при нормировках исходных и целевых распределений `klDef p1 q1` не превосходит KL соответствующих продуктов.
- `dfield_smoothing`: при `0 ≤ p v`, `0 < u v` и `0 < alpha < 1` смесь `(1 - alpha) * p v + alpha * u v` строго положительна для каждого `v`.

## Hagi/Data/DFieldKKT.lean

- `dfield_ascent_transfer`: если `divField_marginal p w j < divField_marginal p w i`, то разность `divField_marginal p w i - divField_marginal p w j` строго положительна.
- Доказан знак линейной первого порядковой модели переноса веса; равенство KL на активном множестве, вогнутость общей задачи и глобальный KKT-оптимум не утверждаются.

## Hagi/Data/DataMixing.lean

- `mixing_loss_convex`: при `0 ≤ K` функция `rho ↦ mixingLoss K c rho` выпукла на всём пространстве пропорций.
- `chunked_sum_exact`: сумма по `range (n * w)` равна двойной сумме по `c < n`, `j < w` значений `f (c * w + j)`.
- `ce_prior_decomposition`: для строго положительных нормированных `p`, `q` сумма `p * log q` равна `∑ p * log p + ∑ p * log (q / p)`.

## Hagi/Data/Distill.lean

- `kl_eq_ce_gap`: для строго положительных `q`, `p` выполняется `klDef q p = crossEntropy q p - crossEntropy q q`.
- `teacher_generated_identity`: `crossEntropy pE pTheta = crossEntropy pE pE + klDef pE pTheta` для строго положительных распределений учителя и ученика.
- `topk_distill_budget_tv`: если `∀ v ∉ S, q v = 0` и `∑ v ∈ S, q v = 1`, `0 < Z ≤ 1`, `p` и `q` положительны на `S` и `klDef q (truncNorm p S Z) ≤ α`, то `klDef q p ≤ α + (1 - Z) / Z`.
- `cooling_topk_bias`: если `m ≤ L v`, минимум `m` достигается, `0 < T` и `card V * exp (-(s / T)) < 1`, отрицательный логарифм оставшейся нормированной массы Гиббса не превосходит `(card V * exp (-(s / T))) / (1 - card V * exp (-(s / T)))`.

## Hagi/Data/DistillRecursion.lean

- `entropy_mix_ge`: при `0 ≤ ν ≤ 1` и строго положительных нормированных `p`, `d` энтропия `freshMix ν p d` не меньше `(1 - ν) * H(p) + ν * H(d)`.
- `entropy_floor`: при `0 < ν ≤ 1`, `0 ≤ δ`, положительных нормированных поколениях и сертификате `H(freshMix ν (p k) d) - δ ≤ H(p (k + 1))` доказано `H(d) - δ / ν - (1 - ν)^T * (H(d) - δ / ν - H(p 0)) ≤ H(p T)`.
- `fresh_data_prevents_collapse`: если дополнительно `H(d) - δ / ν ≤ H(p 0)`, то нижняя граница `H(d) - δ / ν` сохраняется во всех поколениях.
- `fresh_data_prevents_collapse_uniform`: при `δ ≤ ν * ε` и начальном `H(d) - ε ≤ H(p 0)` во всех поколениях сохраняется `H(d) - ε ≤ H(p T)`.

## Hagi/Data/FannesSmooth.lean

- `log_sub_le_div`: при `0 < a ≤ b` выполняется `log b - log a ≤ (b - a) / a`.
- `abs_log_sub_le`: для положительных `a`, `b` справедливо `|log a - log b| ≤ |a - b| / min a b`.
- `entropy_lipschitz_smooth`: при `0 < delta ≤ 1` и `delta ≤ p v, q v ≤ 1` для всех `v` выполняется `|H(p) - H(q)| ≤ (2 / delta + 2 * log (1 / delta)) * TV(p, q)`; полная граница Фаннеса с сингулярным членом не доказывается.

## Hagi/Data/InfoNCE.lean

- `ce_ge_entropy`: для строго положительных нормированных `q`, `p` выполняется `entDef q ≤ crossEntropy q p`.
- `infonce_never_overestimates`: при тех же условиях `k - crossEntropy q p ≤ k - entDef q`.
- `infonce_gap_is_kl`: если все `q v`, `p v` ненулевые, разность этих двух величин равна `klDef q p`.

## Hagi/Data/NessDissipation.lean

- `detailed_balance_zero_ep`: если все потоки `pi i * P i j` положительны и выполнено детальное равновесие `pi i * P i j = pi j * P j i`, то `epRate P pi = 0`.
- `ep_zero_implies_db`: при положительности потоков, стохастичности строк `P`, нормировке `pi` и `epRate P pi = 0` детальное равновесие выполняется для всех `i`, `j`.

## Hagi/Data/PACBayes.lean

- `log_weighted_jensen`: для строго положительной нормированной `q` и строго положительного `x` сумма `∑ i, q i * log (x i)` не превосходит `log (∑ i, q i * x i)`.
- `gibbs_variational`: для строго положительных нормированных `q`, `p` выполняется `∑ i, q i * f i ≤ ∑ i, q i * log (q i / p i) + log (∑ i, p i * exp (f i))`; вероятностный шаг PAC-Bayes здесь не доказывается.

## Hagi/Discovery/PPT.lean

- `truncation_bias`: если ядро `K` не выходит из `S`, а `pi` стационарно, то существование `y₀ ∉ S` с `0 < pi y₀` невозможно.
- `pptMixing`: для `pptKernel K`, входного ограничения `eps ≤ K x y`, нормированных неотрицательных `mu`, `pi` и стационарной `pi` выполняется `TV(chainAt mu K n, pi) ≤ (1 - card Seq * eps)^n * TV(mu, pi)`.
- `stationary_value_ge`: при `0 ≤ V x` и неотрицательной нормированной `pi` выполняется `gamma * Pr_pi[V ≥ gamma] ≤ ∑ x, pi x * V x`.
- `pptSuccess_lower`: из `p ≤ Pr[V(sample) ≥ gamma]` следует `p - Pr[pptRejectGood] - Pr[pptOverrun] ≤ Pr[pptSuccess]`; события проверки и бюджета остаются исходными условиями модели.

## Hagi/Discovery/PPTCanonical.lean

- `discovery_prob_stationary_identity`: на конечном непустом измеримом пространстве с измеримыми одноэлементными множествами для неотрицательной нормированной `pi` вероятность события `gamma ≤ V x` при тождественном выборе из `toPMF pi` равна `∑ x ∈ goodSet V gamma, pi x`.
- Результат касается сконструированного конечного распределения и не описывает инициализацию или смешивание другой цепи.

## Hagi/Dynamics/ControllerPolicy.lean

- `ratio_dominance`: при `0 < K i`, максимальном отношении `Gam ibest / K ibest` и `0 ≤ B` выполняется `Gam j * (B / K j) ≤ Gam ibest * (B / K ibest)`.
- `budget_allocation_dominance`: при `0 ≤ Gam i`, `0 ≤ alloc a` и `∑ a, alloc a * K (idx a) ≤ B` суммарный выигрыш не превосходит `(Gam ibest / K ibest) * B`.

## Hagi/Dynamics/EndpointContraction.lean

- `endpoint_bivariate_bound`: при `0 ≤ κ < 1`, `0 ≤ β` и `x (t + 1) ≤ κ * x t + β * c t` выполняется `x T ≤ κ^T * x 0 + β * ∑ i < T, κ^i * c (T - 1 - i)`.
- `endpoint_geometric_tail`: если дополнительно `0 ≤ cbar` и `c t ≤ cbar`, то `x T ≤ κ^T * x 0 + β * cbar / (1 - κ)`.
- `endpoint_depth_budget`: при `0 < κ < 1`, `0 < ε` и `x 0 / ε ≤ (1 / κ)^T` получается `x T ≤ β * cbar / (1 - κ) + ε`.

## Hagi/Dynamics/FastGrowth.lean

- `capability_takeoff_floor`: при `0 < alpha`, `0 ≤ C 0`, `C (t + 1) ≥ C t * (1 + alpha)^(s t)` и `N ≤ ∑ t < T, s t` выполняется `C T ≥ C 0 * (1 + alpha)^N`.
- `risk_takeoff_counted`: при `0 < beta < 1` и `R (t + 1) ≤ R t * (1 - beta)^(s t)` получается `R T ≤ R 0 * (1 - beta)^(∑ t < T, s t)`.
- `risk_epsilon_floor`: при `0 < eps`, `0 < R0`, `eps ≤ R0`, `0 < beta < 1` и достаточно большом `N` из логарифмического условия следует `R0 * (1 - beta)^N ≤ eps`.

## Hagi/Dynamics/Laws.lean

- `patient_configuration_reaches`: при `0 < κ < 1`, `0 ≤ β`, `0 < ε`, ограничении `c t ≤ cbar`, рекурсии `x (t + 1) ≤ κ * x t + β * c t` и `x 0 / ε ≤ (1 / κ)^T₀` доказано `x T₀ ≤ β * cbar / (1 - κ) + ε`.
- `kl_contraction_budget`: при `0 < κ_KL < 1`, `0 < δ`, `kl (t + 1) ≤ κ_KL * kl t` и `kl 0 / δ ≤ (1 / κ_KL)^T` получается `kl T ≤ δ`.
- `kl_half_steps`: из `kl 0 ≤ KL₀` и `kl (t + 1) ≤ (1 / 2) * kl t` следует `kl T ≤ KL₀ * (1 / 2)^T`.

## Hagi/Dynamics/ProxyGap.lean

- `budget_consumed`: при `0 ≤ e t + delta t` свойство `BudgetAlive e delta eps (T + 1)` влечёт `BudgetAlive e delta eps T`.
- `guarantee_horizon_bound`: если `0 < c ≤ e t + delta t` для всех `t` и бюджет жив на горизонте `T`, то `(T : ℝ) * c ≤ eps`.
- `shift_paid_from_budget`: при `0 ≤ e t`, `0 ≤ delta t`, `S ⊆ range T` и `BudgetAlive e delta eps T` сумма `delta t` по `S` не превосходит `eps`; малость самого сдвига не доказывается.

## Hagi/Dynamics/WallClockTakeoff.lean

- `wallclock_rate_from_cone`: при `0 < alpha`, `0 < tau`, `0 < C 0`, мультипликативном росте по `s t` и `p0 * T - Delta ≤ ∑ t < T, s t` нижняя грань `C T` равна `C 0 * exp ((p0 * log (1 + alpha) / tau) * (T * tau) - log (1 + alpha) * Delta)`.
- `wallclock_rate_from_cone_concentrated`: подставляет `concDelta T delta` вместо произвольного `Delta`; концентрационная оценка, дающая такую нижнюю сумму успехов, остаётся посылкой.
- `wallclock_rate_avg_tau`: при `0 < tauBar`, `0 ≤ p0`, `T ≠ 0`, `∑ t < T, tau t ≤ T * tauBar` и аналогичной нижней сумме `s t` получается экспоненциальная грань с фактическим `∑ t < T, tau t` и коэффициентом `p0 * log (1 + alpha) / tauBar`.

## Hagi/Energy/Cooling.lean

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
- `landauer_cooling_floor`: при `0 < T₀`, `0 < ρ < 1`, `0 < cUnit`, `0 ≤ bits` и посылке `h_emp_cooling` для всех `t < N` сумма диссипаций не меньше `cUnit * bits * (T₀ * (1 - ρ^N) / (1 - ρ))`; геометрическая сумма затрат охлаждения также ограничена `cUnit * bits * T₀ / (1 - ρ)`.

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

## Hagi/Energy/Variational.lean

- `kl_tilted_decompose`: для строго положительных нормированных `q,p` выполнено `KL(q‖tilted p U) = KL(q‖p) − ΣqU + log(Σ_w p w*exp(U w))`.
- `free_energy_variational`: при тех же условиях доказано `ΣqU − KL(q‖p) ≤ log(Σ_w p w*exp(U w))`.
- `gibbs_optimal_bound`: для `T > 0` и строго положительного нормированного `q` доказано `ΣqL + T·Σq·log q ≥ −T·log(Σ_v exp(−L v/T))`.

## Hagi/Ensemble/CompressionCert.lean

- `deltaCost_concat` и обобщение `deltaCost_sum`: стоимость конкатенации дельт равна сумме стоимостей, в том числе `deltaCost (flatMap Δ (range K)) = Σ_{k<K} deltaCost (Δ k)`.
- `merged_bound`: если для каждого добавления задано `risk (δ₀ ++ Δ k) ≤ risk δ₀ + lambda*deltaCost(Δ k) + mu` и `lambda ≥ 0`, то после `K` добавлений `risk ≤ risk [] + lambda*Σcost + K*mu`. Это индуктивная аддитивная оценка риска при переданной посылке happly, а не самостоятельная PAC-Bayes-теорема.

## Hagi/Ensemble/GapLaw.lean

- `twoGap_nonneg`: для строго положительного `p` с суммой 1 зазор `twoGap p d` неотрицателен; `twoGap_zero_iff` утверждает равенство нулю тогда и только тогда, когда `d u = c` для некоторой константы `c` и всех `u`.
- `twoGap_cosh`: двойная сумма с `exp(d u − d v)` точно равна двойной сумме с `cosh(d u − d v)`.
- `pairVarEq`: при `Σp = 1` двойная взвешенная сумма `(d u − d v)^2` равна удвоенной дисперсии `Σp*d² − (Σp*d)^2`.

## Hagi/Ensemble/Hoeffding.lean

- `twoGap_bounded`: для вероятностных `p`, `M > 0` и условия `|d u − d v| ≤ M` доказано `Hagi.twoGap p d ≤ M^2/4`.
- `hoeffding_tail`: если `d v ∈ [a,b]`, `a < b`, веса `w` неотрицательны и нормированы (`∀ v, 0 ≤ w v`, `∑ v, w v = 1`) и `Σw*d = 0`, то масса точек с `ε ≤ d v` не превышает `exp(−2ε²/(b−a)^2)` при `ε ≥ 0`.
- `hoeffding_union_tail`: для конечного семейства `K` таких центрированных функций и тех же неотрицательных нормированных весов `w` масса объединения событий `∃k, ε ≤ d k v` ограничена `card K·exp(−2ε²/(b−a)^2)`.

## Hagi/Ensemble/HoeffdingBridge.lean

- `hoeffding_tail_via_weighted`: для `IsProbSys p`, `0 ≤ X i v ≤ 1`, `n > 0` и `t ≥ 0` вероятность `prodPq` события `t ≤ centeredSum p X` ограничена `exp(−t²/(2*n²))`. Случайный носитель здесь — произведение компонент, а не произвольная зависимая выборка.

## Hagi/Ensemble/MergeIdentity.lean

- `softmax_shift_invariance`: на конечном `V` общий сдвиг логитов `z v + c` не меняет softmax.
- `geometric_mean_logit_mean`: для непустых конечных `V,K`, при `Zᵢ = ∑ᵤ exp(z i u)` доказано поточечное равенство `(∏ᵢ (exp(z i v) / Zᵢ))^(1/card K) = exp((∑ᵢ z i v) / card K) / (∏ᵢ Zᵢ)^(1/card K)`; общий по `v` множитель `(∏ᵢ Zᵢ)^(−1/card K)` сокращается при последующей softmax-нормировке.

## Hagi/Ensemble/MergeMixture.lean

- `merged_output_exact`: для любых вещественных весов `w` линейность даёт `(Σᵢ w i • W i) *ᵥ x = Σᵢ w i • (W i *ᵥ x)`.
- `routing_drift_bound`: если `‖W i *ᵥ x‖ ≤ B` для каждого `i`, то смена маршрутных весов `w` на `w'` меняет выход по норме не более чем на `Σᵢ |w' i − w i|*B`.

## Hagi/Ensemble/MergePrice.lean

- `merge_price_quad`: при `M − Wi = −dev` квадратичная модель `QuadModel xs Wi M` точно равна `sigmaPrice xs dev`.
- `price_zero_iff_ker`: `sigmaPrice xs dev = 0` тогда и только тогда, когда `dotProduct (xs x) dev = 0` для всех `x`.
- `merge_gate_certified`: из выполненного предиката `MergeApproved` заключается `Σᵢ w i*sigmaPrice(xs i)(devs i) + κ*(n'*s)/2 < twoGap`; это распаковка сертифицированного порога, а не доказательство качества произвольного слияния.

## Hagi/Ensemble/MergeScaling.lean

- `two_channel_step_law`: при `a > 0`, `b > 0`, `N > 0` доказана лишь точная эквивалентность `2*a/N^3 − b = 0 ↔ N^3 = 2*a/b`. Утверждений об ускорении обучения, параметрическом паритете или найденном экспериментальном минимуме теорема не содержит.

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

## Hagi/Legacy/HAGICertWitness.lean

- `hagicert_nonvacuous`: построены последовательности состояний и числовые параметры, для которых выполнен `HAGICert … T`. Это свидетель совместимости формального контракта на конкретных данных, а не оценка качества реального обучения.

## Hagi/Legacy/Nonvacuity.lean

- `merge_energy_bridge`: для midpoint-логитов доказано точное `CE(mid) = (CE(z₁)+CE(z₂))/2 − jensenGap z₁ z₂`, а также неотрицательность зазора.
- `h_emp_merge_of_bridge` — доказанная теорема, а не внешняя посылка: она выводит одновременно `CE(mid) ≤ meanCE − jensenGap` и `0 ≤ jensenGap`.
- `corePremises_nonvacuous_strict`: для любого `E` существуют состояния, `epsQ,w`, удовлетворяющие `CorePremises`, с положительными gap и growGain.
- `corePremises_single_step_obstruction`: два подряд `CorePremises` несовместимы с `gap > 0`, `growGain ≥ 0` и `kappa = 0`; это отрицательный результат о статической модели эффектов, а не про всякое обучение.

- C219 (legacy quarantine B2, аудит P0a; 19 модулей): все
  модули Hagi/{Unified,Examples,Challenge}/*.lean из карантинного
  списка B2 перенесены в Hagi/Legacy/ без изменения математических
  тел: 3 файла — чистые renames (ArchitectureTheorem, MasterHAGI,
  TopLevel, 0 байт изменений), 16 — import-переписывание только
  Hagi.Unified.X → Hagi.Legacy.X среди перенесённых модулей
  (18 строк ±). Мотив — вакуумные свидетельства на самом дереве
  наследия (Nonvacuity.lean:521/586/1011 —
  corePremises_two_step_decrease_nonpos,
  full_cycle_two_step_growth_inconsistent,
  state_capability_two_step_inconsistent): карантин отделяет
  наследие от живого корневого import-замыкания; Hagi.lean больше
  не импортирует их, umbrella Hagi/Legacy.lean и lean_lib
  Hagi.Legacy сохраняют собираемость и CI-покрытие.
- Census (.tmp/C219/validation/root-census.tsv SHA-256
  1f1473c24bb7cbbd5a1d24799edc0fced083576b6bb067606985cb590bce6ba0):
  OWNER 12284 → 11862 (−422 = ровно 19 модулей), IR −17 → 1247,
  CONSUMER 38, модули 499 → 480; 2 дублирующихся имени
  (Hagi.System.gainJoint.eq_1, Hagi.Generalization.Qvec.eq_1)
  объяснены OWNER-строками в двух перенесённых модулях; NamePool:
  owner_gone=418, gone_in_pool=0.
- Evidence (cycle C219): lake build rc=0 (.tmp/C219/build2.log);
  полный CI rc=0 (.tmp/C219/final-ci/ci.log SHA-256
  148cb1dcf7349e915872330e327224eb4f2a4d246e4e6d30b70cf9de5d84e5ed,
  1×CI: PASS, 1×ALLAXIOMS: PASS); Freeze PASS, lock идентичен
  снапшоту (.tmp/C219/declarations-before.lock, нулевой diff);
  ReachLint PASS (21 legacy-exempt; отрицательная проба:
  временный недостижимый файл даёт FAIL rc=1); NsLint/DocLint/
  StatusLint PASS; AssumptionScan 1 path-ключ, assumptions.lock
  11 path-only секций (+11/−11). Plan GO
  .tmp/C219/reviews/plan-review.md SHA-256
  ab083f2b26439957b2f2daaae109e80ce5b690e89d2c44262088802b122b3eb6.

- C220 (удаление zero-consumer дубликатов, 8 теорем): удалены
  ew_regret (HedgeSurvivor), mwu_regret_static и mwu_regret_regimes
  (MWU), mirror_regret_uniform (MirrorDescent),
  info_preservation_regret (InfoPreservation),
  forward_thinking_regret (Imagination), hoeffding_fin_via_mgf
  (Ensemble/Hoeffding), gibbs_concentration_via_canon (GibbsCore)
  — только удаления, математические тела соседей не тронуты.
  Sign-off (удалено → канонический выживший): ew_regret →
  router_regret_bound (Hedge.lean); mwu_regret_static /
  mwu_regret_regimes / mirror_regret_uniform /
  info_preservation_regret → mirror_regret;
  forward_thinking_regret → router_regret_bound;
  hoeffding_fin_via_mgf → Ensemble.hoeffding_fin + Foundations
  mgf_hoeffding; gibbs_concentration_via_canon →
  gibbs_concentration_canon. Orphans (осознанное продуктовое
  решение, компилируются, каскадных удалений нет):
  router_regret_bound, mirror_regret, hsurv_derived, mwu_partition_sum,
  mwu_sqrt_bound, one_div_ge_sub — теперь zero-consumer;
  исторические логи .omc с упоминаниями удалённых имён намеренно
  не тронуты.
- Census (C220, .tmp/C220/validation/root-census.tsv SHA-256
  99a557e74773e71545b0a1bda30ff316297969fc3d95f05f93f5d39aaf24f024):
  OWNER 11862 → 11847 (−15 = 8 теорем + 7 компиляторных
  mirror_regret_uniform._simp_* строк), added 0; names_gone —
  ровно эти 15. Freeze --update: lock diff = ровно −8 имён
  (+1 строка path-rename Hagi/Examples/Nonvacuity → Hagi/Legacy
  из C219; +118 additions — pre-existing backlog циклов C214–C219,
  каждое имя проверено в более ранних коммитах git log -S).
- Evidence (cycle C220): lake build rc=0 (.tmp/C220/build2.log);
  полный CI rc=0 (см. .tmp/C220/precommit/scope-review.md);
  DocLint/StatusLint/ReachLint/NsLint PASS. Plan GO
  .tmp/C220/reviews/plan-review-final.md SHA-256
  32b526f0b0946a67bf4813f8c0166772cbebf5a83913da95e3e601da8301f03d.

- C221 (Gibbs corollary): `gibbs_concentration`
  (Hagi/Probability/GibbsCooling.lean) — формулировка байт-в-байт
  неизменна (361 байт, сверка с HEAD-блобом программно), независимое
  ~86-строчное доказательство заменено тонкой ~31-строчной
  конструкцией поверх канонического `gibbs_concentration_canon`
  (GibbsCore): card-мост `(univ.erase vstar).card = card V - 1`,
  дефинициональный мост `exp/∑ = gibbsW/gibbsZ` и private мост
  арифметики `1 - x ≤ 1/(1 + x)` при `x ≥ 0` (C224: дедуплицирован
  в пользу канона `one_div_ge_sub`, GibbsCore).
  GibbsCooling теперь импортирует GibbsCore; мёртвый обратный
  import удалён (цикла нет). Потребители (NernstFannes,
  Thermostat, gibbs_concentration_tendsto) не тронуты.
- Census (C221, .tmp/C221/validation/root-census.tsv SHA-256
  4601e915df73d9c5869379dff8bc28c7c8ac49383f15dc885b605f3d7289246e):
  OWNER 11846 → 11849 (+3 = private bridge-теорема +
  компиляторные gibbsW.eq_1 / gibbsZ.eq_1 из новых использований),
  IR 1247 без изменений, gone 0.
- Evidence (cycle C221): lake build rc=0 (.tmp/C221/build2.log);
  `#print axioms gibbs_concentration` = [propext, Classical.choice,
  Quot.sound]; Freeze PASS без --update (6293, ничего не потеряно/
  не изменено); STMDUP PASS; полный CI rc=0 (см.
  .tmp/C221/precommit/scope-review.md); DocLint/StatusLint PASS.
  Plan GO .tmp/C221/reviews/plan-review.md SHA-256
  464ee293b221a66915494686c9b50c6dd7711f9da11ad9d0c6f073718791d0b0.

Заявление — перенос и карантин 19 модулей без изменения
доказательств; не утверждаются новые математические результаты,
wall-clock, сжатие весов или улучшение качества.

## Hagi/Legacy/NonvacuityHorizon.lean

- `sat_step_laws`: при `γ ≠ 0` параметрическая траектория одновременно удовлетворяет шагу `C(t+1)=C(t)+γ*F(t)` и насыщению `C(t+1)=C(t)+σ*(Cstar−C(t))`.
- `sat_cone_iff`: при `γ > 0` условие `k*satC … t ≤ satF … t` эквивалентно `γ*k*Cstar ≤ (γ*k+σ)*Δ*(1−σ)^t`.
- `witness_achieves_horizon`: при положительных `γ,k,Cstar,C0`, `0<σ<1`, `C0<Cstar`, `1≤T` и геометрическом условии для всех `t<T` доказаны оба закона шага, конус и строгое `satC 0 < satC T`.

## Hagi/Examples/QuadLoopWitness.lean

- `quadE_qhalf`: после `t` полушагов энергия равна `quadE a (qhalf a x t) = (1/4^t)*quadE a x`.
- `quad_loop_horizon`: если `quadGrad a x ≠ 0` и `n ≥ 1`, то `quadE a (qhalf a x n) < quadE a x`; `quad_witness_T3` и `quad_witness_T10` — конкретные специализации.

## Hagi/Legacy/QuadraticConcrete.lean

- `quad_core_premises`: для любых `a : ℝ` и `w : Fin 5 → ℝ` построены квадратичные состояния, удовлетворяющие `CorePremises (quadGen a) (quadGen' a) 0 w`.
- `quad_kappa_at0` даёт `‖fderiv ℝ (quadE a) 0‖ ≤ 1+|a|`; `quad_conj13` проверяет соответствующее неравенство для квантованного скалярного шага с тем же коэффициентом.

## Hagi/Examples/QuadraticEndToEnd.lean

- `qStep_descent`: при `0 < eta < 1` и `x ≠ a` шаг `qStep` строго уменьшает `qLoss a`.
- `qIter_loss`: после `t` итераций потеря точно равна `(1−2*eta)^(2*t)*(x−a)^2`.
- `qQuant_err_bound`: при `Δ>0` и `|y−a| ≤ R` увеличение потери после `gridQ` не превышает `(Δ/2)*(2R+Δ/2)`.

## Hagi/Examples/QuarticWitness.lean

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
- `decision_criterion`: при `ε>0` и `spectralGap A > ε*‖A‖_F` вновь получается та же оценка с множителем 2.

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

## Hagi/Foundations/Chord.lean

- `exp_chord_ab`: для `a<b` и `x∈[a,b]` доказана хордовая оценка `exp x ≤ ((b−x)/(b−a))*exp a + ((x−a)/(b−a))*exp b`; `exp_chord_r` — форма для `exp(r*x)`.
- `log_cosh_le`: для любого вещественного `M` доказано `log(cosh M) ≤ M²/2`.

## Hagi/Foundations/ConeCorridor.lean

- `cone_exact_exponential`: при `α≥0`, `γ>0`, `ρ≥0`, `C t>0`, начальном конусе, капе `C(t+1)≤(1+α)C t`, динамике `D`, пороге на `β`, шаге `C(t+1)=C t+G t` и `γD≤G` доказано одновременно `(1+α)^T*C0 ≤ C T` и `C T ≤ (1+α)^T*C0`.

## Hagi/Foundations/ConeTakeoff.lean

- `takeoff_from_cone`: если `γ,k≥0`, на `range T` выполнен шаг `C(t+1)=C t+γD t`, а на `range (T+1)` — конус `k*C t≤D t`, то `C0*(1+γ*k)^T ≤ C T`.
- `frontier_cone_inductive`: при `α>0`, `γ>0`, `ρ≥0`, `C t>0`, текущем конусе, динамике `ρ*D t + β*C t − ξ t ≤ D(t+1)`, капе и условии `α/γ*((1+α)−ρ)+ξ t/C t≤β` конус сохраняется на следующем шаге; `frontier_cone_invariant` при начальном конусе `α/γ*C 0 ≤ D 0` и выполнении тех же динамики, капа и β-порога для всех `t` распространяет это на все `t`.

## Hagi/Foundations/GrowthBand.lean

- `growth_band_iter`: при `0≤αmin≤αmax` и двустороннем шаге `(1+αmin)C t≤C(t+1)≤(1+αmax)C t` доказаны обе границы `(1+αmin)^T*C0≤C T≤(1+αmax)^T*C0`.
- `saturation_gap`: при `0≤σ≤1` и шаге насыщения зазор точно равен `Cstar−C T=(1−σ)^T*(Cstar−C0)`.
- `saturation_ceiling`: если дополнительно `C0≤Cstar`, то `C T≤Cstar−(1−σ)^T*(Cstar−C0)` и `C T≤Cstar`.

## Hagi/Foundations/GrowthDynamics.lean

- `band_guaranteed_growth_range`: из `C(t+1)=C t+G t`, `b*(1−σ)^t≤G t` для `t<T` и `0<σ≤1` следует `C T ≥ C0 + b*(1−(1−σ)^T)/σ`.
- `time_to_target_log`: при `b≥0`, `0<σ<1`, `C0≤Cstar`, `σ*(Cstar−C0)<b` и `log(1−σ*(Cstar−C0)/b)/log(1−σ)≤T` доказано достижение `Cstar≤C T`.

## Hagi/Foundations/Hoeffding.lean

- `bern_mgf_bound`: для `0≤θ≤1` и любого `s` доказано `1−θ+θ*exp s ≤ exp(θ*s+s²/8)`.
- `mgf_hoeffding_ab`: для конечного непустого `V`, нормированных неотрицательных `q` и `h v∈[a,b]` выполнено `log E_q[e^h] ≤ E_q[h]+(b−a)²/8`.
- `mgf_hoeffding`: если для любых `u,v` выполнено `h u−h v≤D`, то та же верхняя оценка имеет добавку `D²/8`.

## Hagi/Foundations/MesoScale.lean

- `macro_collapse`: для неотрицательных `A,L` с оценками `A ℓ≤a0*ℓ^p`, `L ℓ≤L0*ℓ^(−q)` и `p<q` доказано `A ℓ*L ℓ → 0` при `ℓ→∞`.
- `micro_collapse`: для неотрицательных `A,L` при `p>0`, `A ℓ≤a0*ℓ^p` и ограниченной `L` произведение стремится к нулю справа при `ℓ→0`.
- `meso_peak_exists`: если `EI` непрерывна на `ℓ>0`, положительна в одной точке и стремится к нулю на обоих концах, то существует глобальный максимум на положительной полуоси.

## Hagi/Foundations/Ortho.lean

- `ortho_norm_sq`: для ортонормального семейства `v` на конечном `ι` доказано `‖Σᵢ c i•v i‖²=Σᵢ(c i)²`; имеется и вариант по произвольному `Finset`.
- `gating_tail_bound`: квадрат нормы разности полной суммы и суммы по `s` равен `Σ_{i∈sᶜ}(c i)²`.

## Hagi/Foundations/PerronCone.lean

- `cone_eigenvector_iff`: равенство `coneMatrix γ β ρ *ᵥ coneVec k = (1+γ*k)•coneVec k` эквивалентно `β=γ*k²+(1−ρ)*k`.
- `cone_perron_growth`: при точных линейных шагах `C,D`, этом условии на `β` и `D0=k*C0` доказаны `C T=(1+γ*k)^T*C0` и `D T=k*C T`.
- `h_emp_takeoff_exponential` — имя доказанной теоремы, не дополнительная посылка: из `γ≥0`, `1+γ*k≥0`, шага `C`, оценки `γD≤G` и конуса `kC≤D` следует `(1+γ*k)^T*C0≤C T`.

## Hagi/Foundations/Potential.lean

- `hagiPotential_penalty_drop`: при `epsQ≥0` и `q−epsQ≤q'` доказано `max 0 (qTarget−q') ≤ max 0 (qTarget−q)+epsQ`.
- `sum_sub_mean_zero`: для `n>0` сумма отклонений от среднего равна нулю; `sq_decomp` даёт точное `Σ(r−c)²−Σ(r−mean r)²=n*(mean r−c)²`.

## Hagi/Foundations/QuadEta.lean

- `quad_eta_identity`: для `quadLossAt a w = ½‖w−a‖²` градиентный шаг даёт точное `E(w−η∇E)= (1−η)²*E(w)`.
- `quad_eta_descent`: при `0<eta<2` и `0<quadLossAt a w` новая потеря строго меньше исходной.

## Hagi/Foundations/Recurrence.lean

- `recurrence_upper`: при `0≤ρ<1` и `x(t+1)≤ρ*x t+c` для `t<T` доказано `x T≤ρ^T*x0+c*(1−ρ^T)/(1−ρ)`.
- `contraction_limit`: при постоянном `δ≥0` и аналогичной рекуррентности получается `x T≤ρ^T*x0+δ/(1−ρ)`.
- `growing_batch_stabilized`: при `0<ρ<1`, `ρ=1−ηL`, `σ²≥0`, `b0>0`, `δ≥1`, `ρδ>1`, `T≥1` и заданной шумовой рекурренте доказана явная граница `E T≤ρ^T E0+(η²σ²/b0)*ρ^(T−1)/(1−(ρδ)⁻¹)`.

## Hagi/Foundations/StageCalculus.lean

- `compress_stage`: при `κ,s≥0`, `h_emp_dist : dnorm≤1/2` и `h_emp_lip : E3−E2pre≤κ*s*dnorm` следует `E3−E2pre≤κ*s/2`.
- `joint_stage_cap_optimal`: при `L>0`, `dnorm²≤inner` и посылке `h_emp_smooth` для шага `1/L` доказано `E2≤E1−dnorm²/(2L)`.
- `compound_budget`: при `α≥0`, `αD+J≤ε_c` и `G_next≤D` получается `α*G_next+J≤ε_c`; `adaptive_ns_exists` при `eps≥0` и `e 100=0` лишь даёт существование `s` с `e s≤eps`.

## Hagi/Foundations/Telescope.lean

- `lyapunov_telescope_fin`: если `E(t+1)≤E t−eps` для всех `t<k`, то `E k≤E0−k*eps`.
- `lyapunov_gain_noise`: из `V(t+1)≤V t−gain t+noise t` на горизонте `T` следует `V T≤V0−Σgain+Σnoise`.
- `lyapunov_termination_fin`: при нижней границе `Emin≤E t`, постоянном спуске `eps>0` получается `(k:ℝ)≤(E0−Emin)/eps`.

## Hagi/Generalization/ModeState.lean

- `generalization_safe_step`: при `lam,nu,ε_Q≥0`, посылках `h_emp_fit`, ограничении прироста риска величиной budget и `h_emp_G : Qgen S−ε_Q≤Qgen S'` потенциал удовлетворяет `Φ'≤Φ−ε_E+lam*budget+nu*ε_Q`.
- `modeDrop_rejected`: условия `ModeDrop`, `h_emp_G` и строгое `ε_Q<ε_Qmode` несовместимы.
- `selector_skips_dominated`: при строго положительных весах скаляризации глобальный argmin не равен строго доминируемому checkpoint.
- `qgen_frontier_bridge_invariant`: при `0<α`, `0<γ`, `0≤ρ`, `0≤ηQ`, положительных `C t`, начальном конусе `α/γ*C 0≤D 0`, заданной `ΔQ`-усиленной динамике `h_emp_dyn`, капе и ослабленном пороге `hβ_eased` конус `α/γ*C t≤D t` сохраняется для всех `t`.

- C218: подсчитанные здесь binder-сайты эмпирических посылок
  (h_C_cap=2, hβ_eased=2) занесены в per-file shrink-only реестр
  `AssumptionScan.py` (см. запись C218 в разделе
  Hagi/Unified/MasterHAGI.lean).

## Hagi/Geometry/SphericalSimplex.lean

- `dihedral_angle_ge_pi_div_three` и `dihedral_angle_lt_pi_div_two`: при `x≥2` выполнено `π/3≤arccos(1/x)`, а при `x>1` — `arccos(1/x)<π/2`.
- `euclid_sum_bounds`: для `n≥2` и `K=n(n+1)/2` доказано `(π/3)*K ≤ K*arccos(1/n) < (π/2)*K`.

## Hagi/Growth/AdaptiveQuery.lean

- `avgRadius_shrinks`: при `e≥0` и `0<K≤L` выполнено `e/√L≤e/√K`, а при одном запросе радиус равен `e`.
- `certified_gain_select_avg`: если ошибки всех оценок не превышают `avgRadius e K`, безопасный `a₀` имеет `g a₀>3*avgRadius e K`, то найдётся безопасный `a'` с `g a'>0` и `g a₀−2*avgRadius e K≤g a'`.

## Hagi/Growth/Ceilings.lean

- `gain_product_bound`: норма композиции непрерывных линейных операторов не превосходит произведения норм; `gain_stack_ceiling` при `q≥0` и `‖T‖≤q` для всех слоёв даёт `‖stackComp Ts‖≤q^Ts.length`.
- `frozen_saturation`: для неотрицательного `V` и шага `V(t+1)≤V t−eps t` сумма `eps` на любом `Ico m T` с `m≤T` не превосходит `V m`.
- `growth_dichotomy`: при `V(t+1)≤V t−eps t+b t` либо суммы `b` неограниченно растут, либо существует `B`, для которого все `Σ_{t<T}eps t≤V0+B`.

## Hagi/Growth/ChainToCone.lean

- `chain_feeds_cone`: при `β,κ,D≥0`, нижней границе `β` для четырёх стадийных коэффициентов и `κ*D≤E_raw` доказано `β^4*κ*D≤G_cap`.
- `cone_two_sided_certificate`: помимо `0≤k`, неотрицательных `C,D`, начального конуса `k*C 0≤D 0`, шага и нижней оценки `γD≤G`, требуются верхняя `G≤gbar D`, динамика `D`, `gbar*k≤ρ` и порог на `β`; тогда `k*C t≤D t` сохраняется до `T`.
- `takeoff_from_certificate`: при `β,κ,k≥0`, начальном конусе `k*C 0≤D 0`, стадийных сертификатах, верхней ленте прироста и двусторонней конусной динамике следует `C0*(1+(β^4*κ)*k)^T≤C T`.

## Hagi/Growth/ChainUnification.lean

- `training_core_is_measurement_tail`: если `E_dev=E_aligned`, `G_cap=η_p*η_o*η_s*E_dev`, а E_aligned и `α_align` ненулевые, то `η_p*η_o*η_s=α_trunc*α_safe*α_cap`.
- `deficit_factorizes`: при ненулевых семи измеренных знаменателях отношение двух произведений равно произведению соответствующих семи отношений.

## Hagi/Growth/ConeDynamics.lean

- `cone_reinvest_invariant`: при `C t>0`, `k≥0`, `γ*k≤ρ`, текущем конусе, динамике `ρD+βC≤D'`, капе `C'≤C+γD` и пороге `γ*k²+(1−ρ)*k≤β` следует `k*C'≤D'`.
- `cone_ratio_step_is_reinvest`: те же вывод получается при точном шаге `C'=C+γD`; это специализация reinvest-формы, а не безусловный закон роста.

## Hagi/Growth/FiberNecessity.lean

- `configs_injective_on_separated` и `used_configs_lower_bound`: если разделённые задачи обслуживаются своими конфигурациями, отображение конфигураций инъективно на семействе и `tasks.card ≤ card(image cfg tasks)`.
- `fiber_params_floor`: если у каждой использованной конфигурации `rank q≥rmin`, то суммарное `Σ rank q*d` не меньше `tasks.card*rmin*d`.

## Hagi/Growth/FrontierProduction.lean

- `injection_law_of_measured`: если `D(t+1)≥κ*dis t` и потребность `ρD t+βC t−ξ t≤κ*dis t` для всех `t`, то выполнен `InjectionLaw D C ξ ρ β`.
- `certified_cycle_renewal`: для продуктовой `IsProbSys`, `Y i v∈[0,1]`, `n>0`, `ε>0`, `0≤thr≤1`, `κ≥0` и условий на `D(t+1)` и thr вероятность импликации «большая сумма проб → renewal-неравенство» не меньше `1−2*exp(−2*n*ε²)`.
- `takeoff_lifts_utility`: из `CapabilitySound C U` (то есть `C t≤U t` для всех `t`) и `C0*(1+α)^T≤C T` следует та же нижняя граница для `U T`.

## Hagi/Growth/FrontierScaling.lean

- `takeoff_edge_forced`: при `γ>0`, точном шаге `C=C+G`, нижнем gain-законе, конусе и капе в каждый момент одновременно выполнены `G=α*C`, `D=α/γ*C` и `C'=(1+α)*C`.
- `sustained_takeoff_from_production`: при `α,γ>0`, `ρ≥0`, `C0>0`, начальном конусе, заданных динамике `D`, капе и пороге на `β` доказано `C0*(1+α)^T≤C T`.
- `frontier_asymptotic`: достаточная замена поточечного порога — `ξ t≤ξbar*C t` и `α/γ*((1+α)−ρ)+ξbar≤β`; вывод о горизонтальном взлёте сохраняется.

## Hagi/Growth/GainDecomposition.lean

- `merge_is_mean`: из разложения `mergeDecomp W M dev` следует `N • M=ΣW`.
- `pairwise_variance_identity`: для того же разложения `ΣᵢΣⱼ‖W i−W j‖²=2N*Σ_k‖dev k‖²`.
- `anticorrelated_suppressed`: для любого `u` доказаны `⟪M,u⟫=(Σ⟪W k,u⟫)/N` и `Σ⟪dev k,u⟫=0`; это точная проекционная алгебра, а не утверждение об измеренной антикорреляции.
- `deficit_localizes`: если `ρ,β≥0`, `β^4=ρ` и произведение четырёх стадийных коэффициентов меньше `ρ`, то хотя бы один коэффициент меньше `β`.

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

## Hagi/Growth/GrowthGate.lean

- `verdict_ttt`: при `eps>0`, `eps≤GF` и `R≤eps` доказаны `0≤GF−R` и `eps≤GF`.
- `verdict_grow`: при `eps<R` получается `0<R−eps`; `verdict_exhausted` просто соединяет `GF<eps` и `eps<R`.

## Hagi/Growth/IntegrationOrder.lean

- `sum_perm_invariant`: сумма конечного семейства выигрышей инвариантна относительно любой перестановки.
- `negative_expert_hurts_any_order`: если `g i<0`, полная сумма строго меньше суммы без `i`; `positive_selection_dominates` доказывает то же улучшение для любого `s`, содержащего `i`.

## Hagi/Growth/NoiseDisentangle.lean

- `orthogonal_noise_averaging`: для ненулевого `N`, попарно ортогональных `n i` с `‖n i‖²=σ²` среднее имеет квадрат нормы ровно `σ²/N`.
- `disagreement_convergence_floor`: при `0≤κ<1`, `σ≥0`, `Dseq 0≤D₀` и `Dseq(t+1)≤κDseq t+σ²/N` доказано `Dseq t≤κ^t D₀+(σ²/N)*(1−κ^t)/(1−κ)`.
- `fiber_merge_denoise`: residual ошибки равен `avgVec n−n i`, а его квадрат нормы точно равен `σ²*(1−1/N)` при тех же предположениях ортогональности.

## Hagi/Growth/NonlinearCone.lean

- `sqrt_gain_step`: при `γ,k,x>0` доказано `√x+γ√k/(2+γ√k/√x)≤√(x+γ√(k*x))`.
- `sqrt_gain_takeoff`: если `C0>0`, все `C t>0` и `C(t+1)=C t+sqrtGain γ k (C t)`, то `C T≥(√C0+γ√k/(2+γ√k/√C0)*T)^2`.

## Hagi/Growth/PlasticityLedger.lean

- `kl_le_log_card`: для `IsProbs P`, строго положительных `P i v` и `famMix P v` каждое `KL(P i‖famMix P)≤log(card I)`.
- `radius_le_log_card`: при дополнительном `card I>0` радиус `plasticityRadius P≤card I*log(card I)`.
- `radius_zero_of_eq`: если все `P i` совпадают и положительны, радиус равен нулю.

## Hagi/Growth/RecursiveSelfDevelopment.lean

- `opportunity_renewal`: из `ρD+βC−ξ≤D'` и `(1−ρ)D+δ_O≤βC−ξ` следует `D+δ_O≤D'`; `recursive_self_development` при `C≤C'`, `D≥0`, `δ_O>0` дополнительно даёт `D'>0`.
- `multiplicative_growth`: из `C(t+1)≥C t*exp(αS t−eps t)` для всех `t` следует `C0*exp(α*Σ_{t<T}S t−Σeps)≤C T`.
- `closed_loop_takeoff`: для продуктовой вероятности, `Y i v∈[0,1]`, `SuccessFloor`, `n>0`, `0<δ<1`, `C0≥0`, `eps t≥0`, `α≥0` и заданного шага `C` вероятность импликации «нижняя сумма успехов → экспоненциальная нижняя граница `C n`» не меньше `1−δ`; это не безусловное утверждение роста.

## Hagi/Growth/RoundViability.lean

- `round_exhausted`: при `devEnergy dev=0` и `GainOp` доказаны `ρD−ξ≤D'` и `η*devEnergy dev=0`; `cycle_criterion` — импликативная форма.
- `round_viable`: при точном шаге `C'=C+γD`, `GainOp`, `γ*k≤ρ`, конусе, пороге на `(η_p*η_s)*devEnergy dev` и `devEnergy dev>0` следует `k*C'≤D'`.

## Hagi/Growth/RsiCriterion.lean

- `rsi_step_growth`: из `ρD t+βC t−ξ t≤D(t+1)` и строгого `ξ t+(1−ρ)D t<βC t` следует `D t<D(t+1)`.
- `rsi_cone_criterion`: при `γ>0`, `C t>0`, `ρ≤1`, `D t≤α/γ*C t` и `(1−ρ)*α+γ*ξ t/C t<β*γ` получается тот же строгий рост `D`.

## Hagi/Growth/Saturation.lean

- `saturation_limit`: при `0<σ≤1` и нижнем PL-шаге для любого `ε>0` найдётся `T`, после которого `Cstar−ε≤C t`.
- `pl_gap_geometric_lo`: при `σ≤1`, верхнем PL-шаге и `C0≤Cstar` доказано `(1−σ)^t*(Cstar−C0)≤Cstar−C t`.
- `takeoff_with_saturation`: при `γ,k>0`, `σ≤1`, точном cone-шаге, обеих PL-оценках, `ConeRatio` и `C0≤Cstar` доказана двусторонняя полоса `C0*(1+γ*k)^T≤C T≤Cstar−(1−σ)^T*(Cstar−C0)`.

## Hagi/Growth/SeedOnly.lean

- `cycle_decay_mono`: при `s≥0`, `F>0`, `0<k<F+s` новое `F*(1−k/(F+s))` строго меньше `F` и неотрицательно; `cycle_decay_ratio` даёт точное отношение соседних приростов.
- `channel_switch`: при положительных `F,k,s,b,Cm,Cr` и `√F*(k*Cr)<b*Cm*s` индекс rank-канала строго больше movement-индекса.
- `seed_only_disp_bound`: при посылках `h_emp_lip`, `h_emp_disp_step`, `a,s≥0` и `dispP 0=0` доказано `dispL t≤Lam²*s*Σ_{i<t}a^i`.

## Hagi/Growth/SelfDevelopment.lean

- `self_development_find`: при наличии безопасного `a₀` с `G a₀>0` существует безопасный `a'` с `0<G a'` и `G a₀≤G a'`.
- `certified_gain_select`: если `|Ghat a−g a|≤eps` для всех `a` и `3*eps<g a₀`, найденный безопасный кандидат имеет `g a'>0` и `g a₀−2eps≤g a'`.
- `search_cost_bound`: сумма постоянных стоимостей измерений по `safeCandidates` равна `card*cMeas`; речь о математической сумме, а не о физическом времени.

## Hagi/Growth/StateBinding.lean

- `capability_takeoff_state`: при `0<α`, `0<γ`, `0≤ρ`, положительной начальной capability, начальном конусе, полевых законах шага, gain- и frontier-динамики, капе и пороге на `β` доказано `(S 0).capability*(1+α)^T≤(S T).capability`.
- `candidate_completeness_find`: из `0≤eps`, `CandidateComplete gen G safe eps`, безопасного `a₀` и `eps<G a₀` следует существование сгенерированного безопасного `a'` с `G a'>0` и `G a₀−eps≤G a'`.
- `usableFrontier_renewal`: из ingest-неравенства для dataField и оценки `β*capability−ξ≤r` выводится требуемая frontier-динамика.

## Hagi/Growth/T3Ignition.lean

- `ignitionGate_nonneg`: при `k>0` и `(1−ρ)*k≤cbeta` величина `(cbeta−(1−ρ)k)/k²` неотрицательна.
- `ignitionCeiling_pos`: при `k,ρ>0` и строгом `(1−ρ)*k<cbeta` минимум `min(ρ/k,(cbeta−(1−ρ)k)/k²)` положителен.
- `T3_ignition`: при `β,κ,k>0`, неотрицательных `C,D` на нужном горизонте, `β^4*κ≤ignitionCeiling` и всех стадийных, верхних gain- и динамических сертификатах доказано `C0*(1+(β^4*κ)*k)^T≤C T`.

## Hagi/Growth/Takeoff.lean

- `elasticity_chain`: если `(1+e t)*x t≤x(t+1)` и `1+e t>0` на `range T`, то `x0*∏_{t<T}(1+e t)≤x T`.
- `ratio_takeoff`: при `γ,k>0`, шаге `C(t+1)=C t+γD t` и глобальном `ConeRatio C D k` доказано `C0*(1+γ*k)^T≤C T`.
- `frontier_decay_no_growth`: при `ρ≥0` и `D(t+1)≤ρD t` получается `D T≤ρ^T*D0`; это верхняя оценка затухания frontier, а не самостоятельный вывод отсутствия всякого роста capability.

## Hagi/Growth/Thermostat.lean

- `thermostat_stop`: при `0<α<1`, `T0,δ>0`, `0<θ<1` и `t≥⌈log(δ/(T0*log(1/θ)))/log α⌉` доказано `exp(−δ/(T0*α^t))≤θ`.
- `certified_state_excess_tendsto`: для конечного непустого `V`, глобального минимизатора `E` с энергетическим зазором `δ>0` и верхней границей `Δ` разность средней энергии Гиббса и свободной энергии при охлаждении `T0*α^t` стремится к нулю.

## Hagi/Information/Capacity.lean

- `separated_needs_capacity`: если каждая задача из `SepSeparated good tasks` допускает подходящий ответ через некоторое состояние `S`, то `tasks.card≤card S`.
- `router_capacity_bound`: в аналогичной модели с `encode : A→Q` и `card Q≤2^B` получается `tasks.card≤2^B`. Отдельная `bits_floor` доказывает лишь неотрицательность `logb 2 (card S)` для непустого конечного `S`, а не оценку взаимной информации.
- `recoverable_avg`: при `N>0` и `0<devEnergyF dev` существует `k`, для которого `devEnergyF dev/N≤dev k ⬝ᵥ dev k`.

## Hagi/Information/DiscreteFannes.lean

- `entropy_le_diagonal`: для положительно полуопределённой `A` энтропия не превосходит `Σᵢ negMulLog(Re(A i i))`; `concaveOn_entropy` доказывает вогнутость энтропии на PSD-состояниях.
- `discrete_fannes_coupling`: для вероятностных `p,q` на непустом конечном `ι` и посылки hbridge, отождествляющей энтропию неотрицательной диагонали с `shannon`, доказано `shannon p−shannon q≤tvHalf*log(card ι)+(1+tvHalf)*binEntropy(tvHalf/(1+tvHalf))`.

## Hagi/Learning/BitBudget.lean

- `ternary_bit_error_bound`: если покомпонентно `|QR i j−R i j|≤1/2`, то выходная ошибка ограничена `(√(layerBits m r/bitsPerTrit)/2)*eunorm x`; `bitsPerTrit_pos` отдельно подтверждает положительность знаменателя.

## Hagi/Learning/FOOF.lean

- `foof_normal_eq`: при обратимости `regCov X lam` определённый `foofW V X lam` удовлетворяет `foofW*regCov=V*Xᵀ`.
- `foof_step_identity`: при той же обратимости точно `foofW−W0=(V−W0*X)*Xᵀ*regCov⁻¹−lam • (W0*regCov⁻¹)`. Второе слагаемое является частью доказанного тождества и не опускается.

## Hagi/Learning/FOOFUnique.lean

- `foof_normal_unique`: если `regCov X lam` обратима и обе матрицы `W1,W2` удовлетворяют одному нормальному уравнению `W*regCov=V*Xᵀ`, то `W1=W2`.
- `foofW_unique`: любая матрица `W`, удовлетворяющая этому уравнению, равна каноническому `foofW V X lam`.

## Hagi/Learning/HRCN.lean

- `domainTerm_gauge_shift`: при ненулевом знаменателе сдвиг значений `vs i` на `ws i • b` меняет доменный вклад ровно на `charProjR w b`.
- `hrcn_cross_talk_zero`: для `w≠u` проекция такого изменения вклада домена `w` на характер `u` равна нулю при том же условии ненулевого знаменателя.

## Hagi/Learning/HadamardComplete.lean

- `charRow_sum_offdiag_zero`: для `x≠y` сумма по всем `w` произведений вещественных характеров `charRowR w x*charRowR w y` равна нулю.
- `charProjR_sum_eq_self`: для любого вещественного сигнала на булевом кубе `Σ_w charProjR w v=v`.

## Hagi/Learning/HadamardParseval.lean

- `charProjR_cross_zero`: проекции на разные характеры ортогональны относительно скалярного произведения `⬝ᵥ`; `charProjR_norm_sq` вычисляет квадрат нормы проекции через `(charRowR w ⬝ᵥ v)²/2^k`.
- `parseval`: доказано `v ⬝ᵥ v=Σ_w (charProjR w v ⬝ᵥ charProjR w v)`.

## Hagi/Learning/HadamardProjectors.lean

- `charProjR_idem`: `charProjR w (charProjR w v)=charProjR w v`.
- `charProjR_orthog`: при `w≠u` выполнено `charProjR w (charProjR u v)=0`; `charProjR_add` отдельно подтверждает аддитивность проектора.

## Hagi/Learning/NetworkBudget.lean

- `exists_layer_ge_average`: для `n>0`, неотрицательных `a i` с суммой `N` существует слой `i` с `N/n≤a i`.
- `network_bit_error`: при `L≥1`, `N≥0`, `n>0` и `n` парах слоёв, где номинальные слои `L`-липшицевы и каждая ошибка ограничена `√(N/n)/2`, ошибка композиции не превышает `(√(n*N)/2)*L^n`.

## Hagi/Learning/PertTelescope.lean

- `lip_composition`: при `L≥0` и `L`-липшицевых слоях композиция имеет оценку `L^length` для нормы разности выходов.
- `pert_telescope`: при `L≥1`, `delta≥0` и поточечной ошибке каждой пары слоёв не более delta ошибка всей композиции ограничена `length*delta*L^length`.

## Hagi/Learning/RCDL.lean

- `dual_apply`: для `dualW W0 xs vs` доказана поточечная формула `(W0*q)i+Σ_t dotProduct(xs t)q*vs t i`.
- `gauge_shift`: при ненулевом знаменателе замена `vs i` на `vs i+ws i • b` даёт `weightedSoftmax … q = weightedSoftmax … vs q + b`; выход сдвигается на `b`, а не остаётся буквально инвариантным.
- `gauge_exists`: для `g≠0` и `eps>0` существует `b`, для которого `dotProduct g (s+b)≥eps`.

## Hagi/Learning/RegCovPD.lean

- `regCov_posDef`: при `lam>0` матрица `XXᵀ+lam*I` строго положительно определена; `regCov_transpose` подтверждает симметричность.
- `regCov_det_unit`: при `lam>0` детерминант этой матрицы является обратимым элементом, что даёт условие обратимости для FOOF.

## Hagi/Learning/RouterMix.lean

- `routerMix_apply`: выход по координате `i` равен `Σ_{w∈doms} p w*domainTerm w ks ws vs q i`.
- `router_is_simplex`: при `T>0` и строго положительных `p₀` результат `mirrorStep` строго положителен и имеет сумму 1.
- `routerMix_switch`: доказано алгебраическое сокращение `(routerMix p−p'w•term+p'w•term)=routerMix p`; это тождество отмены слагаемых, а не независимость `routerMix` от самих весов `p`.

## Hagi/Learning/SpectralBudget.lean

- `spectral_budget`: если для каждого `w` квадрат доменной ошибки не превосходит `delta²*‖charProjR w v‖²`, `delta≥0`, то `‖v−Q‖²≤delta²*‖v‖²` в форме скалярного произведения `⬝ᵥ`.
- `zero_energy_domain_free`: из нулевой доменной энергии следует, что любой `e` с `e⬝ᵥe≤0` равен нулю; `charProjR_sub` отдельно доказывает линейность по вычитанию.

## Hagi/Learning/TernaryPert.lean

- `frob_submul`: для конечной вещественной матрицы `E` выходная норма ограничена `√(frobSq E)*eunorm x`; основа — `cs_dotProduct`.
- `ternary_layer_pert`: если `|QR i j−R i j|≤1/2` покомпонентно, ошибка выхода ограничена `√(m*r*(1/2)^2)*eunorm x`.

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
- `floorCappedChunks L r width xs` — тот же producer с точной ёмкостью
  `⌊L / r⌋₊`, без floating-point или expected-ratio вычисления. Из его
  `hsuccess` `floorCappedChunks_flatten` даёт `chunks.flatten = xs`; при
  `0 ≤ L`, `0 < r` `floorCappedChunks_length_le` дополнительно даёт
  `(chunks.length : ℝ) ≤ L / r`.
- При `[Fintype k]`, `∀ l, 0 ≤ c l`, `0 ≤ L`, `0 < r` и том же `hsuccess`
  `floorCappedChunks_cost_le_floor` и `floorCappedChunks_adaptive_le_static`
  используют общий для всех уровней возвращённый счётчик
  `M := fun _ => (chunks.length : ℝ)` и доказывают соответственно
  `adaptiveCost c M ≤ ∑ l, c l * (⌊L / r⌋₊ : ℝ) ^ 2` и
  `adaptiveCost c M ≤ ∑ l, c l * (L / r) ^ 2`; вторая применяет неизменённую
  `adaptive_le_static`. Это специализация к конечному `k` и одному общему
  `chunks.length`, не универсальный arbitrary per-level router.
- Root API использует singleton `floorCappedChunks 1 1 1 [42] = some [[42]]`
  для точного сохранения и прямых применений обеих cost-оценок. Training
  gains не заявляются. Нулевые capacity или width не принимают непустой вход;
  пустой вход законно даёт `some []`. Отказ не является успешным zero-cost
  разбиением, а при непустом входе flatten coverage исключает пустой результат.

Это одно детерминированное fixed-width разбиение входного списка, не
learned/adaptive per-level H-Net routing, causal-поведение, дифференцируемые
границы, физическое хранение или runtime-engineering adapter. Неравенства
относятся только к `adaptiveCost` при указанных nonnegativity/cap hypotheses:
не следуют FLOPs, physical RAM, wall-time, training quality, held-out CE,
IEEE/RNE/BF16, оптимальная end-to-end архитектура или глобальный HAGI.
Throughput, sparsity, compression и качество router не доказываются.

- Для данной конечной последовательности и выбранной функции границ
  `boundaryChunks` начинает новую непустую группу перед каждым следующим
  токеном с флагом true; флаг первого токена игнорируется и не создаёт пустой
  префикс. `length_boundaryChunks` даёт 0 для пустого входа и
  1 + tail.countP boundary для first :: tail. `flatten_boundaryChunks`
  сохраняет вход, `ne_nil_of_mem_boundaryChunks` подтверждает непустоту
  возвращённых групп, а `length_boundaryChunks_le` ограничивает их число длиной
  входа.
- `cappedBoundaryChunks_eq_some_iff` связывает успех с тем же вычисленным
  разбиением и его фактическим count ≤ capacity; пустой вход может успешно
  вернуть some [], а непустой не может вернуть пустой результат.
  `floorBoundaryChunks_length_le` при 0 ≤ L, 0 < r и фактическом успехе даёт
  (chunks.length : ℝ) ≤ L / r. Для конечного k и неотрицательных c
  `floorBoundaryChunks_adaptive_le_static` ограничивает adaptiveCost одним
  возвращённым chunks.length на всех уровнях через
  ∑ l, c l * (L / r) ^ 2. `floorBoundaryChunks_adaptive_lt_of_strict` делает
  оценку строгой лишь при положительной цене c l₀ и фактическом
  (chunks.length : ℝ) < L / r.

Это детерминированный конечный token-functor, не learned/causal/online или
дифференцируемый H-Net router и не произвольный per-level router. Capacity —
абстрактный count, не байты или native память. Model quality, RAM, FLOPs,
latency/runtime, training/held-out CE, BF16/RNE, глобальная оптимальность HAGI
и вывод worst-case из average ratio не утверждаются.

- C214 добавляет `adjacentPairs`: `[] ↦ []`, а
  `a :: rest ↦ (a,a) :: (a :: rest).zip rest`. Все пары после seed имеют
  вид `(previous,current)`; `map_snd_adjacentPairs` восстанавливает исходные
  значения через `Prod.snd`, а `length_adjacentPairs` сохраняет их число.
  Первый `(a,a)` — детерминированный dummy seed, чей флаг C213 игнорирует,
  а не learned prior или forced first flag H-Net. Полярность
  `Prod.fst` неверна: на `[0,1]` получается `[0,0]`.
- Для supplied θ : α × α → Bool маршрут остаётся существующим
  `boundaryChunks θ (adjacentPairs xs)`; `List.splitBy` видит флаг следующей
  пары, поэтому `true` режет перед current, `false` продолжает chunk, а
  dummy в счёт не входит. `flatten_map_snd_adjacentBoundary` возвращает все
  исходные значения после `chunks.map (List.map Prod.snd)` и flatten;
  `length_adjacentBoundary_projection` сохраняет фактический raw route
  count. `length_adjacentBoundary_projection_exact` даёт `0` для пустого
  входа и `tail.countP θ + 1` для непустого paired tail;
  `ne_nil_of_mem_adjacentBoundary_projection` исключает пустые projected
  члены.
- При фактическом hSuccess : cappedBoundaryChunks capacity θ
  (adjacentPairs xs) = some chunks теоремы
  `flatten_cappedAdjacent_projection`, `length_cappedAdjacent_projection_le`
  и `ne_nil_of_mem_cappedAdjacent_projection` доказывают lossless erasure,
  projected count ≤ capacity и непустоту членов одного фактически успешного
  raw route. В противном случае Option даёт none; пустой успешный fallback
  или произвольный count не создаются.
- При фактическом hSuccess : floorBoundaryChunks L r θ
  (adjacentPairs xs) = some chunks теорема
  `floorAdjacent_projection_flatten` сохраняет вход;
  `floorAdjacent_projection_length_le` при `0 ≤ L`, `0 < r` использует
  точную ёмкость Nat floor `⌊L / r⌋₊` и даёт
  `((chunks.map (List.map Prod.snd)).length : ℝ) ≤ L / r`;
  `ne_nil_of_mem_floorAdjacent_projection` доказывает непустоту членов.
  Для конечного k, неотрицательных c и тех же hL/hr/hSuccess
  `floorAdjacent_projection_adaptive_le_static` ограничивает
  `adaptiveCost c (fun _ => projectedCount)` суммой
  `∑ l, c l * (L / r) ^ 2`. Строгая
  `floorAdjacent_projection_adaptive_lt_of_strict` дополнительно требует
  выбранный l₀, `0 < c l₀` и фактический projected count < L / r. Все cost
  формулы используют один фактический count, не caller M или average ratio.
- Итого здесь одна определённая функция и четырнадцать публичных теорем:
  перечисленные `adjacentPairs`, `map_snd_adjacentPairs`,
  `length_adjacentPairs`, `flatten_map_snd_adjacentBoundary`,
  `length_adjacentBoundary_projection`,
  `length_adjacentBoundary_projection_exact`,
  `ne_nil_of_mem_adjacentBoundary_projection`,
  `flatten_cappedAdjacent_projection`, `length_cappedAdjacent_projection_le`,
  `ne_nil_of_mem_cappedAdjacent_projection`,
  `floorAdjacent_projection_flatten`, `floorAdjacent_projection_length_le`,
  `floorAdjacent_projection_adaptive_le_static`,
  `floorAdjacent_projection_adaptive_lt_of_strict` и
  `ne_nil_of_mem_floorAdjacent_projection`.
- Проверенная локальная тестовая θ `!(p.1 + 1 == p.2)` даёт
  `[0,1,3,4,10] ↦ [[0,1],[3,4],[10]]`, а direct successor как cut —
  неверное `[[0],[1,3],[4,10]]`. На `[0,1,1,2,10,11,11]` получается
  `[[0,1],[1,2],[10,11],[11]]`: равные current значения могут принимать
  разные решения в зависимости от previous. Отдельной production-декларации
  nonSuccessorCut нет.

Это generic finite Boolean adjacency над supplied значениями, а не learned,
differentiable, causal, online или per-level router. Paper v2 использует
`Q(current)/K(previous)`, `p₁ = 1`, `≥ 0.5`; pinned code main 3673fe...
использует `Q(previous)/K(current)`, strict step `> 0.5` и normalization
epsilon; источники не усредняются. Lossless относится только к erasure paired
chunks, тогда как H-Net head selection отбрасывает non-head значения.
Первый флаг для будущей head-mask equivalence требуется отдельно; dummy его
не задаёт. Не утверждаются encoder, projection, cosine, zero-norm/tie,
causal stability supplied representations, stateful packed mask,
BF16/Float, runtime, минимальная память, training quality, target-ratio cap,
глобально завершённая или оптимальная модель HAGI.

- C215 добавляет `boundaryHeads`: heads фактического маршрута C213,
  `boundaryHeads boundary xs = (boundaryChunks boundary xs).map List.head?`,
  носитель `List (Option α)`. `length_boundaryHeads` сохраняет точный счёт
  chunks; `isSome_of_mem_boundaryHeads` доказывает, что каждый head —
  реальный токен (пустой head невозможен из-за непустоты chunks);
  `mem_of_mem_boundaryHeads` возвращает каждый head-токен в исходный вход.
- `boundaryHeads_head?_cons` принуждает первый head быть первым токеном
  входа независимо от его флага — структурный аналог forced first head
  H-Net v2 `p₁ = 1`, без Q/K, cosine, порога и normalization epsilon.
  `boundary_of_mem_boundaryHeads_tail` доказывает, что каждый не-первой
  head лежит точно на boundary-токене (private-помощник
  `head_boundary_of_mem_tail` проходит по цепочке `List.splitBy`), поэтому
  chunk-start mask восстанавливается из самих heads.
- На paired route C214 `boundaryHeads_adjacent_first` даёт первым headом
  ровно dummy seed (a, a): seed структурно играет роль forced first head,
  а `theta_of_mem_adjacentHeads_tail` переносит свойство границ на
  θ-пар: каждый не-первой head paired маршрута удовлетворяет θ p = true.
- Nodup честно не заявляется: при boundary = (· == 1) вход [1,1] даёт
  chunks [[1],[1]] и heads [some 1, some 1]; heads — позиции первых
  токенов chunks, а не множество уникальных значений. Пример [0,1,2] с
  той же boundary даёт chunks [[0],[1,2]], heads [some 0, some 1]:
  первый head принуждён при boundary 0 = false, не-первой лежит на границе.
- Итого здесь одна публичная функция и семь публичных теорем:
  `boundaryHeads`, `length_boundaryHeads`, `isSome_of_mem_boundaryHeads`,
  `mem_of_mem_boundaryHeads`, `boundaryHeads_head?_cons`,
  `boundary_of_mem_boundaryHeads_tail`, `boundaryHeads_adjacent_first`,
  `theta_of_mem_adjacentHeads_tail`; `head_boundary_of_mem_tail` private.
- Evidence (cycle C215): установленный источник
  Hagi/Model/AdaptiveChunking.lean SHA-256
  f0faeaf7f6abeb57fce47491fcabda8cd49e50765f1b1bcedc3a5913e12edbf4
  (27244 bytes / 582 LF / 0 CR, +128 строк против C214, дифф чисто
  аддитивный); plan GO
  c919c621ff86523ba1e7607cc725713b9292b8c59e0dfa602a32c529a31dbcc6;
  source-statement GO
  b7eeb600ac18edd9e5d61861b7c2ef3d6ce98ff3aff82853f6f654c3f0835f8e;
  root-build log
  e1453aaef85dcbbb2ff29eb0e753f51eceeb731745ede75eafb19cb96f141e53;
  rootapi log
  c09bab4958680997359dabb04607ea52bb37f101ad2ce1d30f288dd4d3fb010d;
  triviallint log
  11ef18a234f4357f375fc0d4188c803f819811ad44816ded0790cc79b4af92dc.
  Census (fresh, .tmp/C215/validation/census-report.md, TSV SHA
  bcd363f63a758a5d79843363a9a65183a0440134968bc60f9dc3408a20fdb711,
  2928937 bytes / 14104 LF / 0 CR): OWNER 12270 → 12281 (модуль
  AdaptiveChunking 51 → 62, +11: 8 публичных, 1 private, 2
  compiler-generated), IR 1261 → 1264 (+3 codegen aux), CONSUMER 38 без
  изменений и byte-identical, fingerprint 12672784764919925193 →
  4917100471297953757; NamePool delta 11/0 (ADDED=11, REMOVED=0).

Это структурные свойства детерминированного фактического маршрута над
supplied предикатом, а не learned/differentiable/causal/online router и не
routing-quality утверждение. Forced first head — следствие `List.splitBy`,
а не H-Net gate; head selection H-Net отдельно отбрасывает non-head
представления. Не доказаны полная head-mask equivalence, Nodup heads,
learned sparsity, encoder, Q/K projection, cosine, zero-norm/tie, causal
stability supplied representations, stateful packed mask, BF16/Float,
runtime, минимальная память, training/held-out качество или глобальная
оптимальность HAGI.

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
- `stream_bounded`: `streamCache T n_s w ≤ n_s + w` для любого `T`;
  при `n_s + w < T` полный кэш строго больше, а экономия при увеличении
  `T` на единицу возрастает ровно на единицу (`stream_saving_step`).
- Для `0 ≤ m` и `d₁ ≤ d₂` ALiBi удовлетворяет
  `alibiBias m d₂ ≤ alibiBias m d₁`; при `0 < m`, `d₁ < d₂` затухание
  экспоненциального ядра строгое. `rope_shift_invariant` доказывает
  `ropeInner u v (m+d) (n+d) θ = ropeInner u v m n θ`, а
  `rope_normSq_preserved` — сохранение `Complex.normSq` вращением.

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
- Для произвольного `D` `batchDirectionSafeEta_pos_iff` эквивалентно
  непустому батчу и `∀ b, dirAction (X b) θ (y b) D < 0`.
  `ceOneHot_batchDirectionNextParameters_le` доказывает невозрастание CE
  для каждого примера, а при непустом батче и этих строгих отрицательных
  действиях — строгое убывание.
- При `0 < ∑ b, |featureNormSum (X b)|`
  `pmfMean_featureNormSum_optimalPropensity` доказывает покоординатную
  несмещённость взвешенного градиента остатка для
  `meanResidualTranspose`; `selectedMeanGradientMSE_featureNormSum_le`
  ограничивает MSE величиной
  `B⁻¹^2 * ((∑ b, |featureNormSum (X b)|)^2 -
  ‖∑ b, batchResidualGradient (X b) θ (y b)‖^2)`.

- C223 (batch range-step mirror of C216) добавляет в batch engine
  острую константу диапазона: `dirLogitRange` = `sup d − inf d`
  directional logit displacement (`sup' d + sup' (−d)`, общий witness
  `Finset.univ_nonempty`); `dirLogitRange_nonneg`, `dirLogit_sub_le`,
  `dir_logitDisplacement_logitRange` (η-масштабированная разностная
  оценка в `lse_shift_upper`) и `dirLogitRange_le_dirRange`
  (`R' ≤ R = dirRange`). Per-example мажоранта
  `ceOneHot_alongNext_le_logitRange`:
  `CE(θ+ηD) ≤ CE(θ) + η·dirAction + (ηR')²/8`; batch-агрегация
  `batchLogitRangeSquare` (среднее квадратов острых диапазонов общего
  `batchMeanDirection`) с `batchLogitRangeSquare_nonneg`,
  `batch_pos_of_logitRangeSquare_pos` и
  `batchAlignment_pos_of_logitRangeSquare_pos` (зеркало
  `batchAlignment_pos_of_rangeSquare_pos`).
- Averaged majorizer `batchLogitMajorizer` = `L − ηA + η²R'²/8`,
  certified step `batchLogitSafeStep` = `4A/R'²` при `0 < R'²`
  (иначе 0), общий update `batchLogitNextParameters`.
  `batchLoss_alongNext_le_batchLogitMajorizer` усредняет per-example
  оценки, `batchLogitMajorizer_logitSafeStep_eq` даёт точное значение
  мажоранты на шаге, MAIN `batchLoss_logitSafeStep_le_residual`:
  `batchLoss(batchLogitNextParameters) ≤ batchLoss − 2A²/R'²`;
  `batchLoss_logitSafeStep_lt` — строгий спуск. Сосуществование
  аддитивное: `batchLogitRangeSquare_le_batchRangeSquare` и
  `batchLogitSafeStep_ge_batchSafeStep` (новый шаг ≥ старого
  `batchSafeStep` при `0 < R'²`); вырожденный случай честен: `R'² = 0`
  даёт нулевой шаг (`dirLogitRange_eq_zero_of_forall_eq_zero`),
  фиктивного witness нет.
- Numeric controls (V=2, RootApi, независимая проверка
  `.tmp/C223/production/RootApi.lean`): `dirRange = 4` против
  `dirLogitRange = 2` (строгое `2 < 4`), certified step и residual
  выигрывают до 4×; neg1/neg2 — отрицательные пробы.
- Census (C223, .tmp/C223/validation/root-census.tsv SHA-256
  492e9386457b1915e460de938ce353b5d52683b3d4327775901211486d255081,
  2850509 bytes / 13664 LF / 0 CR): OWNER 11849 → 11878 (+29 =
  22 source-level + 7 компиляторных `.eq_1`/`.congr_simp`, ровно
  NamePool ADDED по множествам), IR 1247 без изменений, CONSUMER 38
  без изменений, модуль Hagi.Model.BatchCEDescent 249 → 278,
  fingerprint 14718226048161838198 → 14249654862734778222; retained
  rows byte-identical. NamePool delta: ADDED 32 (22 OWNER), REMOVED 16
  — все удалённые имена предшествуют C223 (автогенерируемые
  вспомогательные и приватизация C221), в BatchCEDescent удалений нет
  (.tmp/C223/validation/namepool-delta.txt).
- Evidence (cycle C223): установленный источник
  Hagi/Model/BatchCEDescent.lean SHA-256
  f78dbd7c71c64c3d0f012eee5e69c49da9d7740cfe64098ddb4ecd3265508686
  (135605 bytes, CRLF 1:1, 0 `\r\r`, canonical LF blob
  87bce31dad70397d7d096352a04bbdf3b244e65a; дифф против родителя
  чисто аддитивный +342/−0, блок перед финальным end-маркером, без новых
  imports); source GO
  45ac5af84c59946d124610a337f6a0a1b133bfd4aec9aaeb4575769bb66255ac;
  plan GO
  681277405c4e0218cfe96e8a7cabda3b474a52b6b0fa71efcbcaa6d0723cff9f;
  fresh lake build rc=0
  (.tmp/C223/production/root-build.log); RootApi rc=0 (22 exact-type
  + axioms clean [propext, Classical.choice, Quot.sound] + V=2
  controls + 2 negatives; rootapi.log
  3cbca894553bf6361d52fcaa66d81c7901e533c034516c506b8001a95dd8d853);
  TrivialLint new:0 PASS
  55886cbdc75579f4e02f801675b7d22464e29492d84225f29c93bc544af4969a;
  census-report
  56b54c333b80e5a98b6bc54d5b2c071ffd51babe739f13d222dc45d8742119f6;
  полный CI rc=0 (см. .tmp/C223/precommit/scope-review.md и
  .tmp/C223/precommit/ci.log); DocLint/StatusLint PASS.

Заявление — только certified descent одношаговой верхней оценки
arithmetic-mean batch loss и размера certified step; не утверждаются
wall-clock, сходимость итерации, CE→0, generalization, samplewise
гарантии или применимость вне log-linear one-hot CE.

## Hagi/Model/BlockNorm.lean

- Для `Blocks m = Fin 3 → Fin m → ℝ` `global_eq_mean_blocks` доказывает
  `(globalRms x)^2 = (∑ b : Fin 3, (blockRms (x b))^2) / 3`.
- `equal_blocks_global`: если `blockRms (x b₁) = blockRms (x b₂)` для
  всех блоков `b₁ b₂ : Fin 3`, то `globalNorm x = blockNorm x`.

## Hagi/Model/CEConfidenceScale.lean

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
- На одноблочном носителе `EuclideanSpace ℝ (Fin 5)`
  `ceQuantWitness_decoded_packedShortcutScales_strict_descent` даёт
  существование декодированного вектора из реального упакованного
  представления со строгим снижением CE относительно нулевых параметров.

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

- C216 добавляет range-based сертификат в CE engine:
  `ceStepLogitRange` = `sup d − inf d` directional logit displacement
  (`sup' d + sup' (−d)` с общим witness `Finset.univ_nonempty`);
  `ceStepLogitRange_nonneg` даёт неотрицательность,
  `ceDirectionLogit_sub_le` и `ce_logitDisplacement_range` — поточечную
  разностную оценку смещения, `ceStepLogitRange_le_ceStepRange`
  доказывает `R' ≤ R = ceStepRange = 2Σ|d|`.
- `ceRangeMajorizer` (CE − ηA + (ηR')²/8, та же острота `r²/8` из
  `lse_shift_upper`, но диапазон вместо суммы по словарю) и
  `ceRangeSafeStep = 4A/R'²` дают certified step с
  `ceRangeMajorizer_safeStep_eq` (точное значение мажоранты на шаге) и
  главным `ceOneHot_rangeSafeStep_le_residual`:
  `CE(θ') ≤ CE(θ) − 2A²/R'²`; `ceOneHot_rangeSafeStep_lt` даёт строгий
  спуск при `0 < R'` (строгость из
  `ceAlignment_pos_of_logitRange_pos`: `R' > 0 ⟹ A > 0`).
- Сосуществование аддитивное: `ceRangeSafeStep_ge_safeStepSize`
  (при `0 < R'` новый шаг ≥ старого) и `ceRange_residual_ge` (новый
  certified residual ≥ старого); потенциальный выигрыш шага до `V²`.
  Старый сертификат (`ceMajorizer`, `ceOneHot_next_le`, `safeStepSize`)
  не изменён. Вырожденный случай честен: `R' = 0` влечёт `A = 0` и
  нулевой старый шаг (Lean-теорема рецензента в
  `.tmp/C216/review-negative2.lean`), условие `0 < R'`
  эквивалентно `0 < R`.
- Numeric controls (identity 2-class): `identityTwoClass_logitRange_test`
  R 2 → R' 1, `identityTwoClass_rangeSafeStep_test` шаг 1/2 → 2,
  `identityTwoClass_step_comparison_test` 1/2 < 2 (4×),
  `identityTwoClass_residual_comparison_test` residual 1/8 → 1/2 (4×).
  Закрывает пункт P0c аудита
  `.omc/analysis/external-architecture-audit-2026-11-12.md`.
- Итого здесь три публичные функции и восемнадцать публичных теорем
  (последние четыре — тесты; всего 21 имя, плюс 2 private `c216_*`): `ceStepLogitRange`,
  `ceStepLogitRange_nonneg`, `ceDirectionLogit_sub_le`,
  `ce_logitDisplacement_range`, `ceStepLogitRange_le_ceStepRange`,
  `ceStepLogitRange_eq_zero_of_eq_zero`,
  `ceAlignment_pos_of_logitRange_pos`, `ceRangeMajorizer`,
  `ceRangeSafeStep`, `ceRangeSafeStep_nonneg`,
  `ceRangeSafeStep_pos_of_logitRange_pos`,
  `ceRangeMajorizer_safeStep_eq`, `ceOneHot_next_le_rangeMajorizer`,
  `ceOneHot_rangeSafeStep_le_residual`,
  `ceOneHot_rangeSafeStep_lt`, `ceRangeSafeStep_ge_safeStepSize`,
  `ceRange_residual_ge`, `identityTwoClass_logitRange_test`,
  `identityTwoClass_rangeSafeStep_test`,
  `identityTwoClass_step_comparison_test`,
  `identityTwoClass_residual_comparison_test`.
- Evidence (cycle C216): установленный источник
  Hagi/Model/CEDescent.lean SHA-256
  5a05958db6cade2dc093479cc48fdcfce70bd756f35e5ed617e347755fec70f0
  (748 строк, +311 против C215, дифф чисто аддитивный); source GO
  7cfdb02d6c0c6aa1f27ed8ac7cf27f25eeae3fe3437ca00a305cdc681b02d2f1;
  plan GO
  06f238bff9cd722941610965833d040eb87bf698dc6b406f303e343defcda651;
  research report
  c85b09ba406a75202dcb3074617b9b4fe494c6e28103919a773954a2804d6f54;
  rootapi log
  d382ace68cffebf5de9f94bb7c2ab396c1f7738f573322462865838034afea36.
  Census (fresh, .tmp/C216/validation/census-report.md, TSV SHA
  1f2f63279977e1aa634fcbbdaf36363313ad79e6b2eaf81d06fb7e6390dc5e06,
  2933930 bytes / 14131 LF / 0 CR): OWNER 12281 → 12308 (модуль
  Hagi.Model.CEDescent 328 → 355, +27 = ровно namepool ADDED, включая
  2 private mangled c216_*), IR 1264 → 1264 (+0), CONSUMER 38 без
  изменений, fingerprint 4917100471297953757 → 11502919156674973306;
  retained rows byte-identical.

Заявление — только certified descent одношаговой верхней оценки CE и
размера certified step; не утверждаются wall-clock, сходимость
итерации, CE→0, generalization или применимость вне log-linear
one-hot CE.

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
- `ceQuantWitness_decoded_packedBlock_strict_descent` поставляет явный
  декодированный вектор на `Fin 5` со строгим спуском для одноблочного
  примера.

## Hagi/Model/CEHeldout.lean

- `normalizedCE_mem_unit`: для непустого конечного `V` нормированный
  декодированный CE лежит в `[0,1]`; нормировка выполнена положительным
  `ceBound X`, а не произвольной верхней оценкой.
- `codebook_raw_selected_population_mean_gap_lower_confidence`: для
  фиксированного декодера, `IsProbSys p`, `0 < n`, `0 < eps` и любых
  зависящих от выборки `baseline candidate` в фиксированной кодовой книге
  вероятность события `эмпирическая разность - 2*eps ≤ генеральная разность` не менее
  `1 - 2*61965^G*exp(-2*n*(eps/ceBound X)^2)`.
- `ceOneHot_mean_ceLogits_le` доказывает невозрастание CE в средней точке
  двух параметров относительно среднего CE концов;
  `ceOneHot_decodeJoint_encodeJoint_mean_le_ceQuantPenalty` добавляет к
  этой оценке ровно объявленный штраф квантования.

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
- Полный поиск включает `255^G` назначений; упакованный связанный пример
  на `Fin 5` декодируется в параметры со строгим спуском CE
  (`ceQuantWitness_decoded_packedCoupledScales_strict_descent`).

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

## Hagi/Model/CEMarkovMaximalConfidence.lean

- `raw_bank_freedman_maximal_confidence`: для исходной (не нормированной)
  CE, вычисленной по фиксированному decodeJoint на парах «банк — метка», пусть
  `g = F − μ`, где `μ` — conditional PMF mean следующей CE, а `v` — точный
  conditional second moment `g`. При `0 < r`, `0 ≤ V`, нижняя граница
  `1 - 2*m*(T+1)*exp(-r^2/(4*(V + ceBound X*r)))` относится к индикатору
  одновременного события: для каждого `i : Fin m` и каждого префикса `j ≤ T`,
  если `historyCounter v T j ≤ V`, то `|historyAdditive g T j| < r`.
  Банк объединяется через Freedman и union bound; времена не ограничены
  одним конечным `T T` внутри события, хотя сам горизонт конечен.
- Условный диапазон выводится из `0 ≤ F,μ ≤ ceBound X`, без подмены raw CE
  диапазоном `[0,1]`. Пустой банк `m=0` остаётся допустимым vacuous случаем.
  Доказано вероятностное утверждение для данной конечной Markov-истории;
  не следуют individual CE improvement, causal stopping/selection,
  held-out качество, произвольный stopping time, strict `StepCert`,
  оптимальная константа или снижение вычислительной стоимости.


## Hagi/Model/CEMarkovSelectedPrefix.lean

- `raw_bank_selected_prefix_conditional_ce_gap_pos_of_good`: для банка raw
  CE, kernel `K` и одновременного события для всех `j ≤ T`, явно задаются
  baseline `b`, full-history selector `σ` и bounded prefix `τ`, причём
  `0 ≤ τ ω ≤ T`. Если conditional бюджеты `v` у `b` и `σ ω` не превосходят
  `V` на этом префиксе, а наблюдаемая разность raw CE больше `2*r`, то
  conditional mean разность «baseline минус выбранный» на `τ ω` строго
  положительна. Сохранён raw baseline/selected gap; stationary kernel не
  предполагается. Это pointwise conditional результат, не безусловный
  expected loss, causal stopping-time policy, optimal bank selection,
  training progress или `StepCert`; hobs не выводится из Freedman-события.
## Hagi/Model/CEPackedStep.lean

- `packedStep_payload` фиксирует 16-битный объект со значением `8311`;
  `decodeStep_packedStep = some (ternaryCEParameters (1/4) rawSuccessor)`.
- `decoded_packedStep_strict_descent`: существует декодированный
  `w : EuclideanSpace ℝ (Fin 5)` из этого представления, для которого
  фактический CE строго меньше CE нулевых параметров на заданном примере.

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
- При непустом конечном `V`, `0 < ceStepRange X θ t` и существовании
  связанного назначения со штрафом меньше остатка безопасного шага
  `shortcutScales_unpad_strict_descent_of_exists`
  даёт строгий спуск CE уже на исходной `d`-мерной модели.

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

## Hagi/Model/CEScaleSelection.lean

- `scaleEvaluationCount_eq = 255`; `selectedScale_spec` выбирает код,
  минимизирующий `scalePenalty` среди всех `DyadicScaleCode`.
- `selectedScale_strict_descent_of_exists`: на непустом конечном `V`, при
  `0 < ceStepRange` и
  существовании кода со штрафом меньше остатка безопасного шага выбранный
  код сохраняет строгий спуск фактического CE.
- `decodeStep_packedSelected` возвращает ровно выбранные тритарные параметры,
  а `decoded_packedSelected_strict_descent` поставляет соответствующий
  декодированный вектор со строгим спуском на одноблочном примере.

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

## Hagi/Model/GatedCEDescent.lean

- Для непустого конечного `V` производная CE вдоль
  `gatedDirection X θ t` в нуле равна `-gatedAlignment X θ t`
  (`hasDerivAt_gatedLineObjective`).
- При `0 < gatedAlignment X θ t`
  `exists_gated_ceOneHot_descent` даёт существование `η > 0` со строгим
  локальным снижением фактического CE управляемой модели; явный размер
  шага в этой теореме не вычисляется.

## Hagi/Model/GatedCEGradient.lean

- `hasFDerivAt_gatedForward` задаёт точный якобиан обучаемого
  `gatedForward`, а `fderiv_ceOneHot_gatedForward` выражает производную CE
  как сумму произведений компонент softmax-остатка на
  `gatedAction X θ D v`.
- `differentiable_gatedForward` доказывает глобальную дифференцируемость
  по управляющим параметрам; `abs_tanh_sub_le` доказывает глобальную
  1-липшицевость `Real.tanh`.

## Hagi/Model/GatedCEPositiveCurvature.lean

- Из `0 < gatedAlignment X θ t`
  `gatedResidualSecondOrderMass_pos_of_alignment_pos` получает строго
  положительную вторую моментную массу остатка, а
  `gatedCurvature_pos_of_alignment_pos` — положительную полную кривизну
  квадратичного мажоризатора.
- `gatedSafeStepSize_eq_div_of_alignment_pos`: в этой ветви
  `gatedSafeStepSize = gatedAlignment / (2*gatedCurvature)`.

## Hagi/Model/GatedCESafeStep.lean

- `gatedDisplacement_eq_linear_add_remainder` точно разделяет линейное
  якобианово смещение и остаток; `abs_gatedLogitRemainder_le` ограничивает
  остаток величиной `2*η^2*gatedUnitSecondOrderMass X D v`.
- `gatedMajorizer_safeStep_eq`: при явном безопасном шаге мажоранта равна
  старому CE минус `gatedSafeDrop`; для непустого `V` и `0 ≤ η`
  фактический CE не превышает `gatedMajorizer`, а
  `gated_ceOneHot_safeStep_le_drop` переносит эту оценку на CE.
- При `0 < gatedAlignment` безопасный шаг строго положителен и
  `gated_ceOneHot_safeStep_lt` даёт строгий спуск. При нулевой кривизне
  шаг равен `1`, а уменьшение мажоранты равно согласованности; при
  положительной кривизне шаг минимизирует названный квадратичный
  мажоризатор.

## Hagi/Model/GatedCEUniformCurvature.lean

- `gatedResidualSecondOrderMass_direction_le` ограничивает вторую
  моментную массу остатка величиной `gatedSecondOrderFeatureMass X`;
  `gatedCurvature_le_uniformBound` ограничивает кривизну функцией только от
  признаковой матрицы.
- `gatedCurvatureUniformBound_pos`: эта зависящая только от признаков
  верхняя граница строго положительна, включая нулевые признаки и нулевую
  размерность.

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
- `hnet_opt_ratio`: для любого вещественного `r > 0`
  стоимость в `hnetOptRatio` не превосходит стоимости в `r`.
- `hnet_opt_ratio_unique`: при `a b T r > 0` равенство стоимостей в `r`
  и `hnetOptRatio` влечёт `r = hnetOptRatio a b T`.

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
- VicReg: `vh_nonneg` доказывает неотрицательность, `vh_zero` — нуль при
  `gamma^2 ≤ popVar z`; `vh_anti` при `popVar z₁ < popVar z₂` и
  `0 < vh gamma z₁` доказывает строгое убывание.
- TripletLoss: `tl_nonneg` доказывает неотрицательность, `tl_zero`
  отделяет нулевой случай `dap+m ≤ dan` (`0 ≤ m`) от строго
  положительного `dan < dap+m` в `tl_pos`; `tl_mono_pos` и `tl_mono_neg`
  доказывают монотонность по расстояниям.

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
- CFG `cfg_convex` при `0 ≤ w ≤ 1` и `eu ≤ ec` даёт двусторонние границы
  `eu ≤ eu + w*(ec-eu)` и `eu + w*(ec-eu) ≤ ec`;
  `cfg_boost` при `1 < w` даёт превышение над условным предсказанием
  `(w-1)*(ec-eu)`.
- DPO: `boltzmann_from_reward` при `β ≠ 0` и положительных `pi pref`
  даёт `pi i = pref i*exp(dpoReward β pi pref i/β)`; `bt_pref_iff`
  доказывает `1/2 < btPref r1 r2 ↔ r1 > r2`.

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
- `machine_stop_horizon`: если `0 ≤ q < 1`, `0 ≤ F eps`,
  `E(t+1) ≤ q*E t+F`, `E 0 = E0` и `q^t*E0 ≤ eps`, то
  `E t ≤ eps + F/(1-q)`.
- На `EuclideanSpace ℝ (Fin n)` `machine_pl_instance` даёт точное PL-
  неравенство с `μ=1`; `batch_anneal_floor` при `0 ≤ sigma`, `0 < B0`,
  `1 < c`, `0 < n`, `0 < Delta` и соответствующей границе сетки доказывает
  `n*Delta^2/8 ≤ sigma^2/(B0*c^t)`.

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
- `deadlock_witness` (негативный pinned-challenge): 3-ключевой
  точнорациональный софтмакс (внимание полезного ключа ровно
  ε = 1/10, `dwScores`/`dw_att0`/`dw_att1`) — вклад полезного ключа
  в градиент запроса имеет норму ≤ ε·M: полезный-но-игнорируемый
  ключ обучает запрос медленно.

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
- `two_level_stop`: при `0 ≤ q < 1`, `0 < δ`, `0 ≤ eps`, `1 ≤ K`,
  `E(s+1) ≤ q*E s + n*(δ/2^(K-1))^2/8`, `E 0 = E0` и `q^t*E0 ≤ eps`
  `E t ≤ eps + n*δ^2/(8*(1-q)*(2^(K-1))^2)`.
- `two_level_optimal_depth`: если дополнительно `0 ≤ floor_budget` и
  `n*δ^2/8 ≤ floor_budget*(1-q)*(2^(K-1))^2`, тот же шаг даёт
  `E t ≤ eps + floor_budget`.

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
- `budget_capability_ceiling`: при `1 ≤ 1+α`, `0 < c`,
  стоимости каждого цикла `≥ c`, `0 ≤ (tr.state t).budget`, `0 ≤ C0` и
  `C(t+1)≤(1+α)C t`
  `C T ≤ (1+α)^(B0/c)*C0`; `growth_corridor` сопоставляет это с нижней
  конусной оценкой.
- `plan_reachability`: при `0 ≤ γ`, `0 ≤ 1+γ*k`, конусных `D` и
  измеренных приростах, бюджетных посылках и `Cstar ≤ (1+γ*k)^T*C0`
  доказывает `Cstar ≤ C T` и `T*c ≤ B0`.
  `three_cycle_varying_gain_nonvacuous` даёт конкретные разные
  положительные приросты `1,2,4`, энергии `30,27,23,17` и способности
  `1,2,4,8` с положительными `η`.

## Hagi/Model/TanhCEStep.lean

- Для модели `x ↦ ![Real.tanh x, 0]` на `Fin 2`
  `ceOneHot_tanh_step_le` доказывает
  `CE(![tanh(2/33),0]) ≤ CE(![0,0]) - 1/66`; локальная оценка остатка
  имеет радиус `1` и коэффициент `2`.
- `ceOneHot_tanh_step_lt` делает спуск строгим; равенство фактического
  спада величине `1/66` не утверждается.

## Hagi/Model/TanhTaylor.lean

- `norm_deriv_sechSq_le`: `‖deriv sechSq x‖ ≤ 2`;
  `abs_sechSq_sub_le` доказывает глобальную 2-липшицевость `sechSq`.
- `abs_tanh_taylor_sub_le`:
  `|tanh y-tanh x-sechSq x*(y-x)| ≤ 2*(y-x)^2`
  для произвольных вещественных `x y`.

## Hagi/Numerics/SoftmaxFix.lean

- `ce_grad_sum_zero`: для нормированной `p`
  `Σ(softDef z-p)=0`; `distill_grad_self_zero` обнуляет остаток при
  `zS=zT`.
- Если `univ.erase t` непуст, `margin_rest_sum` даёт
  `Σ_{j≠t}exp(z j-z t)=exp(-logitMargin z t)`, а `ce_loss_margin`
  переписывает CE как `log(1+exp(-logitMargin z t))`.
- `adamw_equilibrium_magnitude`: при `0 < ε lam |θ|`,
  `lam*|θ| < 1` и `g/(|g|+ε)+lam*θ=0`
  `|g| = lam*|θ|*ε/(1-lam*|θ|)`.
- `margin_equilibrium_value`: если `0 < c` и
  `c*exp(-m) = lam*|θ|*ε/(1-lam*|θ|)`, то
  `m = log(c*(1-lam*|θ|)/(lam*|θ|*ε))`.
- При строго положительной нормированной `p` `expTilt p c` положителен и
  нормирован; `expTilt_centering` сохраняет его при вычитании `p`-среднего,
  `expm1_form_diff` выражает `expTilt p c-p`, а
  `expTilt_uniform_is_softDef` отождествляет наклон равномерной ссылки с
  `softDef`.

## Hagi/Omni/ConditionalInformation.lean

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

## Hagi/Omni/CrossModalGap.lean

- Для непустых конечных `X Y` и строго положительной нормированной
  `p : X×Y→ℝ`
  `crossModalGap_eq_kl` равна `klDef p (margX p * margY p)`;
  `crossModalGap_nonneg` доказывает неотрицательность.
- `crossModalGap_zero_iff_indep`: разрыв равен нулю тогда и только тогда,
  когда `p(x,y)=margX p x*margY p y` для всех `x y`.

## Hagi/Omni/OmniInvariant.lean

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

## Hagi/Omni/OmniState.lean

- `driftTube_closed`: при `ρ ≠ 1`
  `driftTube ρ e d0 t = ρ^t*d0 + e*(1-ρ^t)/(1-ρ)`;
  `drift_limit` при `0 ≤ ρ < 1`, `0 ≤ e d0` ограничивает его
  `d0 + e/(1-ρ)`, а `drift_zero` убирает аддитивный член ошибки при `e=0`.
- `admissionChain`: если `0 < deltaNet` и
  `C s+deltaNet ≤ C(s+1)` для всех `s<t`, то `C 0+t*deltaNet ≤ C t`.
- `omniLeafCost` и `omniParamCost` дают `r*d` и `k*(r*d)` элементов;
  `sharedStateCostBound` при `0 < d`, `k*r < d` доказывает
  `∑ i<k,r*d < d*d`.
- `sharedStateEnergy` при ортонормированных `U V` и `UᵀV=0` равна сумме
  квадратов норм; `sharedStatePerturbed` содержит дополнительный член
  `2*√frobSq(VᵀW)*‖r‖*‖s‖`.

## Hagi/Optimization/AdaGrad.lean

- `acc_mono`: `adagradAcc g t ≤ adagradAcc g (t+1)`.
- `adagrad_step_anti`: при `0 ≤ eta` и `0 < adagradAcc g t`
  `eta/√(acc+g t^2) ≤ eta/√acc`.

## Hagi/Optimization/AdamBias.lean

- `adamM_recur` доказывает `adamM β g 0=0` и
  `adamM β g (t+1)=β*adamM β g t+(1-β)*g`;
  `adam_bias_bound` раскрывает `adamM β g t = g-β^t*g`.
- `adam_unbiased_const`: при `0 ≤ β < 1`, `1 ≤ t`
  `adamM β g t/(1-β^t) = g`.

## Hagi/Optimization/AdamW.lean

- `adamw_shrink`: при `0 < lam ≤ 1`, `w ≠ 0` и нулевом градиенте
  `|adamwStep lam eta w 0| < |w|`.
- `l2_decay_diluted`: при `0 < lam`, `0 ≤ vhat` и
  `1 ≤ lam*(√vhat+1)` эффективное затухание
  `lam/(√vhat+1) ≤ lam^2`.

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

## Hagi/Optimization/CautiousOptimizer.lean

- `cautiousMask_abs_le`: `|cautiousMask u g| ≤ |u|`;
  `cautiousAligned`: `0 ≤ cautiousMask u g*g`.
- При `0 < u*g` `cautiousId` возвращает `u`, а при `u*g ≤ 0`
  `cautiousZero` возвращает `0`.

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

## Hagi/Optimization/GradAccum.lean

- `accum_equiv`: для разбиения `c : Fin N → Fin k`
  `∑ i, microGrad c f i = fullGrad f`; это точное равенство сумм по
  слоям разбиения, а не приближение градиентов.

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
- Для `start : targetComponent G target` вложенные поддерживаемые истории
  сохраняют `PrefixOKAt`; классификатор внешнего графа возвращает `.Hold`
  до первого попадания и `.Arrived target` начиная с него.

## Hagi/Optimization/HBRate.lean

- `hb_discriminant_interval`: при `0 < β < 1` и
  `(1-√β)^2 ≤ η*μ ≤ (1+√β)^2` дискриминант неположителен;
  `hb_root_modulus` для корня `λ²-tλ+β=0` с `0 < β` и
  дискриминантом `≤0` даёт `normSq λ = β`.
- `hb_cfg_rate`: при `0 < ρ < 1` и корне характеристического уравнения
  конфигурации `β=ρ²`, `η=(1-ρ)²` имеет место `normSq λ = ρ²`.
- `hb_repeated_root_closed_form` даёт `e n=(C+D*n)*ρ^n`;
  `hb_critical_trajectory_bound` для `0 < ρ` оценивает критическую
  скалярную моду через `(|e0|+|e1/ρ-e0|*n)*ρ^n`, сохраняя жорданов фактор.
- `hb_two_root_closed_form` разлагает траекторию в
  `A*λ1^n+B*λ2^n`; при `‖λ1‖=‖λ2‖=rho`
  `hb_two_root_common_norm_bound` даёт `‖e n‖≤(‖A‖+‖B‖)*rho^n`.
- Для исходной пары Heavy Ball `hb_pair_second_order` получает свободный
  коэффициент `β+η*(1-β)`. При корнях с общей границей `rho i` и
  `0 < gap i ≤ ‖λ1 i-λ2 i‖` `hb_pair_l2_initial_gap_bound` ограничивает
  `‖e n‖` корнем из суммы квадратов
  `(2*(‖e1 i‖+rho i*‖e0 i‖)/gap i * rho i^n)^2`.

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

## Hagi/Optimization/InfoPreservation.lean

- C220 (удаление zero-consumer дубликатов): regret-обёртка
  этого модуля удалена; каноническая regret-оценка — `mirror_regret`
  (Hagi/Optimization/MirrorDescent.lean).

## Hagi/Optimization/LLRD.lean

- `llrd_strict_mono`: при `0 < eta`, `0 < gamma < 1`,
  `l1 < l2 ≤ L` `layerLR eta gamma L l1 < layerLR eta gamma L l2`.
- `llrd_nonneg`: при `0 ≤ eta gamma` все `layerLR` неотрицательны.

## Hagi/Optimization/LRSchedule.lean

- `late_phase_bound`: при `plRec`, `0 ≤ mu etaMax`, `0 ≤ eta t ≤ etaMax`,
  `0 ≤ e t`, `mu*eta t ≤ 1`
  `e(m+k) ≤ e m+k*sig^2*etaMax^2` (устойчивая фаза и фаза затухания).
- `wsd_full_bound`: при `0 < mu etaMax`, `mu*etaMax ≤ 1`,
  `0 ≤ eta t ≤ etaMax`, `0 ≤ e t` и `eta t=etaMax` для `t<m`
  ограничивает `e(m+k)` величиной
  `ρ^m*e0 + sig^2*etaMax^2*(1-ρ^m)/(1-ρ) + k*sig^2*etaMax^2`,
  где `ρ=1-mu*etaMax`.
- `cosLR_start = etaMax`, `cosLR_end = 0` при `T ≠ 0`;
  `cosLR_anti` при `0 < T`, `0 ≤ etaMax`, `0 ≤ s ≤ t ≤ T`
  доказывает невозрастание.

## Hagi/Optimization/Lion.lean

- `sign_sq_le_one`: `(sgn x)^2 ≤ 1`; `lion_step_norm_bound` даёт точную
  суммарную оценку `∑ i, (signStep eta m i)^2 ≤ eta^2*d` на `Fin d`.

## Hagi/Optimization/Lookahead.lean

- `lookahead_mem`: при `0 ≤ α ≤ 1` новый якорь лежит между `min w x` и
  `max w x`; `lookahead_gap` при `0 ≤ α` даёт
  `|slowStep w x α-w| = α*|x-w|`.
- `lookahead_range`: если `0 ≤ α ≤ 1` и `w x` находятся в `[lo,hi]`,
  новый якорь также находится в `[lo,hi]`.

## Hagi/Optimization/MarkovPercolation.lean

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
- `weightedNeighborKernel_support`: при ненулевой и нетоповой сумме весов
  на каждой строке и положительности веса каждого ребра маскированное
  взвешенное ядро поддерживается ровно графом; принадлежность точечному носителю
  эквивалентна `G.Adj a b ∧ w a b ≠ 0`.

## Hagi/Optimization/MirrorDescent.lean

- Для строго положительных нормированных `ρ₀ ρ` и `0 < T`
  `mirror_regret` ограничивает суммарное превышение потерь
  `mirrorIterate` над `ρ` величиной `T*KL(ρ‖ρ₀)`.
- При фиксированных `ℓ` с нижней границей `C`
  `mirrorIterate_energy_converges` доказывает, что энергия входит в любой
  `ε`-коридор над инфимумом траектории потерь; `mirrorIterate_partial_mono` даёт покадровое
  невозрастание потерь.
- `hedge_wealth_rate`: среднее
  `-T*log(∏stepNorm)/n` сходится к минимальному значению `ℓ`
  в смысле `∀ε>0, ∃N, ∀n≥N`.
- `mirror_step_variational_descent` доказывает
  `⟨mirrorStep,ℓ⟩ + T*KL(mirrorStep‖ρ₀) ≤ ⟨ρ₀,ℓ⟩`.

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
- `zero_inertia_optimal`: для `0 < θ < 1`, `0 < q < 1`, `0 ≤ δ` и
  `e(k+1)≤θ*q*e k+δ` получается
  `e k≤(θq)^k*e0+δ/(1-θq)`; это редукция к неточному сжатию.
- `anderson_momentum_reach`: при `0 < θ < 1`, `0 < q < 1`, `0 ≤ β δ`,
  `θ*q+β<1` и полной неточной инерционной рекурсии для каждого
  `0 < ε` существует горизонт с
  `e s≤δ/(1-θ*q-β)+ε` навсегда после него.

## Hagi/Optimization/MomentumHB.lean

- `hb_pair_recurrence` задаёт компонентное
  `e'=(1-eta)*e+v`; `hb_char_eq_1d` проверяет соответствующее
  характеристическое тождество второго порядка.
- `hb_stability`: при `0 ≤ beta < 1`, `0 < eta ≤ 1-beta`
  `|1+beta-eta| < 1+beta` и `beta < 1`.
- `hb_critical_discriminant` и `hb_root_sqrt_beta` подтверждают двойной
  корень `√beta` при критическом `η`; `hb_rate_critical` при
  `0 ≤ beta < 1` даёт `|√beta| < 1`.
- `hb_lyapunov_step_bound` ограничивает функцию Ляпунова после шага
  суммой `(2*(1-eta)^2+2*eta^2)*∑e^2 +
  (2+2*beta^2)*∑v^2`; сжатие этой формы не утверждается.

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

## Hagi/Optimization/PPOClip.lean

- `ppoClip r lb ub = max lb (min ub r)`; доказаны монотонность по `r` и `ppoClip_fixed`: при `lb ≤ r ≤ ub` отсечка равна `r`.
- `ppo_clip_term_abs_bound` при `0 ≤ e` даёт `|ppoClip r (1-e) (1+e) * A| ≤ (1+e) * |A|`.
- `ppo_surr_upper_bound` ограничивает `min (r*A) (ppoClip r (1-e) (1+e) * A)` сверху той же величиной `(1+e)*|A|`. Нижняя граница суррогатной цели и сходимость оптимизации здесь не утверждаются.

## Hagi/Optimization/PolyStep.lean

- Для непустого конечного индекса `polyWeights C eps` неотрицательны и суммируются в `1`. При `0 < eps` и `C u < C w` теорема `polyWeights_strict_mono` даёт `polyWeights C eps w < polyWeights C eps u`.
- `polyDelta` образует взвешенную сумму направлений, а `polyStepUpdate` прибавляет её с коэффициентом `ℓ` к `θ`.
- `polyDelta_basis_sum`: если `dirs v j = if v = j then 1 else 0`, то при непустом конечном `n` сумма координат `polyDelta dirs C eps` равна `1`; это не утверждение о невырожденности каждой координаты или о качестве обновления.

## Hagi/Optimization/RobbinsMonro.lean

- `robbins_monro_decay`: при `0 ≤ x 0`, `0 ≤ η k ≤ 1`, рекурсии `x (k+1) ≤ (1-η k)*x k` и `Tendsto (fun n => ∑ k ∈ range n, η k) atTop atTop` для любого `ε > 0` найдётся `T`, после которого `x s ≤ ε`.
- `robbins_monro_abs` переносит тот же вывод на `|y s|` при рекурсии `|y (k+1)| ≤ (1-η k)*|y k|`.
- `robbins_monro_bias`: из `x (k+1) ≤ (1-η k)*x k + D*η k` и расходимости суммы шагов следует существование хвоста с `x s ≤ D + ε`. Это верхняя граница хвоста, а не равенство предела `D`.

## Hagi/Optimization/SAM.lean

- `samW L rho w` — супремум значений `L (w+e)` на `ball rho`, где `norm2 e ≤ rho^2`. При `0 ≤ rho` и ограниченности сверху образа `sam_ge` даёт `L w ≤ samW L rho w`.
- `sam_mono`: при `0 ≤ r1 ≤ r2`, `0 ≤ r2` и ограниченности сверху образа на большем шаре `samW L r1 w ≤ samW L r2 w`.
- `sam_flat`: если `L (w+e) = L w` для всех `e ∈ ball rho`, `0 ≤ rho` и образ ограничен сверху, то `samW L rho w = L w`.

## Hagi/Optimization/Schelling.lean

- `localCompatibleDegree` считает соседей `w` с `k ≤ compatibility v w`, а `locallySatisfied` требует не менее `min k (G.degree v)` таких соседей. Нулевой порог и изолированная вершина удовлетворены автоматически.
- Доказаны `localCompatibleDegree_le_degree` и, при `G.degree v ≤ k`, эквивалентность `locallySatisfied_iff_forall_of_degree_le`: удовлетворённость означает выполнение порога совместимости для каждого соседа.
- `locallySatisfied_disconnected` строит на `Fin 4` граф из двух ребер: все вершины локально удовлетворены при `k = 1`, но вершины `0` и `2` недостижимы друг из друга и выполнено `¬ disconnectedGraph.Preconnected`. Динамика переселения не формализуется.

## Hagi/Optimization/SchellingPercolation.lean

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

## Hagi/Percolation/Site.lean

- На конечной решётке определены `openAt`, `openGraph`, `crossing` и равномерная по всем конфигурациям затравки вероятность `R`. `card_Ω` равен `M^(L*L)`, а `crossing_mono` и `R_monotone` доказывают монотонность по порогу на одном пространстве затравок.
- Для чётной затравки на решётке `2×2` доказаны `parity_not_crossing1` и `parity_crossing2`; `emergence_jump_witness` упаковывает этот пример, а `R_strict_jump` даёт строгое `R 2 rowTop rowBot 1 < R 2 rowTop rowBot 2`.
- Все результаты конечны; бесконечный перколяционный порог и асимптотический закон критической точности здесь не выводятся.

## Hagi/Planning/Imagination.lean

- C220 (удаление zero-consumer дубликатов): forward-thinking
  regret-утверждение удалено; родственная доказанная граница той же
  формы `A − L* ≤ log K/eta + eta*T/2` — `router_regret_bound`
  (Hagi/Autonomy/Hedge.lean).
- `imagination_compounding`: при пошаговой ошибке прогноза не более `ε` на `k < K` и `L`-липшицевости каждой `V k` на `k ≤ K` разность `∑ V k (oh k) - ∑ V k (o k)` не превышает `K*L*ε`. Доказана односторонняя, а не абсолютная, оценка.
- `adaptive_first_sufficient`: из `|Vhat π₁ - V π₁| ≤ ε` и `θ ≤ Vhat π₁` следует `θ - ε ≤ V π₁`. `branching_avoids_detectable_failure` использует одностороннюю ошибку `Vhat - V ≤ ε` и посылку `θ < Vhat π` для исполняемых планов; `branching_dominates_linear` затем отделяет заведомо плохой `π₁` от исполняемого `πb`.

## Hagi/Prelude/Info.lean

- Введены конечные `klDef`, `ceDef`, `entDef`, `tvDef` и `softDef`. При `p v ≠ 0` тождество `klDef_eq_ceDef_sub` выражает KL как `ceDef q p - ceDef q q`, а `ceDef_self` даёт `ceDef q q = entDef q`.
- `kl_nonneg_of_nonneg` требует неотрицательные `q`, положительные `p` и суммы обеих функций, равные `1`; `kl_nonneg` вариант с положительными `q`. Для неотрицательного распределения на непустом типе `sum_negMulLog_le_log_card` ограничивает энтропию через `log (Fintype.card V)`.
- На непустом конечном индексе `softDef_pos` и `softDef_sum_one` доказывают положительность и нормировку softmax.

## Hagi/Pretraining/DataPruning.lean

- `pruning_nfl`: если `p ∉ kept` и результат `g` зависит только от значений на kept, то для двух функций-таргетов, совпадающих везде кроме `p` и принимающих там значения `0` и `1`, сумма абсолютных ошибок в `p` не меньше `1`.
- `pruning_free_for_constant` показывает границу применимости: если `g` возвращает общую константу `c` для согласованных данных, аналогичная сумма ошибок равна `0`.
- `pruning_recovery_bound` — независимая липшицева оценка: при `x0 ≤ t ≤ x1` и `|x1-x0| ≤ δ` получается `|f t - f x0| ≤ L*δ`.

## Hagi/Pretraining/Dust.lean

- `hcDelta` вычисляет среднее `signR (u i) * signR (u j)` по булеву кубу как `if i = j then 1 else 0`. `esUnbiased` при `σ ≠ 0` доказывает точное равенство среднего симметричной разности `esEst` и `quadfGrad` для квадратичной модели.
- `varianceHalving` для центрированного векторного поля даёт точное уменьшение среднего квадрата суммы двух независимых выборок вдвое; `dustNoiseHalving` переносит это на ошибку `esEst - quadfGrad`.
- В этом файле доказан случай двух выборок, а не общий закон `1/K` и не общая K-ошибка выравнивания.

## Hagi/Pretraining/DustAlign.lean

- `hcVarK`: для центрированного скалярного поля и `K > 0` средний квадрат среднего по `K` независимым точкам куба равен одношаговому среднему квадрату, делённому на `K`. `dustVarK` доказывает такое же точное тождество для суммы квадратов координатной ошибки `esEst`, а `dustVarK_expQ` записывает его через `Probability.expQ`.
- `dustAlignmentK`: при `K > 0`, `0 < δ ≤ 1` и положительной норме `quadfGrad` масса `prodQ` траекторий с `(1-2δ)*Nrm(g)*Nrm(ĝ_K) ≤ g ⬝ᵥ ĝ_K` не меньше `1 - (V/K)/(δ*Nrm(g))^2`, где `V` — одношаговая сумма квадратов ошибки.
- Это конечная вероятностная оценка скалярного произведения и норм, а не утверждение о сходимости обучения.

## Hagi/Pretraining/DustMeasure.lean

- `rademacherLaw` получает вероятностную меру честного булева произведения; `rademacher_expect_sign` и `rademacher_projection_mean` дают нулевые средние знака и проекции шума.
- `rademacher_projection_independent` доказывает независимость проекций по координатам `j : Fin m` для фиксированных эксперта `i` и направления `d`, с отдельными результатами измеримости.
- Если каждое `u i` имеет единичную норму, `rademacherNoise_norm_le_one` даёт `‖rademacherNoise u i j ω‖ ≤ 1`. Независимость между экспертами или моментами времени не вводится.

## Hagi/Pretraining/Grokking.lean

- `drift_hasDeriv` проверяет производную `w0 * exp (-lam*t)`, а `drift_half_life` при `lam > 0` вычисляет значение в момент `(log 2)/lam` как `|w0|/2`. Также доказаны неувеличение модуля для `t ≥ 0` и оценка полной вариации через `|w0|`.
- `grokking_timescale_separation`: для любых `T_fast > 0` и `k > 0` существует `lam > 0`, для которого `(log 2)/lam > k*T_fast`.
- Это результаты о выбранной экспоненциальной траектории и её временном масштабе, а не доказательство двухфазной динамики или обобщения нейросети.

## Hagi/Pretraining/ProbeError.lean

- `fd_probe_error`: при `σ > 0` и модельной гладкости с константой `L` абсолютная ошибка прямой разности не превышает `(L/2)*σ*‖v‖^2`; `linear_probe_exact` даёт точность для аффинной функции.
- `centralQuadraticProbe_exact` восстанавливает квадратичный градиент точно, тогда как `forwardQuadraticProbe_error` для `x v : X` при `0 ≤ L` и `0 < σ` вычисляет ошибку прямой пробы как `(L/2)*σ*‖v‖^2`. Для кубической модели `centralCubicProbe_remainder` равен `(c/6)*σ^2*‖v‖^6`; `noisyCentralCubicProbe_optimal_bound` ограничивает ошибку через `probeCost` при ограниченных шумах.
- `residual_vec_bound` и `mlpResidual_bound` ограничивают норму отброшенного хвоста суммой `|φ j|*‖v j‖` по дополнению выбранного индекса.
- `safe_certificate_margin` переносит ошибку градиента в добавку `ε*‖d‖` к квадратичной оценке. `cut_safe_accept` при ошибке пробы `ε_probe`, ошибке механизма внимания `ε_att`, гладкости L_att и бюджете `dLmeas + (ε_probe + L_att*ε_att)*‖d‖ ≤ 0` заключает `dLexact ≤ 0`.

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

## Hagi/Pretraining/TrustRegion.lean

- `hadamardRows_sup_bound`: при `Q*Qᵀ = 1` каждая координата `Q *ᵥ δ` по модулю не превосходит `Real.sqrt (∑ j, δ j * δ j)`.
- `transpose_mul_self_of_mul_transpose` выводит `Qᵀ*Q = 1`, а `orthonormal_mulVec_isometry` доказывает равенство суммы квадратов `Q *ᵥ δ` и `δ`. Результаты относятся к квадратным вещественным матрицам с этой ортогональностью.

## Hagi/Probability/AdaptiveSuccess.lean

- `adaptive_success_count_floor`: на конечном независимом произведении, для `X i v ∈ [0,1]`, общего пола `SuccessFloor p X p0`, `n > 0` и `t > 0` вероятность события `n*p0 - t ≤ ∑ i, X i (ω i)` не меньше `1 - exp (-2*t^2/n)`.
- `adaptive_success_concentrated` при `0 < delta < 1` даёт вероятность не меньше `1-delta` для порога `n*p0 - sqrt (n*log(1/delta)/2)`.
- Пол `coordMean p X t ≥ p0` требуется по каждой координате; одинаковое распределение успехов не предполагается.

## Hagi/Probability/Azuma.lean

- `hoeffding_lemma_prefix` ограничивает MGF условно центрированной величины с `-c ≤ X ≤ c` через `exp (lam^2*c^2/2)`. `azuma_mgf` по префиксным условным средним даёт `prodE ... ≤ exp (n*lam^2*c^2/2)`.
- `azuma_tail_low`: при `c > 0`, `n > 0`, `Δ > 0` масса события `azumaSum X n ω ≤ -Δ` не превышает `exp (-Δ^2/(2*n*c^2))`; это односторонний хвост.
- `adaptive_success_azuma`: для `S t pref ∈ [0,1]` и префиксных полов `p0 ≤ ∑ v, q v * S (t+1) (snoc pref v)` вероятность `n*p0 - Δ ≤ azumaSum S n ω` не меньше `1 - exp (-Δ^2/(2*n))`.

## Hagi/Probability/BatchSNR.lean

- `snr_realized` записывает SNR как квадрат среднего, делённый на дисперсию batchMean; `snr_linear` даёт точное `snr g B = B * snr g 1`.
- При `popMean g ≠ 0` и `0 < popVar g` теорема `snr_ge_one_iff` эквивалентно связывает `snr g B ≥ 1` и `criticalBatch g ≤ B`.
- `gain_decreasing_past_critical`: при положительных `Bstar alpha beta` и `Bstar ≤ B1 < B2` значение `gainPerCost` строго убывает от `B1` к `B2`.

## Hagi/Probability/BernoulliFactory.lean

- `probAccept_eq_bernPoly` доказывает равенство двух явных сумм `probAccept` и `bernPoly`; `binomWeight` содержит биномиальные веса `choose n j * p^j * (1-p)^(n-j)`.
- При `0 ≤ p ≤ 1` и `0 ≤ c j ≤ 1` для `j ∈ range (n+1)` теорема `probAccept_bounds` даёт `0 ≤ probAccept n p c ≤ binomMass n p`.
- Это точные тождества и границы конечной Bernstein-конструкции; равенство `binomMass n p = 1` отдельной теоремой файла не сформулировано.

## Hagi/Probability/CertifiedEstimator.lean

- Для независимых `X i ∈ [0,1]` доказаны `hoeffding_chernoff`, оптимизированный `hoeffding_tail` и `hoeffding_two_sided`: односторонний хвост суммы центрирований имеет границу `exp (-2*t^2/n)`, двусторонний для `n*eps` — `2*exp (-2*n*eps^2)` при `n > 0`.
- `certified_premise`: с вероятностью не меньше `1 - 2*exp (-2*n*eps^2)` из измеренного условия `∑X + 2*n*eps ≤ ∑Y` следует `∑coordMean p X ≤ ∑coordMean p Y`. Это вероятностная импликация на общем событии, не безусловная проверка посылки.
- `premises_union_confidence` объединяет фиксированное `S`: если каждое `A i` имеет вероятность не меньше `1-δ`, одновременное выполнение имеет нижнюю границу `1 - S.card*δ`.
- `anytime_safe_threshold` для положительных нормированных `q`, `0 < σ2`, `0 < α < 1`, `T > 0` и посылки CGF на каждом префиксе ограничивает через `α` массу существования `t < T` с превышением `μ + sqrt (2*σ2*log (T/α))`.

## Hagi/Probability/ChernoffCGF.lean

- `cgf_centering` для положительных `q` даёт `log ∑q*exp(c*g) = c*μ + log ∑q*exp(c*(g-μ))`; нормировка `q` в этой алгебраической формуле не требуется.
- `chernoff_subgauss_tail`: при `q > 0`, `σ2 > 0`, `u > 0` и ограничении центрированного CGF через `c^2*σ2/2` масса `{μ+u ≤ g}` не превышает `exp (-u^2/(2*σ2))`. `tail_complement` отдельно нормирует дополнение хвоста при `∑q = 1`.
- `kl_dv_attained`, `cramer_cgf` и `cramer_sup_le_kl` связывают KL с вариационным функционалом и супремумом Чернова; `subgauss_dev_kl` выводит нижнюю оценку KL через квадрат сдвига среднего, делённый на `2*σ2`.
- `mean_shift_tv` для ограниченной `g ∈ [a,b]`, `a < b`, оценивает сдвиг среднего через `(b-a)` и половину `L¹`-расстояния между положительными нормированными законами.

## Hagi/Probability/ConditionalSuccess.lean

- `success_count_lower` и `success_count_lower_p0`: при `0 < delta < 1`, измеримости, значениях `S t ∈ [0,1]` и `iIndepFun S μ` сумма успехов с вероятностью не меньше `1-delta` ограничена снизу суммой средних минус `concDelta T delta`, а при поле `p0 ≤ μ[S t]` — величиной `p0*T - concDelta T delta`.
- `log_growth` добавляет поточечную посылку `log C(t+1) - log C t ≥ a*S t - eps t`, `a ≥ 0` и положительность `C`; на том же стохастическом событии получается нижняя граница логарифма роста с вычетом `∑eps`.
- `takeoff_time_form` превращает её в `C T ≥ C 0 * exp (a*(p0*T - concDelta T delta) - ∑eps)` с вероятностью не меньше `1-delta`. Независимость успехов остаётся явной посылкой `h_emp_indep`.

## Hagi/Probability/EntropyConvexity.lean

- `log_sum_ineq` для положительных `a b` даёт `sum(a)*log(sum(a)/sum(b)) ≤ ∑a*log(a/b)`; `kl_convex_first` доказывает выпуклость KL по первому аргументу при `0 < lam < 1` и положительных функциях на конечном носителе.
- `kl_data_processing` для произвольной конечной `T : V → W` и положительных нормированных законов ограничивает KL после агрегации по волокнам исходным KL.
- `entropy_chain` раскладывает совместный `∑ρ log ρ` через маргиналь и условные строки; отсюда `joint_entropy_ge_marginal` и `entropy_subadditive`, все при положительной нормированной `ρ`.
- `gibbs_free_energy_identity` при `T > 0` точно равняет `-T*log Z` сумме средней энергии и `T*∑γ log γ` для канонического `γ`.

## Hagi/Probability/ExpChord.lean

- `exp_chord` — псевдоним `Hagi.Foundations.exp_chord_r`; `hoeffding_chord_mgf` для положительного нормированного `q` и `a ≤ g ≤ b`, `a < b`, ограничивает центрированный MGF хордой между `a` и `b`.
- `log_chord` и `amgm_weighted` дают вогнутость логарифма и взвешенное среднее при положительных `a b` и `0 < w < 1`; `young_two` доказывает `x*y ≤ x^p/p + y^q/q` для `x y ≥ 0` и сопряжённых `p > 1`, `1/p + 1/q = 1`.
- `hoelder_finite` и `hoelder_weighted` дают неравенство Гёльдера; `lp_mean_le_rms` использует нормированные неотрицательные веса, а `lyapunov_moment_mono` доказывает монотонность моментов при `0 < r < s`.
- `minkowski_weighted` даёт `L^p`-оценку суммы для неотрицательных весов и сопряжённых `p q`.

## Hagi/Probability/FiniteBayes.lean

- `observationEvidence_eq_sum` вычисляет свидетельство наблюдения как `∑x, p₀ x * K x y`; `posterior_apply` при `0 < observationEvidence` нормирует `p₀ x * K x y` этим свидетельством, а `posterior_sum_toReal` даёт сумму `1`.
- `mode_posterior_le` показывает, что `mode` максимизирует апостериорный закон; `mode_zeroOneLoss_le` минимизирует `zeroOneLoss` среди всех решений, а `mode_zeroOneLoss_le_observation` сравнивает его также с решением `y` для наблюдения того же конечного типа.
- `linkedPosterior_apply` отдельно раскрывает апостериорный закон связанного XOR-канала через `ν.map (eventMask neighbors)` и `flip x y` при положительном свидетельстве наблюдения.

## Hagi/Probability/FiniteEM.lean

- Центральное разложение выражает `ceDef q (jointMass model) - entDef q` как `-log evidence + KL(q, posterior)` при положительном свидетельстве наблюдения и `q.support ⊆ posterior.support`; при `q = posterior` оно упрощается до `-log evidence`.
- `observationEvidence_le_of_ceDef_jointMass_le`: при положительных свидетельствах наблюдения обеих моделей, включении поддержки старого апостериорного закона в новый и неравенстве ожидаемых полных кросс-энтропий новое свидетельство не меньше старого.
- `mStep_spec` для конечного непустого семейства выбирает кандидата, минимизирующего ожидаемую полную кросс-энтропию, и сохраняет требуемые положительность свидетельства и поддержку. `current_observationEvidence_le_mStep` при точном старом апостериорном законе доказывает монотонность фактического свидетельства наблюдения.

## Hagi/Probability/FiniteFamilyConfidence.lean

- `finite_family_upper_confidence`: для заранее фиксированного конечного семейства и независимых `[0,1]`-выборок все истинные средние одновременно не превосходят выборочные средние плюс `eps` с вероятностью не меньше `1 - card(ι)*exp(-2*n*eps^2)`.
- `finite_family_abs_error_confidence` даёт одновременную границу `|populationMean - empiricalMean| ≤ eps` с вероятностью не меньше `1 - 2*card(ι)*exp(-2*n*eps^2)`.
- `finite_family_selected_population_mean_gap_lower_confidence` сохраняет тот же двусторонний уровень для `baseline ω` и `candidate ω`, выбранных после наблюдения: эмпирический разрыв минус `2*eps` ограничивает разрыв истинных средних. Оценка опирается на границу вероятности объединения по всему заранее заданному семейству, а не на независимость выбранного индекса.

## Hagi/Probability/FiniteHamming.lean

- `changedCount_eq_sum` и `hammingRisk_eq_sum_coordinateLoss` разлагают число изменённых битов и его математическое ожидание по координатам, отличая эту цель от потерь всей плоскости.
- `coordinateMode_zeroOneLoss_le` выбирает моду каждой координаты; `hammingRisk_coordinateDecoder_le` доказывает глобальную минимальность покоординатного декодера по ожидаемому риску Хэмминга.
- `posterior_coordinateDecoder_le` переносит минимальность на апостериорный закон при положительном свидетельстве наблюдения; `posterior_coordinateDecoder_le_observation` дополнительно сравнивает его риск с риском самого наблюдения.

## Hagi/Probability/FiniteJointLogScore.lean

- `ceDef_chain` и `klDef_chain` разлагают совместные CE и KL на маргинальный член и взвешенную сумму условных строк при `p ≥ 0`, поддержке `0 < p z → 0 < q z` и соответствующей поддержке положительных левых маргиналов.
- Для нулевых маргиналов `conditionalRow` использует нулевую функцию как тотализацию; такая строка не объявляется вероятностным законом.
- При `leftMarginal q = leftMarginal p` и неотрицательных `p q` теорема `ceDef_eq_self_iff_conditionalRow_eq_of_leftMarginal_eq` характеризует `ceDef p q = ceDef p p` равенством условных строк на положительных маргиналах `p`.

## Hagi/Probability/FiniteLogScore.lean

- При неотрицательных нормированных `p q` и поддержке `0 < p x → 0 < q x` доказаны `klDef_nonneg_of_support` и `klDef_eq_zero_iff_of_support`: `klDef p q ≥ 0`, а равенство нулю эквивалентно `q = p`.
- `ceDef_self_le_of_support` даёт `ceDef p p ≤ ceDef p q`; родственные результаты характеризуют случай равенства через равенство функций на поддержке.
- `fromPMF_ceDef_self_le` и `posterior_ceDef_self_le` переносят оценку на PMF при включении поддержек, для апостериорного закона дополнительно требуя положительное свидетельство наблюдения.

## Hagi/Probability/FiniteMultiEM.lean

- `total_negativeLogEvidence_drop_eq` при положительных свидетельствах наблюдения и включениях поддержек старых апостериорных законов в новые раскладывает суммарное убывание отрицательного логарифма свидетельства в убывание полной ожидаемой кросс-энтропии плюс сумму апостериорных KL.
- `total_negativeLogEvidence_le_of_total_completeCE_le` из неравенства суммарных полных кросс-энтропий выводит невозрастание суммарного отрицательного логарифма свидетельства; отдельного улучшения по каждой единице не утверждается.
- `batchMStep_spec` выбирает один глобальный кандидат для всей индексированной семьи и минимизирует суммарную полную кросс-энтропию. `current_totalNegativeLogEvidence_le_batchMStep` при точных старых апостериорных законах доказывает итоговое невозрастание суммы.

## Hagi/Probability/Freedman.lean

- `freedman_lemma_prefix`: при `|X| ≤ b`, нулевом условном среднем, `∑q*X^2 ≤ sig` и `lam ≥ 0` MGF не превосходит `exp (lam^2*sig*exp(lam*b)/2)`. `freedman_mgf` итерирует эту границу по префиксам.
- `freedman_tail_low` при `b ≥ 0`, `sig > 0`, `n > 0`, `Δ > 0` ограничивает `P(azumaSum X n ≤ -Δ)` через `exp (-Δ^2/(2*(n*sig + b*Δ)))`.
- `adaptive_success_freedman`: для `S ∈ [0,1]`, префиксных полов `p0` и измеренной посылки `∑q*S^2 ≤ sig` вероятность `n*p0 - Δ ≤ azumaSum S n` не меньше `1 - exp (-Δ^2/(2*(n*sig + Δ)))`.
- `freedman_confidence` для фиксированного `n`: если `A ω ↔ ¬(azumaSum X n ω ≤ -Δ)`, то `A` выполняется с вероятностью не меньше `1 - exp (-Δ^2/(2*(n*sig + b*Δ)))`.

## Hagi/Probability/FreedmanFamilyConfidence.lean

- `finite_family_freedman_confidence`: для заранее фиксированного `s`, `c > 0`, `r > 0`, `V ≥ 0`, ограниченных центрированных приращений и вторых моментов, ограниченных `v`, с вероятностью не меньше `1 - 2*s.card*exp(-r^2/(4*(V+c*r)))` на всех `i ∈ s` из `historyCounter ≤ V` следует `|historyAdditive| < r`.
- `finite_family_selected_conditional_gap_of_good`: на этом общем событии, если базовый `b` и выбранный `σ ω` принадлежат `s` и оба счётчика не превосходят `V`, наблюдаемый разрыв минус `2*r` ограничивает разрыв условных средних.
- `finite_family_selected_conditional_gap_pos_of_good` добавляет предположение, что наблюдаемый разрыв больше `2*r`, и выводит положительность разрыва условных средних уже для выбранного по истории кандидата.

## Hagi/Probability/FreedmanTwoSided.lean

- `finite_freedman`: для марковской траектории с `X 0 ≤ 0`, `c > 0`, `r > 0`, `v ≥ 0`, ограниченными приращениями, условным средним приращения не выше нуля и рекурсией накопленной дисперсии фиксированный хвост `{r ≤ X k ∧ V k ≤ v}` не превосходит `exp (-r^2/(4*(v+c*r)))`.
- `history_additive_freedman` при `c > 0`, `r > 0`, `V ≥ 0` даёт фиксированный `k`-хвост для суммы центрированных вкладов. `history_additive_freedman_two_sided` для единых `r V` ограничивает событие `∃j ≤ T` с нарушением абсолютного порога через `2*(T+1)*exp(-r^2/(4*(V+c*r)))`.
- `anytime_freedman_thresholds` и `anytime_freedman_thresholds_two_sided` допускают разные `r j > 0` и `V j ≥ 0`: итоговые границы равны сумме по `j ∈ range (T+1)` соответствующих экспонент, с коэффициентом `2` в двустороннем случае.

## Hagi/Probability/GibbsConcentration.lean

- При единственном минимизаторе `v*`, зазоре `δ > 0` и верхней границе энергетического превышения `Δ` доказано `gibbs_var_tendsto_zero`: дисперсия энергии по Гиббсу при температуре `δ/(n+1)` стремится к нулю.
- `gibbs_var_steps_bound` даёт конечную оценку `≤ eps` при дополнительном условии `log (Δ^2 * card(univ.erase vstar) / eps) ≤ n+1`, положительных `Δ`, `eps` и ненулевом числе конкурентов.
- `mutual_info_nonneg` доказывает неотрицательность взаимной информации положительного конечного совместного закона.
- `efe_ceiling` из `G = P - I` и `I ≥ 0` даёт `G ≤ P`; `amortized_policy_bound` при равномерной ошибке `|Ghat-G| ≤ c` и минимизации `Ĝ` получает `G pih ≤ G π_s + 2*c` для любого `π_s`.

## Hagi/Probability/GibbsCooling.lean

- `gibbs_concentration`: при `T > 0` и зазоре `E vstar + δ ≤ E v` для всех `v ≠ vstar` доля Гиббса минимизатора не меньше `1 - card(univ.erase vstar)*exp(-δ/T)`. C221: формулировка байт-в-байт неизменна, доказательство — тонкий королларий канонического `gibbs_concentration_canon` (GibbsCore) с card-мостом и мостом `1 - x ≤ 1/(1 + x)`.
- На последовательности температур `δ/(n+1)` с `δ > 0` доказаны `gibbs_concentration_tendsto` и `gibbs_tv_tendsto`; при дополнительной верхней границе превышения `Δ` также `gibbs_expected_energy_tendsto` и `gibbs_entropy_tendsto_zero`. Свободная энергия стремится к `E vstar` по `free_energy_tendsto`.
- `free_energy_sandwich` даёт `Emin - T*log(card V) ≤ -T*log Z ≤ Emin`; `free_energy_sharp_lower` усиливает нижнюю границу через `log(1 + ((Finset.univ.erase vstar).card : ℝ)*exp(-δ/T))`.
- `gibbs_posterior_ratio` при `E vstar + δ ≤ E v` связывает доли `v` и `v*` множителем `exp(-δ/T)`; это пошаговое неравенство, а не только предельное утверждение.

## Hagi/Probability/GibbsCore.lean

- `gibbsW_pos`, `gibbsZ_pos` и `gibbs_normalize` при `T > 0` вводят положительные веса и нормировку; `gibbsZ_shift` вычисляет сдвиг энергии на константу как множитель `exp(-c/T)`.
- `gibbs_concentration_canon` даёт нижнюю долю минимизатора `1/(1 + (card V - 1)*exp(-δ/T))`.
- `gibbs_mean_energy_gap` при зазоре `δ` и общей верхней границе `E v ≤ E vstar + Δ` ограничивает среднюю энергию через `E vstar + Δ*(card V - 1)*exp(-δ/T)`.

## Hagi/Probability/GibbsInfoCore.lean

- `finite_kl_nonneg` доказывает неотрицательность KL для положительных нормированных законов. `gibbs_variational` при `T > 0` даёт `-T*log Z ≤ ∑ρ E + T*∑ρ log ρ` для любого такого `ρ`.
- `gibbs_free_energy_lower` и `free_energy_upper` образуют границы `Emin - T*log(card V) ≤ -T*log Z ≤ E vstar`, где вторая оценка верна для любого выбранного `v*`.
- `finite_max_entropy` ограничивает `-∑ρ log ρ` через `log(card V)`; `gibbs_expected_energy_lower` отдельно даёт `Emin ≤` среднюю энергию Гиббса.

## Hagi/Probability/KLSBridge.lean

- `gradCovBound`: для неотрицательной нормированной `q`, `C ≥ 0`, из посылки Пуанкаре для каждого направления и оценки чувствительности `(sens a x)^2 ≤ L^2*sqN a` следует `gradVar q g a ≤ C*L^2*sqN a`.
- `klsBatchNoise`: при `B > 0`, тех же посылках и нулевых попарных ковариациях центрированных проекций второй момент центрированного среднего по батчу не превосходит `C*L^2*sqN a / B`.
- `uncorrMeanVar` даёт точное разложение второго момента среднего по некоррелированным слагаемым, а `expQ_varEq` — стандартное тождество центрального второго момента.
- `klsChebyshev` из `expQ q (F^2) ≤ V` и `t > 0` получает массу `{t ≤ |F|}` не более `V/t^2`; предполагается неотрицательность `q`, но нормировка в самой формуле не требуется.

## Hagi/Probability/LinkedFlip.lean

- `linkedChannel_apply` представляет переход как `(ν.map (eventMask neighbors)) (x ^^^ y)`. Для `ν = pure none` канал оставляет `x` на месте, а для `pure (some a)` применяет `linkedMask neighbors a`.
- При `(neighbors a).card ≤ k` размер поддержки маски и `changedCount` после инверсии битов не превосходят `k+1`; якорь включается в это число.
- `uniformPlane_bind` доказывает сохранение равномерного закона после связанного канала, а `decodeByteRows_encodeBytePlane` и `encodeBytePlane_decodeByteRows` — обратимость конечного байтового представления. Смешивание цепи и равномерность эмпирических данных не утверждаются.

## Hagi/Probability/MWU.lean

- `mwu_potential_step`: при положительных нормированных весах, `ℓ ≥ 0`, `η > 0` и `η*ℓ ≤ 1/2` выполнено `log Z' ≥ -2*η*∑w*ℓ`.
- `mwu_sqrt_bound` даёт квадратично-корневую оценку regret при явных условиях баланса. C220: статический и двухрежимный regret-варианты удалены как zero-consumer дубликаты; канонический regret-результат — `mirror_regret` (Hagi/Optimization/MirrorDescent.lean).
- `selectedLoss_optimalPropensity_mse` при `0 < ∑|ℓ|` равен `(∑|ℓ|)^2 - ∑ℓ^2`. Строгое улучшение относительно равномерного PMF эквивалентно непостоянству `|ℓ|`; нулевой MSE эквивалентен наличию ровно одного ненулевого слагаемого.
- Аналогичные `selectedGradientMSE` и `selectedMeanGradientMSE` результаты при `0 < ∑‖g‖` дают строгое улучшение относительно равномерного распределения в точности при непостоянных нормах градиентов; `selectedGradientMSE_upperBoundPropensity_le` ограничивает MSE через `(∑|a|)^2 - ‖∑g‖^2` при `0 < ∑|a|` и `‖g b‖ ≤ a b`.
- Lint repair (C220): the lock refresh exposed a C216 private nonemptiness witness duplicating the Runtime one (equal statement hash; the lock had been stale since C216). Fixed by deleting the private duplicate and using Mathlib canonical `Finset.univ_nonempty` at all 13 sites (proof-body-level only; public statements unchanged; census −16 = 8 theorems + 7 simp rows + the duplicate).

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

## Hagi/Probability/PMFBridge.lean

- `toPMF` строит PMF из неотрицательной функции `q` с суммой `1`, а `fromPMF` переводит массы через `ENNReal.toReal`; `toPMF_apply` даёт `ENNReal.ofReal (q v)`, `fromPMF_sum` — сумму вещественных масс, равную `1`.
- `fromPMF_toPMF` и `toPMF_fromPMF` доказывают оба обратных тождества на конечном носителе. Мост между `klDef` и интегральной KL-дивергенцией на мерах этими теоремами не устанавливается.

## Hagi/Probability/PinskerTV.lean

- `pinsker_sqrt_kl` даёт `TV ≤ sqrt(KL)` для положительных нормированных законов, `tv_le_sqrt_one_minus_exp` — оценку `TV ≤ sqrt(1-exp(-KL))`, а `tv_le_pos_part_kl` ограничивает TV положительной частью KL-суммы.
- `kl_variational_lower` доказывает вариационную нижнюю границу KL через произвольную `f`; `pac_chernoff_events` при `KL(p‖q) ≤ κ` ограничивает `p(s)` через `κ + log(1 + (exp 1 - 1)*q(s))`.
- `pinsker4_fin` для `f : V → [0,1]` даёт `|E_q f - E_p f| ≤ 2*sqrt(klDef q p)`. `gen_pair_bound` добавляет стабильность `E_q|f-g|`, а `cmi_iteration` при `n > 0`, неотрицательных `stab KL` и поэлементных границах выводит усреднённую оценку `Δ/n ≤ stab/n + 2*sqrt(KL/n)`.

## Hagi/Probability/RankedStopRouting.lean

- Если каждый поддерживаемый нетерминальный переход выполняет `R a b` и строго увеличивает rank, терминальные строки являются `PMF.pure a`, `rank a ≤ B` и `B ≤ T`, то `terminal_at_rankBudget_of_historyLaw_support` доказывает терминальность координаты `B` каждой поддерживаемой полной истории. Начальный ранг нулём не требуется.
- `historyLaw_ranked_hitBy_eq_one` усиливает это до массы `1` события `∃j ≤ L, terminal (historyIndex T j)`; `classifyRouting_some_ranked_arrived` возвращает `.Arrived` в координате `L`.
- Для общего `classifyRouting` доказаны различия режимов: `.Arrived` при корректном префиксе и терминальности, `.Hold` при `k < T`, корректном префиксе, готовой строке и нетерминальности, `.Unknown` при неготовой строке, нарушенном префиксе либо исчерпанном бюджете без терминальности.

## Hagi/Probability/SphericalAngle.lean

- `sphericalAngle_add_two` при `n > 0` даёт `Ω(n+2) = (2π/n)*Ω n`; `sphericalAngle_even_geo` и `sphericalAngle_odd_geo` ограничивают чётную ветвь от `8` и нечётную от `9` геометрическими последовательностями с множителем `π/4`.
- `sphericalAngle_tendsto_zero` доказывает `Tendsto sphericalAngle atTop (nhds 0)`.
- `sphericalAngle_seven` вычисляет `Ω 7 = 16*π^3/15`, а `Omega_7_gt_Omega_6` и `Omega_7_gt_Omega_8` доказывают строгие сравнения с соседними целыми размерностями.
- `digamma_peak_exists` и `digamma_logpi_root_exists_sharp` при явных двусторонних ограничениях на постоянную Эйлера–Маскерони доказывают существование корня уравнения для дигаммы в заданных интервалах. Это не полное доказательство численного положения непрерывного максимума `Ω`.

## Hagi/Probability/StationaryFlatness.lean

- `tail_sum_identity`: для натуральнозначного `X ≤ M` на конечном вероятностном пространстве `expectNat q X = ∑_{k<M} probGe q X (k+1)`.
- `sum_pow2_inv_le` при `N ≥ 1` даёт `∑_{k<N} (k+1)⁻¹^2 ≤ 2 - N⁻¹` через телескопическую оценку `inv_sq_le_sub_inv`.
- `flatness_moment_bound`: если `C ≥ 0` и каждый хвост `probGe q X (k+1) ≤ C*(k+1)⁻¹^2`, то `expectNat q X ≤ 2*C`. Связь этого вывода с обобщением модели не доказывается.

## Hagi/Probability/ThermoAxes.lean

- `noise_axes_coincide`: при `r^2*c = 1`, `eta0^2*B0 = 1` и `B0 ≠ 0` для каждого `t` выполнено `eta0^2*r^(2*t) = 1/(B0*c^t)`.
- `noise_budget_axes_equal` при тех же посылках доказывает равенство конечных сумм по `range n`. Это почленное алгебраическое совпадение двух заданных последовательностей, а не эквивалентность траекторий обучения.

## Hagi/Probability/ThermoBridge.lean

- `prodE_as_expQ` отождествляет ожидание `prodE (uniP b)` с `Probability.expQ` по постоянной плотности равномерного произведения.
- `batchVar_expQ` для непустого `Fin b` переносит точный закон дисперсии в этот интерфейс: `expQ` центрированного квадрата `batchMean` равен `popVar g / b`.

## Hagi/Probability/WSqD.lean

- `stable_phase_noise` при `B0 ≠ 0` вычисляет сумму по n_w стабильных шагов как `sigma^2*n_w/B0`.
- `cooldown_tail_constant`: при `sigma ≥ 0`, `c > 1`, `Bd 0 > 0` и геометрическом росте для `t < n_d` сумма фазы затухания не превосходит `sigma^2*c/(Bd 0*(c-1))`.
- `wsqd_noise_budget` объединяет ровно две суммы: стабильную длину n_w и длину затухания n_d, с `B0 > 0`, `Bd 0 = B0` и теми же условиями роста. Отдельного слагаемого разогрева в теореме нет.

## Hagi/Runtime/BF16Delta.lean

- `Code` и `decode` задают все конечные BF16-коды с точным значением в `ℚ`,
  включая signed zeros и subnormals. `exists_IsNearest` строит ближайший код
  для каждого рационального аргумента без глобальной RNE/tie-breaking функции.
- `extreme_nearest_delta_loses_update`: при двух pointwise nearest-посылках
  обновление от anchor `2^127` к `129/128` может оказаться нулевым после
  nearest delta/recovery. Поэтому наивная rounded delta-write не сертифицируется.
- `exists_sameBinade_difference`: для положительных кодов с равным ненулевым
  exponent точная разность представима в обоих порядках, включая subnormal.
- `guardedRead_nearest_returns_new`: под этим guard две nearest-посылки
  возвращают `decode new`; вне guard функция также возвращает `decode new`
  непосредственно, не используя readback.
- Это логический code contract, не packed RAM, support FTZ, GDN adapter или
  доказательство memory/latency saving и улучшения качества обучения.

## Hagi/Runtime/ControllerGates.lean

- `logitRange_scale` при `tau > 0` даёт линейное масштабирование диапазона, `variance_gate_contract` при `tau ≥ 1` — сокращение квадратичной величины `range^2/8`, а `variance_gate_normalize` при `Rbar > 0` и `Rbar ≤ range f` нормализует диапазон ровно к `R̄`.
- `trust_region_proj_norm` при `R > 0` и `R ≤ ‖x‖` даёт норму `R` для `(R/‖x‖)•x`; `trust_region_nearest` доказывает, что эта точка является ближайшей к `x` среди всех `y` с `‖y‖ ≤ R`.
- `dynamic_branch_variance` при `L > 0` и `v ≥ 0` вычисляет сумму `L` одинаковых вкладов `((sqrt(2*L))⁻¹)^2*v` как `v/2`.

## Hagi/Runtime/DyadicTernary.lean

- `dyadicLevel_pos` подтверждает положительность всех 255 масштабов, а `dyadicLevel_zero` равен `1/128`. `dyadicPayload_injective`, `dyadicBlock_injective` и `dyadicBlockDecode_encode` доказывают инъективность и точное декодирование пары масштаба с пятью тритами.
- Декодер отклоняет нулевой старший байт и зарезервированные байты троичного кода; пример `knownSample_decode_reconstruction` восстанавливает `![1/4, -1/4, 0, 0, 0]`.
- `dyadicBlock_eight_bit_impossible` и `dyadicBlock_fifteen_bit_impossible` исключают инъективные коды соответствующей ширины. `reference64BitCounter_eq = 320` и `16 < reference64BitCounter` относятся только к явно названной модели подсчёта, не к физической памяти или времени.

## Hagi/Runtime/LiveDeltaQuant.lean

- `quantMat_entry`: при `s > 0` и `ternInRange s (M i j)` поэлементная ошибка `|M i j - quantMat s M i j|` не превышает `s/2`.
- `quantMat_sq_bound`: если условие диапазона выполнено для всех элементов, суммарная квадратичная ошибка не превосходит `(card m * card n)*(s/2)^2`. Сатурированные элементы в эту формулу не входят.

## Hagi/Runtime/TernaryCodec.lean

- `ternaryValueDecode_encode` восстанавливает именно `qTern level value`; `ternaryBlockDecode_encode` декодирует каждый из пяти тритов, а `packedTernarySamples_decode_point` даёт покоординатное `qTern level (values i)` после упаковки.
- `ternaryByteBlock_injective` доказывает инъективность байтового блока; `ternaryOneBit_impossible` исключает вложение трита в один бит, а `ternaryBlock_seven_bit_impossible` — вложение пяти тритов в семь бит.
- Это свойства фиксированного логического кодека, а не восстановление исходных вещественных значений или оценка размещения данных в памяти компьютера.

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

## Hagi/Step/AdaptiveSafeQP.lean

- `latticeNet_covers`: при `n > 0`, `D ≥ 0`, `epsDir > 0`, `D*sqrt n/epsDir + 1 ≤ M` и `‖x‖ ≤ D` существует точка сетки на расстоянии не более `ε_dir`; `latticeNet_card_le` ограничивает размер через `(2*M+1)^n`.
- `adaptive_net_concentration` при `m > 0`, `sigma > 0`, `delta ∈ Ioo 0 1` и посылках нулевого среднего, независимости, измеримости и ограниченности шума на всём шаре `D+epsDir` даёт равномерную по сетке концентрацию с вероятностью не меньше `1-delta`.
- `adaptive_direction_concentration` переносит её на любое `dstar ω` с `‖dstar ω‖ ≤ D`, добавляя `sigma*epsDir`; измеримость `d*` отдельно не требуется.
- `adaptive_safeQP_feasibility` на событии вероятности не меньше `1-delta`: если градиенты мини-батча выполняют `-(eps i) ≤ ⟪g i + noise, dstar⟫`, то истинные градиенты выполняют `-(eps i + adaptiveNoiseEps + sigma*epsDir) ≤ ⟪g i,dstar⟫`.

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

## Hagi/Step/MDLObjective.lean

- `mdlObjective_delta` раскладывает изменение цели в изменение ошибки предсказания плюс `λ` на изменение длины описания.
- `mdlObjective_nonincreasing` при `lam ≥ 0` и невозрастании обеих частей доказывает невозрастание всей цели.
- `mdlObjective_tradeoff`: при `lam ≥ 0`, выигрыше предсказания не меньше `δ ≥ 0`, `0 < c` и кодовой добавке не более `δ-c` получается строгое улучшение с запасом `c`; `mdlObjective_lambda_zero` устраняет кодовую часть.

## Hagi/Step/MDLThreeCurrency.lean

- `J3_nonincreasing`: если ошибка предсказания, стоимость состояния и защищённый риск не возрастают, а `lamM lamR ≥ 0`, суммарная цель `J3` не возрастает.
- `double_counting_identified` при `cst = Lpred` упрощает цель до `(1+lamM)*Lpred + lamR*Rprot`, явно выявляя повторный учёт одной величины.
- `no_compression_below_entropy` для положительных нормированных `p q` доказывает `sourceEntropy p ≤ dataCodeLen p q`.

## Hagi/Step/Muon.lean

- `muon_step_bound` и квадратичный `muon_pl_rate`: если `‖P z‖ ≤ ‖z‖` для всех `z`, то `muonDir P g` не увеличивает норму и квадрат нормы.
- `MuonNS.ns_error_factor` даёт `1 - ns u = (u-1)^2*(u+2)/2`; на `0 < u ≤ 1` доказаны инвариант и монотонность, а на `0 < u < 1` — строгое `u < ns u < 1`.
- `MuonAlign.muon_alignment_optimal`: для `sig i ≥ 0` и комплексной `Q` с `Qᴴ*Q = 1` сумма `sig i*(Q i i).re` не превышает суммы `sig i`.
- `grad_norm_grows` для линейной квадратичной модели со всеми весами `1` равен `m*d^3`; `mup_grad_invariant` при `m ≥ 1` и весах `1/sqrt m` равен `d^3`.
- `muon_wd_recursion` даёт пошаговую оценку с затуханием весов; `wd_boundedness` при `0 < eta*lam ≤ 1`, `eta ≥ 0` и `‖U s‖ ≤ C` ограничивает `‖theta T‖` через `(1-eta*lam)^T*‖theta 0‖ + C/lam` при заданной рекурсии.

## Hagi/Step/NCEExact.lean

- `nce_decomposition`: при `0 < p v → 0 < q v` на поддержке `p` выполнено `log p = log q + log(p/q)`; `nce_correction_pos` доказывает положительность этой коррекции.
- `partEst_unbiased` при положительном нормированном `q` даёт `∑q*impW z q = partZ z`; `partEst_gap_jensen` и `jensen_log` ограничивают средний логарифм логарифмом `partZ z`.
- При положительном нормированном `q` теорема `secondMomentW_ge_sq` даёт `(partZ z)^2 ≤ secondMomentW z q`; `adaptiveK_bound` при `moment ≥ 0`, `eps > 0` и `moment/eps ≤ K` выводит `moment/K ≤ eps`.
- `anchor_cadence_criterion` при `gamma rho eps > 0` доказывает критерий остановки: для любого `s ≤ gamma*eps/rho` выполнено `rho*s/gamma ≤ eps`.

## Hagi/Step/NewtonPolar.lean

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
- `segmentMinNorm_inner_nonneg` даёт неотрицательность скалярного произведения для каждой точки исходного сегмента; `hard_budget_forces_orthogonal` из одновременных неотрицательных и неположительных ограничений выводит точное `⟪g i,d⟫ = 0`.

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

- `spectral_tail_energy`: для ортонормированного семейства `v` и
  `x = Σᵢ⟪x,vᵢ⟫vᵢ` энергия отброшенного хвоста равна
  `‖x − spectralProj s x‖² = Σ_{i∈sᶜ}⟪x,vᵢ⟫²`.
- `three_stage_error_budget`: из `‖P W − A‖ ≤ eps_rank` и
  `‖A − QA‖ ≤ eps_quant` следует
  `‖W − QA‖ ≤ ‖W − P W‖ + eps_rank + eps_quant`.
- `spectral_safeQP_target`: в вещественном `InnerProductSpace X` с
  `[FiniteDimensional ℝ X]`, при `eps i ≥ 0` существует евклидова проекция
  `d*` фильтрованной цели `P g0` на `safeSet g eps`; её ошибка относительно
  `g0` не превосходит суммы проекционной ошибки и хвоста `‖g0 − P g0‖`.

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

## Hagi/Step/StochasticSafeQP.lean

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

## Hagi/Step/SubspaceSafeQP.lean

- `subspace_eps_le_full`: при `r ≤ n`, `D,epsDir,σ ≥ 0`, `m > 0`, `δ > 0`
  и `δ ≤ 2|K|(2M+1)^r` выполняется
  `adaptiveNoiseEps K r D epsDir M σ m δ
    ≤ adaptiveNoiseEps K n D epsDir M σ m δ`.
- Тем самым меньшая размерность сети не увеличивает тот же модельный порог
  концентрации; утверждение ограничивается сравнением этих двух порогов.

## Hagi/Step/Upgrades.lean

- `skip_bound`: если `p = softmaxW s` — распределение и масса `δ`
  пропущенного множества меньше `1`, после удаления этого множества и
  перенормировки сумма абсолютных изменений весов не превосходит `2δ`.
- `readPolicy_exists` выражает существование максимума конечного набора
  вариантов для функции выигрыша от чтения.
- `sink_cost_bound` повторяет ту же оценку `2δ` для перенормированного
  распределения после отбрасывания массы `δ`; `sink_window_substitutes`
  из `T > 0` и `T(W+S)=C` получает `W+S=C/T`.

## Hagi/Step/VariantSafeQP.lean

- `mProject_exists_unique`: в вещественном `InnerProductSpace X` с
  `[FiniteDimensional ℝ X]`, при `eps i ≥ 0` и непрерывном линейном
  автоморфизме `A` существует единственный минимизатор `mDist A d d0`
  на `safeSet g eps`. Через `mDist_eq` это евклидова проекция в координатах `A d`.
- `klsSafeQP_certified`: при `C ≥ 0`, `B > 0`, принятых условиях Пуанкаре,
  границе чувствительности и некоррелированности батча, точной девиации
  оценки, `t > 0` и
  `eps + |gd|t ≤ gd·trueInner x` для всех `x`, масса события
  `eps ≤ gd·estInner` не меньше
  `1 − (C·L²‖a‖²/B)/t²`.

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

## Hagi/System/DiscreteStep.lean

- `quantized_descent_telescope`: при `Δ > 0` и фактических обновлениях
  `x(t+1) = gridQ Δ (x t − γg t)` для `t < T` выполняется
  `x T ≤ x 0 − Σ_{t<T}γg t + T·Δ/2`.

## Hagi/System/GrowthComputed.lean

- `growthQuad_step`: для `growthQuad w = Σᵢwᵢ²/2` градиентный шаг
  даёт точное равенство `growthQuad(growthStep w eta) = (1−eta)²growthQuad w`.
- `growthQuad_descent`: при `0 < eta < 2` и `Σᵢwᵢ² ≠ 0` энергия строго
  убывает.
- `growEnergy_derived`: если `S.energy = growthQuad S.weights`, а
  `S.effects.growEnergy` равна энергии после того же шага, то при этих условиях
  доказывается одновременно неравенство
  `growEnergy ≤ S.energy − (1−(1−eta)²)growthQuad S.weights`
  и положительность вычтенного gain.

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
- `budget_account` точно раскрывает бюджет составного шага как
  `S.budget − verify(S).budgetSpend`.

## Hagi/System/GrowthStateViews.lean

- `GrowthState_parts_roundtrip`: разбиение состояния на модельные, метрические,
  ресурсные, оптимизаторные и памятные проекции обратимо:
  `ofParts(toParts S) = S`.
- `toParts_injective`: равенство всех проекций двух состояний влечёт
  равенство самих состояний.

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

## Hagi/Legacy/AdvanceWitness.lean

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

## Hagi/Unified/AnytimePACBayes.lean

- `anytime_catoni`: при `lam > 0`, неотрицательном супермартингале `L`
  с `E[L0] ≤ 1`, `L t = exp(lam·S t − ψt)` и `δ > 0` вероятность существования
  `t ≤ n`, для которого `S t > (ψt + log(1/δ))/lam`, не превосходит `δ`.
  Условие супермартингала является частью теоремы, а не выводится из формулы `L`.

## Hagi/Legacy/ArchitectureTheorem.lean

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
- `budget_horizon_nonneg`: из `B T ≥ 0`, `spend t ≥ 0` и
  `B t = B0 − Σ_{j<t}spend j` следует `B t ≥ 0` для всех `t ≤ T`.

## Hagi/Legacy/Assumptions.lean

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

## Hagi/Unified/CanonicalParams.lean

- `advance_params_ne`: для перехода с `u.stepDir ≠ 0`
  канонические `S.params` действительно различаются; положительность шага
  закреплена типом входного перехода.
- `bridge_update`: законный инъективный проектор toW переносит это различие
  на `canonWeights`; `idProj` доказывает существование такого проектора
  на `Fin d → ℝ`.

## Hagi/Unified/CapabilityLocal.lean

- `capability_geometric_of_local`: при `alpha > 0`,
  `capability(t+1) = capability t + growGain t` и
  `alpha·capability t ≤ growGain t` для всех `t` получается
  `capability 0·(1+alpha)^T ≤ capability T`.
- `capability_strict_first`: при положительной начальной capability и строгом
  условии `alpha·capability 0 < growGain 0` первый шаг строго превосходит
  `(1+alpha)·capability 0`.

## Hagi/Unified/CertUnify.lean

- `tc_consequence`: из цепочки `StepCert` и нижней границы
  `Φ_min ≤ obj(f t)` для всех `t ≤ n` следует
  `Σ objectiveDrop ≤ obj(f 0) − Φ_min + Σ riskSpend`.
- `ec_chain_to_tc`: тот же телескоп получается из связанных исполнением
  сертификатов `ExecutedCert` при неотрицательных заданных рисках и бюджетах,
  без отдельной постановки шаговой гипотезы `StepContract`.

## Hagi/Legacy/CertifiedGrowth.lean

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

## Hagi/Legacy/CorePremisesDerived.lean

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

## Hagi/Unified/Ctv2Telescope.lean

- `ctv2_family_telescope`: для фактических `S(t+1)=advance(S t,u t)`,
  сертификатов `CertifiedTransitionV2`, grow/merge-оценок, `0 < L`,
  `eta ≤ 1/L`, `‖stepDir‖² ≤ inner`, квадратичного joint и
  `compressEnergy−jointEnergy ≤ κ·s·quantErr`
  получается `Σ stepDrop(u t) ≤ energy(S0) − energy(S T)`.
- `verify_family_telescope`: если дополнительно `0 ≤ eta`, `0 ≤ κ,s`
  и `quantErr ≤ 1/2` на каждом шаге, то сумма `verify(S(t+1)).decrease`
  ограничена тем же фактическим убыванием.

## Hagi/Unified/DerivAlong.lean

- `lip_energy_from_gradient`: если `E` всюду дифференцируема и
  `‖fderiv E w‖ ≤ κ`, то `|E w−E q| ≤ κ‖w−q‖` для любых `w,q`.
- `smooth_from_lipschitz_gradient`: при дифференцируемости,
  `‖fderiv E y−fderiv E x‖ ≤ L‖y−x‖` и непрерывности производной вдоль
  сегмента получается
  `E(q+dir) ≤ E q + fderiv E q dir + L‖dir‖²/2`.
- `core_premises_joint_operational` специализирует это к `params−eta·stepDir`
  с `eta ≥ 0`, `E params ≤ mergeEnergy` и совпадением производной с `grad`.
  `core_premises_compress_operational` для скалярного `E` получает
  `E(gridQ Δ x)−jointEnergy ≤ κ|x−gridQ Δ x|`
  при `Δ > 0`, `E x ≤ jointEnergy` и `‖fderiv E‖ ≤ κ`.
- `potential_joint_of_ceOneHot_jacobian_remainder`: в вещественном
  `InnerProductSpace X`, для конечного непустого `V`, дифференцируемого `f`
  с якобианом `J`, остатка `≤ ρ‖w−params‖²` на шаре и условий
  `∀ z, fderiv ℝ (fun w => Hagi.ceOneHot y (f w)) S.params z =
    ⟪S.grad, z⟫_ℝ` и
  `∀ u v, -(J S.stepDir u - J S.stepDir v) ≤ R`, а также
  `stepDir ≠ 0`, `‖stepDir‖² ≤ inner`, `0 < L`, `0 ≤ eta ≤ 1/L`,
  `eta‖stepDir‖ ≤ r`, точных значений CE до/после и
  `L = 2(R²/8 + 2ρ‖stepDir‖²)/‖stepDir‖²`
  получается `potential(joint S)−potential S ≤ −gainJoint S + riskJoint S`.
- `potential_joint_of_ceLinear_residualDirection`: для `GrowthState` на
  `EuclideanSpace ℝ (Fin d)`, конечного непустого `V`, матрицы
  `X : Matrix V (Fin d) ℝ` и цели `t` требуются
  `S.stepDir = -ceDirection X S.params t`, `S.grad = S.stepDir`, `0 < S.sp.L`,
  `S.sp.L = featureAbsSum X ^ 2`, `0 ≤ S.sp.eta ≤ 1 / S.sp.L`, а также
  идентификации старой энергии с CE текущих logits и
  `S.effects.jointEnergy` с CE в фактических `(joint S).params`. Получается
  `potential(joint S)−potential S ≤ −gainJoint S + riskJoint S`; нулевое
  направление допускается, global smoothness и universal strict descent не
  утверждаются.

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
  `w−a` выполняется `quadE(w−eta·grad) = (1−eta)²quadE a w`.
- `quad_eta_descent`: при `0 < eta < 2` и `quadE a w > 0` энергия строго
  убывает; при `eta=1` тождество даёт нулевую энергию только для этой цели.

## Hagi/Unified/Distillation.lean

- `soft_dial_max` и `soft_dial_zero`: `softProb x → 1` при `x→+∞` и
  `softProb x → 1/2` при `x→0`.
- `soft_entropy_bound`: для `0 < p < 1` двоичная энтропия не превосходит
  `log 2`.
- `attention_scale_softens`: `softProb(s/√n) → 1/2` по `n`;
  `attention_no_scale_saturates`: если `s > 0`, то `softProb(s·n) → 1`.

## Hagi/Unified/EFTheory.lean

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

## Hagi/Unified/ExecutableController.lean

- `finiteSelection_cost_eq_minimumResource`: если вычислимый список
  содержит все действия, выбранная стоимость совпадает со стоимостью
  математического минимума в cast-модели; совпадение самих действий при равных
  стоимостях не утверждается.
- `selectionReport_comparisons`: число вызовов отношения равно
  `admitted.length − 1` и не превосходит длины исходного списка.
  Это логические вызовы, не инструкции процессора или время.
- Частные результаты показывают, что фильтрованный выбор реально является
  `List.argmin` по memory-first стоимости среди допущенных элементов списка.

## Hagi/Unified/ExecutableSelection.lean

- `auditedArgmin_fst`: инструментированный fold выбирает ровно тот же
  элемент, что `List.argmin` по заданной стоимости.
- `auditedArgmin_snd`: число сравнений равно `as.length − 1`;
  `auditedFilter_snd` насчитывает ровно один вызов составного guard
  на каждый входной элемент. Счётчики относятся к логическим вызовам.

## Hagi/Unified/ExecutedCert.lean

- `measured_honest` и `measured_lower`: зависимый сертификат связывает
  измерение `m`, фактический спуск `C.drop` и ошибку `d` неравенствами
  `drop−d ≤ m ≤ obj(s)−obj(step s)+d`, а `drop > 0` входит в сертификат.
- `telescope_measured`: по исполненной цепочке из `n` шагов
  `Σm ≤ obj(s)−obj(traj step s n) + Σd`, и все шаговые `(cs t).drop` положительны.

## Hagi/Unified/FannesComplete.lean

- `shannon_le_log_card`: для вектора вероятностей на конечном носителе
  `H(p) ≤ log|ι|`.
- `fanes_unconditional`: для неотрицательных `p,q` с суммами `1`
  и `t = tvHalf p q` выполняется
  `H(p)−H(q) ≤ t·log|ι| + (1+t)·h₂(t/(1+t))`
  без дополнительной разлагающей гипотезы.
- `mix_entropy_upper` и `mix_entropy_lower` дают соответствующие
  верхнюю и нижнюю оценки энтропии выпуклой смеси; это поддерживающие
  неравенства, а не замена основной Fannes-границы.

## Hagi/Unified/FunctionalState.lean

- `fs_two_steps_productive`: при `0 < eta < 2`, `eta ≠ 1`, `a ≠ w`
  и `s.weights = w` два последовательных `funStepJoint` строго убывают
  энергию на каждом шаге. Условие `eta ≠ 1` гарантирует ненулевой остаток
  после первого шага.
- `fs_energy_after` вычисляет энергию преемника из его новых весов,
  а не копирует старое значение.

## Hagi/Unified/GaugeQuotient.lean

- `quotientResidual_gauge_invariant`: остаток
  `r_G(z) = inf_φ‖Tz−e^{iφ}z‖` не меняется при фазовом вращении.
- `relativeEquilibrium_residual_zero`: если `Tz = rot φ₀ z`, то `r_G(z)=0`;
  `relativeEquilibrium_orbit` дополнительно даёт `T^k z = rot(kφ₀) z`.
- `seq_dev_exact` при `s ≠ 1` даёт точное решение скалярной модели
  `x_t−c/(1−s) = s^t·(x₀−c/(1−s))`.

## Hagi/Legacy/GrandSynthesis.lean

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

## Hagi/Unified/GrowthBridge.lean

- `growth_state_takeoff`: при `alpha > 0`, `sigma t ≤ 1`,
  положительной capability и gate `alpha·C_t ≤ growGain` на каждом
  успешном шаге итог не меньше `C0·(1+alpha)^{Σsigma}`.
- `growth_state_takeoff_window`: для фиксированного положительного
  `G = S.effects.growGain`, начального gate и того же gate при успехах
  `Σsigma ≤ 1/alpha + 1 − C0/G` и
  `(1+alpha)^{Σsigma} ≤ exp(1+alpha−alpha·C0/G)`.
  Так фиксированный gain даёт только ограниченное окно роста.
- `growth_state_takeoff_probabilistic`: при `0 < δ < 1`, `a ≥ 0`,
  измеримых независимых `[0,1]`-индикаторах со средними `≥ p0`,
  положительной capability и поточечном log-bridge нижняя экспоненциальная граница с
  `a(p0T−concDelta(T,δ))−Σeps` имеет вероятность не менее `1−δ`.

## Hagi/Unified/GrowthComputedCert.lean

Именованных top-level theorem-деклараций нет; носители результата —
две definitions.
- `next S eta`: сохраняет все каналы `S`, кроме замены `S.weights`
  на `growthStep S.weights eta`.
- `stepCert`: при `0 < eta < 2` и `Σᵢ S.weightsᵢ² ≠ 0`
  создаёт `CertStep` с `drop = (1−(1−eta)²)growthQuad S.weights`.
  Его поля `CertStep.drop_pos` и `CertStep.actual` содержат доказательства положительности
  и фактического неравенства, но не являются отдельными top-level теоремами.

## Hagi/Unified/GuardedRobustLogit.lean

- `logitCE_guardedLogitNext_le`: для скалярной логистической модели
  выбранный преемник никогда не увеличивает `logitCE`; без estimated upgrade
  он равен текущему состоянию.
- `guardedLogitNext_eq_update_of_upgrade`: при `eta > 0`, ресурсных условиях
  `M ≥ 1`, `C ≥ 2` и активном guard преемник точно равен
  `w + eta/(1+exp w)`; `logitCE_guardedLogitNext_lt_of_upgrade`
  даёт его строгий спуск.
- Тот же точный преемник можно получить из явного условия
  `1 ≤ logitCE w − logitCE(w+eta/(1+exp w))`.
  Меньший спуск не обязан проходить guard с радиусом `1/2`.

## Hagi/Unified/GuardedRobustResourceMin.lean

- `guardedMinimumResource_feasible`: при допустимом stay и односторонней
  ошибке базового действия выбранное действие остаётся в исходном `feasible`.
- `guardedMinimumResource_quality_ge_stay`: если абсолютная ошибка оценки
  на всех допустимых преемниках не превосходит `eps`, фактическое качество
  выбора не ниже качества stay.
- `guardedMinimumResource_cost_le`: при активном upgrade,
  `hb : b ∈ feasible p M C` и
  `herr : ∀ a ∈ feasible p M C,
    |value(step a s) − estimate(step a s)| ≤ eps`
  стоимость не выше стоимости любого такого допустимого `b`, для которого
  `stay + 2eps ≤ value(step b)`.
  Это сравнение только с указанными конкурентами, не всеобщий минимум.

## Hagi/Unified/GuardedRobustSelection.lean

- `guardedRobustNext_exists`: guard возвращает фактический преемник
  некоторого исходного допустимого действия; без estimated upgrade —
  именно преемник stay.
- `guardedRobustNext_quality_ge_stay`: при равномерной по допустимым
  преемникам абсолютной ошибке `≤ eps` и пороге `2eps`
  фактическое качество не убывает относительно stay.

## Hagi/Unified/GuardedRobustTrajectory.lean

- `guardedRobustPath_quality_monotone`: если stay тождествен на состояниях,
  а на каждом шаге ошибки оценки всех допустимых преемников не превосходят
  `eps t`, фактическое качество монотонно; при верхней границе `B`
  оно сходится к условному супремуму, не обязательно равному `B`.
- `guardedRobustGain_sum_range` точно телескопирует приросты;
  `guardedRobustGain_summable` и `guardedRobustGain_tendsto_zero`
  получают суммируемость и стремление приростов к нулю при тех же условиях
  и общей верхней границе качества. Сходимость параметров не утверждается.
- `fixedBiasBinaryPath_eventually_eq`: на двух действиях с фиксированной
  смещённой оценкой и тождественным stay ограниченная сверху ценность
  влечёт стабилизацию самого пути на одном конечном состоянии.
  `scaledBiasBinaryPath_tendsto_eventual_value` переносит это на положительный
  порог `δ`; нормировка не означает достижение глобального оптимума.

## Hagi/Unified/HonestTransition.lean

- `honest_actual_drop`: сертификат содержит строгое фактическое убывание
  `obj s' < obj s` и `objectiveDrop > 0`, а не только положительность
  числового показателя.
- `honest_telescope`: два связанных перехода дают
  `obj s2 ≤ obj s0 − (drop1+drop2)`.
- `honest_two_steps_existent`: построен числовой свидетель двух
  последовательных положительных спусков на квадратичной цели.

## Hagi/Unified/InfoCanonical.lean

- `shannon_eq_entDef` и `tvHalf_eq_tvDef` доказывают точные равенства двух
  пар информационных определений.
- `fanes_entDef`: для вероятностных `p,q` получается
  `entDef p−entDef q ≤ tvDef(p,q)·log|V| +
    (1+tvDef(p,q))·h₂(tvDef(p,q)/(1+tvDef(p,q)))`.

## Hagi/Unified/InterpretiveGrowth.lean

- `pointEffect` и `causalEffect` неотрицательны; нулевое изменение выхода
  на всём выбранном наборе даёт нулевой эффект, а существование точки с
  положительным эффектом делает средний эффект положительным.
- `mass_split`: для неотрицательных весов сумма живой и пассивной массы
  равна полной массе.
- `passive_starves`: при `alpha > 0`, `gMax ≥ 0`, `wLive ≥ 0`,
  `G t ≤ gMax·wLive` и `alpha·C t ≤ G t` получается
  `C t ≤ gMax·wLive/alpha`; это оценка в заданной модели прироста.

## Hagi/Legacy/LearningKernel.lean

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

## Hagi/Legacy/LinkedWitness.lean

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

## Hagi/Unified/LogitGrowth.lean

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

## Hagi/Legacy/MasterHAGI.lean

- `MasterHAGI`: при `lam ≥ 0`, `nu > 0`, `epsQ ≥ 0`, `CorePremises`,
  SafeQP-окнах, суммировании доменных рисков,
  условии `lam·riskSpend + nu·epsQ ≤ decrease`, достаточном бюджете,
  неотрицательном риске, нижней энергии и заданных производственных законах
  роста получается `CertifiedHAGIInvariant`. Производственные предпосылки
  включают `C(t+1)=C t+G t`, `γD t ≤ G t`, динамику `D`
  и верхний темп `(1+alpha)` с β-порогом.
- `MasterHAGI_linked`: при дополнительной связи `C t = capability(S t)`
  и тех же остальных условиях экспоненциальная нижняя граница утверждается
  уже о фактической capability состояния.
- `certifiedHAGI_nonvacuous_strict`: при `alpha,c0,delta,s > 0` и `e ≥ 0`
  существует траектория с одновременным ростом, убыванием потенциала,
  риском и ненулевыми расходами, удовлетворяющая инварианту.

- C218 (unprefixed empirical premise registry, аудит P0b, tooling-only):
  в `AssumptionScan.py` добавлен реестр UNPREFIXED_EMPIRICAL —
  per-file подсчёт binder-сайтов признанных эмпирических посылок
  без h_emp_-префикса: MasterHAGI.lean — h_step=3, h_gain_prod=3,
  h_dyn=2, h_C_cap=2, hβ=2 (docstring 84–92); ModeState.lean —
  h_C_cap=2, hβ_eased=2. Проверка unprefixed_check() сравнивает
  фактическое число binder-сайтов `(NAME :` в comment-stripped
  источнике с зарегистрированным: любое отклонение FAIL; рост
  запрещён outright, сжатие требует сознательного обновления
  реестра через план-ревью (shrink-only политика). Реестр — НЕ
  name-registry: имена вроде hbeta имеют ~60 структурных binder-сайтов
  в других файлах репозитория, поэтому кросс-файловое сравнение
  по имени ложно регистрировало бы структурные гипотезы как
  эмпирические (задокументированная слепота: пер-файловость).
  assumptions.lock расширен секцией (+4 строки, только новая
  секция); TestAssumptionScan.py +4 теста (baseline, shrink,
  growth, missing file) — 9/9 OK.
- Evidence (cycle C218): полный CI rc=0
  (.tmp/C218/final-ci/ci.log SHA-256
  23cdf320b8877e7396612682ab6fdcdfc9677257c65b1c640ff85960a9b96ff6,
  1×CI: PASS, 1×ALLAXIOMS: PASS); AssumptionScan PASS на текущем
  дереве; plan GO
  .tmp/C218/reviews/plan-review-final.md SHA-256
  784533e355b6eb3023f7e771b86cd5e24b5afd77fbb8a6abb049ebc14db7b134.

Заявление — расширение аудиторского инструментария (реестр
непрефиксованных эмпирических посылок); не утверждаются новые
математические результаты, wall-clock, сжатие весов или
улучшение качества.

## Hagi/Legacy/MasterHAGICoupled.lean

- `CoupledHAGIInvariant` связывает канал capability непосредственно с
  состояниями и содержит отдельные неотрицательные spend/risk,
  векторный probe-floor и бюджетную бухгалтерию.
- `budget_no_growth`: из `B T = B0−Σspend` и `spend t ≥ 0`
  следует `B T ≤ B0`.
- `qvec_floor_implies_scalar`: при `w i ≥ 0` покомпонентный floor влечёт
  `Σw i·qfloor i ≤ Σw i·qvec T i`.
- `certified_family_linked_progress`: при сертифицированных переходах,
  неотрицательных рисках/затратах, нижнем бюджете и отдельных growth,
  qvec, energy-telescope условиях получается усиленный инвариант, у которого
  для каждого `t < T` `0 < verify(S(t+1)).decrease` и
  `∑_{t<T} verify(S(t+1)).decrease ≤ energy(S0) − energy(ST)`.

## Hagi/Legacy/MasterHAGITrunc.lean

- `MasterHAGI_trunc`: формулировка `MasterHAGI` требует посылки роста только
  для `t < T`, сохраняя SafeQP, `CorePremises`, net-cover, риск, бюджет,
  энергетический floor и probe-ограничения. Условие отдельного capability
  ceiling в заключение не входит.
- `masterhagi_growth_witness`: при `C t=G t=D t=2^t`,
  `alpha=gamma=1`, `rho=0`, `beta=2`, `xi=0` все усечённые посылки верны
  для `T ≤ 6`.
- `cone_premises_force_exact`: при `gamma > 0` одновременные cone,
  `γD≤G`, `C'=C+G` и `C'≤(1+alpha)C` дают точное
  `C'=(1+alpha)C`; это свойство этих посылок, а не более общий вывод роста.

## Hagi/Unified/MemoryCycle.lean

- `descentFold_eq_effective`: для истории пар `(v,x)` плотная свёртка
  `W₀+Σ outerProd(v,x)` точно равна эффективным весам представления
  `fromHistory W₀ hist`.
- `history_storage_cost`: число сохраняемых элементов блоков равно
  `hist.length·(|m|+|n|)`.
- `admission_margin_sound`: если `|gtrue−gain| ≤ ε_cert` и запись допущена,
  то `lamM·Δcost + lamR·Δrisk ≤ gtrue`.
- `consolidation_quality_bound`: при блочных ошибках Frobenius-квадрата
  `≤ εᵢ` и `L`-липшицевой функции потерь `|loss(old)−loss(new)| ≤ L√(k·Σεᵢ)`.

## Hagi/Unified/MemorySemantics.lean

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

## Hagi/Unified/ModelComparison.lean

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

## Hagi/Unified/NernstFannes.lean

- `nernst_fannes`: если `p` нормировано и масса вне `v*` равна `t`,
  то `H(p) ≤ t·log|V| + (1+t)·h₂(t/(1+t))`;
  `tvHalf_dirac_eq` уточняет, что `t` есть TV-полурасстояние до дельта-меры.
- `gibbs_nernst`: при `T > 0` и энергетическом зазоре
  `E vstar+δ ≤ E v` для всех `v ≠ vstar` энтропия гиббсова распределения
  ограничена выражением
  `̂t·log|V| + (1+̂t)·log 2`, где `̂t=(|V|−1)e^{−δ/T}`.

## Hagi/Unified/OptimalConfig.lean

- `cfg_rate`: при `rho > 0` `√cfgBeta(rho) = rho`;
  `cfg_stability` при `0 < rho < 1` даёт `0 ≤ cfgBeta < 1`,
  `0 < cfgEta ≤ 1−cfgBeta`.
- `cfg_descent`: на `TaskState k 1`, `0 < rho < 1` и ненулевой сумме
  квадратов градиента шаг `cfgEta rho` строго уменьшает энергию;
  это одношаговый результат заданной модели.
- `cfg_bits`: если `eps > 0`, `m·r ≤ (2eps)²` и все поэлементные ошибки
  `|QR−R| ≤ 1/2`, выходная норма квантованного возмущения не превосходит
  `eps·‖x‖`.

## Hagi/Unified/ParetoExecution.lean

- `selection_pareto`: внутри конечного множества допустимых действий
  никакой кандидат не может иметь качество не ниже выбранного и одновременно
  не большие память и operations, если хотя бы одно из трёх сравнений строго.
  При всех трёх нестрогих улучшениях все три величины равны.
- Выбор рассматривает фактический преемник `step a s` и лексикографическую
  цель `(value,−memory,−operations)` при заданном непустом допустимом
  семействе. Глобальная или аппаратная оптимальность не утверждается.

## Hagi/Unified/ParetoLogit.lean

- `logit_budget_loop`: для рекуррентности
  `w(t+1)=w t+eta t/(1+exp(w t))`, `0 < eta t ≤ 2`,
  `b(t+1)=b t−eta t`, `0 ≤ eta t ≤ b t` и `0 ≤ b0`
  сохраняются качественные floors на всём пути, телескоп CE-спусков,
  неотрицательный и ограниченный бюджет; при `n ≥ 1` CE строго убывает.
- `logit_quadratic_bound`: при тех же рекуррентности и окне шагов
  `logitCE(w n) ≤ logitCE(w0) −
    Σ_{t<n}eta t·(1/(1+exp(w t)))²/2`.

## Hagi/Unified/ProductiveTransition.lean

- `idle_not_productive`: при `δC,δL > 0` переход `S → S`
  не удовлетворяет предикату `Productive`.
- `ctv3_idle_contra`: `CertifiedTransitionV3` несовместим с равенством
  энергии до и после перехода; `productive_of_ctv3` получает `Productive`
  при фактическом спаде не меньше `δL > 0`.

## Hagi/Unified/QuadMachine.lean

- `quadE_eq_energy` и `quadGrad_eq_grad`: квадратичная энергия и градиент
  вычислительной машины совпадают с соответствующими определениями
  `DescentCoreQuad`.
- `machine_one_step_zero`: на этой модели шаг с `eta=1` обнуляет энергию.
- `trajDropBound`: сумма фактических разностей энергии по gate-траектории
  не превосходит начальной энергии; `commitCountBound` даёт
  `commitCount ≤ T`.

## Hagi/Unified/QualityResourceMin.lean

- `minimumResource_next_quality_ge`: при непустом `qualityEligible`
  фактический преемник выбора удовлетворяет `qfloor ≤ value`.
- `minimumResource_cost_min`: ни один элемент того же конечного
  `qualityEligible` не имеет меньшей `(memory,operations)`-стоимости
  в memory-first порядке.
- `minimumResource_safe`: выбранное действие сохраняет исходный model-safe
  предикат; это не физическая гарантия и не минимум вне заданного семейства.

## Hagi/Unified/QuantSafeUpdate.lean

- `quantized_safe_window`: при `L i,eps i,eta ≥ 0`, идеальном окне,
  `‖δ‖ ≤ q` и линейной оценке возмущённого шага получается
  `dL i ≤ eps i + eta‖g i‖q + L i·eta²(‖d‖q+q²/2)` для всех `i`.
- `quantized_step_bound` доказывает использованную верхнюю оценку через
  `‖δ‖` без предположения, что `q` получена из конкретного квантователя.

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

## Hagi/Legacy/RecursiveGrowth.lean

- `macro_step_decrease`: при merge-выигрыше `G ≥ 0`, `0 < L`,
  `0 ≤ eta ≤ 1/L`, `dnorm² ≤ inner`, квадратичной joint-оценке,
  `κ,s,dnormq ≥ 0`, `dnormq ≤ 1/2` и compress-Lipschitz оценке
  получается `E4 ≤ Emean − (G + eta·dnorm²/2 − κs/2)`.
- `safeqp_eps_critical`: при нижней энергии Emin,
  `E(t+1) ≤ E t−eta t·dn t²/2`, `etamin > 0`,
  `eta t ≥ etamin`, `eps > 0` и `dn t² ≥ eps²`
  горизонт удовлетворяет `n ≤ 2(E0−Emin)/(etamin·eps²)`.
- C217 (legacy quarantine, аудит P0a): модуль перенесён без
  изменения байтов из Hagi/Unified/RecursiveGrowth.lean в
  Hagi/Legacy/RecursiveGrowth.lean (SHA-256
  ef6907ef5ce1c44f4b85c308148860acf799326f2ce165de15e1d56e0d6933b0,
  14644 байт / 347 строк / 0 CR) и выведен из корневого
  import-замыкания: Hagi.lean больше не импортирует его; новый
  umbrella-модуль Hagi/Legacy.lean и отдельная lean_lib
  Hagi.Legacy (defaultTargets += Hagi.Legacy) сохраняют
  собираемость и CI-покрытие. Утверждения `macro_step_decrease`
  и `safeqp_eps_critical` сохранены дословно: это карантинный
  рефакторинг, а не новое доказательство.
- Освобождения точечные, кодового уровня: ReachLint исключает
  только модули Hagi/Legacy/** плюс umbrella Hagi.Legacy
  (временный недостижимый не-Legacy файл всё ещё даёт FAIL,
  rc=1 — отрицательная проба воспроизведена); NsLint исключает
  только префикс Hagi/Legacy/ и файл Hagi/Legacy.lean, baseline
  не тронут; ClosureReport переименован только путь записи;
  assumptions.lock — path-only move секции (+1/−1, тот же список
  h_emp_-посылок). Все гейты для не-Legacy кода остаются
  строгими.
- Census (fresh, .tmp/C217/validation/root-census.tsv SHA-256
  0e08fa29c070902eeb06f80d257165908e22adc17313ab4184e2ec3dd66771eb):
  OWNER 12308 → 12284, ровно −24 = строки модуля
  Hagi.Unified.RecursiveGrowth, теперь 0; NamePool −24 / +0;
  модули 500 → 499; fingerprint
  11502919156674973306 → 6171893465292583947.
- Evidence (cycle C217): lake build Hagi Hagi.Legacy rc=0; полный
  CI rc=0 (.tmp/C217/final-ci/ci2.log SHA-256
  41a88367222fe38f1aefb4ee01e8c1b58edb6708cdac33f1448daa0e01bc3519,
  1×CI: PASS, 1×ALLAXIOMS: PASS); Freeze NO-OP (declarations.lock
  не изменён, SHA-256
  1af9d36899cb8420eafe38b5634c9bcda4f0a7d4f6120a7de666b2e90b222621
  до и после); plan GO
  .tmp/C217/reviews/plan-review-final.md SHA-256
  ac334c9d0107225c21941e4a145bce790cbc2b62592e52c83ca7d482b4d0ec24.

Заявление — перенос и карантин модуля без изменения
доказательств; не утверждаются новые математические результаты,
wall-clock, сжатие весов или улучшение качества.

## Hagi/Unified/RobustCostSensitivity.lean

- `robustEligible_mono_epsilon`: при `eps1 ≤ eps2` всякий допустимый
  в большем радиусе кандидат допустим и в меньшем.
- `robustMinimumResource_cost_mono`: если заданы witnesses для обоих
  непустых классов, минимальная memory-first стоимость при `ε₁`
  не превосходит стоимости при `ε₂`.
- `robustMinimumResource_memory_mono` отдельно даёт ту же неубываемость
  только для памяти; монотонность operations из неё не утверждается.

## Hagi/Unified/RobustRadius.lean

- `robust_eligible_iff_radius_le_margin`: для конечного контроллера
  с допустимым stay существование floor-certified кандидата равносильно
  `eps ≤ estimatedMaxValue − qfloor`, включая равенство.
- `no_robust_eligible_above_margin`: при большем `eps`
  ни один кандидат не проходит эту проверку; `estimatedMaxValue_upper`
  показывает, что максимум берётся по оценкам фактических преемников.

## Hagi/Unified/RobustResourceMin.lean

- `robustMinimumResource_actual_quality_ge`: если оценка всех фактических
  преемников отличается от ценности не более чем на `eps`, выбор удовлетворяет
  истинному qfloor.
- `robustMinimumResource_cost_min`: выбор минимален только среди кандидатов,
  для которых одновременно `qualityEligible` при пороге `qfloor+eps`;
  истинно допустимый, но не сертифицированный кандидат не сравнивается.
- `robustMinimumResource_zero_exact`: при точном estimate и `eps=0`
  конструкция совпадает с обычным `minimumResource`.

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

## Hagi/Legacy/StateTakeoff.lean

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

## Hagi/Legacy/TernaryGrad.lean

- `quantized_net_gain`: из `gamma·D ≤ Graw` и `Graw−G ≤ p`
  следует `gamma·D−p ≤ G`.
- `quantized_cone_gain`: при `kC ≤ D`, `gamma ≥ 0`,
  `gamma·D ≤ Graw`, `Graw−G ≤ p` и margin
  `p ≤ gamma(D−kC)` доказывается `gamma·k·C ≤ G`.
- `sgn1_grid_fix`: решётка шага `1` фиксирует знаковые значения.
  `tern_grad_inner` даёт точное `Σᵢ gridQ 1(sign gᵢ)·gᵢ = Σᵢ|gᵢ|`,
  без второй ошибки квантования.

## Hagi/Unified/TernaryProbe.lean

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

## Hagi/Unified/TernaryWitness.lean

- `quantOpt_energy_bound`: при `s > 0` и `ternInRange s (a i)`
  для всех `i` энергия `quadE a (quantOpt s a)` не превосходит
  `|k|·s²/8`.
- `quant_jump_honest`: если исходная энергия строго больше этого потолка,
  переход к `quantOpt` имеет положительный фактический drop при нулевых
  риске и расходе. `ternaryStepCert` упаковывает тот же переход в `StepCert`.

## Hagi/Legacy/TopLevel.lean

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

## Hagi/Unified/TwoDomainConfidence.lean

- `finite_family_two_domain_guarded_improvement`: на конечном product-law
  для `[0,1]`-targets, `n,eps_old,eps_target > 0`,
  при вероятности общей старой ошибки не менее `1−δ`,
  `2|A|exp(−2n·eps_target²) ≤ δ` и наблюдаемом margin
  `> 2eps_target` для каждого допустимого представителя guard
  с вероятностью не менее `1−2δ` одновременно выполняются:
  фактическое качество не ниже stay, выбран допустимый представитель,
  а population-loss строго меньше у него, чем у stay.
- Результат относится к фиксированному семейству и заданному product-law;
  наблюдаемый margin остаётся посылкой, селектор не использует target
  при выборе действия.

## Hagi/Unified/VerticalCapstone.lean

- `accuracy_for_budget`: при `0 ≤ q < 1`, `σ ≥ 0`, `B0 > 0`,
  `c > 1`, `Estar ≥ 0` и
  `e(s+1) ≤ q·e s + σ²/(B0·c^s)` получается
  `e t ≤ Estar + q^t(e0−Estar) + σ²/(B0(1−q))`.
  Постоянный шумовой член — консервативная граница данной рекуррентности.
