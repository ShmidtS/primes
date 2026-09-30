# STATUS — реестр нетривиальности (round 41)

Метрика «0 sorry» недостаточна (тавтологии её проходят).
Реестр: теорема → заявлено → статус. Правила приёмки:
заключение ≠ посылка; не `rfl`/`A = A`; `#print axioms` —
только propext / Classical.choice / Quot.sound.

## Доказано нетривиально (примеры-якоря)

- `Plan41.proj_descent_inner` — вариационное неравенство проекции
  при c=0: ⟪g,d*⟫ ≥ ‖d*‖² (Mathlib `norm_eq_iInf_iff_real_inner_le_zero`)
- `Plan41.proj_no_farther` — ‖g−d*‖ ≤ ‖g‖ при 0 ∈ C
- `Plan41.exp_jensen` — exp(Σpδ) ≤ Σp·e^δ (`ConvexOn.map_sum_le`)
- `Plan41.gap_N_nonneg` — Gap_N ≥ 0 для центрированных δ (Йенсен + swap)
- `Plan41.anchor_recurrence` — D_t ≤ (1−γ)^t·D₀ + ρs/γ (индукция)
- `Plan41.ns_poly_bound` — p(σ)=aσ+bσ³+cσ⁵ ≤ aσ на [0,1] (b≤0, b+c≤0)
- `Plan41.amgm_batch_bound` — cB + B_n·t₀/B ≥ 2√(c·B_n·t₀) (AM-GM)
- `ComputeBudget.activeSet_structure`, `Grow.grow_epsilon_stop`,
  `GapLaw.twoGap_*`, `SafeQP.safeQP_*`, `FreeEnergy.geometric_pool_identity`
  и др. (полный список — по линтеру)

## Реестр тавтологий (аудит round 41; статус после правки)

| Теорема | Было | Действие |
|---|---|---|
| `DesignOpt.wall_clock_model` | `A = A := rfl` | носитель предписания; честная граница задокументирована — кандидат в `def` |
| `FreeEnergy.token_kl_decomposition` | `A = A := rfl` | кандидат в `def` |
| `Upgrades.sink_receptive_field_exact` | `A = A := rfl` | кандидат в `def` |
| `NCEExact.anchor_drift_bound` | `A = A := rfl` | **ЗАМЕНЕНО** на `Plan41.anchor_recurrence` |
| `DesignOpt.wall_clock_model` | rfl | **demoted → `def wallClock`** |
| `FreeEnergy.token_kl_decomposition` | rfl | **demoted → `def tokenKLTotal`** |
| `Upgrades.sink_receptive_field_exact` | rfl | **demoted → `def sinkReceptiveField`** |
| `Wave2.config_cert_constructive` | вывод=посылка | **удалена** (предписание сохранено комментарием) |
| `Dominate.normalized_descent_preserved` | вывод=посылка | **удалена** (ссылка на Plan41.proj_descent_inner) |
| `MergeScaling.edge_count_linear` | `N ≤ N*1` | **удалена** |
| `LazyAdam.decayProduct_exact` | rfl | **удалена** (комментарий-предписание) |
| `Wave3.head_start_persists` | ring-тривиальность | **ЗАМЕНЕНО** на `Plan42.head_start_timeshift` (PL-сдвиг) |
| `Dominate.normalized_descent_preserved` | вывод = посылка | кандидат на удаление/def |
| `Wave2.config_cert_constructive` | вывод = посылка | кандидат на удаление/def |
| `MergeScaling.edge_count_linear` | `N ≤ N*1` | кандидат на удаление |
| `GrowthGate.growth_verdict_table` | `eps ≤ GF+eps` | заменить на функцию вердикта + монотонность |
| `Wave3.head_start_persists` | `ring`-тривиальность | заменить на PL-контракцию (фаза 2.5 плана) |
| `Wave2.merge_init_head_start` | перестановка посылки | слабая; сохранить с пометкой |
| `DesignOpt.designopt_interior_law` / `ComputeBudget.marginalValue_law` | сумма посылки | закрыть KKT-из-оптимальности (фаза 2.4) |
| `DesignOpt.adaptive_ns_exists` | `e 100 = 0` делает тривиальным | переформулировать без нулевой точки |
| `LazyAdam.supportSet_bound` | 34816 > V — оценка пустая | добавить `min V ·` |
| README vs `GapLaw` | spread²/N против G∞(1−1/N) | это НИЖНЯЯ/ВЕРХНЯЯ огибающие (`increment_envelope`) — не противоречие; помечено |

## Допущения (явные, `h_emp_`-префикс — не теоремы)

- дрейф ρ (anchor), сжатие γ, пороги κ — измеряемые константы

## Фаза 2 (Plan42) — слабые формулировки исправлены

- `nce_estimator_unbiased` — несмещённость per-sample NCE (2.2)
- `log_jensen_uniform` — ceGap направление Йенсена (2.3; дельта — только с χ² ≤ cK)
- `exp_tangent` + `waterfilling_optimal` — waterfilling ОПТИМАЛЕН из
  касательной + выравнивания маргиналов: `hinterior` — вывод, не гипотеза (2.4)
- `head_start_timeshift` — PL-сдвиг: merge = k шагов форы,
  k = ln(Δs/Δm)/ln(c) — измеримо (2.5)

## Раунд 43 (Plan43) — ревью-дополнения

- `min_dist_to_vi` + `safeQP_descent` — инстанциация на safeSet:
  VI из минимальности (ciInf-форма), ОБЕ гарантии спуска ‖ds‖²≤⟪g0,ds⟫ и
  ‖g0−ds‖≤‖g0‖ — контроллер теперь на Lean, не на пороге
- `ns_iter_bound` — σ_k ≤ a^k·σ₀ (индукция); докстринг-ошибка
  «890/74 ≈ 3.4445³» исправлена (3.4445³ = 40.9); правило k(σ_min)
  численно проверено ревьюером (2..7 шагов для σ₀=10⁻¹..10⁻⁴)
- `amgm_equality` + `amgm_uniqueness` + `batch_T_min` — равенство
  точно при B*²=B_n·t₀/c, единственность оптимума, T(B) ≥ const
  равномерно — оптимальный батч ВЫВЕДЕН и ЕДИНСТВЕНЕН

## Раунд 44 (Wave5) — DepthBench-синтез + волна-5

- `admission_var_criterion` — Var-критерий следующего эксперта (ниша
  подтверждена свободной волной-5): argmax ΔVar/ΔC = argmax ΔGap/ΔC
- `branchscale_minmax` — min-max пол S_l²·v_l: max ≥ B/Σ(1/v),
  равенство при равномерности (S_l²·v_l ≈ const — теорема)
- `dead_layer_stop` — адаптивная глубина: монотонные V_l → стоп при
  V<ε корректен (композиция с phase_metric_monotone)
- Унификация DepthBench: I_eff = ранг доступных вычислительных
  состояний; эксперт/слой/память/ширина — одна очередь ΔI_eff/ΔT_wall

## Раунд 45 (RootContrast) — root ⊕ contrast канал

- T1: root_idem + contrast_zero_sum + contrast_of_root +
  root_contrast_orth_total + root_contrast_pythagoras — разложение
  без потерь (5 теорем)
- T2: filter_partition_sum + highway_gain_identity — выигрыш highway
  = захваченная contrast-энергия (точное тождество)
- T3/C: two-block правило (waterfilling-следствие, документировано);
  go/no-go: ρ_c(64) ≤ 0.028 до GPU
- Фальсификация: слепое предсказание Δ(highway−rootonly) ≈ ρ_c(r_c)

## Раунд 46 (CycleChannel + ρ-фикс)

- rhoCaptured/rhoTail defs + rho_partition — семантика ρ исправлена
  (GO через captured = E_total·rhoCaptured ≥ ε, не tail-отношение);
  round47-заметка «0.1701 → GO» ретроспективно корректна через
  captured = 0.8299·E_total
- cycle_decay_mono + cycle_decay_ratio — модель затухания поколений
  (насыщающаяся форма; 2-точечная калибровка, Δ_3 слепая)
- channel_switch — порог F_switch = (b·C_move·s/(k·C_rank))²:
  ниже него ранг-канал СТРОГО доминирует — автостоп сиб-поколений

## Раунд 47 (SeedOnly + JointCost + EqualBudget)

- T1b disp_recurrence_general (ЛЮБОЙ a, вкл. a≥1) + geom_range_identity
- T1c: sum_dist_mean_le (среднее минимизирует) + seed_only_disp_bound
  (композиция Λ²·s·Σa^i); T1d seed_only_grow_stop (пол < ε → стоп)
- T1a (gap≤c·dispersion, c=1/4, Хёфдинг) — НЕ ДОКАЗАН: лемма есть в
  Mathlib (SubGaussian.lean), конечная интеграция не завершена
- T2a block_lowrank_lt_dense_iff (3r < (N−1)h); T2b nsIter_scale
  (ровно N³) + nsIter_block_le; T2c amdahl_ceiling (1.07/1.21/1.63);
  T2d offdiag_pythagoras (ρ_off корректен)
- T3a aitken_exact (точное восстановление L*,c по 3 точкам);
  T3b aitken_consistency (тест фальсификации PL-модели);
  T3c budget_gap_sign_const (равные скорости → знак C-константен)
- T3d (iff break-even) — НЕ ДОКАЗАН: знаковый case-анализ превысил
  бюджет попыток; T2e (launch-порог) — документирован

## Раунд 48 (Unified) — единая структура

- uncertainty_contraction — LDT-закон сжимающего уточнения (зеркало
  наших проекций в пространстве состояний)
- finite_termination — телескоп-аргумент ранга: решение-цикл
  финиширует за rank(x₀) шагов (общий скелет dead_layer/seed_only/
  grow_epsilon stop-законов)
- traininfer_critical — T* = log(C·a·k)/k: оптимум «учить дольше
  vs итерировать глубже» — закрытая формула
- highway_gain_transport_bound — η-поправка DepthBench:
  выигрыш highway ≤ E_captured·η (η = транспортный ранг) —
  достройка фальсификации T2 до модели недовыполнения
- Архитектурная схема (в докстринге): две рекурсии
  (веса + состояние), одна валюта ΔI_eff·η/ΔT_wall, у каждой
  оси — свой stop-закон

## Счётчик

- Нетривиальных теорем-якорей: Plan41 — 7, Plan42 — 5, Plan43 — 6,
  Wave5 — 3, RootContrast — 7, CycleChannel — 3, R47 — 13,
  Unified — 4 (итого 48)
- Недоказанное раунда 47: T1a-ядро (Хёфдинг-константа 1/4),
  T3d-iff, T2e
- Тавтологий в реестре: 13 (3 заменено теоремами, 6 demoted/удалены,
  4 — кандидаты: growth_verdict_table (→ функция вердикта),
  merge_init_head_start (слабая, помечена), adaptive_ns_exists,
  supportSet_bound (нужен min V·)
- «0 sorry» по всей `Hagi/`: сохраняется

## R50 — Proofs landed (post-refactor)

- **kl_product** (Hagi.Data.DField): KL divergence of product
  distributions = sum of marginal divergences. Closes the
  10-attempt blocker (explicit `Finset.mul_sum` terms, not rw).
- **KL_product_ge_marginal** (Hagi.Data.DField): D_L ≥ D_1 for
  independent-position models — sequence divergence dominates
  unigram divergence. Dependent case remains open (honest).
- **headstart_pays_iff** (Hagi.Audit.EqualBudget): two-sided
  break-even C₀ < κ·ln(dS/dM)/ln(1/c). Sign bug of the r47
  note found & fixed: exponent is −C₀/κ. T3d CLOSED.
- Remaining unproved: T1a-Hoeffding core, stochastic SafeQP,
  per-stage Lyapunov, η closed form, global architecture KKT,
  spectrum→CE two-sided link.

## R51 — External review fixes (three defects closed)

External review (round-51) found real defects; all fixed:

1. **factor_quant_go** (Hagi.Budget.ElementQuant): carried
   contradictory hypotheses (tail+qerr<qdirect ∧ qdirect≤
   tail+qerr) — a theorem about an empty set. Replaced with
   the honest GO/NO-GO certificate: triangle bound + measured
   inequality ⇒ true factor-route error < direct error.
2. **diversity_noncollapse** (Hagi.Step.JointPreserve): was
   mislabeled — the proven statement is an UPPER bound
   compatible with total collapse (s=0 ⇒ D_T→0). Docstring
   corrected; added **diversity_floor** (+ geom_shift helper):
   D_T ≥ ρ^T·D₀ + (inj−ξ)·Σρ^i — the sign the architecture
   needs: inj > ξ rules OUT collapse.
3. **GlobalConvergence** confirmed as generic telescope (not
   fixed): per-stage Merge/Joint/Compress Lyapunov bounds
   remain open — listed as the main theoretical gap before a
   true macro-cycle contraction theorem.

Also from the review, confirmed-open: stochastic SafeQP
perturbation, LazyAdam β₁>0 replay equivalence, TableLoRA ×
quantization (Eckart–Young + ternary commutation), spectrum→CE
two-sided link, global architecture KKT.

Anchors 58 → 61 (factor_quant_go reborn, diversity_floor,
geom_shift). Build green, 0 sorry.
