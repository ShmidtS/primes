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

## Счётчик

- Нетривиальных теорем-якорей: Plan41 — 7, Plan42 — 5, Plan43 — 6,
  Wave5 — 3, RootContrast — 7 (+rho_partition), CycleChannel — 3
  (итого 32)
- Тавтологий в реестре: 13 (3 заменено теоремами, 6 demoted/удалены,
  4 — кандидаты: growth_verdict_table (→ функция вердикта),
  merge_init_head_start (слабая, помечена), adaptive_ns_exists,
  supportSet_bound (нужен min V·)
- «0 sorry» по всей `Hagi/`: сохраняется
