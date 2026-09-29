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

## Счётчик

- Нетривиальных теорем-якорей в `Plan41`: 7
- Тавтологий в реестре: 13 (1 заменено, 12 — кандидаты)
- «0 sorry» по всей `Hagi/`: сохраняется
