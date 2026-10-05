# STATUS — текущее состояние формализации HAGI

Метрика «0 sorry» недостаточна (тавтологии её проходят).
Правила приёмки: заключение ≠ посылка; не `rfl`/`A = A`;
`#print axioms` — только propext / Classical.choice /
Quot.sound; эмпирические посылки — префикс `h_emp_`.

Историческая ретроспектива раундов R41–R166 удалена
(см. git log / docstrings модулей); здесь — только текущее
описание корпуса.

## Корпус

- 162 Lean-модулей в 24 папках `Hagi/`, 841 theorem/lemma,
  0 sorry; `lake build` — зелёный (9081 jobs).
- CI (`scripts/ci.sh`): TrivialLint + тривиальность +
  DocLint + LayerLint + StatusLint — PASS.
- Аксиомы: стандартные (проверено выборочно по капстоунам).

## Слоистая архитектура (миграция 2026-10-05)

- `Foundations/` (L0, только Mathlib): `Recurrence`
  (`recurrence_upper`, `recurrence_pure`, `recurrence_lower`,
  `geom_telescope`, `geom_sum_le_inv`, `contraction_limit`),
  `Telescope` (`telescope_le`, `telescope_sum_le`,
  `telescope_sub_sum`), `ConeTakeoff`
  (`cone_invariant_horizon`, `takeoff_from_cone`), `Chord`
  (`exp_chord_ab`, `log_cosh_le`), `Hoeffding`
  (`bern_mgf_bound`, `mgf_hoeffding_ab`, `mgf_hoeffding`),
  `TakeoffCounted` (`capability_takeoff_counted`).
- Правило LayerLint: импорт только из строго нижних слоёв;
  same-folder DAG допустим; baseline-исключений — 23
  (сокращающийся список в `scripts/LayerLint.py`).
- Дедупликация: MasterHAGI-телескопы, Saturation
  (`pl_gap_geometric`), Dynamics/Contraction — делегации
  Foundations.

## Вероятностный слой (Probability/)

- `AdaptiveSuccess` (конечные вероятностные системы:
  `prodE`, `prodPq`, `markov_ge`), `CertifiedEstimator`,
  `ConditionalSuccess`.
- `Azuma`: мартингальная концентрация
  (`hoeffding_lemma_prefix`, `azuma_mgf`, `azuma_tail_low`,
  `adaptive_success_azuma`).
- `Freedman` (R167): дисперсионно-адаптивная концентрация —
  `exp_tail_two` (двойной MVT), `freedman_lemma_prefix`,
  `freedman_mgf`, `freedman_tail_low`,
  P[ΣX ≤ −Δ] ≤ exp(−Δ²/(2(nσ²+bΔ))), `cond_var_le_second`,
  `adaptive_success_freedman` (σ²=1 воспроизводит Азуму,
  σ²<1 — сильнее).

## Growth-каскад и капстоуны

- Growth: `RatioTakeoff`, `FrontierScaling`
  (`frontier_cone_invariant`), `GainRenewal`
  (`gain_renewal_recurrence`), `Saturation`
  (`pl_gap_geometric`, `saturation_limit`), `GrowthCeiling`
  (`growth_dichotomy`), `TakeoffElasticity`
  (`elasticity_chain`), `PlasticityLedger` (`kl_le_log_card`),
  `RsiCriterion` (`rsi_cone_criterion`), `SeedOnly`,
  `StateBinding`, `StateClosedRenewal`.
- Unified: `MasterHAGI` (условный капстоун, телескопы через
  Foundations), `MasterHAGITrunc`
  (`MasterHAGI_trunc`, `masterhagi_growth_witness` —
  свидетель не-вакуозности), `ArchitectureTheorem`
  (`cone_invariant_trunc`, `pl_gap_lower_trunc`),
  `GrowthState`, `TopLevel`, `AnytimeValid`.
- Model: `SoftmaxStep` (`descent_step` — гарантированный
  спуск CE конкретной модели без `h_emp_`-посылок).
- Budget: `CertifiedArgmax` (`argmax_pair_certified`,
  `tie_ambiguity` — контрпример противоречивости argmax при
  малых зазорах), `ComputeBudget`, `JointCost`.
- Probability→Growth мосты: `WallClockTakeoff`,
  `GrowthBridge`, `Liveness`.

## Честные границы (открытое)

- `h_emp_`-посылки (измеряемые, не теоремы): дрейф ρ,
  сжатие γ, условные дисперсии σ², условные полы успехов —
  проверяются runtime-измерением, не выводимы.
- γ-дефицит mixer.gain→0 (9×) — НЕ закрыт (честный
  статус R160).
- Полная Fannes-граница (остаток R157 после `binEnt_mono`
  клона) — открыта; pinsker-часть доказана.
- Freedman: совместная (M ≥ x И V ≤ v) и anytime-формы —
  открыты.
- Eckart–Young в Mathlib отсутствует — спектральный хвост
  R132 уровня 2 не переносится.
- R158 Lean↔Runtime property-тесты — требует torch-рантайма
  E:\HAGI_v2 (blocked).
- §I LSL-стек (SupportGate/GateRetention/LocalSafeQP/
  Consolidation) — нет спецификации §I (blocked).
- Covariance-Projected Gain Operator — после gen7-вердикта.
- `frontier_cone_invariant` — структурно отличен от
  Foundations-конуса (ξ-член, cap вместо равенства шага);
  канонизация — будущая работа.

## Миграция — оставшиеся шаги

- Разворот 23 baseline-рёбер LayerLint (в основном
  Unified-хабы GrowthState/TopLevel, Growth↔Budget) —
  требует шага «мосты»: capability-семантика через KL/CE,
  GrowthState ← DField/Merge.
- git mv папок по слоям, spec_manifest.toml, регенерация
  STATUS скриптом (шаги 4, 6, 7 плана миграции).

## Счётчик

- 841 theorem/lemma; 0 sorry; LayerLint baseline: 23;
  Foundations: 7 модулей L0. CI: PASS.
