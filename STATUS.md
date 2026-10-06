# STATUS — текущее состояние формализации HAGI

Метрика «0 sorry» недостаточна (тавтологии её проходят).
Правила приёмки: заключение ≠ посылка; не `rfl`/`A = A`;
`#print axioms` — только propext / Classical.choice /
Quot.sound; эмпирические посылки — префикс `h_emp_`.

Историческая ретроспектива раундов R41–R166 удалена
(см. git log / docstrings модулей); здесь — только текущее
описание корпуса.

## Корпус

- 174 Lean-модулей в 24 папках `Hagi/`, 887 theorem/lemma,
  0 sorry; `lake build` — зелёный (9094 jobs).
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

- 900 theorem/lemma; 0 sorry; LayerLint baseline: 23;
  Foundations: 7 модулей L0. CI: PASS.

## Бюджет-линия (R176, цикл 2026-10-06)

- Hagi/Budget/BitAlloc: оптимальное распределение битов при
  ограничении объёма — transfer_exact (маржинальный обмен:
  перестановка бита меняет ошибку ровно на e_k − e_j/2),
  two_layer_equalize (балансировка двух слоёв — water-
  filling как теорема), imbalance_yields_gain +
  stable_factor_two (фактор-2 инвариант на фикс-поинте
  жадного цикла), distill_quant_composite (полный
  сертификат поколения: S_n + n·g ≤ E_0 + δ_n +
  totalError). Источники: 2609.38169, 2607.16097, 2607.16600.
- Анализ цикла: формализуемые ядра темы «максимальное
  качество при минимальном объёме» в корпусе исчерпаны
  (Eckart–Young нет в Mathlib и в корпусе; width-скейлинг
  2606.28242 покрыт tail-eigenvalue формой DesignOpt;
  QAT/JL/superposition теорий нет).
- Термослой ЗАВЕРШЁН (R174a–e): IFT+второй закон (a),
  температура шума 1/B + отжиг батчем (b, R174d-ядро
  anneal_by_batch), детальный баланс ⟺ нулевая диссипация
  (c), субквадратичные хвосты → момент плоскости (e,
  StationaryFlatness: tail-sum identity + 2C-граница).
- R157-остаток ч.2 закрыт (FannesSmooth): липшиц энтропии
  на δ-интерьере симплекса, |ΔH| ≤ (2/δ+2log(1/δ))·TV;
  открыта только сингулярная h₂-граница (нулевые массы).
- Открыто: h₂-Fannes (тяжёлый порт), R158 (torch-рантайм),
  LSL (нет §I-спецификации), frontier_cone канонизация.
- Цикл 2026-10-06 (продолжение): R181 CortexFiber (законы
  энергии кортекс⊕волокна), R182 AlignedMerge (штраф за
  невыравнивание линеен по δ), R183 FiberSplit (Grow-закон:
  расщепление эксперта точно), R184 dustNoiseHalving (мост A
  ч.1: zeroth-order шум гасится популяцией), R185 DustCert
  (мост A замкнут: статистические предпосылки klsBatchNoise —
  теоремы для Dust-оценки), R186 ThermoBridge (мост C:
  носители prodE/expQ сварены; 1/B-закон один в трёх
  словарях). Мост D (биты↔спектр): арифметика покрыта
  (fiberParamCount), спектральная форма blocked (Eckart–Young
  нет в Mathlib). Мост E ЗАКРЫТ (R187 DustAlign, c43b6ef):
  cos-закон выравнивания в Markov-форме — q-масса пар с
  floor-выравниванием (1−2δ)·‖g‖·‖ĝ‖ ≤ ⟨g,ĝ⟩ не хуже
  1 − V/(δ·‖g‖)², где V — гашёная энергия ошибки
  (dustNoiseHalving); норма/CS/треугольник самодостаточны
  (absDot_le, nrmTriangle, alignLower). Общий-K
  дисперсионный закон Dust ЗАКРЫТ (R188 DustVarK, 1ea8500):
  hcVarKTotal/hcVarK — 1/K-закон для ЛЮБОГО K ≥ 1 (индукция
  по K через Fin.cons-сплит), esErrCentered — центрированность
  из esUnbiased, dustVarK — векторная форма: ожидаемая
  квадратичная ошибка K-draw усреднённой esEst-оценки ровно
  (1/K) одночной. R189 (5019aa3): prodQ/dustVarK_expQ/
  dustAlignmentK — вероятностный cos(K)-закон для ЛЮБОГО K ≥ 1:
  масса пар с floor-выравниванием ≥ 1 − (V/K)/(δ‖g‖)². Dust-цепь
  полностью замкнута: энергия 1/K (R188) + выравнивание с
  вероятностью 1−V/(K·δ²‖g‖²) (R189) — формальный аналог
  эмпирического cos(K) = c_max/√(1+c/K) для всех K.
- R177 WaterFilling (dac7e86): существование фактор-2
  сбалансированной аллокации — замыкание R176 (конечный
  argmin через Finset.min' + бюджет-сохраняющие переносы).
  Честная граница (поправлена R-аудитом): доказательство
  ЭКЗИСТЕНЦИАЛЬНО, не конструктивно; терминантность жадного
  цикла переносов НЕ формализована; OPT-аппроксимационные
  гарантии water-filling не формализуемы без структуры.
- R178 Dust ч.1–2b (c042c9c, 3b0f325, 82ab1d2; источник
  qlabs.sh/research/dust): Rademacher-гиперкуб без теории
  меры — hcFactorized (pi-фубини), hcDelta (E[u_i u_j]=δ),
  esUnbiased (ТОЧНАЯ несмещённость симметрично-разностной
  оценки на квадратичных потерях, без σ²-смещения),
  drawPairOrtho (интерференция дро исчезает в среднем),
  varianceHalving (K=2: удвоение популяции делит средний
  квадрат ошибки). Открыто: общий-K дисперсионный закон,
  cos(K)-закон выравнивания.
- R179 KLSBridge (ad9db69): Poincaré-ИНТЕРФЕЙС (константа
  arXiv:2610.01447v2 НЕ импортирована — препринт не
  верифицирован независимо): gradCovBound (Cov(g) ⪯ C·L²·I
  по направлениям), uncorrMeanVar, expQ_varEq, klsBatchNoise
  (σ² ≲ C·L²/B), klsChebyshev. Лог-вогнутость данных НЕ
  утверждается — Poincaré входит явной гипотезой.
- R180 KLSSafeQP (45eceb2): композиция R179 → SafeQP-слой:
  klsSafeQP_certified — при guard ε+|gd|·t шумный чек
  сертифицирует ε с вероятностью ≥ 1 − V/t²
  (V = C·L²·‖a‖²/B). Рецепт SafeQPRobust (margins ε+m)
  получил теоретический шумовой бюджет.
- Аудит R-цикла (94a21a5+): докстринги BitAlloc/WaterFilling
  поправлены — убраны overclaim'ы («constructive», «greedy
  loop terminates»): доказано существование, не конструкция;
  терминантность жадного цикла не формализована.
