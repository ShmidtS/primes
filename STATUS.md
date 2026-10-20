# STATUS — состояние формализации HAGI

Метрика «0 sorry» недостаточна (тавтологии её проходят).
Правила приёмки: заключение ≠ посылка; не `rfl`/`A = A`;
`#print axioms` — только propext / Classical.choice /
Quot.sound; эмпирические посылки — префикс `h_emp_`.
История раундов удалена (git log, docstrings); здесь —
текущее состояние, главные формулы и открытые задачи.

## Корпус

- 290 Lean-модулей в `Hagi/` (28 каталогов), 2683 деклараций
  в declarations.lock (Freeze, 2026-10-18), 1714
  theorem/lemma, 0 sorry; `lake build Hagi` зелёный.
- LayerLint: 0 исключений; TrivialLint T0 fail-closed
  (axiom/sorry/native_decide в любом месте → exit 1).
- Батарея: Freeze, DocLint, StatusLint, LayerLint,
  triviality_lint — PASS (`bash scripts/ci.sh`).

## Слои

```
0  Mathlib
1  Foundations/  Prelude/          — скалярные каноны
2  Core..Step/   (математика)      — линейка, квантование,
                                     концентрация, SafeQP
3  System/  Unified/  Growth/      — состояние, цикл, капстоуны
   Runtime/ Discovery/ Autonomy/
```

Правило LayerLint: импорт только из строго нижних слоёв;
same-folder DAG свободен.

---

## Модули: состояние и главные формулы

### Канонизация Information (состояние)

- KL: единое определение `Hagi.Prelude.klDef`; дубли
  `Distill.klDiv`, `FreeEnergy.kldiv`, `Variational.kldiv'`
  делегируют телом; `DField.KLdiv` связан rfl-мостом
  `KLdiv_eq_klDef` (полн. телегация отклонена: каскадно
  ломает 8 потребителей, сила rfl-моста та же).

### Prelude и Foundations (L1 — каноны)

- Prelude.Info: KL, TV, энтропия, softmax. Каноны:
  `klDef`, `tvDef`; `kl_nonneg` (KL ≥ 0 — единственный),
  `kl_nonneg_of_nonneg` (KL ≥ 0 и при нулевых q).
- `Ensemble/Hoeffding` (R411):
  `two_sided_good_point` + `calibrated_good_point` — при
  2|K|θ < 1 существует v: ∀k |d k v| < ε_θ =
  (b−a)√(ln(1/θ)/2) (вероятностный метод R404 × калибровка
  R409): термостатная θ гарантирует существование
  репрезентативной точки.
- `Ensemble/Hoeffding` (R410):
  `calibrated_two_sided_mass` — при ε = (b−a)√(ln(1/θ)/2):
  масса класс-хороших точек ≥ 1 − 2|K|θ (R405 × R409) —
  финал моста: охлаждение → ε-допуск → сертифицированная
  равномерная точность.
- `Ensemble/Hoeffding` (R409):
  `tolerance_calibration` — калибровка: ε := (b−a)·√(ln(1/θ)/2)
  даёт ровно e^{−2ε²/(b−a)²} = θ — мост термостата (θ-гейт
  R407) × Хёфдинга (ε-хвост R384): калиброванный хвост =
  |K|·θ.
- `Ensemble/Hoeffding` (R406): `class_size_lower` —
  нижняя граница: нет ε-хорошей точки ⟹ |K| ≥
  e^{2ε²/(b−a)²} (covering-number bound; контрапозиция
  R402).
- `Ensemble/Hoeffding` (R405):
  `two_sided_good_mass` — двусторонняя масса хороших
  точек ≥ 1 − 2|K|·e^{−2ε²/(b−a)²} (R404 + filter-расщеп-
  ление): вероятностная форма двусторонней uniform
  convergence.
- `Ensemble/Hoeffding` (R404):
  `two_sided_union_tail` — двусторонняя граница: масса
  {∃k |d k v| ≥ ε} ≤ 2|K|e^{−2ε²/(b−a)²} (индикаторное
  расщепление |d| + R384 к d и −d).
- `Ensemble/Hoeffding` (R403): `uniform_good_mass` —
  масса хороших точек ≥ 1 − |K|·e^{−2ε²/(b−a)²} —
  вероятностная форма uniform convergence (расщепление
  filter/filter_not + R384).
- `Ensemble/Hoeffding` (R402): `uniform_good_point` —
  вероятностный метод: при |K|·e^{−2ε²/(b−a)²} < 1
  существует v: ∀k d k v < ε (плохое множество покрыло бы
  всю массу, но union bound даёт < 1) — первое
  existential-применение uniform-convergence конвейера.
- `Ensemble/Hoeffding` (R384): `hoeffding_union_tail` —
  union bound: Σ_{∃k: ε ≤ d k v} w v ≤ |K|·exp(−2ε²/(b−a)²)
  — равномерный хвост над конечным классом (finite-class
  uniform convergence kernel): поточечная доминация
  индикаторов + single_le_sum + per-k R383.
- `Ensemble/Hoeffding` (R383): `hoeffding_tail` —
  Chernoff-хвост из MGF (hoeffding_fin): Σ_{d v ≥ ε} w v ≤
  exp(−2ε²/(b−a)²) при центрированном d; закрыт honest
  boundary файла («Hoeffding tail form not proven»).
  t* = 4ε/(b−a)² — точная минимизация показателя.
- `Ensemble/Hoeffding` (R374): `hoeffding_fin` — конечная
  форма леммы Хёфдинга (missing half из negative finding):
  веса w > 0 (∑ = 1), значения d v ∈ [a,b], центрированность
  ∑ w·d = 0 ⟹ ∀ t: ∑ w v·e^{t·d v} ≤ e^{t²(b−a)²/8}.
  Мост к Mathlib-мере через PMF.ofFintype +
  PMF.integral_eq_sum — движок bounded-CMI ⟹ generalization
  (Steinke–Zakynthinou этап-1) и фактор-за-фактором twoGap
  ≤ M²/8.
- `Step/WeightDecay` (R372, план §2): `wd_norm_bound` —
  обновление w(t+1) = (1−ηλ)w(t) − ηg(t) с ‖g‖ ≤ G держит
  всю траекторию в шаре max(‖w₀‖, G/λ): weight decay сам
  является ограничением нормы (неявный spectral-constraint,
  2507.01598-family), без внешней аксиомы ограниченности.
- `Probability/GibbsConcentration` (R467):
  `amortized_policy_bound` — гарантия амортизиро-
  ванной EFE-политики: суррогатный argmin при
  равномерном зазоре c исполняет в 2c от оптимума
  (RAG arXiv 2607.13612 Prop 7-структура).
- `Probability/GibbsFluctuations` (R498): `gibbs_energy_variance_bound` — для Gibbs-весов дисперсия энергии ограничена `Δ²·(n−1)·exp(−δ/T)`; доказательство: R393 (экспоненциальный избыток среднего) + R496 (Бхатия—Дэвис). Это теоретический термостатный сертификат флуктуаций, не эмпирическое измерение качества.
- `Probability/GibbsConcentration` (R491):
  `chernoff_subgauss_tail` — Чернов-subG-хвост:
  при CGF-границе q({g ≥ μ+u}) ≤ e^{−u²/(2σ²)}
  (λ = u/σ²; R483 + R490-центринг +
  exp_sub-RHS-переупаковка; связка h2.le).
- `Probability/MomentBounds` (R492–R497): вертикаль
  моментов для g∈[a,b]: `popoviciu_var` (Var ≤ (b−a)²/4;
  барицентр+midpoint+минимальность среднего),
  `chebyshev_popoviciu` (двусторонний хвост ≤
  (b−a)²/4t²; Марков на квадрате), `cantelli_one_side`
  (односторонний хвост σ²/(σ²+t²); сдвинутый квадрат,
  точная константа), `popoviciu_abs_dev` (E|g−μ| ≤
  (b−a)/2; Коши–Шварц), `bhatia_davis` (Var ≤
  (b−μ)(μ−a); per-v (b−g)(g−a)≥0), `bhatia_implies_
  popoviciu` (мост AM-GM).
- `Probability/MomentBounds` (R513, R515): мосты
  избыток↔дисперсия: `var_le_delta_excess`
  (Var ≤ (b−a)(μ−a)), `excess_ge_var_over_range`
  (Var/(b−a) ≤ μ−a) — дисперсия и избыток среднего
  взаимно сертифицируются (двусторонние stop-gate).
- `Probability/ExpChord` (R498–R508): Lp-вертикаль:
  `exp_chord` (хорда e^{rx} через ConvexOn.
  comp_linearMap), `hoeffding_chord_mgf` (взвешенная
  хордовая MGF-оценка), `log_chord` (двухточечный
  Jensen для ln), `amgm_weighted` (AM-GM),
  `young_two` (неравенство Юнга), `hoelder_finite`,
  `minkowski_finite`, `lp_one_le_card` (L1≤Lp·n^{1/q}),
  `hoelder_weighted` (поглощение w=w^{1/p}w^{1/q}),
  `lp_mean_le_rms` (E|g|≤(E|g|^p)^{1/p}),
  `minkowski_weighted` — полная невзвешенная и
  взвешенная Young→Hölder→Minkowski-вертикаль.

- `Probability/GibbsFluctuations` (R510–R512): термо-
  статное трио сертификации: `thermostat_var_stop` /
  `thermostat_threshold` (порог T ≤ δ/ln(c/ε) ⟹
  Var ≤ ε), `gibbs_var_tendsto_zero` (Var → 0 вдоль
  T_n = δ/(n+1)), `gibbs_var_steps_bound` (n+1 ≥
  ln(Δ²(n−1)/ε) ⟹ Var ≤ ε — число шагов).
- `Probability/CertifiedEstimator` (R516–R517):
  anytime-лестница шаги 1–2: `union_bound_finite`
  (T-событий union ≤ сумма), `max_bound_union` /
  `max_bound_chernoff_sum` (P(max_{t<T} g_t ≥ u) ≤
  Σ-хвостов ≤ Σ e_t). `Probability/ChernoffCGF`
  (R518): `tail_complement` (q{g<t}+q{g≥t}=1).
  `Probability/CertifiedEstimator` (R519):
  `max_bound_abs_union` — двусторонний anytime-
  хвост: P(max_{t<T} |g_t−μ_t| ≥ u) ≤ Σ_t
  (плюс-хвост + минус-хвост); 1-форма через
  le_abs' + single_le_sum, взвешивание
  mul_le_mul_of_nonneg_left, развёртки
  sum_filter/mul_sum/sum_comm. Шаг 2b
  anytime-лестницы.
- `Probability/SphericalAngle` (R520):
  `sphericalAngle` (Ω_n = 2π^{n/2}/Γ(n/2)),
  `sphericalAngle_add_two`, `sphericalAngle_factor_lt_one`,
  `sphericalAngle_even_geo` / `sphericalAngle_odd_geo`
  (геометрическое доминирование ветвей от 8 и 9),
  `sphericalAngle_tendsto_zero` (collapse:
  Γ(n/2) ~ (n/2)! растёт быстрее π^{n/2}),
  `sphericalAngle_seven` (Ω_7 = 16π³/15 —
  дискретный «пик размерностей», континуальный
  максимум n ≈ 7.257). Мост к d_eff ≤ 8
  дисциплине FactorizedBPW и прунингу.
  `Omega_7_gt_Omega_6` / `Omega_7_gt_Omega_8`
  (R521): строгое неравенство пика —
  Ω_6 < Ω_7 ∧ Ω_8 < Ω_7 (при π < 16/5),
  дискретный максимум n = 7 доказан
  полностью.
- `Ensemble/ThermoPrune` (R522):
  `condensation_budget` (каркасная
  девиация M ⟹ CE-стоимость ≤ M²/4;
  бюджет ε ⟹ девиация 2√ε) и
  `thermo_prune_certificate` — двухступенчатый
  сертификат: слои за L мертвы
  (dead_layer_stop) И каркас перестраивается
  ≤ M²/4 (prune_certificate). Формализация
  тезиса «98,5% тепловая масса, знание —
  в 1,5% каркаса».
- `Probability/CertifiedEstimator`
  `anytime_subgauss_exp` (R523):
  anytime-лестница шаг 3 — явные
  exp-члены: P(∃t<T: μ_t+u_t ≤ g) ≤
  Σ_t e^{−u_t²/(2σ²_t)} (композиция
  union_bound_finite + chernoff_subgauss_tail).
  `anytime_subgauss_const` (R524):
  стационарный случай (μ,σ²,u постоянны) —
  хвост T·e^{−u²/(2σ²)}.
  `anytime_safe_threshold` (R525):
  uniform-уровень α — порог
  u = √(2σ²ln(T/α)) ⟹ anytime-событие
  контролируется на уровне α.
- `Budget/ScaffoldFraction` (R526):
  количественный мост «1,5% ⟺ d_eff ~ 5-6»:
  факториальная таблица 4!..8!,
  `scaffold_15pct_at_deff5` (1/5! ≈ 0.83% <
  1,5%), `inv_fact_mono` (доля убывает
  по d_eff). Связка с FactorizedBPW.
- `Budget/ThermoCondensation` (R527):
  полная интеграционная связка трёх
  вертикалей: `condensation_epsilon_to_gap`
  (CE-бюджет ε ⟹ допустимая девиация каркаса
  δ = 2√ε, перестройка стоит ровно ε) и
  `thermo_condensation_full` — «слои за L
  мертвы ∧ живой каркас конденсируется в
  ε ∧ каркасная доля 1/5! ≤ 1,5%» —
  итоговая формализация тезиса «98,5%
  тепловая среда, знание в ≤1,5% каркаса,
  отрезаемого и перестраиваемого за ε».
- `Budget/AnytimeCondensation` (R528):
  динамический мост anytime-мониторинга
  и конденсации: `pointwise_upper_band`
  (пустой bad-set ⟹ точечная полоса) и
  `anytime_condensation` — при
  CGF-ограниченной (subGauss σ²) статистике
  g с пустым anytime-bad-set (вероятность
  ≤ α по anytime_safe_threshold) перестройка
  softmax-каркаса девиацией d = g − μ стоит
  ≤ 2σ²·ln(T/α) CE. Мониторинг с уровнем α
  сертифицирует конденсацию без
  переобучения.
- `Unified/TopLevel` `risk_budget_termination`
  (R529): терминация из телескопа с
  риск-бюджетом — композиция
  stage_certificate_telescope + лиапуновской
  терминации: decrease ≥ ε в каждом
  поколении ∧ суммарный risk-спенд ≤ R ∧
  потенциал ≥ Emin ⟹ горизонт ограничен:
  T ≤ (Φ₀ − Emin + R)/ε. Риск-бюджет входит
  в числитель горизонта линейно — открытый
  пункт STATUS §«Терминация из телескопа»
  закрыт.
- `Growth/GammaDeficit` (R530): закрытие
  открытого пункта «γ-дефицит mixer.gain→0»:
  `gamma_min_for_target` — достижение цели C*
  требует γ ≥ α·C*/D̄ (контрапозиция
  bounded_frontier); `gamma_deficit_no_takeoff`
  — при γ·D̄ < α·C* capability не превышает
  потолка γ·D̄/α ни в один момент: честный
  взлёт требует γ-бюджета.
- `Unified/NonvacuityHorizon` (R531):
  закрытие пункта «параметрические
  nonvacuity-свидетели ↔ cert_horizon_bound»:
  семейство насыщения satC/satF
  (C t = Cstar − Δ(1−σ)^t,
  F t = σΔ(1−σ)^t/γ) реализует ВСЕ посылки
  cert_horizon_bound на любом горизонте T,
  совместимом с геометрией конуса
  γkCstar ≤ (γk+σ)Δ(1−σ)^t; sat_cone_iff —
  точная эквивалентность конуса и
  геометрии; witness_achieves_horizon —
  честный рост C0 < C T. Witness-горизонт
  совпадает с горизонтом границы.
- `Unified/FannesComplete` (R532): ПОЛНАЯ
  Fannes-граница без hbridge-моста:
  `zs_kl` (zero-safe KL≥0 через
  носитель-сужение log_sum_ineq_on),
  `xlogx_superadd` (супераддитивность
  x·log x = Дженсен против нуля),
  `mix_point`/`mix_entropy_upper`
  (H(смесь) ≤ aH+bH+h₂), `mix_entropy_lower`
  (вогнутость), `shannon_le_log_card`,
  ГЛАВНАЯ `fanes_unconditional`: H(p)−H(q) ≤
  t·log d + (1+t)h₂(t/(1+t)), t = ½‖p−q‖₁ —
  безусловная (без eigenvalues-of-diagonal
  Mathlib-пробела R268).
- `Unified/RecursiveClean` (R533): формализация
  теории «Neural Networks Are Already Clean»
  (Goodfire/Cammarata): рекурсивное обобщение против
  суперпозиции. branchLocality L_j (средневзвешенная
  семантическая длина ветви), Условие A
  `locality_le_of_bounded` (все ветви ≤ ε ⟹ L_j ≤ ε),
  timeConsistency T*_j, Условие B
  `timeConsistency_eq_one` (упорядочены ⟹ T* = 1),
  indepMass U_j, `indepMass_eq_zero_of_cover`
  (покрывающая компонента ⟹ U = 0),
  `activationMass_entropy_le` (мост к R532),
  структура CleanCertificate + композит
  `clean_neuron_of_conditions` (A+B+U ⟹ L≤ε ∧
  T*=1 ∧ U=0), доля π̂_R с оценкой `piR_le_one`.
  Интерпретируемость — вектор характеристик, не
  единый индекс.
- `Unified/ModelComparison` (R534): Δ_j-критерий
  различения рекурсивного обобщения и суперпозиции:
  Score (MDL-качество − λ·сложность), modelGap Δ_j,
  `delta_pos_of_dominates` (MDL-обмен: проигрыш в
  правдоподобии ≤ ρ при экономии сложности > ρ/λ ⟹
  Δ > 0), правило zIndicator (1 при Δ > δ₀, 0 иначе),
  `piR_lower_of_certified` (k сертифицированных из N ⟹
  π̂_R ≥ k/N). Интерпретируемостный стек R533+R534
  замкнут: сертификат + зазор ⟹ статистика сети.
- `Unified/CausalEffect` (R535): причинный слой
  интерпретируемости — «что нейрон делает»:
  pointEffect (L1-норма изменения выхода при
  вмешательстве), causalEffect I_j(v) (средний эффект
  по данным понятия), неотрицательность,
  `causalEffect_zero_of_pointwise` (мёртвый нейрон:
  нет изменения выхода ⟹ эффект 0), контрапозиция
  `causalEffect_pos_of_point` (живой вход ⟹ живое
  понятие), `causalEffect_le_max` (среднее ≤ max
  точечного эффекта), passiveCarrier — причинное
  вето: понятие-носитель массы без вычисления не
  подтверждает ветвь обобщения (завершение вектора
  интерпретируемости R533/R534: локальность +
  история + связность + причинность).
- `Unified/InterpretiveGrowth` (R536): термодинамическая
  связка интерпретируемости с ростом: liveMass/passiveMass
  (живая = причинно-эффективная часть массы), `mass_split`
  (разложение полной массы), `gain_le_mix` (прирост ≤ ρ на
  живую + σ ≤ ρ на пассивную ⟹ ≤ ρ·total и ≤ 2ρ·total —
  пассивная конверсия подавлена), `passive_starves`
  (потолок capability ∝ живой массе: G ≤ gMax·wLive при
  gate ⟹ C ≤ gMax·wLive/α). Рост требует причинной
  интерпретируемости — корреляция без вычисления не
  конвертируется в capability (композиция R530+R535).
- `Unified/GaugeQuotient` (R537): формализация ядра
  QRR (Park & Rusch, arXiv:2610.18174 «Looped Reasoning
  Finishes Earlier Than You Think»): rot — token-local
  U(1) gauge-действие (e^{iφ}z); GaugeSystem —
  эквивариантность T(g·z)=g·T(z); quotientResidual
  r_G(z)=inf_φ‖Tz−e^{iφ}z‖ (Eq.19 статьи);
  `quotientResidual_gauge_invariant` — r_G(g·z)=r_G(z)
  (движение по орбите невидимо для quotient-теста);
  `relativeEquilibrium_residual_zero` — T z=g·z ⟹ r_G=0:
  quotient сходится раньше raw (ранний halting); ядра
  rate inheritance (Thm 3.2): `seq_dev_exact` —
  x_t−x*=s^t(x₀−x*) и `seq_dev_modulus` — |s|^t-форма:
  осцилляторная мода (s=−r) при r≥1 не затухает, при
  r<1 затухает геометрически с темпом r.
- `Unified/GaugeQuotient` аппендикс (R538): non-forcing
  (Prop A.2 QRR): `rotStep` (композиция фаз rot b∘rot a =
  rot(a+b)), `iterate_gauge_commute` — T^k(g·z)=g·(T^k z)
  (орбиты переносятся параллельно, через Function.Commute.
  iterate_left), `relativeEquilibrium_orbit` —
  T^k z = rot(kφ₀) z навсегда: raw вечно обходит орбиту,
  quotient стоит; вырожденная степень свободы с нулевой
  работой (термодинамика: работа по симметрии = 0).
- `Unified/NernstFannes` (R539): Нернст через Фаннес —
  третья теорема термодинамики как композиция R532+R386:
  dirac-сравнение (shannon_dirac_zero = 0), переводчик
  `tvHalf_dirac_eq` (tvHalf p dirac = масса вне v* —
  через sum_filter_add_sum_filter_not + sum_erase),
  `nernst_fannes` — S(p) ≤ t·log d + (1+t)h₂(t/(1+t))
  при t = масса вне минимума; с концентрацией R386
  t ≤ Ce^{−δ/T} ⟹ S(p_T) → 0 при T → 0⁺ (экспоненциально).
  Nernst-пункт закрыт.
- `Probability/GibbsConcentration` (R490):
  `cgf_centering` — центрирование CGF: ln Σq·e^{cg}
  = c·μ + ln Σq·e^{c(g−μ)} (standalone-
  лемма, выделена из R487 по Rule-of-Three).
- `Probability/GibbsConcentration` (R489):
  `mean_shift_tv` — сдвиг среднего ~ TV: при
  a ≤ g ≤ b: |E_p g − E_q g| ≤ (b−a)·TV(p,q)
  (нормировка f = (g−a)/(b−a) + R473-дуаль +
  линейный мост Δ = d·F через div_sub_div_same
  и mul_div_cancel₀).
- `Probability/GibbsConcentration` (R488):
  `subgauss_dev_kl` — sub-Gaussian измерение:
  при lnΣq·e^{c(g−μ)} ≤ c²σ²/2 и μ ≤ E_p g:
  (E_p g − μ)²/(2σ²) ≤ KL (λ*-подстановка
  λ = (E_p g − μ)/σ² в R487, без дифф. исчисления;
  вырожденный случай t = μ через R447).
- `Probability/GibbsConcentration` (R487):
  `cramer_cgf` — CGF-форма Cramér: при CGF-
  границе lnΣq·e^{c(g−μ)} ≤ ψ(c) и E_p g ≥ t:
  c·(t−μ) − ψ(c) ≤ KL для любого c > 0
  (сдвиг-centering: Σq·e^{cg} = e^{cμ}·Σq·e^{c(g−μ)}
  через exp_add + ← mul_sum-константу).
- `Probability/GibbsConcentration` (R486):
  `cramer_sup_le_kl` — sup-форма Cramér-наклона:
  sSup{c·t − lnΣq·e^{cg} | c > 0} ≤ KL
  (csSup_le + R485; неэквимости-независимая
  упаковка sup-и-bound).
- `Probability/GibbsConcentration` (R485):
  `cramer_tilt_kl` — Cramér-наклон: при
  E_p g ≥ t и c > 0: c·t − ln Σq·e^{cg} ≤ KL
  (из R481 + монотонность; НОВАЯ ОПОРА:
  arXiv 2401.01148 «PAC-Bayes-Chernoff bounds
  for unbounded losses», NeurIPS 2024).
- `Probability/GibbsConcentration` (R484):
  `exp_tilt_interpol` — экспоненциальная
  интерполяция: для a ≤ g ≤ b: Σp·e^{cg} ≤
  e^{ca}·Σp·w₁ + e^{cb}·Σp·w₂ (w₁ = (b−g)/(b−a),
  w₂ = (g−a)/(b−a)) — выпуклость e через
  двухточечный AM-GM (R454); три случая (края
  аналитически, середина через ln-вогнутость).
  Хёффдинг-кирпич.
- `Probability/GibbsConcentration` (R483):
  `chernoff_event` — Чернофф на событии: для
  λ > 0: p({g ≥ t}) ≤ e^{−λt}·E_p e^{λg}
  (Марков R482 на H := e^{λg}; эквивалентность
  фильтров через exp-монотонность).
- `Probability/GibbsConcentration` (R482):
  `markov_finite` — конечный Марков: для g ≥ 0 и
  t > 0: t·p({g ≥ t}) ≤ E_p g (фильтр-событие +
  двухшаговое расширение подмножества).
- `Probability/GibbsConcentration` (R481):
  `kl_chernoff_tilt` — Чернофф-наклон: для любого
  c: c·E_p g − ln E_q e^{c·g} ≤ KL(p‖q)
  (инстанс R477 с f := c·g — Cramér-параметризация
  функции моментов).
- `Probability/GibbsConcentration` (R480):
  `hellinger_sq_eq_one_minus_bc` — H² = 1−BC
  (точное тождество) и `hellinger_le_half_kl` —
  H² ≤ KL/2 (мост из R471).
- `Probability/GibbsConcentration` (R479):
  `kl_dv_attained` — точность ДВ: sup достижим
  (f := ln(p/q): Z = Σq·p/q = 1 через exp_log,
  log 1 = 0); с R477 — эквивалентность
  KL = sup_f (E_p f − ln E_q e^f).
- `Probability/GibbsConcentration` (R478):
  `pac_chernoff_events` — PAC-Чернофф для событий:
  при KL(p‖q) ≤ κ: p(s) ≤ κ + ln(1+(e−1)·q(s))
  (софтмакс-форма R477 с f := индикатор s).
- `Probability/GibbsConcentration` (R477):
  `kl_variational_lower` — Донскер–Варадхан
  (нижняя грань): KL(p‖q) ≥ E_p f −
  ln(Σq·e^f) (софтмакс r := q·e^f/Z +
  KL(p‖r) ≥ 0, per-v ln(p/r) = ln(p/q) − f +
  ln Z).
- `Probability/GibbsConcentration` (R476):
  `kl_joint_convex` — совместная выпуклость KL:
  KL(c·p₁+(1−c)·p₂ ‖ c·q₁+(1−c)·q₂) ≤
  c·KL₁ + (1−c)·KL₂ (per-v двухточечный log-sum:
  R451 на Fin 2 + mul_div_mul_left-разбавления);
  последний крупный классический кирпич
  инфо-теории.
- `Probability/GibbsConcentration` (R475):
  `tv_le_sqrt_one_minus_exp` — Бретаньоль–Юбер:
  TV ≤ √(1−e^{−KL}) (Коши-часть R472 →
  Σ|p−q|² ≤ 4(1−BC²); R474: BC ≥ e^{−KL/2});
  точнее R472 при большом KL.
- `Probability/GibbsConcentration` (R474):
  `neg_log_bc_le_half_kl` — −ln BC ≤ KL/2
  (log_sum R451 с парой a := p, b := √(pq):
  LHS = ln(1/BC); per-v p/√(pq) = √(p/q));
  эквив. BC ≥ e^{−KL/2} — кирпич
  Бретаньоль–Юбера.
- `Probability/GibbsConcentration` (R473):
  `tv_dual_abs` — дуальная характеризация TV:
  |E_p f − E_q f| ≤ (1/2)Σ|p−q| для любой
  0 ≤ f ≤ 1 (расщепление по {q<p} + замена
  f → 1−f); PAC-Bayes-кирпич.
- `Probability/GibbsConcentration` (R472):
  `pinsker_sqrt_kl` — Пинскер, слабая √-форма:
  TV = (1/2)Σ|p−q| ≤ √(KL) (тождество
  |p−q| = |√p−√q|(√p+√q) + Коши-сумм →
  Σ|p−q|² ≤ 4(1−BC)(1+BC) ≤ 8(1−BC) ≤ 4KL
  по R470/R471); цепь R469–R472 замкнута.
- `Probability/GibbsConcentration` (R471):
  `one_minus_bc_le_half_kl` — 1−BC ≤ KL/2 (per-v:
  t−1 ≤ t·ln t при t = √(p/q) через ln u ≤ u−1
  с u := 1/t); с R470 замыкает Пинскер-цепь
  1−BC ≤ KL/2.
- `Probability/GibbsConcentration` (R470):
  `bhattacharyya_cauchy` — Бхаттачарья-коэффициент
  BC = Σ√(pq) ≤ 1 (Коши для сумм в форме квадратов
  + sq_sqrt-свёртка); кирпич Пинскер-цепи.
- `Probability/GibbsConcentration` (R469):
  `tv_le_pos_part_kl` — TV ≤ положительная часть KL:
  (1/2)Σ|p−q| ≤ Σ_{q<p} p·ln(p/q) (расщепление
  Σ|p−q| = 2Σ_A(p−q) + ln u ≥ 1−1/u на A; МАТАН-
  ЛОВЛЯ: линейное KL ≥ TV неверно — контрпример
  0.368 < 0.4; Пинскер требует √; кирпич).
- `Probability/GibbsConcentration` (R466):
  `mutual_info_nonneg` (I = KL(ρ‖μ₁×μ₂) ≥ 0, R447 на
  R459-мерах) + `efe_ceiling` (G = P − I ≤ P — EFE не
  превышает прагматики; state-epistemic gap = I;
  RAG arXiv 2607.13612 Prop 6-структура).
- `Probability/GibbsConcentration` (R465):
  `compounding_bound` + `compounding_sq` —
  геометрический Lipschitz-компаундинг ошибки:
  e_H ≤ L^H·e₀ и e_H² ≤ (L²)^H·e₀² (O(L^{2H})-член
  RAG arXiv 2607.13612 Thm 2(ii); MPC horizon-one
  обнуляет его, Thm 2(iii)).
- `Probability/GibbsConcentration` (R464):
  `gap_decomposition` + `gapII_nonpos` +
  `gap_graceful` — трёхисточниковая декомпозиция
  зазора суррогат/истина (prior-miscalibration +
  estimator-bias + optimization-slack), Gap II ≤ 0
  для нижних прокси, линейная graceful degradation
  (RAG arXiv 2607.13612 Prop 1 / Cor 2).
- `Probability/GibbsConcentration` (R463):
  `proxy_cert_preserved` + `proxy_cert_lost` +
  `gibbs_cert_bridge` — дихотомия безопасности
  энтропийных прокси (RAG arXiv 2607.13612 Prop 2):
  нижний прокси сохраняет surprise-сертификат по
  построению, верхний строго теряет; мост к
  Гиббс-равновесию через R462.
- `Probability/GibbsConcentration` (R462):
  `gibbs_free_energy_identity` — F = ⟨E⟩ − T·S на
  равновесии: −T·ln Z = ⟨E⟩_γ + T·Σγ ln γ (per-v
  декомпозиция + свёртки; термодинамическая форма
  тождества Катони R446).
- `Probability/GibbsConcentration` (R461):
  `dist_log_nonpos` (Σρ·lnρ ≤ 0; single_le_sum +
  log-монотонность) + `joint_entropy_ge_marginal` —
  условная энтропия неотрицательна: S(V,W) ≥ S(V)
  (R460 + неположительность лог-сумм условных строк).
- `Probability/GibbsConcentration` (R460):
  `entropy_chain` — цепное правило Шеннона:
  S(V,W) = S(V) + Σ μ₁·S(условная) (per-term
  log-разделение + Fubini-свёртки ядер).
- `Probability/GibbsConcentration` (R459):
  `entropy_subadditive` — субаддитивность энтропии:
  S(совместное) ≤ S₁ + S₂ (взаимная информация
  KL(ρ‖μ₁×μ₂) = S₁+S₂−S ≥ 0; R447 + Fubini в стиле
  R458).
- `Probability/GibbsConcentration` (R458):
  `kl_product_additive` — аддитивность KL на
  произведении: KL(ρ₁×ρ₂‖γ₁×γ₂) = KL₁ + KL₂
  (цепное правило для независимых; log-разложение +
  Fubini через Σρ = 1).
- `Probability/GibbsConcentration` (R457):
  `kl_convex_first` — выпуклость KL по первому
  аргументу: KL(λρ₁+(1−λ)ρ₂‖γ) ≤ λKL(ρ₁‖γ)+
  (1−λ)KL(ρ₂‖γ) (R456 почленно + разделение сумм).
  Дуга R454→R457 завершена.
- `Probability/GibbsConcentration` (R456):
  `xlog_div_convex` — скалярная выпуклость x·ln(x/y)
  по x (R455 + линейность z·ln y; кирпич выпуклости
  KL по первому аргументу).
- `Probability/GibbsConcentration` (R455):
  `xlogx_convex` — выпуклость энтропийной функции
  x·ln x (R451 на Bool-носителе с β = (λ, 1−λ);
  кирпич выпуклости KL).
- `Probability/GibbsConcentration` (R454):
  `log_concave_two` — двухточечная вогнутость ln:
  λ·ln x + (1−λ)·ln y ≤ ln(λx+(1−λ)y) (взвешенное
  AM-GM без calculus; кирпич выпуклости KL).
- `Probability/GibbsConcentration` (R453):
  `kl_data_processing` — DPI для KL: KL(Tρ‖Tγ) ≤
  KL(ρ‖γ) для любого T (fiber-разложение + R452
  почленно по слоям; пустые слои — нулевой вклад).
- `Probability/GibbsConcentration` (R452):
  `log_sum_ineq_on` — log-sum на подмножестве s:
  (Σ_{v∈s} a)·ln(Σa/Σb) ≤ Σ_{v∈s} a·ln(a/b) (R451 на
  подтипе {v // v ∈ s}; кирпич DPI).
- `Probability/GibbsConcentration` (R451):
  `log_sum_ineq` — log-sum неравенство: A·ln(A/B) ≤
  Σ a·ln(a/b) (нормализация в распределения + R447;
  без Коши-Энгеля; кирпич Пинскера/Гиббса-Дюгема).
- `Probability/GibbsConcentration` (R450):
  `finite_max_entropy` — максимальная энтропия:
  S ≤ ln n для любого распределения (R447 при
  γ = uniform; с R418 полный контур 0 ≤ S ≤ ln n).
- `Probability/GibbsConcentration` (R449):
  `gibbs_free_energy_lower` — нижняя грань F:
  E_min − T·ln n ≤ F; с R421 — сэндвич
  E_min − T·ln n ≤ F ≤ E_min (Z ≤ n·e^{−E_min/T}
  почленно + монотонность ln).
- `Probability/GibbsConcentration` (R448):
  `gibbs_variational` — вариационный принцип Гиббса:
  ⟨E⟩_ρ + T·Σρ ln ρ ≥ −T·ln Z для любого ρ (R447 на
  Гиббс-мере; равенство на Гиббсе = R446; минимум
  свободной энергии достигается равновесием).
- `Probability/GibbsConcentration` (R447):
  `finite_kl_nonneg` — общий второй закон: KL(ρ‖γ) ≥ 0
  для любых распределений (ln u ≤ u−1 почленно с
  u := γ/ρ; телескоп Σ(ρ−γ)=0; обобщение R418;
  основа вариационного принципа).
- `Probability/GibbsConcentration` (R446):
  `gibbs_katoni_kl` — KL-тождество Катони: KL(ρ‖unif) =
  −ln Z − ⟨E⟩/T + ln n (суммирование R445; с R422 даёт
  F = ⟨E⟩ − TS из PAC-Bayes). Термодинамика ↔ PAC-Bayes
  формально замкнуты.
- `Probability/GibbsConcentration` (R445):
  `gibbs_weight_log_decomp` — log-декомпозиция веса:
  ln(ρn) = ln n − ln Z − E/T (PAC-Bayes/Катони-кирпич,
  RAG arXiv 2609.12891; суммирование даст KL-тождество).
- `Probability/MWU` (R468):
  `mwu_regret_regimes` — двухрежимный regret-капстоун:
  −ln((1/n)Σe^{−ηℓ}) ≤ max(2√(η⟨ℓ⟩·lnn), 2η⟨ℓ⟩)
  (малый режим: R444 √-балансировка; большой:
  линейная R436; η = √(lnn/⟨ℓ⟩) даёт классический
  2√(⟨ℓ⟩·lnn)).
- `Probability/MWU` (R444):
  `mwu_sqrt_bound` — η-сбалансированная: −ln W ≤
  2√(η⟨ℓ⟩·ln n) при η⟨ℓ⟩ ≤ ln n (равновесие R443-оценок
  через среднее геометрическое; классическая regret-
  структура).
- `Probability/MWU` (R443):
  `mwu_double_upper` — двойная верхняя грань: −ln W ≤
  min(2η⟨ℓ⟩, ln n + ηℓ_min): база для η-оптимизации.
- `Growth/Thermostat` (R442):
  `mwu_representative` — Хёфдинг↔MWU: выборка из
  hedge-распределения e^{−ηL} репрезентативна (R413 при
  T := 1/η). ПОЛНЫЙ ГРАФ МОСТОВ: 4 вертикали, все 6 пар.
- `Probability/MWU` (R441):
  `gibbs_hedge_squeeze` — Гиббс = hedge при η = 1/T:
  (1/T)E_min ≤ −ln((1/n)Σe^{−E/T}) ≤ 2(1/T)⟨E⟩_unif.
  Мост вертикалей: температура = обратный learning rate;
  вся MWU-механика переносится на термодинамику.
- `Probability/MWU` (R440):
  `mwu_regret_static` — статический MWU-regret в
  произведенческой форме: ηL_min ≤ −ln((1/n)Σ∏e^{−ηℓ_t}) ≤
  2η⟨L⟩_unif (R439 + R436: многошаговая механика сведена
  к одношаговому сертификату).
- `Probability/MWU` (R439):
  `mwu_partition_sum` — замкнутая форма разбиения:
  Σ∏e^{−ηℓ_t} = Σe^{−ηL} (MWU ↔ Гиббс на уровне
  разбиения).
- `Probability/MWU` (R438):
  `mwu_prod_exp` — телескоп весов: ∏e^{−ηℓ_t} =
  e^{−ηΣℓ_t} (замкнутая форма u_T = e^{−ηL_v}; полная
  многошаговая механика MWU собрана).
- `Probability/MWU` (R437):
  `mwu_potential_upper_uniform` — классический ln n-член:
  −ln W ≤ ln n + η·L_min (запас на инициализацию = ln n).
- `Probability/MWU` (R436):
  `mwu_uniform_squeeze` — uniform-старт (классический
  hedge): ηL_min ≤ −ln W ≤ 2η⟨L⟩_unif — телескопический
  потенциал кумулятивных потерь.
- `Probability/MWU` (R435):
  `mwu_potential_squeeze` — сертификат зажатия:
  ηℓ_min ≤ −ln Z' ≤ 2η⟨ℓ⟩ (R434+R433; одношаговая
  без-регретность; телескоп — следующая цель).
- `Probability/MWU` (R434):
  `mwu_potential_lower` — нижняя грань потенциала:
  ln Z' ≤ −η·ℓ_min (вклад минимизатора доминирует).
  С R433: −ηℓ_min ≤ −ln Z' ≤ 2η⟨ℓ⟩ — потенциал зажат.
- `Probability/MWU` (R433, новый файл):
  `mwu_potential_step` — одношаговый потенциал
  экспоненциальных весов: ln Z' ≥ −2η⟨ℓ⟩ при ηℓ ≤ 1/2
  (hedge-ядро без рядов: (1+2x)(1−x) ≥ 1 ⟹ e^{−2x} ≤
  1−x). Шаг 2 моста к MWU-regret.
- `Probability/GibbsConcentration` (R432):
  `gibbs_energy_gap_crude` — ⟨E⟩_T ≤ E_min + T·n для любых
  E без гэп-предположений: первый кирпич моста к
  multiplicative weights (RAG-опора arXiv 2608.09389
  EW-regret). Retry [162] успешен.
- `Growth/Thermostat` (R431):
  `thermostat_monotone` — T_{t+1} ≤ T_t: монотонность
  охлаждения (семантический кирпич вертикали).
- `Growth/Thermostat` (R430):
  `certified_state_excess_tendsto` — калориметрический
  ноль: ⟨E⟩−F → 0 (R427+R428 через Tendsto.sub; асимпто-
  тическая версия R417).
- `Growth/Thermostat` (R429):
  `certified_state_entropy_tendsto` — Нернст на термостате:
  S_t = (⟨E⟩−F)/T_t → 0. Ключ: e^{−δ/T} = (e^{−δ/2T})² ≤
  (2T/(2T+δ))² ⟹ e/T ≤ 4T/δ². ЧЕТВЁРТАЯ чистота: метрика
  + энергия + свободная энергия + энтропия.
- `Growth/Thermostat` (R428):
  `certified_state_free_energy_tendsto` — F(T_t) → E*
  вдоль термостатного графика (R398 × ln(1+x)≤x ×
  R421). ТРИАДА ЧИСТОТЫ ЗАВЕРШЕНА: метрика (R426) +
  энергетика (R427) + свободная энергия (R428).
- `Growth/Thermostat` (R427):
  `certified_state_energy_tendsto` — ⟨E⟩_{T_t} → E* вдоль
  термостатного графика (R420 × R393 × R426-хвост):
  энергетическая чистота наряду с метрической (R426).
- `Growth/Thermostat` (R426):
  `certified_state_tv_tendsto` — TV(p_t, δ*) → 0 вдоль
  отжига: сжатие TV ≤ C·e^{−δ/T_t} ≤ C·T_t/(T_t+δ) → 0
  (R386 × R395 × R425): асимптотическая чистота
  сертифицированного состояния.
- `Growth/Thermostat` (R425):
  `thermostat_tendsto_zero` — график охлаждения T_t =
  T0·α^t → 0: семантика термостата (квази-нуль),
  фундирует все tendsto-результаты вертикали.
- `Step/NewtonPolar` (R424):
  `newton_iter_bracket` — 1 ≤ newtonIter x₀ T ≤ x₀ при
  x₀ ≥ 1: инвариант-скобка вдоль всей траектории
  (индукция: R423-спуск + R53-инвариант ≥ 1).
- `Step/NewtonPolar` (R423):
  `newton_step_descent` + `_lt` — монотонный спуск
  полярного Ньютона: newtonStep x ≤ x при x ≥ 1, строго при
  x > 1. С R380/R382 траектория сертифицирована целиком:
  монотонный спуск + квадратичное сжатие к 1.
- `Probability/GibbsConcentration` (R422):
  `gibbs_kl_uniform_split` — перекрёстная энтропия:
  Σ w·ln(w·n) = Σ w·ln w + ln n (KL(Гиббс‖unif) = ln n − S;
  мост энтропия↔KL, питает Пинскер-фронт).
- `Probability/GibbsConcentration` (R421):
  `free_energy_upper` — верхняя грань: F(T) ≤ E* поточечно
  (Z ≥ w*); с R398 полный сэндвич F: сжимается к E* при
  охлаждении.
- `Probability/GibbsConcentration` (R420):
  `gibbs_expected_energy_lower` — нижняя грань: E* ≤ ⟨E⟩_T
  почленно; с R393 полный сэндвич E* ≤ ⟨E⟩ ≤ E*+Δ(n−1)e^{−δ/T}.
- `Growth/MemoryController` (R419):
  `admission_margin_sound` — обоснованность запаса
  ε_cert: если истинный выигрыш в пределах ε_cert от
  оценки (что даёт θ-калибровка R410/R413), admit
  гарантирует покрытие стоимости+риска истинным
  выигрышем. Запас — сертификат, а не декорация.
- `Probability/GibbsConcentration` (R418):
  `gibbs_entropy_nonneg` — второй закон: S(p_T) ≥ 0
  (w ≤ 1 как веса меры ⟹ −ln w ≥ 0 почленно). Вместе с
  R400 (Нернст S→0): 0 ≤ S_n → 0 — третий закон с двух
  сторон.
- `Growth/Thermostat` (R417):
  `certified_state_excess` — калориметрический избыток:
  ∃N ∀t≥N: ⟨E⟩_t − F_t ≤ (Δ+T0)·C·θ (R416 + R398 + T≤T0)
  — энергия и свободная энергия согласованы в θ-масштабе.
- `Growth/Thermostat` (R416):
  `certified_state_energy` — энергетическое следствие:
  ∃N ∀t≥N: ⟨E⟩_{T_t} ≤ E* + Δ·C·θ (R393 × R407) — энергия
  сертифицированного состояния прижата к основному.
- `Growth/Thermostat` (R415):
  `certified_state_tv` — TV-следствие: ∃N ∀t≥N: TV(p_t,
  δ*) ≤ C·θ (R408 × R395-идентификация) — сертифицированное
  состояние метрически близко к минимизатору.
- `Growth/Thermostat` (R414):
  `hagi_certified_state` — СУПЕР-КАПСТОУН: ∃N ∀t≥N:
  остановка ∧ merge-гейт ∧ концентрация ∧ ∃
  ε_θ-репрезентативная точка (R412 + R413): термодинами-
  ческая машина HAGI сертифицирована целиком — три
  вертикали + три моста в одном утверждении.
- `Growth/Thermostat` (R413):
  `gibbs_representative` — третий мост (Гиббс × Хёфдинг):
  при центрировании d по Гиббс-мере ∃v: ∀k |d k v| < ε_θ —
  выборка из охлаждённого ансамбля репрезентативна для
  класса. Треугольник мостов замкнут (R408, R409–411,
  R413).
- `Growth/Thermostat` (R412):
  `consolidation_certificate` — капстоун контроллера:
  ∃N ∀t≥N: остановка ∧ merge-гейт ∧ концентрация ≥ 1−Cθ —
  режим «консолидация» формально наступает и
  поддерживается (R407 ∧ R408, max горизонтов).
- `Growth/Thermostat` (R408):
  `phase_concentration` — после фазовой точки: share(T_t)
  ≥ 1 − C·θ ∀t ≥ N (R407 × R386): режим консолидации =
  сконцентрированное состояние (термостат × Гиббс в одном
  утверждении).
- `Growth/Thermostat` (R407):
  `thermostat_phase_point` — единая фазовая точка: ∃N,
  ∀t≥N: эксплорация остановлена ∧ merge-гейт открыт —
  одна точка переключения T-контура в режим
  «консолидация» (max горизонтов R388 × R389).
- `Growth/Thermostat` (R389): `merge_gate_eventually` —
  merge-гейт: фазовый переход неизбежен: ∀ᶠ t, θ·(T₀·α^t)
  ≤ J при J > 0 — любой положительный Jensen-зазор рано
  или поздно проходит T-гейт слияния (eventually-форма
  закона охлаждения).
- `Growth/Thermostat` (R388): `thermostat_stop` —
  термостат селектора: замкнутый горизонт остановки
  N = ⌈ln(δ/(T₀·ln(1/θ)))/ln α⌉: при t ≥ N эксплорация
  остановлена по закону Гиббса (e^{−δ/(T₀α^t)} ≤ θ) —
  T-контур: расписание T_t = T₀α^t управляет admission и
  merge-гейтами; stopping-by-law вместо эвристики.
- `Probability/GibbsConcentration` (R401):
  `gibbs_posterior_ratio` — likelihood-ratio: p_v ≤
  e^{−δ/T}·p_{v*} для δ-зазора — относительный вес
  проигравшего экспоненциально гасится (admission-гейт
  сертификат).
- `Probability/GibbsConcentration` (R400):
  `gibbs_entropy_tendsto_zero` — Нернст: S_n = (⟨E⟩−F)/T_n
  → 0 — остаточная энтропия исчезает при охлаждении
  (третий закон термодинамики HAGI; squeeze R393/R394 ×
  R398 + (n+1)e^{−(n+1)} ≤ 2e^{−(n+1)/2}).
- `Probability/GibbsConcentration` (R399):
  `free_energy_tendsto` — предел: F(T_n) → E* вдоль
  annealing-графика (squeeze R390 × R398; ошибка ≤
  δCe^{−n}/(n+1) → 0) — Nernst-стиль: свободная энергия
  вырождается в основное состояние.
- `Probability/GibbsConcentration` (R398):
  `free_energy_sharp_lower` — острая нижняя граница F(T) ≥
  E* − T·ln(1+(n−1)e^{−δ/T}): зазор δ улучшает энтропийный
  пол R390 до экспоненциально малой поправки при малых T.
- `Probability/GibbsConcentration` (R397):
  `gibbs_tv_mutual_bound` — количественный Коши: TV(p_n,
  p_m) ≤ C·(e^{−(n+1)}+e^{−(m+1)}) — явная
  экспоненциальная скорость взаимного сближения Гиббс-мер
  вдоль annealing-графика (R396 × R386).
- `Probability/GibbsConcentration` (R396):
  `gibbs_tv_mutual` — TV-треугольник: TV(p_T, p_S) ≤
  (1−share_T)+(1−share_S) — взаимная сходимость охлаждения
  (Коши-свойство; abs_add_le + R395-идентификация).
- `Probability/GibbsConcentration` (R395): `gibbs_tv_eq`
  + `gibbs_tv_tendsto` — метрическое замыкание: TV(p_T,
  δ_{v*}) = 1 − share (идентификация) и TV → 0 вдоль
  annealing-графика — охлаждение сходится в TV.
- `Probability/GibbsConcentration` (R394):
  `gibbs_expected_energy_tendsto` — предел: ⟨E⟩_{T_n} → E*
  вдоль annealing-графика (squeeze: взвешенное среднее ≥
  минимума + R393 с e^{−(n+1)} → 0) — предельная форма
  физики охлаждения.
- `Probability/GibbsConcentration` (R393):
  `gibbs_expected_energy_bound` — капстоун: ⟨E⟩_T ≤ E* +
  Δ·(n−1)·e^{−δ/T} (композиция R392 × R386): при охлаждении
  ожидаемая энергия экспоненциально прижимается к
  основному состоянию.
- `Probability/GibbsConcentration` (R392):
  `gibbs_excess_energy_bound` — избыточная энергия
  Гиббс-состояния: Σ(E v − E*)·e^{−Ev/T} ≤ Δ·(Z − w_*) —
  физика охлаждения: энергия над основным состоянием
  ограничена зазором × масса конкурентов (с R386 —
  экспоненциальное гашение при T → 0).
- `Probability/GibbsConcentration` (R391):
  `gibbs_neg_log_share_tendsto` — −ln share(T_n) → 0:
  KL(p_T ‖ δ_min) гаснет экспоненциально вдоль
  annealing-графика — мост Гиббс-вертикали к KL/Pinsker
  (охлаждение = поток информации).
- `Probability/GibbsConcentration` (R390):
  `free_energy_sandwich` — F(T) = −T·ln Z зажат между
  E* − T·ln|V| и E(v): энтропийный пол + вариационная
  верхняя — ядро границ simulated annealing (второй закон:
  описание не дешевле энтропии данных).
- `Probability/GibbsConcentration` (R387):
  `gibbs_concentration_tendsto` — предел охлаждения: вдоль
  annealing-графика T_n = δ/(n+1) доля глобального минимума
  → 1 (squeeze с exp(−(n+1)) → 0).
- `Probability/GibbsConcentration` (R386):
  `gibbs_concentration` — термодинамический закон
  охлаждения: доля веса глобального минимума в мере Гиббса
  ≥ 1 − (n−1)·e^{−δ/T} при δ-зазоре (simulated annealing /
  temperature scaling ядро); связка с ThermoAxes — куда
  сходится охлаждение.
- `Step/RiemannNewtonPolar` (R385): `radial_tangential_
  curvature` — ковариантная θθ-поправка риманова Ньютона в
  полярных координатах: h(s)=φ(√(r²+s²)) ⟹ h''(0)=φ'(r)/r =
  (r·φ'(r))/g_θθ — поправка Кристоффеля +r∂_r f равна
  истинной тангенциальной кривизне (наивный ∂²θθ=0
  вырожден — источник осцилляций у начала координат).
- `Step/NewtonPolar` (R382): `newton_polar_tendsto_one` —
  сходимость: при 1 ≤ x₀ < 3 итераты newtonIter x₀ T → 1
  (rate R380 + squeeze r^{2^T} ≤ r^T через T ≤ 2^T
  (индукция) + tendsto_pow_atTop_nhds_zero_of_lt_one).
- `Step/NewtonPolar` (R380): `newton_polar_convergence` —
  T-шаговая квадратичная сходимость: |newtonIter x₀ T − 1| ≤
  2·((x₀−1)/2)^{2^T} (удвоение экспоненты; AM-GM инвариант
  newtonStep x ≥ 1 = Byers–Xu ветка) — формальный rate
  Higham 1986.
- `Step/NewtonPolar` (R379, план §2 Muon-two-level): ядро
  Higham 1986 — Newton-polar итерация x ↦ (x+x⁻¹)/2 с ТОЧНО
  квадратичной ошибкой x_{k+1}−1 = (x_k−1)²/(2x_k);
  монотонная ветка x ≥ 1: |error| ≤ |x−1|²/2 (Byers–Xu
  scaling держит в этой ветке).
- `Budget/BitAlloc` (R381): `two_layer_clamped_corner` —
  ограниченный (b ≥ 0) 2-слойный water-filling: угловая
  оптимальность (0, B) при c₁ ≤ c₂/2^B через ТОЧНУЮ
  факторизацию (2^x−1)(c₂·2^x/2^B−c₁)/2^x ≥ 0 без calculus;
  вместе с two_layer_equalize — полный 2-слойный
  active-set оптимум.
- `Budget/BitAlloc` (R378, план §1.2): n-слойный непрерывный
  water-filling оптимум ЗАКРЫТ: `water_filling_inner_optimum`
  — выровненное по ошибкам распределение (все c i/2^{f i}
  равны) минимизирует totalErrorCont при том же бюджете;
  движок `jensen_exp_sum_le` (Σ e^y ≥ n·e^{ȳ} через
  convexOn_exp.map_sum_le). Опоры: He–Zhao–Zhou TWC 2013.
  Остаток: b ≥ 0-граница (active set) — отдельный юнит.
- `Information/Pinsker` (R377): `cmi_iteration` — финальная
  сборка bounded-CMI вертикали: средний swap-gap ≤ средняя
  стабильность + 2√(средний KL) (Коши–Шварца-concavity √);
  вместе R374–R377: полный конвейер Хёфдинг→Пинскер→
  стабильность+информация→итерация = механизм теоремы
  Steinke–Zakynthinou √(CMI/n).
- `Information/Pinsker` (R376): `gen_pair_bound` —
  обобщение = стабильность + информация: |E_q f − E_p g| ≤
  E_q|f−g| + 2√(KL(q‖p)) (sup-парное ядро доказательства
  Steinke–Zakynthinou: первый член — стабильность алгоритма
  при замене точки, второй — информация о выборе; то, что
  итерирует bounded-CMI теорема по выборке).
- `Information/Pinsker` (R375): `pinsker4_fin` — Пинскер
  (константа 4) в конечной форме: для распределений q, p и
  f : V → [0,1]: |Σ q·f − Σ p·f| ≤ 2·√(KL(q‖p)). Доказано
  БЕЗ calculus: KL ≥ −2·ln A (послаговый log_le_sub_one с
  нормировкой — «Jensen даром»), TV ≤ 2√2·H через
  Коши–Шварца на √-расщеплении, A ≤ 1 (Коши). Рабочая
  лошадка bounded-CMI ⟹ generalization (этап-2; этап-1
  hoeffding_fin R374, этап-3 — сборка CMI-теоремы).
- `Nonvacuity` (R373, аудит v8): FULL-контракт перехода —
  `CorePremises` связывает S' с композитным циклом ПОЛНОСТЬЮ
  (conjunct 14: `S'.toGrowthState = compress(joint(merge(grow S)))`,
  conjunct 15: `S'.gen = S.gen`). Свидетель
  `masterhagi_productive_witness` (T=1, орбита `Mw`):
  `Mw E 1` дефиниционно равен циклу — `FullCycleRefinement` по
  `rfl`; энергия строго убывает, capability +3/2, риск 1/4
  честно начислен. `mw_core_premises` — переиспользуемое
  свидетельство полной посылки; `corePremises_single_step_
  obstruction` (kappa=0) показывает невозможностьproductive
  траектории T≥2 при честном ledger.
- `Recurrence`: `grokking_threshold_time` (R366, ядро
  спектральной теории grokking, arXiv:2609.26679): остаточная
  динамика r(t+1) = r(t) − ηλ·r(t) достигает порога ε к
  времени ln(r₀/ε)/(ηλ) — inverse-product скейлинг времени
  генерализации; `one_sub_pow_le_exp`: (1−x)^T ≤ e^{−xT};
  `growing_batch_stabilized` (R371, план §2 «растущий
  batch»): рекурсия E(t+1) ≤ ρE(t) + η²σ²/(b₀δ^t) при
  ρ = 1−ηL < 1, δ ≥ 1, ρδ > 1 ⟹ E(T) ≤ ρ^T E0 +
  c·ρ^(T−1)/(1−(ρδ)⁻¹) — стохастический хвост гаснет на
  скорости контракции: геометрически растущий batch полностью
  extinguish'ит шумовой хвост.
  `certified_descent_with_grokking_tail` (R368): Φ_T ≤
  Φ_0 − Σ dec_t + ε — certified-спуск + погашенный
  grokking-хвост к моменту ln(r₀/ε)/(ηλ).
  Геометрический телескоп; рекуррентное
  неравенство u(t+1) ≤ ρ·u(t) + c при ρ < 1 даёт
  u(t) ≤ ρᵗ·u(0) + c/(1−ρ); `contraction_limit` (предел),
  `disp_recurrence_general`.
- `Telescope`: `telescope_le`, `lyapunov_telescope_fin`,
  `lyapunov_termination_fin` — если E падает на ε за шаг,
  то k ≤ (E₀ − Emin)/ε (терминация по Ляпунову).
- `ConeTakeoff`: конус C(t+1) ≥ ρF + γC ⟹ C₀(1+γk)^T ≤ C_T
  (`frontier_cone_inductive`, `takeoff_from_cone`).
- `StageCalculus`: законы стадий + оптимальный шаг (R347):
  `quadratic_bound_max` (потолок спуска inner²/(2L·dnorm²)),
  `eta_star_exceeds_cap` (безусловный оптимум η* нарушает кап
  1/L при certified descent), `joint_stage_cap_optimal`
  (η = 1/L оптимален на допустимом интервале: спуск
  dnorm²/(2L)), `cap_cost_factor` (цена капа — фактор
  inner/dnorm²). Покомпонентные законы стадий —
  `merge_stage` (E′ ≤ E − G при G ≥ 0), `joint_stage`
  (E′ ≤ E − η⟨g,d⟩ + Lη²‖d‖²/2), `compress_stage`
  (E′ − E ≤ κ·s·qerr при qerr ≤ 1/2), `merge_stage_decrease`.
- `Ortho`: `ortho_norm_sq_finset` — ‖∑ cₜvₜ‖² = ∑ cₜ² для
  ортонормальных vₜ (канон); следствия `gating_tail_bound`,
  спектральный хвост.
- `Chord` (`exp_chord_ab`, `log_cosh_le`), `Hoeffding`
  (Хёфдинг через MGF), takeoff-counting (слит в `FastGrowth`),
  WeightedVar (слит в `DBridge`).

### Energy / Data / Information (L2 — квантование и инфо)

- Ternary: тернарная сетка, округление к ближайшему,
  ошибка ≤ полшага s/2; qerr-инварианты.
- MergeBridge-канон: CE(t, mid) = mean CE − JensenGap,
  gap ≥ 0 (Jensen для lse на конкатенации экспертов);
  `jensenGap_pos_witness` (R356): для реального
  несогласия (z₁=(0,0), z₂=(a,−a), a≠0) зазор строго
  положителен (½log cosh a > log cosh(a/2) через
  half-angle) — не-idle свидетель: слияние расходящихся
  экспертов строго лучше среднего.
- Prelude-мосты: Fannes/Pinsker условные формы
  (`entropy_continuity_pinsker'`), бинэнтропийная монотонность.
- Дистилляция: CE/KL-тождества, mixture KKT, floors памяти.

### Probability (L2 — концентрация)

- `Azuma`: P[ΣX ≤ −Δ] ≤ exp(−Δ²/(2n)) (MGF-путь).
- `Freedman`: дисперсионно-адаптивная граница
  P[ΣX ≤ −Δ] ≤ exp(−Δ²/(2(V + bΔ/3))) — при V ≪ n
  сильнее Азумы; `adaptive_success_freedman`.
- `PMFBridge`: V↔ℝ ↔ PMF оба пути; anytime-формы
  (AnytimeValid слит в `AnytimeMartingale`).

### Step (L2 — контроллер шага)

- ProjectionDescent: `proj_descent_inner`, `min_dist_to_vi`,
  `safeQP_descent` — спуск E(w+ηd*) ≤ E − η‖d*‖²/2 при
  ε-ограничениях ⟨gᵢ,d⟩ ≥ −εᵢ на старые домены.
- SafeQP: существование/единственность, стохастический и
  адаптивный варианты с явными константами;
  `lr_batch_equivalence` (Smith+ 1711.00489): шумовой бюджет
  шага η·noiseEps инвариантен при (η,m) → (kη, k²m) — LR-
  расписание заменяется batch-масштабированием при тех же
  сертификатах;
  `safeqpEtaMax` — аналитический потолок η (не гиперпараметр).
- `MetricSafeQP`, `MDLThreeCurrency` (трёхвалютная MDL-цель
  с детектором двойного учёта), `FrobeniusLMO`,
  `PreconditionerDescent`, `ArmijoAcceptance`, `WarmupSchedule`.
- `ControllerGates` (Runtime): variance gate — R²/8
  контрактуется квадратично при τ = R/R̄;
  `trust_region_proj_norm` — ‖(R/‖x‖)•x‖ = R и проекция
  на шар ближайшая.

### QuantBridge (L2 — квантование→потеря)

- `quant_loss_bridge`: ‖(Ŵ−W)x‖ ≤ D·√(mn)·‖x‖ (ранг-1);
  `quant_frob_loss`: ΔE ≤ κ_F·D·√(mn);
  `frob_minkowski` (Коши–Буняковский + Минковский),
  `compress_chain_cost`: |ℓ(W)−ℓ(W″)| ≤ κ_F·(δ₁+δ₂).

### Spectral / External (L2 — внешний порт FLYWHEEL)

- Порт FLYWHEEL (Apache-2.0, acomarce): singularValues,
  SVD-разложение, `eckart_young_frobenius` (нижняя
  оптимальность), Weyl, Courant–Fischer, MDL-ранг
  (`mdlJ_first_order`, `mdl_rank_ce`).
- Namespace Mathlib.* сохранён осознанно (внешний порт).
- Спектральный хвост: `spectral_tail_energy`,
  `cert_horizon_witness`, `mdl_rank_ce`, `gate_retention`.

### Model (L2 — явная модель)

- `SoftmaxStep` (Model): `joint_stage_logitCE` (R350) —
  h_emp_smooth ВЫВЕДЕН из явной logit-CE модели
  (десцент-лемма = L-smoothness при L = 1/2, η ≤ 2):
  certified joint stage без измеряемых посылок — первый
  закрытый мост «явная модель → stage-calculus»;
  `logitCE_trajectory_bound` (R354) — телескоп T шагов:
  logitCE(w_T) ≤ logitCE(w_0) − Σ η_t·d_t²/2, все посылки
  выведены, h_emp_* нет;
  `descent_step`, `grad_lipschitz` (σ² ≤ 1/4).

### Spectral: RankGrowth (R360)

- `rank_orthogonal_growth` (ядро arXiv:2607.14571 «What
  Does Model Growth Really Add?»): если k новых строк
  функционального Якобиана линейно независимы и
  ортогональны всем старым строкам (dormant directions), то
  rank стек-матрицы РОВНО rank M + k — ёмкость растёт на
  полное число добавленных направлений при нетронутом
  старом row space. Мост к h_emp_grow-фронту.
  `span_growth_zero_interference` (R367): любое обновление
  в спане новых (ортогональных старым градиентам)
  направлений имеет нулевое вмешательство во все старые
  домены (SafeQP ε=0) — рост ёмкости не платит бюджет
  безопасности.

### Budget (L2/L3 — распределение ресурсов)

- BitAlloc: маржинальный обмен битами точен
  (`transfer_exact`); water-filling = балансировка двух
  слоёв (`two_layer_equalize`); фактор-2 жадный инвариант;
  полный сертификат поколения
  S_n + n·g ≤ E₀ + δ_n + totalError.
- `CertifiedArgmax`: сертифицированный argmax доминирует
  (`argmax_pair_certified`); при малых зазорах argmax
  противоречив (`tie_ambiguity` — контрпример).

### Growth-каскад (L3 — взлёт)

- `StateBinding`: C(t) = capability, G(t) = growGain поля
  состояния — конус на реальной траектории.
- `FrontierScaling` (`frontier_cone_invariant`),
  `GainRenewal`, `Saturation` (насыщение: C_T ≤ C* −
  (1−σ)^T·(C*−C₀)), `GrowthCeiling` (`growth_dichotomy`),
  `RatioTakeoff`, `TakeoffElasticity`.
- `ConeTakeoff`-мост: `ChainToCone`, `DisagreementChain`.

### System / Unified (L3 — состояние и капстоуны)

- `GrowthState` (System): ядро состояния (weights, params,
  energy, protectedRisk, budget, capability, stepDir, sp) +
  `StageEffects` (12 измеренных полей эффектов) +
  `Certificate`/`Metrics`/`Candidate` + verify/measure/
  discover. Законы:
  - `growth_cycle_potential`: Φ(после цикла) ≤ Φ −
    (gainGrow + G + η‖d*‖²/2) + (Σ рисков + κs/2);
  - `certificate_sound`: Φ′ ≤ Φ − dec + riskSpend;
  - `budget_account`: budget′ = budget − budgetSpend;
  - `macro_termination_derived` (делегат Ляпунова);
  - `protected_generation_budget`: регресс ≤ T·ε,
    расход ≤ T·b.
- `StageCertificate` (R342): before/after/cert; телескоп
  `stage_certificate_telescope`:
  Φ_{T−1} ≤ Φ₀ − Σ decrease + Σ riskSpend при континуитете
  before(t+1) = after(t) (скрытых отождествлений нет);
  `termination_from_telescope`: если decreaseₜ ≥ ε и
  riskSpendₜ ≤ r < ε, то T ≤ (Φ₀ − φmin)/(ε − r) — цикл
  не может работать бесконечно (композиция с
  `lyapunov_termination_fin`).
- `MasterHAGI_linked` (R362, аудит v6 §4.1): посылка
  C t = (S t).capability для t ≤ T — рост доказан для
  capability РЕАЛЬНОЙ траектории состояний, а не свободной
  последовательности. Аудит v6 §12: MasterHAGI /
  hagi_synthesis / grand_synthesis — аксиомы чистые.
- `MasterHAGI` (условный капстоун): полный цикл на
  GenState-траектории; `MasterHAGI_trunc` +
  `masterhagi_growth_witness` (свидетель не-вакуозности);
  `CertifiedHAGIInvariant`/`CoupledHAGIInvariant` с
  числовыми свидетелями (`certifiedHAGI_nonvacuous`,
  `coupledHAGI_nonvacuous`).
- `ArchitectureTheorem` (R338: Fin 1 → Fin I):
  `HAGICert` на произвольном семействе доменов;
  `hagi_synthesis`:
  - взлёт: C₀(1+γk)^T ≤ C_T ≤ C* − (1−σ)^T(C*−C₀);
  - риск: ∀ домен i: Σ risk(t,i) ≤ T·best(i) + R +
    ε₀/(1−ρₑ);
  - `cert_horizon_bound`/`hagi_horizon_bound` —
    логарифмическая совместимость взлёта и насыщения;
  - `cert_horizon_log_bound` (R349) — явный потолок
    горизонта: (T−1)·ln(1+γk) ≤ ln(σC*) − ln((γk+σ)·C₀)
    при зазоре (γk+σ)·C₀ < σC*;
  - `cert_horizon_witness`, `band_witness`.
- `GrandSynthesis` (compositions-capstone): измерительная
  цепочка + конус + coupled-капстоун в одном утверждении
  о траектории (взлёт, риск-телескоп, точный бюджет,
  probe-полы); пункты 2/4 — плоские передачи посылок
  (честно обозначено).
- `Assumptions.Trunc` + `trunc_nonvacuous` (idle-свидетель),
  `Nonvacuity` (S₀/S₁ свидетели CorePremises),
  `HAGICertWitness` (горизонт-1, все 17 полей);
  `masterhagi_productive_witness` (R370, ВЕРШИНА):
  на X = ℝ, K = Fin 1 — траектория, где ВСЕ посылки капстоуна
  MasterHAGI выполнены одновременно с живыми величинами:
  ненулевой безопасный шаг (stepDir = 1, η = 1/2 внутри
  SafeQP-окна против старого градиента −1, риск честно
  платится 1/4/шаг), энергия строго убывает, capability
  растёт составно (×3/2 за шаг), budget-счёт точен;
  заключение CertifiedHAGIInvariant выведено самим
  MasterHAGI. Полная лестница R357 → R359 → R369 → R370.
  Аудит v8: многошаговый trajectory-witness (R369) снят —
  при FULL-контракте перехода measured effects копируются
  дословно, поэтому «продуктивная» траектория T≥2
  невозможна при честном ledger (см.
  `corePremises_single_step_obstruction`); productive
  свидетель имеет форму одного честного шага T=1.
  `corePremises_nonvacuous_strict` (R357) — не-idle
  свидетель: gap = строгий Йенсен-зазор (слит в Nonvacuity, R356),
  growGain = gap > 0, энергии E → E−g → E−2g — все 15
  конъюнктов CorePremises + строгое убывание ledger.

### Autonomy / Omni / Discovery / Deployment (L3)

Universality (слит в `ArchitectureTheorem`; `universality_longhorizon`,
  Fin I):
  Σ risk ≤ T·best + R + ε₀/(1−ρₑ); `Liveness`
  (`liveness_two_axis`: цикл не замерзает, пока жива ось);
  `Insight` (KL-канал обучения, `forgetting_kl_bound`);
  Omni (кросс-модальный gap = взаимная информация);
  `PPT` (discovery-ядра).

---

## Рефакторинг по аудиту v4 (фаза 0 — сделано)

- `HypothesisCompetition` (Model, DHC): ядро динамической
  конкуренции гипотез — softmax-веса выбора
  (`dhcWeights`: положительность, нормировка,
  монотонность, лидер ≥ 1/K, уникальность лидера
  при весе > 1/2), шаг динамики с взаимным
  подавлением (`dhcStep`: инерция + поддержка +
  κ·C·p), орбита `dhcOrbit` с инвариантом
  ограниченности `dhcOrbit_bound` (индукция по
  `dhcStep_abs_bound`); критерий завершения p₁ ≥ τ ∧
  p₁-p₂ ≥ Δ корректен на каждом шаге
  (`dhcOrbit_weights_sum_one`).
- `ProbeError` (Pretraining, мост Boost→Cut PR #11): теория проявления
  Модель гладкости — явная гипотеза; ошибка прямой
  разности от градиента ≤ Lσ‖v‖²/2
  (`fd_probe_error`); аффинное вырождение — точное
  восстановление (`linear_probe_exact`);
  top-k маршрутизация MLP: остаток и его приращение
  ограничены треугольником по нормам столбцов
  (`residual_vec_bound`, `residual_vec_diff`, `mlpResidual_bound`);
  дальнейший путь ошибки — через
  `Core.ErrorProp.propagate_bound`. Спуск
  по неточному сигналу: сертификат с аддитивным запасом
  `dLexact ≤ dLmeas + ε·‖d‖` (`safe_certificate_margin`,
  Cauchy–Schwarz на разности направлений) и приём шага при
  нулевом бюджете риска (`probe_safe_accept`) — мост
  «приближённый сигнал → SafeQP-допуск». Накопление
  измеримого выигрыша: `measured_gain_horizon` — горизонт
  безопасных шагов ограничен `(E0−Emin)/gain` при факт-лоссе
  как ledger-энергии (делегирование
  `System.macro_termination_derived`; прирост измеряется
  фактически, без назначенного growGain).
  Аудит-регрессии (P1): дефекты фиксированной
  записи эффектов зафиксированы как теоремы —
  `corePremises_two_step_decrease_nonpos` (общий κ: два подряд
  `CorePremises` дают `decrease ≤ κ·s·(quantErr − 1/2) ≤ 0`) и
  `full_cycle_two_step_growth_inconsistent` (аддитивный
  growGain + конусное насыщение несовместимы при T=2, α>0,
  C₀>0). Чинит семантику: измерения — вход перехода
  (модуль `Hagi.Model.StageSemantics`: `advance`/`Trajectory`/
  `advance_energy_drop`/`cone_growth_window` с окном
  `alpha_min <= alpha_cap` без зажатия; witness
  `three_cycle_varying_gain_nonvacuous` — три активных цикла
  (приросты 1, 2, 4; энергия 30-27-23-17; capability 1-2-4-8) —
  невозможен в старой модели по двум регрессиям выше;
  `two_cycle_certified_descent` связывает witness с
  `advance_energy_drop`). Усиление и
  объединение: `capability_takeoff_amplified` (state-linked
  геометрический рост по траектории при свободных поцикловых
  приростах), `trajectory_energy_telescope` (многоцикловой
  сертификат прогресса), `cycle_drop_ge_certificate` (старый
  сертификат `System.verify` — нижняя граница реального
  per-cycle drop; то самое зажатие окна — теперь конструктивно),
  `witness_takeoff_realized` — takeoff (1+1)^3 * 1 = 8
  РЕАЛИЗОВАН на witness-траектории (старой модели был вакуумен). Дедуп
  exp-хорды: канон `Foundations.exp_chord_r` (r-обобщение);
  `Probability.exp_chord` и `Foundations.exp_chord_ab` (r=1)
  делегируют; `Ensemble.exp_chord` — симметричный частный случай
  поверх `exp_chord_ab` — одна математическая копия вместо трёх. Ещё один
  дословный дубль устранён: `System.Certificates.penalty_drop_bound`
  теперь делегирует канону `Foundations.hagiPotential_penalty_drop`. KL-канон:
  `Prelude.kl_nonneg` (строгий q>0) — частный случай нулейтолерантного
  `kl_nonneg_of_nonneg`; копия proof'а заменена однострочной
  делегацией (канон перенесён раньше по файлу). Терминация
  отремонтированной модели: `trajectory_termination` — при
  сертифицированном drop >= d0 > 0 и floor Emin весь горизонт
  ограничен T <= (E0-Emin)/d0 (объединение телескопа с канонической
  лиапуновской арифметикой; при старой фиксированной модели
  положительный d0-горизонт был невыполним). Честные
  ledger'ы: advance_budget_le/advance_risk_ge и
  trajectory_ledgers_monotone — типовая неотрицательность трат
  (proof-поля StageInput) даёт бух فقط в честную сторону: бюджет
  вдоль траектории не растёт, защищённый риск не убывает. Количественная
  форма ε_attention: `clamped_attention_grad_bound` (гладкость
  по клампнутым выходам, гипотеза `h_emp_attsmooth`), итог
  `‖gu − gF x‖ ≤ ε_probe + L_att·ε_att`
  (`cut_signal_attention_quant`) и сквозной приём шага
  `cut_safe_accept` (объединение Теорем 1–3: суммарный запас
  → нулевой бюджет риска → истинный спад). Термодинамика
  (research-цикл, ask.sciencemadereadable.com): модуль
  `Energy.Landauer` — цена стирания информации при тернарном
  квантовании (Sagawa–Ueda PRL 2009, Janzing quant-ph/0002048,
  Tkachenko arXiv:2503.09980): при физическом мосте
  (диссипация >= c_unit·KL стёртых весов, `h_emp_landauer`)
  discarded-info за compress-шаг ограничена энергетическим
  бюджетом: `landauer_sandwich` (KL <= kappa*s*quantErr/c_unit),
  `landauer_cap_certified` (KL <= kappa*s/(2*c_unit) при
  quantErr <= 1/2) — бюджет каппит разрушаемую информацию:
  давление к минимальному объёму при заданной точности. Итерация 2:
  память, а не арифметика (Tkachenko) + конечное время
  (Konopik–Lutz Nat Commun 2023): `written_bits_cap`
  (запись F бит стоит >= F·c_unit → F <= B/c_unit),
  `ternary_weight_growth_cap` (n новых тернарных весов:
  n <= B/(c_unit·log 3) — термодинамический потолок роста
  архитектуры за цикл), `serial_divergence_cap` (serial-ран
  расходится с размером задачи; рост должен оставаться
  параллелизуемым). Итерация 3 (интеграция speedrun-рецепта
  qlabs-eng/noise train/speedrun/run.py):
  `Hagi/Pretraining/Speedrun.lean` — точные readout-credit
  тождества forward-only бустинга: `cePartition_move` (сдвиг
  одного логита меняет partition ровно на один член),
  `ceLogit_move_change` (замкнутая форма изменения CE при сдвиге
  логита: target-сдвиг + log(1 + w_j(e^δ−1)) из ЧИСТЫХ
  softmax-весов — nothing is differentiated), `head_probe_linear`
  (линейный head на пробе = чистые логиты + предвычисленное
  направление: probe стоит один head-eval). Честная граница:
  софт-кап 15·tanh(z/15) рантайма — h_emp-мост вне тождеств. Плюс `hadamard_probe_inversion`:
  при строково-ортогональных probe (H·Hᵀ = c•1) измерения
  g = H·Δ восстанавливают credit-вектор Δ ТОЧНО (Δ = c⁻¹·Hᵀg) —
  k forward-оценок дают все k координат против 2k при
  координатных разностях; восстановление — тождество, не
  оценка (мост с Hagi.Core.Hadamard sylvester-ортогональностью). Итерация 4 (spectral trust region, Muon/ANVIL-мост;
  theory: arXiv:2506.15054, 2502.02900):
  `Hagi/Pretraining/TrustRegion.lean` — ортогонализованный шаг
  живёт под спектральным trust region: `hadamardRows_sup_bound`
  (|Q·ᵥδ|_i <= ||δ||_2 для строково-ортонормальной Q:
  Cauchy–Schwarz + единичные строки — шаг двигает каждую
  координату не дальше η·||δ||_2), `orthonormal_mulVec_isometry`
  (Parseval: Q·ᵥδ сохраняет L2-норму credit-вектора —
  ортогонализованный momentum не усиливает и не гасит ни одно
  направление), `transpose_mul_self_of_mul_transpose`
  (QᵀQ = 1 из QQᵀ = 1 через обратимость). Итерация 5: `probe_lower_bound` —
  нижняя граница измерений: менее k линейных probe-строк всегда
  существует ненулевой credit-вектор со ВСЕМИ нулевыми
  показаниями (finrank-аргумент: injective → k <= n) — точное
  восстановление Δ = c⁻¹Hᵀg невозможно; минимальная
  термодинамическая цена ПОЛНОГО credit'а — ровно k
  forward-оценок за итерацию (цена оценки — Landauer-мост
  Energy.Landauer). Связка Speedrun+Landauer замкнута:
  hadamard_probe_inversion ДОСТИГАЕТ нижнюю границу. Итерация 6 (capstone):
  `cycle_budget_split` — бюджет цикла B расщепляется на
  измерение (k·c_unit, нижняя граница итерации 5) и запись
  (F·c_unit, Landauer): c_unit·(k+F) <= B — качество (объём
  измеренного credit'а) и объём (размер записанной модели)
  конкурентны за один и тот же энергобюджет ЛИНЕЙНО
  (линия k + F = B/c_unit). Итерация 7:
  `trajectory_budget_telescope` — композиция по траектории: если
  каждый цикл t удовлетворяет c_unit·(k_t+F_t) <= B_t и суммы
  бюджетов телескопируются (sum B_t <= E_total), то ВЕСЬ прогон
  удовлетворяет той же линии: c_unit·(sum k_t + sum F_t) <=
  E_total — термодинамический потолок не на цикл, а на весь
  саморазвивающийся запуск. Итерация 8
  (композиция lifetime × budget):
  `lifetime_thermodynamic_ceiling` — потолок ВЫВЕДЕН из времени
  жизни траектории: при per-cycle диссипации <= d0 и lifetime
  T <= (E0−Emin)/d0 весь прогон за жизнь измеряет и запишет
  не более (E0−Emin)/c_unit бит-эквивалентов — потолок
  саморазвития следует из терминации, не постулируется.
  Итерация 9 (не-пустота): `witness_ceiling_attainable` —
  потолок ДОСТИЖИМ (tight): чисто измерительный цикл с
  B = c_unit·k, F = 0 сидит ровно на кромке
  c_unit·(k+0) = B — задача обучения сводится к выбору
  расщепления (k, F) на линии k + F = B/c_unit для максимума
  реализованной capability — формальное ядро принципа
  «максимальное качество при минимальном объёме».
  СВОДКА цикла (ит. 1–9): 16+ теорем, 0 sorry/axiom, все
  axioms = [propext, Classical.choice, Quot.sound]. Замкнуты две
  линии: (A) термодинамическая: Landauer-сэндвич → memory-кап →
  cycle_budget_split → trajectory_telescope →
  lifetime_thermodynamic_ceiling (ВЫВЕДЕН) → witness (ДОСТИЖИМ);
  (B) credit: speedrun-тождества → hadamard_probe_inversion
  (k оценок достаточно) → probe_lower_bound (k необходимо) +
  spectral trust region (Muon). Результат: задача обучения HAGI
  при термодинамических законах формально сводится к выбору
  точки (k, F) на линии k + F = (E0−Emin)/(c_unit·T).
  СЛЕДУЮЩИЙ шаг: tying (k, F) к capability-росту (cone-takeoff /
  GrowthState) — содержательная модель качества. Итерация 10:
  `optimal_split_pareto` — максимум качества при минимальном
  объёме СТАЛ теоремой: при строго монотонной по измеренному
  credit capability θ (quality-as-information, Jeon–Van Roy
  arXiv:2407.01456) расщепление k* = B/c_unit − F_max
  Парето-доминирует любую другую точку линии бюджета с капом
  объёма — всё, что не потрачено на измерение, чистая потеря.
  Итерация 11 (ядро саморазвития): `thermodynamic_growth_witness`
  — СУЩЕСТВОВАНИЕ растущего прогона: при T >= 1, k_min > 0 и
  энергии, покрывающей линию чистого измерения
  (c_unit·T·k_min <= E_total), существует легальная траектория
  (каждый цикл на кромке бюджета, F = 0), и финальная capability
  СТРОГО БОЛЬШЕ начальной: модель выросла, соблюдая все
  термодинамические законы — потолок не запрещает саморазвитие,
  лишь ограничивает его полный объём. Итерация 12:
  `strict_prefix_growth` — строгое покса-развитие: capability
  растёт КАЖДЫЙ цикл, не только в конце: для всех i < j < T
  кредит-префикс после j циклов строго больше префикса после i,
  значит (строгая монотонность θ) capability на стадии j строго
  выше стадии i — саморазвитие в сильном смысле: без плато,
  каждый цикл окупает себя. Итерация 13:
  `first_crossing_le_lifetime` — время до цели: если прогон из T
  циклов превосходит целевой уровень capability
  (θ(T·k_min) > θ_target), существует МИНИМАЛЬНОЕ n <= T первого
  пересечения (Nat.find-минимальность: все более ранние префиксы
  не достигают цели) — термодинамически легальный прогон сам
  сообщает, сколько саморазвитие занимает времени; время до цели
  ограничено временем жизни.
  СВОДКА полного цикла (ит. 1–13): 25+ теорем, 0 sorry/axiom,
  все axioms = [propext, Classical.choice, Quot.sound], каждый
  коммит с полным CI. Три замкнутых линии:
  (A) Термодинамика: Landauer → memory-cap → cycle split →
      telescope → lifetime ceiling (выведен) → witness (достижим)
      — рост совместим с законами термодинамики (ит. 11–12:
     покажди-циклный строгий рост без плато; ит. 13: время до цели
      = первое пересечение, <= lifetime).
  (B) Credit: speedrun-тождества → Hadamard-инверсия
      (k достаточно) → probe_lower_bound (k необходимо).
  (C) Оптимум: spectral trust region (Muon) +
      optimal_split_pareto (качество при минимальном объёме).
  Формальное ядро objective исчерпано: дальнейшие шаги требуют
  содержательной гипотезы формы θ (h_emp-территория) вне
  алгебраического ядра. Итерация 14 (контрольный пример
  перколяции, ответ на критический аудит §5):
  `Hagi/Percolation/Site.lean` — слои 1–2 конкретной случайной
  микродинамики: сетка LxL (cellAdj/openGraph), общее
  вероятностное пространство порогов (seed ω : V → Fin M,
  openAt qv), событие прорыва crossing. Строго доказаны
  заявления аудита 1–3: crossing_mono (дополнительные клетки не
  разрушают путь — supergraph+Reachable.mono), card_Ω (точная
  перечислимость: |Ω| = M^(L·L)), R_monotone (R не убывает по
  порогу — вложенность событий на общем seed, без теории меры).
  Честная граница: p_c ≈ 0.5927 бесконечной решётки НЕ выводится —
  асимптотика и мост к takeoff (Layer 4) остаются открытыми
  разрывом, теперь конкретным, а не аналогическим. Итерация 15
  (Layer 3, эмерджентность): `emergence_jump_witness` — на сетке
  2×2 с parity-seed подъём порога 1 → 2 ПЕРЕВОРАЧИВАЕТ макро-
  свойство на том же seed: при qv=1 открытые клетки {(0,0),(1,1)}
  попарно не смежны — пути нет; при qv=2 ОДНА клетка (0,1)
  соединяет половины и путь (0,0)→(0,1)→(1,1) возникает.
  Глобальная capability из ОДНОГО локального события — строгий
  качественный переход, формализованный. Итерация 16
  (объединение): класс `ThresholdSystem` (cap : Ints → ℝ,
  монотонность по интенсивности) — общая форма перколяционного R
  (`percolationSystem`: intensity = порог, mono = R_monotone) и
  HAGI-моделей θ (intensity = absorbed credit): монотонно-
  пороговые аргументы — например, Парето-доминирование
  optimal_split — переносятся ОДИН раз на все системы,
  реализующие интерфейс. Итерация 17 (Layer 3, количественное
  замыкание): рефакторинг свидетельства на именованные части
  (`paritySeed`, `rowTop`, `rowBot`, `parity_not_crossing1`,
  `parity_crossing2`) и строгое усиление `R_strict_jump` —
  вероятность пересечения СТРОГО растёт: R(1) < R(2) на той
  же сетке 2×2, весь строгий прирост 1/16 идёт от одного seed
  `paritySeed` (индикатор 0 → 1), все прочие seeds движутся
  монотонно (crossing_mono + Finset.single_le_sum); аксиомы
  [propext, Classical.choice, Quot.sound].
- Итерация 18 (объединение, маршрут B — единое ядро вперёд,
  нейтральные имена без разрушения Freeze): (1) новый модуль
  `Hagi/Energy/Quantizer.lean` — канонический квантователь
  решётки `gridQ Δ x = Δ * round (x / Δ)`: равномерная ошибка
  ≤ Δ/2 БЕЗ ограничений на x (обобщает roundHalf_error и
  roundTern_error_scaled), idemпотентность,
  gridQ_mem_grid (образ = решётка Δℤ), gridQ_div — единый
  оператор вместо россыпи точечных округлений; (2)
  `lyapunov_gain_noise` в Foundations/Telescope — нейтральная
  форма верхнего рекуррентного сертификата
  (V(t+1) ≤ V t − gain t + noise t ⟹ V T ≤ V 0 − Σ gain +
  Σ noise), точная форма Master-сертификатов без ролевой
  лексики. Аксиомы всех трёх: [propext, Classical.choice,
  Quot.sound].
- Итерация 19 (объединение, маршрут B — зеркальный спуск):
  `gibbs_optimal_bound` в `Hagi/Energy/Variational.lean` —
  точная оптимизационная форма темперированного софтмакса:
  для всех q на симплексе, L и T > 0
  ⟨L⟩_q + T·Σ q log q ≥ −T·log Σ exp(−L/T) — нижняя граница
  вариационного принципа, достигаемая Гиббс-весами
  softmax(−L/T) (равенство); выведена из
  free_energy_variational на равномерной базе (decomposition
  KL + Finset-алгебра, без новой аксиоматики). Вместе с
  gridQ (ит. 18) и lyapunov_gain_noise замыкает компоненты
  1–3 единого ядра (квантование, телескоп, охлаждение).
- Итерация 20 (объединение, маршрут B — компонент 4,
  квантованный шаг): новый модуль `Hagi/System/DiscreteStep.lean`
  — `quantized_descent_telescope`: фактическая динамика
  x(t+1) = Q_Δ(x t − γ·g t) (решётка Δℤ из gridQ, ит. 18)
  даёт сертификат горизонта T
  x T ≤ x 0 − Σ γ·g + T·Δ/2 — ошибка квантования входит в
  ляпуновский телескоп (lyapunov_gain_noise, ит. 18) как
  аддитивный шум Δ/2 за шаг, цена квантования явная.
  Замкнуты все 4 компонента единого ядра: квантование
  (gridQ), телескоп (lyapunov_gain_noise), охлаждение
  (gibbs_optimal_bound, ит. 19), шаг (DiscreteStep).
- Итерация 21 (рефакторинг по аудиту 2, шаг A —
  state-dependent effects): в `Hagi/Model/StageSemantics.lean`
  добавлен слой эффектов, ВЫЧИСЛЯЕМЫХ ИЗ ТЕКУЩЕГО СОСТОЯНИЯ:
  `stateGrowthEffects α S` (growGain = α·C_t — продуктивный
  закон, который модель с фиксированными эффектами не выражает)
  + `growInput` (честный StageInput на цикл) +
  `growAdvance_capability` (прирост ровно α·C_t за переход),
  `grow_two_step_consistent` (C₂ = (1+α)²·C₀ — зеркальное
  опровержение two-step-противоречия: геометрический закон
  ВЫПОЛНИМ на двух циклах, прирост порождается переходом, а не
  встроен формулой) и `grow_strict_productive` (строгий рост
  каждый цикл — клауза Productive трихотомии аудита
  Nonempty/Productive/SustainedTakeoff). Старая модель и её
  регрессионный тест
  full_cycle_two_step_growth_inconsistent сохранены.
- Итерация 22 (объединение по аудиту 3 — единая траектория,
  SustainedTakeoff): в StageSemantics добавлены `growSeq`
  (рекурсивная последовательность честных переходов:
  S(t+1) = advance(S(t), growInput α S(t)) — эффекты
  пересчитываются из текущего состояния КАЖДОГО цикла),
  `growTraj` (Trajectory-обёртка, h_step = rfl) и
  `growSeq_capability` — ростовой закон по всей Honest-
  траектории: capability(S(t)) = (1+α)^t·C₀ при t ≤ T, каждый
  множитель порождён реальным переходом (ср. с упрёком аудита
  к `coupledGrowthTraj`, где рост встроен формулой). Замкнуты
  все три клаузы трихотомии аудита: Nonempty (idle-свидетели),
  Productive (ит. 21), SustainedTakeoff (ит. 22).
- Итерация 23 (объединение по аудиту §3 — платный рост и
  единый ledger): в state-зависимом слое рост сделан ПЛАТНЫМ:
  `stateGrowthEffects α μ S` теперь несёт growCost = μ·C_t
  (рост пропорционально оплачивается из бюджета — «рост без
  цены», слабость прежнего свидетеля, устранена).
  Последовательность `growSeq` несёт инвариант
  0 ≤ μ·capability КОНСТРУКТИВНО на каждом шаге (subtype),
  что делает честность цены частью определения — без
  внешних гипотез в рекурсии. Новые теоремы на ОДНОЙ
  траектории: `growAdvance_budget` (цикл списывает ровно
  μ·C_t), `grow_two_step_consistent` (второй цикл
  пересчитывает и gain и cost из выросшего состояния),
  `growSeq_capability` (C_t = (1+α)^t·C₀) и
  `growSeq_budget_ledger` — бюджетный ledger на той же
  траектории: budget(t) + μ·Σ_{i<t} C_i = budget(0), где
  C_i — та же capability-последовательность. Capability,
  энергия и бюджет теперь из одной динамики (мост
  MasterHAGI-предпосылок к честным переходам). Инфослой
  (аудит §4A) проверен: все KL/TV-определения — rfl-мосты
  к канону Prelude.Info, независимых копий нет.
- Итерация 24 (рефакторинг по аудиту 3, этапы 1+4):
  (1) новый CI-гейт `AssumptionScan` — воспроизводимый
  реестр внешних допущений и примитивов: все идентификаторы
  h_emp_* (117 в 34 файлах) и все определения
  информационных примитивов (kl/tv/ent/softmax/lse — 17) —
  фиксируются в scripts/assumptions.lock (workflow как у
  Freeze: осознанный diff при добавлении); критерий
  готовности этапа 1 аудита закрыт; измеримая база для
  дальнейшей свёртки дубликатов. (2) свернут канонический
  пример этапа 4: ratio_takeoff (Growth/RatioTakeoff) —
  ручная индукция (25 строк) заменена следствием
  elasticity_chain (Growth/TakeoffElasticity) с
  константной конусной эластичностью e t = γ·k: конус даёт
  пошаговую нижнюю границу эластичности, произведение
  цепочки — взлёт; утверждение теоремы НЕ изменилось
  (Freeze прошёл без update), всё семейство takeoff теперь
  имеет единый позвоночник: cone_step → elasticity_chain.
- Итерация 25 (этап 4 аудита 3 — ядро Перрона): новый модуль
  `Hagi/Foundations/PerronCone.lean`, формализующий
  алгебраическое наблюдение аудита: `coneMatrix γ β ρ`
  (= [[1,γ],[β,ρ]]), `coneVec k` (= (1,k));
  `cone_eigenvector_iff` — (1,k) собственный вектор с
  собственным значением 1+γ·k РОВНО при β = γk²+(1−ρ)k
  (условие конуса = уравнение собственного вектора, скорость
  взлёта = корень Перрона); `cone_perron_growth` — при
  равенствной динамике и старте на границе конуса
  C T = (1+γk)^T·C0 И D T = k·C T для всех T (точный
  геометрический рост, одно утверждение, которое все шесть
  вариантов takeoff-семейства аппроксимируют; вместе с
  elasticity_chain (ит. 24) даёт их неравенственные формы с
  той же скоростью). Позвоночник конус-семейства:
  cone_step → cone_perron_growth/elasticity_chain.
- R351: Freeze переведён на 3-колоночный lock (name, hash,
  name-независимый stmt-хеш): переименование утверждения
  проходит автоматически как alias, правка утверждения —
  FAIL. scripts/Metrics.py в ci.sh.
- R352–R353 (Фаза 1): namespace = каталог для всех файлов
  без новых сущностей — только группировка + прямая правка
  ссылок (qualified, root-relative, open). M1: 54 → 3
  (остаток — RealF3/RoPE-группы: файлы делят namespace с
  ядром группы, это корректная семантическая группировка).
  Freeze: 0 потерь, утверждения не изменены.

## Рефакторинг по аудиту v5 (группировка без потерь)

- Решения: сохраняем ВСЕ доказанные утверждения (Freeze),
  Flywheel и капстоуны не удаляем; капстоуны честно
  документируем как условные телескопы. Цель — 5 групп
  (Math/Optimization/Dynamics/Protocol/Assumptions)
  постепенными переносами каталогов.
- R361: Depth (F3Root, RootContrast → Core) и Deployment
  (ProxyGap → Dynamics) слиты; каталоги Depth/Deployment
  удалены. 26 каталогов. LayerLint PASS.

## Честность контрактов (аудит v7)

- `cone_premises_force_exact` (R363): посылки
  frontier_cone_trunc (конус + продукция + шаг + потолок)
  СОВМЕСТНО принуждают точный закон C(t+1)=(1+α)C(t) —
  зафиксировано как лемма-экспонат; точный темп роста —
  часть модели (закон перехода), не вывод. Чистая слабая
  версия: `takeoff_from_cone` (конус + шаг, без потолка).
- `saturation_law_forced` (R364, §6.2): hpl_up + hpl_lo
  принуждают ТОЧНЫЙ закон насыщения C(t+1) =
  C(t) + σ(Cstar − C(t)) — насыщение часть модели, не вывод.
- `budget_horizon_nonneg` (R364, §6.1): точный счёт бюджета
  + неотрицательные расходы ⟹ B_t ≥ 0 на ВСЁМ горизонте
  (∀t ≤ T), не только в конечной точке.
- `MasterHAGI_linked` (R362): рост-канал C связан с
  capability состояний (§4.1 аудита v6 закрыт).

## Открытые задачи

- Вывод `h_emp_*`-посылок из Core-слоя: закрыты merge
  сжатие (слит в Nonvacuity) и compress (тернарное округление);
  открыты `h_emp_grow`, `h_emp_smooth`, `h_emp_lip`
  (требуют модель выпуклости/липшицевости измерений).
- GrandSynthesis: пункты 2/4 выведены из более слабых
  посылок (R540): `risk_telescope_of_growth_covered`
  (глобальный телескоп C T − C 0 ≤ Σ risk из пошагового
  покрытия G t ≤ risk t — индукция с mem_range-переводом),
  `qfloor_le_of_monotone` (полы из floor-в-нуле +
  покомпонентной монотонности), композит
  `grand_synthesis_weak` — та же 5-частная конъюнкция
  при ослабленных посылках. Пункт закрыт.
- Фаза 7 namespace=каталог: мигрированы (R543) три flat-модуля
  термоконденсации: ThermoPrune → Hagi.Ensemble,
  ThermoCondensation/AnytimeCondensation → Hagi.Budget
  (FREEZE PASS без потери имён); остались flat: Core/RealF3*
  (вложенный ns), Core/Select; Flywheel-файлы — Matrix.*-ns
  (узаконенный внешн. стиль). Остаток — постепенная миграция;
  сокращение широких `import Mathlib` (Certificates и др.).
- Flywheel → отдельный Lake-пакет (постепенно, план §3).
- Certified гарантия роста закрыта (R561 ч.2,
  `CertifiedGrowth.certified_band_growth`): нижняя полоса
  горизонта сертифицируется margins-парами (prob_ladder),
  на хорошем событии band_guaranteed_growth_range даёт рост:
  «margins → C T ≥ C 0 + (b/σ)(1−(1−σ)^T)» с уровнем
  1 − 2T·e^{−2nε²}; certified-каскад и рост-дуга сомкнуты
  в обе стороны (верх R555-канал, низ R561-канал).
- Range-версия гарантированного роста (R561 ч.1,
  `band_guaranteed_growth_range`): полоса только на горизонте
  t < T — сертифицируемая форма (канон R540-лямбд);
  подготовка к certified-нижней полосе (ч.2).
- Нижняя полоса + таймер цели закрыты (R560):
  `GrowthDynamics.band_guaranteed_growth` (G t ≥ b(1−σ)^t ⟹
  C T ≥ C 0 + (b/σ)(1−(1−σ)^T) — гарантированный рост при
  затухающей поддержке) и `band_time_to_target` (цель внутри
  нижнего насыщения ⟹ C* ≤ C T — таймер термостата);
  полоса теперь двусторонняя: верхний потолок R556 + нижняя
  гарантия R560.
- РЕФАКТОРИНГ Фаза 0/начало (внешний аудит принят,
  верифицирован Map!=Territory): (1) баррель Hagi.lean
  расширен на ВСЕ 328 модулей — раньше 38 (аудит говорил
  22) были вне CI-цели, включая все новые Certified*/
  NernstFannes/DerivAlong; lake build 9253 jobs,
  конфликтов имён нет; (2) пустые библиотеки
  Hagi.Deployment/Depth удалены из lakefile (каталогов
  не существует); (3) аудит-уточнение: полный локальный
  lake build строил всё и раньше — ЗАМЕТКА: моё
  «Build completed (9231 jobs)» было локальным полным
  билдом, но ci.sh до сих пор гатил только баррель;
  теперь гейт эквивалентен. Дальше: TrivialLint на
  покомпонентный пересказ + линт неиспользуемых
  параметров (D0). План пробуждения из аудита в чате;
  REFACTOR_PLAN.md НЕ восстанавливать (gitignore).
- R569 ЗАКРЫТ: острый брекет пика — ψ(7/2) = 46/15 −
  2ln2 − γ ≈ 1.103 < ln π ≈ 1.145 (γ > 0.5357), IVT сужает
  s* ∈ (7/2, 4), x* ∈ (7, 8) (реальный пик ≈ 7.257 ✓).
  digamma_half_step (рекуррента в полуцелых) +
  digamma_seven_half_val/re + digamma_logpi_root_exists_
  sharp. Канон: Complex.sub_re ДО log/γ-rewrite (re
  применён к целому sub-выражению); hlast-замена (↑r).re
  через simp; рекуррентная цепь через (2k+1)/2-cast-
  форму. FREEZE 2553→2557; CI PASS.
- R568 ЗАКРЫТ: континуальный пик замкнут —
  `SphericalAngle.digamma_peak_exists`: при γ-брекетах
  сущ. x* ∈ (6,8) с Re ψ(x*/2) = ln π (подстановка x* = 2s
  из R566-корня; field_simp для (2*s)/2-cast). Диагамма-
  дуга ПОЛНА: значения (R562) + непрерывность (R566) +
  корень (R566) + пик (R568). FREEZE 2552→2553;
  аксиомы канон; CI PASS.
- R567 ЗАКРЫТ (fc5f564): таймер термостата в замкнутой
  лог-форме — `GrowthDynamics.time_to_target_log`: при
  sigma < 1 и sigma(C*-C0) < b горизонт T >=
  ln(1-sigma(C*-C0)/b)/ln(1-sigma) влечёт C* <= C T.
  Механика: div_le_iff_of_neg (log(1-sigma) < 0!) +
  Real.log_lt_log контрапозиция + Real.log_pow +
  band_time_to_target-подстановка. Требует СТРОГОЕ
  sigma < 1 (при sigma = 1 вырождено) и hс0: C0 <= C*.
  Канон: div_le_iff_of_neg hc : b/c <= a <-> a*c <= b
  (c < 0); le_div_iff₀ (у = b/c форму); div_lt_one hb.
  FREEZE 2551→2552; аксиомы канон; CI PASS.
- R566 ЗАКРЫТ (8c62ae3): континуальный пик-фундамент —
  `SphericalAngle.digamma_continuousOn_right` (ψ непрерывна
  на {Re w > 2} через Γ-quotient и AnalyticOnNhd.deriv),
  `digamma_re_continuousOn` (вещественная ветвь на [3,4]),
  `digamma_logpi_root_exists` (IVT: при γ-брекетах сущ.
  s в (3,4), Re ψ(s) = ln π, пик x* = 2s в (6,8)).
  Канон: Complex.Gamma_ne_zero; Complex.differentiableAt_
  Gamma (open Real перебивает имя); Complex.ofReal_re t;
  intermediate_value_Ioo (hab) (hf) : Ioo (f a) (f b) ⊆
  f '' Ioo; DifferentiableOn.analyticOnNhd — 2 аргум.
  FREEZE 2548→2551; аксиомы канон; CI PASS.
- R565 ЗАКРЫТ (6bfe8ac): `Unified.DerivAlong.
  smooth_from_lipschitz_gradient` — h_emp_smooth ВЫВЕДЕН
  из L-гладкости градиента (‖∇E(y)−∇E(x)‖ ≤ L‖y−x⟫):
  Newton–Leibniz вдоль сегмента + pointwise-оценка
  deriv_along_segment_le (Cauchy–Schwarz для CLM через
  ContinuousLinearMap.le_opNorm) + integral_mono_on +
  полиномиальный интеграл ∫₀¹ t = 1/2. E(q+dir) ≤ E(q) +
  ⟨∇E(q),dir⟩ + L·‖dir‖²/2. Канон: hsmooth-порядок
  аргументов (x y) даёт ‖fderiv y − fderiv x‖;
  add_le_add_right (не left!) в calc-цепочках с правым
  слагаемым; le_opNorm даёт норму значения (нужен
  Real.norm_eq_abs-мост для скаляра); le_trans по
  цепочке вместо многошагового calc. h_emp-троица
  ПОЛНОСТЬЮ закрыта (lip R563, grow R564, smooth R565).
  FREEZE 2544→2548; аксиомы [propext, Classical.choice,
  Quot.sound]; CI PASS.

- h_emp_grow закрыт (R564): `LipEnergy.
  grow_gain_from_smooth_descent` — энергетический учёт
  grow-стадии (growEnergy ≤ energy − growGain) выводится
  из upper-quadratic модели (h_emp_smooth) + certified
  descent + SafeQP-окна одной подстановкой joint_stage
  (StageCalculus); growGain = η·dnorm²/2 — измеримая
  константа. Из h_emp-троицы осталась только smooth
  (вторая производная / L-гладкость).
- h_emp_lip-модель закрыта (R563): `Unified.LipEnergy.
  lip_energy_from_gradient` — MVT-вывод |E(w)−E(q)| ≤
  κ·‖w−q‖ из градиентной модели (‖∇E‖ ≤ κ всюду),  `lip_energy_quantization` — h_emp_lip-форма (dE ≤
  κ·dist(w, qTern(w))); измеренный κ = sup‖∇E‖ —
  открытый пункт STATUS «модель липшицевости измерений»
  закрыт на уровне согласованной посылки (MVT на сегменте).
- ψ-инструментарий дополнен (R562 шаг 2): `SphericalAngle.
  digamma_half_value` (ψ(1/2) = −2ln2−γ, Complex-форма),
  `digamma_reflection_bridge` (Эйлер: ψ(1−s)=ψ(s)+π·cot πs),
  `digamma_recurrence_bridge` (ψ(s+1)=ψ(s)+1/s); полная
  ψ-монотонность отложена (Mathlib: Gauss-интеграл TODO —
  многовитковый проект, нужен trigamma-ряд).
- Дигамма-мосты закрыты (R562 шаг 1): `SphericalAngle.
  digamma_three_eq/four_eq` — harmonic-форма ψ(3) = H₂−γ,
  ψ(4) = H₃−γ (cast-цепочки ℚ→ℝ→ℂ); брекет-следствия
  `digamma_three_below_logpi / four_above_logpi` — при
  γ-посылках x* ∈ (6,8) сведено к σ-интервалу; следующий
  шаг — ψ-монотонность (trigamma > 0) + IVT.
- План континуального пика (R562+, виток #203):
  существующая теория Ω (SphericalAngle) уже в Γ-языке
  (2π^{n/2}/Γ(n/2), Ω_7-мост через Γ-recurrence);
  континуальный максимум x*: ψ(x/2) = ln π требует
  Mathlib Complex.digamma + ψ-монотонности (trigamma > 0 —
  в Mathlib отсутствует, строить самому); числовая
  развилка: ψ(3) = H₂−γ = .9228 < ln π = 1.1447 < ψ(4) =
  H₃−γ = 2.2561 ⟹ x* ∈ (6,8) — согласовано с 7.257.
  Формализационный план: ψ-monotone (через harmonic-форму +
  trigamma-ряд) → IVT-существование → бracket (6,8) →
  числовой zoom до (7.2, 7.3).
- Двойной потолок закрыт (R559): `Unified.DualCeiling.
  dual_ceiling` — при полосе + γ-гейте оба ограничительных
  канала работают одновременно: C T ≤ C 0 + b/σ ∧
  C T ≤ γ·D̄/α; термостат-модель собрана в единую
  двухканальную характеристику (R556+R557+R559).
- Термостат-дуга замкнута (R557): `band_target_unreachable` —
  цель выше потолка полосы (C 0 + b/σ < C*) не достигается
  ни на каком горизонте; обратная сторона R530 γ-дефицита:
  полоса — второй механизм блокировки takeoff (после
  γ-бюджета); пара {γ-дефицит; полоса-потолок} = полная
  термостат-характеристика недостижимости.
- Затухающая полоса ⟹ capability-потолок закрыт (R556):
  `GrowthDynamics.band_telescope` (∀t-форма) +
  `geometric_band_ceiling` — прирост накрыт G t ≤ b(1−σ)^t
  (b ≥ 0, σ ∈ (0,1]) ⟹ C T ≤ C 0 + (b/σ)(1−(1−σ)^T) ≤ C 0 + b/σ:
  формальный мост к сигнатуре насыщения satC (R531); docs-sync
  README (324 модуля, 2524→2526 frozen, 1924 theorem).
- Certified-каскад замкнут (R558): `CertifiedTakeoff.
  sample_size_adequate` — n ≥ ln(2T/α)/(2ε²) ⟹ дефект
  лестницы 2T·e^{−2nε²} ≤ α: обратная задача «сколько
  измерений нужно» решена в явной формуле; кнопка
  «уровень доверия → размер выборки» формализована.
- Certified T-шаговый takeoff закрыт (R555 ч.2):
  `CertifiedGains.prob_ladder_lower` (универсальная лестница:
  шаговые bad-события ≤ M ⟹ P(q) ≥ 1 − T·M) и
  `certified_gainprod_takeoff` (A_t = {margin_t ∧ μ-нарушение}
  ≤ 2e^{−2nε²} + точечное покрытие + лестница ⟹ импликация
  «все T margins → takeoff» с уровнем 1 − 2T·e^{−2nε²}) —
  первая полная цепочка «выборка → T-шаговый takeoff».
- Union bound для нулевых масс закрыт (R555 ч.1):
  `UnionBound.union_bound_nonneg` — ladder-объединение при
  0 ≤ q v (prodDens имеет нули; старый union_bound_finite
  требовал 0 < q v); фундамент для T-шаговой сертификации
  прироста (ч.2 — следующий виток).
- Certified-takeoff закрыт (R554): `Unified.CertifiedTakeoff.
  certified_cone0_takeoff` — cone0-посылка через μ-средние
  сертифицируется certified_premise (P ≥ 1 − 2e^{−2nε²});
  на хорошем событии точечно sustained_takeoff_trunc ⟹
  импликация «margin → takeoff» с тем же уровнем. Первый
  мост «выборка → детерминированный takeoff».
- Export-чистка завершена (R553-retry, fb1e84d): строгий
  сканер (same-dir потребители считаются, docstrings
  исключены) — 14 мёртвых блоков удалены, −42 строки;
  total за кампанию: 98+14=112 файлов, −571 строка живых
  re-export-мостов удалено билд-гейтом.
- E3/E4-вердикт (виток #192): Contract-типизация h_emp_*
  УЖЕ реализована в R199: MasterHAGITrunc.frontier_cone_struct
  принимает GrowthDynamics-bundle (emp*-поля делают
  условность видимой в сигнатуре) — внешний аудит-пункт
  закрыт существующим кодом; остаток (certified-вариант
  inequality-посылок через certified_premise) — следующий
  исследовательский фронт.
- Внешний аудит репо верифицирован по коду (R550, дополнение в
  REFACTOR_PLAN §4): kl-дубли УЖЕ сведены rfl-мостами к klDef;
  ProjectionMoments — фантом; числа файлов неверны (Step=42,
  Growth=35); audit-каталог — ghost, но удаление = FREEZE LOST;
  export-блоки (185) отбывать массово — отклонено; h_emp_-Contract
  — подтверждено (фаза E4). Скорректированы приоритеты 1–3.
- Гиббс+Нернст композит закрыт (R549): `NernstFannes.gibbs_nernst`
  — у Гиббс-распределения с δ-зазором S(p_T) ≤ t̂·log d +
  (1+t̂)·log 2 при t̂ = (d−1)e^{−δ/T}: третий закон с явной
  экспоненциальной скоростью (gibbs_concentration + nernst_fannes
  + binEntropy ≤ log 2); T → 0⁺ ⟹ S → 0 экспоненциально.
- Anytime-growth бюджет закрыт (R548):`Foundations.GrowthDynamics.
  telescope_band` (полный прирост ≤ телескоп полосы) и
  `anytime_growth_budget` (полоса μ+u ⟹ C T ≤ C 0 + T·μ + T·u)
  — базовая композиция концентрации с capability-телескопом.
- REFACTOR_PLAN B2 начат (R547): канонический бридж
  shannonEntropy = Information.shannon (DistillRecursion),
  починен изолированный CR в файле; tvDist-unify — следующий шаг.
- REFACTOR_PLAN E2/Ф2 закрыт (R546): бюджетная неповышаемость
  выделена в бюджетную лемму budget_nonincreasing_of_nonneg_spend
  (арифметическое следствие 0 ≤ spend, не содержательное
  утверждение); grand_synthesis использует её вместо inline-блока.
- Конденсационный конвейер закрыт (R545, REFACTOR_PLAN D1):
  `Budget.AnytimeCondensation.condensation_pipeline` — одна
  составная: CGF(subGauss σ²) + пустой anytime-bad-set (≤ α)
  ⟹ dead layers за L + стоимость каркаса ≤ 2σ²·ln(T/α) CE
  + scaffold ≤ 1,5% (d_eff=5); трио ThermoPrune/ThermoCondensation/
  AnytimeCondensation соединено в линейный конвейер.
- Anytime-Freedman композиция: закрыта (R541+R542):
  `anytime_freedman_thresholds` — лестница k-зависимых
  порогов (P[∃ j ≤ T: r j ≤ S_j ∧ C_j ≤ V_j]
  ≤ Σ_j exp(−r j²/(4(V j + c·r j))), мост historyLaw_past_mean
  + pmfMean_event_union) и R542 `anytime_freedman_thresholds_
  two_sided` — двусторонняя |S|-лестница: 2·Σ_j того же члена
  (плечи S и −S — свои пороговые лестницы).
- Lean↔Runtime property-тесты — требует torch-рантайма
  E:\HAGI_v2 (blocked); §I LSL-стек — нет спецификации.

## Счётчик

- 1714 theorem/lemma; 2683 деклараций (Freeze); 0 sorry;
  LayerLint-исключений: 0.
