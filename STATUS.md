# STATUS — состояние формализации HAGI

Метрика «0 sorry» недостаточна (тавтологии её проходят).
Правила приёмки: заключение ≠ посылка; не `rfl`/`A = A`;
`#print axioms` — только propext / Classical.choice /
Quot.sound; эмпирические посылки — префикс `h_emp_`.
История раундов удалена (git log, docstrings); здесь —
текущее состояние, главные формулы и открытые задачи.

## Корпус

- 290 Lean-модулей в `Hagi/` (28 каталогов), 2196 деклараций
  в declarations.lock (Freeze, 2026-10-11), 1712
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
- `Nonvacuity` (R373): `masterhagi_productive_witness_all` —
  R370-witness обобщён с T=1 на произвольный T ≥ 1: все
  посылки MasterHAGI на каждом шаге t < T, энергия строго
  убывает на всём горизонте, capability 2(3/2)^T, риск T/4;
  терминальный энергополоток Emin := e_T (T-зависимый).
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
  (Хёфдинг через MGF), `TakeoffCounted`, `WeightedVar`.

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
  (`AnytimeValid`, `AnytimeMartingale`).

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
  `corePremises_trajectory_productive` (R369): для ЛЮБОГО
  горизонта T существует траектория, на которой
  CorePremises выполняется на КАЖДОМ шаге со строго
  убывающей энергией (E − 2t·g), строгим зазором g > 0 и
  растущей capability (+g за шаг) — полный
  траекторный (category-2) свидетель аудита v7 §5.3.
  `corePremises_nonvacuous_strict` (R357) — не-idle
  свидетель: gap = строгий Йенсен-зазор (MergeBridge, R356),
  growGain = gap > 0, энергии E → E−g → E−2g — все 15
  конъюнктов CorePremises + строгое убывание ledger.

### Autonomy / Omni / Discovery / Deployment (L3)

- `Universality` (`universality_longhorizon`, Fin I):
  Σ risk ≤ T·best + R + ε₀/(1−ρₑ); `Liveness`
  (`liveness_two_axis`: цикл не замерзает, пока жива ось);
  `Insight` (KL-канал обучения, `forgetting_kl_bound`);
  Omni (кросс-модальный gap = взаимная информация);
  `PPT` (discovery-ядра).

---

## Рефакторинг по аудиту v4 (фаза 0 — сделано)

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
  (`MergeBridge`) и compress (тернарное округление);
  открыты `h_emp_grow`, `h_emp_smooth`, `h_emp_lip`
  (требуют модель выпуклости/липшицевости измерений).
- GrandSynthesis: вывести пункты 2/4 из более слабых
  посылок или оставить композицией (нужна новая математика).
- Фаза 7 namespace=каталог: ~50 flat-namespace модулей
  (Hagi.BatchCap в Budget/ и т.д.) — постепенная миграция;
  сокращение широких `import Mathlib` (Certificates и др.).
- Flywheel → отдельный Lake-пакет (постепенно, план §3).
- γ-дефицит mixer.gain→0 — честно открыт.
- Полная Fannes-граница (Pinsker-часть доказана); anytime-
  Freedman (совместная M/V форма).
- Параметрические nonvacuity-свидетели ↔ `cert_horizon_bound`
  (связать свидетель с горизонтом).
- Терминация из телескопа: композиция
  `stage_certificate_telescope` + `lyapunov_termination_fin`
  (если decrease ≥ ε > 0 и riskSpend ограничен — стоп).
- Lean↔Runtime property-тесты — требует torch-рантайма
  E:\HAGI_v2 (blocked); §I LSL-стек — нет спецификации.

## Счётчик

- 1712 theorem/lemma; 2196 деклараций (Freeze); 0 sorry;
  LayerLint-исключений: 0.
