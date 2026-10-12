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

### Prelude и Foundations (L1 — каноны)

- Prelude.Info: KL, TV, энтропия, softmax. Каноны:
  `klDef`, `tvDef`; `kl_nonneg` (KL ≥ 0 — единственный),
  `kl_nonneg_of_nonneg` (KL ≥ 0 и при нулевых q).
- `Recurrence`: геометрический телескоп; рекуррентное
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
