# ALGORITHMS.md — алгоритмы HAGI, выведенные из доказанных теорем

Каждый алгоритм — прямое следствие машинно-верифицированной
теоремы Lean 4 / Mathlib (Hagi/, 1889 theorem/lemma, 0 sorry,
аксиомы только propext/Classical.choice/Quot.sound).
Ссылки: `Hagi/<Каталог>/<Модуль>.lean`. Измеряемые посылки
помечены `h_emp_` и никогда не скрыты.

---

## 0. Главный цикл: certified growth loop

```
loop:
  1. ИЗМЕРИТЬ      энергию E, зазор G, d*, κ, s, бюджеты
  2. СЕРТИФИЦИРОВАТЬ StageCertificate (before/after/dec/risk)
  3. ВЫБРАТЬ       действие argmax Γ_certified/K
  4. ИСПОЛНИТЬ     grow → merge → joint → compress
  5. ПРОВЕРИТЬ     Φ′ ≤ Φ − dec + riskSpend   [certificate_sound]
  6. СТОП          если consensus ∧ inj ≤ ξ   [liveness_two_axis]
```

- Потенциал: Φ = E + protectedRisk.
- Одно поколение: `growth_cycle_potential` —
  Φ(после) ≤ Φ − (gainGrow + G + η‖d*‖²/2) + (Σ рисков + κs/2).
- T поколений: `stage_certificate_telescope` —
  Φ_{T−1} ≤ Φ₀ − Σₜ decreaseₜ + Σₜ riskSpendₜ
  при континуитете before(t+1) = after(t).
- Бюджет: `budget_account` — budget′ = budget − budgetSpend
  (точная арифметика, не оценка).
- Терминация: `macro_termination_derived` — если каждый шаг
  уменьшает E ≥ ε > 0, то k ≤ (E₀ − Emin)/ε.

## 1. Выбор действия: argmax Γ/K

- Теоремы: `ratio_dominance`, `budget_allocation_dominance`,
  `argmax_pair_certified` (Budget/CertifiedArgmax).
- Алгоритм:

```
for i in ACTIONS:                     # merge/joint/grow/
                                       # internalize/prune
    Γ_i = сертифицированный прирост:
        merge:   G = JensenGap ≥ 0    # MergeBridge
        joint:   η‖d*‖²/2             # safeQP_descent
        grow:    growGain (h_emp_)
        prune:   экономия − δ²/4
    K_i = измеренная стоимость
choose argmax Γ_i/K_i                  # доминирует любую разбивку
```

- Контрпример-предостережение: `tie_ambiguity` — при малых
  зазорах argmax противоречив; порог задаётся certified-полем.
- Запрет: не выбирать по standalone CE — `selection_hurts`.

## 2. Безопасный шаг: SafeQP (без learning rate)

- Теоремы: `safeQP_exists_unique`, `safeQP_descent`,
  `safeqp_inactive`, `safeqpEtaMax` (Step/ProjectionDescent,
  Step/MetricSafeQP).

```
d* = proj_C(g₀),  C = {d : ⟨g_i, d⟩ ≥ −ε_i}   # старые домены
η* ≤ safeqpEtaMax = min(1/L, ...)              # аналитический
если g₀ ∈ C:  шаг неактивен (d* = g₀)
```

- Гарантия спуска (joint_stage):
  E′ ≤ E − η⟨g₀,d*⟩ + Lη²‖d*‖²/2 ≤ E − η‖d*‖²/2
  при η ≤ 1/L и ‖d*‖² ≤ ⟨g₀,d*⟩.
- Оптимальный η (R347, StageCalculus):
  `quadratic_bound_max` — безусловный потолок модельного
  спуска inner²/(2L·dnorm²) при η* = inner/(L·dnorm²);
  `eta_star_exceeds_cap` — при certified descent η* > 1/L,
  кап активен; `joint_stage_cap_optimal` — на допустимом
  интервале оптимален η = 1/L, спуск dnorm²/(2L);
  `cap_cost_factor` — цена капа = фактор inner/dnorm² > 1.
  Правило: η = 1/L всегда (не настраивать); усилие — не в
  η-тюнинге, а в росте dnorm² (quality of direction).
- LR↔batch эквивалентность (`lr_batch_equivalence`,
  StochasticSafeQP; Smith et al. 1711.00489): шумовой бюджет
  шага η·noiseEps ∝ ησ/√m инвариантен при (η, m) → (kη, k²m).
  Правило планировщика: вместо снижения LR в k раз —
  увеличение batch в k² раз; сертификаты
  `stochastic_safeQP_feasibility` сохраняются на том же δ,
  а последовательных обновлений на ту же кривую — в k раз
  меньше (больше параллелизма). 

## 3. Гейт слияния: реальный CE-зазор

- Теорема (Unified/MergeBridge): CE(t, mid) = mean CE −
  jensenGap(z₁,z₂), jensenGap ≥ 0 — выводится из Core-lse
  теории, не постулируется.
- Правило: сливать пару, если jensenGap ≥ порога; экономия
  экспертов без роста CE гарантирована теоремой.
- Строгость (R356, `jensenGap_pos_witness`): при реальном
  несогласии экспертов (z₁=(0,0) vs z₂=(a,−a), a≠0) зазор
  строго положителен: ½log(cosh a) > log(cosh(a/2)) —
  слияние расходящихся экспертов строго лучше среднего,
  не-idle свидетель.

## 4. Квантование: тернарная сетка + мост потери

- Тернарное округление: |w − qTern| ≤ s/2 (Energy/Ternary).
- Мост в потерю (QuantBridge):
  - `quant_loss_bridge`: ‖(Ŵ−W)x‖ ≤ D·√(d_in·d_out)·‖x‖;
  - `quant_frob_loss`: ΔE ≤ κ_F·D·√(d_in·d_out);
  - `compress_chain_cost`: |ℓ(W)−ℓ(W″)| ≤ κ_F·(δ₁+δ₂);
  - `frob_minkowski`: норма-Минковского + Коши–Буняковский.
- Compress-стадия (compress_stage): E′ − E ≤ κ·s·qerr при
  qerr ≤ 1/2 — из этих канонов.

## 5. Спектральный отбор (Flywheel-порт)

- `eckart_young_frobenius`: усечение SVD оптимально по
  Фробениусу; Weyl-стабильность; `mdlJ_first_order`,
  `mdl_rank_ce` — MDL-ранг первого порядка.
- Правило: ранг k выбирать по MDL-критерию; потеря
  контролируется сертификатом Эккарта–Юнга.

## 6. Бюджет битов: water-filling

- `transfer_exact`: маржинальный обмен битами точен;
  `two_layer_equalize`: балансировка = water-filling;
  фактор-2 жадного инварианта (`stable_factor_two`).
- Сертификат поколения (distill_quant_composite):
  S_n + n·g ≤ E₀ + δ_n + totalError.

## 7. Концентрация и anytime-валидность

- Хёфдинг (MGF), Азума: P[ΣX ≤ −Δ] ≤ exp(−Δ²/2n).
- Freedman (`freedman_tail_low`):
  P[ΣX ≤ −Δ] ≤ exp(−Δ²/(2(V+bΔ/3))) — адаптивно к
  дисперсии; при V ≪ n сильнее Азумы.
- Мартингальные успехи: `adaptive_success_freedman`,
  anytime-формы (AnytimeValid) — доверительные границы
  валидны при произвольной остановке.

## 7b. Grokking-расписание (R366, Recurrence)

- `grokking_threshold_time`: остаточная динамика
  r(t+1) = r(t) − ηλ·r(t) достигает порога ε к моменту
  T = ln(r₀/ε)/(η·λ) — время генерализации управляется
  ПРОИЗВЕДЕНИЕМ learning rate × weight decay (формальное
  ядро спектральной теории grokking, arXiv:2609.26679).
- Правило планировщика: для целевого времени генерализации T*
  выбирать η·λ ≥ ln(r₀/ε)/T*; при фиксированном η (кап 1/L,
  R347) это задаёт weight decay λ — ещё один гиперпараметр
  выведен, а не настроен. Фазовая геометрия: слишком большое
  λ (ηλ > 1) — расходимость (условие ηλ ≤ 1 в теореме).

## 8. Мета-закон роста: конус и насыщение

- Конус (frontier_cone_inductive):
  F(t+1) ≥ ρF(t) + γC(t) ⟹ C₀(1+γk)^T ≤ C_T.
- Насыщение (pl_gap_lower_trunc):
  C_T ≤ C* − (1−σ)^T·(C*−C₀).
- Совместимость (`cert_horizon_bound`): логарифмический
  горизонт — взлёт и потолок совместимы только если
  (1+γk)^(T−1) ≤ σC*/((γk+σ)C₀); явная форма (R349,
  `cert_horizon_log_bound`): T ≤ 1 + [ln(σC*) −
  ln((γk+σ)C₀)]/ln(1+γk) — чем сильнее конус, тем короче
  совместимый горизонт.
- На состоянии: `StateBinding` — C(t) = (S t).capability,
  G(t) = growGain; конус на реальной траектории состояний.
- Каскад: `sustained_takeoff_trunc`, `growth_dichotomy`,
  `elasticity_chain`, `saturation_limit`.

## 9. Капстоун: HAGI-синтез на семействе доменов

- `HAGICert` (ArchitectureTheorem, Fin I — произвольное
  семейство доменов):

```
взлёт:   C₀(1+γk)^T ≤ C_T
потолок: C_T ≤ C* − (1−σ)^T(C*−C₀)
риск:    ∀ домен i:
         Σₜ risk(t,i) ≤ T·best(i) + R + ε₀/(1−ρₑ)
```

  (`hagi_synthesis`; риск-часть — `universality_longhorizon`.)
- Свидетели не-вакуозности: `trunc_nonvacuous`,
  `certifiedHAGI_nonvacuous`, `coupledHAGI_nonvacuous`,
  `masterhagi_growth_witness`, `cert_horizon_witness` —
  все структуры предпосылок населены конкретными
  траекториями.

## 10. Интернализация инсайтов и инсайт-канал

- `insight_kl_descent`: KL-зазор как сертифицированный
  прирост; `forgetting_kl_bound` — забывание ограничено.
- `liveness_two_axis`: цикл не замерзает, пока жива любая
  ось (консенсус/новизна); заморозка = честный стоп.

## 11. Контроллерные гейты (Runtime/ControllerGates)

- Variance gate: logitRange(f) масштабируется линейно при
  делении температуры; R²/8-граница контрактуется
  квадратично; перелёт R ≥ R̄ чинится точно τ = R/R̄
  (`variance_gate_contract`, `variance_gate_normalize`).
- Trust region: шаг (R/‖x‖)•x имеет норму ровно R и
  ближайший к x в шаре (`trust_region_proj_norm`,
  `trust_region_nearest`).
- Динамический роутинг: инжекция 1/√(2L) на ветвь даёт
  суммарную дисперсию v/2 независимо от глубины пути.

## 12. Направляющие константы (вместо гиперпараметров)

- η: аналитический `safeqpEtaMax` (не гиперпараметр);
- порог слияния: jensenGap-гейт (измеренный, не настроечный);
- ранг: MDL-критерий первого порядка;
- τ variance gate: R/R̄ (точный ремонт перелёта);
- горизонт: `cert_horizon_bound` (логарифмическая стыковка
  γk-взлёта и σ-насыщения);
- бюджет битов: water-filling `two_layer_equalize`.

## 13. Термостатный контроллер (Growth/Thermostat,
Probability/GibbsConcentration)

Отжиг T_t = T₀·α^t (0 < α < 1) как управляющий контур
селектора; все величины сходятся к пределам без настройки
гиперпараметров.

- Монотонность: `thermostat_monotone` — T_{t+1} ≤ T_t;
  `thermostat_tendsto_zero` — T_t → 0.
- Полярный Ньютон: `newton_step_descent` — итерация
  x ↦ (x+2)/3(x) монотонно спускается при x ≥ 1 и зажата
  1 ≤ newtonIter x₀ ≤ x₀ (`newton_iter_bracket`).
- Сертификат состояния: `hagi_certified_state` —
  ∃N ∀t≥N: stop ∧ gate ∧ концентрация ∧ ∃ε-репрезен-
  тативная точка (R412+R413).
- ЧЕТЫРЕ ЧИСТОТЫ вдоль отжига:
  - метрика: `certified_state_tv_tendsto` — TV → 0;
  - энергия: `certified_state_energy_tendsto` —
    ⟨E⟩_t → E*;
  - свободная энергия: `certified_state_free_energy_-
    tendsto` — F_t → E*;
  - энтропия (Нернст): `certified_state_entropy_tendsto` —
    S_t → 0;
  - избыток: `certified_state_excess_tendsto` —
    ⟨E⟩−F → 0.
- Энергетические флуктуации (R498): `gibbs_energy_variance_bound` — при `E* ≤ E ≤ E*+Δ` и зазоре `δ` дисперсия Gibbs-энергии не выше `Δ²·(n−1)·exp(−δ/T)` (R393 + R496). Кандидатный variance-stop: завершать дальнейшее охлаждение, когда эта верхняя граница ≤ заданного `ε_var` и остальные сертификаты состояния уже выполнены. Это гарантирует только малость флуктуаций выбранной энергии; влияние на task loss/качество необходимо измерить отдельно.
- Калориметрия: `certified_state_excess` —
  ⟨E⟩−F ≤ (Δ+T₀)·C·θ.
- Admission-гейт памяти: `admission_margin_sound` —
  ε_cert-запас = сертификат soundness: истинный выигрыш
  покрывает стоимость + риск.

## 14. Hedge-селектор и regret (Probability/MWU)

Мультипликативные веса как универсальный селектор;
температура = обратный learning rate (η = 1/T).

- Одношаговое зажатие потенциала: `mwu_potential_squeeze`
  — ηℓ_min ≤ −ln Z′ ≤ 2η⟨ℓ⟩ (hedge-ядро без рядов:
  (1+2x)(1−x) ≥ 1 ⟹ e^{−2x} ≤ 1−x).
- Телескоп: `mwu_uniform_squeeze` — потенциал кумулятивных
  потерь зажат с двух сторон при uniform-старте.
- √-балансировка: `mwu_sqrt_bound` — −ln W ≤
  2√(η⟨L⟩·ln n) при η⟨L⟩ ≤ ln n (равновесное геометри-
  ческое среднее R443-пары; классическая regret-структура).
- Гиббс = hedge: `gibbs_hedge_squeeze` — при η = 1/T
  (1/T)E_min ≤ −ln((1/n)Σe^{−E/T}) ≤ 2(1/T)⟨E⟩.
- Репрезентативность: `mwu_representative` — выборка из
  hedge-распределения e^{−ηL} репрезентативна (мост
  Хёфдинг ↔ MWU; полный граф мостов: 4 вертикали,
  все 6 пар).

## 15. PAC-Bayes мост (Probability/GibbsConcentration)

Тождество Катони замыкает термодинамику и PAC-Bayes.

- Log-декомпозиция веса: `gibbs_weight_log_decomp` —
  ln(ρ_v·n) = ln n − ln Z − E_v/T (вес = сложение
  случайности, нормировки и энергии).
- KL-тождество Катони: `gibbs_katoni_kl` —
  KL(ρ‖unif) = −ln Z − ⟨E⟩/T + ln n; вместе с
  R422 (KL = ln n − S) даёт F = ⟨E⟩ − T·S — гиббсовская
  свободная энергия выведена из PAC-Bayes.

## 16. Ядро теории информации
(Probability/GibbsConcentration)

- Второй закон в общем виде: `finite_kl_nonneg` —
  KL(ρ‖γ) ≥ 0 для любых распределений (ln u ≤ u−1
  почленно с u := γ/ρ).
- Log-sum: `log_sum_ineq` (+ `_on` на подмножествах) —
  A·ln(A/B) ≤ Σa·ln(a/b) (нормализация + R447).
- Обработка данных: `kl_data_processing` —
  KL(Tρ‖Tγ) ≤ KL(ρ‖γ) для любого сжатия T
  (fiber-разложение + log-sum по слоям).
- Выпуклость: дуга R454–R457 — вогнутость ln →
  выпуклость x·ln x → скалярная x·ln(x/y) →
  KL по первому аргументу.
- Арифметика совместных: `kl_product_additive`
  (KL аддитивен на произведении), `entropy_subadditive`
  (S(joint) ≤ S₁+S₂), `entropy_chain` (цепное правило
  Шеннона), `joint_entropy_ge_marginal` (условная
  энтропия ≥ 0), `mutual_info_nonneg` (I ≥ 0).
- Равновесие: `gibbs_free_energy_identity` —
  F = ⟨E⟩ − T·S на Гиббс-мере.

## 17. Active-Inference вертикаль
(RAG arXiv 2607.13612)

- Прокси-дихотомия: `proxy_cert_preserved` /
  `proxy_cert_lost` — нижняя оценка энтропии
  сохраняет surprise-сертификат по построению,
  верхняя строго теряет; `gibbs_cert_bridge` — мост
  к Гиббс-равновесию (R462).
- Зазор суррогат/истина: `gap_decomposition` +
  `gapII_nonpos` + `gap_graceful` — три источника
  (miscalibration/bias/slack), смещение ≤ 0 для
  нижних прокси, линейная деградация.
- Компаундинг: `compounding_bound` / `compounding_sq`
  — e_H ≤ L^H·e₀ и e_H² ≤ (L²)^H·e₀²; MPC
  horizon-one обнуляет.
- EFE-потолок: `efe_ceiling` — G = P − I ≤ P;
  state-epistemic gap = взаимная информация.
- Амортизированная политика:
  `amortized_policy_bound` — суррогатный argmin при
  равномерном зазоре c исполняет в 2c от оптимума.

## 18. Pinsker-семейство и TV-дуальность
(Probability/GibbsConcentration)

- Капстоун MWU: `mwu_regret_regimes` —
  −ln((1/n)Σe^{−ηℓ}) ≤ max(2√(η⟨ℓ⟩·lnn), 2η⟨ℓ⟩);
  η = √(lnn/⟨ℓ⟩) даёт классический 2√(⟨ℓ⟩·lnn).
- Верхнее TV: `tv_le_pos_part_kl` — TV ≤ Σ_{q<p}
  p·ln(p/q). МАТАН-ЛОВЛЯ: линейное KL ≥ TV неверно
  (контрпример 0.368 < 0.4 — Пинскер требует √).
- Бхаттачарья: `bhattacharyya_cauchy` — BC ≤ 1
  (Коши-сумм); `one_minus_bc_le_half_kl` —
  1−BC ≤ KL/2 (per-v t−1 ≤ t·ln t).
- Пинскер: `pinsker_sqrt_kl` — TV ≤ √(KL)
  (тождество |p−q| = |√p−√q|(√p+√q) + Коши);
  `neg_log_bc_le_half_kl` — BC ≥ e^{−KL/2};
  `tv_le_sqrt_one_minus_exp` — Бретаньоль–Юбер
  TV ≤ √(1−e^{−KL}) (точнее при большом KL).
- Дуальность: `tv_dual_abs` — |E_p f − E_q f| ≤ TV
  для любой 0 ≤ f ≤ 1 (расщепление + f → 1−f).
- Совместная выпуклость: `kl_joint_convex` —
  классическое замыкание ядра инфо-теории.

## 19. Дониер-Варадхан и Cramér-вертикаль
(Probability/GibbsConcentration)

- ДВ-нижняя грань: `kl_variational_lower` —
  KL ≥ E_p f − ln E_q e^{f} (софтмакс-наклон
  r = q·e^f/Z + R447); точность:
  `kl_dv_attained` (f := ln(p/q), Z = 1);
  наклон-констант: `kl_chernoff_tilt`.
- Cramér-вертикаль (2401.01148, NeurIPS 2024):
  `cramer_tilt_kl` (пороговая форма),
  `cramer_sup_le_kl` (sup-форма через csSup_le),
  `cramer_cgf` (CGF-форма с центрированием),
  `subgauss_dev_kl` (λ*-подстановка, (E−μ)²/2σ² ≤
  KL — без дифф-исчисления).
- События и масштаб: `markov_finite` (t·p({g≥t}) ≤
  E_p g), `chernoff_event` (p({g≥t}) ≤ e^{−λt}·
  E_p e^{λg}), `exp_tilt_interpol` (интерполяция
  через R454 — 3 случая), `mean_shift_tv`
  (|E_p g − E_q g| ≤ (b−a)·TV через R473),
  Hellinger: `hellinger_sq_eq_one_minus_bc`,
  `hellinger_le_half_kl`.

## Честные границы (что НЕ выведено)

- `h_emp_grow`, `h_emp_smooth`, `h_emp_lip` — измеряемые
  посылки stage-теорем; их вывод из Core-слоя открыт
  (merge и compress закрыты мостами).
- γ-дефицит mixer.gain→0 — не закрыт (контрпримерная зона).
- GrandSynthesis пункты 2/4 — плоские передачи посылок,
  не вывод.
- Полная Fannes-граница; anytime-Freedman (M∧V-форма).
- Lean↔Runtime property-тесты — требуют torch-рантайма.
