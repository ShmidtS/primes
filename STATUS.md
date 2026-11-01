# STATUS — состояние формализации HAGI

## Корпус

- 429 Lean-модулей в `Hagi/`; 3718 деклараций (Freeze);
  2909 theorem/lemma; 0 sorry; 0 кастомных аксиом
  (все теоремы: [propext, Classical.choice, Quot.sound]).
- CI (16 гейтов, `scripts/ci.sh`): LINT, MathlibPin, DupLint,
  NsLint, DocLint, LayerLint, Freeze, AssumptionScan,
  StatusLint, CHALLENGE (Gen-3: `master_hagi_challenge_v3`),
  STMDUP, MACHINEDIFF, ALLAXIOMS — все PASS.

## Доказанные результаты (главные формулы)
- **KL ≥ 0** (`kl_nonneg`): Σ q log(q/p) ≥ 0 при q ≥ 0, p > 0
  (лемма о хорде log x ≤ x − 1).
- **Pinsker** (`PinskerTV`): TV(p,q) ≤ √(KL(p‖q)/2), через
  коэффициент Бхаттачарьи Σ√(pᵢqᵢ) ≤ 1 (Коши–Шварц).
- **Fannes-непрерывность**: условные и сглаженные формы
  (`DiscreteFannes`, `FannesSmooth`, `NernstFannes`).
- **Полный инфо-канон**: единые Prelude-определения
  (klDef/tvDef/entDef/softDef); все 16 прочих примитивов
  проекта — rfl-мосты к канону; замыкающий мост
  `softDef_eq_exp_sub_lse`: softmax = exp(z a − lse z).
- **Гиббс+Нернст** (`gibbs_nernst`): у Гиббс-распределения с
  δ-зазором S(p_T) ≤ t̂·log d + (1+t̂)·log 2 при
  t̂ = (d−1)e^{−δ/T} — третий закон с экспоненциальной
  скоростью; T → 0⁺ ⟹ S → 0.
- **Ляпунов-телескоп** (`lyapunov_gain_noise`):
  V(t+1) ≤ V t − gain t + noise t (t < T) ⟹
  V T ≤ V 0 − Σ gain + Σ noise.
- **Терминация** (`lyapunov_termination_fin`):
  Emin ≤ E t, E(t+1) ≤ E t − ε ⟹ k ≤ (E 0 − Emin)/ε.
- **Рекуррента** (`recurrence_upper`):
  x(t+1) ≤ ρ·x t + c, ρ ∈ [0,1) ⟹
  x T ≤ ρ^T·x 0 + c·(1 − ρ^T)/(1 − ρ).
- **Эластичная цепочка** (`elasticity_chain`, horizon-форма):
  (1 + e_t)·x t ≤ x(t+1) ⟹ x T ≥ x 0·∏_{t<T}(1 + e_t).

### L1. Ядро конуса (Перрон)
- **Конус = уравнение собственного вектора**
  (`cone_eigenvector_iff`): вектор (1, k) — собственный
  вектор матрицы M = [[1,γ],[β,ρ]] с собственным значением
  1 + γk РОВНО при β = γk² + (1−ρ)k. Скорость взлёта
  1 + γk — корень Перрона конусной динамики.
- **Точный рост Перрона** (`cone_perron_growth`): при
  равенствной динамике C(t+1) = C t + γ·D t,
  D(t+1) = ρ·D t + β·C t, старте на границе D 0 = k·C 0:
  C T = (1+γk)^T·C 0 и D T = k·C T для всех T.
- **Шаг конуса** (`cone_step`): при γk ≤ ρ и
  γk² + (1−ρ)k ≤ β инвариант k·C t ≤ D t сохраняется.
- **Взлёт как следствие** (`ratio_takeoff`,
  `takeoff_from_certificate`): конус + C(t+1) = C t + γ·D t
  ⟹ C 0·(1+γk)^T ≤ C T (трёхстрочные следствия
  эластичной цепочки; для цепочки несогласия —
  C 0·(1 + β⁴κ·k)^T ≤ C T).

### L2. Квантование и энергия
- **Единый квантователь решётки** (`gridQ`):
  Q_Δ(x) = Δ·round(x/Δ); |Q_Δ(x) − x| ≤ Δ/2 (без
  ограничений на x), идемпотентность Q(Q(x)) = Q(x),
  образ = решётка Δℤ.
- **Комозитный шаг единой теории** (`unified_step_certificate`,
  System/UnifiedStep): веса Гиббс-ансамбля w = softmax(−L/Tt)
  — строго положительное распределие (канонич. леммы
  `softDef_pos`, `softDef_sum_one`), точка смешения
  m = Σ wᵢθᵢ, квантованное обновление
  Q_Δ(m − γ·g) с ошибкой ≤ Δ/2 — охлаждение × ансамбль ×
  решётка в одном сертификате.
- **Квантованный спуск** (`quantized_descent_telescope`):
  x(t+1) = Q_Δ(x t − γ·g t) ⟹
  x T ≤ x 0 − Σ γ·g t + T·Δ/2 — цена квантования Δ/2/шаг.
- **Тернарное кодирование**: 5 тритов в байт (243 ≤ 2⁸,
  инъективность), ошибка округления ≤ s/2.
- **Ландауэр-мосты** (через h_emp-посылки):
  F ≤ B/cUnit (written_bits_cap);
  n ≤ B/(cUnit·log 3) (тернарный рост весов);
  cUnit·(k+F) ≤ B на цикл, Σ по прогону ≤ Etot;
  потолок жизни T ≤ (E 0 − Emin)/d 0 — выведен и достижим
  (witness); Парето-оптимум разбиения бюджета
  (Jeon–Van Roy): максимум качества при минимальном объёме.

### L2. Гиббс / зеркальный спуск
- **Вариационное неравенство** (`free_energy_variational`):
  E_q[U] − KL(q‖p) ≤ log Σ p·e^U для всех q на симплексе.
- **Оптимальность Гиббс-весов** (`gibbs_optimal_bound`):
  ⟨L⟩_q + T·Σ q log q ≥ −T·log Σ e^{−L/T} —
  темперированный софтмакс минимизирует
  энтропийно-регуляризованные потери; равенство на
  softmax(−L/T).
- **MWU-телескопирование**, тождество Катони
  KL(ρ‖unif) = −ln Z − ⟨E⟩/T + ln n; свободная энергия
  F = −T ln Z = ⟨E⟩ − T·S.

### L2. Пробы / предобучение
- **Инверсия Адамара-проб** (`hadamard_probe_inversion`):
  k оценок восстанавливают credit-вектор точно
  (Δ = c⁻¹·Hᵀg).
- **Парсеваль** (`orthonormal_mulVec_isometry`):
  |Q·ᵥδ|ᵢ ≤ ‖δ‖₂ для ортонормированных строк.
- **Нижняя граница проб** (`probe_lower_bound`):
  k измерений необходимы (finrank).
- **Замкнутая форма CE-возмущения** (`ceLogit_move_change`).
- **LR↔batch эквивалентность** (`lr_batch_equivalence`,
  Smith+ 1711.00489): шумовой бюджет η·noiseEps
  инвариантен при (η,m) → (kη, k²m).

### L2. Концентрация
- **Хёфдинг**: двухсторонние хорошие точки; при
  2|K|θ < 1 существует v: ∀k |d k v| < ε_θ =
  (b−a)√(ln(1/θ)/2); масса хороших точек ≥ 1 − 2|K|θ.
- **Азума**: P[ΣX ≤ −Δ] ≤ exp(−Δ²/(2n)).
- **Фридман** (дисперсионно-адаптивная):
  P[ΣX ≤ −Δ] ≤ exp(−Δ²/(2(V + bΔ/3))).
- **Anytime-лестницы Фридмана** (односторонняя и
  двусторонняя): P[∃ j ≤ T: …] ≤ Σ_j exp(−r²/(4(V+c·r))).
- **Сертифицированный takeoff** (`certified_gainprod_takeoff`):
  все T margins ⟹ takeoff с уровнем ≥ 1 − 2T·e^{−2nε²};
  размер выборки n ≥ ln(2T/α)/(2ε²) даёт уровень 1 − α.
- **Конденсационный конвейер**: CGF(subGauss σ²) +
  anytime-bad-set ≤ α ⟹ dead layers + стоимость каркаса
  ≤ 2σ²·ln(T/α).

### L2. Спектральная теория (порт FLYWHEEL, Apache-2.0)

- Матрицы Адамара (H₂H₂ᵀ = 2I), произведения Кронекера,
  DFT-3 над 𝔽₃ и вещественный лифт 6×6.
- **Eckart–Young** (нижняя оптимальность низкорангового
  приближения), **Weyl**, **Courant–Fischer**,
  Newton–полярная итерация, спектральный хвост.
- **Ранг-рост** (`rank_orthogonal_growth`,
  arXiv:2607.14571): k новых линейно независимых строк
  Якобиана, ортогональных старым ⟹ rank = rank M + k;
  обновления в спане новых направлений не вмешиваются в
  старые домены (SafeQP ε = 0).

### L2. Безопасный шаг (SafeQP)
- **Спуск** (`safeQP_descent`): E(w + ηd*) ≤ E − η‖d*‖²/2
  при ε-ограничениях ⟨gᵢ, d⟩ ≥ −εᵢ; существование и
  единственность d*; стохастический/адаптивный варианты;
  аналитический потолок η (`safeqpEtaMax`).
- **Трёхвалютная MDL-цель**, variance gate (R²/8
  контрактируется квадратично), проекция на trust region.
- **Мост h_emp-троицы** (полностью выведена):
  h_emp_lip: |E(w)−E(q)| ≤ κ‖w−q‖ (MVT, κ = sup‖∇E‖);
  h_emp_smooth: E(q+dir) ≤ E(q) + ⟨∇E,dir⟩ + L‖dir‖²/2
  (Newton–Leibniz + Коши–Шварц);
  h_emp_grow: growEnergy ≤ energy − η‖d*‖²/2.

### L3. Единая динамика траектории (StageSemantics)
- **Платный рост с конструктивной честностью цены**
  (`growSeq`): эффекты вычисляются из текущего состояния
  (growGain = α·C t, growCost = μ·C t); инвариант
  0 ≤ μ·C t несётся в типе.
- **Закон роста** (`growSeq_capability`):
  C t = (1+α)^t·C 0 по честным переходам.
- **Бюджетный ledger на той же траектории**
  (`growSeq_budget_ledger`):
  budget(t) + μ·Σ_{i<t} C i = budget(0).
- **Двухшаговая совместимость** (`grow_two_step_consistent`):
  C 2 = (1+α)²·C 0 — зеркальное опровержение
  противоречия фиксированных эффектов.
- **Obstruction (регрессионный тест)**
  (`full_cycle_two_step_growth_inconsistent`): при
  копируемых effects два шага геометрического роста
  дают False — дефект старой модели зафиксирован.
- **Явная модель шага** (`SoftmaxStep`): h_emp_smooth
  выведен из logit-CE модели (L = 1/2); телескоп T шагов:
  logitCE(w_T) ≤ logitCE(w_0) − Σ η_t d_t²/2.

### L3. Насыщение и термостат
- **Насыщение**: C T ≤ C* − (1−σ)^T·(C* − C 0).
- **Полоса роста**: G t ≤ b(1−σ)^t ⟹
  C T ≤ C 0 + (b/σ)(1 − (1−σ)^T) ≤ C 0 + b/σ (потолок);
  цель выше потолка недостижима ни на каком горизонте.
- **Нижняя гарантия**: G t ≥ b(1−σ)^t ⟹
  C T ≥ C 0 + (b/σ)(1 − (1−σ)^T); таймер цели в
  лог-форме: T ≥ ln(1 − σ(C*−C 0)/b)/ln(1−σ) ⟹ C* ≤ C T.
- **Двойной потолок** (`dual_ceiling`):
  C T ≤ C 0 + b/σ ∧ C T ≤ γ·D̄/α одновременно.
- **Дихотомия роста** (`growth_dichotomy`): взлёт или
  потолок.

### L3. Мост к AR-экспрессивности (Sidon, arXiv:2610.17283)
- **Sidon-множества**: `SidonSet` (парные суммы различны с
  точностью до перестановки), `sidon_diff_eq` — Sidon ⟹
  положительные попарные разности различны;
  `sidon_pair_diff_injective` — для строгой нумерации вершин
  шагами из Sidon-сета отображение рёбер (i,j) ↦ t_j − t_i
  инъективно: бесконфликтное кодирование весов схемы одним
  общим вектором параметров (ядро сериализационной техники
  статьи); свидетель `sidonSet_golomb4` = {0,1,4,6}.
- **Time-invariant разделение параметров HAGI**
  (`advance_weights_shared`): переход сохраняет вектор
  весов между циклами — та же структура, что AR-нейрон
  статьи; по её Theorem 1/2 параметр-шеринг не ограничивает
  вычислительную мощность: time-invariant семантика
  Trajectory способна симулировать любую σ-схему.

### L3. Термодинамическая ось охлаждения (Нернст)
- **Нернст-скорость Гиббс-значения** (`gibbs_value_nernst_bounds`):
  для любого поля потерь L на конечном пространстве существует
  достигаемый минимум m и двусторонняя оценка
  `m − T·log n ≤ −T·log ∑ e^{−Lᵢ/T} ≤ m` — точность достижения
  глобального минимума имеет радиус T·log n: при T → 0 Гиббс-значение
  стремится к минимуму с экспоненциальной концентрацией весов.
  Исследовательская база: Hajek 1988 (необх./дост. условие
  сходимости отжига), Catoni–Cot 1998 (кусочно-постоянные
  оптимальные расписания). Вместе с `gibbs_optimal_bound`
  (Variational) задаёт термодинамическую ось обучения HAGI:
  расписание температуры определяет качество на конечном горизонте.
- **Тождество ансамбля E = F + T·S** (`gibbs_free_energy_identity`):
  ожидаемая потеря Гиббс-ансамбля раскладывается точно
  `∑ wᵢ·Lᵢ = −Tt·log Z − Tt·∑ wᵢ·log wᵢ` — энергия = свободная
  энергия + T·энтропия. Ядро термодинамической семантики HAGI:
  качество исполняемой смеси (`unified_step_certificate`)
  связано со свободной энергией (`gibbs_optimal_bound`) через
  энтропийный член.
- **Максимум энтропии** (`shannon_entropy_le_log_card`): для
  любого строго положительного распределения на конечном ι
  −∑ wᵢ·log wᵢ ≤ log |ι| (Jensen; максимум — равномерное).
- **Качество исполняемой смеси** (`gibbs_mixture_quality`):
  композиция трёх сертификатов (E = F + T·S, S ≤ log n,
  V_T ≤ m) даёт ∑ wᵢ·Lᵢ ≤ m + Tt·log n — расписание
  Tt·log n ≤ ε доставляет ε-оптимальность РЕАЛЬНО
  исполняемой Гиббс-смеси (`unified_step_certificate`).
  Полная термодинамическая цепочка HAGI замкнута:
  расписание охлаждения → свободная энергия → энергия
  исполняемой смеси.
- **Термическое размытие** (`thermal_blur`):
  log wᵢ − log wⱼ = (Lⱼ−Lᵢ)/T — точное лог-отношение
  Гиббс-весов; чтобы различать понятия с зазором s с
  лог-точностью τ, температура обязана быть T ≤ s/τ —
  термодинамическая НИЖНЯЯ граница расписания охлаждения:
  нагрев стирает различимость направлений.
- **Охлаждение раскрывает различимость** (`thermal_reveal`):
  при зазоре ≥ s и T ≤ s/τ лог-расстояние весов ≥ τ —
  нижняя оценка (дополнение к corridor): при T → 0
  различимость растёт; вместе с welch_min_dimension —
  термодинамическая развертка вместимости.
- **Время раскрытия** (`reveal_horizon`): при
  геометрическом охлаждении Tₜ = T₀ρᵗ шаг t с Tₜ ≤ s/τ
  раскрывает зазор s (лог-точность τ) — момент раскрытия
  логарифмичен по T₀τ/s: термодинамические часы
  различимости понятий.
- **Момент раскрытия существует** (`reveal_time_exists`):
  ∀ s, τ > 0 ∃ t: T₀ρᵗ ≤ s/τ — вместе с reveal_horizon:
  каждое понятие с конечным зазором будет раскрыто
  (термодинамические часы полны).
- **Динамическая пара** (`cooling_schedule_pair`): ∃t с
  ОДНОВРЕМЕННЫМ раскрытием (Tₜ ≤ s/τ) и ε-качеством
  (Tₜ·log n ≤ ε) — часы и бюджет сходятся в min-окне.
- **ε-горизонт PL** (`pl_sufficient_horizon`):
  (1−μ/L)^t·(E 0−E*) ≤ ε ⟹ E t − E* ≤ ε — достаточное
  число шагов до точности ε.
- **RobustnessLaw (Bubeck–Li–Sellke 2110.06401, ядро;
  Wu–Huang–Zhang 2202.11592)**
  (`Hagi/Pretraining/RobustnessLaw.lean`):
  robust_interpolation_lipschitz_floor — архитектурно-
  независимая нижняя граница липшицевости интерполятора
  L ≥ |Δy|/|Δx|; no_lipschitz_interpolator_of_steep —
  крутые данные И L-липшицева интерполяция несовместимы
  (робастность требует сверхпараметризации);
  lipschitz_floor_of_noisy_labels — шум σ при шаге ≤ δ
  требует L ≥ σ/δ (количественное ядро);
  noisy_interpolation_step_cap — мост к обучению:
  L ≥ σ/δ + стабильность η·L ≤ 1 ⟹ η ≤ δ/σ (robustness
  caps learning rate);
  robust_slows_learning — D ≤ T·η·G + cap η ≤ δ/σ ⟹
  T ≥ D·σ/(δ·G) (робастность замедляет обучение
  количественно);
  robust_budget_floor — мост к бюджету: T·c ≤ B ⟹
  B ≥ c·D·σ/(δ·G) (шумные данные дорожают количественно);
  robust_spacing_bound — плотная выборка ограничивает
  колебания L·δ.
- **Дифференциальные тесты машины 
  паттерн qwenputer fuzz.py)**: scripts/MachineDiffTest.py +
  гейт MACHINEDIFF в CI — Python-порт ReferenceMachine на 2000
  случайных конфигурациях; все 5 формальных законов
  подтверждаются численно (1923 certified, 77 вне
  ledger-условия теоремы — легальные skip).
- **RoPE, уровень 2 — ОТНОСИТЕЛЬНОСТЬ (ядро RoPE)**:
  ropeInner (Re-часть (star w_m·u)·(w_n·v)),
  rope_shift_invariant: одновременный сдвиг d обеих
  позиций НЕ меняет внутреннего произведения
  (star w_d·w_d = 1, d-экспоненты сокращаются) —
  взаимодействие токенов зависит только от ВЗАИМНОГО
  расположения. Полное ядро RoPE формализовано.
- **Flow Matching №41 уровень 2**: flow_const_velocity —
  скорость пути d/dt flowPath = x₁ − x₀ НЕ зависит от t
  (постоянная скорость прямолинейного потока — основа
  constant-velocity matching-цели; HasDerivAt-цепь
  const_mul/const_add + simpa).
- **DDPM №39 уровень 2**: ddpm_recover — идеальный
  noise-predictor восстанавливает x₀ ТОЧНО:
  (x_t − √(1−ᾱ)·ε)/√ᾱ = x_0 при корректном ε (тождество
  реконструкции denoising-петли).
- **Perceiver №54 уровень 2**: perceiver_saving_mono —
  при фиксированном m экономия бутылочного горлышка РАСТЁТ с
  удлинением входа n (каждый новый токен увеличивает
  преимущество; unfold + ring-разложения + omega).
- **СИНТЕЗ cost-семейства**:
  Unified/CostComposition — гибрид MoD(№55)×SWA(№56)×глубина:
  hybrid_cost_lt (L·k·(2w+1) < L·n² — механизмы экономии
  складываются в одну цепочку), hybrid_ratio_le (относительная
  стоимость ≤ (k/n)·((2w+1)/n) — произведение факторов
  экономии).
- **BYOL (источник №87**: self-distillation
  без негативов (2006.07733): cosS (с вырожденным
  0-случаем), CSCarrier (CS как контракт |cos|≤1 —
  производитель будущий Cauchy-модуль), bl_bounds
  ([0,2]), bl_anti, bl_zero_at_perfect,
  cos_scale_inv (масштаб-инвариантность при s·t>0 —
  КОНТРПРИМЕР st<0 пойман до коммита: cos антисимметричен
  знаку); bl без variance-давления — контраст с VicReg.
- **ProtoTrajectory**: полная цепочка
  execution × measurement × certificate замкнута:
  proto_loss_mono / proto_loss_telescope /
  proto_progress_bound (loss-канал протокола вдоль
  реальной commit/hold-траектории: монотонность, точный
  телескоп, суммарный прогресс ≤ начального loss) +
  proto_capa_mono (capability-канал НЕ убывает вдоль
  траектории — инверсия loss-монотонности). Все
  величины происходят из протокола и исполнения.
- **MeasureProtoаудит №5 P1/E)**: протокол
  измерений — происхождение как ТИП: MeasureProto
  (loss/risk/capability/cost — поля-функции Params→ℝ),
  machineProto (инстанс машины: loss = energy — реальное
  вычисление), machineProto_gap (dStep QuadGate = loss(θ)
  − loss(step) — rfl-тождество с протоколом),
  machineProto_capa_mono (capability 1/(1+E) монотонна
  по реальной энергии — каналы согласованы).
- **GradCentralization (источник №86**:
  центрирование градиента (2004.02861): gc (реюз
  centered), gc_zero_sum (реюз sum_centered),
  gc_pythagoras (ТОЧНЫЙ Пифагор ‖g‖² = ‖gc‖² + n·μ²),
  gc_norm_le (центрирование не увеличивает норму),
  gc_const_zero (константный градиент → 0).
- **certified_loop_allусиление)**:
  покомпонентный floor держится на ВСЕХ промежуточных
  состояниях сертифицированной цепочки (не только
  финально). Проверки чистоты: дублей длинных докстрингов
  0 (hash-скан), легаси-нарратива 0, группировка
  Unified-ядра отражает построение.
- **Grokfast (источник №88**: ускорение
  гроккинга (2505.15833): gLow/gHigh (EMA-разложение
  градиента — реюз ema из ModelSoup), decompose (ТОЖДЕСТВО
  gL+gH=g), ampDir + amp_recompose (усиление меняет ТОЛЬКО
  низкочастотную часть — шум не усиливается),
  const_grad_fix (на постоянном градиенте gL=g, gH=0 —
  стационарный сигнал не искажается).
- **QuadUnifyаудит №5 P3-сведение)**:
  квадратичные линии УНИФИЦИРОВАНЫ: quadE_eq_energy и
  quadGrad_eq_grad (DescentCoreQuad ≡ ReferenceMachine —
  формы совпадают точно), machine_one_step_zero (η=1:
  один шаг машины — точно в оптимум). Сертификаты машины
  (QuadGate/Trajectory/Budget) и Objective-контракт
  говорят об ОДНОЙ величине.
- **VicReg (источник №85**: variance-hinge
  антиколлапс (2105.04906): vh = max 0 (γ−√popVar) (реюз
  popVar из NoiseTemperature), pv_nonneg, vh_nonneg,
  vh_zero (var ≥ γ² ⟹ ноль, любой знак γ), vh_anti
  (СТРОГОЕ убывание по var на АКТИВНОЙ зоне — честная
  посылка vh>0; контрпример «оба нуля» пойман до коммита).
- **Mixup (источник №84**: Zhang (1710.09412):
  mixLabel (выпуклая комбинация меток), mixLabel_dist
  (симплекс замкнут — смесь распределений — распределение),
  mixScore, mix_loss_le (Jensen: выпуклый лосс на
  смиксованном счёте ≤ смеси лоссов — реюз
  soup_loss_le_avg из ModelSoup на Fin 2).
- **NTXent (источник №83**: SimCLR
  (2002.05709), бинарный InfoNCE: nt2 m = log(1+e^{−m}):
  nt2_nonneg, nt2_le_log2 (m≥0 ⟹ ≤ log 2), nt2_anti
  (СТРОГО убывает по марже), nt2_zero_margin (m=0 —
  порог неразличимости log 2). Контрастная пара к
  TripletLoss №82 (hinge vs log-хижина).
- **DescentCoreDiag**: второй реальный
  инстанс гладкости: ВЗВЕШЕННАЯ квадратичная
  E=½Σaᵢ(wᵢ−yᵢ)²: diag_descent_eq (ТОЧНОЕ тождество),
  diag_descent_le (L-гладкость с L = любая верхняя
  граница весов — НЕтривиальная константа, выведена
  поточечным aᵢ ≤ L; контракт DescentCore проверен при
  произвольном L, не только L=1).
- **TripletLoss (источник №82**: FaceNet
  (1503.03832): tl = max 0 (d⁺ − d⁻ + m): tl_nonneg (hinge),
  tl_zero (маржа выполнена ⟹ ноль), tl_pos (нарушение ⟹
  строгий сигнал), tl_le_hinge (граница при d±≥0 —
  контрпример dap<0 пойман до коммита), tl_mono_pos/neg
  (правильные направления тяги: ближе позитив / дальше
  негатив).
- **QuadBudget**: леджер сертифицированной
  траектории: trajDropSum (ТОЧНЫЙ телескоп Σ(E_t−E_{t+1})
  = E₀−E_T — разности РЕАЛЬНЫХ энергий), trajDropBound
  (Σ certified-убываний ≤ E₀ — прогресс конечен; телескоп-
  граница StepContract выведена на реальной траектории),
  commitInd/commitCount, budgetLedger (все hold ⟹
  #commits = 0 — бюджет нетронут), commitCountBound
  (#commits ≤ T при любой траектории).
- **QuadTrajectoryаудит №5 P3)**:
  многошаговый сертифицированный цикл над вычисленным
  gate: gateStep (commit/hold-ветвление), gateTraj
  (итерация), gateStep_mono (энергия не возрастает на
  любом шаге: commit — строго, hold — равенство),
  gateTraj_mono (кумулятивная монотонность по T),
  gateStep_drop (честный телескоп: разность РЕАЛЬНЫХ
  энергий), gateStep_pos (строгое убывание при открытом
  gate — реюз quad_gate_commit). Нетривиальный
  многократный цикл с реальным изменением параметров.
- **QuadGateаудит №5 P1/P3)**: CommitGate
  ЗАМКНУТ на эталонной машине: machineCert — GateCert,
  где ВСЕ поля вычислены (V=energy a w, dStep=machineGap,
  quant=quantLift √(2X)z+z²/2 из решётки), machine_energy_lift
  (E(градиент+квантование) ≤ X + quantLift — реюз
  machine_energy_bound), quad_gate_commit: gate открыт ⟹
  РЕАЛЬНАЯ энергия полного машинного шага СТРОГО убывает —
  ни одного постулированного поля, всё из весов.
- **CapabilityLocalаудит №5 P1/K8)**:
  геометрический рост ПОЛЕВОЙ capability из ЛОКАЛЬНОГО
  условия: capability_geometric_of_local (ΔΓ_t ≥ α·Γ_t +
  рекуррентность поля ⟹ Γ_T ≥ (1+α)^T·Γ₀ — чистая
  индукция, внешний C-канал MasterHAGI не нужен;
  привязка к (S t).effects.growGain реальна),
  capability_strict_first (строгий рост на первом шаге —
  нетривиальный witness).
- **riskLim-дефантомизацияаудит №5 P1)**:
  CertifiedTransition получил активное поле riskBound
  (S'.protectedRisk − S.protectedRisk ≤ riskLim) — лимит
  риска теперь ГАРАНТИРУЕТСЯ типом, а не является
  неиспользуемым параметром. Конструктор дополнен;
  все потребители (MasterHAGICoupled, LinkedWitness,
  CertifiedTrajectory) — гипотезы, остались валидны.
- **CI-фикс H2аудит №5)**: финальный гейт
  в конце ci.sh — поздние проверки (AxiomCheck,
  ChallengeCheck, StatementDupCheck, MachineDiffTest)
  теперь ВЛИЯЮТ на exit code (ранее ранний PASS мог
  маскировать поздние FAIL — подтверждённый ложный-PASS
  дефект закрыт).
- **BlockNormаудит P1-RMSNorm)**: поблочная
  нормализация сохраняет ансамбль: global_eq_mean_blocks
  (глобальная дисперсия = среднее блочных — ТОЧНОЕ
  тождество), equal_blocks_global (равные RMS блоков ⟹
  глобальная нормализация = поблочной ПОТОЧЕЧНО — GroupNorm(3)
  сохраняет шаг 0 слияния без возмущения). Устранён
  семантический разрыв Merge×RMSNorm из аудита.
- **CommitGateаудит D TRD-GMS)**: инвариант
  ветвления вместо h_emp_grow: GateCert (V, dStep-контракт,
  gap≥0, quant, gen≥0), gate (win > loss — решаемое
  условие), commitProductive (gate=true ⟹ СТРОГОЕ убывание
  потенциала), holdSafe (rollback: Δ=0, parent-preserving),
  quant_bound_of_gridQ (Σ квант-ошибок² ≤ n·Δ²/4 — реюз
  gridQ_error). Условие продуктивности — ВЕТВЛЕНИЕ
  АЛГОРИТМА, не внешняя гипотеза.
- **DescentCoreQuadаудит #3/#8)**: первый
  НЕПОСТУЛИРОВАННЫЙ инстанс Objective: квадратичная
  машина E(w)=½Σ(w−a)²: quad_descent_eq (descent-лемма —
  ТОЧНОЕ РАВЕНСТВО, выведено алгебраически, L=1),
  quadObjective (все поля контракта доказаны),
  quadAligned (выравнивание — вычисление, не гипотеза),
  quad_one_step (η=1/L: ОДИН шаг попадает точно в оптимум
  a, E(a)=0 — сквозной witness: алгоритм реально меняет
  параметры и доказанно достигает цели), quad_drop
  (строгое убывание при x≠a).
- **GDN-фиксаудит P0)**: каноническая
  gated-форма gdnUpdate: S' = gS + β(v − gSk)kᵀ (остаток
  по ЗАТУХШЕМУ состоянию, как в оригинальной статье; при
  g=1 формы совпадают — старые теоремы сохранены) +
  gdn_onehot_interp: при one-hot и произвольных g, β —
  точная колоночная интерполяция (1−β)gS + β·v (β — мера
  перезаписи; обобщение точной записи g=β=1).
- **DescentCoreаудит #4/#1)**: семантический
  центр спуска: Objective (L-гладкость — descentLemma
  поле-контракт), aligned (‖dir‖² ≤ ⟨g,dir⟩),
  descent_drop: ЧИСТОЕ УБЫВАНИЕ f(x−η·dir) ≤
  f(x) − η(1−Lη/2)‖dir‖² при η ≤ 1/L — ВЫВОДИТСЯ из
  гладкости, h_emp_smooth больше не постулат потребителя.
- **SAM (источник №81**: Sharpness-Aware
  Minimization (2010.01412): norm2/ball, samW (worst-case
  лосс на ρ-шаре), sam_ge (sam ≥ L), ball_mono + sam_mono
  (вложение шаров ⟹ монотонность остроты по ρ),
  sam_flat (константа на шаре ⟹ нулевая острота — цель
  SAM: плоские минимумы устойчивы к квантованию).
- **TernaryGrad-мост**: SignSGD × Quantizer:
  sgn1_round, sgn1_grid_fix (gridQ 1 фиксирует знаковый
  градиент — тернарный вектор уже в решётке 1·ℤ),
  sgn1_zero_quant_error (ошибка квантования строго 0,
  не Δ/2), tern_grad_inner (⟨Q(sign g), g⟩ = ‖g‖₁ —
  композиция каналов компрессии без деградации сигнала).
- **DiffAttention (источник №80**: дифф-внимание
  (2410.05258): sm (softmax), sm_sum_one/sm_nonneg,
  sm_shift (СДВИГ-ИНВАРИАНТНОСТЬ: общий сдвиг логитов не
  меняет веса — key-bias сокращается в нормировке),
  noise_cancel (общий аддитивный шум самосокращается),
  diffW + diff_range (w₁−λw₂ ∈ [−λ,1] при λ≥0).
- **BatchSNR-углубление**: модель
  критического батча с издержками: batchGain (min(1,B/B*)),
  stepCost (α·B+β), gainPerCost; gain_decreasing_past_critical
  — при α>0, B₂>B₁≥B* прогресс/стоимость СТРОГО убывает
  (оптимум эффективности в B*; α=0-случай исключён — там
  эффективность постоянна, контрпример пойман до коммита).
- **SignSGD (источник №79**: 1-bit градиентная
  компрессия: sgn1 (тернарный знак), sign_inner_nonneg
  (⟨sign(g),g⟩ = ‖g‖₁ ≥ 0 — компрессия не переворачивает
  направление спуска), sign_inner_pos (строгий косинус при
  g≠0), sgn1_ternary ({−1,0,1} — совместимость с тритарным
  ядром), sgn1_fix + sign_idempotent (sign∘sign=sign).
- **RVCore (приоритет 2-ядро обзора**:
  бит-точное ALU-ядро RISC-V над UInt32: wordAdd_spec
  (toNat(w+w') = (n+n')%2³² — точный перенос),
  wordSub_spec (заём-обёртка), wordAnd_spec (Nat.land),
  wordAnd_idem, execDeterministic (CPU — функция: нулевая
  энтропия ошибки, основа RAM_Parity). wordAdd_spec зависит
  ТОЛЬКО от propext (конструктивная бит-арифметика).
- **DistillCert (приоритет 6 обзора**:
  сертификат консолидации: DistillCert (teacher/student/
  Δ/lip/dist2-прокси с честными полями), quant_pointwise
  (Δ/2-реюз gridQ_error), quant_L2 (‖Q(s)−s‖² ≤ n(Δ/2)²),
  consolidation_bound (|L(Q(student)) − L(teacher)| ≤
  Λ·(2n(Δ/2)² + 2·dbound²) — каналы квантования и
  дистилляции суммируются через (a+b)²≤2a²+2b²).
- **NCTheorem (приоритет 7 обзора**:
  ГЛОБАЛЬНАЯ теорема нейрокомпьютера: ncContract (мост
  NCInput → StepContract: decrease=сертификат,
  risk=riskSpend, budget=cost); nc_trajectory_bound
  (телескоп: Σd ≤ Φ₀−Φ_min+Σrisk на ncAdvance-траектории —
  реюз trajectory_convergence); nc_cpu_frozen_trajectory
  (процессор заморожен на ВСЕМ горизонте — индукция
  инварианта).
- **NeuralComputer (приоритет 4 обзора**:
  NCState — ЕДИНОЕ состояние нейрокомпьютера (φ, base,
  adapt, cpu, mem, E, R, B, C); ncAdvance — канонический
  переход; инварианты: nc_cpu_frozen (процессор заморожен
  rfl), nc_base_frozen (тритарная база консервативна),
  nc_mem_only_via_write (память — только адресуемая
  запись), nc_budget_ledger (точная бухгалтерия),
  nc_risk_mono (риск неубывающий) — три типа изменяемости
  разделены формально.
- **AdaptiveChunking (приоритет 3 обзора**:
  adaptiveCost (C(x)=Σ c_ℓ·M_ℓ(x)² — стоимость иерархии как
  функция ВХОДА); adaptive_le_static (поточечное
  доминирование M_ℓ(x) ≤ L/r ⟹ адаптивная стоимость ≤
  статической); adaptive_lt_of_strict (строгое превосходство
  на одном уровне при положительной цене ⟹ строгая
  экономия) — математическая модель обучаемого чанкинга
  H-Net (M зависит от входа, а не от константного r).
- **CPUFreeze (приоритет 5 обзора**: safeStep
  (CPU-блок шага обнулён, rest сохранён): cpu_frozen
  (ΔCPU'=0 rfl-контракт — веса процессора инвариантны к
  градиентам), norm_le (‖safe‖ ≤ ‖proposal‖ — trust region
  наследуется), anchor_drift (якорный дрейф только по rest;
  C1/C2/C3 SafeQP-расширения закрыты).
- **GDNBridge (приоритет 1 обзора HAGI Neural Computer,
 gdnUpdate (delta rule S' = g·S + β·(v−S·k)kᵀ);
  gdn_onehot_is_colUpdate (g=β=1, k=e_i — ТОЧНАЯ замена
  i-го столбца: рекуррентная GDN-нейросеть в режиме
  Qwenputer исполняет адресуемую запись); 
  gdn_transpose_is_ramWrite (транспонированная delta-запись
  = ramWrite из GDNRAM — мост реальной архитектуры к
  абстрактной RAM-семантике).
- **TransitionContract (P1-миграция v3**: мост
  CertifiedTransitionV2 → StepContract: ctContract (decrease
  = verify-сертификат, risk = Σ эффект-рисков ≥ 0, budget =
  Σ стоимостей), ctv2_contract (rfl-связка), ctRisk_covers
  (ΔR ≤ riskCost контракта — safety-бухгалтерия накрывает
  реальный прирост риска). Единая trajectory_convergence
  теперь применима к реальным переходам напрямую.
- **CautiousOptimizer (источник №78: 2411.16085
  №245)**: cautiousMask (сохранять только компоненты update,
  согласованные со знаком градиента): cautiousMask_abs_le
  (маска не увеличивает модуль), cautiousAligned (выжившие
  компоненты u'·g ≥ 0), cautiousId/cautiousZero (тождество
  при согласии, полный отказ при конфликте — «не вредить»).
- **InfoPreservation 
  info_preservation_regret — СРЕДНИЕ потери траектории
  mirrorIterate ≤ потери целевого распределения +
  T·KL(ρ*‖ρ₀)/n — информационный дрейф гасится начальной
  близостью, исчезает с горизонтом (реюз mirror_regret).
  Тем самым v16-тесты: 1✓ 2✓ 3✓ 5✓ 6✓ 7✓ (Test 4 —
  SafeQP-домены, общий вид).
- **BytePatch (источник №77: Cartesia From-Tokens-to-Bytes
  H-Net; patchCount ⌈N/p⌉₊ — байтовые патчи:
  patch_cover (p·⌈N/p⌉ ≥ N — покрытие входа), patch_le_raw
  (p ≥ 1 ⟹ патчей ≤ байтов), patch_real_bound (< N/p+1),
  patch_attn_saving (⌈N/p⌉² < N² при p≥2, N≥2p — строгая
  экономия квадратичного внимания).
- **QuantizedAdvance 
  advanceQ — РЕАЛЬНАЯ семантика компрессии: params' =
  q(params − η·d) (advance + фактическое квантование);
  advanceQ_quantized (Test 3 rfl-контракт), advanceQ_prox
  (контракт квантовщика ‖qx−x‖≤Δ ⟹ квантованное состояние в
  Δ-окрестности идеального), compressQ_eq_gridQ +
  compressQ_prox (machineStep эталона = advanceQ с
  q = compressQ, контракт выполнен поточечно Δ/2 через
  gridQ_error).
- **CertifiedTransitionV2 
  №241)**: hRiskLim — риск-лимит АКТИВНО проверяется полем
  структуры (счётчик ≠ соблюдение лимита); ctv2_of_ct — мост
  V1→V2 (полная совместимость, Freeze стабилен); ранее
  добавлена теорема ct_risk_respects_budget (ΔR ≤ riskLim
  выводится из safety-бухгалтерии при сумме эффект-рисков ≤
  лимита).
- **BatchSNR (источник №76: McCandlish Gradient Noise Scale,
  1812.06162; snr (μ²B/σ²), snr_realized
  (= μ²/E[(ĝ−μ)²] — реализованный SNR через temperature law
  Var=B⁻¹), snr_linear (SNR(B)=B·SNR(1) — линейный рост),
  criticalBatch (B*=σ²/μ²), snr_ge_one_iff (SNR≥1 ⟺ B≥B* —
  пороговый закон критического батча). Поверх
  NoiseTemperature-капстроуна без дублирования.
  md +12 записей тактов 225–238 (ретро №239).
- **LookaheadTrajectory (связка №75×EMA**:
  anchorSeq (якорная последовательность Lookahead);
  anchor_eq_ema (тождество: slowStep-рекурсия = EMA при
  β=1−α — DRY-мост); anchor_stable (якорная траектория в
  [lo,hi] на любом горизонте — реюз ema_invariant:
  двухмасштабная схема не может дрейфовать за оболочку
  данных).
- **Lookahead (источник №75: 1907.08610;
  slowStep (w' = w + α(x−w)); lookahead_mem (новый якорь ∈
  [min, max] старого и быстрого — шаг назад не проскакивает
  цель), lookahead_gap (|w'−w| = α·|x−w| — дрейф якоря
  пропорционален α), lookahead_range (инвариант [lo,hi]).
- **LabelSmoothing ур.2 (углубнение №74**:
  ls_entropy_ge — СГЛАЖИВАНИЕ НЕ УМЕНЬШАЕТ ЭНТРОПИЮ ЦЕЛИ:
  H(q) ≤ H(q^LS) при строго положительной цели (Jensen по
  слагаемым x·log x из xlogx_convex + шенноновская граница
  shannon_entropy_le_log_card: H(q^LS) ≥ (1−ε)H(q) +
  ε·log card K ≥ H(q)) — регуляризация к равномерному.
- **LabelSmoothing (источник №74: Szegedy 1606.04586;
 lsTarget ((1−ε)q + ε·u — выпуклая комбинация
  с равномерной), ls_sum_one (сглаженная цель —
  распределение), ls_nonneg, ls_pointwise_dist
  (|q^LS−q| = ε·|q−1/K| — линейно по ε), ls_l1_bound
  (∑|q^LS−q| ≤ ε·card — цель обучения в ε-окрестности).
- **Насыщение роста 
  saturation_gap (C*−C_T = (1−σ)^T(C*−C_0) — геометрическое
  сжатие зазора до потолка: ЛИНЕЙНАЯ сходимость вместо
  обязательного экспоненциального взлёта),
  saturation_ceiling (C_T ≤ C* − (1−σ)^T(C*−C_0) ≤ C* —
  рост монотонен и не пересекает потолок). Рекомендация
  v14 выполнена: жёсткая модель cone_premises_force_exact
  дополнена честной динамикой с насыщением и шумом.
- **StepContract-мост 
  constContract (постоянный контракт decrease=eps, risk=0),
  termination_via_stepcontract — канонический телескоп
  lyapunov_termination_fin ВЫВОДИТСЯ из единой
  trajectory_convergence: телескоп-дубли (ProbeError,
  GrowthState, TopLevel) суть экземпляры одного принципа.
- **ModelSoup/EMA (источник №73: Model Soups, 2203.05482;
 soup (выпуклая комбинация параметров),
  soup_mem (суп ∈ [min,max] — выпуклая оболочка),
  soup_loss_le_avg (Jensen: выпуклый лосс супа ≤ супа
  лоссов — ConvexOn.map_sum_le), ema-рекурсия +
  ema_invariant (EMA ∈ [lo,hi] на любом горизонте при
  β ∈ [0,1] — сглаживание без выхода за диапазон).
- **MuonNS (источник №72: Muon is Scalable, 2502.25082;
 реальная скалярная модель итерации
  Ньютона-Шульца ортогонализации Muon: ns u = u(3−u²)/2 —
  ns_invariant ((0,1]-инвариант), ns_monotone_ascent
  (подъём к 1), ns_error_factor (1−ns u = (u−1)²(u+2)/2 —
  КВАДРАТИЧНАЯ сходимость сингулярных чисел),
  ns_error_contract (строгое сжатие u < ns u < 1).
- **CertifiedTrajectory**: ЕДИНАЯ траекторная
  теорема certified_progress_honest — связка трёх уровней
  (execution → measurement → contract): Σmeasured − Σδ ≤
  Φ₀−Φ_min+Σrisk (прогресс подтверждён снизу данными И
  ограничен сверху теорией); certified_progress_signal —
  суммарный измеренный прирост > шума ⟹ кумулятивный
  decrease строго положителен И бюджетно-рисково ограничен.
- **MeasurementCert (направление TorchLean spec→exec→verify;
 двухуровневая сертификация — StepMeasurement
  (claimed ∈ [measured−δ, measured+δ], anytime-полоса),
  claimed_floor/claimed_ceiling (честные границы),
  claimed_pos_of_signal (прирост > шума ⟹ положителен),
  compose + chain_floor (кумулятивная честность цепочки).
  Уровень 2 из рекомендации аудита: сертификат ИЗМЕРЕНИЯ
  поверх сертификата ИСПОЛНЕНИЯ (CertifiedTransition.exec).
- **Anytime PAC-Bayes / time-uniform Catoni (источник №71:
  направление FormalSLT; real_mono_prob (хелпер
  монотонности реальной меры), anytime_catoni — если
  L_t = exp(lam·S_t − ψ·t) неотрицательный супермартингал с
  E[L₀]≤1, то P(∃t≤n: S_t > (ψt+log(1/δ))/lam) ≤ δ —
  TIME-UNIFORM гарантия (момент проверки адаптивен), Ville ×
  Catoni композиция. Закрывает лакуну «time-uniform bounds»
  из обзора конкурирующих проектов (FormalSLT).
- **Вариационное ядро (источник №70: Bridging Control/
  Inference/Transport/Thermodynamics, 2609.15897;
  mirror_step_variational_descent (экспоненциальное обновление
  НЕ увеличивает свободную энергию F(q)=⟨q,ℓ⟩+T·KL(q‖ρ₀):
  F(γ) ≤ F(ρ₀) — вариационный принцип; вывод из
  floor+attainment), mirrorIterate_partial_mono (итерационная
  монотонность при фиксированном ландшафте — JKO-аналог
  убывания свободной энергии вдоль траектории).
- **StepContract 
  моноид сертификатов шага — StepContract (decrease/riskCost/
  budgetSpend + неотрицательности), compose (assoc/нейтраль
  по rfl-структуре), chain (foldr-свёртка; компоненты = суммы),
  trajectory_convergence (ЕДИНАЯ телескопическая теорема:
  Σdecrease ≤ Φ₀−Φ_min+Σrisk; замещает дубли телескопирования).
- **LogitPSV (источник №69: Rethinking Neural Thickets,
  2610.40649; аудит v14)**: logitPSV_gap_nonneg (ансамбль
  K статических логит-смещений НЕ ХУЖЕ среднего — реюз
  twoGap_nonneg), logitPSV_gap_zero_of_no_spread (σ=0:
  без разнообразия нет выигрыша — twoGap_zero_iff),
  frozenWeights (база заморожена: тернарность не
  разрушается, стоимость изменений весов = 0).
- **Сквозной пример + КВАНТОВАНИЕ**:
  qQuant_err_bound — потеря функции потерь от
  квантования постшаговой точки ≤ (Δ/2)(2R+Δ/2) при
  |x'−a| ≤ R (gridQ_error + разность квадратов): цепочка
  «биты → реальное квантование → ошибка параметров →
  ошибка loss» замкнута ВЫЧИСЛЕНИЕМ на сквозном примере
  .
- **LLRD (источник №68: послойное LR-затухание, ULMFiT
  1801.06146-стиль)**: llrd_strict_mono (при 0<γ<1 LR
  СТРОГО растёт с номером слоя — верхние слои учатся
  быстрее, нижние почти заморожены), llrd_nonneg.
- **ReZero (источник №67: Bachlechner et al., 2003.04887)**:
  rezero_identity (α=0: блок = ТОЖДЕСТВО — глубокая сеть в
  инициализации есть чистый residual-путь), 
  rezero_perturb_bound (возмущение ≤ |α|·‖f‖ — линейное
  управление глубиной одним скаляром).
- **PreNorm (источник №66: DeepNet 2203.04627 — pre-norm
  стабильность)**: preNorm_step_bound (треугольник:
  ‖x+f‖ ≤ ‖x‖+‖f‖), preNorm_depth_bound (по глубине L:
  ‖x_L‖ ≤ ‖x_0‖ + L·B — глубина НЕ взрывает норму,
  экспоненциальный рост невозможен).
- **GradAccum (источник №65: микробатчи/fiberwise)**:
  accum_equiv — сумма микробатч-градиентов РАВНА полному
  батч-градиенту (Finset.sum_fiberwise: разбиение по
  классам c восстанавливает полную сумму; накопление по
  частям математически тождественно одному большому шагу).
- **AdamW (источник №64: Loshchilov & Hutter,
  1711.05101)**: adamw_shrink (decoupled decay действует
  ВСЕГДА: при нулевом градиенте веса строго сжимаются,
  фактор |1−λ|<1), l2_decay_diluted (coupled-L2
  ослабляет decay адаптивным знаменателем: эффективный
  фактор ≤ λ² — ядро критики расцепления).
- **FlashAttention (источник №63: Dao et al., 2205.14135)**:
  flash_io_lt (IO N²d²/M < N²+Nd при ЧЕСТНОЙ гипотезе
  M > d² — наивная M > d ЛОЖНА: d=2, M=2.1, N=10 →
  flash≈190 > std=120; выгодность требует SRAM > d²),
  flash_io_antitone (монотонность по M).
- **GDNRAM (источник №62: Qwenputer/GDN one-hot — аудит
  v10 §5.3)**: контракт ТОЧНОЙ адресуемой памяти —
  ram_read_after_write (чтение после записи возвращает
  значение в точности), ram_write_independent (строки
  изолированы), ram_write_idem (перезапись идемпотентна).
- **StreamingLLM (источник №61: Xiao et al., 2309.17453)**:
  stream_bounded (KV-кэш ≤ n_s + w при ЛЮБОМ горизонте —
  память не растёт с длиной входа: стриминг без
  ограничений), stream_mem_lt (строгая экономия против
  полного кэша), stream_saving_step (экономия растёт
  линейно: +1 на токен).
- **ALiBi (источник №60: Press et al., 2108.12409)**:
  alibi_bias_anti (bias −m·d монотонно убывает по
  расстоянию), alibi_bias_nonpos, alibi_kernel_decay
  (экспоненциальное затухание attention-ядра дальних
  позиций: exp(−m·d₂) ≤ exp(−m·d₁) — основа «train short,
  test long»), alibi_kernel_decay_lt (строгое).
- **SourceMixture №58 уровень 2 (MaxRL-ядро**:
  successDist_norm — распределение успешных ответов
  π⁺(y)=π(y)·r(y)/p НОРМИРОВАНО (RL-цель корректна как
  likelihood-обучение на успешных ответах — мост
  генерация→верификация→MLE), successDist_nonneg.
  №59-нормировка (бином-индукция) — карантин (не
  выводится в пин-версии Mathlib).
- **SourceMixture (источник №58: Song et al., 2610.40564 —
  единый training objective)**: mixture_sum_one (смесь
  вероятностных источников с весами λ (Σλ=1) — САМА
  вероятностное распределение: корректность единого
  likelihood-обучения на смеси), mixture_nonneg. Уровень 2
  (MaxRL/TailRL-цели, токен-нормировка) — далее.
- **BernoulliFactory (источник №59: Taylor 2610.38964)**:
  Bernstein-гейт — probAccept_eq_bernPoly (вероятность
  принятия = Bernstein-полином в точности),
  binomWeight_nonneg (при p ∈ [0,1]), probAccept_bounds
  (0 ≤ P ≤ binomMass; полная нормировка = 1 — уровень 2,
  индукция/Vandermonde). Оговорка аудита v12: gate НЕ
  заменяет SafeQP-гарантии отдельного шага.
- **GQA (источник №57: Ainslie et al., 2305.13248)**:
  gqa_kv_lt (KV-кэш n_kv < n_h голов строго меньше MHA),
  gqa_kv_ratio (отношение = n_kv/n_h), gqa_kv_mono
  (монотонность по числу KV-голов; MQA-минимум).
- **Sliding Window Attention (источник №56: Mistral,
  2310.06825)**: swa_cost_lt (n·(2w+1) < n² при 2w+1<n),
  swa_cost_ratio_lt (<1), swa_cost_mono (уменьшение окна
  СТРОГО уменьшает стоимость — монотонное управление
  бюджетом внимания).
- **Mixture-of-Depths (источник №55: Raposo et al., 2404.02258)**:
  mod_layer_cost_lt (top-k слой строго дешевле dense),
  mod_stack_saving (глубина УМНОЖАЕТ экономию: L-слойный
  стек экономит ровно L·(послойная экономия), Nat.mul_sub).
- **Perceiver latent bottleneck (источник №54: Jaegle et al.,
  2103.03206)**: perceiver_cost_lt (при 2m ≤ n блок
  cross+latent СТРОГО дешевле self-attention; честная
  оговорка: при m → n сумма ПРЕВЫШАЕТ n² — экономия только
  у настоящего бутылочного горлышка), perceiver_cost_ratio_lt
  (< 1), perceiver_saving_pos (2m < n).
- **Best-of-N rejection sampling (источник №53, Dong
  2304.06767)**: best_of_n_mean_le_sup (средняя награда ≤
  максимума — отбор лучшего не хуже среднего: порядковая
  гарантия RAFT), best_of_n_pos. Отборочная выборка
  формализована.
- **RLHF KL-контроль (источник №52, Ziegler 1909.08593)**:
  rlhf_penalty_floor — KL-штраф НИКОГДА не увеличивает
  цель U = E[r] − β·KL ≤ E[r] (композиция kl_nonneg):
  однонаправленный урез reward-hacking. RL-стек замкнут:
  RLHF + PPO + GRPO + GAE + DPO.
- **GAE (источник №51, Schulman 1506.02438)**:
  gae_weight_bound (сумма GAE-весов (1−λ)(γλ)^i ≤ 1 при
  γ,λ∈[0,1] — выпуклость смеси с хвостовой утечкой; реюз
  one_sub_beta_geom из №28), gae_weight_pos. RL-стек:
  PPO + GRPO + GAE + DPO.
- **Sparse Upcycling (источник №50, Komatsuzaki 2210.06264)**:
  upcycle_preserves — идентичные эксперты + равномерный
  роутер ⟹ MoE-выход = dense-выходу (СТАРТОВАЯ ФУНКЦИЯ
  СОХРАНЯЕТСЯ при upcycling: наследование предобучения;
  композиция с равномерностью №34).
- **Weight Tying (источник №49, Press & Wolf 1608.05859)**:
  wtParams/untiedParams (mn vs 2mn), wt_saving (СТРОГАЯ
  экономия половины параметров проекции при связывании
  входных/выходных эмбеддингов).
- **Gradient Checkpointing (источник №48, Chen 1604.06174)**:
  ckpt_mem_floor (k + n/k ≥ 2√n — нижняя граница памяти,
  разложение квадрата), ckpt_sqrt_opt (k = √n — оптимум:
  O(√n) память за линейный пересчёт). Инфраструктурный
  стек обучения пополнен.
- **Lion (источник №47, Chen 2302.06675)**: sgn/signStep,
  sign_sq_le_one (split-стиль, без deprecated if-лемм),
  lion_step_norm_bound (∑(η·sgn m i)² ≤ η²·d — норма
  sign-шага ограничена η√d независимо от амплитуды
  градиентов: robustness к взрывной шкале; контраст с
  AdaGrad-затуханием №46). Оптимизаторный стек: Adam +
  AdaGrad + Lion + Muon + SafeQP.
- **AdaGrad (источник №46, Duchi 1110.4001)**: adagradAcc
  (∑ g_s²), acc_mono, adagrad_step_anti (накопление НИКОГДА
  не увеличивает адаптивный шаг η/√(G+g²) ≤ η/√G —
  монотонное затухание), adagrad_step_pos. Оптимизаторный
  стек: Adam + AdaGrad + Muon + SafeQP.
- **Logit soft-capping (источник №45, Gemma 2 2408.00118)**:
  tanhE/softcap (l' = cap·tanh(l/cap)), tanhBound (|tanh| ≤ 1
  через разность квадратов — tanh-лемм в пине нет),
  softcap_bound (|softcap| ≤ cap — ГЛАДКОЕ ограничение
  логитов без градиентных разрывов), softcap_zero.
  Стек стабилизации: QK-norm + softcap.
- **Mamba №38 уровень 2**: mamba_disc_contract —
  дискретизация SSM: e^{−ΔA} ≤ 1 при Δ,A ≥ 0 — дискретный
  шаг никогда не усиливает состояние (устойчивость явной
  схемы selective SSM).
- **Matryoshka Representation Learning (источник №44,
  Kusupati 2205.13147)**: matryoshka_norm_le (норма усечения
  m ≤ n не превосходит полной — вложенность
  представлений), matryoshka_dist_le (расстояние усечений ≤
  полного — усечение никогда не усиливает). Гранулярность
  одного эмбеддинга обслуживает любой бюджет.
- **H-Net №37 уровень 2 — ОПТИМАЛЬНЫЙ РАНГ ПУЛА**: amgm3
  (трёхчленный AM-GM из geom_mean_le_arith_mean_weighted),
  hnet_cost_floor — cost(r) = aTr + bT²/r² ≥
  3·(a²bT⁴/4)^{1/3} НЕ зависит от r (r сокращается в
  AM-GM-произведении x=x=aTr/2, z=bT²/r²); оптимум
  r* = (2bT/a)^{1/3} ∝ T^{1/3} — скейлинг ранга иерархии.
- **RMSNorm №25 уровень 3 (КОНТРАСТ)**: rms_not_centered —
  на константном векторе ∑(rnVec x i) = n ≠ 0: RMSNorm НЕ
  центрирует (цена экономии без mean-subtraction);
  LayerNorm центрирует (ln_sum_zero) — точная пара
  контрастных теорем.
- **LayerNorm №21 уровень 3**: ln_sum_zero — LN-выход
  ЦЕНТРИРОВАН: ∑(lnVec x i) = 0 (реюз groupAdv_sum_zero);
  RMSNorm этим НЕ обладает — точный контраст нормировок.
- **Мост №21↔№25**: variance_decomp — var(x) = ms(x) −
  mean(x)² (E[x²]−E[x]²): LayerNorm-дисперсия = RMSNorm-ключ
  минус квадрат среднего — центрированная и нецентрированная
  нормировки связаны ТОЧНО (реюз groupAdv_sq_decomp с c=0).
- **GRPO уровень 3 (№33+)**: groupAdv_std_unit —
  стандартизованный advantage A_i = (r_i−mean)/σ имеет
  ЕДИНИЧНУЮ дисперсию: ∑A_i² = n (Dr.GRPO-нормировка).
- **DPO уровень 2 (№31+)**: btPref (Bradley–Terry
  sigmoid-link p(y₁≻y₂) = σ(r₁−r₂)), bt_pref_iff
  (p > 1/2 ⟺ r₁ > r2 — link корректно кодирует порядок
  наград; строго через exp-монотонность).
- **QK-Norm уровень 2 (№36+)**: qk_no_saturation — при
  логит-гэпе ≤ 2n (после QK-норм) отношение любых двух
  вероятностей внимания ≤ e^{2n}: каждый токен получает
  ≥ e^{−2n} доли внимания — ПОЛНАЯ САТУРАЦИЯ softmax
  структурно исключена (спайки №23 дополнены жёсткой
  нижней границей).
- **Z-loss router-стабилизация (источник №43, ST-MoE
  2202.08906)**: zloss_bound (штраф c·log²Z ≤ B ⟹
  |log Z| ≤ √(B·c) — квадратичный штраф даёт корневую
  границу на рост логит-нормы), zloss_zero (нулевой штраф
  ⟺ Z = 1 — сбалансированная нормировка как глобальный
  минимум). MoE-стек: Switch-баланс (№34) + Z-loss (№43).
- **MLA латентный KV-кэш (источник №42, DeepSeek-V2
  2405.04434)**: cacheFull/cacheLatent (память 2nd vs n·dc),
  mla_cache_saving (dc < d ⟹ латентный кэш СТРОГО меньше —
  экономия растёт с контекстом; K,V восстанавливаются из
  латента той же низкоранговой структурой, что LoRA №35).
  Inference-стек: GQA + spec-decoding + H-Net + MLA.
- **Flow Matching (источник №41, Lipman 2210.02747)**:
  flowPath (линейный путь (1−t)x₀+tx₁ — прямая
  интерполяция шум→данные), flow_start/end (точная
  доставка endpoints), flow_convex (путь между x₀ и x₁
  при t∈[0,1]), flow_mid. Генеративный стек: DDPM + CFG +
  Flow Matching.
- **Classifier-Free Guidance (источник №40, Ho & Salimans
  2207.12598)**: cfg_interp (ε̃ = (1−w)ε_u + wε_c),
  cfg_convex (при w∈[0,1] предсказание между условным и
  безусловным), cfg_boost (при w>1 отклонение ∝ (w−1)
  от безусловного — экстраполяция усиливает условность).
  Diffusion-стек: DDPM (№39) + CFG (№40).
- **DDPM forward-процесс (источник №39, Ho 2006.11239)**:
  alphaBar (∏(1−β_s)) + рекуррентность, alphaBar_mono
  (сигнал монотонно НЕвозрастает при β∈[0,1]),
  alphaBar_exp_bound (ᾱ_t ≤ (1−b)^t — ЭКСПОНЕНЦИАЛЬНОЕ
  затухание сигнала, геометрическая скорость перевода в
  шумовой режим). Генеративный стек: KD + DPO + diffusion.
- **Mamba/SSM (источник №38, Gu & Dao 2312.00752)**:
  ssm_linear_cost_lt (рекуррентный O(T·κ) проход строго
  дешевле O(T²)-attention при T > κ — crossover),
  ssm_memory_const (O(1)-память состояния vs линейный
  KV-кэш при d ≥ 1), ssm_state_bound (при сжатии ρ < 1
  состояние ограничено B/(1−ρ) — стабильность SSM,
  геометрическая серия). Sequence-стек: attention (№23) +
  H-Net иерархия (№37) + SSM (№38).
- **H-Net byte-level (источник №37, Cartesia From Tokens
  to Bytes I/II + Merrill 2509.06784)**: hier_seq_shorten
  (пул r байтов в латент: T → T/r), hier_attn_saving
  (КВАДРАТИЧНАЯ экономия: attention на латентах = 1/r² от
  byte-level — иерархия конвертирует линейное сокращение
  в квадратичную экономию), hier_attn_saving_lt (строгая
  при r>1). Обоснование внутренней токенизации вместо
  замороженного BPE.
- **QK-Norm (источник №36, Henry 2002.10872)**:
  qk_logit_bound: для RMS-нормированных q, k
  |q·k| ≤ n — логиты внимания ограничены размерностью
  головы (Cauchy–Schwarz через dotCS), attention-спайки
  исключены, масштаб входов не влияет. Композиция №25
  (rn_unit_rms) + dotCS — ноль новых примитивов.
- **LoRA, уровень 1 (источник №35, Hu 2106.09685)**:
  lora_out ((W+BA)x = Wx + B(Ax) — адаптация через
  низкоранговый канал), lora_kernel_preserved (A·x = 0 ⟹
  поведение НЕ МЕНЯЕТСЯ — аналог GPM zero-forgetting на
  охвате адаптера), lora_param_saving ((m+n)r ≤ mn —
  экономия против полного fine-tuning).
  Адаптационный стек: LoRA + LiveDelta + RankBudget.
- **Switch MoE load balancing (источник №34, Fedus
  2101.03961)**: switch_floor (∑P_i² ≥ 1/n при ∑P = 1 —
  нижняя граница нагрузочного члена; реюз GRPO sq_decomp с
  c=0), switch_floor_eq_iff (равенство ⟺ равномерный
  роутинг — единственный минимум баланса). MoE-стек:
  Hopfield-ёмкость (№16) + water-filling + Switch-баланс.
- **GRPO, уровни 1+2 (источник №33, Shao 2402.19327)**:
  groupAdv (A_i = r_i − mean(r) — групповой baseline без
  value-сети), groupAdv_sum_zero (∑ A_i = 0 — смещение-
  компенсация), groupAdv_sq_decomp (∑(r−c)² − ∑(r−mean)² =
  n·(mean−c)²), groupAdv_sq_min (mean — ОПТИМАЛЬНЫЙ baseline:
  сумма квадратов минимальна ровно на среднем). RL-стек:
  DPO + PPO + GRPO.
- **PPO-clip (источник №32, Schulman 1707.06347)**: ppoClip,
  границы/монотонность/тождественность внутри отрезка,
  ppo_clip_term_abs_bound (|clip·A| ≤ (1+ε)|A|),
  ppo_surr_upper_bound (L = min(rA, clip·A) ≤ (1+ε)|A|
  при любом r — клипнутый surrogate ограничен сверху:
  обновление политики не может дать неограниченный
  выигрыш). RL-выравнивание: DPO (№31) + PPO (№32).
- **DPO, уровень 1 (источник №31, Rafailov 2305.18290)**:
  dpoReward (β·(ln π − ln π_ref)), boltzmann_from_reward
  (π = π_ref·exp(r/β) — политика восстанавливается из
  неявной награды без RL-цикла), boltzmann_norm
  (болцмановская реконструкция АВТОМАТИЧЕСКИ нормирована:
  Z = ∑ π_ref·exp(r/β) = 1). Pref-обучение без RL.
- **Cosine LR Schedule (источник №30, SGDR, Loshchilov &
  Hutter 1608.03983)**: cos_anti (косинус анти-монотонен на
  [0,π] — через произведение синусов, без анализа),
  cosLR (η/2·(1+cos(πt/T))), cosLR_nonneg, cosLR_start (η(0)
  = η_max), cosLR_end (η(T) = 0), cosLR_anti (расписание
  анти-монотонно на [0,T]). LR-расписания: WSD (№11) +
  cosine (№30).
- **Gradient Clipping (источник №29, Pascanu 1211.5063)**:
  clip (масштабирование до шара нормы — теоремы для любой
  нормы), clip_norm_le (‖clip R g‖ ≤ R — защита от взрывных
  градиентов), clip_eq_of_le (инертность при ‖g‖ ≤ R),
  clip_idem, clip_dir (при R < ‖g‖ клип = c•g, c > 0),
  clip_descent_pos (КЛИП СОХРАНЯЕТ СПУСКОВОСТЬ: острый угол
  ⟨g,d⟩ > 0 сохраняется — положительное масштабирование не
  меняет знака). Стабилизационный стек замкнут.
- **Adam bias correction (источник №28, Loshchilov & Hutter
  1711.05101)**: one_sub_beta_geom ((1−β)∑β^i = 1−β^t),
  adamM_recur (closed form = рекуррентность m₀=0,
  m_{t+1}=βm_t+(1−β)g), adam_unbiased_const (НА ПОСТОЯННОМ
  ГРАДИЕНТЕ КОРРЕКЦИЯ ТОЧНА: m̂_t = g при 0≤β<1, t≥1),
  adam_bias_bound (без коррекции m_t = g−β^t·g — смещение
  затухает геометрически). Оптимизаторный стек замкнут.
- **Speculative Decoding, уровень 1 (источник №27, Chen
  2302.01318)**: accept_chain_prob (α^k), 
  speculative_expected_tokens (геометрическая серия
  (1-α^{k+1})/(1-α), индукция), speculative_win (при α>0,
  k≥1 ожидаемое число токенов/проход > 1 — спекулятивный
  цикл строго выгоднее последовательного декодирования).
  Inference-стек: GQA + shift-softmax + spec-decoding.
- **Multi-scale Engine: композиционный сертификат микро-шага
  (MicroStepCert)**: microstep_cert — МОСТ рычагов: L-гладкость
  + дессент ⟨G,ΔW⟩ ≤ -ε + gpmOrth ⟹ ОДНОВРЕМЕННО
  E(W+ΔW) ≤ E W - ε + L/2‖ΔW‖²_F и ТОЧНОЕ воспроизведение
  старых входов ((W+ΔW)x_k = Wx_k ∀k — gpm_zero_forgetting).
  microstep_net_drop: при L/2‖ΔW‖²_F < ε — строгий чистый
  спуск. SafeQP в подпространстве GPM совместим со спуском.
- **SwiGLU, уровень 1 (источник №26, Shazeer 2002.05202)**:
  sig/swish/swiglu, swish_abs_le (|Swish z| ≤ |z| — гейт
  σ(z)∈(0,1) не усиливает активацию), swiglu_abs_le
  (|Swish(a)·b| ≤ |a·b| — drift-границы residual-потока №22
  переносятся на SwiGLU-блоки без изменения констант).
  FFN-слой стека замкнут.
- **RMSNorm, уровни 1+2 (источник №25, Zhang & Sennrich
  1912.11247)**: ms/rnVec, rn_scale_invariant (как LN —
  инвариантность к масштабу, направление сохраняется),
  rn_unit_rms (∑(rn x i)² = n при x ≠ 0 — единичный RMS
  выхода). Стек нормализации замкнут: LN (№21) + RMSNorm.
- **RoPE, уровень 1 (источник №24: Su et al., RoFormer,
  arXiv 2104.09864)**: Hagi/Model/RoPE.lean — rot
  (вращение позиции (e^{iθ})^k), rot_normSq_one (единичность,
  cos²+sin²), rope_normSq_preserved (ИЗОМЕТРИЧНОСТЬ:
  вращение сохраняет normSq — фаза меняется, модуль нет —
  ядро корректности позиционного кодирования).
- **RoPE-задел + μP-контраст-сводка **:
  muP_bound_le_sp_bound (μP-граница ≤ SP-границы при n ≥ 1
  — формальное сопоставление переносимого и непереносимого
  скейлинга). RoPE (№24, Su 2104.09864) — ядро
  shift-инвариантности формализовано; расширение отложено до
  следующей попытки.
- **Attention-масштабирование 1/√d (источник №23:
  Vaswani et al., arXiv 1706.03762)**: композиции
  температурного диала №19 — attention_scale_softens
  (масштаб 1/√n держит softmax в мягкой зоне: softProb
  (s/√n) → 1/2 при n → ∞ — живые градиенты),
  attention_no_scale_saturates (без масштаба зазор ~ n:
  сатурация к 1, градиент затухает) — формальное ядро
  необходимости 1/√d-скейлинга в attention.
- **Контраст линейного/экспоненциального (уровень 2
  источника №22)**: cascade_exp_bound (plain-каскад:
  ‖x_T‖ ≤ (1+δ)^T·‖x₀‖ — экспоненциальный рост по глубине),
  linear_le_exp_contrast (Бернулли: (1+δ)^T ≥ 1+Tδ) —
  формальное ядро необучаемости глубоких plain-сетей vs
  обучаемости residual (линейный дрейф).
- **Residual-соединения: ограниченный дрейф (источник №22:
  He et al., arXiv 1512.03385)**: Hagi/Model/Residual.lean —
  resStep/resStream, res_bounded_drift: T residual-шагов с
  приращениями ≤ ε ⟹ суммарный дрейф ≤ T·ε (индукция +
  треугольник): приращения АДДИТИВНЫ — глубина даёт
  линейный, не экспоненциальный рост дрейфа (ядро
  обучаемости глубоких residual-сетей).
- **LayerNorm: масштабная инвариантность (источник №21:
  Ba, Kiros, Hinton arXiv 1607.06450; RMSNorm 1904.10510)**:
  Hagi/Model/LayerNorm.lean — mean/variance/lnVec,
  mean_smul, variance_smul (однородность 2-й степени),
  ln_scale_invariant: LN(c•x) = LN(x) при c > 0 —
  нормировка выделяет НАПРАВЛЕНИЕ, отбрасывая длину
  (устойчивость глубоких сетей к масштабу активаций).
- **SWA-теория, уровень 2 источника №17 (Izmailov et al.,
  arXiv 1803.05407)**: swa_average_bound — энергия СРЕДНЕГО
  по T точкам траектории ≤ среднего энергий (Jensen для
  квадратичной энергии через Cauchy–Schwarz:
  (Σd)² ≤ T·Σd²): стохастическое усреднение весов не хуже
  среднего по траектории.
- **Compute-optimal масштабирование (источник №20:
  Hoffmann et al., Chinchilla, arXiv 2203.15556)**:
  Hagi/Model/ComputeOptimal.lean — chinchillaLoss (A/N +
  B·N/C: параметрический член убывает, член данных растёт
  при D = C/(c·N)), chinchilla_optimum — ТОЧНЫЙ глобальный
  минимум (AM–GM): N* = √(A·C/B), min L = 2√(A·B/C):
  и слишком малые, и слишком большие модели проигрышны;
  оптимум сбалансирован, N* растёт как √C.
- **Дистилляция знаний: температурный диал (источник №19:
  Hinton, Vinyals, Dean, arXiv 1503.02531)**:
  Hagi/Unified/Distillation.lean — softProb (двухклассовый
  soft-зазор x = d/T), soft_dial_max (x→∞: one-hot, полный
  бит), soft_dial_zero (x→0: равномерное, ноль бит),
  soft_entropy_bound (H ≤ ln 2 — следствие канонического
  shannon_le_log_card). Температура непрерывно управляет
  количеством переносимой информации — формальное ядро
  temperature scaling в KD.
- **μP-скейлинг / μTransfer (источник №18: Yang et al.,
  "Tensor Programs V" arXiv 2203.03466)**:
  Hagi/Model/MuPScaling.lean — row_output_bound
  (Cauchy–Schwarz строчная оценка выхода), muP_width_invariant
  (шаг η/√n ⟹ изменение выхода ≤ η·c·‖x‖₂ — НЕ зависит от
  ширины n: перенос LR между моделями разных ширин),
  sp_grows_with_width (без скейлинга оценка растёт как √n —
  стандартная параметризация непереносима). Ядро μTransfer:
  обучение малой модели с переносом гиперпараметров на
  большую — прямая цель HAGI (минимум вычислений).
- **Mode Connectivity, квадратичный режим (источник №17:
  Garipov et al. NeurIPS 2018 arXiv 1802.10026; Theus et al.
  NeurIPS 2025)**: Hagi/Model/ModeConnectivity.lean —
  energy_convex (выпуклость квадратичной энергии вдоль
  линейного пути), linear_no_barrier (энергия вдоль отрезка
  ≤ max концов — барьер между режимами ОТСУТСТВУЕТ: строгая
  формализация LMC; в ньютоновской окрестности минимума
  выполняется автоматически), linear_midpoint_bound (основа
  SWA-усреднения). Обоснование слияния экспертов HAGI:
  переходы между решениями не обязаны проходить через
  барьеры.
- **Мост машина → семантика **:
  Hagi/Model/MachineBridge.lean — machineStageInput (StageInput,
  СОБРАННЫЙ из машинных измерений: growEnergy = E(w),
  jointEnergy = E(w−η∇E), compressEnergy = E(Q(w−η∇E)),
  quantErr — вычисленный; L=1 — фактическая кривизна),
  machine_advance_certified: при S.energy = E(w) и ledger-факте
  канонический advance_energy_drop сертифицирует переход —
  измерения имеют происхождение (веса), сертификат —
  следствие, а не постулат.
- **Эталонный исполнитель цикла обучения 
  этап 6, паттерн qwenputer ref.Machine)**:
  Hagi/Model/ReferenceMachine.lean — носитель, где операции
  РЕАЛЬНО вычисляют веса (jointStep — градиентный шаг,
  compressQ — квантование решёткой Δ·round), а ВСЕ измерения
  — функции весов: jointStep_energy ((1−η)²·E),
  jointStep_energy_decrease (0<η<2 ⟹ строгое снижение
  без постулатов), machine_quant_err_bound (≤ √n·Δ/2),
  machine_energy_bound (полная оценка цикла: шаг+квантование
  через Cauchy–Schwarz). Закрывает разрыв «доказательства
  не связаны с операциями над весами».
- **Modern Hopfield / attention-ретривал (источник №16:
  Ramsauer et al., arXiv 2008.02217 "Hopfield Networks is
  All You Need")**: Hagi/Model/ModernHopfield.lean —
  hopfield_concentration (softmax-концентрация ретривала:
  при зазоре Δ лучшего логита вес лучшего паттерна
  ≥ 1/(1+(K−1)e^{−Δ}) — механизм точного восстановления),
  capacity_bound_arith (арифметика экспоненциальной ёмкости:
  2K·log K ≤ d ⟹ K ≤ 2^{d/(2·log K)}).
- **DREAM (источник №15: Gürbüzbalaban et al., arXiv
  2610.37444, Delay-Resistant Acceleration with Momentum;
  интеграция по анализу пользователя)**:
  Hagi/Optimization/DREAM.lean — уровень 1
  (dream_delay_recurrence): DREAMState (x/xPrev/gHist/
  α,β,ν,τ), dreamY (экстраполяция y_k = x+ν(x−x⁻)),
  delayedGrad (∇f(y_{k−τ}) из истории), dreamStep (РОВНО
  рекурсия статьи: x⁺ = x − αg_{k−τ} + β(x−x⁻)), 
  dream_delayed_gd (β=ν=0 — запаздывающий GD), dreamMomentum;
  dream_bridge (Model/StageSemantics): при stepDir :=
  (1/η)•(α•g_{k−τ} − β•m) шаг advance РЕАЛИЗУЕТ DREAM-шаг.
  Разделение ролей с PolyStep: DREAM — гладкая часть при
  задержанных градиентах, PolyStep — недифференцируемые
  операции; HAGI — сертифицирующий контур. Уровень 2-lite:
  dreamY_gap_norm (‖y−x‖ = |ν|·‖x−x⁻‖),
  dream_tau_extrapolation (ν = 2τ+1/2 — экстраполяция
  растёт линейно по задержке); склейка №15×№11:
  dream_gd_as_plRec (запаздывающий GD как PL-рекуррентность,
  σ кодирует цену задержки), dream_gd_wsd — полная
  WSD-оценка (сжатие+шум+late-decay) наследуется DREAM-GD.
  Следующие уровни:
  dream_quadratic_stability, dream_strongly_convex_rate,
  hagi_dream_stage_sound, hagi_async_budget.
- **PolyStep (источник №14: Training Non-Differentiable
  Networks via Optimal Transport; интеграция по анализу
  пользователя)**: Hagi/Optimization/PolyStep.lean — ядро
  уровня 1 вертикального прототипа: polyWeights
  (softmax-веса по стоимостям, Σ=1, ≥0), 
  polyWeights_strict_mono (строго меньшая потеря ⟹ строго
  больший вес), polyDelta/polyStepUpdate (взвешенное
  направление, шаг θ+ℓ·D), polyDelta_basis_sum (невырожденность
  координатного блока); sign_bridge_polyStep (в Model/
  StageSemantics): при stepDir = −(ℓ/η)•D (η>0) обновление
  advance РЕАЛИЗУЕТ PolyStep-шаг — знаковый мост конвенций
  HAGI(спуск)/PolyStep(приближение). Следующие уровни:
  polyStep_cost_sound (измерение потерь), связь с матричными
  весами, continual_learning_regression_bound.
- **DataMixing (источник №13: Ye et al., Data Mixing Laws,
  arXiv 2403.16952, ICLR'25)**: Hagi/Data/DataMixing.lean —
  mixingLoss (экспоненциальный закон потери от линейной
  формы пропорций), mixing_loss_convex — ВЫПУКЛОСТЬ закона
  смешивания по пропорциям (K≥0): оптимизация смеси доменов
  есть выпуклая задача (ядро применимости закона).
- **MuonAlign (источник №12: arXiv 2506.15054, Muon Optimizes
  Under Spectral Norm Constraints)**: Hagi/Step/MuonAlign.lean
  — НАСТОЯЩЕЕ Muon-ядро (закрывает замечание аудита v6
  «Muon.lean не содержит Muon»): unitary_diag_abs_le (|Qᵢᵢ|≤1
  из QᴴQ=1), muon_alignment_optimal — в собственном базисе
  градиента (diag σ, σ≥0) Muon-шаг (полярная часть = I)
  достигает выравнивания Σσᵢ, максимального среди унитарных Q
  (Σσᵢ·Re Qᵢᵢ ≤ Σσᵢ — ядро неравенства фон Неймана о следе;
  steepest descent при спектральной норме).
- **LRSchedule (источник №11: Li et al. ICLR'26, arXiv
  2602.06797, Optimal LR Schedules under FSL)**:
  Hagi/Optimization/LRSchedule.lean — ядро WSD-результата:
  plRec (PL-рекуррентность с расписанием η_t),
  pl_step_noise_bound (шаг добавляет ≤ σ²η²),
  late_phase_bound — любые k последних шагов с η ≤ η_max
  добавляют к ошибке ≤ k·σ²·η_max²: θ-доля горизонта
  затухания вносит O(θT) — позднее затухание не портит
  порядок скорости (shape-insensitivity ядра WSD);
  wsd_full_bound — полная оценка: stable-фаза m с η=η_max ⟹
  ρ^m·e₀ + σ²η_max²(1−ρ^m)/(1−ρ) + k·σ²η_max²
  (геометрическое сжатие + шумовой бюджет + late-decay);
  wsd_cycle_bound — мост в Certified Growth Loop: WSD-оценка
  энергии + ТОЧНАЯ бюджетная бухгалтерия траектории
  сертифицированных переходов с LR-расписанием;
  cycle_certificate_of_transitions — звено 3 цепочки L3:
  семейство CertifiedTransition + законы стадий ПОРОЖДАЮТ
  CycleCertificate T-горизонта (точный рост, спуск
  потенциала, бюджетный ledger).
- **MesoScale (источник №10: Chen arXiv 2508.12016, A Law of
  Emergence)**: Hagi/Foundations/MesoScale.lean — ядро
  Middle-Scale Peak Theorem: EI(ℓ)=A(ℓ)·L(ℓ), усреднение A ≤
  a₀ℓ^p, локальность L ≤ L₀ℓ^{-q}, q>p ⟹ macro_collapse:
  EI(ℓ) → 0 при ℓ→∞ — эмерджентность исчезает на
  макро-масштабе (носитель — мезо); + rpow_tendsto_zero;
  micro_collapse — симметрично EI(ℓ) → 0 при ℓ → 0⁺ (шум):
  эмерджентность исчезает на обоих концах шкалы, носитель —
  только мезо-масштаб (полный закон эмерджентности);
  meso_peak_exists — capstone: непрерывность + двусторонний
  коллапс + EI(ℓ₀)>0 ⟹ глобальный максимум ДОСТИГАЕТСЯ
  (компакт [ε,M], exists_isMaxOn) — формальный Middle-Scale
  Peak Theorem.
- **Grokking (источник №9: Boursier–Pesme–Dragomir NeurIPS'25)**:
  Hagi/Pretraining/Grokking.lean — двухфазная динамика
  gradient flow + weight decay: drift_solution/drift_hasDeriv
  (пост-интерполяционный дрейф w'=-λw), drift_norm_nondecreasing
  (|w| невозрастает), drift_half_life (полужизнь (ln2)/λ),
  grokking_timescale_separation (∀T_fast ∃λ: время полужизни
  > k·T_fast — обобщение задержано Θ(1/λ) относительно
  обучения); drift_total_variation — полная вариация дрейфа
  ∫|w'| ≤ |w₀| безусловно: риманов дрейф имеет конечный
  «бюджет движения» начальной нормы.
- **NeuronAlloc (resource model of neural scaling)**:
  neuron_alloc_lower_bound — суммарная обратная потеря
  Σ cᵢ/nᵢ ≥ (Σ √cᵢ)²/N при бюджете Σnᵢ = N (Коши–Шварц,
  структура Энгеля); источник — resource-модель скейлинга
  (потеря подтаска ∝ 1/нейроны);
  neuron_alloc_opt_attained — аллокация nᵢ ∝ √cᵢ·N/Σ√cⱼ
  достигает границы РОВНО (двусторонняя замкнутость);
  neuron_alloc_equal_costs — равные c ⟹ равномерная
  аллокация, потеря k²·c₀/N (uniform growth модели).
- **Фасад Unified/MiscCore (closure 312/317, 98%)**:
  разрозненные теоремные модули (12: System×3, Audit×2,
  PPT, SoftmaxFix, TemporalState, QFormerBridge, Diversity,
  RankGrowth, Information.Pinsker) под капстоуном;
  misc_quantized_telescope_and_aitken — квантованный
  телескоп (ошибка ≤ T·Δ/2) ∧ точность Айкен-экстраполяции.
- **Теоремные модули и витнесы в CAPSTONES (closure
  300/316, 95%)**: Unified-мелочь (Fannes, LearningKernel,
  Pinsker, QuantizedCone, Robustness, DataCentric,
  MasterHAGICoupled), ConeCorridor, Examples-витнесы.
- **Фасад Unified/MatrixLib (closure 292/316, 92%)**:
  матричная библиотека Flywheel (10 модулей: SVD,
  Эккарт–Янг, Вейль, Курант–Фишер, MDL-ранг) под капстоуном;
  matrix_svd_nonneg_and_mdl_antitone — неотрицательность
  сингулярных значений ∧ антинтонность MDL-ошибки.
- **BUGFIX ClosureReport (closure 281/315, 89%)**: пропущенная
  запятая после "GrowthStateViews" сливала две строки в один
  мусор-элемент (Budget-фасад не был капстоуном);
  исправлено — покрытие честно 89%.
- **Фасад Unified/ModelPretrain + EdgeTests (closure
  276/315, 88%)**: модель и предобучение (14 модулей) под
  капстоуном; memory_capped_and_time_correct — битовый кап
  консолидации ∧ корректность времени-до-capability.
- **Фасад Unified/StepExt (closure 258/314, 82%)**:
  расширения шага и компонентов (15 модулей Step/Core) под
  капстоуном; step_warmup_monotone_and_wd_bounded —
  warmup-монотонность ∧ weight-decay ограниченность.
- **Фасад Unified/GrowthExt (closure 242/313, 77%)**:
  расширения роста (10 модулей) под капстоуном;
  growth_renews_and_seed_survives — обновление возможностей ∧
  выживание посева.
- **Layer-6 теоремные модули как капстоуны (closure
  231/312, 74%)**: 21 Unified-модуль (AdvanceWitness,
  AnytimeMartingale, ArchitectureTheorem, CertifiedGrowth,
  ... TopLevel) добавлены в CAPSTONES — слой 6 вершины по
  определению.
- **Фасад Unified/BudgetExt (closure 206/312, 66%)**:
  бюджетные расширения (11 модулей) под капстоуном;
  budget_waterfill_and_lowrank — KV-водолив оптимален ∧
  блочно-низкоранговая экономия ⟺ 3r < (N−1)h.
- **Фасад Unified/OptStepExt (closure 192/311, 62%)**:
  оптимизационные расширения (12 модулей Step/Optimization)
  под капстоуном; opt_objective_monotone_and_bias_bounded —
  монотонность MDL-объектива ∧ измеримость инерционного
  смещения.
- **Фасад Unified/StepLaws (closure 178/310, 57%)**:
  теория шага (Step/Runtime/Sparsity, 10 модулей) под
  капстоуном; step_armijo_and_sgd_stable — достаточное
  убывание Armijo ∧ строгая стабильность SGD-шага.
- **Фасад Unified/DynamicsLaws (closure 166/309, 54%)**:
  динамика и омнимодальность (12 модулей) под капстоуном;
  dynamics_growth_and_distillation — счётный такофф ∧
  KL-контракция с бюджетом.
- **Фасад Unified/ProbInfo (closure 153/308, 50%)**:
  вероятностно-информационный блок (10 модулей) под
  капстоуном; info_not_free_and_detectable — бесплатного
  восстановления нет ∧ девиация обнаружима. ПОЛОВИНА
  библиотеки под капстоунами.
- **Фасад Unified/DataEnergy (closure 142/307, 46%)**:
  данные и энергия (12 модулей) под капстоуном;
  data_certified_and_thermodynamic — сертифицированный
  argmax ∧ холодный предел статсуммы.
- **Фасад Unified/GrowthLaws (closure 127/306, 42%)**:
  законы роста (10 модулей) под капстоуном;
  growth_balanced_and_conic — потенциал-телескоп ∧ конусная
  инвариантность данных.
- **Фасад Unified/AutonomyCore (closure 115/305, 38%)**:
  автономный контур (6 модулей) под капстоуном;
  autonomy_regret_and_stability — EW-регрет (склеенная
  цепочка) ∧ TTT BIBO-стабильность.
- **Фасад Unified/EnsembleTheory (closure 105/304, 35%)**:
  теория ансамблей (8 модулей) под капстоуном;
  merge_calibrated_and_exact — shift-инвариантность softmax ∧
  точность смешанной продукции.
- **Фасад Unified/CoreAlgebra (closure 96/303, 32%)**:
  компонентная алгебра (7 Core-модулей) под капстоуном;
  core_stable_and_optimal — демпфирование ошибки внимания ∧
  глобальная оптимальность риджа.
- **Фасад Unified/ArchitectureCore (closure 88/302, 29%)**:
  архитектурный блок (10 модулей) под капстоуном;
  architecture_invariant_and_economical — ортогональные
  волокна (инвариантность) ∧ конфигурационная экономия.
- **Фасад Unified/Budget.lean** (ClosureReport 77/296, 26%):
  экспорт бюджетного блока (WaterFilling/FlopsEconomy/BitAlloc/
  ThermoCondensation/WaterFillingMoE) +
  budget_allocation_and_distillation — сбалансированная
  аллокация бит и дистилляционный телескоп одновременно.
- **Фасад Unified/DataCentric.lean**: pruning_dichotomy —
  гладкие+плотные таргеты восстанавливаются (≤ L·δ),
  состязательные — NFL ≥ 1; успех pruning определяется
  данными, не алгоритмом отбора.
- **DataPruning (Sorscher et al. 2220.09597 контекст;
  Paul–Santamaria NeurIPS 2023 NFL)**: pruning_nfl — ученик,
  зависящий только от kept-данных, не различает два таргета,
  расходящихся в выброшенной точке: сумма ошибок ≥ 1
  (прореживание не бесплатно);
  pruning_recovery_bound — липшицев таргет + плотная сетка
  ⟹ выброшенная точка восстанавливается с ошибкой ≤ L·δ;
  pruning_free_for_constant — на константных таргетах
  pruning бесплатен (ошибка 0) — цена возникает только на
  информативных точках.
- **Фасад Unified/Robustness.lean + коридор**: экспорт
  robustness-теории (слой 6) + robust_growth_corridor —
  шумные данные дают нижнюю границу бюджета
  B0 ≥ c·D·σ/(δ·G), бюджет — верхнюю границу роста
  C T ≤ (1+α)^(B0/c)·C0 (данные и физика зажимают рост).
- **Edge-тесты RobustnessLaw**: достижимость границы
  (f(x)=x, L=1); несовместимость (уклон 2 на шаге 1/2 ⟹
  L=1-интерполятор не существует, требуется L ≥ 4);
  step cap (σ=δ=1 ⟹ η ≤ 1).
- **Населённость CertifiedTransition**
  (`witness_certifiedTransition`): реальный witness-переход
  (wS0, wU0) порождает сертификат; certified_family_linked
  добавлен в AxiomCheck-капстоуны (21).
- **Capstone-мост certified_family_linked**: семейство
  CertifiedTransition ПОРОЖДАЕТ LinkedHAGIInvariant —
  телескопы бюджета/риска/роста становятся полями связанного
  инварианта; путь сертификатов → капстоун замкнут
  (AxiomCheck-кандидат).
- **Горизонтный рост CertifiedTransition**
  (`certified_trajectory_capability`): C T = C 0 + Σ growGain —
  точный телескоп capability из exec-переходов; триада
  горизонтных гарантий (бюджет/риск/рост) замкнута.
- **Горизонтный риск CertifiedTransition**
  (`certified_trajectory_risk`): R T = R 0 + Σ risk spends —
  телескоп защищённого риска из exec-переходов.
- **Горизонтизация CertifiedTransition**
  (`certified_trajectory_budget`): семейство сертифицированных
  переходов телескопирует ТОЧНЫЙ бюджетный ledger
  S T = S 0 − Σ spends — ресурсы только через exec-переходы.
- **CertifiedTransition **
  (`Hagi/Model/CertifiedTransition.lean`): зависимый
  сертификат перехода — exec (S' = advance S u), progress
  (verify-спуск > 0), safety (риск-лимит), resources (точный
  бюджетный ledger); конструктор
  certifiedTransition_of_advance из операциональных условий.
- **PL-линейная сходимость**
  (`Hagi/Optimization/PLConvergence.lean`,
  `pl_linear_convergence`): Поляк–Лоясевич — градиентное
  доминирование + честный градиентный шаг ⟹
  E t − E* ≤ (1−μ/L)^t·(E 0−E*) — first-order оптимальность
  без выпуклости.
- **План достижимости цели** (`plan_reachability`): при
  конусной отдаче, честном бюджете и достаточном горизонте:
  C* ≤ C T ∧ T·c ≤ B — интегральный критерий осуществимости
  плана (takeoff × horizon × budget).
- **Достаточный горизонт цели** (`sufficient_horizon`):
  (C*/C 0) ≤ (1+γk)^T ⟹ C* ≤ C T — достаточное время взлёта
  (лог-форма T ≥ log(C*/C 0)/log(1+γk)); симметрия
  минимальному бюджету.
- **Лог-форма минимального бюджета**
  (`minimal_budget_log`): B ≥ c·log(C*/C 0)/log(1+α) — явная
  формула цены экспоненциального роста цели.
- **Цель требует бюджета** (`target_needs_budget`): достижимость
  C* на горизонте ⟹ C* ≤ (1+α)^{B/c}·C 0 — минимальный бюджет
  цели (лог-форма B ≥ c·log(C*/C0)/log(1+α)).
- **AxiomCheck: 20 капстоунов** (+ growth_corridor —
  двусторонний закон роста) и граничный T=0 тест коридора.
- **Коридор роста** (`growth_corridor`): композиция нижней
  (конусный взлёт) и верхней (бюджетный потолок) границ:
  (1+γk)^T ≤ (1+α)^{B/c} — согласованность скорости роста с
  ресурсами; закон роста двусторонне замкнут.
- **Бюджетный потолок роста**
  (`budget_capability_ceiling`): честный бюджет (тратит ≥ c за
  шаг, бюджет ≥ 0) ⟹ T·c ≤ B; с C-cap:
  C T ≤ (1+α)^{B/c}·C 0 — ресурсный предел экспоненты роста.
- **Достижимость k-ресурсной границы**
  (`compute_scaling_multi_attained`): аллокация
  mᵢ = √aᵢ·s достигает (Σ√aᵢ)²/Σmᵢ — многоресурсный
  compute-оптимум точный, семейство scaling-теорем полно.
- **AxiomCheck-гейт: 18 капстоунов** (добавлены закон роста
  advance_trajectory_takeoff и отбор safe_selection_productive)
  — итоговый алгоритм под защитой CI.
- **Отбор безопасного шага** (`safe_selection_productive`):
  итоговый алгоритм — если хоть один кандидат имеет
  положительный decrease-сертификат, отбор по максимуму
  сертификата даёт продуктивный шаг (bestDecrease).
- **P2.9 разбиение состояния**
  (`Hagi/System/GrowthStateViews.lean`): GrowthState разложен
  на 5 сущностей (ModelPart/MetricsPart/MemoryPart/
  OptimizerPart/ResourcePart) с проекциями toParts/ofParts и
  раунд-трипом (rfl) + инъективностью — канон не сломан.
- **P3.14 граничные тесты** (`Hagi/Examples/EdgeTests.lean`):
  тестовая триада завершена — продуктивные (witness-серия,
  attained), отрицательные (obstruction-серия), граничные
  (γ=0 takeoff, M=0 speed limit, ε=0 термодинамика, симметрия
  и singleton для compute_scaling).
- **P2.10 StepCertificate**
  (`Hagi/System/StepCertificate.lean`): полный сертификат шага —
  базовый Certificate (спуск/риск/стоимость) + gen-полоса epsG;
  конструктор stepCertificateOfParts + звучность.
- **P2.11 фасад Master** (`Hagi/Unified/Master.lean`):
  сведение четырёх Master-форм к одной иерархии: главная —
  premises_to_certified; MasterHAGI/trunc/Coupled/
  GrandSynthesis — тонкие специализации (срезы).
- **P1.8 фасад SafeStep** (`Hagi/Unified/SafeStep.lean`):
  единый контракт безопасного шага — StageCalculus + все
  варианты SafeQP (базовый/стохастический/адаптивный/KLS) +
  Joint; общий контракт — окно безопасности StageInput.
  P1 полностью закрыт (P1.4–P1.8).
- **P1.7 фасад GrowthTheory**
  (`Hagi/Unified/GrowthTheory.lean`): единая точка теории
  динамики и насыщения — телескопные законы, конусная
  динамика, FrontierScaling, Saturation, speed limit,
  advance-закон роста.
- **P1.6 фасад Concentration** (`Hagi/Unified/Concentration.lean`):
  реестр концентрационного слоя (хордовое ядро, Бернулли-MGF,
  Азума, Фридман ± anytime/union, Чернов-CGF); объекты
  различны (iid/мартингал/adaptive), дублей нет.
- **P1.5 фасад Pinsker** (`Hagi/Unified/Pinsker.lean`): единая
  точка входа семейства Пинскера — реестр трёх форм
  (функциональная pinsker4_fin, TV-форма pinsker_sqrt_kl,
  энтропийная непрерывность); канон Prelude.klDef/entDef/tvDef.
- **P1.4 фасад Fannes** (`Hagi/Unified/Fannes.lean`): единая
  точка входа неравенства Фанне — реестр четырёх слоёв
  (матричный DiscreteFannes, вероятностный FannesSmooth,
  комбинаторный FannesComplete, термодинамический NernstFannes);
  дубликатных определений нет, канон Prelude.entDef/tvDef.
- **P0.1 (закрыт ранее)**: `advance_decompose` — единый
  переход: advance = compress(joint(merge(grow(prepare))));
  полный P0 закрыт: P0.1 мост, P0.2 закон роста, P0.3 полосы.
- **P0.2 мост (закон роста advance)**:
  `advance_trajectory_takeoff`: траектория настоящих
  advance-циклов с конусными посылками (k·C ≤ D, γ·D ≤
  измеренный growGain) даёт C T ≥ (1+γk)^T·C 0 —
  пересчитываемый gain согласован с экспоненциальным
  законом; конфликт линейного/экспоненциального роста
  разрешён.
- **P0.3 рефакторинг**: `S'.gen = S.gen` УДАЛЁН из
  CorePremises/FullCycleRefinement; вместо plumbing-равенства —
  измерительная связь: компонентная полоса
  Qvec S'.gen i ≤ Qvec S.gen i + epsQ (CorePremises) и
  |ΔQvec i| ≤ epsG (FullCycleRefinement, параметр epsG) —
  метрики обобщения ограничены фактическим изменением,
  двусторонняя честность с Qgen-конъюнктом.
- **Холодный предел Z(T)** (`partition_cold_limit`, NTL):
  при T → 0+ Z(T) → число глобальных минимизаторов —
  вырожденные уровни вносят 1, возбуждённые вымерзают;
  холодный двойник partition_hot_limit.
- **Speed limit обучения**
  (`learning_time_lower_bound`, Seroussi et al. arXiv
  2307.14653, дискретный аналог): E(t+1) ≥ E t − M ⟹
  E 0 − E T ≤ T·M — спуск на Δ требует ≥ Δ/M шагов;
  новый модуль Hagi/Dynamics/SpeedLimit.lean.
- **K-ресурсная compute-граница**
  (`compute_scaling_multi`): Σ aᵢ/mᵢ ≥ (Σ √aᵢ)²/Σ mᵢ для
  любого конечного набора ресурсов — многоресурсная аллокация
  вычислений (индукция по 2-ресурсной базе).
- **Достижимость compute-границы**
  (`compute_scaling_bound_attained`): аллокация
  m = √a·s, n = √b·s достигает (√a+√b)²/(m+n) — граница
  точная, оптимум вычислений на линейной пропорции.
- **Compute-optimal нижняя граница**
  (`compute_scaling_lower_bound`, Jeon–Van Roy arXiv
  2407.01456): потери a/m + b/n при линейной стоимости C=m+n
  удовлетворяют L ≥ (√a+√b)²/C для любой аллокации — бюджет
  ограничивает потери снизу (Engel-форма Коши–Буняковского).
- **Двухуровневая теплоёмкость > 0**
  (`two_level_meanEnergy_strictMono`, Neural Thermodynamic
  Laws arXiv 2505.10559): ⟨E⟩(T) = ε/(1+e^{ε/T}) строго ↑ по
  T — положительная теплоёмкость, охлаждение концентрирует
  на основном уровне.
- **Вероятностная композиция**
  (`probable_conclusion`): потраекторная импликация
  «все посылки ⟹ Q» + per-посылочные 1−δ ⟹
  P(Q) ≥ 1 − |S|·δ — финальное звено: выборка → посылки →
  детерминированная теорема → итоговое свойство.
- **Union bound для блока посылок**
  (`prodPq_iff`, `prodPq_union_finset`,
  `premises_union_confidence`): конгруэнтность prodPq по
  эквивалентным предикатам; общий union bound по Finset;
  k посылок с вероятностью ≥ 1−δ каждая ⟹ все одновременно
  с вероятностью ≥ 1 − |S|·δ.
- **Мост Фридмана ⇒ посылки** (`freedman_confidence`):
  если эмпирическая посылка A потраекторно эквивалентна
  неотрицательности суммы мартингал-разностей, то
  P(A) ≥ 1 − exp(−Δ²/(2(nσ+bΔ))) — anytime-валидная
  уверенность в h_emp-посылках (последний разрыв аудита v3).
- **Замыкание мастер-цепочки**
  (`premises_to_certified`): конусные посылки trunc +
  операционные компоненты ⟹ CertifiedHAGIInvariant напрямую
  (capability_growth из trunc_premises_takeoff, без старой
  статичной effects-семантики).
- **Полный взлёт из посылок trunc**
  (`trunc_premises_takeoff`): композиция — конусный блок
  MasterHAGI_trunc + шаги C/G дают C T ≥ (1+α)^T·C 0.
- **Конусная инвариантность посылок trunc**
  (`trunc_cone_invariance`): блок h_emp_{cone0, C_cap, dyn,
  beta} поддерживает (α/γ)·C t ≤ D t индукцией по t — ядро
  конусного блока аудита v3.
- **Экспоненциальный взлёт** (`h_emp_takeoff_exponential`):
  конусное соотношение k·C ≤ D на каждом шаге ⟹
  C T ≥ (1+γk)^T·C 0 — неравенственная версия
  cone_perron_growth.
- **Комбинированный 2D-рост**
  (`h_emp_gain_geometric`): C-телескоп + D-геометрия дают
  C T ≥ C 0 + γ·D 0·(1−ρ^T)/(1−ρ) при ρ<1 — явная
  нижняя оценка capability из конусного блока посылок.
- **Линейный рост при ρ=1**
  (`h_emp_dyn_linear_growth`): без геометрической скидки —
  D T ≥ D 0 + (β−ε)·T·C 0 при монотонной C и β ≥ ε.
- **Мост h_emp_dyn ⇒ явная оценка**
  (`h_emp_dyn_explicit`): возмущённая посылка MasterHAGI_trunc
  ρ·D+β·C−ξ ≤ D' при ξ ≤ ε·C, C ≥ 0 даёт
  D T ≥ ρ^T·D 0 + (β−ε)·Σ ρ^{T−1−i}·C i.
- **Монотонное следствие конуса**
  (`cone_explicit_monotone`): при монотонной capability
  (C i ≥ C 0 ≥ 0, β,ρ ≥ 0) — одночленная оценка
  D (T+1) ≥ ρ^{T+1}·D 0 + β·C 0.
- **Явная нижняя оценка конуса**
  (`cone_explicit_lower`): D T ≥ ρ^T·D 0 +
  β·Σ_{i<T} ρ^{T−1−i}·C i — замкнутая форма T-кратной
  подстановки конусного неравенства.
- **Термодинамический потолок свидетеля**
  (`witness_step_landauer_cap`,
  `witness_horizon_landauer_cap`): запись параметров
  witness-цикла ≤ 2/cUnit бит/шаг, горизонт ≤ 100/cUnit —
  Landauer-гейт продуктивной траектории.
- **Продуктивный T=2 свидетель итогового инварианта**
  (`certified_invariant_advance_witness`): CertifiedHAGIInvariant
  на T=2 из РЕАЛЬНЫХ advance-переходов wTraj (энергия убывает
  30→23, capability 1→4 = 2², риск 0, бюджет 100−2t) — ответ на
  критику 1 аудита v3 (вакуумность мастер-цепочки при T≥2).
- **Разводка CycleCertificate×2** : System-версия
  переименована в StageCycleCertChain; параметрический
  Model.CycleCertificate — единственный с этим именем.
- **Мост advance→verify** (`advance_verify_decrease_pos`):
  decrease шага канонической advance-семантики строго
  положителен при gap ≥ 0, η ≥ 0 и оплаченной компрессии
  (κs < 2·gain) — связка StageSemantics с certify-слоем.
- **Отчёт замыкания капстоунов** (`scripts/ClosureReport.py`,
  CI): 50/277 модулей в транзитивном замыкании итоговых теорем
  (MasterHAGI, GrandSynthesis, StageSemantics + мосты +
  CertifiedEstimator + фасады P1/P2: Master/SafeStep/
  GrowthTheory/Concentration/GrowthStateViews), 217 —
  библиотечный слой (реестр).
- **Сравнение с возмущением** (`cone_comparison_perturbed`):
  ξ_t ≤ ε·C_t поглощается сдвигом β→β−ε (ε ≤ β) —
  возмущённая динамика доминируется системой с эффективным
  коэффициентом.
- **Монотонное сравнение конуса** (`cone_comparison`,
  аудит v3 Phase 3): неравенства динамики доминируются
  решением системы с равенствами (γ,ρ,β ≥ 0, БЕЗ C_cap);
  cone_perron_growth — случай равенства.
- **CI-гейт аксиом** (`scripts/AxiomCheck.lean`): 12 капстоунов
  (MasterHAGI, grand_synthesis, witness-серия, мосты CorePremises,
  термодинамика) проверяются на стандартные аксиомы Lean при
  каждом CI-прогоне .
- **Взлёт свидетеля** (`wTraj_takeoff`): gate alpha·C ≤ gain
  (α=1, gain=C_t: 1,2,4) на каждом шаге ⟹ экспоненциальный
  рост C_0·2^t ≤ C_t — связка Trajectory с cone/takeoff.
- **Инварианты продуктивной траектории**
  (`wTraj_budget_risk_invariants`): бюджет = 100−2t,
  неотрицателен; риск = 0 на всём горизонте T=3 — сертификаты
  бюджета и риска для каждого перехода .
- **Многошаговый продуктивный witness** (`wTraj_productive`):
  на канонической семантике Trajectory существует траектория
  T=3, каждый шаг строго продуктивен (gain>0, энергия −3,
  capability растёт), состояния — только через advance
  .
- **Мост CorePremises (grow)**
  (`core_premises_grow_operational`): компонент 2 (h_emp_grow)
  выводится из замены приора на Гиббс-учителя:
  ⟨γ,ℓ⟩ ≤ energy − T·(KL+KL).
- **Мост CorePremises (merge)**
  (`core_premises_merge_operational`): компонент 3
  (h_emp_merge) выводится из реального усреднения логитов:
  CE(mid) ≤ средн CE − jensenGap.
- **Мост CorePremises (compress)** 
  (`core_premises_compress_operational`): компонент 13
  (граница энергии сжатия) выводится из реального gridQ
  через липшицевость: E(g x) − jointE ≤ κ·|x − g x|.
- **Мост CorePremises** (`core_premises_joint_operational`):
  компонент 8 (h_emp_smooth) CorePremises выводится из
  реальной E(params−η•stepDir) с L-градиентом + монотонности
  энергий стадий (E(params) ≤ mergeEnergy).
- **Мост grow→операция** (`grow_gain_from_mirror`,
  `grow_gain_nonneg`): выигрыш Гиббс-эксперта = T·(KL(ρ₀‖γ)+
  KL(γ‖ρ₀)) — T-кратная дивергенция Джеффриса; неотрицателен
  (h_emp_grow пол выводится из KL-неотрицательности).
- **Мост compress→операция** (`compress_energy_bridge`):
  |E x − E(gridQ Δ x)| ≤ κ·Δ/2 — изменение энергии при
  реальном квантовании выводится из липшицевости E;
  замыкает h_emp_lip/h_emp_dist этапа сжатия.
- **Мост аудит→операции** (`joint_emp_smooth_derived`,
  DerivAlong): эмпирическое условие гладкости этапа Joint
  ВЫВОДИТСЯ из L-липшицева градиента реальной функции
  потерь: E(w−ηd) ≤ E(w) − η·DE(w)d + Lη²‖d‖²/2 — эффекты
  стадии как следствие операции, а не предпосылка.
- **LayerLint: закрыты слепые зоны** (Geometry, Numerics,
  Optimization, Percolation, Planning; External→Optimization
  в LAYER_EXCEPTIONS как остров MemT); Hagi.Ensemble.UniformCert
  зарегистрирован в Hagi.lean .
- **Термодинамика Z(T)** (`partition_strictMono`,
  `partition_hot_limit`): статистическая сумма Гиббса строго
  возрастает по T (нагрев размытие, охлаждение концентрация);
  T → ∞ ⟹ Z → |V| (полное размытие).
- **Единственность минимума дистилляции**
  (`distillation_floor_attained_iff_kl_zero`): студент
  достигает пола free energy ⟺ KL(σ‖γ)=0.
- **KL-дистилляция = зеркальный шаг** (`context_distillation_identity`,
  `gibbs_variational_floor`, Cortex §3.3 ↔ MirrorDescent):
  T·KL(σ‖γ) = ⟨σ,ℓ⟩+T·KL(σ‖ρ₀)+T·logZ; учитель-Гиббс —
  вариационный минимум free energy (floor ≥ −T·log Z).
- **Термодинамика консолидации** (`Hagi/Model/MemoryConsolidation`):
  consolidation_bits_cap (запись F бит параметров в бюджете B —
  F ≤ B/cUnit), consolidation_no_free_lunch (бюджета < n·cUnit
  недостаточно для записи n бит — мост Cortex ↔ Landauer).
- **Условие реализуемости shared down-projection**
  (`shared_down_projection_iff`, Cortex A.4): ∃L, L·H=Δ ⟺ каждая
  строка Δ — линейная комбинация строк H (row(Δ) ⊆ row(H)).
- **MoE shared expansion** (`moe_shared_expansion_identity`,
  Cortex arXiv 2610.20399v1 Appx A.5, eq.18): при Σ a_e = 1
  общая ветка сворачивается в каждого эксперта без изменения
  выхода: F + S = Σ a_e·(E_e + S) — сохранение функции при
  минимальном числе параметров.
- **Углы сферического симплекса** (`Hagi/Geometry/SphericalSimplex`,
  arXiv 2610.31592v1): dihedral_count (K(n)=n(n+1)/2 упорядоченных
  пар граней), dihedral_angle_strictMono (θ(x)=arccos(1/x) строго
  возрастает), dihedral_angle_lt_pi/lt_pi_div_two (sup=π, θ<π/2),
  excess_as_supplement/excess_pos (эксцесс = arccos(−1/x) > 0),
  euclid_sum_bounds ((π/3)K ≤ S_euc < (π/2)K при n ≥ 2).
- **GRPO-ядро** (`grpo_centered_sum_zero`, `grpo_advantage_pos`):
  сумма центрированных наград группы = 0; награда выше
  средней даёт положительное преимущество (§2.3).
- **Branching-теоремы Agima** (`branching_avoids_detectable_failure`,
  `branching_dominates_linear`): детектируемо-вредные ветви
  исключаются из выполнения; branching строго доминирует
  линейный агент на детектируемых отказах (§3.2).
- **Формализация arXiv 2610.26845v1** (`Hagi/Planning/Imagination`):
  forward_thinking_regret (argmax по неточной оценке теряет
  ≤ 2ε), imagination_compounding (K-шаговое воображение
  накапливает ≤ K·L·ε — обоснование деградации при K→∞),
  adaptive_first_sufficient (адаптивный формат: первый
  успешный предсказанный план не требует второго кандидата).
- **Скорость капитала на шаг** (`hedge_wealth_rate`):
  −T·log(∏Z_k)/n → ℓmin при n → ∞ — средний лог-капитал
  сходится к минимальным потерям (скорость T·log|V|/n).
- **Нернст-сэндвич капитала** (`hedge_wealth_nernst`):
  n·ℓmin − T·log|V| ≤ −T·log(∏Z_k) ≤ n·ℓmin − T·log(min ρ₀)
  — кумулятивная свободная энергия зажата энтропийным
  запасом и минимальным априорным весом.
- **Капитал hedge телескопирует** (`stepNorm`,
  `stepNorm_compose`, `hedge_wealth_product`): ∏_{k<n} Z_k =
  Z(ρ₀, Σℓ) — произведение пошаговых нормировок равно
  кумулятивной; потенциал-функция MWU/Hedge в замкнутой форме.
- **Утилиты наклона** (`expTilt_pos`, `expTilt_sum_one`,
  `expTilt_uniform_is_softDef`): наклон — распределение;
  softmax = наклон равномерного — триада
  softmax/hedge/наклон — одна операция.
- **Nernst-предел итераций hedge** (`mirrorIterate_energy_infimum`):
  ∀ε>0 ∃N ∀n≥N: ℓmin ≤ ⟨w_n,ℓ⟩ ≤ ℓmin+ε — итерированный hedge
  сходится по энергии к минимуму потерь (Z_n ≥ min ρ₀ ·
  e^{−nℓmin/T}, термодинамический предел T/n → 0).
- **Мост Optimization ↔ Numerics** (`mirrorStep_is_expTilt`):
  mirrorStep ρ₀ ℓ T = expTilt ρ₀ (−ℓ/T) — hedge-обновление и
  лог-форма фиксированного CE — одна операция наклона.
- **Инвариантность наклона + форма expm1** (`expTilt`,
  `expTilt_centering`, `expm1_form_diff`): expTilt p (c−⟨p,c⟩)
  = expTilt p c; u_k = p_k·(e^{s_k}−1) = q_k − p_k точно —
  ядро фикса Softmax Cancellation (eq.9) формализовано.
- **Центрирование §3 (eq.9)** (`centered_delta_sum_zero`,
  `sum_p_expm1_nonneg`): ⟨p,d⟩ = 0 для d = δ−⟨p,δ⟩; вход
  log1p неотрицателен (Йенсен: Σ p e^d ≥ 1) — корректность
  лог-пространственной формы soft-target CE.
- **Zero-sum декомпозиция фиксированного CE**
  (`fixed_ce_grad_sum_zero`): g_t = −Σ_{j≠t} g_j точно —
  сумма градиентов фиксированного CE равна нулю за
  пределами precision cliff (eq.7).
- **Равновесие маржи m* = log(c(1−λ|θ|)/(λ|θ|ε))**
  (`margin_equilibrium_value`, `adamw_normalized_bounds`):
  при |g| = c·e^{−m} равновесие AdamW даёт точное m* ≈
  log(1/ε); нормированный шаг ≤ 1 и ≥ |g|/(2ε) при
  |g| ≤ ε (§5 eq.11 завершён).
- **Формализация arXiv 2610.31642v1** (`Hagi/Numerics/SoftmaxFix`):
  ce_grad_sum_zero (градиент CE суммируется в 0 — анти-Softmax
  Collapse), logitMargin + margin_rest_sum + ce_loss_margin
  (маржа-форма фиксированного CE: L = softplus(−m)),
  adamw_equilibrium_magnitude (|g| = λ|θ|ε/(1−λ|θ|) ⟹
  m* ≈ log(1/ε) — равновесие маржи AdamW),
  distill_grad_self_zero (анти-Softmax Cancellation).
- **Сходимость энергии итераций**
  (`mirrorIterate_energy_converges`): убывающая и
  ограниченная снизу последовательность энергий ⟨w_n,ℓ⟩
  входит в ε-коридор над инфимумом — итерированный hedge
  сходится по энергии (полнота ℝ).
- **Монотонность энергии вдоль траектории**
  (`mirrorIterate_energy_monotone`): при фиксированных ℓ
  повторные шаги не поднимают энергию (⟨w_n,ℓ⟩ ≤ ⟨ρ₀,ℓ⟩).
- **Монотонность энергии hedge** (`mirror_energy_decrease`):
  ⟨mirrorStep ρ₀ ℓ T, ℓ⟩ ≤ ⟨ρ₀, ℓ⟩ — обновление никогда не
  поднимает ожидаемые потери (KL ≥ 0 + attainment + Йенсен
  выпуклости exp).
- **N-кратный полугрупповой закон** (`mirrorStep_zero_loss`,
  `mirrorIterate_cumulative`): траектория hedge за n шагов =
  ОДИН зеркальный шаг с кумулятивными потерями Σ_{k<n} ℓ_k.
- **Полугрупповой закон зеркального шага**
  (`mirror_step_semigroup`): два последовательных шага = один
  шаг с ℓ₁+ℓ₂ (нормировки согласованы: Z₂·Z₁ = Z₁₂) —
  траектория hedge за n шагов есть один шаг с кумулятивными
  потерями.
- **Классическая граница MWU T·log n**
  (`mirror_regret_uniform`): при равномерном старте регрет
  ≤ T·log n — KL(ρ*‖u) ≤ log n (Σρ log ρ ≤ 0); канонический
  результат экспоненциальных весов выведен из зеркального
  телескопирования.
- **Телескопированный регрет hedge/MWU** (`mirrorIterate`,
  `mirror_step_regret`, `mirror_regret`): суммарное превышение
  потерь обновляемых весов над целью ρ* ≤ T·KL(ρ*‖w₀) —
  KL-убыль телескопирует; полная regret-граница зеркального
  спуска (Модуль 3 аудита завершён).
- **Одношаговое тождество прогресса** (`mirror_progress_identity`):
  ⟨ρ,ℓ⟩ − F(γ) = T·(KL(ρ‖γ) − KL(ρ‖ρ₀)) — прирост расстояния
  Брегмана равен превышению потерь над полом; база
  телескопирования регрета MWU.
- **Гиббс = зеркальный шаг** (`gibbs_from_mirror`):
  вариационная грань Гиббса (R421) выводится из
  mirror_descent_floor при равномерной ссылке ρ₀=1/n —
  унификация Гиббс == MWU == EFE завершена (4 моста).
- **EFE-мост Active Inference** (`aif_efe_attainment`,
  `aif_efe_floor`): при ℓ = surprise − info gain минимизатор
  EFE — mirrorStep; единая грань доминирует любое убеждение —
  третий член унификации Гиббс == MWU == EFE.
- **Мост MWU ↔ зеркальный спуск** (`hedge_free_energy_step`):
  hedge-обновление = mirrorStep при T=1/η; F(γ) ≤ 2⟨ℓ⟩_w при
  ηℓ ≤ 1/2 — изоморфизм MWU и вариационного принципа как
  теорема (пункт 3 аудита).
- **Достижимость пола зеркального шага**
  (`mirror_descent_attainment`): F(γ) = −T·log Z точно —
  γ = mirrorStep минимизирует свободную энергию; полнота
  унификации Гиббса/MWU/EFE.
- **Единый вариационный принцип зеркального спуска**
  (`mirrorStep`, `mirror_descent_identity`, `mirror_descent_floor`):
  argmin ⟨ρ,ℓ⟩+T·KL(ρ‖ρ₀) = ρ₀·e^{−ℓ/T}/Z, минимум −T·log Z —
  унификация Гиббса, MWU/Hedge и EFE Active Inference
  (Модуль 3 аудита).
- **РМ с систематическим смещением** (`robbins_monro_bias`):
  при δ_k ≤ D·η_k последовательность входит в коридор над D
  (центрирование y = x−D; ветка y₀ ≤ 0 — тривиальна).
- **РМ по модулю** (`robbins_monro_abs`): закон на |y| гасит
  |y| к нулю при любом знаке старта (применение ядра к |y|).
- **Ядро Роббинса-Монро** (`robbins_monro_decay`): η_k ∈ [0,1]
  с расходящейся суммой ∧ x_{k+1} ≤ (1−η_k)x_k ⟹ x_k → 0
  (∏(1−η) ≤ e^{−Ση} → 0) — детерминированное ядро
  стохастической аппроксимации и затухающих learning rate.
- **Достижимость Anderson × momentum** (`anderson_momentum_reach`):
  ∀ε>0 ∃T ∀s≥T: e_s ≤ δ/(1−θq−β)+ε — сырая инерция + AA
  также входит в коридор за конечное время (ρ(θq,β)).
- **Нулевая инерция как оптимальная стратегия**
  (`zero_inertia_optimal`): β=0 ⟹ чистое сжатие (θq)^k и пол
  δ/(1−θq) — итоговая конфигурация ускоренного метода:
  Anderson-направление + нулевая инерция + бисекция шага.
- **Затухающее расписание импульса** (`momentum_schedule`):
  β_k ≤ bbar ∧ q+bbar < 1 ∧ e ≥ 0 ⟹ затухание со скоростью
  ρ(q, bbar) — расписание импульса безопасно при равномерном
  бюджете инерции.
- **Полная стоимость двухфазной стратегии** (`two_phase_total`):
  Σ_{k<T+n} e_k ≤ B₁ + e_T(1−q'ⁿ)/(1−q') + n·δ/(1−q) —
  бюджет полной ошибки coarse+fine складывается из
  измеренной грубой и сертифицированной точной части.
- **Коррекция улучшает и пол** (`nesterov_floor_beats_plain`):
  δ/(1−q) ≤ δ/(1−q−β) — коррекция Нестерова доминирует сырой
  heavy-ball по обеим осям: скорость (nesterov_beats_plain)
  и пол неточности.
- **Время входа Anderson × Нестеров**
  (`nesterov_anderson_entry`): T ≥ log(e₀/ε)/
  log((1+β)/(θq+β)) с коридором δ/(1−θq)+ε — полная
  композиция: фактор, пол и время входа ускоренного
  квантованного метода явны.
- **Line search: скобка и бисекция** (`step_bracket`,
  `bracket_bisect`): анти-монотонное условие приёма шага ⟹
  s принят ∧ 2s отвергнут локализует порог в [s, 2s);
  бисекция делит скобку пополам за шаг — экспоненциальная
  локализация оптимального шага.
- **Суммарная ошибка коррекции** (`nesterov_total_error`):
  Σ_{k<n} e_k ≤ e₀(1−q'ⁿ)/(1−q') + n·δ/(1−q) — полный
  бюджет ошибок ускоренного метода (геометрия + пол).
- **Явный горизонт входа коррекции** (`nesterov_entry_horizon`):
  ∃T ≥ log(e₀/ε)/log((1+β)/(q+β)) с коридором пол+ε — время
  входа ускоренного метода выражено в явных шагах.
- **Достижимость при коррекции Нестерова**
  (`nesterov_achievability`): ∀ε>0 ∃T ∀s≥T: e_s ≤ δ/(1−q)+ε —
  скорректированный метод входит в коридор над полом за
  геометрическое время с фактором (q+β)/(1+β).
- **Мост Нестеров × модель** (`trajectory_potential_nesterov`):
  потенциал состояний под скорректированным законом затухает
  с фактором (q+β)/(1+β) — ускорение с коррекцией напрямую
  управляет потенциалом модели.
- **Anderson × Нестеров** (`nesterov_anderson`): фактор
  (θq+β)/(1+β), пол δ/(1−θq) — полная граница ускоренного
  квантованного метода с коррекцией: θ ускоряет и процесс,
  и пол; β платит только за скорость.
- **Пол неточной коррекции Нестерова** (`nesterov_floor`):
  закон с δ даёт фактор (q+β)/(1+β) и пол δ/(1−q) — инерция
  улучшает только переходную скорость, пол не меняет.
- **Монотонность фактора Нестерова** (`nesterov_factor_monotone`):
  (q+β)/(1+β) возрастает по β при q<1 — и в скорректированном
  законе оптимальный импульс нулевой; вывод модуля: ускорение
  — только через направление (Anderson θ·q), импульс — цена.
- **Доминирование коррекции** (`nesterov_beats_plain`):
  (q+β)/(1+β) < ρ(q,β) при β>0 — коррекция направления
  строго быстрее сырого импульса: механизм ускорения один.
- **Коррекция Нестерова** (`nesterov_corrected`): look-ahead
  закон e_{k+1}+β(e_{k+1}−e_k) ≤ q·e_k ⟹ эффективный фактор
  (q+β)/(1+β) — механизм истинного ускорения: деление на
  (1+β), а не добавка к фактору.
- **Ускоренный вход потенциала в коридор**
  (`trajectory_accelerated_entry`): неточный инерционный
  закон на потенциале ⟹ ∃T ∀s≥T: Φ(S_s) ≤ δ/(1−q−β)+ε —
  ускоренный цикл выводит модель в коридор за конечное
  логарифмическое время.
- **Momentum: оптимум импульса** (`momentum_optimal_beta` +
  `momentumRate_zero_beta`): ρ(q,0)=q < ρ(q,β) при β>0 — в
  рамках закона ошибки чистый градиент строго оптимален;
  ускорение Нестерова — через коррекцию направления.
- **Momentum: суммарная ошибка** (`momentum_total_error`):
  Σ_{k<n} e_k ≤ C(1−ρⁿ)/(1−ρ) — бюджет полной ошибки
  ускоренного метода конечен и контролируется геометрией.
- **Мост ускорение × модель** (`trajectory_potential_momentum`):
  потенциал состояний Φ(S_t), подчиняющийся инерционному
  закону, затухает со скоростью ρ(q,β) — ускоренный алгоритм
  напрямую управляет потенциалом модели.
- **Anderson × Momentum** (`anderson_momentum_compose`):
  ускоренная неточная рекурсия (фактор θ·q, инерция β,
  неточность δ): скорость ρ(θq,β), пол δ/(1−θq−β) — полная
  граница ускоренного квантованного метода.
- **Momentum: точная граница устойчивости** (`momentum_rate_ge`):
  q+β ≤ ρ(q,β) — грубая сумма есть НИЖНЯЯ граница истинной
  скорости: условие q+β<1 из momentum_bound точно (ρ<1 ⟺
  q+β<1), инерция всегда дороже грубой оценки.
- **Momentum: переключение точности** (`coarse_to_fine`):
  после смены режима в момент T ошибка следует инерционному
  закону НОВОГО режима (пол δ₂/(1−q₂−β₂), скорость ρ₂) с
  новыми начальными данными — композиция полов coarse-to-fine.
- **Momentum: явный горизонт входа** (`momentum_entry_horizon`):
  ∃T ≥ log(C/ε)/log(1/ρ): ∀s≥T ρ^s·C < ε — время входа в
  коридор логарифмично по C/ε (скорость ускорения явна).
- **Momentum: достижимость качества** (`momentum_achievability`):
  ∀ε>0 ∃T ∀s≥T: e_s ≤ δ/(1−q−β) + ε — ускоренный неточный
  метод входит в коридор над полом за геометрическое время.
- **Momentum: направление бьёт инерцию**
  (`momentum_direction_beats_inertia`): θ<1 ⟹
  ρ(θq, β) < ρ(q, β) при любом β — Anderson-ускорение
  (улучшение фактора до θ·q) доминирует цену инерции:
  ускоряться следует улучшением направления.
- **Momentum: цена инерции точна** (`momentum_beta_strict_cost`):
  β > 0 ⟹ ρ(q,β) > q — импульс сам по себе НЕ ускоряет;
  выигрыш приходит только через улучшение направления
  (уменьшение q, как в Anderson θ·q), β — только цена.
- **Momentum: пол при неточности** (`momentum_floor`):
  e_{k+1} ≤ q·e_k + β·e_{k−1} + δ ⟹ e_k ≤ δ/(1−q−β) +
  max(x₀, x₁/ρ)·ρ^k — импульс не ухудшает стационарный пол
  чистого сжатия (аналог inexact_contraction_floor).
- **Momentum: скорость ускорения** (`momentum_bound` +
  `momentumRate_char`): инерционная рекурсия
  e_{k+1} ≤ q·e_k + β·e_{k−1} затухает геометрически со
  скоростью ρ=(q+√(q²+4β))/2 (корень ρ²=qρ+β): e_k ≤
  max(e₀,e₁/ρ)·ρ^k при q+β<1 — импульс не ломает сжатие,
  цена инерции точна (ρ→q при β→0).
- **Положительный чистый прирост** (`admit_gated_net_gain`,
  P5/этап 6): gainOk-сертифицированные циклы ⟹
  capability(k) ≥ cap0 + λM·Σspend + λR·Σrisk + k·ε —
  саморазвитие с сертификатом чистой пользы (зеркало
  MemoryCycle.gainOk на траекториях advance).
- **Единый инвариант контроллера** (`controller_horizon_bound`,
  этап 6): k ≤ min(budget0/g, (Rmax−risk0)/ρ) — горизонт
  ограничен минимумом структурного и рискового потолков;
  бюджетная ось ограничивает качество (budget_stops_growth).
- **Риск-кэп останавливает** (`risk_cap_bounds_horizon`,
  этап 6): ρ ≤ per-cycle риск ∧ risk(k) ≤ Rmax ⟹
  k ≤ (Rmax − risk0)/ρ — накопление риска ограничивает
  горизонт (третья ось контроллера: бюджет/риск/структура).
- **Структурный рост оплачен** (`experts_pays_budget`, MemT
  P1): эксперты = структурный масштаб: g ≤ spend ∧ budget ≥ 0
  ⟹ experts(k) ≤ experts(0) + budget(0)/g — экспансия
  архитектуры без ресурса невозможна.
- **Критерий остановки** (`budget_stops_growth`, этап 7):
  цель дороже бюджета (Qtarget > cap0 + budget0/c) ⟹
  недостижима ни на каком горизонте с неотрицательным
  бюджетом — контрапозиция оплаченного роста.
- **Канон 2.1: единый KL/энтропия/TV** (`kl_tilted_decompose`,
  `entDef_eq_shannon`): все модули
  (DField, Distill, Variational, FreeEnergy, DBridge,
  DistillRecursion, NessDissipation, CrossModalGap,
  MDLThreeCurrency, Insight, PlasticityLedger,
  InfoNCE, PPT) используют
  ArchitectureTheorem) используют
  канонический klDef напрямую (дубликаты KLdiv/kldiv/kldiv'
  и их rfl-мосты удалены, аудит 2026-10-24).
- **Интегральный сертификат траектории**
  (`integral_trajectory_certificate`, уровень E): единая
  теорема — точные леджеря ∧ ресурсная граница роста,
  композиция уровней A→B→D с явными предпосылками.
- **Рост оплачен** (`growth_pays_budget`, уровень D):
  c·gain_t ≤ spend_t ∧ budget_k ≥ 0 ⟹ capability(k) ≤
  capability(0) + budget(0)/c — прирост качества ограничен
  ресурсом: сертификат саморазвития опирается на
  ресурсный сертификат.
- **Телескопирование траектории** (`trajectory_cycle_ledgers`,
  уровень B этапа 4): budget(T) = budget(0) − Σ budgetSpend ∧
  capability(T) = capability(0) + Σ growGain — единая
  телескопная теорема из per-cycle сертификатов.
- **Сертификат одного цикла** (`advance_cycle_certificate`,
  уровень A этапа 4): advance точно исполняет бюджетный
  (полная 4-стадийная сумма), рисковый (накопление) и
  качественный (прирост) леджеря — из определений операторов
  (rfl-композиция P1.1+P1.3), без предположений согласованности.
- **Единый ресурсный учёт (P1.3)**: StageEffects +
  mergeCost/compressCost; операторы merge/compress и advance
  тратят их; verify.budgetSpend — полная 4-стадийная сумма;
  StageInput.h_costs_nn — 4-компонентная честность;
  advance_budget_le/budget_account/advance_decompose
  сохранены (rfl-симметричная миграция).
- **Единый потенциал: мост Φ1↔Φ2** (`potential_decrease_bridge`
  + `hagiPotential_special_eq`): при λ=1, ν≥0 убывание базового
  Φ=E+R и неубывание качества переносятся на канонический
  Φ=E+λR+ν·max(0,Q_target−Q); специализация λ=1,ν=0 совпадает
  с Φ1 (P1.2 большого плана).
- **Термодинамическое затухание смещения Top-K**
  (`cooling_topk_bias`, + `gibbs_tail_mass`): при
  n·e^{−s/T} < 1 смещение усечения Гиббс-учителя ≤
  (n·e^{−s/T})/(1−n·e^{−s/T}) — при T→0 цена Top-K-дистилляции
  обнуляется: охлаждение учителя восстанавливает допустимость
  (мост Distill × Gibbs).
- **Top-K дистилляция: линейный хвостовой бюджет**
  (`topk_distill_budget_tv`): Z ∈ (0,1] ⟹ KL ≤ α +
  (1−Z)/Z (−log Z ≤ (1−Z)/Z через log x ≤ x−1) — порог
  допуска в относительной массе хвоста без логарифмов.
- **Top-K дистилляция: бюджет смещения** (`topk_distill_budget`):
  Z ≥ e^(−β) ∧ KL(ученик‖усечённый) ≤ α ⟹ KL(ученик‖полный)
  ≤ α + β — смещение усечения входит в бюджет аддитивно.
- **Top-K дистилляция: KL-версия** (`kl_topk_shift`):
  KL(q‖p|_S/Z) = KL(q‖p) + log Z — Top-K-дистилляция не
  добавляет скрытых штрафов сверх цены усечения хвоста.
- **Top-K дистилляция: точное смещение CE** (`ce_topk_shift`):
  CE(q, p|_S/Z) = CE(q,p) + log Z — усечение учителя до Top-K
  смещает кросс-энтропию ровно на логарифм удержанной массы
  (MemT×HAGI P3: KL/Top-K контур обучения памяти).
- **GDN-2: корректность сброса** (`gdn2_reset_bound`):
  свежая память (M₀=0) ≤ b(1−qᵗ)/(1−q) — независимая
  траектория никогда не превышает потолок инжекции.
- **GDN-2: забывание начальных условий** (`gdn2_forgets_initial`):
  ‖iter M₁ t − iter M₂ t‖ ≤ qᵗ·‖M₁−M₂‖ — возмущения начальной
  памяти затухают экспоненциально (сжатие по начальным данным).
- **GDN-2: стабилизация памяти** (`gdn2_stabilizes`):
  ∀ε>0 ∃T ∀s≥T: ‖Mₛ‖ ≤ b/(1−q)+ε — рекуррентная память
  сходится в стационарный коридор потолка сжатия
  (qᵗ→0 через архимедов фильтр-аргумент).
- **GDN-2: ошибка чтения приближённой памяти** (`gdn2_read_error`):
  ‖Q·(Aₜ−Eₜ)‖ ≤ ‖Q‖·δ(1−qᵗ)/(1−q) — композиция сжатия,
  возмущения и линейного чтения: ошибка квантованной памяти
  не растёт с горизонтом чтения.
- **GDN-2: распространение ошибки** (`gdn2_perturbation`):
  при пошаговой ошибке реализации ≤ δ расхождение
  приближённой и точной траекторий памяти ≤ δ(1−qᵗ)/(1−q) —
  квантованная память не накапливает ошибку быстрее потолка
  сжатия (+ лемма линейности gdn2Update_sub).
- **GDN-2: чувствительность чтения** (`gdn2_read_sensitivity`):
  ‖Q·M₁ − Q·M₂‖ ≤ ‖Q‖·(‖M₁‖+‖M₂‖) — линейное извлечение не
  усиливает различие памятей сильнее нормы запроса (+ лемма
  rowSumNorm_sub_le).
- **GDN-2: горизонтная граница памяти** (`gdn2_horizon`):
  при q=‖(I−UᵀU)·D‖<1 норма T-шаговой памяти ≤ qᵀ‖M₀‖ +
  b/(1−q) — рекуррентная память MemT зажата стационарным
  потолком неточного сжатия (мост к InexactContraction).
- **GDN-2: граница нормы шага памяти** (`gdn2_step_bound`):
  ‖M̃'‖ ≤ ‖(I−UᵀU)·D‖·‖M‖ + ‖Uᵀ(ω⊙V)‖ — первая формализация
  оператора MemT-1.0 (arXiv:2610.26825): рекуррентная память
  подчиняется q·x+b рекурсии; связка с неточным сжатием даст
  стационарный потолок b/(1−q). План MemT×HAGI P0/P2.
- **Единая семантика перехода** (`advance_decompose`):
  advance = compress ∘ joint ∘ merge ∘ grow ∘ prepare (rfl) —
  этап P1.1 плана рефакторинга: измерения привязываются явно,
  эффекты цикла порождаются операторами, а не предполагаются.
- **Коридор температур** (`temperature_corridor`): если
  s/τ ≤ ε/log n, существует T (свидетель s/τ) с
  ОДНОВРЕМЕННОЙ различимостью (зазор s → лог-точность τ,
  thermal_blur) и качеством (E ≤ m + ε,
  gibbs_mixture_quality). Двустороннее расписание HAGI:
  T ∈ [s/τ, ε/log n] — ниже нельзя, выше не нужно.
- **Расписание → качество** (`gibbs_schedule_quality`): любая
  температура T > 0 с T·log n ≤ ε даёт Гиббс-значение в
  ε-окрестности глобального минимума (m − ε ≤ V_T ≤ m);
  T := ε/log n оптимальна по порядку — явная связь бюджета
  охлаждения с качеством обучения.
- **Суммарный бюджет качества шага** (`unified_step_budget`):
  Гиббс-ансамбль ε-оптимален по потерям (Tt·log n) +
  квантованное исполнение Δ/2-точно по параметрам — полный
  вычислительный компромисс «качество × вычисления» явный,
  слагаемые минимизируются независимо.
- **Геометрическое охлаждение** (`geometric_cooling_steps`):
  расписание Tₜ = T₀·ρᵗ достигает ε-качества исполняемой
  смеси за N ≥ log(T₀·log n / ε)/log(1/ρ) шагов —
  вычислительная сложность качества ε есть O(log(1/ε)) фаз
  охлаждения. Прямая формализация «минимизации вычислений»:
  экспоненциальная точность за логарифмическое число шагов
  управления температурой.
- **Термодинамическая цена обучения** (`landauer_cooling_floor`,
  + `geometric_temp_sum`): при геометрическом расписании
  Tₜ = T₀·ρᵗ суммарное рассеивание обучения (h_emp_cooling —
  ландауэровская стоимость стирания бит при температуре фазы)
  имеет нижнюю оценку cUnit·bits·T₀(1−ρ^N)/(1−ρ) и ограничено
  константой расписания cUnit·bits·T₀/(1−ρ). Вместе с
  `geometric_cooling_steps` — тройная граница «качество ×
  вычисления × энергия»: ε-качество за O(log(1/ε)) фаз при
  ограниченной энергии.
- **Оптимальный шаг решётки Δ\* = c** (`quantizer_optimal_step`):
  компромисс «точность × объём» f(Δ) = Δ + c·log(1/Δ)
  (ошибка квантования + ландауэровская цена log(1/Δ) бит)
  минимален ровно при Δ = c — доказано алгебраически из
  log x ≤ x − 1. Оптимальный уровень квантования весов равен
  удельной цене информации: формальный ответ на «максимальное
  качество при минимальном объёме».
- **Сферическое демпфирование** (`Hagi/Optimization/
  SphericalDamping.lean`, мост к SFPRM arXiv:2610.25646):
  `chordal_residual_eq` — хордовый остаток остановки
  ρ = 1 − ⟨u,v⟩ = ½‖u−v‖² (масштабно-инвариантный halting);
  `angular_damping_window` — окно устойчивости углового шага
  |1 − η + ηζ| < 1 ↔ 0 < η < 2/(1−ζ) для мод ζ < 1
  (действительный случай Thm 1 SFPRM). Синтез с R520 (пик
  Ω_n при n = 7): сферическая параметризация шага как доли
  угла согласована с максимумом телесного угла в 7-мерии.
- **Неточное сжатие и пол квантования**
  (`Hagi/Optimization/InexactContraction.lean`): внутренняя
  индукция «трёх геометрий» — рекурсия x(k+1) ≤ q·x(k) + ε
  даёт точную границу x(k) ≤ q^k·x₀ + ε(1−q^k)/(1−q)
  (`inexact_contraction_bound`) и предельный пол
  x(k) ≤ q^k·x₀ + ε/(1−q) (`inexact_contraction_floor`):
  квантование ставит пол сходимости ε/(1−q); с
  `quantized_descent_telescope` (ε = Δ/2) — требование к
  решётке Δ < 2τ(1−q) для останова по допуску τ.
- **Критерий останова** (`inexact_contraction_halt`): при
  пол ε/(1−q) < τ и x 0 ≤ B горизонт K с
  q^K < (τ − ε/(1−q))/B даёт x K < τ — явный
  логарифмический K-горизонт останова; внутренняя индукция
  «трёх геометрий» (сжатие + квантование + останов)
  замкнута.
- **Контроллер подпространства и конечность роста**
  (`Hagi/Optimization/SubspaceGrowth.lean`): невязка
  представления projResidual u v = v − ∑⟪uᵢ,v⟫uᵢ —
  ортогональна базису (легитимное новое направление),
  несёт свою норму (⟪r,v⟫ = ‖r‖²), ограничена нормой
  запроса (δ(v) ≤ ‖v‖); `growth_finite` — внешняя индукция:
  при неотрицательной метрике покрытия и минимальном
  улучшении δ > 0 на расширение число расширений конечно
  (k·δ ≤ C₀). Вторая «геометрия» адаптивной HAGI
  формализована: рост по новым независимым направлениям
  останавливается за C₀/δ шагов.
- **Полный адаптивный цикл** (`adaptive_cycle_expansions`):
  композиция внешней (конечность расширений N ≤ C₀/δ) и
  внутренней (K-горизонт останова `inexact_contraction_halt`)
  индукций — цикл «расширение → пересчёт → останов»
  геометрически адаптивной HAGI замкнут.
- **Граница Уэлча** (`Hagi/Optimization/DirectionPacking.lean`,
  полная): для M единичных направлений в d-мерном пространстве
  с когерентностью μ ≥ |⟪uᵢ,uₖ⟫| (i≠k) справедливо
  (M−d)/(M−1) ≤ d·μ² — через Коши на диагонали frame operator
  (sum_sq_cauchy + Sop_self_adjoint + Sop_trace tr S = M +
  Sop_trace_sq tr S² = Σᵢₖ⟪uᵢ,uₖ⟫² + разложение
  M + M(M−1)μ²). Геометрическое ограничение упаковки
  направлений: необходимое условие d ≥ M/(1+(M−1)μ²) —
  размерность по числу различимых направлений и допустимому
  смешению (измеримая замена эвристики «пик Ω₇»).
- **Вместимость упаковки** (`welch_capacity_full`): M+1
  направлений с когерентностью μ существуют только при
  (M+1)/(1+Mμ²) ≤ d — контрапозиция = триггер контроллера
  роста: при d ниже вместимости новое направление невозможно
  добавить без роста размерности или смешения.
- **Минимальная размерность по Уэлчу**
  (`welch_min_dimension`): M/(1+(M−1)μ²) ≤ d — прямое
  следствие: размерность = f(число различимых направлений,
  допустимое смешение).
- **Архитектурный контракт адаптивной HAGI (4 оси)**
  (`adaptive_hagi_contract_thermal`): размерность (Уэлч) ∧
  конечный рост (C₀/δ) ∧ honest останов (x K < τ) ∧
  термодинамический коридор (∃T: различимость ∧ качество) —
  единая четырёхосевая сводная теорема адаптивной HAGI
  (3-осевая версия свёрнута в неё, дедуп итерации 56).
- **Геодезия смеси** (`mixture_norm_sq`,
  `normalized_mixture_inner`): ‖αu+βv‖² = α²+2αβ⟪u,v⟫+β² и
  точная формула положения нормализованной смеси на дуге —
  аддитивная инъекция (FPRM) и Slerp-геодезика (SFPRM)
  двигают состояние по одной дуге (ядро Lemma 3 SFPRM):
  сферическая параметризация шага совместима с аддитивной.
- **Шаг остаётся на сфере** (`mixture_normalize_unit`):
  нормализованная смесь единична — структурная
  ограниченность SFPRM (расходимость невозможна по
  построению, связанные коэффициенты FPRM не нужны).
- **Явная хордовая дистанция шага**
  (`normalized_mixture_distance`):
  ½‖step−u‖² = 1 − (α+β⟪u,v⟫)/‖αu+βv‖ — критерий останова
  SFPRM получает явную формулу через параметры инъекции
  (композиция chordal × дуга × единичность).
- **Ускорение Андерсона × пол квантования**
  (`anderson_floor_gain`, мост к Evans–Pollock–Rebholz
  2020): при per-step gain θ ускорённая рекурсия имеет
  эффективный фактор θ·q — точная граница (θq)^k·x₀ +
  ε(1−(θq)^k)/(1−θq) и улучшенный пол ε/(1−θq) ≤ ε/(1−q):
  ускорение снижает предельную ошибку квантованной итерации.
- **AA-горизонт останова** (`anderson_halt`): ускоренная
  рекурсия останавливается при (θq)^K < (τ − ε/(1−θq))/B —
  объединение gain-фактора и K-горизонта: ускорение
  сокращает и пол, и горизонт останова.
- **Рефакторинг утилит** (`unit_inner_self`): вынесен
  повторяющийся паттерн ⟪u,u⟫ = 1 из ‖u‖ = 1 (3 вхождения
  SphericalDamping; итерация 58).
- **Консолидация термодинамической оси** (ит. 59,
  рефакторинг): 8 теорем охлаждения (н burst-оценки, E=F+T·S,
  максимум энтропии, качество смеси, геометрическое
  охлаждение, термическое размытие, коридор) выделены из
  Variational в `Hagi/Energy/Cooling.lean` — вся
  термодинамическая ось в одном модуле; импортёры
  обновлены, Freeze без потерь (2762).

### L3. Сертификатный слой (CycleCertificate)
- **Сертификат полного цикла** (`CycleCertificate`,
  Model/CycleCertificate): независимые компоненты —
  прогресс (C(t+1) = C t + gain t), потенциал
  (Φ(t+1) ≤ Φ t − drop t + risk t), бюджет
  (B(t+1) = B t − spend t), каждый с честностью.
- **Композиция** (`cycle_certificate_composition`): один
  сертификат на горизонте T даёт одновременно точный рост
  C T = C 0 + Σ gain, телескоп потенциала
  Φ T ≤ Φ 0 − Σ drop + Σ risk и точный ledger
  B T = B 0 − Σ spend.
- **Инстанс-мост «механизм → сертификат»**
  (`growSeq_cycle_certificate`, `honest_trajectory_global`):
  честная платная траектория доставляет сертификат (gain =
  α·C t, spend = μ·C t, энергия постоянна) — глобальные
  гарантии применимы к траектории без доп. гипотез.

### L3. Капстоуны
- **MasterHAGI** (условный): CertifiedHAGIInvariant — риск,
  потенциал, рост, бюджет, обобщение; связанная форма
  `MasterHAGI_linked` (C t = capability реальной
  траектории); числовые свидетели непустоты.
- **hagi_synthesis** (ArchitectureTheorem):
  взлёт C 0(1+γk)^T ≤ C T ≤ C* − (1−σ)^T(C*−C 0);
  риск ∀i: Σ risk(t,i) ≤ T·best(i) + R + ε₀/(1−ρₑ);
  логарифмический потолок горизонта
  (T−1)·ln(1+γk) ≤ ln(σC*) − ln((γk+σ)C 0) при
  (γk+σ)C 0 < σC*.
- **GrandSynthesis** (в т.ч. ослабленная форма):
  измерительная цепочка + конус + coupled-капстоун;
  риск-телескоп C T − C 0 ≤ Σ risk из пошагового покрытия.
- **Продуктивный свидетель** (`masterhagi_productive_witness`,
  T = 1): все посылки MasterHAGI с живыми величинами —
  безопасный шаг, строгое убывание энергии, рост ×3/2,
  точный бюджет; при FULL-контракте старой модели
  T ≥ 2 невозможно (obstruction) — ремонт через
  state-dependent effects (см. growSeq).

### Перколяция (отдельная ветка)

- |Ω| = M^{L·L} (card_Ω); R монотонна по порогу
  (вложенность событий на общем seed, без теории меры).
- **Скачок эмерджентности**: на 2×2 с parity-seed порог
  1 → 2 переворачивает crossing — одна клетка (0,1)
  порождает путь (0,0)→(0,1)→(1,1).
- **Строгий скачок R** (`R_strict_jump`):
  R(1) < R(2) — весь строгий прирост 1/16 от одного seed.
- Класс `ThresholdSystem` (cap : Ints → ℝ, монотонность) —
  общая форма перколяционного R и θ-моделей HAGI.

### Вспомогательное

- Дигамма-дуга: ψ(1/2) = −2ln2−γ, ψ(3) = H₂−γ,
  ψ(4) = H₃−γ, отражение Эйлера, рекуррента;
  непрерывность ψ на {Re w > 2}; существование пика
  ψ(x*/2) = ln π, x* ∈ (7, 8) (численно ≈ 7.257 ✓).
- Конкуренция гипотез (DHC): softmax-веса, орбита
  ограничена, критерий завершения корректен.
- Water-filling: маржинальный обмен битами точен;
  двухслойная балансировка; фактор-2 жадный инвариант.
- Jensen-gap: CE(t, mid) = mean CE − gap, gap ≥ 0;
  строгий свидетель (½ log cosh a > log cosh(a/2)).

---

## Канонический стек Gen-3 (капстоун и мосты)

- **CertifiedLoop (Unified/CertifiedLoop.lean)**: `certified_loop`
  — цепочка `StepCert` (честный спуск + покомпонентный floor +
  бюджет) даёт одновременно Σdrops ≤ obj₀ − objₙ, `FloorKept`,
  неотрицательный остаток и телескоп бюджета;
  `certified_loop_strict` — при n ≥ 1 спуск строгий;
  `certified_loop_all` — floor на всех промежуточных состояниях;
  `gate_never_increases` — принцип commit/hold.
- **HonestTransition (Unified/HonestTransition.lean)**:
  зависимое доказательство спуска actualDescent:
  obj s' ≤ obj s − drop; сертификат ⇒ строгий спуск.
- **Сквозной свидетель (Examples/QuadLoopWitness.lean)**:
  `qhalf` (полушаговая траектория, энергия × 1/4 за шаг),
  `halfStepCert` — StepCert на каждом шаге, `quad_loop_horizon`
  — strict-спуск на любом горизонте, `quad_witness_T3` /
  `quad_witness_T10` — свидетели без CorePremises.
- **Капстоун-гейт (Challenge/MasterChallengeV3.lean)**:
  `master_hagi_challenge_v3` — comparator-закрепление Gen-3
  капстоуна (CHALLENGE 2/2).
- **SignSGD/Lion (Unified/SignDescent.lean)**:
  `sign_scaled_aligned` — масштабированный sign-шаг (s = ‖g‖₁/n)
  выровнен; `sign_descent` — чистое убывание сжатого шага;
  `scaled_sign_aligned_of_coherence` + `lion_descent` —
  момент-Lion при согласованности с градиентом;
  `sign_is_pointwise_max` — знак максимизирует ⟨g, v⟩ на
  ℓ∞-кубе (ядро спектральной оптимальности Muon).
- **SAM (Unified/SamDescent.lean)**: `sam_descent_bridge` —
  спуск по worst-neighbor цели переносится на истинную с
  потерей на остроту; `sam_descent_flat` — плоский случай.
- **Нейрокомпьютер в капстоуне (Unified/NCStepCert.lean)**:
  ncCertStep (обучающий переход с честным энергийным
  спуском), ncStepCert — полный StepCert нейрокомпьютера
  (спуск + покомпонентный пол capability + честный бюджет,
  риск — консервативным комбинированным лимитом),
  ncTraj_capa_mono, ncTraj_cpu_frozen, nc_loop_horizon —
  certified_loop_strict на траектории NC: строгий спуск
  энергии на любом горизонте при замороженном CPU.
- **Двухстадийное чанкование (Model/HNet2.lean)**:
  hier2_compression_product (полная компрессия =
  произведение коэффициентов стадий), hier2_positions_le,
  hier2_beats_dense (условие выигрыша двухстадийной
  иерархии над dense-базлайном).
- **Bignum-кирпич CPU (Model/RVCoreBignum.lean)**:
  wordAdd_carry_decomp (полная сумма = машинная сумма +
  перенос·сетка), carry_le_one (перенос ≤ единицы),
  carry_eq_zero_iff — точная многословная арифметика
  без накопления ошибки переноса.
- **M6-свидетель (Examples/QuarticWitness.lean)**:
  нелинейная цель E(w) = Σ(w² + w⁴) на Fin-пространстве,
  два последовательных продуктивных градиентных шага
  с точной рациональной арифметикой; каждый шаг —
  полный StepCert с ненулевыми spend и riskLim,
  растущим capability-каналом и покомпонентным полом;
  quartic_two_steps: строгий спуск + FloorKept +
  честный бюджетный телескоп; quartic_drops_pos:
  оба спуска строго положительны. CHALLENGE-гейт
  переведён исключительно на Gen-3 капстоун
  (Gen-1 comparator снят).
- **Семейственный телескоп (Unified/Ctv2Telescope.lean)**:
  ctv2_family_telescope — кумулятивная связь Σ спусков ≤
  E₀ − E_T ВЫВОДИТСЯ из поштучных CertifiedTransitionV2 с
  операциональными условиями (advance_energy_drop по
  индукции); stepDrop_ge_verify — мост: честный спуск
  шага не меньше показателя verify нового состояния (при
  выровненном направлении, η ≤ 1/L, ошибке квантования
  ≤ полсетки); verify_family_telescope — телескоп
  НЕПОСРЕДСТВЕННО в форме показателей verify: гипотеза
  hetelescope в MasterHAGICoupled теперь выводима как
  теорема (закрытие находки внешнего аудита).
- **Композиционная экономия внимания (Model/AttentionSpend.lean)**:
  hybridAttnCost/denseAttnCost; hybrid_spend_lt — окно
  короче длины и KV-групп меньше головок ⟹ гибрид SWA×GQA
  строго дешевле плотного внимания; hybrid_ratio —
  относительная стоимость РОВНО произведение факторов
  экономии (окно/длина)·(n_kv/n_h) — механизмы экономии
  ПЕРЕМНОЖАЮТСЯ; hybrid_ratio_lt_one — строго ниже
  dense-базлайна. Полный стек: fullStack_ratio —
  относительная стоимость MoD×SWA×GQA стека ТОЧНО
  (k/n)·(окно/длина)·(n_kv/n_h) — произведение ТРЁХ
  факторов; fullStack_lt — при трёх активных механизмах
  полный гибридный стек строго дешевле плотного.
- **Alignment-риск (Model/AlignmentRisk.lean)**:
  kl_budget_risk_bound — KL-бюджет штрафа (Пинскер) +
  липшицевый по TV риск-канал ⟹ риск ≤ c·√KL;
  kl_penalty_certifies_risk — штраф ≤ δ ⟹ риск-лимит
  c·√δ (riskBound certified-цикла из alignment-штрафа);
  rlhf_zero_drift_zero_risk — нулевой дрейф ⟹ нулевой
  риск.
- **Сертифицированный сжатый шаг (Unified/SignStepCert.lean)**:
  signStepCert — полный StepCert для знакового шага на
  квадратичной машине: честный спуск (выравнивание
  масштабированного знакового направления через
  descent_drop), покомпонентный пол качества и ДЕШЁВЫЙ
  бюджет — пересылка бита на координату вместо слова
  (signCommCost/fullCommCost, sign_comm_le);
  signStep_nrm_pos (норма знакового направления > 0 при
  ненулевом градиенте), signDrop_pos, signStep_energy_le.
- **PL-скорость certified-цикла (Unified/PLLoop.lean)**:
  pl_linear — при PL-условии (‖∇E‖² ≥ 2μ(E−E*)) и
  равномерной drop-грани (drop ≥ κ·‖∇E‖²) цепочка шагов
  даёт ЛИНЕЙНУЮ сходимость: E_T − E* ≤ (1−2κμ)^T·(E_0−E*);
  certified_pl_horizon — та же скорость для StepCert-цепочки
  (drop-грань связана с сертификатами). Закрыт пункт аудита
  «без PL только остановка»: PL даёт формальную скорость.
- **Точная PL-инстанциация (Unified/PLQuad.lean)**:
  quad_pl_exact — для квадратичной машины PL-неравенство
  ТОЧНОЕ: nrm2(quadGrad) = 2·quadE (μ = 1), оптимум
  quadE a a = 0; quad_pl_rate — линейная скорость цепочки
  честных спусков с drop-гранью κ·‖g‖²: энергия сжимается
  фактором (1 − 2κ)^n. PL-теория PLLoop теперь заземлена
  на эталонной машине.
- **Отрицательный результат: у знакового сжатия нет
  равномерной drop-грани (Unified/SignNoKappa.lean)**:
  sign_pointmass_ratio — ТОЧНАЯ идентичность: на
  градиенте-точечной массе знаковый шаг сжимает квадрат
  нормы в квадрат размера носителя (nrm2(signStep)·n² =
  1); sign_no_uniform_floor — при любой константе выше
  1/n² точечная масса нарушает оценку «знаковый шаг ≥
  κ·градиент». Формальное обоснование: чистое сжатие без
  компенсации стоит PL-скорости (нужен error feedback
  или покоординатная нижняя грань) — граница применимости
  quad_pl_rate.
- **Error feedback: точное отражение (Unified/
  ErrorFeedback.lean)**: ef_telescope — сумма сжатых
  векторов равна сумме точных плюс изменение резидуала;
  ef_shadow_sum — разность сжатой и точной сумм РОВНО
  равна изменению резидуала; ef_iterate_shadow — ГЛАВНАЯ:
  итераты сжатого EF-цикла отклоняются от идеальных
  РОВНО на масштабированное изменение резидуала
  (xC n − xF n = η•(e n − e 0)). Ответ на отрицательный
  результат SignNoKappa: сжатие с EF не теряет
  траекторию — отклонение контролируется резидуалом.
- **Обструкция Gen-1 (Diagnostics/Obstructions.lean)**:
  `full_cycle_two_step_growth_inconsistent'` — регрессионный
  тест: копируемые эффекты противоречивы на T = 2.
- **Изоляция**: MasterHAGI / MasterHAGI_linked / MasterHAGICore /
  MasterHAGI_trunc / grand_synthesis — `@[deprecated]` →
  `certified_loop`.

## Каталог: доказанное по файлам (theorem/lemma)
- `Hagi/Architecture/AlignedMerge.lean` — `dotCS`, `frobSubord`, `misalignCross`, `mergeEnergyPerturbed`
- `Hagi/Architecture/ConfigurationCost.lean` — `config_storage_beats_dense`
- `Hagi/Architecture/ConfigurationRouting.lean` — `selector_never_flips_verdict`, `switchable_beats_naive_dense`
- `Hagi/Architecture/CortexFiber.lean` — `mulVec_vecMul_gram`, `orthoNorm`, `fiberCross`, `fiberPythagoras`, `fiberParamCount`
- `Hagi/Architecture/FactorRank.lean` — `rank_le_of_nonnegFactorization`, `rank_le_nonnegRank`, `positive_measure_pos_prob`, `regimeC_fractional`
- `Hagi/Architecture/FactorizedMerge.lean` — `is`, `routed_eval_exact`, `merge_core_residual_identity`, `factorized_merge_exact`, `mean_norm_le`, `routed_approx_bound`, `factorized_error_bound`, `factorized_budget` (+1)
- `Hagi/Architecture/Heterarchy.lean` — `no_global_ranking`, `cycle_breaks_ranking`, `disagreement_survives_configs`
- `Hagi/Architecture/LiveDelta.lean` — `rollback_addBlock`, `block_rank_le`, `null_effect`, `blocks_cost`
- `Hagi/Architecture/OrthoInjection.lean` — `fiberSplitOrtho`, `fiberActionNoInterference`, `fiberSplitEnergy`, `fiber_cortex_zero`, `fiber_injection_preserves_cortex`, `fiber_injection_norm_split`
- `Hagi/Architecture/ResidualSplit.lean` — `rotated_factors_same_matrix`, `signMatrix_orthogonal`, `signMatrix_mul_self`, `sign_flip_functional_equiv`, `naive_latent_merge_kills_flipped`, `residual_gate_two_sided`, `expert_residual_not_compressible`, `fidelity_bound_with_fibers`
- `Hagi/Audit/EqualBudget.lean` — `aitken_exact`, `aitken_consistency`, `budget_gap_sign_const`, `headstart_pays_iff`
- `Hagi/Audit/Exactness.lean` — `exp_jensen`, `gap_N_nonneg`, `anchor_recurrence`, `ns_poly_bound`, `amgm_batch_bound`, `nce_estimator_unbiased`, `log_jensen_uniform`, `exp_tangent` (+6)
- `Hagi/Autonomy/Hedge.lean` — `exp_neg_le_quad`, `hedge_step`, `hedge_telescope`, `router_regret_bound`
- `Hagi/Autonomy/HedgeSurvivor.lean` — `ewWeight_nonneg`, `ewWeight_exp`, `ewWeight_pos`, `ewPot_pos`, `ewNorm_nonneg`, `ewNorm_sum`, `ewPot_step`, `ewPot_upper` (+4)
- `Hagi/Autonomy/Insight.lean` — `forgetting_kl_bound`, `insight_kl_descent`, `experience_cycle_bound`, `insight_consolidation_safe`, `gate_retention`, `tldr_drift_null`, `tldr_two_tier_safety`
- `Hagi/Autonomy/ParetoController.lean` — `dirTau_le`, `le_dirTau`, `dirTau_char`, `pareto_validity`, `dir_controller_find`, `sup_stab`, `noisy_pareto_select`
- `Hagi/Autonomy/SupervisorSafety.lean` — `capacity_member_mono`, `ternary_beats_binary`, `no_restore_without_checkpoint`
- `Hagi/Autonomy/SupervisorViability.lean` — `versionSpace_mono`, `versionSpace_append_singleton`, `halving_mistake_halves`, `mistakesAux_bound`, `halving_mistake_bound`, `majority_wrong_verdict`, `majority_wrong_persists`
- `Hagi/Autonomy/TTTStability.lean` — `ttt_bibo`, `ttt_chain_bounded`
- `Hagi/Budget/ActiveCompute.lean` — `active_flops`, `switching_never_exceeds_dense`, `active_beats_dense_family`
- `Hagi/Budget/AnytimeCondensation.lean` — `pointwise_upper_band`, `anytime_condensation`, `condensation_pipeline`
- `Hagi/Budget/BatchCap.lean` — `sfo_min_core`, `sfo_global_min`, `critical_batch_lower`, `two_term_amgm`, `optimal_split`, `batchCapMonotone`, `batchCapSaturates`
- `Hagi/Budget/BitAlloc.lean` — `distill_chain_telescoping`, `ensemble_linear_descent`, `distill_compound_gain`, `distill_leak_gate`, `harvest_budget`, `exhausted_when`, `field_nonneg`, `harvest_accounting_identity` (+15)
- `Hagi/Budget/BitAllocTermination.lean` — `alloc_entry_le`, `error_chain_descends`, `improving_chain_injective`, `no_infinite_improving_chain`
- `Hagi/Budget/CertifiedArgmax.lean` — `argmax_pair_certified`, `argmax_select_certified`, `tie_ambiguity`
- `Hagi/Budget/DesignOpt.lean` — `spectral_tail_mono`, `spectral_rank_exists`, `shadow_price_sum_identity`
- `Hagi/Budget/ElementQuant.lean` — `factor_quant_error`, `factor_quant_go`, `ternary_factor_qerr_bound`, `ternary_pair_qerr_sum`
- `Hagi/Budget/FlopsEconomy.lean` — `equal_budget_baseline`, `lower`, `pipeline_beats_baseline_iff`, `amortized_growth_cheaper`
- `Hagi/Budget/JointCost.lean` — `block_lowrank_lt_dense_iff`, `nsIter_scale`, `nsIter_block_le`, `amdahl_ceiling`, `offdiag_pythagoras`
- `Hagi/Budget/KVWater.lean` — `waterfilling_bound`, `waterfilling_inactive_clamp`
- `Hagi/Budget/RankBudget.lean` — `rankResidual_equalized`, `rankResidual_allocation`
- `Hagi/Budget/ThermoCondensation.lean` — `schedule_descent`, `schedule_conflict_step`, `jl_inner_approx`, `orthogonal_preserves_grad_dist`, `mup_scale_invariance`, `vocab_critical_point`, `phase_metric_monotone`, `frozen_norm_no_dynamics` (+20)
- `Hagi/Budget/TokenWeightBias.lean` — `token_weight_decomposition`, `zero_bias_iff_uncorrelated`
- `Hagi/Budget/WaterFilling.lean` — `sum_two_point`, `exists_balanced_allocation`
- `Hagi/Budget/WaterFillingMoE.lean` — `genMean_assoc`, `marginalValue_law`, `activeSet_structure`
- `Hagi/Challenge/MasterChallenge.lean` — `master_hagi_core_comparator`
- `Hagi/Challenge/MasterChallengeV3.lean` — `master_hagi_challenge_v3`
- `Hagi/Core/Ambig.lean` — `lse_shift`, `consensus_no_gain`
- `Hagi/Core/Attention.lean` — `attention_error_damped_sum`, `attention_error_damped`, `attention_error_damped'`
- `Hagi/Core/BlockDiag.lean` — `blockDiagonal'_mulVec_apply`, `step0_equivalence`
- `Hagi/Core/Concat.lean` — `concatCols_identical`, `concatCols_identical_apply`, `concat_unique_identity_scale`, `temperature_softmax_eq_forces_const`, `temperature_changes_softmax`, `exp_sum_pos`, `softDef_eq_exp_sub_lse`, `lse_midpoint_le` (+4)
- `Hagi/Core/Element.lean` — `residualLeaf_zero`, `residualLeaf_zero_apply`, `delta_rank_le`, `delta_exact_rank_bound`, `params_count`
- `Hagi/Core/ErrorProp.lean` — `propagate_cons`, `propagate_bound`, `propagate_bound_contractive`, `propagate_sq_bound`
- `Hagi/Core/F3Root.lean` — `root_invariance`, `root_no_leaf_signal`, `anova_split`
- `Hagi/Core/FrobOuter.lean` — `frobSq_outer_orthonormal`, `frobSq_outerSum`, `frobSq_trunc_tail`
- `Hagi/Core/Hadamard.lean` — `zmod2_add_self`, `zmod2_neg_eq_self`, `zmod2_one_add_one`, `zmod2_cases`, `chi2_zero`, `chi2_one`, `chi2_sq`, `chi2_mul` (+9)
- `Hagi/Core/Kronecker.lean` — `kronecker_mul_conjTranspose`, `conjTranspose_kronecker_mul`, `kronecker_mul_transpose`, `transpose_kronecker_mul`
- `Hagi/Core/Lift.lean` — `parentPreservingQ_mul_transpose`, `parentPreservingQ_diag`, `parentPreservingQ_leafSub`, `diagonalAdd_preserves_equality`, `rootProj_is_mean`, `parentPreservingQ_root_fixed`, `mixerQ_orthogonal`, `mixerQ_root_fixed` (+3)
- `Hagi/Core/Merge.lean` — `head_prerotation`, `blockCols_mulVec_sum`, `mulVec_dotProduct_mulVec`
- `Hagi/Core/Mix.lean` — `mixed_invisible`
- `Hagi/Core/NonlinearStep0.lean` — `gauge_equiv_comp`, `perBlock_gauge_equiv`, `perBlock_net_blockwise`, `zero_init_identity`
- `Hagi/Core/RealF3Ortho.lean` — `sq3`, `sq3c`, `omega_sq_add_add`, `omega_cubed`, `conj_omega`, `omega_ne_one`, `norm_omega`, `omega_pow_mod` (+22)
- `Hagi/Core/Ridge.lean` — `ridge_optimal`
- `Hagi/Core/RoPEMoments.lean` — `rot_norm`, `rope_score_delta`, `rope_translation_shift`, `rope_context_dichotomy`, `rope_limit_irreversible`, `rope_mean_sum`, `rope_second_moment_sum`, `cosSum_zero'` (+3)
- `Hagi/Core/RootContrast.lean` — `root_sum_eq`, `root_idem`, `contrast_zero_sum`, `contrast_of_root`, `root_contrast_orth_total`, `root_contrast_pythagoras`, `filter_partition_sum`, `highway_gain_identity` (+1)
- `Hagi/Core/Select.lean` — `meanBound_greedy`, `selection_hurts`
- `Hagi/Data/BytePatch.lean` — `patch_cover`, `patch_le_raw`, `patch_real_bound`, `patch_attn_saving`
- `Hagi/Data/CertifiedArgmax.lean` — `certified_argmax_strict`, `certified_argmax_ambiguity`
- `Hagi/Data/DBridge.lean` — `dQuad_nonneg`, `dfield_entropy_identity`, `equilibrium_bracket`
- `Hagi/Data/DField.lean` — `kl_nonneg`, `log_eq_sub_one_iff_one`, `mixtureCorpus_pos`, `mixtureCorpus_sum_one`, `log_lt_sub_one'`, `kl_zero_iff_eq`, `divField_zero_iff`, `log_ratio_add` (+4)
- `Hagi/Data/DFieldKKT.lean` — `dfield_ascent_transfer`
- `Hagi/Data/DataMixing.lean` — `exp_segment_le`, `mixing_loss_convex`
- `Hagi/Data/Distill.lean` — `kl_eq_ce_gap`, `ce_gap_kl_identity`, `teacher_generated_identity`, `ce_topk_shift`, `kl_topk_shift`, `topk_distill_budget`, `topk_tail_bound`, `topk_distill_budget_tv` (+2)
- `Hagi/Data/DistillRecursion.lean` — `entDef_eq_shannon`, `freshMix_pos`, `freshMix_sum_one`, `entropy_mix_ge`, `entropy_kl_ce_identity`, `distill_step_entropy`, `distill_entropy_recurrence`, `entropy_floor` (+3)
- `Hagi/Data/FannesSmooth.lean` — `log_sub_le_div`, `abs_log_sub_le`, `entropy_lipschitz_smooth`
- `Hagi/Data/InfoNCE.lean` — `shannon_eq_canonical`, `tvHalf_eq_canonical`, `kl_excess_cross_entropy`, `ce_self_eq_entropy`, `ce_ge_entropy`, `infonce_never_overestimates`, `infonce_gap_is_kl`
- `Hagi/Data/NessDissipation.lean` — `detailed_balance_zero_ep`, `ep_zero_implies_db`
- `Hagi/Data/PACBayes.lean` — `log_weighted_jensen`, `gibbs_variational`
- `Hagi/Diagnostics/Obstructions.lean` — `full_cycle_two_step_growth_inconsistent'`
- `Hagi/Discovery/PPT.lean` — `pptNorm_pos`, `pptTarget_isProbability`, `pptTarget_pos`, `pptKernel_nonneg`, `mh_stationary`, `pptSwapAccept_nonneg`, `pptSwapAccept_le_one`, `pptSwapAccept_mem` (+24)
- `Hagi/Dynamics/CapabilityGain.lean` — `capability_gain_transfer`, `pb_gap_bound_mono`
- `Hagi/Dynamics/ControllerPolicy.lean` — `ratio_dominance`, `budget_allocation_dominance`
- `Hagi/Dynamics/DistillationRate.lean` — `kl_contraction_budget`, `kl_half_steps`
- `Hagi/Dynamics/EndpointContraction.lean` — `geom_sum_telescope`, `geom_sum_le_inv`, `contraction_limit`, `endpoint_bivariate_bound`, `endpoint_geometric_tail`, `endpoint_depth_budget`
- `Hagi/Dynamics/FastGrowth.lean` — `capability_takeoff_counted`, `capability_cumulative`, `growth_efficiency_lower`, `growth_efficiency_div`, `capability_multiplicative`, `capability_takeoff_floor`, `risk_takeoff_counted`, `risk_epsilon_floor`
- `Hagi/Dynamics/ProxyGap.lean` — `budget_consumed`, `guarantee_horizon_bound`, `shift_paid_from_budget`
- `Hagi/Dynamics/SpeedLimit.lean` — `learning_time_lower_bound`
- `Hagi/Dynamics/UrgencyDepth.lean` — `depth_capped_by_time`, `shallow_misses_tube`, `patient_configuration_reaches`
- `Hagi/Dynamics/WallClockTakeoff.lean` — `log_one_add_ge_sub_half_sq`, `exp_le_one_add`, `wallclock_takeoff_product`, `prod_exp_le_prod_one_add`, `wallclock_takeoff`, `wallclock_takeoff_small_steps`, `counted_takeoff_exp`, `wallclock_rate_from_cone` (+2)
- `Hagi/Energy/Cooling.lean` — `gibbs_value_nernst_bounds`, `gibbs_schedule_quality`, `gibbs_free_energy_identity`, `shannon_entropy_le_log_card`, `gibbs_mixture_quality`, `geometric_cooling_steps`, `thermal_blur`, `temperature_corridor` (+8)
- `Hagi/Energy/EntropyProduction.lean` — `exp_neg_entropyProduction`, `ift_normalization`, `second_law`
- `Hagi/Energy/FreeEnergy.lean` — `free_energy_gap`, `geometric_pool_identity`, `geometric_pool_identity_nonneg`
- `Hagi/Energy/Landauer.lean` — `landauer_sandwich`, `landauer_cap_certified`, `written_bits_cap`, `ternary_weight_growth_cap`, `serial_divergence_cap`, `cycle_budget_split`, `trajectory_budget_telescope`, `lifetime_thermodynamic_ceiling` (+7)
- `Hagi/Energy/PoEBound.lean` — `sum_exp_pos`, `smax_pos`, `smax_nonneg`, `smax_sum_one`, `sum_smax_exp`, `lse_shift_lower`, `lse_shift_upper`, `weighted_center_le` (+7)
- `Hagi/Energy/PreNorm.lean` — `var_recursion`, `constructive_scale`, `rms_direction`, `rms_idempotent`, `requires`, `bf16_frozen_update`
- `Hagi/Energy/Quantizer.lean` — `gridQ_error`, `gridQ_mem_grid`, `gridQ_div`, `gridQ_idem`, `quantizer_optimal_step`
- `Hagi/Energy/STEStep.lean` — `covered`, `tern_distortion_round`, `tern_scale_invariance`, `ste_step_residual`
- `Hagi/Energy/Ternary.lean` — `three_pow_five`, `trits_fit_byte`, `sum_two_pow`, `encode_lt_aux`, `tritEncode_lt`, `last_digit_eq`, `abs_sub_le`, `sum_injective_aux` (+7)
- `Hagi/Energy/Variational.lean` — `tilted_sum_one`, `tilted_pos`, `kl_tilted_decompose`, `free_energy_variational`, `gibbs_optimal_bound`
- `Hagi/Ensemble/CompressionCert.lean` — `deltaCost_concat`, `deltaCost_sum`, `merged_bound`
- `Hagi/Ensemble/GapLaw.lean` — `twoGap_pos_measure`, `twoGap_cosh`, `twoGap_nonneg`, `twoGap_zero_iff`, `pairVarEq`
- `Hagi/Ensemble/Hoeffding.lean` — `exp_chord`, `sum_pair_weights`, `sum_pair_diff_zero`, `sum_pair_const`, `sum2_mul`, `exp_prod_le_cosh`, `half_log_cosh_le`, `twoGap_bounded` (+14)
- `Hagi/Ensemble/MergeIdentity.lean` — `softmax_shift_invariance`, `geometric_mean_logit_mean`
- `Hagi/Ensemble/MergeMixture.lean` — `merged_output_exact`, `routing_drift_bound`
- `Hagi/Ensemble/MergePrice.lean` — `sigmaPrice_neg`, `merge_price_quad`, `price_zero_iff_ker`, `merge_gate_certified`
- `Hagi/Ensemble/MergeScaling.lean` — `two_channel_step_law`
- `Hagi/Ensemble/PolicyCompatibility.lean` — `integration_net_gain_pos`, `integration_rejects_far_teacher`, `mopd_kl_scaling_warning`
- `Hagi/Ensemble/QFormerBridge.lean` — `punctured_unbiased`, `vista_bridge_zero`, `vista_residual_identity`
- `Hagi/Ensemble/SigmaKernel.lean` — `quad_form_factorization`, `quad_form_zero_iff`, `kernel_interference_zero`, `gn_grad_inner_ker`, `gpm_implies_safeqp_gn`
- `Hagi/Ensemble/UniformCert.lean` — `uniform_good_point`, `uniform_good_mass`, `two_sided_union_tail`, `two_sided_good_mass`, `class_size_lower`, `tolerance_calibration`, `calibrated_two_sided_mass`, `two_sided_good_point` (+1)
- `Hagi/Examples/HAGICertWitness.lean` — `eq_zero_of_mem_range_one`, `hagicert_nonvacuous`
- `Hagi/Examples/Nonvacuity.lean` — `jensenGap_nonneg`, `merge_energy_bridge`, `h_emp_merge_of_bridge`, `cosh_half_sq`, `jensenGap_pos_witness`, `core_premises_merge_operational`, `witness_quantErr_bounded`, `witnessGap_pos` (+38)
- `Hagi/Examples/NonvacuityHorizon.lean` — `sat_step_laws`, `sat_cone_iff`, `witness_achieves_horizon`
- `Hagi/Examples/QuadLoopWitness.lean` — `qhalf_succ`, `quadE_half`, `quadE_qhalf`, `quadE_pos_of_grad`, `qhalf_grad_ne`, `quadE_qhalf_le`, `quad_loop_horizon`, `quad_witness_T3` (+1)
- `Hagi/Examples/QuadraticConcrete.lean` — `quad_hasDeriv`, `quad_fderiv_apply`, `quad_smooth`, `quad_kappa_bound`, `quad_gcont`, `quad_hasFDeriv`, `quad_conj8`, `quad_kappa_at0` (+2)
- `Hagi/Examples/QuadraticEndToEnd.lean` — `qGrad`, `qStep_loss_exact`, `qStep_descent`, `qIter_loss`, `qQuant_err_bound`
- `Hagi/External/Diversity.lean` — `grad_dist_polarization`, `grad_zero_merge_perfect`, `gittins_index_max`, `merge_init_head_start`
- `Hagi/External/Flywheel/CoherenceCharacterization.lean` — `singularValues_ne_zero_iff_eigenvalues_ne_zero`, `rank_eq_card_nonzero_singularValues`, `sum_singularValues_sq_le_rank_mul_max_sq`, `rank_pos_of_ne_zero`, `sum_singularValues_sq_le_card_mul_max_sq`, `frobenius_spectral_ratio_le_sqrt_dim`, `coherenceFactor_zero`, `coherenceFactor_le_one` (+50)
- `Hagi/External/Flywheel/CourantFischer.lean` — `subspace_intersection_nontrivial`, `exists_nonzero_in_intersection`, `finrank_inf_ge_of_sum_gt`, `eigenspace_span_finrank`, `exists_eigenspace_of_dim`, `inner_toEuclideanLin_eq_eigenvalue_sum`, `rayleigh_eq_eigenvalue_on_eigenvector`, `rayleigh_eq_eigenvalue_weighted_sum` (+37)
- `Hagi/External/Flywheel/FrobeniusNorm.lean` — `Complex`, `Complex`, `frobenius_norm_sq_eq_trace`, `trace_conjTranspose_unitary_mul`, `trace_conjTranspose_mul_unitary`, `frobenius_norm_unitary_mul`, `frobenius_norm_mul_unitary`, `frobenius_norm_sq_diagonal` (+13)
- `Hagi/External/Flywheel/MDLRank.lean` — `mdlErr_antitone`, `mdlErr_zero_of_ge`, `mdlErr_step`, `mdlJ_argmin_exists`, `mdlDj_eq`, `mdlDj_ge_card`, `mdlJ_first_order`, `mdl_rank_ce`
- `Hagi/External/Flywheel/MatrixNormRelations.lean` — `R_apply`, `vec_apply`, `outerProduct_apply`, `R_kronecker`, `R_add`, `R_smul`, `R_frobenius_norm_eq`, `R_inv_R` (+50)
- `Hagi/External/Flywheel/NormSupport.lean` — `toEuclideanLin_apply`, `complex_sum_cauchy_schwarz`, `mulVec_eucl_norm_sq_le`, `mulVec_eucl_norm_le`, `frobenius_norm_eq_sqrt`
- `Hagi/External/Flywheel/SVD.lean` — `singularValues_nonneg`, `singularValues_sq`, `singularValues`, `singularValues`, `singularValues_eq_singularValues`, `singularValues`, `matrix_charpoly_zero`, `eigenvalues` (+153)
- `Hagi/External/Flywheel/SpectralNormGap.lean` — `sum_norm_sq_eq_norm_sq_euclidean`, `outerProduct_frobenius_norm_sq'`, `outerProduct_frobenius_norm'`, `R_inv_frobenius_norm_eq`, `l2_opNorm_le_frobenius`, `R_inv_spectral_le_frobenius`, `R_inv_outerProduct_spectral_bound`, `R_inv_outerProduct_spectral_bound_unit` (+27)
- `Hagi/External/Flywheel/TruncatedSVDRank1.lean` — `singularValues`, `truncatedSVD_rank1_identity`
- `Hagi/External/Flywheel/WeylInequality.lean` — `toEuclideanLin_add`, `rayleigh_add`, `weyl_eigenvalue_lower_bound`, `weyl_eigenvalue_upper_bound`, `weyl_eigenvalue_bounds`, `rank_conjTranspose_mul_self_eq`, `rank_mul_conjTranspose_eq`, `antitone_nonneg_zeros_from_rank` (+18)
- `Hagi/External/MemT/GDN2.lean` — `rowSumNorm_nonneg`, `rowSumNorm_mul_le`, `rowSumNorm_add_le`, `gdn2_step_bound`, `gdn2_horizon`, `rowSumNorm_sub_le`, `gdn2_read_sensitivity`, `gdn2Update_sub` (+5)
- `Hagi/Foundations/Chord.lean` — `exp_chord_r`, `exp_chord_ab`, `log_cosh_le`
- `Hagi/Foundations/ConeCorridor.lean` — `cone_exact_exponential`
- `Hagi/Foundations/ConeTakeoff.lean` — `cone_step`, `cone_invariant_horizon`, `takeoff_from_cone`, `frontier_cone_inductive`, `frontier_cone_invariant`
- `Hagi/Foundations/GrowthBand.lean` — `growth_band_step`, `growth_band_iter`, `saturation_gap`, `saturation_ceiling`
- `Hagi/Foundations/GrowthDynamics.lean` — `telescope_band`, `anytime_growth_budget`, `band_telescope`, `geometric_band_ceiling`, `band_target_unreachable`, `geo_sum_decay`, `band_guaranteed_growth`, `band_time_to_target` (+2)
- `Hagi/Foundations/Hoeffding.lean` — `bernDenom_pos`, `bernDenom_ne_zero`, `bernRho_hasDerivAt`, `bernRho_deriv_le`, `bernRho_cont`, `bernRho_diff`, `bernRho_slope`, `bernF_hasDerivAt` (+7)
- `Hagi/Foundations/MesoScale.lean` — `rpow_tendsto_zero`, `macro_collapse`, `micro_collapse`, `meso_peak_exists`
- `Hagi/Foundations/Ortho.lean` — `ortho_norm_sq_finset`, `ortho_norm_sq`, `gating_tail_bound`
- `Hagi/Foundations/PerronCone.lean` — `cone_eigenvector_iff`, `cone_perron_growth`, `cone_comparison`, `cone_comparison_perturbed`, `cone_explicit_lower`, `cone_explicit_monotone`, `h_emp_dyn_explicit`, `h_emp_dyn_linear_growth` (+4)
- `Hagi/Foundations/Potential.lean` — `hagiPotential_penalty_drop`
- `Hagi/Foundations/Recurrence.lean` — `geom_telescope`, `recurrence_upper`, `recurrence_pure`, `recurrence_lower`, `geom_sum_le_inv`, `contraction_limit`, `genMean_compound`, `genGap_decay` (+6)
- `Hagi/Foundations/StageCalculus.lean` — `compress_stage`, `adaptive_ns_exists`, `compound_budget`, `merge_stage`, `merge_stage_decrease`, `joint_stage`, `quadratic_bound_max`, `eta_star_exceeds_cap` (+2)
- `Hagi/Foundations/SumIdentities.lean` — `sum_sub_mean_zero`, `sq_decomp`
- `Hagi/Foundations/Telescope.lean` — `telescope_le`, `telescope_sum_le`, `telescope_sub_sum`, `lyapunov_telescope_fin`, `lyapunov_gain_noise`, `lyapunov_termination_fin`
- `Hagi/Generalization/ModeState.lean` — `Qgen_le`, `Qgen_drop_bound`, `relu_shift_le`, `generalization_safe_step`, `generalization_safe_step_at_target`, `safeqp_risk_bound_compose`, `modeDrop_rejected`, `scalarized_argmin_pareto` (+4)
- `Hagi/Geometry/SphericalSimplex.lean` — `dihedral_count`, `dihedral_angle_strictMono`, `dihedral_angle_lt_pi`, `excess_as_supplement`, `excess_pos`, `dihedral_angle_ge_pi_div_three`, `dihedral_angle_lt_pi_div_two`, `euclid_sum_bounds`
- `Hagi/Growth/AdaptiveQuery.lean` — `avgRadius_shrinks`, `certified_gain_select_avg`
- `Hagi/Growth/ChainToCone.lean` — `chain_feeds_cone`, `cone_two_sided_certificate`, `takeoff_from_certificate`
- `Hagi/Growth/ChainUnification.lean` — `training_core_is_measurement_tail`, `deficit_factorizes`
- `Hagi/Growth/ConeDynamics.lean` — `cone_data_invariant`, `frontier_cone_inductive_is_cone_data`, `cone_reinvest_invariant`, `cone_ratio_step_is_reinvest`
- `Hagi/Growth/DisagreementChain.lean` — `gain_chain_opt`, `any_stage_kills_gain`, `disagreement_chain`, `deficit_localizes`, `alignment_factor_le_one`, `stages_cone_gain`
- `Hagi/Growth/FiberNecessity.lean` — `configs_injective_on_separated`, `used_configs_lower_bound`, `fiber_params_floor`
- `Hagi/Growth/FrontierProduction.lean` — `injection_law_of_measured`, `coordMean_const`, `const_probe_sum`, `certified_cycle_renewal`, `takeoff_lifts_utility`
- `Hagi/Growth/FrontierScaling.lean` — `takeoff_edge_forced`, `cone_and_pos`, `sustained_takeoff_from_production`, `frontier_asymptotic`
- `Hagi/Growth/GainCeiling.lean` — `gain_product_bound`, `stackComp_cons`, `gain_stack_ceiling`, `amplification_needs_expansion`
- `Hagi/Growth/GainDecomposition.lean` — `merge_is_mean`, `deviations_cancel`, `pairwise_variance_identity`, `orthogonal_energy_split`, `decompose_reconstruct`, `anticorrelated_suppressed`, `gainop_cone_step`, `gainop_pairwise_bridge` (+3)
- `Hagi/Growth/GainRenewal.lean` — `gain_renewal_recurrence`, `geo_sum_mul`, `geo_sum_closed`, `gain_renewal_growth`, `gain_renewal_floor_pos`, `geo_sum_ge_one`, `gain_renewal_floor`, `gain_renewal_growth_one` (+3)
- `Hagi/Growth/GammaDeficit.lean` — `gamma_min_for_target`, `gamma_deficit_no_takeoff`
- `Hagi/Growth/Grow.lean` — `newBound`, `certifiedGain_monotone`, `grow_epsilon_stop`, `certifiedGain_positive`, `pl_stop_certificate`
- `Hagi/Growth/GrowthCeiling.lean` — `potential_telescope`, `edge_total_bound`, `frozen_saturation`, `expansion_required`, `growth_dichotomy`
- `Hagi/Growth/GrowthGate.lean` — `verdict_ttt`, `verdict_grow`, `verdict_exhausted`
- `Hagi/Growth/IntegrationOrder.lean` — `sum_perm_invariant`, `negative_expert_hurts_any_order`, `positive_selection_dominates`
- `Hagi/Growth/NoiseDisentangle.lean` — `orthogonal_noise_averaging`, `disagreement_convergence_floor`, `fiber_merge_denoise`
- `Hagi/Growth/NonlinearCone.lean` — `sqrt_gain_step`, `sqrt_gain_takeoff`, `nonlinear_zero_kill`
- `Hagi/Growth/PlasticityLedger.lean` — `kl_le_log_card`, `radius_le_log_card`, `radius_zero_of_eq`
- `Hagi/Growth/RatioTakeoff.lean` — `cone_ratio_step`, `cone_ratio_invariant`, `ratio_takeoff`, `frontier_decay_no_growth`
- `Hagi/Growth/RecursiveSelfDevelopment.lean` — `opportunity_renewal`, `recursive_self_development`, `multiplicative_growth`, `sum_realized`, `closed_loop_takeoff`
- `Hagi/Growth/RoundViability.lean` — `round_exhausted`, `round_viable`, `cycle_criterion`
- `Hagi/Growth/RsiCriterion.lean` — `rsi_step_growth`, `rsi_cone_criterion`
- `Hagi/Growth/Saturation.lean` — `never_overshoot`, `pl_gap_geometric`, `saturation_limit`, `pl_gap_geometric_lo`, `takeoff_with_saturation`
- `Hagi/Growth/SeedOnly.lean` — `cycle_decay_mono`, `cycle_decay_ratio`, `channel_switch`, `sum_dist_mean_le`, `seed_only_disp_bound`, `seed_only_grow_stop`
- `Hagi/Growth/SelfDevelopment.lean` — `controller_max_exists`, `self_development_find`, `certified_gain_select`, `search_cost_bound`
- `Hagi/Growth/StateBinding.lean` — `capability_takeoff_state`, `candidate_completeness_find`, `usableFrontier_renewal`
- `Hagi/Growth/T3Ignition.lean` — `ignitionGate_nonneg`, `ignitionCeiling_pos`, `T3_ignition`
- `Hagi/Growth/TakeoffElasticity.lean` — `elasticity_chain`, `takeoff_elasticity`, `decay_elasticity`, `elasticity_chain_horizon`
- `Hagi/Growth/Thermostat.lean` — `thermostat_stop`, `merge_gate_eventually`, `thermostat_phase_point`, `phase_concentration`, `consolidation_certificate`, `gibbs_representative`, `hagi_certified_state`, `certified_state_tv` (+11)
- `Hagi/Information/DiscreteFannes.lean` — `trace_unitary_conj`, `trace_cfc_eq`, `entropy_eq_sum`, `entropy_nonneg`, `unitary_row_sq_sum`, `unitary_col_sq_sum`, `diag_eq_spectral_mix`, `entropy_le_diagonal` (+56)
- `Hagi/Information/GainRecoverability.lean` — `dotSelf_nonneg`, `devEnergyF_pos_iff`, `recoverable_avg`, `devSignal_self`
- `Hagi/Information/MemoryCapacity.lean` — `separated_needs_capacity`, `bits_floor`
- `Hagi/Information/Pinsker.lean` — `pinsker4_fin`, `gen_pair_bound`, `turns`, `cmi_iteration`
- `Hagi/Information/RoutingCapacity.lean` — `no_free_recovery`, `quantized_separation_needs_range`, `repRate_trichotomy`, `router_capacity_bound`
- `Hagi/Model/ALiBi.lean` — `alibi_bias_anti`, `alibi_bias_nonpos`, `alibi_kernel_decay`, `alibi_kernel_decay_lt`
- `Hagi/Model/AdaptiveChunking.lean` — `adaptive_le_static`, `adaptive_lt_of_strict`
- `Hagi/Model/BYOL.lean` — `bl_bounds`, `bl_anti`, `bl_zero_at_perfect`, `cos_scale_inv`
- `Hagi/Model/BestOfN.lean` — `best_of_n_mean_le_sup`, `best_of_n_pos`
- `Hagi/Model/BlockNorm.lean` — `global_eq_mean_blocks`, `equal_blocks_global`
- `Hagi/Model/CFG.lean` — `cfg_interp`, `cfg_convex`, `cfg_boost`
- `Hagi/Model/CertifiedTransition.lean` — `certifiedTransition_of_advance`, `certified_trajectory_budget`, `certified_trajectory_risk`, `certified_trajectory_capability`, `witness_certifiedTransition`, `certificate_of_transition`, `transition_safe_selection`, `wsd_cycle_bound` (+3)
- `Hagi/Model/ComputeOptimal.lean` — `chinchilla_optimum`
- `Hagi/Model/ConsolidationMirror.lean` — `context_distillation_identity`, `gibbs_variational_floor`, `distillation_floor_attained_iff_kl_zero`, `grow_gain_from_mirror`, `grow_gain_nonneg`, `core_premises_grow_operational`
- `Hagi/Model/CycleCertificate.lean` — `cycle_certificate_composition`, `growSeq_capability_nonneg`, `growSeq_energy_const`, `honest_trajectory_global`
- `Hagi/Model/DDPM.lean` — `alphaBar_succ`, `alphaBar_mono`, `alphaBar_exp_bound`, `ddpm_recover`
- `Hagi/Model/DPO.lean` — `boltzmann_from_reward`, `boltzmann_norm`, `bt_pref_iff`
- `Hagi/Model/DiffAttention.lean` — `sm_sum_one`, `sm_nonneg`, `sm_shift`, `noise_cancel`, `diff_range`
- `Hagi/Model/DistillCert.lean` — `quant_pointwise`, `quant_L2`, `two_sq`, `consolidation_bound`
- `Hagi/Model/FlashAttention.lean` — `flash_io_lt`, `flash_io_antitone`
- `Hagi/Model/FlowMatching.lean` — `flow_start`, `flow_end`, `flow_convex`, `flow_mid`, `flow_const_velocity`
- `Hagi/Model/GAE.lean` — `gae_weight_bound`, `gae_weight_pos`
- `Hagi/Model/GDNBridge.lean` — `gdn_onehot_is_colUpdate`, `gdn_transpose_is_ramWrite`, `gdn_onehot_interp`
- `Hagi/Model/GDNRAM.lean` — `ram_read_after_write`, `ram_write_independent`, `ram_write_idem`
- `Hagi/Model/GQA.lean` — `gqa_kv_lt`, `gqa_kv_ratio`, `gqa_kv_mono`
- `Hagi/Model/GRPO.lean` — `groupAdv_sum_zero`, `groupAdv_sq_decomp`, `groupAdv_sq_min`, `groupAdv_std_unit`
- `Hagi/Model/GradNorm.lean` — `gnBalanced`, `gnPos`, `gnInverse`
- `Hagi/Model/Grokfast.lean` — `decompose`, `amp_recompose`, `const_grad_fix`, `amp_inner_ge`
- `Hagi/Model/HNet.lean` — `hier_seq_shorten`, `hier_attn_saving`, `hier_attn_saving_lt`, `amgm3`, `hnet_cost_floor`
- `Hagi/Model/HypothesisCompetition.lean` — `dhcTotal_pos`, `dhcWeights_pos`, `dhcWeights_sum_one`, `dhcWeights_le_one`, `dhcWeights_mono`, `dhcStep_suppressed`, `dhcStep_abs_bound`, `dhcOrbit_succ` (+9)
- `Hagi/Model/LabelSmoothing.lean` — `ls_sum_one`, `ls_nonneg`, `ls_pointwise_dist`, `ls_l1_bound`, `ls_entropy_ge`
- `Hagi/Model/LayerNorm.lean` — `mean_smul`, `variance_smul`, `ln_scale_invariant`, `variance_decomp`, `ln_sum_zero`
- `Hagi/Model/LoRA.lean` — `lora_out`, `lora_kernel_preserved`, `lora_param_saving`
- `Hagi/Model/LogitPSV.lean` — `logitPSV_gap_nonneg`, `logitPSV_gap_zero_of_no_spread`, `logitPSV_weights_frozen`
- `Hagi/Model/LookaheadTrajectory.lean` — `anchor_eq_ema`, `anchor_stable`
- `Hagi/Model/MLA.lean` — `mla_cache_saving`
- `Hagi/Model/MachineBridge.lean` — `machine_advance_certified`
- `Hagi/Model/MambaSSM.lean` — `ssm_linear_cost_lt`, `ssm_memory_const`, `ssm_state_bound`, `mamba_disc_contract`
- `Hagi/Model/Matryoshka.lean` — `matryoshka_norm_le`, `matryoshka_dist_le`
- `Hagi/Model/MeasuredEffects.lean` — `trainStep_measured`, `trainStep_budget_balance`, `trainStep_capability_band`, `ofStageEffects_roundtrip`, `totalCost_ofStageEffects`, `totalRisk_ofStageEffects`
- `Hagi/Model/MeasurementCert.lean` — `claimed_floor`, `claimed_pos_of_signal`, `claimed_ceiling`, `chain_floor`
- `Hagi/Model/MemoryConsolidation.lean` — `consolidation_bits_cap`, `consolidation_no_free_lunch`
- `Hagi/Model/Mixup.lean` — `mixLabel_dist`, `mix_loss_le`
- `Hagi/Model/MoD.lean` — `mod_layer_cost_lt`, `mod_stack_saving`
- `Hagi/Model/ModeConnectivity.lean` — `energy_convex`, `linear_no_barrier`, `linear_midpoint_bound`, `swa_average_bound`
- `Hagi/Model/ModelSoup.lean` — `soup_mem`, `soup_loss_le_avg`, `ema_invariant`
- `Hagi/Model/ModernHopfield.lean` — `hopfield_concentration`, `capacity_bound_arith`
- `Hagi/Model/MoeExpansion.lean` — `moe_shared_expansion_identity`, `shared_down_projection_iff`
- `Hagi/Model/MuPScaling.lean` — `row_output_bound`, `muP_width_invariant`, `sp_grows_with_width`, `muP_bound_le_sp_bound`
- `Hagi/Model/NTXent.lean` — `nt2_nonneg`, `nt2_le_log2`, `nt2_anti`, `nt2_zero_margin`
- `Hagi/Model/NeuralComputer.lean` — `nc_cpu_frozen`, `nc_base_frozen`, `nc_mem_only_via_write`, `nc_budget_ledger`, `nc_risk_mono`
- `Hagi/Model/Perceiver.lean` — `perceiver_cost_lt`, `perceiver_cost_ratio_lt`, `perceiver_saving_pos`, `perceiver_saving_mono`
- `Hagi/Model/PreNorm.lean` — `preNorm_step_bound`, `preNorm_depth_bound`
- `Hagi/Model/QKNorm.lean` — `qk_logit_bound`, `qk_no_saturation`
- `Hagi/Model/QuantizedAdvance.lean` — `advanceQ_quantized`, `advanceQ_prox`, `ReferenceMachine`, `ReferenceMachine`
- `Hagi/Model/RLHF.lean` — `rlhf_penalty_floor`
- `Hagi/Model/RMSNorm.lean` — `ms_smul`, `rn_scale_invariant`, `rn_unit_rms`, `rms_not_centered`
- `Hagi/Model/RVCore.lean` — `wordAdd_spec`, `wordSub_spec`, `execDeterministic`, `wordAnd_spec`, `wordAnd_idem`
- `Hagi/Model/ReZero.lean` — `rezero_identity`, `rezero_perturb_bound`
- `Hagi/Model/ReferenceMachine.lean` — `jointStep_energy`, `jointStep_energy_decrease`, `machine_quant_err_bound`, `machine_energy_bound`
- `Hagi/Model/Residual.lean` — `res_bounded_drift`, `cascade_exp_bound`, `linear_le_exp_contrast`
- `Hagi/Model/RoPE.lean` — `rot_normSq_one`, `rope_normSq_preserved`, `star_mul_self`, `rope_shift_invariant`
- `Hagi/Model/SWA.lean` — `swa_cost_lt`, `swa_cost_ratio_lt`, `swa_cost_mono`
- `Hagi/Model/Sidon.lean` — `sidon_diff_eq`, `sidon_pair_diff_injective`, `sidonSet_golomb4`, `advance_weights_shared`
- `Hagi/Model/Softcap.lean` — `tanhBound`, `softcap_bound`, `softcap_zero`
- `Hagi/Model/SoftmaxStep.lean` — `logitCE_deriv`, `logitGrad_deriv`, `sigmoid_sq_le_quarter`, `grad_lipschitz`, `logitCE_descent_lemma`, `descent_step`, `descent_example`, `joint_stage_logitCE` (+3)
- `Hagi/Model/SourceMixture.lean` — `mixture_sum_one`, `mixture_nonneg`, `successDist_norm`, `successDist_nonneg`
- `Hagi/Model/Speculative.lean` — `accept_chain_prob`, `speculative_expected_tokens`, `speculative_win`
- `Hagi/Model/StageSemantics.lean` — `growAdvance_capability`, `growAdvance_budget`, `grow_two_step_consistent`, `grow_strict_productive`, `growSeq_capability`, `growSeq_budget_ledger`, `advance_energy_drop`, `cone_growth_window` (+42)
- `Hagi/Model/StreamingLLM.lean` — `stream_bounded`, `stream_mem_lt`, `stream_saving_step`
- `Hagi/Model/SwiGLU.lean` — `sig_lt_one`, `sig_pos`, `swish_abs_le`, `swiglu_abs_le`
- `Hagi/Model/SwitchMoE.lean` — `switch_floor`, `switch_floor_eq_iff`
- `Hagi/Model/TripletLoss.lean` — `tl_nonneg`, `tl_zero`, `tl_pos`, `tl_le_hinge`, `tl_mono_pos`, `tl_mono_neg`
- `Hagi/Model/Upcycling.lean` — `upcycle_preserves`
- `Hagi/Model/VicReg.lean` — `pv_nonneg`, `vh_nonneg`, `vh_zero`, `vh_anti`
- `Hagi/Model/WeightTying.lean` — `wt_saving`
- `Hagi/Model/ZLoss.lean` — `zloss_bound`, `zloss_zero`
- `Hagi/Numerics/SoftmaxFix.lean` — `ce_grad_sum_zero`, `margin_rest_sum`, `ce_loss_margin`, `adamw_equilibrium_magnitude`, `distill_grad_self_zero`, `margin_equilibrium_value`, `adamw_normalized_bounds`, `fixed_ce_grad_sum_zero` (+8)
- `Hagi/Omni/CapabilityMatrix.lean` — `groupGap_nonneg`, `groupGap_zero_iff_indep`, `admissionChain`
- `Hagi/Omni/CrossModalGap.lean` — `crossModalGap_eq_kl`, `margX_sum_one`, `margY_sum_one`, `margX_pos`, `margY_pos`, `prodMarg_sum_one`, `crossModalGap_nonneg`, `crossModalGap_zero_iff_indep`
- `Hagi/Omni/OmniInvariant.lean` — `omniGrowth_admits`, `omniGrowth_positive`, `omniGate_crossModal`, `omniSafeStep`, `omniSafeStep_sum`, `omniGate_complete`, `crossModalGap_pos_of_dep`, `omniPhi_step` (+2)
- `Hagi/Omni/SharedStateComposition.lean` — `sharedStateEnergy`, `omniLeafCost`, `omniParamCost`, `sharedStateCostBound`, `sharedStatePerturbed`
- `Hagi/Omni/TemporalState.lean` — `geom_sum_fin`, `driftTube_closed`, `drift_limit`, `drift_zero`
- `Hagi/Optimization/AdaGrad.lean` — `acc_mono`, `adagrad_step_anti`
- `Hagi/Optimization/AdamBias.lean` — `one_sub_beta_geom`, `pow_lt_one'`, `adamM_recur`, `adam_bias_bound`, `adam_unbiased_const`
- `Hagi/Optimization/AdamW.lean` — `adamw_shrink`, `l2_decay_diluted`
- `Hagi/Optimization/AdaptiveCycle.lean` — `adaptive_cycle_expansions`, `adaptive_hagi_contract_thermal`
- `Hagi/Optimization/CautiousOptimizer.lean` — `cautiousMask_abs_le`, `cautiousAligned`, `cautiousId`, `cautiousZero`
- `Hagi/Optimization/Checkpoint.lean` — `ckpt_mem_floor`, `ckpt_sqrt_opt`
- `Hagi/Optimization/ComputeScaling.lean` — `compute_scaling_lower_bound`, `compute_scaling_bound_attained`, `compute_scaling_multi`, `compute_scaling_multi_attained`
- `Hagi/Optimization/DREAM.lean` — `dream_delayed_gd`, `dreamY_gap_norm`, `dream_tau_extrapolation`, `dream_gd_as_plRec`, `dream_gd_wsd`
- `Hagi/Optimization/DirectionPacking.lean` — `sum_sq_cauchy`, `Sop_inner`, `Sop_inner_left`, `Sop_self_adjoint`, `Sop_trace`, `Sop_trace_sq`, `welch_bound_core`, `welch_min_dimension` (+1)
- `Hagi/Optimization/GradAccum.lean` — `accum_equiv`
- `Hagi/Optimization/InexactContraction.lean` — `inexact_contraction_bound`, `inexact_contraction_floor`, `inexact_contraction_halt`, `anderson_floor_gain`, `anderson_halt`
- `Hagi/Optimization/InfoPreservation.lean` — `info_preservation_regret`
- `Hagi/Optimization/LLRD.lean` — `llrd_strict_mono`, `llrd_nonneg`
- `Hagi/Optimization/LRSchedule.lean` — `pl_step_noise_bound`, `late_phase_bound`, `wsd_full_bound`, `cos_anti`, `cosLR_nonneg`, `cosLR_start`, `cosLR_end`, `cosLR_anti`
- `Hagi/Optimization/Lion.lean` — `sign_sq_le_one`, `lion_step_norm_bound`
- `Hagi/Optimization/Lookahead.lean` — `lookahead_mem`, `lookahead_gap`, `lookahead_range`
- `Hagi/Optimization/MirrorDescent.lean` — `mirrorStep_pos`, `mirrorStep_sum_one`, `mirror_descent_identity`, `mirror_descent_floor`, `mirror_descent_attainment`, `hedge_free_energy_step`, `aif_efe_attainment`, `aif_efe_floor` (+20)
- `Hagi/Optimization/Momentum.lean` — `momentumRate_char`, `momentumRate_pos_lt_one`, `momentum_bound`, `momentum_floor`, `momentum_beta_strict_cost`, `momentum_direction_beats_inertia`, `momentum_achievability`, `momentum_entry_horizon` (+23)
- `Hagi/Optimization/NeuronAlloc.lean` — `neuron_alloc_lower_bound`, `neuron_alloc_opt_attained`, `neuron_alloc_equal_costs`
- `Hagi/Optimization/PLConvergence.lean` — `pl_linear_convergence`, `pl_sufficient_horizon`
- `Hagi/Optimization/PPOClip.lean` — `ppoClip_le_upper`, `ppoClip_le_lower`, `ppoClip_mono`, `ppoClip_fixed`, `ppo_clip_term_abs_bound`, `ppo_surr_upper_bound`
- `Hagi/Optimization/PolyStep.lean` — `polyWeights_nonneg`, `polyWeights_sum_one`, `polyWeights_strict_mono`, `polyDelta_basis_sum`
- `Hagi/Optimization/RobbinsMonro.lean` — `robbins_monro_decay`, `robbins_monro_abs`, `robbins_monro_bias`
- `Hagi/Optimization/SAM.lean` — `zero_mem_ball`, `sam_ge`, `ball_mono`, `sam_mono`, `sam_flat`
- `Hagi/Optimization/SphericalDamping.lean` — `chordal_residual_eq`, `angular_damping_window`, `unit_inner_self`, `mixture_norm_sq`, `normalized_mixture_inner`, `mixture_normalize_unit`, `normalized_mixture_distance`
- `Hagi/Optimization/SubspaceGrowth.lean` — `projResidual_ortho`, `projResidual_self_inner`, `projResidual_le_norm`, `growth_finite`
- `Hagi/Percolation/Site.lean` — `cellAdj_symm`, `cellAdj_loopless`, `crossing_mono`, `card_`, `R_monotone`, `edgeless_reachable_eq`, `parity_not_crossing1`, `parity_crossing2` (+2)
- `Hagi/Planning/Imagination.lean` — `forward_thinking_regret`, `imagination_compounding`, `adaptive_first_sufficient`, `branching_avoids_detectable_failure`, `branching_dominates_linear`, `grpo_centered_sum_zero`, `grpo_advantage_pos`
- `Hagi/Prelude/Info.lean` — `KLSupported_pos`, `klDef_terms_finite`, `softDef_pos`, `softDef_sum_one`, `kl_nonneg_of_nonneg`, `kl_nonneg`
- `Hagi/Pretraining/DataPruning.lean` — `pruning_nfl`, `pruning_free_for_constant`, `pruning_recovery_bound`
- `Hagi/Pretraining/Dust.lean` — `hcCard`, `hcFactorized`, `hcDelta`, `crossDiff`, `esUnbiased`, `drawPairOrtho`, `varianceHalving`, `dustNoiseHalving`
- `Hagi/Pretraining/DustAlign.lean` — `hcVarKTotal`, `hcVarK`, `esErrCentered`, `dustVarK`, `prodQ_nonneg`, `prodQ_isProb`, `dustVarK_expQ`, `pairQ_isProb` (+9)
- `Hagi/Pretraining/Grokking.lean` — `drift_solution`, `drift_hasDeriv`, `drift_norm_nondecreasing`, `drift_half_life`, `grokking_timescale_separation`, `drift_total_variation`
- `Hagi/Pretraining/ProbeError.lean` — `fd_probe_error`, `linear_probe_exact`, `residual_vec_bound`, `residual_vec_diff`, `mlpResidual_bound`, `cut_signal_triangle`, `safe_certificate_margin`, `probe_safe_accept` (+4)
- `Hagi/Pretraining/RobustnessLaw.lean` — `robust_interpolation_lipschitz_floor`, `no_lipschitz_interpolator_of_steep`, `robust_spacing_bound`, `lipschitz_floor_of_noisy_labels`, `noisy_interpolation_step_cap`, `robust_slows_learning`, `robust_budget_floor`
- `Hagi/Pretraining/Speedrun.lean` — `cePartition_move`, `cePartition_factor`, `ceLogit_move_change`, `head_probe_linear`, `hadamard_probe_inversion`, `probe_lower_bound`
- `Hagi/Pretraining/SyntheticPretrain.lean` — `time_to_capability_correct`, `synth_investment_dominates`, `task_selection_marginal`
- `Hagi/Pretraining/TrustRegion.lean` — `transpose_mul_self_of_mul_transpose`, `hadamardRows_sup_bound`, `orthonormal_mulVec_isometry`
- `Hagi/Probability/AdaptiveSuccess.lean` — `adaptive_success_count_floor`, `adaptive_success_concentrated`
- `Hagi/Probability/Azuma.lean` — `hoeffding_lemma_prefix`, `prodE_snoc`, `azumaSum_congr`, `azumaSum_snoc`, `azuma_mgf`, `azumaSum_neg`, `azuma_tail_low`, `azumaSum_sub` (+3)
- `Hagi/Probability/BatchSNR.lean` — `snr_realized`, `snr_linear`, `snr_ge_one_iff`, `gain_decreasing_past_critical`
- `Hagi/Probability/BernoulliFactory.lean` — `probAccept_eq_bernPoly`, `binomWeight_nonneg`, `probAccept_bounds`
- `Hagi/Probability/CertifiedEstimator.lean` — `prodDens_nonneg`, `sum_prod_factor`, `prodE_one`, `prodPq_le_one`, `prodPq_compl`, `prodPq_mono`, `prodPq_union_le`, `prodE_exp_sum` (+24)
- `Hagi/Probability/ChernoffCGF.lean` — `kl_dv_attained`, `hellinger_sq_eq_one_minus_bc`, `hellinger_le_half_kl`, `kl_chernoff_tilt`, `markov_finite`, `chernoff_event`, `exp_tilt_interpol`, `cramer_tilt_kl` (+7)
- `Hagi/Probability/ConditionalSuccess.lean` — `concDelta_nonneg`, `success_count_lower`, `success_count_lower_p0`, `log_growth`, `takeoff_time_form`
- `Hagi/Probability/EntropyConvexity.lean` — `log_sum_ineq`, `log_sum_ineq_on`, `kl_data_processing`, `log_concave_two`, `xlogx_convex`, `xlog_div_convex`, `kl_convex_first`, `kl_product_additive` (+5)
- `Hagi/Probability/ExpChord.lean` — `exp_chord`, `hoeffding_chord_mgf`, `log_chord`, `amgm_weighted`, `young_two`, `hoelder_finite`, `minkowski_finite`, `lp_one_le_card` (+4)
- `Hagi/Probability/Freedman.lean` — `exp_tail_two`, `freedman_lemma_prefix`, `freedman_mgf`, `freedman_tail_low`, `cond_var_le_second`, `adaptive_success_freedman`, `freedman_confidence`
- `Hagi/Probability/FreedmanTwoSided.lean` — `pmf_weight_sum`, `pmfMean_const`, `pmfMean_congr`, `pmfMean_add`, `pmfMean_sub`, `pmfMean_mul_const`, `pmfMean_const_mul`, `pmfMean_nonneg` (+41)
- `Hagi/Probability/GibbsConcentration.lean` — `gibbs_energy_variance_bound`, `thermostat_var_stop`, `thermostat_threshold`, `gibbs_var_tendsto_zero`, `gibbs_var_steps_bound`, `gibbs_excess_mean_bound`, `proxy_cert_preserved`, `proxy_cert_lost` (+9)
- `Hagi/Probability/GibbsCooling.lean` — `gibbs_concentration`, `gibbs_concentration_tendsto`, `free_energy_sandwich`, `gibbs_neg_log_share_tendsto`, `gibbs_excess_energy_bound`, `gibbs_expected_energy_bound`, `gibbs_expected_energy_tendsto`, `gibbs_tv_eq` (+8)
- `Hagi/Probability/GibbsInfoCore.lean` — `gibbs_expected_energy_lower`, `free_energy_upper`, `gibbs_kl_uniform_split`, `gibbs_energy_gap_crude`, `gibbs_weight_log_decomp`, `gibbs_katoni_kl`, `finite_kl_nonneg`, `gibbs_variational` (+2)
- `Hagi/Probability/KLSBridge.lean` — `expQ_mono`, `gradCovBound`, `uncorrMeanVar`, `expQ_varEq`, `klsBatchNoise`, `klsChebyshev`
- `Hagi/Probability/MWU.lean` — `mwu_potential_step`, `mwu_potential_lower`, `mwu_potential_squeeze`, `mwu_uniform_squeeze`, `mwu_potential_upper_uniform`, `mwu_prod_exp`, `mwu_partition_sum`, `mwu_regret_static` (+4)
- `Hagi/Probability/MomentBounds.lean` — `popoviciu_var`, `chebyshev_popoviciu`, `cantelli_one_side`, `popoviciu_abs_dev`, `bhatia_davis`, `bhatia_implies_popoviciu`, `var_le_delta_excess`, `excess_ge_var_over_range`
- `Hagi/Probability/NoiseTemperature.lean` — `popVar_eq`, `sum_centered`, `card_pos_of_nonempty`, `prod_two_sel`, `sum_coord`, `sum_pair`, `uniP_isProb`, `uniP_dens` (+4)
- `Hagi/Probability/PMFBridge.lean` — `ofReal_finset_sum`, `pmfWeight_le_one`, `toPMF_apply`, `fromPMF_sum`, `toPMF_fromPMF`, `fromPMF_toPMF`
- `Hagi/Probability/PinskerTV.lean` — `tv_le_pos_part_kl`, `bhattacharyya_cauchy`, `one_minus_bc_le_half_kl`, `pinsker_sqrt_kl`, `tv_dual_abs`, `neg_log_bc_le_half_kl`, `tv_le_sqrt_one_minus_exp`, `kl_joint_convex` (+2)
- `Hagi/Probability/SphericalAngle.lean` — `sphericalAngle_add_two`, `sphericalAngle_factor_lt_one`, `sphericalAngle_even_geo`, `sphericalAngle_odd_geo`, `tail_parity_split`, `sphericalAngle_tail_bound`, `sphericalAngle_tendsto_zero`, `sphericalAngle_six` (+21)
- `Hagi/Probability/StationaryFlatness.lean` — `tail_sum_identity`, `inv_sq_le_sub_inv`, `sum_pow2_inv_le`, `flatness_moment_bound`
- `Hagi/Probability/ThermoAxes.lean` — `noise_axes_coincide`, `noise_budget_axes_equal`
- `Hagi/Probability/ThermoBridge.lean` — `prodE_as_expQ`, `batchVar_expQ`
- `Hagi/Probability/WSqD.lean` — `stable_phase_noise`, `cooldown_tail_constant`, `wsqd_noise_budget`
- `Hagi/Runtime/ControllerGates.lean` — `univNE`, `sup_div`, `logitRange_scale`, `variance_gate_contract`, `variance_gate_normalize`, `trust_region_proj_norm`, `trust_region_nearest`, `dynamic_branch_variance`
- `Hagi/Runtime/LiveDeltaQuant.lean` — `quantMat_entry`, `quantMat_sq_bound`
- `Hagi/Runtime/TernaryExact.lean` — `qTern_error_in`, `qTern_error_out`, `ternary_split_bound`, `ternary_inrange_bound`, `ternary_split_le`, `satTail_nonneg`, `sqrt_add_le`, `quant_energy_bridge_saturation` (+1)
- `Hagi/Sparsity/SparseStep0.lean` — `sparse_step0`
- `Hagi/Spectral/RankGrowth.lean` — `rank_orthogonal_growth`, `span_growth_zero_interference`
- `Hagi/Step/AdaptiveSafeQP.lean` — `latticeNet_norm_le`, `latticeNet_covers`, `latticeNet_card_le`, `adaptive_net_concentration`, `adaptive_direction_concentration`, `adaptive_safeQP_feasibility`
- `Hagi/Step/ArmijoAcceptance.lean` — `armijo_sufficient_decrease`, `armijo_step_size`
- `Hagi/Step/CPUFreeze.lean` — `cpu_frozen`, `norm_le`, `anchor_drift`
- `Hagi/Step/CausalFilter.lean` — `gqa_shared_score`, `gqa_cache_card`, `swa_reach_step`, `swa_reach_eq`, `swa_reach_mono`, `swa_relay_full`, `swa_cost_bound`, `causal_prefix_determined` (+1)
- `Hagi/Step/Compound.lean` — `compound_c_stabilizes`, `compound_constant_regime`, `compound_trajectory`, `compound_cumulative`, `compound_budget_interval`, `compound_fold_interval`
- `Hagi/Step/Dominate.lean` — `domination_decompose`, `domination_regression`, `safe_consensus_harmless`, `dominated_collateral_bound`, `guard_weight_parity`
- `Hagi/Step/FrobeniusLMO.lean` — `sgd_stable_step`, `muon_stable_step`, `muon_avg_not_max`, `lmo_lower_bound`, `lmo_attained`, `lmo_descent_direction`
- `Hagi/Step/GPM.lean` — `mulVec_eq_dotProduct`, `gpm_zero_forgetting`, `sigma_orth_zero`, `sigma_orth_necessary`
- `Hagi/Step/GradCentralization.lean` — `gc_zero_sum`, `gc_pythagoras`, `gc_norm_le`, `gc_const_zero`
- `Hagi/Step/GradClip.lean` — `clip_norm_le`, `clip_eq_of_le`, `clip_idem`, `clip_dir`, `clip_descent_pos`
- `Hagi/Step/HybridState.lean` — `stale_momentum_bias`, `fresh_momentum_unbiased`
- `Hagi/Step/Joint.lean` — `jointStep_conflict_regression`, `jointStep_regression_bound`, `trustRegion_bound`
- `Hagi/Step/JointPreserve.lean` — `diversity_noncollapse`, `geom_shift`, `diversity_floor`, `diversity_floor_fresh`, `diversity_floor_strict_pos`
- `Hagi/Step/KLSSafeQP.lean` — `klsSafeQP_certified`
- `Hagi/Step/LazyAdam.lean` — `lazyDecay_exact`, `lazyReplay_exact`, `supportSet_bound`
- `Hagi/Step/LazyAdamMomentum.lean` — `dense_m_decay`, `lazy_moment_drift`, `lazy_momentum_bound`
- `Hagi/Step/LiveDeltaSafe.lean` — `updateNewest_base`, `updateNewest_length`, `updateNewest_tail`, `updateNewest_cost`, `safe_update_window`
- `Hagi/Step/MDLObjective.lean` — `mdlObjective_delta`, `mdlObjective_nonincreasing`, `mdlObjective_tradeoff`, `mdlObjective_lambda_zero`, `mdlObjective_neg_lambda_forbidden`
- `Hagi/Step/MDLThreeCurrency.lean` — `J3_nonincreasing`, `double_counting_identified`, `no_compression_below_entropy`
- `Hagi/Step/MetricSafeQP.lean` — `inner_transport`, `mDist_eq`, `mProject_exists_unique`
- `Hagi/Step/Muon.lean` — `chunked_sum_exact`, `ce_prior_decomposition`, `grad_norm_grows`, `mup_grad_invariant`, `muon_step_bound`, `muon_pl_rate`, `ns_invariant`, `ns_monotone_ascent` (+2)
- `Hagi/Step/MuonAlign.lean` — `unitary_diag_abs_le`, `muon_alignment_optimal`
- `Hagi/Step/MuonTwoLevel.lean` — `ns_gap_scaled`
- `Hagi/Step/MuonWD.lean` — `muon_wd_recursion`, `wd_boundedness`
- `Hagi/Step/NCEExact.lean` — `nce_decomposition`, `nce_correction_pos`, `nce_var_identity`, `secondMoment_ge_mean_sq`, `adaptiveK_bound`, `jensen_log`, `partEst_unbiased`, `secondMomentW_ge_sq` (+3)
- `Hagi/Step/NewtonPolar.lean` — `newton_polar_scalar_error`, `newton_error_ratio`, `newtonStep_ge_one`, `newton_polar_convergence`, `newton_polar_tendsto_one`, `newton_step_descent`, `newton_step_descent_lt`, `newton_iter_bracket`
- `Hagi/Step/PreconditionerDescent.lean` — `preconditioned_descent`, `preconditioned_step_size`
- `Hagi/Step/ProjectionDescent.lean` — `proj_descent_inner`, `min_dist_to_vi`, `safeQP_descent`, `joint_stage_linked`, `orthogonal_zero_interference`, `hard_budget_forces_orthogonal`
- `Hagi/Step/RiemannNewtonPolar.lean` — `radial_tangential_curvature`
- `Hagi/Step/SNRWeights.lean` — `uniform_is_mean`, `focused_beats_uniform`
- `Hagi/Step/SafeQP.lean` — `proj_residual_identity`, `proj_residual_nonneg`, `proj_monotone`, `spectralProj_idempotent`, `spectralProj_selfAdj`, `spectralProj_orth`, `spectral_tail_energy`, `three_stage_error_budget` (+9)
- `Hagi/Step/SafeQPStep.lean` — `safeqp_second_order`, `safeqp_trust_region`, `safeqp_monotone_domain`, `le_safeqpEtaMax_iff`, `safeqp_eta_max_domain`, `safeqp_eta_max`, `safeqp_eta_zero_direction`, `le_safeqpEtaMaxConflictFree_iff` (+2)
- `Hagi/Step/SignSGD.lean` — `sign_inner_nonneg`, `sign_inner_pos`, `sgn1_fix`, `sgn1_ternary`, `sign_idempotent`
- `Hagi/Step/StochasticSafeQP.lean` — `minibatch_inner_tail`, `minibatch_inner_concentration`, `minibatch_inner_concentration_upper`, `stochastic_safeQP_feasibility`, `sqrt_div_sq`, `lr_batch_equivalence`
- `Hagi/Step/Upgrades.lean` — `skip_bound`, `readPolicy_exists`, `sink_cost_bound`, `sink_window_substitutes`, `ns_geometric_envelope`
- `Hagi/Step/WarmupSchedule.lean` — `warmup_eta_monotone`, `warmup_telescope_bound`, `warmup_beats_constant`
- `Hagi/Step/WeightDecay.lean` — `wd_norm_bound`
- `Hagi/System/Certificates.lean` — `penalty_drop_bound`, `cycle_certificate_sound`
- `Hagi/System/DiscreteStep.lean` — `quantized_descent_telescope`
- `Hagi/System/GrowthState.lean` — `macro_termination_derived`, `protected_generation_budget`, `verify_decrease`, `potential_grow`, `potential_merge`, `potential_joint`, `potential_compress`, `growth_cycle_potential` (+7)
- `Hagi/System/GrowthStateViews.lean` — `GrowthState_parts_roundtrip`, `toParts_injective`
- `Hagi/System/StepCertificate.lean` — `stepCertificate_base`, `safe_selection_productive`, `safe_feasible_selection_productive`
- `Hagi/System/UnifiedStep.lean` — `unified_step_certificate`, `unified_step_budget`
- `Hagi/Unified/AdvanceWitness.lean` — `certified_invariant_advance_witness`, `witness_step_landauer_cap`, `witness_horizon_landauer_cap`
- `Hagi/Unified/AlgebraMatrixCore.lean` — `core_stable_and_optimal`, `matrix_svd_nonneg_and_mdl_antitone`
- `Hagi/Unified/AnytimeMartingale.lean` — `merge_stage_linked`, `merge_stage_linked_nonneg`, `anytime_valid_budget`, `eprocess_stopped_budget`, `ville_supermartingale`, `ville_anytime_false_alarm`, `anytime_failure_budget`, `anytime_safety` (+2)
- `Hagi/Unified/AnytimePACBayes.lean` — `real_mono_prob`, `anytime_catoni`
- `Hagi/Unified/ArchitectureTheorem.lean` — `entTV_nonneg`, `entTV_symm`, `binEnt_half`, `entropy_continuity_pinsker`, `binEnt_mono`, `binEnt_nonneg`, `entropy_continuity_pinsker'`, `distill_kl_bridge` (+23)
- `Hagi/Unified/Assumptions.lean` — `masterhagi_trunc_of_assumptions`, `idle_cycle_fixed`, `idle_Qgen_zero`, `trunc_nonvacuous`, `premises_to_certified`
- `Hagi/Unified/BudgetCore.lean` — `budget_allocation_and_distillation`, `budget_waterfill_and_lowrank`
- `Hagi/Unified/CanonicalParams.lean` — `advance_params_ne`, `bridge_update`, `idProj`
- `Hagi/Unified/CapabilityLocal.lean` — `capability_geometric_of_local`, `capability_strict_first`
- `Hagi/Unified/CertUnify.lean` — `tc_step_of_stepcert`, `tc_consequence`, `protoMeasured_spec`
- `Hagi/Unified/CertifiedGrowth.lean` — `certified_cone0_takeoff`, `sample_size_adequate`, `union_bound_nonneg`, `prob_ladder_lower`, `certified_gainprod_takeoff`, `certified_band_growth`
- `Hagi/Unified/CertifiedLoop.lean` — `certified_loop`, `certified_loop_all`, `gate_never_increases`, `certified_loop_strict`
- `Hagi/Unified/CertifiedTrajectory.lean` — `certified_progress_honest`, `certified_progress_signal`
- `Hagi/Unified/CommitGate.lean` — `commitProductive`, `holdSafe`, `quant_bound_of_gridQ`
- `Hagi/Unified/CoreFacades.lean` — `architecture_invariant_and_economical`, `autonomy_regret_and_stability`, `misc_quantized_telescope_and_aitken`
- `Hagi/Unified/CorePremisesDerived.lean` — `conj8_h_emp_smooth_derived`, `conj13_h_emp_lip_derived`, `core_premises_operational_scalar_v2`, `MasterHAGICoreOperational_v2`
- `Hagi/Unified/CostComposition.lean` — `hybrid_cost_lt`, `hybrid_ratio_le`
- `Hagi/Unified/DerivAlong.lean` — `lip_energy_from_gradient`, `lip_energy_quantization`, `grow_gain_from_smooth_descent`, `hasDerivAt_along_segment`, `integral_deriv_segment`, `deriv_along_segment_le`, `smooth_from_lipschitz_gradient`, `joint_emp_smooth_derived` (+3)
- `Hagi/Unified/DescentCore.lean` — `descent_drop`
- `Hagi/Unified/DescentCoreDiag.lean` — `diag_descent_eq`, `diag_descent_le`
- `Hagi/Unified/DescentCoreQuad.lean` — `quad_descent_eq`, `quadAligned`, `quad_one_step`, `quad_drop`
- `Hagi/Unified/Distillation.lean` — `soft_dial_max`, `soft_dial_zero`, `soft_entropy_bound`, `attention_scale_softens`, `attention_no_scale_saturates`
- `Hagi/Unified/DynamicsGrowthCore.lean` — `dynamics_growth_and_distillation`, `growth_balanced_and_conic`, `idle_merge_zero_gap`
- `Hagi/Unified/ExecutedCert.lean` — `measured_honest`, `measured_lower`, `telescope_measured`
- `Hagi/Unified/FannesComplete.lean` — `zs_kl`, `nml_mul`, `xlogx_superadd`, `mix_point`, `mix_entropy_upper`, `mix_entropy_lower`, `shannon_le_log_card`, `fanes_unconditional`
- `Hagi/Unified/FsGate.lean` — `fsGate_weights_eq`, `fsGate_mono`, `fsTraj_mono`, `fsGate_budget`, `fsGate_count`, `fsTraj_budget_le`, `fsTraj_count_le`
- `Hagi/Unified/FunctionalState.lean` — `fs_energy_after`, `energy_at_target`, `fs_two_steps_productive`
- `Hagi/Unified/GaugeQuotient.lean` — `norm_rot`, `norm_rot_sub`, `residual_nonneg`, `quotientResidual_gauge_invariant`, `relativeEquilibrium_residual_zero`, `seq_dev_exact`, `seq_dev_modulus`, `iterate_gauge_commute` (+2)
- `Hagi/Unified/GrandSynthesis.lean` — `budget_nonincreasing_of_nonneg_spend`, `grand_synthesis`, `risk_telescope_of_growth_covered`, `qfloor_le_of_monotone`, `grand_synthesis_weak`
- `Hagi/Unified/GrowthBridge.lean` — `additive_as_multiplicative`, `growMul_eq_grow`, `growCycle_succ`, `growCycle_zero`, `growMul_step_multiplicative`, `growCycle_growGain`, `growCycle_capability_succ`, `growCycle_capability` (+3)
- `Hagi/Unified/GrowthEnsembleCore.lean` — `growth_renews_and_seed_survives`, `merge_calibrated_and_exact`, `dual_ceiling`
- `Hagi/Unified/HonestTransition.lean` — `honest_actual_drop`, `honest_telescope`, `honest_two_steps_existent`
- `Hagi/Unified/InfoDataCore.lean` — `pinsker4_via_canon`, `info_not_free_and_detectable`, `pruning_dichotomy`, `data_certified_and_thermodynamic`
- `Hagi/Unified/InterpretiveGrowth.lean` — `pointEffect_nonneg`, `causalEffect_nonneg`, `causalEffect_zero_of_pointwise`, `causalEffect_pos_of_point`, `causalEffect_le_max`, `mass_split`, `gain_le_mix`, `passive_starves`
- `Hagi/Unified/LearningKernel.lean` — `grow_premise_derived`, `merge_premise_derived`, `merge_slack_feasible`
- `Hagi/Unified/LinkedQVec.lean` — `floor_preserved`, `qgen_hides`, `floor_catches`
- `Hagi/Unified/LinkedWitness.lean` — `wTraj_certified_family`, `linkedHAGI_witness`
- `Hagi/Unified/LiveDeltaCycle.lean` — `tri`, `audit_violation_witness`, `audit_chain`, `live_delta_cycle`
- `Hagi/Unified/Liveness.lean` — `liveness_merge`, `liveness_data_axis`, `liveness_two_axis`
- `Hagi/Unified/LoopInstances.lean` — `quadCert_hits_optimum`, `quadE_nonneg`, `quad_loop_strict`
- `Hagi/Unified/MasterHAGI.lean` — `exists`, `MasterHAGICore`, `full_cycle_field_eq`, `hagi_gen_floor`, `MasterHAGI`, `gate_success_multiplier`, `MasterHAGI_wallclock`, `log_bridge_from_multiplier` (+4)
- `Hagi/Unified/MasterHAGICoupled.lean` — `budget_no_growth`, `qvec_floor_implies_scalar`, `scalar_hides_deficit`, `coupledHAGI_nonvacuous`, `coupledHAGI_nonvacuous_strict`, `LinkedHAGIInvariant_to_coupled`, `certified_family_linked`, `certified_family_linked_progress`
- `Hagi/Unified/MasterHAGITrunc.lean` — `frontier_cone_trunc`, `frontier_cone_struct`, `sustained_takeoff_trunc`, `sustained_takeoff_struct`, `MasterHAGI_trunc`, `masterhagi_growth_witness`, `cone_premises_force_exact`
- `Hagi/Unified/MeasureProto.lean` — `machineProto_gap`, `energy_nonneg`, `machineProto_capa_mono`, `evalCapa_bounds`
- `Hagi/Unified/MemoryCycle.lean` — `rank1Block_eq_outer`, `effective_addBlock`, `effective_fold`, `effective_fromHistory`, `descentFold_eq_effective`, `blocks_length_fold`, `history_storage_cost`, `sum_sub_eq` (+13)
- `Hagi/Unified/MicroStepCert.lean` — `frobSq_eq`, `microstep_cert`, `microstep_net_drop`
- `Hagi/Unified/ModelComparison.lean` — `delta_pos_of_dominates`, `zIndicator_one_of_ge`, `zIndicator_zero_of_neg`, `piR_lower_of_certified`
- `Hagi/Unified/NCTheorem.lean` — `nc_trajectory_bound`, `nc_cpu_frozen_trajectory`
- `Hagi/Unified/NernstFannes.lean` — `dirac_sum`, `shannon_dirac_zero`, `tvHalf_dirac_eq`, `nernst_fannes`, `gibbs_nernst`
- `Hagi/Unified/PretrainOptRobustCore.lean` — `memory_capped_and_time_correct`, `opt_objective_monotone_and_bias_bounded`, `robust_growth_corridor`
- `Hagi/Unified/ProtoTrajectory.lean` — `proto_loss_mono`, `proto_loss_telescope`, `proto_progress_bound`, `proto_capa_mono`
- `Hagi/Unified/QuadBudget.lean` — `trajDropSum`, `trajDropBound`, `budgetLedger`, `commitCountBound`
- `Hagi/Unified/QuadGate.lean` — `machine_energy_lift`, `quad_gate_commit`
- `Hagi/Unified/QuadTrajectory.lean` — `gateStep_mono`, `gateTraj_mono`, `gateStep_drop`, `gateStep_pos`
- `Hagi/Unified/QuadUnify.lean` — `quadE_eq_energy`, `quadGrad_eq_grad`, `machine_one_step_zero`, `diag_is_quad`, `diagGrad_is_quadGrad`
- `Hagi/Unified/QuantSafeUpdate.lean` — `quantized_step_bound`, `quantized_safe_window`
- `Hagi/Unified/QuantizedCone.lean` — `quantized_net_gain`, `quantized_cone_gain`
- `Hagi/Unified/RecursiveClean.lean` — `locality_le_of_bounded`, `timeConsistency_eq_one`, `indepMass_eq_zero_of_cover`, `activationMass_entropy_le`, `clean_neuron_of_conditions`, `piR_le_one`
- `Hagi/Unified/RecursiveGrowth.lean` — `macro_step_decrease`, `macro_termination`, `topk_routing_optimal`, `fisher_nullspace`, `unitary_perturb_bound`, `unitary_perturb_metric`, `optimal_step_unconstrained`, `optimal_step_value` (+6)
- `Hagi/Unified/SamDescent.lean` — `sam_descent_bridge`, `sam_descent_flat`
- `Hagi/Unified/SignDescent.lean` — `sgn1_mul_self`, `sgn1_sq`, `count_nonzero_le`, `sign_scaled_aligned`, `sign_descent`, `scaled_sign_aligned_of_coherence`, `sign_is_pointwise_max`, `lion_descent`
- `Hagi/Unified/StateTakeoff.lean` — `full_cycle_capability_step`, `state_capability_takeoff`, `corePremises_of_full_refinement`
- `Hagi/Unified/StepContract.lean` — `compose_assoc`, `compose_id_left`, `compose_id_right`, `chain_decrease`, `chain_budget`, `chain_risk`, `trajectory_convergence`, `termination_via_stepcontract`
- `Hagi/Unified/StepExt.lean` — `step_warmup_monotone_and_wd_bounded`
- `Hagi/Unified/StepLaws.lean` — `step_armijo_and_sgd_stable`
- `Hagi/Unified/TernaryGrad.lean` — `sgn1_round`, `sgn1_grid_fix`, `sgn1_zero_quant_error`, `tern_grad_inner`
- `Hagi/Unified/TopLevel.lean` — `quant_residual_norm`, `quant_energy_bridge`, `quant_matrix_perturb`, `quant_matrix_perturb_norm`, `quant_loss_bridge`, `quant_frob_loss`, `frob_minkowski`, `frob_minkowski'` (+10)
- `Hagi/Unified/TransitionContract.lean` — `ctv2_contract`, `ctRisk_covers`

## Открытые проблемы

1. **Closure gap.** 138/424 модулей (33%) в замыкании капстоунов;
   286 library leaves (A=34 Objective/Descent, B=45 Step
   Compressors, C=93 Efficiency/Budget, D=19 Alignment, E=95
   мат-фундамент) не инстанцируют StepCert/DescentCore.Objective.
   Цель — 80%+ через LibrarySynthesis.
2. **Gen-1 рудименты.** 52 модуля без CertifiedLoop в замыкании
   (`python scripts/DepAudit.py`); Nonvacuity-витнесы ещё на
   CorePremises (MasterChallenge v1 снят с гейта, теорема
   депрекнута и вне основного контура).
3. **Сертификатный веер.** 8 представлений перехода не сведены
   к канонической цепочке Execution → Measurement → StepCert →
   CertifiedLoop; StepContract-моноид не завершён; скалярный
   Qgen ещё не заменён на FloorKept везде. Семейственный
   телескоп теперь выводится (ctv2_family_telescope);
   остаётся перевести MasterHAGICoupled на него вместо
   гипотезы.
4. **Асимптотика перколяции.** p_c ≈ 0.5927 бесконечной
   решётки не выводится из конечного ядра.
5. **ψ-монотонность (trigamma > 0).** Отсутствует в Mathlib.
6. **Вынос пакетов.** Flywheel, NeuralComputer — кандидаты в
   отдельные Lake-пакеты; широкие `import Mathlib` в листах.
7. **Namespace-остатки.** Core/Select, RealF3*.
