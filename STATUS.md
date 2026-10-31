# STATUS — состояние формализации HAGI

## Корпус

- 271 Lean-модулей в `Hagi/`; 3376 деклараций (Freeze);
  2148 theorem/lemma; 0 sorry; 0 кастомных аксиом
  (все теоремы: [propext, Classical.choice, Quot.sound]).
- CI: LINT, MathlibPin, DupLint, NsLint, DocLint, LayerLint,
  Freeze, AssumptionScan (реестр 117 `h_emp_*`-посылок и
  17 инфо-примитивов), StatusLint — все PASS.

---

## Доказанные результаты (главные формулы)

### L1. Информация и телескопы

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
- **Аудит v6, шаг 1 (DerivAlong → CorePremises)**:
  Hagi/Unified/CorePremisesDerived.lean — конъюнкты 8
  (h_emp_smooth) и 13 (h_emp_lip) CorePremises стали
  ТЕОРЕМАМИ при операциональных определениях (jointEnergy :=
  E(params−η•stepDir) с L-гладким градиентом; compressEnergy
  := E(gridQ Δ x) с κ-ограниченным градиентом, фактическая
  ошибка сетки, s=1); core_premises_operational_scalar —
  сведение CorePremises к структурным посылкам;
  MasterHAGICoreOperational — капстоун: одностадийный
  мастер-результат из свойств РЕАЛЬНОЙ функции потерь.
- **Дедуп-аудит ядер §6 завершён (Fannes×5, Hoeffding,
  Gibbs)**: гипотеза о дубликатах НЕ подтверждается —
  консолидация выполнена ранее (v4–v6): Fannes — 4 разных
  математических слоя + фасад-реестр (Unified/Fannes);
  Hoeffding — иерархия Foundations(MGF) → Ensemble(chord,
  импортирует Foundations) → Probability(Azuma/Freedman
  поверх); Gibbs — Probability-цепочка зависимых модулей,
  Energy-модули не пересекаются. STMDUP = 0 групп —
  механическое подтверждение. Смысловых дублей не найдено.
- **Дедуп-аудит Pinsker-семейства (v7 §6)**: исследована
  тройка Information/Pinsker (pinsker4_fin) ×
  Unified/Pinsker (pinsker4_via_canon) ×
  Probability/PinskerTV (pinsker_sqrt_kl). Установлено:
  дедуп УЖЕ выполнен мостом via_canon (fin-форма выводится
  из TV-канона); прямое делегирование pinsker4_fin →
  канон НЕВОЗМОЖНО по layer-контракту (Information layer 1
  не может импортировать Probability layer 2 — LAYERLINT
  блокирует). Канон один (pinsker_sqrt_kl), следствие одно
  (via_canon), fin — оригинал уровня 1. Закрыто без
  изменения кода.
- **Дифференциальные тесты машины (аудит v7, этап 6,
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
- **Аудит v9 P3 (фасады), такт №194**: финальная волна —
  CoreAlgebra/MatrixLib→AlgebraMatrixCore; GrowthExt/
  EnsembleTheory/DualCeiling→GrowthEnsembleCore;
  ModelPretrain/OptStepExt/Robustness→PretrainOptRobustCore.
  ИТОГ P3: 20 одно-теоремных фасадов → 7 тематических модулей;
  устранено скрытое задвоение namespace (поймано TrivialLint,
  имена деклараций восстановлены, Freeze 3265 стабилен).
- **Аудит v9 P3 (фасады), такт №193**: слияние
  Budget/BudgetExt → BudgetCore; ArchitectureCore/
  AutonomyCore/MiscCore → CoreFacades (12 одно-теоремных
  фасадов свёрнуто за три такта; Freeze 3265 стабилен).
- **Аудит v9 P3 (фасады), такт №192**: слияние четырёх
  одно-теоремных фасадов Pinsker/ProbInfo/DataCentric/
  DataEnergy → Unified/InfoDataCore (Freeze 3265 стабилен).
- **Аудит v9 P3 (фасады), такт №191**: слияние трёх
  одно-теоремных фасадов DynamicsLaws/GrowthLaws/
  GlobalDynamics → Unified/DynamicsGrowthCore (импортеры
  только Hagi.lean; декларации и Freeze 3265 неизменны).
- **Аудит v9 P1 (vacuity-gate), такт №190**: wTraj2 —
  двухцикловый витнес Gen-2 (T = 2, минимальный горизонт
  гейта аудита); witness_takeoff_realized_T2 — рост
  (1+1)²·1 = 4 СТРОГО реализован семантикой Gen-2 на T = 2,
  где старый Gen-1 (MasterHAGI_linked) уже противоречив.
  Пара {T=2, T=3} закрывает гейт P1 для Gen-2-мастера.
- **Аудит v9 — ответ тактом №189 (P2/P4: разрыв случайных
  связей)**: sq_decomp-семейство перенесено в нижний слой
  Foundations/SumIdentities (sum_sub_mean_zero, sq_decomp —
  канонический дом König–Huygens-тождеств); LayerNorm и
  SwitchMoE больше НЕ зависят от RL-модуля GRPO (аудит v9
  находка 9); GRPO делегирует канону — API/Freeze
  неизменны.
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
- **Аудит v11 P1 (унификация эффектов), такт №204**:
  ofStageEffects — типизированная проекция плоского
  StageEffects в MeasuredEffects (risk/cost/gain разведены);
  ofStageEffects_roundtrip (все 9 полей без искажения, rfl),
  totalCost/totalRisk_ofStageEffects (бухгалтерия согласована).
  LESSONS: перенос строки внутри {...} structure-instance в
  def-теле валит парсер — использовать ⟨...⟩-конструктор.
- **Аудит v11 §3.2 (progress-разрыв), такт №203**:
  LinkedHAGIInvariantProgress — усиленный связанный инвариант:
  per-step PROGRESS-поля CertifiedTransition (0 < verify-
  decrease) ОБЯЗАТЕЛЬНЫ и переносятся в финальный сертификат
  (кумулятивное снижение ≤ E₀ − E_T);
  certified_family_linked_progress — мост: progress-поля
  потребляются явно (закрыт разрыв «progress не используется
  итоговым инвариантом»).
- **Аудит v10 §3.5, такт №202**: честные имена рисков —
  riskGrow/riskMerge/riskJoint (новые канонические defs);
  costGrow/costMerge/costJoint помечены @[deprecated] с
  алиасами (риск ≠ FLOPs; API сохранён, Freeze стабилен).
- **Аудит v10 P0-2/P0-3, такт №201**: Model/MeasuredEffects —
  ТИПИЗИРОВАННЫЕ величины (StageRisk ≠ ComputeCost ≠
  StageGain — развязка риска и FLOPs) + схема v10
  «(S, batch, измеритель) → (S', измеренные эффекты)»:
  trainStep_measured (эффекты = выход измерителя, rfl — НЕТ
  телепортирования), trainStep_budget_balance (баланс по
  измеренной стоимости), trainStep_capability_band (полоса
  роста из измерения, реюз GrowthBand). growth_band перенесён
  в Foundations/GrowthBand (канонический нижний слой;
  Growth реэкспортит, слои соблюдены).
- **Аудит v10 P0 (полоса роста), такт №200**: growth_band_step
  + growth_band_iter — ДВУХСТОРОННЯЯ полоса (1+αmin)^T·C0 ≤
  C_T ≤ (1+αmax)^T·C0 с НЕЗАВИСИМЫМИ коэффициентами;
  устраняет вынужденное ТОЧНОЕ насыщение takeoff_edge_forced
  (сохранён как частный случай αmin = αmax, по рекомендации
  аудита).
- **СИНТЕЗ cost-семейства (такт №199)**:
  Unified/CostComposition — гибрид MoD(№55)×SWA(№56)×глубина:
  hybrid_cost_lt (L·k·(2w+1) < L·n² — механизмы экономии
  складываются в одну цепочку), hybrid_ratio_le (относительная
  стоимость ≤ (k/n)·((2w+1)/n) — произведение факторов
  экономии).
- **РЕТРО такт №213**: LESSONS.md +11 записей (карантин
  №59-бином, Nat.mul-направления, structure-instance
  переносы, namespace-удвоение при merge, DUPLINT-делегаты,
  perceiver-ловушка worst-case, sum_mul/mul_sum стрелки,
  min-в-omega, updateRow-семейство).
- **Сквозной пример + КВАНТОВАНИЕ, такт №223**:
  qQuant_err_bound — потеря функции потерь от
  квантования постшаговой точки ≤ (Δ/2)(2R+Δ/2) при
  |x'−a| ≤ R (gridQ_error + разность квадратов): цепочка
  «биты → реальное квантование → ошибка параметров →
  ошибка loss» замкнута ВЫЧИСЛЕНИЕМ на сквозном примере
  (аудит v13 §6.4).
- **Аудит v13 P4 (сквозной пример), такт №222**:
  Examples/QuadraticEndToEnd — первый END-TO-END обучающий
  шаг: F(x)=(x−a)², qGrad (производная ВЫЧИСЛЕНА),
  qStep_loss_exact (постшаговый loss = (1−2η)²(x−a)²
  В ТОЧНОСТИ), qStep_descent (строгое убывание при η∈(0,1),
  x≠a — ноль эмпирических гипотез), qIter_loss (t шагов =
  геометрическое убывание (1−2η)^{2t} — точная
  многошаговость).
- **Аудит v13 P0 (вакуумность core_premises), такт №221**:
  ПОДТВЕРЖДЕНО противоречие hjointE (E(params) ≤
  jointEnergy = E(params−ηd)) со спуском — вынуждает d=0.
  Исправление: core_premises_operational_scalar_v2 +
  MasterHAGICoreOperational_v2 — ПОСТШАГОВОЕ квантование
  (gridQ от x' = params − η·d), hjointE УДАЛЁН (заменён
  rfl-истинным неравенством в конъюнкте 13). Старые версии
  сохранены (superseded, Freeze-совместимость).
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
- **Аудит v12 (riskLim), такт №209**:
  certifiedTransition_risk_respect — параметр riskLim
  CertifiedTransition РЕАЛЬНО ограничивает прирост
  защищённого риска (мост safety+линейность; закрыто
  замечание «riskLim объявлен, но не используется»).
- **SourceMixture №58 уровень 2 (MaxRL-ядро, такт №208)**:
  successDist_norm — распределение успешных ответов
  π⁺(y)=π(y)·r(y)/p НОРМИРОВАНО (RL-цель корректна как
  likelihood-обучение на успешных ответах — мост
  генерация→верификация→MLE), successDist_nonneg.
  №59-нормировка (бином-индукция) — 5 подходов, карантин
  LESSONS (pin-Mathlib не экспортирует binomial theorem;
  синтакс-формы показателей хрупки для rw).
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
- **Аудит v8 — ответ тактом №146 (P1, фасады Unified)**:
  демонтированы 5 пустых реэкспортеров (Unified/Concentration,
  Fannes, GrowthTheory, Master, SafeStep — 0 деклараций, 0
  внешних импортёров). Статус по P0 аудита: Gen-2 advance(S,u)
  (StageSemantics + LinkedWitness T=3 + ReferenceMachine +
  MachineBridge) уже основная операционная семантика; Gen-1
  CorePremises сохранён только как историческая модель с
  регрессионным UNSAT-тестом (Examples/Nonvacuity). Остатки
  аудита v8: карантин Gen-1-цепочки из Unified, дедуп
  hagiPotential/maxSingularValue, этап 7 (абляции).
- **RoPE, уровень 1 (источник №24: Su et al., RoFormer,
  arXiv 2104.09864)**: Hagi/Model/RoPE.lean — rot
  (вращение позиции (e^{iθ})^k), rot_normSq_one (единичность,
  cos²+sin²), rope_normSq_preserved (ИЗОМЕТРИЧНОСТЬ:
  вращение сохраняет normSq — фаза меняется, модуль нет —
  ядро корректности позиционного кодирования).
- **RoPE-задел + μP-контраст-сводка (такт 143)**:
  muP_bound_le_sp_bound (μP-граница ≤ SP-границы при n ≥ 1
  — формальное сопоставление переносимого и непереносимого
  скейлинга). RoPE (№24, Su 2104.09864) — разведка API
  зафиксирована в LESSONS (Complex.conj/abs_exp отсутствуют
  в пин-версии Mathlib; star доступен; формулировка
  shift-инвариантности без вычитания выбрана) — отложено до
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
- **Мост машина → семантика (аудит v7, этап 4)**:
  Hagi/Model/MachineBridge.lean — machineStageInput (StageInput,
  СОБРАННЫЙ из машинных измерений: growEnergy = E(w),
  jointEnergy = E(w−η∇E), compressEnergy = E(Q(w−η∇E)),
  quantErr — вычисленный; L=1 — фактическая кривизна),
  machine_advance_certified: при S.energy = E(w) и ledger-факте
  канонический advance_energy_drop сертифицирует переход —
  измерения имеют происхождение (веса), сертификат —
  следствие, а не постулат.
- **Эталонный исполнитель цикла обучения (аудит v7 §5 +
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
- **Аудит v6, Concrete-слой (§3, старт)**:
  Hagi/Examples/QuadraticConcrete.lean — квадратичная
  функция потерь E(x)=(x−a)²/2: производная (quad_hasDeriv),
  значение fderiv (quad_fderiv_apply), L-гладкость L=1
  (quad_smooth), κ-граница R+|a| на [−R,R]
  (quad_kappa_bound), непрерывность вдоль сегмента
  (quad_gcont) — ВСЕ операциональные премисы шага 1
  проверяются теоремами для реальной функции потерь;
  quadState + quad_conj8/quad_conj13 — ПОЛНЫЙ Concrete-витнес:
  конъюнкты 8/13 CorePremises — теоремы на реальном
  состоянии (E=(x−a)²/2, stepDir=0, сетка Δ=1);
  quad_core_premises — ПОЛНЫЙ витнес: ВСЕ 16 конъюнктов
  CorePremises — теоремы на квадратичной функции потерь
  (quadGen/quadGen' — точная композиция стадий);
  Concrete-линия аудита v6 §3 завершена.
- **Аудит v6, L3 (единый Certificate, старт)**:
  certificate_of_transition — мост цепочки уточнений:
  CertifiedTransition (ядро) детерминирует все наблюдаемые
  поля Certificate-проекции пост-состояния (спад > 0,
  риск-трата ≤ Σ рисков стадий, точный бюджетный расход);
  13 сертификат-структур проекта сводятся к цепочке с
  CertifiedTransition в вершине; transition_safe_selection —
  звено 2: переход кормит алгоритм отбора bestDecrease
  (safe_selection_productive) — Certified Growth Loop.
- **Аудит v6, критерий готовности «нет двух теорем с
  одинаковым хешем утверждения» — ВЫПОЛНЕН**: разбор
  declarations.lock по type-hash даёт 0 групп дубликатов
  (буквальные statement-дубликаты вычищены прошлыми
  дедуп-раундами); ворота STMDUP в CI закрепляют.
- **Аудит v6, дедуп L1 (порядок работ №3, старт)**:
  hoeffding_lemma_prefix (Azuma) переписан как ВЫВОД из
  канона mgf_hoeffding_ab (Foundations.Hoeffding) — хордовое
  доказательство удалено, лемма Хёффдинга в проекте теперь
  одна (statement неизменен, Freeze стабилен).
- **Аудит v6, шаг 3 (закрепление окружения)**:
  mathlib-rev.txt теперь пинит и toolchain-commit
  (eb6cafb…), ворота MATHLIBPIN в CI сверяют rev Mathlib и
  commit lean-тулчейна — тихий дрейф окружения ловится.
- **Аудит v6, шаг 2 (Comparator-challenge)**:
  Hagi/Challenge/MasterChallenge.lean — честная формулировка
  MasterHAGICore закреплена: заключение прописано полностью
  (смена смысла ломает сборку), посылка CorePremises
  закреплена pinned-типом; Challenge/challenges.json +
  scripts/ChallengeCheck.py — ворота CI (CHALLENGE: PASS):
  допустимые аксиомы ровно propext/Classical.choice/
  Quot.sound, пиннинг типов посылок.
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
- **Аудит v5 п.6 (гигиена): frob_minkowski'** — ручное
  доказательство Минковского-Фробениуса заменено делегацией
  Mathlib (norm_add_le в EuclideanSpace, prod-перестановка
  сумм); Коши–Шварц ℂ уже делегирует norm_inner_le_norm.
- **Аудит v5 п.5, дедупликация TV/Fannes-языка**:
  tvHalf_eq_tvDef — дублированное определение полной
  вариации (Information) связано с каноном Prelude.tvDef
  (rfl); Fannes-семейство теперь на общем TV-языке.
- **Аудит v5 п.5, дедупликация Хёффдинга**:
  hoeffding_fin_via_mgf — Ensemble-форма выведена из
  Foundations-канона mgf_hoeffding_ab (масштабирование h=t·d,
  центрирование, exp-монотонность); три копии связаны.
- **Аудит v5 шаг 4 (ConeSystem), ядро**:
  Foundations/ConeCorridor — cone_exact_exponential:
  при конусных посылках + cap-окне capability зажат ТОЧНОЙ
  экспонентой (1+α)^T·C0 ≤ C T ≤ (1+α)^T·C0 (нижняя — конус,
  верхняя — индукция по cap); коридор вырождается в точную
  двустороннюю оценку.
- **Аудит v5 п.5, дедупликация Пинскера**:
  pinsker4_via_canon — f-форма (pinsker4_fin, Information)
  выведена из канонной TV-формы (pinsker_sqrt_kl,
  Probability): разность ожиданий ≤ TV, TV ≤ √KL; копии
  связаны единым примитивом.
- **Аудит v5 п.5, дедупликация EW**: ewNorm_as_mirror —
  EW-процесс HedgeSurvivor выражен через mirrorStep
  (MirrorDescent): ewNorm = mirrorStep от равномерного ρ₀ с
  кумулятивными потерями и T = 1/η; четыре копии
  экспоненциальных весов сведены к одному примитиву.
- **Аудит v5, склейка (b) — ядро (grow)**:
  Unified/LearningKernel — мини-LearningProblem (ландауэровская
  граница C ≤ E + энергобаланс пары состояний) +
  grow_premise_derived: grow-посылка CorePremises ВЫВЕДЕНА из
  ландауэровского принципа (допущение → теорема, как DerivAlong
  для joint/compress); merge_premise_derived +
  merge_slack_feasible — merge-посылка как каскадный
  остаток (slack ≥ 0, материально обеспеченный энергией
  post-merge). Склейка (b) полностью закрыта.
- **Аудит v5, склейка (c) закрыта**: high_prob_conclusion —
  перенос вывода с high-probability события: если на Good
  (P ≥ 1−δ из anytime-машины δ_t = δ₀ρᵗ) детерминированная
  цепочка MasterHAGI даёт Takeoff, то P(Takeoff) ≥ 1−δ —
  скелет стохастического MasterHAGI. Freeze 3000.
- **Аудит v5, склейка (g) закрыта**: Unified/LinkedWitness —
  wTraj_certified_family + linkedHAGI_witness: НЕТРИВИАЛЬНЫЙ
  витнес LinkedHAGIInvariant на T=3 с ненулевыми состояниями
  (capability 1→8, budget 100→94, alpha=1), построенный через
  certified_family_linked на реальных exec-переходах.
- **Аудит v5, склейка (e) закрыта**: Unified/QuantizedCone —
  quantized_net_gain + quantized_cone_gain: конусное условие
  γ·k·C ≤ G сохраняется на квантованном шаге при
  margin-условии (штраф ≤ γ·(D − k·C)); квантизация внутри
  инварианта.
- **Аудит v5, склейка (f) закрыта**: usableFrontier_renewal —
  динамика фронтира как измеримый контракт пополнения данных
  (сохранение доли ρ + приём свежей массы r t; ξ-член =
  дефицит свежих данных); алиас dataField получил
  операционную семантику.
- **Аудит v5, склейка (d) закрыта**: stages_cone_gain —
  конусная отдача γ = β⁴·κ ВЫВЕДЕНА из стадийных конверсий
  (disagreement_chain × hcert × hdiv): гипотеза hgain конуса
  перестаёт быть независимым допущением.
- **Аудит v5, склейка (a) закрыта**: HedgeSurvivor.lean —
  EW-процесс (ewWeight/ewPot/ewNorm) построен; ewPot_upper
  (hedge_step + 1+u ≤ exp u, индукция), ewPot_lower (луч);
  hsurv_derived — посылка выживания router_regret_bound
  ВЫВЕДЕНА, не гипотеза; ew_regret — полный regret
  A − L* ≤ ln K/η + ηT/2 склеен из компонент.
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
- **CertifiedTransition (аудит v4 §5.4 реализован)**
  (`Hagi/Model/CertifiedTransition.lean`): зависимый
  сертификат перехода — exec (S' = advance S u), progress
  (verify-спуск > 0), safety (риск-лимит), resources (точный
  бюджетный ledger); конструктор
  certifiedTransition_of_advance из операциональных условий.
- **Аудит-v4 §3.3: единая семантика перехода
  (классификация)**: advance — канон; compose эквивалентен по
  всем полям (advance_decompose, rfl); CycleCertificate —
  сертификатный контракт; UnifiedStep — специализированная
  реализация (QMD), не дубликат. Все четыре описания
  разведены по ролям.
- **Аудит-v4 §3.1: прозрачность GrandSynthesis**: конъюнкты
  маркированы — takeoff ВЫВЕДЕН из конусной динамики;
  риск/бюджет/качество ПЕРЕДАНЫ как измеряемые посылки
  (источник — стадия сертификации), выведена лишь
  неповышаемость бюджета.
- **Аудит-v4 §3.2: связанный инвариант**
  (`LinkedHAGIInvariant`): CoupledHAGIInvariant + требование
  S(t+1) = advance (S t) (u t) — состояния получены реальными
  переходами; мост LinkedHAGIInvariant_to_coupled.
- **Аудит-v4 §3.4: полнозвучный отбор**
  (`StepFeasible`, `bestFeasibleDecrease`,
  `safe_feasible_selection_productive`): выбор максимума
  decrease среди кандидатов, удовлетворяющих лимитам риска И
  бюджета — отбор уважает все три ограничения (спуск/риск/
  стоимость), а не только спуск.
- **Аудит-v4 §3.8-2: точная-экспонента-артефакт задокументирован**
  (sustained_takeoff_trunc): при одном alpha в конусе и cap
  поылки принуждают C(t+1)=(1+α)C t; путь без потолка —
  trunc_premises_takeoff (нижняя граница без C_cap); полная
  миграция на alpha_min/alpha_cap — задокументированный шаг.
- **Аудит-v4 §3.5: Fannes-фасад без псевдоинтерфейса**:
  `FannesLayers := True` удалён; фасад несёт явный реэкспорт
  канонической entropy_lipschitz_smooth + реестр слоёв.
- **Аудит-v4 §3.9: KL-контракт допустимости**
  (`Hagi.Prelude.KLSupported`): вероятностные векторы +
  строгая положительность p (носитель q ≪ p); на допустимых
  входах klDef = математическая KL; KLSupported_pos,
  klDef_terms_finite — явная область корректности klDef
  (ENNReal-семантика +∞ — отдельный будущий слой).
- **Аудит-v4 §3.8: cone_growth_window исправлена** — теперь
  НАСТОЯЩЕЕ окно: (1+α_min)C t ≤ C(t+1) ≤ (1+α_cap)C t;
  добавлена посылка h_upper (G ≤ α_cap·C); α_cap/hsep
  реально участвуют; нижняя из конуса, верхняя из cap.
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
- **Разводка CycleCertificate×2** (аудит v3 §5): System-версия
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
  каждом CI-прогоне (аудит v2 §7/P0).
- **Взлёт свидетеля** (`wTraj_takeoff`): gate alpha·C ≤ gain
  (α=1, gain=C_t: 1,2,4) на каждом шаге ⟹ экспоненциальный
  рост C_0·2^t ≤ C_t — связка Trajectory с cone/takeoff.
- **Инварианты продуктивной траектории**
  (`wTraj_budget_risk_invariants`): бюджет = 100−2t,
  неотрицателен; риск = 0 на всём горизонте T=3 — сертификаты
  бюджета и риска для каждого перехода (аудит §9).
- **Многошаговый продуктивный witness** (`wTraj_productive`):
  на канонической семантике Trajectory существует траектория
  T=3, каждый шаг строго продуктивен (gain>0, энергия −3,
  capability растёт), состояния — только через advance
  (аудит §4, регрессионная защита).
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
  зарегистрирован в Hagi.lean (аудит 2026-10-24).
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

## Открытые проблемы

1. **Миграция капстоунов на StageSemantics.** Ростовое ядро
   (growSeq) уже на state-dependent эффектах; MasterHAGI и
   ~23 потребителя старой модели GrowthState с копируемым
   эффекты ещё не переведены на Trajectory-семантику.
   Свидетель T ≥ 3 под FULL-контрактом старой модели
   невозможен (obstruction формализован).
2. **Асимптотика перколяции (Layer 4).** p_c ≈ 0.5927
   бесконечной решётки, форма θ, мост «перколяция →
   takeoff» — не выводятся из конечного алгебраического
   ядра; нужна новая содержательная гипотеза.
3. **ψ-монотонность (trigamma > 0).** Отсутствует в
   Mathlib; построение (гармоническая форма + ряд)
   открыто; зум пика до (7.2, 7.3).
4. **Воспроизводимая сборка.** Локальный путь Mathlib в
   lakefile и отсутствие elan блокируют проверку «чистым
   клоном» на другой машине.
5. **Lean↔Runtime property-тесты.** Требуют torch-рантайма
   E:\HAGI_v2.
6. **Вынос пакетов.** Flywheel → отдельный Lake-пакет
   (кандидат в upstream Mathlib); Primes — отдельный
   репозиторий.
7. **Остатки namespace-миграции.** Core/Select, RealF3*
   (вложенный ns); сокращение широких `import Mathlib`.
