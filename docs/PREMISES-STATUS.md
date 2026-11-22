# PREMISES-STATUS — честный вывод недоказанного (C595)

Аудит от 2026-11-22. Источники: `scripts/assumptions.lock` (гейт
AssumptionScan, PASS против кода), `scripts/premise_registry.toml`
(типизированный реестр, гейт PremiseRegistry). Строки таблицы —
премисы, которые ЕЩЁ ОТКРЫТЫ (не доказаны в Hagi). Полный бюджет:
106 h_emp-binders по 36 файлам + 11 operational + 11 unprefixed.

## Классификация аудита C595

- **PROVEN-NOW (1)**: `h_emp_var` — разряжен: для S ∈ [0,1] второй
  момент ≤ 1 (S² ≤ 1, Σq = 1), дисперсия ≤ 1/4 по Поповичи.
  Безпосылочная строго более сильная форма доказана:
  `Hagi.Probability.adaptive_success_freedman_adaptive`
  (Freedman.lean, через `popoviciu_var_le`). Legacy-binder в
  `adaptive_success_freedman` оставлен ради стабильности statement
  (потребителей нет); см. `resolved_by` в premise_registry.toml.
- **PARTIAL (2)**: `h_emp_fiber`, `h_emp_dist` — разряжены НА
  КАНОНИЧЕСКОМ identity-сэмплере конечного носителя
  (`Hagi.Discovery.discovery_prob_stationary_identity`,
  PPTCanonical.lean). Для runtime PPT-цепей остаются внешними.
- **STILL-EXTERNAL (остальные)**: эмпирика (замеры), модельные
  регуляризации (fit-законы), физика (Landauer), аппроксимации.
- **DEAD (0)**: scan PASS ⇒ каждый binder lock существует в коде.

## Открытые премисы

| Премис | Класс | Файлы (блокируемые пакеты теорем) | Что нужно для доказательства |
|---|---|---|---|
| h_emp_01 | Empirical | Probability/ConditionalSuccess; Dynamics/GrowthBridge; Research/Legacy/MasterHAGI | внешний base-rate успеха: стат. замер испытаний |
| h_emp_indep | Empirical | те же 3 файла | независимость событий успеха: схема сэмплирования |
| h_emp_meas | Empirical | те же 3 файла | измеримость события: конструкция измеримого носителя данных |
| h_emp_p | Empirical | те же 3 файла | оценка p из частот: внешний датасет |
| h_emp_attsmooth | Model | Pretraining/ProbeError | липшицевость attention: доказать из параметров архитектуры |
| h_emp_cooling | Empirical | Energy/Landauer | физический закон охлаждения (термодинамика) |
| h_emp_credit | Empirical | Energy/Landauer | учёт энергобаланса credit-assignment (замер) |
| h_emp_landauer | Empirical | Energy/Landauer | предел Ландауэра (физическая константа) |
| h_emp_memwrite | Empirical | Energy/Landauer; Research/Legacy/AdvanceWitness | энергия записи (замер устройства) |
| h_emp_finite_time | Model | Energy/Landauer | конкретный горизонт: фиксация параметра T |
| h_emp_res | Empirical | Energy/STEStep | residual статистика straight-through (замер) |
| h_emp_scaling | Approximation | Ensemble/PolicyCompatibility | скейлинг-закон совместимости (fit) |
| h_emp_G | Empirical | Generalization/ModeState; Research/Legacy/CorePremisesDerived, MasterHAGI | измеренная граница прироста |
| h_emp_fit | Empirical | Generalization/ModeState | residual-статистика fit'а модового состояния |
| h_emp_frontier_scaling | Approximation | Growth/GainRenewal | степенной закон фронтера (fit данных) |
| h_emp_pl | Approximation | Growth/Grow | power-law аппроксимация роста |
| h_emp_disp_step | Empirical | Research/SeedOnly | замер дисперсии шага |
| h_emp_cone | Model | Growth/Takeoff; Research/Legacy/ArchitectureTheorem | включение в конус роста из динамики модели |
| h_emp_cone0 | Model | Takeoff; ArchitectureTheorem; Assumptions; MasterHAGITrunc; Nonvacuity; StateTakeoff | начальное состояние в конусе: стартовые условия прогона |
| h_emp_step | Empirical | Takeoff; ArchitectureTheorem; Assumptions; MasterHAGITrunc | измеренный одношаговый закон роста |
| h_emp_dyn | Empirical | ModeState; LinearCone; Takeoff; 5 legacy-файлов | измеренный закон динамики (частично: h_emp_dyn_explicit — proven-обёртка) |
| h_emp_gain_prod | Empirical | Assumptions; MasterHAGITrunc; Nonvacuity; StateTakeoff | произведение приростов (частично: h_emp_gain_geometric — proven) |
| h_emp_C_cap | Model | Assumptions; MasterHAGITrunc; Nonvacuity; StateTakeoff | граница capability (аргумент масштабирования) |
| h_emp_beta | Model | те же 4 legacy-файла | интерполяционный параметр easing |
| h_emp_conc | Model | Research/Legacy/TopLevel | вогнутость целевого функционала модели |
| h_emp_grow | Model | CorePremisesDerived; MasterHAGI; System/GrowthState | карта роста (модельная): вывод из h_emp_dyn-типа законов |
| h_emp_quad | Model | Research/Legacy/RecursiveGrowth | квадратичность локальной аппроксимации |
| h_emp_merge | Mathematical (partial: flat-concat разряжен) | StageCalculus; CorePremisesDerived; MasterHAGI; RecursiveGrowth; GrowthState | алгебра merge-закона; РАЗРЯЖЕНА для two-expert flat-concat (h_emp_merge_of_bridge, Nonvacuity R263); вне его — доказать закон для конкретного merge-оператора |
| h_emp_dist | Model (partial) | StageCalculus; MasterHAGI; RecursiveGrowth; PPT; GrowthState | регулярность распределения; точечно-массная форма уже разряжена (PPTCanonical) |
| h_emp_lip | Model (partial: градиентная модель разряжена) | StageCalculus; MasterHAGI; RecursiveGrowth; TopLevel; SeedOnly; TernaryExact; GrowthState | липшицевость: РАЗРЯЖЕНА на модели κ = sup‖∇E‖ (lip_energy_from_gradient R563 + discharge_premise_h_emp_lip_euclidean C605); внешний — измеренный κ (как rn_lipschitz_region в RMSNormTransfer) |
| h_emp_smooth | Model (partial: L-гладкий градиент разряжен) | 8 файлов (StageCalculus…SafeQPStep) | гладкость: РАЗРЯЖЕНА на модели L-гладкого градиента (joint_emp_smooth_derived R565 — точная форма joint_stage); внешний — измеренный L |
| h_emp_gate | Empirical | Pretraining/SyntheticPretrain | статистика активации гейта (замер probe) |
| h_emp_gap | Empirical | Step/Compound | наблюдаемый suboptimality gap (трейс обучения) |
| h_emp_c | Model | Step/Compound | масштабная константа модели |
| h_emp_decay | Model | Step/Compound | закон убывания модели |
| h_emp_fiber | Empirical (partial) | Research/PPT | измеримость волокон сэмплера; identity-сэмплер разряжен (PPTCanonical); runtime-цепь — внешняя |
| h_emp_second | Empirical | Autonomy/Insight | второй момент (внешний замер) |
| h_emp_noise_bound | Empirical | Step/SafeQP; Unified/AnytimeMartingale | норма шума стохастического оракула (замер) |
| h_emp_noise_indep | Empirical | те же 2 | независимость шума по шагам |
| h_emp_noise_meas | Empirical | те же 2 | измеримость шума |
| h_emp_noise_zero | Empirical | те же 2 | несмещённость оракула (калибровка residual) |

## Operational (execution links, 11)

Не доказуемы внутри формализма по определению — связывают теоремы с
фактическим исполнением (реальный спуск/шаг/сэмпл рантайма):
`hActualDescent, h_descent, h_exec, h_step_descent, hdescent,
hdescent', hexec, hexecb, hsample,
hybrid_stack_transfer_descent(_strict)`. Доказательство = сертификация
конкретного рантайма (execution certificate), не математика.

## Unprefixed эмпирические (per-file, shrink-only)

- MasterHAGI.lean: h_step, h_gain_prod, h_dyn, h_C_cap, hβ — legacy
  контракт мастера (см. docstring MasterHAGI 84–92).
- ModeState.lean: h_C_cap, hβ_eased — ease-контракт модового состояния.

## Куда копать дальше (маршруты разрядки)

1. ~~`h_emp_lip`/`h_emp_smooth`~~ — разряжены C605 на уровне
   моделей (κ = sup‖∇E‖, L-гладкость градиента); следующий
   уровень — явные константы для КОНКРЕТНЫХ архитектур
   (RoPE/нелинейные стеки) по образцу rn_lipschitz_region
   (RMSNormTransfer).
2. ~~`h_emp_merge`~~ — разряжен C605 для two-expert flat-concat
   (Nonvacuity R263 уже давал мост; зафиксирован статус).
   Следующий уровень — merge-закон для блочно-диагональных /
   Hadamard-операторов (см. Nonvacuity:258).
3. Runtime-PPT: инициализация/смешивание цепи → разрядка
   h_emp_fiber/h_emp_dist до уровня canonical.
4. `h_emp_quad`: PSD-мажоризация F (dL ≤ ⟪dW, F dW⟫) — готового
   моста нет, кандидат на отдельный виток.
