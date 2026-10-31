# HAGI v3 — критический анализ (код-only) и план рефакторинга

Срез: 380 .lean-файлов, 32 подсистемы, ~3376 деклараций
(2680+ theorems/lemmas по Freeze 3444), commit 418cfae.
Анализ ПО КОДУ (сигнатуры/тела), докстринги игнорируются.

## Часть 1. Что реально доказано (три слоя)

### Слой A — безусловная математика (ядро, честное)
- Теория информации: KL ≥ 0 (Jensen/xlogx), log-sum-ineq,
  Pinsker (277-строчная честная), TV, Fannes (4 варианта —
  НЕ дубликаты: разные носители/гипотезы), label-smoothing
  энтропийная монотонность.
- Вероятности: Hoeffding/Azuma/Freedman (1- и 2-сторонний,
  PMF-конкретика), Ville/e-process/anytime (т238 Catoni),
  temperature law Var=σ²/B, SNR-порог (t240).
- Линейная алгебра: SVD прямоугольный (2599 строк),
  Courant–Fischer, Weyl, Eckart–Young–Frobenius,
  ортогональные проекции/остатки.
- Оптимизация: SafeQP существование/единственность/η_max;
  NewtonPolar квадратичная сходимость; Muon-NS скалярная
  модель (t231); mirror descent floor/attainment/вариационный
  спуск (t227); Robbins–Monro; Lookahead=EMA тождество (t238).
- Ансамбли: LSE-выпуклость, twoGap cosh-форма, gap>0 ⟺
  различие, logit-PSV (t224), ModelSoup Jensen (t232).

### Слой B — условные контракты шага (честно-условные)
- StepContract моноид + trajectory_convergence (t230) —
  ЕДИНЫЙ телескоп; lyapunov_termination_fin = частный случай
  (мост t233).
- CertifiedTransition (exec/progress/safety/resources) + V2
  с активным riskLim (t241); MeasurementCert (полоса
  honest-прироста); CertifiedTrajectory 3-уровневый синтез (t230).
- advanceQ: реальное квантование params'=q(params−ηd) (t242,
  Test 3 ✓); compressQ-контракт Δ/2 поточечно.

### Слой C — фасады/условности (честно, но это композиции)
- MasterHAGI* / GrandSynthesis — телескопирование посылок
  (ΔΦ ≤ −D+λR+νε); Cone/Perron-takeoff: рекуррентные условия
  ⟹ экспоненциальная нижняя граница; saturation (t234) —
  парная верхняя граница.
- Доказанные ВНУТРИ проекта контрпримеры-регрессия:
  full_cycle_two_step_inconsistent (замороженные эффекты),
  cone_premises_force_exact (обязательное насыщение),
  scalar_hides_deficit (векторная честность).

## Часть 2. Дефекты (подтверждено кодом)
1. Замороженные effects в grow/merge/joint/compress —
   ДВОЙНОЙ цикл невозможен (собственные теоремы-свидетели).
   Канон уже есть: StageSemantics.advance (effects := u.eff).
2. Два канала capability (C : ℕ→ℝ vs state.capability) —
   MasterHAGI_linked закрывает, но MasterHAGI без link живёт.
3. GrandSynthesis смешивает capability-рост с risk-бюджетом.
4. 18 certificate-подобных структур → 3 канона: StepContract
   (числа), CertifiedTransitionV2 (исполнение+лимит),
   MeasurementCert (полоса) — остальное делегировать.
5. Дубли-семейства (файлы): geometric(34), SafeQP(38 —
   8 модулей-вариантов), takeoff(39 — частично string-matches),
   Fannes(4 осознанных), termination(6 → StepContract-мост ✓).
6. Pi-тип (Fin n → ℝ) без InnerProductSpace — ReferenceMachine
   не стыкуется с generic X напрямую (t242-урок).

## Часть 3. План рефакторинга HAGI v3 (7 слоёв, сверху-вниз)

L1 MathCore (Foundations+Prelude): Recurrence/GeomSum/
  NormIneq/Ortho — один канон на семейство.
L2 Information (Prelude.Info+Pinsker+Fannes+Distill+LabelSmoothing):
  KL/TV/H/Pinsker/Fannes — по 1 канону, матричная энтропия
  отдельно.
L3 Probability (Hoeffding/Azuma/Freedman*/Ville/anytime/
  NoiseTemperature/BatchSNR): концентрация + anytime.
L4 Optimization (SafeQP-4 уровня: геометрия→проекция→η→
  стохастика; MirrorDescent-ядро: Hedge/MWU = instances;
  NewtonPolar/MuonNS/Momentum/Lookahead/RobbinsMonro/AdamW).
L5 Compression (SVD/EckartYoung/Quantizer gridQ/WaterFilling/
  BatchCap): биты↔ранг↔ошибка.
L6 ExecutionSemantics (GrowthState+StageSemantics/advance+
  advanceQ+ReferenceMachine+MachineBridge): ОДИН переход
  S_{t+1}=advanceQ(S_t,u_t,q_t), u_t.measure(S_t).
L7 CertifiedCycle (StepContract+CertifiedTransitionV2+
  MeasurementCert+CertifiedTrajectory+PerronCone/saturation)
  → MasterTheorem: безопасность+бюджет+прогресс+рост с
  насыщением на одной траектории.

Правило зависимостей: только вниз; Unified — последний слой.

## Часть 4. Синтез с источниками (Qwenputer-GDN, H-Net bytes)

- Qwenputer/GDN (источник №62 GDNRAM ✓): байтовая
  вычислительная память поверх LLM: ram_read_after_write/
  write_idem уже формализованы. В v3 — L6-исполнение:
  GrowthState.memory ↔ GDN-операции, сертификат — V2.
- Cartesia H-Net bytes (НОВОЕ, кандидат №77): байтовый
  уровень = квантование входа: пэтч p байтов ↔ один токен —
  cost-identity: L_byte = L_tok·p, сжатие последовательности
  p×; сплайн-токенизатор ~ гладкая решётка (связь с gridQ:
  ошибка квантования входа ≤ Δ/2 переносится на пэтч-границы).
  Формализуемый уровень 1: byte_patch_cost (последовательная
  компрессия), patch_boundary_error (gridQ-реюз).
- Оптимальный алгоритм (объединение всего):
  цикл = measure(S) → hypothesis-competition (MirrorDescent-
  ядро, anytime-валидно) → SafeQP-шаг (η_max, V2-лимит) →
  advanceQ (реальное квантование) → MeasurementCert (полоса) →
  StepContract-накопление → cone/saturation-мониторинг →
  accept/rollback (LiveDelta). Все компоненты уже формализованы
  по отдельности; v3 = единая траектория через них.

## Часть 5. Порядок работ (критерии готовности)
P0 (done): V2-riskLim ✓, advanceQ ✓, StepContract ✓, saturation ✓.
P1: MasterHAGI _v2 на advanceQ+V2+MeasurementCert; перенос
    MachineBridge на advanceQ;删除 MasterHAGI-без-link (deprecated).
P2: консолидация L2/L4/L5 по карте §3 (export-делегаты,
    DUPLINT-шейкер).
P3: byte-patch (№77) + GDN-связка памяти; MasterTheorem v3.
Контрольные тесты: 2/3-step productive witness (advanceQ),
budget-exactness, cone-from-measurements.
