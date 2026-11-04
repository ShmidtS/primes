
### Аудит-3 (Tech Debt Management): верификация фактов и Фаза 4.2
- Утверждение «QuadMachine — скаляр f(x)=ax²» — ЛОЖНО: quadE/quadCert/
  quadStepCert работают над k → ℝ (произвольная размерность, Fintype k);
  тернарный квантователь qTern также k-мерный (TernaryExact).
- «MasterHAGI*/GrandSynthesis — мёртвый Gen-1 код, effort-1 удаление» —
  НЕВЕРНО по effort: MasterHAGI потребляется 12 модулями; GrandSynthesis
  несёт реальную takeoff-математику (де-паден в 2dc3a31). Удаление —
  зависимостная хирургия, требует отдельного решения.
- «изолированные острова неравенств не участвуют в цикле роста» — ЧАСТИЧНО
  устранено РАНЕЕ (quant_energy_bridge, PinskerTV-мосты) и в этом проходе:
- Фаза 4.2 ВЫПОЛНЕНА конструктивно: Hagi/Unified/TernaryWitness.lean —
  СОСТАВНОЙ многомерный свидетель, связывающий острова:
  quantOpt_energy_bound: тернарно-квантованный оптимум многомерной
  квадратичной цели имеет энергию ≤ k·s²/8 (выведено из пошаговой
  дисторсии qTern_error_in, НЕ постулировано);
  quant_jump_honest: для любого состояния с энергией выше потолка прыжок
  к квантованному оптимуму — HonestTransition с выведенным дропом
  (riskSpend/budgetSpend = 0: прыжок без ресурсных трат — модельный
  сценарий). Аксиомы: только [propext, Classical.choice, Quot.sound].
- TD-6 (удаление Freeze/линтеров) и TD-1 (удаление Gen-1), TD-2 (429→20
  файлов) — конфликтуют с действующими протоколами (Freeze-дисциплина,
  merge-before-delete, §1.3 запрет массовых переименований); не выполнены
  без явного решения пользователя.

### Аудит-4 (P0-5, P0-2): статус по коду
- P0-5 (многократная продуктивная траектория): УДОВЛЕТВОРЕН РАНЕЕ
  кодом — Examples/QuadLoopWitness.quad_loop_horizon: произвольный
  горизонт n, на КАЖДОМ шаге дроп = ¾·E(w_t) ВЫВЕДЕН из точного
  тождества quadE_half текущего состояния (эффекты state-dependent —
  именно тот тип свидетеля, который требует §5.2 аудита;
  two-step-inconsistensia Nonvacuity относится к СТАЦИОНАРНЫМ
  эффектам, а не к пересчитываемым).
- P0-2 (grad привязан к функции потерь): ДОБАВЛЕНО
  (DescentCoreQuad.quad_eta_identity / quad_eta_descent): для
  квадратичного носителя градиент — ИСТИННЫЙ градиент quadE
  (quadGrad), точное тождество E(w−η∇E) = (1−η)²·E(w), спуск
  выводится ИЗ ОДНОГО диапазона 0 < η < 2 (измеримый выбор шага),
  без h_emp/hcond-посылок на спуск.
- P0-1/3/4 (StageEffects, протокол измерений качества, развязка
  gain/energy/capability) и P1–P3 — открытые крупные блоки;
  планы аудита-4 совместимы с фазами A–D действующего плана.
- Воспроизводимость (§10 аудита-4): подтверждено — lakefile.toml и
  lean-toolchain несут локальные абсолютные пути Windows;
  BUILD_REPROD.md описывает ручную замену; полная портируемость —
  отдельная инфраструктурная задача.

## Аудит #6 (RCDL-синтез, 2026-11-02)

Верификация фактов аудита:
- D1 «чужеродная библиотека Primes/ (2.2k строк)» — ОПРОВЕРГНУТО:
  каталог Primes/ в репозитории отсутствует (ls корня: только
  Hagi/, Challenge/, audit/, scripts/). Аддитивной комбинаторики
  в сборке нет.
- «dual identity уже доказан» — ОПРОВЕРГНУТО: дуального тождества
  RCDL в репо не было; формализовано теперь (RCDL.dual_apply).
- «HonestTransition/certified_loop тавтологичен» — ПОДТВЕРЖДЕНО
  частично: телескоп — честная индукция; не-тавтологичная часть
  (реальный GD-спуск) теперь в ToyTrajectory (honest_step_cert,
  traj_energy_explicit).
- MasterHAGI*/GrandSynthesis deprecated — уже зафиксировано ранее.

Выполнено (цикл 5, коммит ниже):
- Hagi/Learning/RCDL.lean: dual_apply (дуальность слой↔attention),
  expw/weightedSoftmax/gauge_shift (gauge-инвариантность со
  сдвигом значений; посылка ненулевого знаменателя — честная).
Осталось из синтеза: negative-weight gauge-выбор b_t (теорема
существования сдвига с ⟨g, s+b⟩ > 0); FOOF/Mesa-мост;
Hadamard-проекторы Π_m для изоляции доменов (частично есть в
Spectral-модулях).

## Исследовательские циклы 9–13 (2026-11-02, после аудита #6)

- Цикл 9 (FOOF): regCov/foofW + foof_normal_eq (W*C = VXᵀ) +
  foof_step_identity (W*−W₀ = (V−W₀X)XᵀC⁻¹ − λW₀C⁻¹) — мост
  Mesa/FOOF: second-order preconditioning одним шагом.
- Цикл 10 (RegCovPD): regCov_quad (точное тождество vᵀCv =
  ‖Xᵀv‖²+λ‖v‖²), regCov_posDef, regCov_det_unit — посылка
  обратимости FOOF стала теоремой при λ>0.
- Цикл 11 (TernaryPert): cs_dotProduct, frob_submul (‖Ex‖ ≤
  ‖E‖_F‖x‖), ternary_layer_pert (ошибка квантования слоя ≤
  √(mr/4)‖x‖) — критика «нет сквозной ошибки квантования»
  закрыта на уровне слоя.
- Цикл 12 (PertTelescope): outNorm_triangle, pert_comp_pair,
  lip_composition, pert_telescope (‖comp e x − comp p x‖ ≤
  nδLⁿ) — полная сквозная оценка квантованной сети.
- Цикл 13 (FOOFUnique): foof_normal_unique, foofW_unique —
  единственность аналитического оптимума Mesa/FOOF.

Примечание процесса: в черновиках циклов 9–13 несколько раз
проскакивали sorry-заглушки — все заменены до коммита, все
коммиты прошли sorry-гейт (rg=0). Ловушка Mathlib-снапшота:
one_le_pow_of_one_le' ведёт к unbundled-версии (MulLeftMono ℝ не
синтезируется) — 1≤Lⁿ доказывается локальной индукцией.

## TD-07 исправен (цикл 14, 2026-11-02)

scOf больше не сбрасывает риск: riskCost := c.riskSpend,
hRiskNonneg := c.hriskSpend_nn (реальный расход риска в
контракте). tc_step_of_stepcert и tc_consequence
переформулированы честно: итог ослаблён на Σ riskSpend
(раньше «Σ riskCost = 0» — скрытая потеря информации о риске).

## TD-04 верифицирован и закрыт (цикл 17, 2026-11-02)

Проверка аудита: «6 вариаций одного Water-Filling» —
ПРЕУВЕЛИЧЕНО. Реальный дубликат один: totalErrorFin
(WaterFilling) vs totalError (BitAlloc) — оба Σ c/2^b;
WaterFilling уже импортирует BitAlloc и делегирует (мост
доказывался inline rfl). Добавлен публичный мост
totalErrorFin_eq_totalError как API (merge-before-delete).
Остальные модули — РАЗНЫЕ модели, не дубликаты:
WaterFillingMoE (genMean/effectiveCapacity), RankBudget
(экспоненциальный ранг-остаток), BatchCap (SFO-стоимость),
KVWater (KV-остаток с каппой).
