# Аналитическое закрытие `scripts/assumptions.lock`

Статус: аудит всех 45 файлов, исследовательский цикл 45.
Критерий: «закрыто» означает только Lean-доказательство,
не переименование binder, запись в record или вывод premise
из равносильного premise. Общая условная теорема и
аналитический инстанс различаются.

## Уже выведено аналитически существующими теоремами

| Класс | Закрытие Lean |
| --- | --- |
| `smooth` | `smooth_from_lipschitz_gradient`, `joint_emp_smooth_derived`, `core_premises_joint_operational`, `conj8_h_emp_smooth_derived`; scalar logit: `logitCE_descent_lemma`, `joint_stage_logitCE`. |
| `lip` | `lip_energy_from_gradient`, `lip_energy_quantization`, `compress_energy_bridge`, `core_premises_compress_operational`, `conj13_h_emp_lip_derived`; vector: `gridQ_energy_bound`. |
| `dist` | `gridQ_error`, `gridQVec_error`, `qTern_error_in`, `witness_quantErr_bounded`, `core_premises_operational_scalar_v2`. |
| `grow` | `growEnergy_derived`, `grow_premise_derived`, `grow_gain_from_mirror`, `core_premises_grow_operational`. |
| `merge` | `merge_energy_bridge`, `core_premises_merge_operational`, `h_emp_merge_of_bridge`, `merge_premise_derived`. |
| STE residual | `ste_residual_of_tern`. |
| PL quadratic | `pl_stop_certificate_quadratic` (цикл 45, точная модель `E(w)=μ(w−a)²/2`). |
| Perron named results | `h_emp_dyn_explicit`, `h_emp_dyn_linear_growth`, `h_emp_gain_geometric`, `h_emp_takeoff_exponential`, `h_emp_merge_of_bridge` — это уже доказанные декларации, не premise binders. |
| Canonical primitives | `lse/softmaxP`, `entropyProduction`, `entropy/tvHalf`, `entryCount`, `entDef/klDef/tvDef`, `softmaxW` — определения с canon-мостами, а не измеряемые недоказанные теоремы. |

## Все 45 файлов и их настоящая граница

| Файл | Аналитический статус |
| --- | --- |
| Autonomy/Insight | Условная кривизна `h_emp_second`; требуется definite energy/Hessian model, общего вывода нет. |
| Discovery/PPT | `MeasuredSet`/stationary distribution are sampler semantics; доказательство конечной суммы выведено, distribution/meas остаются исходными данными. |
| Energy/Landauer | Physical dissipation/memory/write/credit/cooling premises are trust boundaries, not analytic statements. |
| Energy/STEStep | Закрыто каноническим `ste_residual_of_tern`; общий `ste_step_residual` остаётся условной треугольной леммой. |
| Ensemble/PolicyCompatibility | Закрывается только при definitional `Dpolicy=5Dbase`; произвольное scaling equality не выводится. |
| Examples/EdgeTests | `h_emp_takeoff_exponential` уже доказан и применяется, не premise. |
| Examples/Nonvacuity | Merge и quant distortion выведены; idle ledger witnesses не являются физическим выводом. |
| Foundations/PerronCone | Четыре h_emp-имени уже доказаны; остальные `h_emp_dyn` — модельная динамика. |
| Foundations/StageCalculus | Условные арифметические wrappers; аналитические модели закрыты DerivAlong/Nonvacuity, но произвольные E не определены. |
| Generalization/ModeState | Probe telemetry (`G`, fit, Q dynamics) external; только поточечная линейная агрегация доказана. |
| Growth/GainRenewal | `frontier_scaling` — модель реинвестиции, derived takeoff не устраняет premise. |
| Growth/Grow | Каноническая quadratic PL закрыта циклом 45; общий PL остаётся классом функций. |
| Growth/SeedOnly | Lipschitz dispersion/recurrence — исходные модели, не выводятся. |
| Growth/Takeoff | Step/dyn/cone — исходная динамика, доказаны только следствия и точные инстансы. |
| Model/ConsolidationMirror | Grow выведен `core_premises_grow_operational`. |
| Model/Memory | Physical memory write premise остаётся. |
| Model/ReferenceMachine | Quantization distortion модель уже выведена; measured dist остаётся ledger premise только в generic wrappers. |
| Model/SoftmaxStep | Smoothness выведена из производной logitCE; generic doc premise не скрыт. |
| Pretraining/ProbeError | Taylor/probe bound доказан; cross-task attention gradient Lipschitz остаётся допущением модели. |
| Pretraining/SyntheticPretrain | Measured synthetic-task gates/transfer остаются исходными данными. |
| Probability/ConditionalSuccess | `[0,1]`, meas, p — исходные; independence — stochastic premise, не выводится из них. |
| Probability/Freedman | Conditional variance bound остаётся martingale input. |
| Runtime/TernaryExact | Quantization доказан; gradient lip остаётся вариантом energy model. |
| Step/AdaptiveSafeQP | Noise measurable/zero/independence/bounds — probabilistic model inputs. |
| Step/Compound | Consumption/gap/decay — исходная динамика. |
| Step/ProjectionDescent | Projection выведен; smoothness класса E остаётся до DerivAlong model. |
| Step/SafeQPStep | Trust-region arithmetic выведен; общая smoothness модель сохраняется. |
| Step/StochasticSafeQP | Те же stochastic premises. |
| System/GrowthComputed | Canonical computed energy/grow выведен `growEnergy_derived`. |
| System/GrowthState | Переходная арифметика доказана; measured stage effects закрываются только операциональными инстансами. |
| Unified/AdvanceWitness | Memory physics остаётся. |
| Unified/AnytimeMartingale | Те же stochastic premises. |
| Unified/ArchitectureTheorem | Cone/dyn — исходная динамика семейства состояний. |
| Unified/Assumptions | Cone/step/dyn/noise cap — исходная динамика и idle witnesses. |
| Unified/CommitGate | Компьютерный gate уходит от premise; generic `h_emp_grow` мостится canonical instance. |
| Unified/CorePremisesDerived | Smooth/lip/dist выведены; grow/merge/G подключаются отдельными инстансами. |
| Unified/DerivAlong | Основной аналитический smooth/lip/dist мост уже закрыт. |
| Unified/DescentCore | Objective descentLemma исходный; quad/logit инстансы закрыты. |
| Unified/EmpiricalPremises | `holds` не выводит smooth; `premises_give_smooth` требует hsmooth — это НЕ закрытие, misleading docstrings подлежат исправлению. |
| Unified/GrowthBridge | ConditionalSuccess independence/measurability — external. |
| Unified/MasterHAGI | Составной conditional capstone; только stage bridges выведены. |
| Unified/MasterHAGITrunc | Cone dynamics external, Perron consequences доказаны. |
| Unified/RecursiveGrowth | Macro arithmetic доказан; stage premises не удалены без модели. |
| Unified/StateTakeoff | Cone dynamics external, доказаны последствия. |
| Unified/TopLevel | Quant energy модель выведена в EFTheory; noise/smoothness остаются классами моделей. |

## Что нельзя закрыть без новых определений или измерений

- Независимость, measurability, martingale variance и точное
  распределение sampler не следуют из чистой арифметики.
- `cUnit` Landauer, memory write, cooling dissipation и
  operational credit — физические/аппаратные данные.
- Qgen, fit, synthetic-task gates — данные оценки, а не
  следствия energy/KL без конкретной функции измерения.
- Общие `PL`, `second`, `attsmooth`, cone-dyn и scaling — это
  семейства моделей. Они закрываются доказанными инстансами,
  но не исчезают истинно при произвольных функциях.

Следующий механический шаг: не удалять общие conditional lemmas;
подключать новые операциональные инстансы к каноническому
`CertStep` и исправить misleading `EmpiricalPremises` docstring,
который обещал вывод `holds ⇒ smooth`, отсутствующий в теореме.

## Цикл 46 — исполнение замкнуто в CertStep

- `logitStepCertExactCore` — scalar CE с произвольным η>0;
  фактический drop из `descent_step_strict`.
- `ncMinimalStepCert` — drop=`u.gain` из `ncCertStep_energy`.
- `trainStepMinimalCert` — точный drop из `trainStep_actualDescent`
  с sufficient-step positivity; никакой smoothness-гипотезы.
- Все три ядра имеют только стандартные Lean-аксиомы;
  AssumptionScan не получил новых premise binders (137).
