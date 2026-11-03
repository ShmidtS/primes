# PREMISES — реестр предпосылок HAGI (аудит v18 §10)

Каждая предпосылка `CorePremises` (Unified/MasterHAGI.lean) и ключевые
`h_emp_*` получают один из трёх статусов:

1. **[PROVED]** — доказана в Lean из более фундаментальных фактов
   (ядро Foundations / Model);
2. **[DERIVED]** — выводится из свойств операционной модели
   (CorePremisesDerived, ReferenceMachine, GDNBridge) при условиях
   этой модели;
3. **[EXTERNAL]** — передаётся извне (h_emp_*), должна измеряться
   или проверяться экспериментально; закреплена в
   scripts/assumptions.lock (AssumptionScan).

## CorePremises (MasterHAGI) — конъюнкт за конъюнктом

| # | Конъюнкт | Статус | Откуда |
|---|----------|--------|--------|
| 1 | `0 ≤ gap` | DERIVED | Nonvacuity: gap = измеренный jensenGap (Core lse-теория), ≥ 0 |
| 2 | `growEnergy ≤ energy − growGain` (рост укладывается в энергию) | DERIVED | CorePremisesDerived + ConsolidationMirror.core_premises_grow_operational (mirror-descent оператор); для машины — MachineBridge (effects вычислены) |
| 3 | `mergeEnergy ≤ growEnergy − gap` (стоимость слияния) | DERIVED | Nonvacuity.h_emp_merge_of_bridge: gap = jensenGap двух экспентов (Core lse-теория) — посылка выполняется выведением |
| 4 | `0 < sp.L` (гладкость стадии) | DERIVED | из L2/Lipschitz loss модели (CorePremisesDerived: joint-гладкость выводится) |
| 5 | `eta ≤ 1/L` (шаг SafeQP) | PROVED | SafeQP: аналитический выбор шага (Step/SafeQP) |
| 6 | `0 ≤ eta` | PROVED | конструктор SafeQP |
| 7 | `‖stepDir‖² ≤ ⟨grad, stepDir⟩` (направление спуска) | DERIVED | SafeQP_descent: проекция на допустимые даёт direction property |
| 8 | `jointEnergy ≤ merge − η⟨g,d⟩ + Lη²‖d‖²/2` (L-модель шага) | DERIVED | CorePremisesDerived: выводится из гладкости loss (DescentAlong) |
| 9–11 | `0 ≤ kappa`, `0 ≤ s`, `quantErr ≤ 1/2` | PROVED+DERIVED | gridQ-семантика (machine_quant_err_bound); аналитический вывод нормированной формы: ReferenceMachine.quantErrNorm_avg_le_half (|Q(w)ᵢ−wᵢ|/Δ ≤ 1/2 в среднем — из abs_sub_round, без деклараций) |
| 12 | `compressEnergy − jointEnergy ≤ kappa·s·quantErr` (компрессия) | DERIVED | CorePremisesDerived: из нормы производной + фактической ошибки округления |
| 13 | `S' = compress∘joint∘merge∘grow S` (состав) | PROVED | операционное определение advance (StageSemantics) — rfl |
| 14 | `∀ i, Qvec S' i ≤ Qvec S i + epsQ` (gen-полоса покомпонентно) | EXTERNAL | h_emp_C_cap / gen-полоса — измерение на probe-задачах |
| 15 | `Qgen(S) − epsQ ≤ Qgen(S')` (gen-минимум не проседает) | EXTERNAL | измерение weighted probe-score |

## Ключевые h_emp_* (полный список: scripts/assumptions.lock)

| Идентификатор | Смысла | Где критичен |
|---------------|--------|--------------|
| h_emp_smooth / h_emp_lip | гладкость/липшицевость реального loss | квантование→loss (TopLevel), robust descent |
| h_emp_dyn | динамические приросты стадий | рост capability |
| h_emp_noise_meas/zero/indep/bound | свойства шума измерений | StochasticSafeQP концентрация → batch_terminal_gap |
| h_emp_memwrite | энергия записи памяти | Landauer-кэп, consolidation_bits_cap |
| h_emp_C_cap | кэп генерализации | CorePremises (14) |

## Замечание об охвате (честная граница, аудит §10)

Полный аудит аксиом и sorry по всем модулям закрыт CI-гейтами
(ALLAXIOMS: только propext/Classical.choice/Quot.sound; StatusLint/
AssumptionScan: реестр; 0 sorry — блокировано гейтом), но статусная
классификация h_emp_* ПО ПОЛЯМ (не по файлам) продолжается.

## Примечание о консолидации (волна аудита v2, Часть 2)

Семейства SafeQP (5 модулей), DeltaNet-памяти (GDNBridge/Memory/GDN2),
квантования (Quantizer/Ternary/STEStep/TernaryExact) проверены на дубли:
пересечений нет — каждый модуль несёт свой предмет (проекции/окна/
концентрация/решётки; дельта-RAM/параметр-экономика/оператор arXiv;
решётка/трит-кодирование/STE/runtime-точность). Пара
frobeniusNorm'/frobeniusNorm'' (MatrixNormRelations) имеет идентичные
тела, но порядок деклараций Lean не позволяет сводящую делегацию без
переноса, ломающего section-скопы — оставлена как есть (осознанное
исключение).
