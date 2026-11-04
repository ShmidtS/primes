# Gate 0 — Critical Findings (аудит, HEAD 4a94945 + подключение 7 модулей)

Формат каждой находки: путь / имя / проблемная часть / причина / следствие /
исправление / проверка.

## Исправленные в этом цикле (P0 спеки §3; подтверждено CI 16/16)

### F1. NCStepCert: произвольный спуск d (спека §3.1) — FIXED (b65aa6a)
- Hagi/Unified/NCStepCert.lean, `ncCertStep`/`ncStepCert`
- Было: `energy := S.energy - d` при независимом `d` (только `hd : 0 < d`)
  → сертификат с искусственным спуском, не связанным с исполнением.
- Причина: параметр d не обязан равняться u.gain канонического ncAdvance.
- Следствие: любые «гарантии» спуска назначались вручную.
- Исправление (вариант 1 спеки): d удалён; ncCertStep := ncAdvance
  (спад = u.gain по построению); ncTraj/nc_loop_horizon без d.
- Проверка: Freeze CHANGED просмотрен; build green; негативный тест —
  конструирование сертификата с d ≠ u.gain более невозможно типово.

### F2. RamWriteCert: тавтологичное поле (спека §3.4) — FIXED (161a1f8)
- Hagi/Unified/MemorySemantics.lean, `RamWriteCert.post_eq`
- Было: `updateRow S i v = updateRow S i v` (rfl — ничего не доказывает).
- Исправление: явное поле `post` + 4 доказуемых свойства:
  post = updateRow pre address value; read_back; others_untouched;
  rewrite_idem (идемпотентность доказана ext+case-split — в Mathlib нет).
- Проверка: build green; #print axioms = [propext, Classical.choice, Quot.sound].

### F3. StepCert: отождествление риска и бюджета (спека §3.2) — FIXED (5003b72)
- Hagi/Unified/CertifiedLoop.lean, `StepCert`
- Было: один `spend` одновременно riskSpend в HonestTransition и списание
  бюджета (hdec : b' ≤ bt − spend) — нелегитимное равенство каналов.
- Исправление: независимые `riskSpend`/`budgetSpend` (оба ≥ 0);
  trans использует riskSpend, hdec — budgetSpend; равенство между каналами
  не выводимо и не предполагается. Потребители (NCStepCert, CertUnify,
  quad/quartic/sign, MasterChallengeV3) обновлены на фактические величины.
- Проверка: build green; Freeze CHANGED просмотрен; CI PASS.

### F4. CertifiedTransition V1: фантомный riskLim (спека §3.3) — FIXED (6f01948)
- Hagi/Model/CertifiedTransition.lean
- Было: riskLim — параметр без полей, использующих его (safety ограничен
  только точной суммой рисков операций).
- Исправление: активное поле `safetyLim : S'.protectedRisk ≤
  S.protectedRisk + riskLim` (формула спеки) наряду с точным safety-ledger;
  канонический конструктор доказывает оба (riskLim = фактическая сумма).
- Проверка: build green; V2 (hRiskLim) и V3 наделяют V1 активным лимитом.

### F5. Freeze слеп к полям структур — FIXED (5edea7b)
- scripts/Freeze.py
- Было: хеш только до `where` → ослабление ПОЛЕЙ сертификатов невидимо
  (Goodhart-дыра).
- Исправление: полный хеш тела structure/inductive (комментарии вырезаны).
- Проверка: 3936 деклараций, ничего не потеряно; doc-правки не сдвигают хеши.

### F6. assumptions.lock считает комментарии (спека §1.4) — FIXED (485e585, 35bf8da)
- scripts/AssumptionScan.py
- Было: docstring «АНАЛИТИЧЕСКИЙ ВЫВОД h_emp_dist» регистрировался как
  посылка; 5 доказанных h_emp-именованных теорем считались посылками.
- Исправление: комментарии вырезаны; доказанные декларации выделены в
  отдельную секцию. Итог: 134 вхождения = 5 доказанных + 129 binder-посылок.
- Проверка: AssumptionScan PASS; PREMISES.md (проходы 1–3).

### F7. Неиспользуемые фиктивные гипотезы — FIXED (8bde24a, 05b936a, 26760e4)
- PPT.lean: _h_emp_good/_h_emp_ver/_h_emp_bud (union bound не требует
  измеримости); ModeState: _h_emp_G + зависимый ε_Q.
- Исправление: удалены из сигнатур — теоремы строго сильнее.
- Проверка: TrivialLint kernel-level UNUSED_PARAM new:0 (все оставшиеся
  h_emp-биндеры задействованы в доказательствах).

## Открытые находки (требуют решения следующих гейтов)

### O1. 7 модулей вне основного build graph — FIXED ЭТИМ КОММИТОМ
- BatchBudget, NoisyPL, RobustDescent, MemorySemantics,
  ProductiveTransition, TransitionCert, VerticalCapstone —
  не импортировались в Hagi.lean (подтверждено перепроверкой на актуальном
  HEAD, spec §2.2). Все 7 собираются независимо; теперь подключены в
  агрегатор → unreachable = 0 (391/391 файлов в графе).

### O2. CertifiedLoop quality как FloorKept M s' (спека §3.5) — частично
- quality корректно измеряется из фактического состояния s' через
  MeasuredState M (FloorKept M s' floor). Полностью закрывается в P2
  (TrainState + Metrics.evaluate) — единый измеритель состояния.

### O3. Нет единого TrainState/Transition (спека §4–5) — Gate 2/3 pending
- Существующие состояния (NCState, GrowthState, GenState, OmniState…)
  разрознены; сертификаты над ними — через мосты (CertUnify). Центральная
  задача следующих гейтов.

### O4. Внешние backend-интерфейсы (HNet/Qwenputer/QwenBend/qwenGPU) — Gate 5 pending

## Ложные срабатывания сканера (зафиксировано, не дефекты)
- `sorry`: только prose в docstring'ах («0 sorry in the source») —
  комментарий удалён вырезанием, вхождения — внутри оставшихся строк
  документации модулей; реальных тактик нет (TrivialLint + AxiomCheck PASS).
- `admit`: Hagi.Growth.admit — имя функции допуска, не тактика
  (используется как `admit c`, `¬ admit c`); prose-«admit-решение».
- duplicate_names (40): одинаковые имена в разных namespace (Lean
  различает по префиксу); дублиКАТЫ утверждений отсутствуют —
  AlphaDup.py PASS (0 statement-level duplicates).

## Сводка Gate 0
- 391 Lean-файл, 2919 theorems (+ instances/defs = 3936 деклараций Freeze).
- Граф: unreachable 0 (после подключения 7 модулей), циклов на уровне
  импортов нет (lake build успешен), sorry/admit/axiom/unsafe — 0 реальных.
- Классификация A–E: см. audit/theorem_inventory.json (категория
  эвристически: B = с h_emp-биндерами, C = операциональные сертификаты,
  A = остальная математика; D требует runtime-мостов Gate 5, E = PREMISES.md).

### O5. Зависимые формулировки в подключённых модулях — baseline (документировано)
- `certified_gain_margin` (параметр w — носитель admitted-сертификата,
  используется телом доказательства через проекцию w.admitted.2, но не
  входит в тип заключения) и `TC.certs_telescope` (список сертификатов
  certs — источник полей заключения). Зависимый стиль формулировок
  («из сертификата следует»), не фиктивный сертификат: удаление параметра
  потребовало бы замены сертификатного носителя голой гипотезой — изменение
  смысла, запрещённое спекой §1.2. Флаги добавлены в
  scripts/triviallint_baseline.txt (22 suppressed) с настоящим обоснованием.

### Этап 1.2 аудита (Arc/FacadeLaws) — частично выполнен, частично ОТКЛОНЁН с доказательством
- Удалены 8 агрегаторов (BudgetArc, GrowthArc, ModelArc, OptimizationArc,
  ProbabilityArc, StepArc, CompressionArc, UnifiedArc: 0 деклараций);
  их импорты раскрыты в Hagi.lean напрямую (unreachable=0 сохранён).
- EFArc НЕ агрегатор: 710 строк, 26 теорем EF (ef_telescope, quad_ef_exact,
  …). Утверждение аудита «Arc не содержат ни одного доказательства» —
  ЛОЖНО для EFArc. Файл переименован в Hagi/Unified/EFTheory.lean (смена
  имени модуля, все 26 деклараций сохранены, Freeze 0 lost).
- FacadeLaws НЕ удалён: утверждение аудита «22 механические склейки» —
  неточно; robust_growth_corridor (35-строчное индукционное доказательство),
  pinsker4_via_canon (56 строк) и др. содержат настоящие доказательства.
  Удаление файла нарушило бы merge-before-delete. Требуется постатейный
  разбор (отдельная задача), а не удаление файла целиком.
- Откат-инцидент: первое удаление Arc прошло по неполной проверке (3 из 9
  файлов) — пойман Freeze (5 LOST ef_*), полностью восстановлен из git,
  повторная проверка ВСЕХ 9 файлов перед повторным удалением.

### Этап 3 аудита (Hagi.Math) — фактическое состояние
- External/Flywheel УЖЕ изолирован: импортирует только Mathlib и
  себя; зависимостей от StageParams/GrowthState нет (проверено rg по
  import-строкам всех 11 модулей). Требование аудита «убрать
  зависимость от псевдо-структур» выполнено заранее.
- Физический перенос в Hagi/Math/* = массовое переименование модулей
  (нарушает спеку §1.3 «не выполнять массовое переименование в одной
  операции» и §13 «не переносить ради структуры»). Отложено до
  явного решения; содержательная изоляция уже есть.

### Frobenius-нормы (Этап 2.3 аудита)
- 5 локальных определений существуют (AlignedMerge/FrobOuter/
  MicroStepCert/MemoryCycle/frobeniusNormRect), но разных носителей
  (Fin-типизированные vs произвольные индексы; ℝ vs ℂ) и уже связаны
  мостами в External/Flywheel/MatrixNormRelations (57 теорем);
  частичная несводимость зафиксирована семейным аудитом (declaration
  order). Полная унификация — самостоятельная задача с высоким
  регрессионным риском, не предпринята в этом проходе.

### TD-05 (LayerLint) — FIXED (3720f0f)
- LAYERS дополнены State=3, Contracts=7, Challenge=7; 0 новых
  нарушений, 0 baseline-добавлений.
