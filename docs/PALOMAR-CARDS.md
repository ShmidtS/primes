# Palomar-cards — C5XX–C6XX-теория как кандидаты для реестра Lean-результатов

[Palomar](https://palomar-registry.org/) — публичный реестр
Lean-верифицированной математики (Lean FRO + ICARM). Запись
реестра фиксирует: репозиторий + полный commit SHA, формальное
statement (Challenge-модуль, ≤1000 строк, импорты только
Lean core + Mathlib/Tau Ceti), proved Solution-модуль
(аксиомы только `propext`, `Classical.choice`, `Quot.sound`),
comparator.json, formalization.yaml (arXiv-категории, MSC2020,
авторство, автоматизация, honest narrative), результат
механической проверки (Lean kernel + независимый `nanoda`) и
редакционный вердикт («no blocking problem»). Реестр не
ранжирует и не одобряет результаты.

этот файл — подготовительные карточки (draft entries) девятнадцати
machine-checked результатов C5XX–C6XX-витков: самодостаточные
математические формулировки без контекстной терминологии,
точные FQN-якоря и честный статус. Все доказательства
проверены Lean 4.36 (pinned Mathlib, см. lake-manifest.json);
гейт `scripts/AllAxiomCheck.lean` (`ALLAXIOMS: PASS` в ci.sh)
подтверждает: только стандартные три аксиомы
Lean (`propext`, `Classical.choice`, `Quot.sound`), без
`sorryAx` и `Lean.ofReduceBool`.

Отправка в реестр — внешний user-шаг (см. README).

---

## Card 1 — Empirical-Bernstein bound for martingale sums

- **Statement.** Пусть `X_t` — адаптированные к прошлому
  приращения с условным средним 0, диапазоном `|X_t| ≤ b`, и
  измеренной эмпирической дисперсией `σ̂²` (runtime-посылка).
  Тогда при `0 < α < 1`, `L = ln(2/α)`:

  `P[|Σ X_t| < √(2nσ̂²L) + 2bL] ≥ 1 − α`.

  Двухсторонняя инвертированная граница типа Freedman с
  подстановкой эмпирической дисперсии: √-член несёт `σ̂` вместо
  диапазона `R` (экономия vs Hoeffding при `σ̂² ≪ R²`).
- **Anchor.** `Hagi.Probability.EmpiricalBernstein.empirical_bernstein_bound`
  (Hagi/Probability/EmpiricalBernstein.lean:208).
- **Dependencies.** Mathlib (MeasureTheory/Martingale basics);
  внутренний модуль `Hagi.Probability.FreedmanInversion`.
- **Status.** Machine-checked (Lean 4.36); аксиомы: стандартные
  три Lean. Заметка:statement использует измеренную `σ̂²` как
  посылку (runtime-канон h_emp), а не выведенную из данных.
- **Category.** Probability (arXiv math.PR); MSC2020 60G42
  (martingales), 62E17 (bounds).

## Card 2 — Naive multiplicative decay leaks out of a protected subspace

- **Statement.** Для матриц `W : m×n`, проектора `P : n×n` и
  коэффициента `0 < c < 1`: покомпонентное затухание
  `(1−c)·W` строго уменьшает норму защищённой компоненты
  `‖(((1−c)·W)·P)_i‖ < ‖(W·P)_i‖` (для строк с ненулевой
  защищённой частью). Следствие: затухание весей без
  проецирования в дополнение подпространства неизбежно
  «протекает» в защищаемое подпространство; дополнение
  `ΔC·P = 0` оставляет её точно инвариантной
  (`compl_step_preserves`).
- **Anchor.** `Hagi.Theory.WeightDecayLeak.naive_decay_leak`
  (Hagi/Theory/WeightDecayLeak.lean:126); сопутствующая
  `wd_gpm_step_sound` (:159).
- **Dependencies.** Mathlib (Matrix, Real.sqrt); локальные
  леммы модуля.
- **Status.** Machine-checked; аксиомы: стандартные три Lean.
- **Category.** Optimization / matrix analysis (arXiv math.OC /
  15Axx); MSC2020 15A16, 68Q32.

## Card 3 — ε-completeness of a bounded candidate generator

- **Statement.** Пусть предикат `CandidateComplete gen G safe ε`
  означает: для любого порога `g` и safe-элемента `a₀` с
  `G a₀ ≥ g` генератор выдаёт safe-кандидата `a` с
  `G a ≥ g − ε`. Тогда при `0 ≤ ε`, существовании safe `a₀` с
  `ε < G a₀` найдётся `a'` с `gen a'`, `safe a'`, `0 < G a'` и
  `G a₀ − ε ≤ G a'`. Формализация «поиск по эвристикам не
  теряет больше ε качества»: любой argmax-over-generated
  ε-аппроксимирует глобальный optimum.
- **Anchor.** `Hagi.Growth.StateBinding.candidate_completeness_find`
  (Hagi/Growth/StateBinding.lean:86).
- **Dependencies.** Mathlib (Finset, DecidablePred); без
  внешних теорий.
- **Status.** Machine-checked; аксиомы: стандартные три Lean.
- **Category.** Combinatorial optimization / search (arXiv
  cs.DM); MSC2020 68W25, 90C31.

## Card 4 — Zero cross-entropy on exactly-predicted coverage

- **Statement.** Для распределения `p : ι → ℝ` (неотрицательные,
  сумма 1) и конечного списка `xs`: если `p x = 1` для всех
  `x ∈ xs`, то сумма покомпонентных log-loss
  `Σ_{v ∈ xs} −ln(p v) = 0`. Базовый факт теории log-loss:
  классификатор с вероятностью 1 на покрытии даёт нулевую
  ошибку кросс-энтропии.
- **Anchor.** `Hagi.Theory.ExactBypass.ce_covered_zero`
  (Hagi/Theory/ExactBypass.lean:72); строится на
  `ce_pointwise_of_prob_one` (:64).
- **Dependencies.** Mathlib (Real.log, List.sum); без внешних
  теорий.
- **Status.** Machine-checked; аксиомы: стандартные три Lean.
- **Category.** Information theory (arXiv cs.IT / math.IT);
  MSC2020 94A17, 68T05.

## Card 5 — Shared-core + mean-residual merge error bound

- **Statement.** Для конечного индексированного семейства
  моделей `W i` (нормированное пространство) с общим ядром `C` и
  остатками `R i`, удовлетворяющими декомпозиции с зазорами
  `‖R i − (W i − C)‖ ≤ δ i`:

  `‖fullMerge W − (C + meanResidual R)‖ ≤ Σ i (1/|ι|)·δ i`,

  т.е. ошибка слияния N моделей (усреднение) ограничена средним
  зазоров декомпозиции — формальная база low-rank/Matrёshka
  слияния: shared-часть переносится без ошибки, платится
  только средний residual.
- **Anchor.** `Hagi.Architecture.FactorizedMerge.factorized_error_bound`
  (Hagi/Architecture/FactorizedMerge.lean:141); опирается на
  `merge_core_residual_identity` (:76),
  `factorized_merge_exact` (:101).
- **Dependencies.** Mathlib (NormedSpace, Finset.sum);
  внутренние определения модуля (`fullMerge`, `meanResidual`).
- **Status.** Machine-checked; аксиомы: стандартные три Lean.
- **Category.** Approximation / numerical analysis (arXiv
  math.NA); MSC2020 41A25, 65D99.

## Card 6 — Denominator of a dyadic rational stays bounded

- **Statement.** Для целого `q` и натурального `k`:

  `(q / 2^k : ℚ).den ≤ 2^k`.

  Любая точка диадической сетки `q/2^k` имеет канонический
  знаменатель не выше степени сетки; суммы таких точек
  (lcm-комбинаторика степеней двойки) снова лежат в сетке.
  Элементарный, но конструктивно полезный факт для certified
  вычислений на фиксированной сетке.
- **Anchor.** `Hagi.Theory.GrowSnap.snap_denominator_reset`
  (Hagi/Theory/GrowSnap.lean:120).
- **Dependencies.** Mathlib (Rat, Int.divisibility); без
  внешних теорий.
- **Status.** Machine-checked; аксиомы: стандартные три Lean.
- **Category.** Number theory / exact arithmetic (arXiv
  math.NT); MSC2020 11A99, 68W30.

## Card 7 — Explicit interval certificate for a spline cycle map

- **Statement.** Для явной композиции трёх кубических сплайнов
  `p5` с рациональными коэффициентами
  `(10151/2500, −17483/2500, 9623/2500)`,
  `(5429/2000, −25159/10000, 1963/2500)`,
  `(9473/5000, −1119/1000, 2201/10000)`: для всех
  `x ∈ [1/1000, 1]` образ трёхкратной композиции лежит в
  интервале `[9/512, 1049/1024]`. Сертификат не вакуосен:
  коэффициенты `(3, −5, 1)` того же знакового профиля
  опровергаются контрпримером `p(9/10) = −35451/100000 < 0`
  (`polar_express_bad_coeff_counterex`).
- **Anchor.** `Hagi.Optimization.PolarExpressCert.polar_express_cycle_cert`
  (Hagi/Optimization/PolarExpressCert.lean:402);
  ступенчатые леммы `polar_express_step{1,2,3}_bound`.
- **Dependencies.** Mathlib (Real.arith, nlinarith); без
  внешних теорий.
- **Status.** Machine-checked; аксиомы: стандартные три Lean.
  Численно-явный результат (конкретные константы), математическая
  ценность — методика certified interval-анализа композиций.
- **Category.** Real analysis / interval methods (arXiv
  math.CA); MSC2020 26C99, 65G40.

## Card 8 — Rank-r adapter parameter dominance: 2rd ≤ d²

- **Statement.** Для конечных типов `r`, `d` с
  `2·|r| ≤ |d|`: низкоранговый адаптер (down `A : r×d` + up
  `B : d×r`) имеет строго меньшее число параметров, чем полный
  `d×d`-блок того же слоя:

  `2·|r|·|d| ≤ |d|·|d|` (равенство только при `2|r| = |d|`;
  строго при `2|r| < |d|` — `adapter_param_count_lt_block`).

  Явный счёт: `card(A) + card(B) = 2·|r|·|d|`.
- **Anchor.** `Hagi.Theory.AdapterGrowth.adapter_param_count_le_block`
  (Hagi/Theory/AdapterGrowth.lean:158); `adapter_param_count`
  (:140), `block_param_count` (:152),
  `adapter_param_count_lt_block` (:167).
- **Dependencies.** Mathlib (Fintype, Finset.card); без внешних
  теорий.
- **Status.** Machine-checked; аксиомы: стандартные три Lean.
  Элементарная комбинаторика; ценность — формальная опора
  low-rank-эффективности (LoRA-доминирование).
- **Category.** Combinatorics / machine learning theory (arXiv
  cs.LG); MSC2020 05A99, 68T07.

## Card 9 — Optimal gradient step γ* = 1/L: perfect-square gap

- **Statement.** Пусть `φ(γ) = γG − (L/2)γ²G²` — guaranteed
  per-step drop градиентного шага для L-smooth функции с
  градиентной нормой G > 0 (посылка smoothness: `f(y) ≤ f(x) +
  ⟪∇f(x), y−x⟫ + (L/2)‖y−x‖²`). Тогда для любого γ:

  `φ(1/L) − φ(γ) = (G²/(2L))·(1 − Lγ)² ≥ 0`,

  т.е. γ* = 1/L — глобальный максимум параболы (не только на
  descent-зоне [0, 2/L]), а максимальный drop равен
  `φ(1/L) = G²/(2L)` (одношаговый sufficient decrease).
- **Anchor.** `Hagi.Theory.NegativeTransfer.nlDrop_le_optimal`
  (Hagi/Theory/NegativeTransfer.lean:467); `nl_drop_optimal`
  (:481); premise-форма `nl_drop_bound` (:443); определения
  `nlDrop` (:434), `nlStep` (:231).
- **Dependencies.** Mathlib (NormedSpace, inner product);
  внутренние определения модуля. Bench-числа (C609):
  auto-LR γ_auto = 1/(2·trace(H̄)) ∈ {5000000/10470759 ≈
  0.477, 13500000/25944901 ≈ 0.520, 156250/234227 ≈ 0.667} —
  измеренный диапазон 0.48–0.67 против прежней константы 1/10.
- **Status.** Machine-checked (Lean 4.36); аксиомы:
  стандартные три Lean. Классический факт (η = 1/L), ценность —
  certified-мост от измеренной L к шагу (бенчмарк-телеметрия
  per-step drop vs bound G²/(2L)).
- **Category.** Optimization (arXiv math.OC); MSC2020 90C25,
  68T07.

## Card 10 — Hierarchical window coverage for every n with
bounded peak

- **Statement.** Разобьём [0, n) на блоки длины ≤ B
  (`ℓ_j = min B (n − jB)`), в каждом блоке возьмём старты окон
  длины w с шагом s. Тогда при `0 < B`, `0 < s ≤ w`:

  `∀ i < n, ∃ t ∈ starts: t ≤ i ∧ i < t + w`

  — полное покрытие при любом n (без верхней границы на n);
  а при `w ≤ B`, `(B−w)/s + 2 ≤ m` в каждом блоке ≤ m окон,
  т.е. streaming peak-память ≤ m окон (total растёт с числом
  блоков ⌈n/B⌉ — честное peak ≠ total).
- **Anchor.** `Hagi.Theory.CoverageReading.hier_covers_any_n`
  (Hagi/Theory/CoverageReading.lean:282);
  `hier_peak_window_budget` (:315); определения `hierBlockLen`
  (:268), `hierStarts` (:273).
- **Dependencies.** Та же Mathlib-база; сведение поблочно к
  `covStartsStep_covers` (Card 11). Числа-инстансы (C613,
  w = m = 64, B = 4032, s = 64): n = 100000 → 25 блоков
  (per-block 24×63 + 51 окон), total 1563, peak 63 ≤ 64;
  Lean-свидетель n = 8128 → блоки [63, 63, 1], peak 63
  (machine-checked #eval).
- **Status.** Machine-checked (Lean 4.36); аксиомы:
  стандартные три Lean. Ценность — сертифицированное снятие
  одноуровневой границы покрытия (n ≤ 4032 при w = m = 64)
  иерархией без роста peak-памяти.
- **Category.** Discrete mathematics / streaming algorithms
  (arXiv cs.DM); MSC2020 68W40, 68P05.

## Card 11 — Single-level window coverage iff step fits window
and budget

- **Statement.** Для стартов окон [t, t+w) с шагом s на [0, n)
  одноуровневое покрытие

  `∀ i < n, ∃ t ∈ starts: t ≤ i ∧ i < t + w`

  доказуемо при `0 < s ≤ w` (условие точно: шаг > длины окна
  оставляет дыры — контрпример s = 17 > w = 9, байт 9
  непокрыт); число окон ≤ `(n−w)/s + 2`; при бюджете m окон
  покрытие в бюджете доказуемо при `0 < s ≤ w`,
  `(n−w)/s + 2 ≤ m` — замыкание негатива «усечение списка
  стартов до m теряет байт 0»: адаптивный шаг вместо
  усечения сохраняет старт 0. Следствие-граница: при
  s = w одноуровневое покрытие возможно ⟺ n ≤ w +
  s(m−2) ≤ w(m−1) — при w = m = 64 это n ≤ 4032; при
  n > 4032 одноуровнево INFEASIBLE (снимается иерархией
  Card 10).
- **Anchor.**
  `Hagi.Theory.CoverageReading.covStartsStep_covers`
  (Hagi/Theory/CoverageReading.lean:184);
  `covStartsStep_len_le` (:220);
  `covStartsStep_adaptive_covers` (:233).
- **Dependencies.** Mathlib (List, Nat.div); без внешних
  теорий. Bench-числа (C602/C611): n = 540 → s = 8, 61 окно,
  covered; n = 4032 → s = 64 (граница), covered; n = 8128 →
  127 окон > 64 — INFEASIBLE.
- **Status.** Machine-checked (Lean 4.36); аксиомы:
  стандартные три Lean. Sufficiency (0 < s ≤ w ⇒ покрытие;
  + бюджет ⇒ ≤ m окон) — Lean-теоремы; необходимость условия
  s ≤ w и потеря байта 0 при усечении — Lean-witness
  (machine-checked контрпримеры).
- **Category.** Discrete mathematics (arXiv cs.DM); MSC2020
  68W40, 05B40.

## Card 12 — Information-theoretic floor for reading n bytes
with width-w windows

- **Statement.** Информационный floor: любой список стартов L,
  покрывающий каждый байт i < n окном [t, t+w), имеет длину не
  меньше ⌈n/w⌉ — Lean дословно:

  `theorem hier_total_floor (L : List ℕ) (w n : ℕ) (hw : 0 < w)`
  `(hcover : ∀ i < n, ∃ t ∈ L, t ≤ i ∧ i < t + w) :`
  `n ≤ L.length * w`

  и иерархия из Card 10 при s = w, w ∣ B достигает floor
  (`hier_total_min` :462):

  `theorem hier_total_min (n B w : ℕ) (hw : 0 < w) (hB : 0 < B)`
  `(hdiv : w ∣ B) :`
  `(hierStarts n B w w).length = (n + w - 1) / w`

  замыкая оптимум (`hier_optimal` :533): total иерархии = ⌈n/w⌉
  ∧ ∀ L-покрытие: `(n + w - 1) / w ≤ L.length`.
- **Наглядность.** Никакая иерархия не прочитает n байт окнами
  ширины w меньше чем ⌈n/w⌉ чтениями — это геометрия, а не
  алгоритм: k окон покрывают не более k·w байтов (инъекция
  i ↦ (окно, сдвиг) в пары «t × [0, w)»). Floor не зависит от
  структуры иерархии — только от ширины окна w; выбор B
  свободен (любое B, кратное w, даёт один и тот же total,
  гипотеза B* = √(nw) опровергнута телескоп-суммой).
- **Anchor.**
  `Hagi.Theory.CoverageReading.hier_total_floor`
  (Hagi/Theory/CoverageReading.lean:494);
  `hier_total_min` (:462); `hier_optimal` (:533);
  `hier_total_formula` (:440); `hier_blocks_sum_tiling` (:389);
  `covStartsStep_len_tiling` (:354); определения `hierBlockLen`
  (:268), `hierStarts` (:273).
- **Dependencies.** Mathlib (Finset.card_le_card_of_injOn,
  List, Nat.div); без внешних теорий. Числа-инстансы (receipt
  C618): n = 100000, w = m = 64 → total 1563 = ⌈100000/64⌉ для
  всех B ∈ {64, 2048, 4032, 4096} (константен по B); s = 32 < w
  → 3033 > 1563 (строго хуже floor); n = 8128 → 127.
- **Status.** Machine-checked (Lean 4.36); аксиомы: стандартные
  три Lean. Ценность — сертифицированная НЕУЛУЧШАЕМОСТЬ
  иерархии Card 10 по total: достигнут информационный минимум,
  дальше сокращать нечего без уменьшения w.
- **Category.** Discrete mathematics / streaming algorithms
  (arXiv cs.DM); MSC2020 68W40, 68P05, 05B40.

## Card 13 — Linear window cost makes total budget nearly
width-independent

- **Statement.** Модель totalCost(w) = ⌈n/w⌉·c(w). При
  линейной стоимости чтения окна c(w) = c·w total-cost почти
  НЕ зависит от ширины окна — Lean дословно
  (`windowCost_linear_near_const`, для любых 0 < w1, w2):

  `theorem windowCost_linear_near_const (n w1 w2 : ℕ) (hw1 : 0 < w1)`
  `(hw2 : 0 < w2) :`
  `w1 * ((n + w1 - 1) / w1) ≤ w2 * ((n + w2 - 1) / w2) + (w1 - 1)`

  т.е. totalCost(w1) ≤ totalCost(w2) + c·(w1 − 1) и симметрично
  (обе границы `windowCost_linear_bounds` :586: n ≤ w·⌈n/w⌉ ≤
  n + w − 1 — total зажат в [c·n, c·(n+w))). Контраст — режим
  (a) фиксированной стоимости `windowCost_fixed_mono` :577: при
  c(w) = c totalCost(w) = c·⌈n/w⌉ монотонно невозрастает по w
  (ядро `ceil_div_anti` :555) — оптимально w = w_max. Мост к
  иерархии C618: `windowCost_hier` :613 (total = ⌈n/w⌉ при
  w ∣ B).
- **Наглядность.** При линейной стоимости окна ширина почти
  не влияет на общий бюджет — выбирай по точности, не по
  экономии: нижняя граница c·n едина для всех w (каждый байт
  оплачен ровно c раз в лучшем случае), а зазор верхних
  оценок < c·w — цена выбора w ограничена стоимостью ОДНОГО
  окна максимальной ширины, тогда как число чтений ⌈n/w⌉
  меняется на порядки. Смена режима стоимости c(w) = c →
  c·w меняет вывод на противоположный (w_max → свободно).
- **Anchor.**
  `Hagi.Theory.WindowTradeoff.windowCost_linear_near_const`
  (Hagi/Theory/CoverageReading.lean:592);
  `windowCost_linear_bounds` (:586);
  `windowCost_fixed_mono` (:577); `ceil_div_anti` (:555);
  `windowCost_hier` (:613).
- **Dependencies.** Без Mathlib-теорий (Nat.div_add_mod,
  Nat.mod_lt, omega); числа-инстансы (receipt C623): n =
  100000, w ∈ {16, 64, 256} → чтения {6250, 1563, 391}, а
  линейный total-cost {100000, 100032, 100096} — все в
  коридоре [100000, 100000+w); мост hierStarts 100000 4032
  64 64 = 1563 (= Card 12).
- **Status.** Machine-checked (Lean 4.36); аксиомы:
  стандартные три Lean. Режим (c) — суперлинейное окно
  c(w) = a + c·w^α, α > 1, с формулой w* = (a/(c·(α−1)))^(1/α)
  — honest-набросок в STATUS.md (Real-арифметика, вне
  Nat-модели файла), не Lean-клоз.
- **Category.** Discrete mathematics / streaming algorithms
  (arXiv cs.DM); MSC2020 68W40, 68P05.

---

## Card 14 — Certified capacity gate: when growth cannot pay back

- **Statement.** Решение «расти/нет» по формульной границе — Lean
  дословно (`growthGate`, для любых ℚ):

  `def growthGate (potentialBound cAdd : ℚ) : Bool :=`
  `decide (cAdd < potentialBound)`

  grow ⟺ potentialBound > c_add, равенство → stay
  (`growth_gate_stay_char` :580: `growthGate pb c = false ↔ pb ≤ c`).
  MAIN (`growth_gate_sound` :677, CERTIFIED-STAY): если потолок
  возможного выигрыша n-шагового дообучения

  `theorem growth_gate_sound ... (hc : n * (G ^ 2 / (2 * L)) ≤ cAdd) :`
  `f z - f (nlRun n (1 / L) grad z) ≤ cAdd`

  т.е. при `n·G²/(2L) ≤ c_add` ЛЮБОЕ n-шаговое дообучение (в т.ч.
  с добавленной ёмкостью) уменьшает objective не более чем на
  `c_add` — рост НЕ может окупиться за n шагов. Ядро:
  `nl_drop_total` :620 — телескоп-индукция, drop за n шагов ≤
  `n·G²/(2L)` (per-step `nl_drop_step_eq` :608 = C606
  `nl_drop_optimal` при γ* = 1/L).
- **Наглядность.** Certified-совет «не расти»: потолок выигрыша
  ≤ стоимости ёмкости. Гейт сравнивает два числа — гарантированный
  потолок убывания objective против цены новой ёмкости — и если
  даже идеальное дообучение не отобьёт цену, рост запрещён
  математически, без единого измерения. Асимметрия честна:
  stay-ветка certified, grow-ветка — только разрешение (верхняя
  граница возможного ≠ факт). Числа (receipt C635): 6 синтетик —
  S1–S4 STAY (S4: pb = c_add, равенство → stay), G1/G2 GROW;
  λ-sweep при c_add = new_params·λ: PIN λ=1/10⁴ → 6 GROW/0 STAY
  (golden-идентичность C633), first_stay_lam = 1/10³;
  certified_stay_threshold λ* = min(pb/params) ≈ 10⁴¹ — PIN-λ
  на ~45 порядков ниже: stay-ветка реальна при λ ≥ λ*
  (GROW ⟺ λ < pb/params, монотонность по λ).
- **Anchor.**
  `Hagi.Theory.GrowthGate.growthGate`
  (Hagi/Theory/NegativeTransfer.lean:570, namespace внутри модуля);
  `growth_gate_stay_char` (:580); `nl_drop_step_eq` (:608);
  `nl_drop_total` (:620); `growth_gate_sound` (:677).
  Потребитель: bench `--mode grow-snap` / `adapter-grow`.
- **Dependencies.** Без Mathlib-теорий (field_simp, ring,
  nlinarith, induction-телескоп); NegativeTransfer-прологи
  (`nlDrop`, `nlStep`, `nlRun`, C606 `nl_drop_optimal`).
- **Status.** Machine-checked (Lean 4.36); аксиомы: стандартные
  три Lean. Honest pins: потенциал-модель — квадратичный класс
  (`hmodel`, равенство в descent-лемме, прецедент C572); для
  общего L-smooth certified-потолок шире — nlBudget C592
  `γG² + Lγ²G²/2`, гейт пересчитывается. Граница G — градиентная
  граница ТЕКУЩЕЙ модели на residual; grow-ветка ничего не
  обещает (bound — верхняя граница возможного, не факт).
- **Category.** Learning theory / optimization (arXiv cs.LG);
  MSC2020 68T05, 90C25.

---

## Card 15 — Adam's first step is a descent step; later steps
need not be

- **Statement.** Для конечного индексного множества `ι`, градиента
  `g : ι → ℝ` и `eps > 0` на первом шаге Adam (`m̂ = g`, `v̂ = g²`)
  скалярное произведение с градиентом строго положительно, если
  градиент ненулевой — Lean дословно:

  `theorem adam_first_step_dot_pos {ι : Type*} [Fintype ι] [Nonempty ι]`
  `(g : ι → ℝ) (hg : g ≠ 0) {eps : ℝ} (heps : 0 < eps) :`
  `0 < adamDot g (adamDir g (fun i => g i ^ 2) eps)`

  (координатно `⟨g, d⟩ = Σ g i ^ 2 / (|g i| + eps)`; при `0 ≤ eps` —
  `adam_first_step_dot_nonneg` :74). На шаге 2 это ломается:
  контрпример `ema_sign_flip_negative` (:125) при `β₁ = 9/10`,
  `β₂ = 999/1000`, `g₁ = 1`, `g₂ = −1/10` — после коррекции
  смещения `m̂₂ > 0`, поэтому

  `adamDot (fun _ : Fin 1 => (-1 : ℝ) / 10) (adamDir m̂₂ v̂₂ eps) < 0`

  — направление шага Adam образует с текущим градиентом тупой угол
  (`eps ≥ 0`). Скалярный вариант: `adam_step_not_always_descent`
  (:116).
- **Наглядность.** Adam спускается только на первом шаге:
  там направление совпадает с градиентом. Со второго шага
  направление — знак момента, а не градиента, и при смене знака
  градиента шаг может быть подъёмом; нужен явный приём шага
  (descent-проверка/backtracking), а не доверие оптимизатору.
- **Anchor.**
  `Hagi.Step.adam_first_step_dot_pos`
  (Hagi/Step/AdamDirection.lean:85);
  `adam_first_step_dot_nonneg` (:74);
  `ema_sign_flip_negative` (:125);
  `adam_step_not_always_descent` (:116); определения `ema` (:44),
  `adamCoord` (:49), `adamDir` (:53), `adamDot` (:57).
- **Dependencies.** Mathlib (Fintype, Real.sqrt, Finset.sum);
  внутренние определения модуля. Все константы конкретны
  (rationals, `norm_num`), без неконструктивных посылок.
- **Status.** Machine-checked (Lean 4.36); аксиомы: стандартные
  три Lean. Honest pins: β₁ = 0.9, β₂ = 0.999 — torch defaults,
  контрпример на скалярной координате (Fin 1); теорема о первом
  шаге — без коррекции смещения (m̂ = g, v̂ = g²), statement не
  утверждает ничего о шагах ≥ 2.
- **Category.** Optimization / machine learning (arXiv cs.LG,
  math.OC); MSC2020 90C25, 68T07.

## Card 16 — Codelength ↔ cross-entropy via Kraft

- **Statement.** Для конечного `X`, распределения `p` и
  однозначно декодируемого кода `enc : X → List Bool`:

  `theorem codelength_ge_entropy_of_uniquelyDecodable`
  `(p : X → ℝ) (enc : X → List Bool) [Nonempty X]`
  `(henc : Function.Injective enc)`
  `(hud : InformationTheory.IsUniquelyDecodable (Set.range enc))`
  `(hp : ∀ x, 0 ≤ p x) (hsum_p : ∑ x, p x = 1) :`
  `entBits p ≤ expLen p (fun x => (enc x).length)`

  — ожидаемая длина любого UD-кода не меньше H(p) в битах
  (через Kraft–McMillan из Mathlib). Для идеального кодера
  `idealLen q x = ⌈−log₂ (q x)⌉₊` (`:129`) с моделью `q`:

  `theorem idealLen_le_ce_add_one (p q : X → ℝ)`
  `(hp : ∀ x, 0 ≤ p x) (hsum_p : ∑ x, p x = 1)`
  `(hq : ∀ x, 0 < q x) (hq1 : ∀ x, q x ≤ 1) :`
  `expLen p (idealLen q) ≤ ceBits p q + 1`

  и разложение

  `theorem ceBits_eq_entBits_add_kl (p q : X → ℝ)`
  `(hp : ∀ x, 0 ≤ p x) (hpq : ∀ x, 0 < p x → 0 < q x) :`
  `ceBits p q = entBits p + klDef p q / Real.log 2`

  Частный случай `q = p` (`idealLen_self_bounds` :208):
  `H(p) ≤ E_p[⌈−log₂ p⌉₊] ≤ H(p) + 1`.
- **Наглядность.** Отношение сжатия модели равно её
  cross-entropy на данных (в битах/символ), плюс-минус один бит на
  символ из округления длин кодовых слов вверх; разница с идеалом —
  KL-расхождение модели от данных. Хорошая модель = хороший архиватор.
- **Anchor.**
  `Hagi.Theory.ArchiverCodeLength.codelength_ge_entropy_of_uniquelyDecodable`
  (Hagi/Theory/ArchiverCodeLength.lean:106);
  `idealLen_le_ce_add_one` (:164); `ceBits_eq_entBits_add_kl` (:194);
  `idealLen_self_bounds` (:208); определения `expLen` (:35),
  `entBits` (:38), `ceBits` (:41), `log2` (:126), `idealLen` (:129).
- **Dependencies.** Mathlib (`InformationTheory.IsUniquelyDecodable`,
  Kraft–McMillan); внутренние `ceDef`/`entDef`/`klDef` (KL =
  CE − H, `klDef_eq_ceDef_sub_of_support`).
- **Status.** Machine-checked (Lean 4.36); аксиомы: стандартные
  три Lean. Honest pins: классическая теория (Shannon/McMillan),
  ценность — формальный мост к архиватору; round-trip к реальному
  архиватору (L1: mixed/bitmask-код как UD-код) — только оценка
  (≥400 строк Lean), не формализован; `+1` — худший случай
  округления, не измеренное сжатие.
- **Category.** Information theory (arXiv cs.IT / math.IT);
  MSC2020 94A17, 94A24, 68P30.

## Card 17 — Useful first warm-up step: a new block pays from step
one iff there is residual signal

- **Statement.** Пусть `a < 0` — linear descent-сигнал нового
  блока, `R > 0` — range-константа направления, и drop
  `linDrop a R η = −(η·a + η²·R²/8)` (`stepEps = 1e-12`). Тогда:

  `theorem useful_eta_le {a R η : ℝ} (hR : R ≠ 0) :`
  `linDrop a R η ≤ 2 * a ^ 2 / R ^ 2`
  `∧ (linDrop a R η = 2 * a ^ 2 / R ^ 2 → η = -4 * a / R ^ 2)`

  `theorem exists_useful_eta {a R : ℝ} (ha : a < 0) (hR : 0 < R)`
  `(hmax : stepEps < 2 * a ^ 2 / R ^ 2) :`
  `∃ η : ℝ, 0 < η ∧ stepEps < linDrop a R η`

  и на носителе блока (`hlin : L (bη η) u − L b u = η·D u`,
  `hrange : ∀ u v, D u − D v ≤ R`, `a = Σ smax (L b) v · D v − D t`):

  `theorem first_step_strict_improves ... (hdesc : a < 0)`
  `(hmax : stepEps < 2 * a ^ 2 / R ^ 2) (h0 : Hagi.ceOneHot t (L b) = fOld) :`
  `∃ η : ℝ, 0 < η ∧ Hagi.ceOneHot t (L (bη η)) < fOld`

  Т.е. `η* = 4|a|/R²`, `drop_max = 2a²/R²`, максимум единственный; при
  `a = 0` drop `≤ 0` при любом η (`no_signal_no_drop`).
- **Наглядность.** Новый блок выгоден с первого шага тогда и только
  тогда, когда есть residual-сигнал: без него (`a = 0`) никакой шаг
  не даёт улучшения; при `a < 0` и `2a²/R² > stepEps` существует
  `η > 0` с сертифицированным строгим уменьшением CE — COMMIT
  первого шага тёплого блока (function-preserving старт: блок =
  identity, `CE = fOld`).
- **Anchor.**
  `Hagi.Theory.FunctionPreservingGrowth.useful_eta_le`
  (Hagi/Theory/FunctionPreservingGrowth.lean:597);
  `exists_useful_eta` (:616); `first_step_strict_improves` (:672);
  `first_step_useful_certified` (:637); `useful_first_step_pos` (:586);
  `no_signal_no_drop` (:625); определения `linDrop` (:575), `stepEps` (:391).
- **Dependencies.** Mathlib (softmax через `Hagi.Energy.smax`,
  CE `Hagi.ceOneHot`); контракт `CertifiedFiniteStep` и
  `block_step_commit_of_range_bound` модуля.
- **Status.** Machine-checked (Lean 4.36); аксиомы: стандартные
  три Lean. Witness (receipt C657): `a = −1`, `R = 2` → `η* = 1`,
  `drop_max = 1/2`; `a = 0` → COMMIT нет. Honest pin: U2
  (глобальная достижимость в невыпуклом случае) — OPEN, не
  доказано; statement — локальный первый шаг.
- **Category.** Learning theory / optimization (arXiv cs.LG,
  math.OC); MSC2020 68T05, 90C25.

---

## Card 18 — Muon step optimality without von Neumann

- **Statement.** Пусть `G ≠ 0` — действительная квадратная матрица,
  `normed G = (1/‖G‖_F)·G`, `ns_iter k` — `k` итераций схемы
  `X ↦ ½·X(3I − XᵀX)`. Тогда:

  `theorem muon_step_optimal_in_isometry_group (G : Matrix n n ℝ) :`
  `  (∀ Δ, Isometry Δ → fdot G Δ ≤ ssum G) ∧ ∃ Δ, Isometry Δ ∧ fdot G Δ = ssum G`

  `theorem muon_alignment_exact (G : Matrix n n ℝ) (k : ℕ) :`
  `  fdot G (ns_iter k G) = ∑ i, realSingularValues G i * ns_seq k (realSingularValues G i)`

  `theorem muon_near_optimal (G : Matrix n n ℝ)`
  `  (hnorm : ∀ i, realSingularValues G i ≤ 1) :`
  `  39 / 40 * ∑ i ∈ kept G, realSingularValues G i ≤ fdot G (ns_iter 3 G)`

  `theorem normed_near_optimal [Nonempty n] {G : Matrix n n ℝ} (hG : G ≠ 0) :`
  `  39 / 40 * ∑ i ∈ kept (normed G), realSingularValues (normed G) i`
  `    ≤ fdot (normed G) (ns_iter 3 (normed G))`

  где `fdot` — фробениусово скалярное произведение, `ssum` — сумма
  сингулярных чисел (nuclear norm), `kept` — индексы с `σ i ≥ 1/2`.
  Максимум `⟨G, Δ⟩` по группе изометрий `ΔᵀΔ = I` равен `‖G‖_*` и
  достигается на `U Vᵀ`; доказательство идёт через диагональ
  `Q = UᵀΔV` (изометрия ⇒ единичные столбцы ⇒ `Q i i ≤ 1`), без
  неравенства фон Неймана / спектрально-ядерной двойственности.
  Прямоугольное дополнение (C680–C681), `G : Matrix m n ℝ`,
  `card m ≤ card n`, `wnormed G = (1/‖G‖_F)•G`, `wide_iter k` — `k`
  итераций того же `ns_step` на `m×n`:

  `theorem wide_alignment_ge_gradient' (G : Matrix m n ℝ) (hmn) (hG : G ≠ 0) (k : ℕ) :`
  `  fdot_wide (wnormed G) (wnormed G) ≤ fdot_wide (wnormed G) (wide_iter k (wnormed G)) ∧`
  `    Real.sqrt (wfrobSq G) ≤ fdot_wide G (wide_iter k (wnormed G))`

  `theorem muon_step_useful_w1_rect (x b wo W1 t k) (hact) (hg : rowGrad … ≠ 0) (hx : x ≠ 0) (hmn) :`
  `  ∃ η, 0 < η ∧ ceOneHot t (w1L (fun i j => W1 i j - η * wide_iter k (wnormed G) i j) b wo x)`
  `    < ceOneHot t (w1L W1 b wo x)`

  где `G = w1GradR x b wo W1 t = −(g ⊗ x)` — градиент слоя `W1 : ι → δ → ℝ`
  кодовой размерности (`dim × hidden`, lm.py:586), `hmn : card ι ≤ card δ`;
  батч: `muon_step_useful_w1_rect_batch`. Высокий слой (C682):
  `fdot_transpose : fdot_wide Gᵀ Hᵀ = fdot_wide G H`,
  `wnormed_transpose : wnormed Gᵀ = (wnormed G)ᵀ`,
  `tall_alignment_ge_gradient : card n ≤ card m → G ≠ 0 → ‖G‖_F ≤ ⟨G, wide_iter k Ĝ⟩`
  (через `wide_iter_transpose` C680) и prime-версии без `hmn`:

  `theorem muon_step_useful_w1_rect' (x b wo W1 t k) (hact) (hg : rowGrad … ≠ 0) (hx : x ≠ 0) :`
  `  ∃ η, 0 < η ∧ ceOneHot t (w1L (fun i j => W1 i j - η * wide_iter k (wnormed G) i j) b wo x)`
  `    < ceOneHot t (w1L W1 b wo x)`

  батч: `muon_step_useful_w1_rect_batch'`; шаг теоремы = вывод кода
  (`w1StepR_eq_code_ns`, core.py:1358–1361).
- **Наглядность.** Идеальный шаг Muon (ортогонализованный градиент)
  — точный оптимум на группе изометрий; итерации Ньютона–Шульца
  сохраняют сингулярные векторы градиента, и три итерации дают не
  менее 39/40 оптимума на спектре `σ ≥ 1/2` — уже для той матрицы,
  которую код подаёт в итерацию (фробениусова нормировка).
- **Anchor.**
  `Hagi.Theory.MuonIsometry.muon_step_optimal_in_isometry_group`
  (Hagi/Theory/MuonIsometry.lean:175);
  `Hagi.Theory.MuonAlignment.muon_alignment_exact`
  (Hagi/Theory/MuonAlignment.lean:104); `muon_near_optimal` (:131);
  `Hagi.Theory.MuonDescent.normed_near_optimal`
  (Hagi/Theory/MuonDescent.lean:156); `normed_sigma_le_one` (:122);
  `Hagi.Theory.WideSVD.wide_alignment_ge_gradient'`
  (Hagi/Theory/WideSVD.lean:418);
  `Hagi.Theory.MuonDescentW1Rect.muon_step_useful_w1_rect`
  (Hagi/Theory/MuonDescentW1Rect.lean:134),
  `muon_step_useful_w1_rect_batch` (:203);
  `Hagi.Theory.MuonDescentW1Rect.tall_alignment_ge_gradient`
  (Hagi/Theory/MuonDescentW1Rect.lean:276),
  `alignment_ge_gradient_any` (:300), `muon_step_useful_w1_rect'`
  (:348), `muon_step_useful_w1_rect_batch'` (:369);
  определения `ns_iter` (Hagi/Theory/MuonAlignment.lean:86), `ns_p`
  (Hagi/Theory/NewtonSchulzSigma.lean:42), `ns_seq` (:45).
- **Dependencies.** Mathlib; собственный `smax_svd`
  (Hagi/Theory/MuonSpectral.lean) и SVD-файлы Flywheel
  (`Hagi.External.Flywheel.Matrix.SVD.Real`).
- **Status.** Machine-checked (Lean 4.36); аксиомы: стандартные
  три Lean. Honest: максимум по всему спектральному шару `‖Δ‖₂ ≤ 1`
  не доказан (нужен фон Неймана); слой `W1` любой формы покрыт с C682
  (версии C681 — при `card ι ≤ card δ`); `σ i < 1/2` после трёх итераций без
  нижней границы; `η` только существует; momentum (`m1`) и mean-лосс вне теории.
  Проверка ниши: в реестре нет backprop / trace-inequality /
  Muon формализаций — «niche 0/N» по данным receipts C668–C675
  (C668: 1351 entries, revision 1194, 0 cards по HasFDerivAt /
  fderiv / chain rule / backprop; C674: 0 по «muon / newton»);
  API в C677 не запрашивался.
- **Category.** Optimization / matrix analysis (arXiv math.OC,
  cs.LG); MSC2020 15A18 (singular values), 90C25, 68T05.

## Card 19 — Newton–Schulz quadratic defect 39/40

- **Statement.** Скалярная динамика итерации `X ↦ ½·X(3I − XᵀX)`:
  `ns_p t = t(3 − t²)/2`, `ns_seq 0 t = t`,
  `ns_seq (k+1) t = ns_p (ns_seq k t)`.

  `theorem ns_defect_bound {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1 / 2) (k : ℕ) :`
  `  1 - ns_seq k (1 - d) ≤ 2 / 3 * (3 / 4) ^ (2 ^ k)`

  `theorem ns_sigma_min_three {σ : ℝ} (h0 : 1 / 2 ≤ σ) (h1 : σ ≤ 1) :`
  `  39 / 40 ≤ ns_seq 3 σ`

  Дефект `d = 1 − σ` сжимается квадратично, `d ← d²(3 − d)/2`, с
  явной двойной экспонентой; три итерации поднимают `σ₀ ≥ 1/2` до
  `σ₃ ≥ 39/40`.
- **Наглядность.** Явная константа близости трёх итераций
  Ньютона–Шульца к полярному фактору: `1/2 → 11/16 → 1 − 1075/8192
  → ≈ 0.975300` (точная траектория от `1/2`, receipt C673).
- **Anchor.** `Hagi.Theory.NewtonSchulzSigma.ns_defect_bound`
  (Hagi/Theory/NewtonSchulzSigma.lean:83); `ns_sigma_min_three` (:126);
  `ns_quadratic_invariant` (:51); `ns_step_eigenvalue_sigma` (:200);
  определения `ns_p` (:42), `ns_seq` (:45).
- **Dependencies.** Mathlib; statement — только `ℝ`.
- **Status.** Machine-checked (Lean 4.36); аксиомы: стандартные
  три Lean. Honest: `σ₀ ≥ 1/2` — посылка; малые `σ` не поднимаются.
- **Category.** Numerical analysis / optimization (arXiv math.NA,
  cs.LG); MSC2020 65F25 (orthogonalization), 65H05.

---

## Submission requirements (что нужно для реальной отправки)

По /how-to-submit реестра, для каждой карточки требуется
выделенный comparator-проект:

1. Публичный GitHub-репозиторий + полный commit SHA снапшота.
2. `lakefile.toml` + `lean-toolchain` (pinned) +
   `lake-manifest.json`.
3. `Challenge.lean` — statement (≤300 строк желательно;
   импорты: Lean core + Mathlib/Tau Ceti only; `sorry`
   допустимы).
4. `Solution.lean` — proved-версия (те же имена/типы; аксиомы
   только `propext` / `Classical.choice` / `Quot.sound`).
5. `comparator.json` — список compared declarations.
6. `formalization.yaml` — авторы, лицензия, arXiv-категории,
   MSC2020, automation methods, honest narrative + limitations.
7. Форма на submit.palomar-registry.org (GitHub sign-in,
   доказательство write-доступа).

Honest limitations (для formalization.yaml):

- statements живут внутри большого исследовательского
  репозитория; для отправки нужен thin comparator-wrapper с
  выделенным Challenge/Solution;
- editorial floor реестра требует research-interest: лучшие
  кандидаты — Card 1 (EB bound), Card 5 (merge bound), Card 2
  (leak); Cards 4, 6, 8 элементарны — риск ниже floor;
- Palomar не подтверждает новизну: EB-граница имеет
  классические аналоги (Maurer–Pontil); наша версия —
  two-sided inverted с runtime-σ̂².
---

## Niche-recheck C630 (23.11.2026)

Повторение внешней проверки C616 против расширенного набора тем
(теперь включая floor / иерархию / w-trade-off / near-const /
mixed-w* / AM-GM — темы, которых в запросе C616 не было).

Метод: прямой fetch `data.palomar-registry.org/api/v1/results`.
API с C616 сменился на пагинацию (schema_version 1, revision
1129): полный обход 52 страниц по opaque-курсорам `next` →
1298 results / 987 projects (C616: 1293/983; +5 новых, ни одна
не в наших темах). Запросы `q=` по 19 темам (старые C616:
hier_covers, covStartsStep, nlDrop, adaptive span, optimal step
size, window coverage hierarchy; новые C630: window covering
floor, hierarchical attention coverage, context window cost
tradeoff, AM-GM window sizing, information-theoretic reading
bound, sliding window cost invariance, gamma star, negative
transfer, snap quantization, reading cost hierarchy, mixed cost)
плюс независимый локальный substring-скан полного дампа по 28
фразам карточек (title+abstract+preview+path).

Результат: 0 тематических пересечений — ниша подтверждена.
Размытые single-word срабатывания проверены чтением и
нерелевантны: "gamma star" → Mahler minimizers (слово "star");
"negative transfer" → Bugeaud 10.61 (u.d. mod 1);
"mixed cost" → optimal control / packing relaxation;
"am-gm" → некоммутативный AM-GM для PSD-матриц;
"quantization" → Poisson scales / stochastic quantization SPDE;
"floor" (62 вхождения) — floor-функция в чужих текстах, ни
одного про окно чтения/бюджет.

Отличие от C616: расширенный охват тем (все 13 карточек, включая
Cards 9–13 чтение-эры), два независимых метода проверки (API q=
и локальный скан полного дампа сошлись), учёт смены формата API
(пагинация вместо единого дампа). Все 13 карточек внешне
уникальны; отправка остаётся user-шагом. Артефакты:
`.tmp/C630/api/` (results.json, all_entries.json — 1298 записей,
query_summary.json, llms.txt), `.tmp/C630/research.md`.


---

## Niche-recheck C658 (24.11.2026)

Повторение внешней проверки C630 против тем Cards 15–17 (Adam
first step / sign-flip momentum, Kraft codelength ↔ cross-entropy,
useful first warm-up step function-preserving growth; Cards 18–19
Muon / Newton–Schulz — по данным receipts C668–C675, без нового
fetch) плюс прежние
24 темы C630 (muon, newton schulz, orthogonalization, singular value,
 polar factor, nuclear norm, spectral norm, isometry: по данным
 receipts C668–C675 — 0 тематических; в C677 API не запрашивался).

Метод: полный обход `data.palomar-registry.org/api/v1/results`
(curl --http1.1; urllib на этой машине рвёт TLS — WinError 10054)
по opaque-курсорам `next` → 54 страницы, 1331 results / 1011
projects, revision 1167 (C630: 1298 / 987, revision 1129; +33
новых). Три независимых прохода: (1) API `q=` по 24 фразам
(многословные — AND-семантика, все 7 новых фраз → 0 hits);
(2) API `q=` по 10 одиночным терминам (adam, momentum, kraft,
entropy, codelength, decodable, descent, warm, preserving,
optimizer); (3) локальный word-boundary substring-скан полного
дампа (title + abstract + preview + path + theorem_names) по 24
фразам карточек.

| Тема | q= фраза | Локальный скан | Вердикт |
| --- | --- | --- | --- |
| Adam first step descent | 0 | adam 0 (word) | нет |
| sign flip momentum | 0 | sign flip 0; momentum 3 | нет |
| Kraft entropy codelength | 0 | kraft 0, mcmillan 0, entropy 16 | нет |
| cross entropy arithmetic coding | 0 | cross entropy 0, arithmetic coding 0 | нет |
| warm start new block | 0 | warm start / warm-up / warmup 0 | нет |
| function preserving growth | 0 | function preserving 0, net2net 0 | нет |
| first step improvement | 0 | first step 3 | нет |
| прежние 17 тем C630 | 3 размытых (gamma star, negative transfer, mixed cost) | — | нет (как в C630) |

Размытые срабатывания прочитаны (abstract) и нерелевантны:
"adam" (API, 5) — substring в чужих текстах (Schur/Rademacher),
word-boundary 0; "momentum" (3) — угловой момент в PONTRYAGIN /
электродинамика / радиальные harmonic functions; "entropy" (16–17)
— топологическая/Rényi/Latin squares/spin glass, ни одного про
codelength; "descent" (18) — infinite descent в теории чисел,
Collatz, Галуа; ближайшие к теме — PALOMAR-2026-10-12-000006
(last-iterate bounds constant-step GD) и PALOMAR-2026-11-14-000001
(SGD last-iterate WR/WOR): bounds на последний итерат для convex
smooth, не про направление Adam и не про первый шаг блока —
нерелевантны; "optimizer" (3–4) — optimizers в геометрии /
экономике; "first step" (3) — первый шаг доказательства (Selmer,
Bogolyubov–Ruzsa), MCS ordering; "warm" (1) — "warm pump-to-hard-OA
composition" (MIP: warm start без reinitialization), не ML-block;
"preserving" (25) — diameter/measure/value-preserving, не
function-preserving рост сетей.

Результат: 0 тематических пересечений — ниша всех 17 карточек
подтверждена; отправка остаётся user-шагом. Артефакты:
`.tmp/C658/api/` (all_entries.json — 1331 записей,
query_summary.json, api_terms.json, local_phrase_scan.json,
fetch.py).
