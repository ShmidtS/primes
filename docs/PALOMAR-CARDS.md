# Palomar-cards — C5XX-теория как кандидаты для реестра Lean-результатов

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

Этот файл — подготовительные карточки (draft entries) тринадцати
machine-checked результатов C5XX-витков: самодостаточные
математические формулировки без контекстной терминологии,
точные FQN-якоря и честный статус. Все доказательства
проверены Lean 4.36 (pinned Mathlib, см. lake-manifest.json);
гейт `testallax` подтверждает: только стандартные три аксиомы
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
  (Hagi/Theory/WeightDecayLeak.lean:128); сопутствующая
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
  `ce_pointwise_of_prob_one` (:66).
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
  (Hagi/Optimization/PolarExpressCert.lean:403);
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
  (Hagi/Theory/AdapterGrowth.lean:142); `adapter_param_count`
  (:122), `block_param_count` (:134),
  `adapter_param_count_lt_block` (:149).
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
  (Hagi/Theory/CoverageReading.lean:283);
  `hier_peak_window_budget` (:317); определения `hierBlockLen`
  (:270), `hierStarts` (:275).
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
  `covStartsStep_len_le` (:219);
  `covStartsStep_adaptive_covers` (:232).
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
  (`hier_total_min` :468):

  `theorem hier_total_min (n B w : ℕ) (hw : 0 < w) (hB : 0 < B)`
  `(hdiv : w ∣ B) :`
  `(hierStarts n B w w).length = (n + w - 1) / w`

  замыкая оптимум (`hier_optimal` :539): total иерархии = ⌈n/w⌉
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
  (Hagi/Theory/CoverageReading.lean:496);
  `hier_total_min` (:468); `hier_optimal` (:539);
  `hier_total_formula` (:446); `hier_blocks_sum_tiling` (:395);
  `covStartsStep_len_tiling` (:360); определения `hierBlockLen`
  (:270), `hierStarts` (:275).
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
  (обе границы `windowCost_linear_bounds` :86: n ≤ w·⌈n/w⌉ ≤
  n + w − 1 — total зажат в [c·n, c·(n+w))). Контраст — режим
  (a) фиксированной стоимости `windowCost_fixed_mono` :77: при
  c(w) = c totalCost(w) = c·⌈n/w⌉ монотонно невозрастает по w
  (ядро `ceil_div_anti` :55) — оптимально w = w_max. Мост к
  иерархии C618: `windowCost_hier` :113 (total = ⌈n/w⌉ при
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
  (Hagi/Theory/CoverageReading.lean:594);
  `windowCost_linear_bounds` (:581);
  `windowCost_fixed_mono` (:572); `ceil_div_anti` (:550);
  `windowCost_hier` (:608).
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
  (`growth_gate_stay_char` :81: `growthGate pb c = false ↔ pb ≤ c`).
  MAIN (`growth_gate_sound` :178, CERTIFIED-STAY): если потолок
  возможного выигрыша n-шагового дообучения

  `theorem growth_gate_sound ... (hc : n * (G ^ 2 / (2 * L)) ≤ cAdd) :`
  `f z - f (nlRun n (1 / L) grad z) ≤ cAdd`

  т.е. при `n·G²/(2L) ≤ c_add` ЛЮБОЕ n-шаговое дообучение (в т.ч.
  с добавленной ёмкостью) уменьшает objective не более чем на
  `c_add` — рост НЕ может окупиться за n шагов. Ядро:
  `nl_drop_total` :121 — телескоп-индукция, drop за n шагов ≤
  `n·G²/(2L)` (per-step `nl_drop_step_eq` :109 = C606
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
  (Hagi/Theory/NegativeTransfer.lean:574, namespace внутри модуля);
  `growth_gate_stay_char` (:580); `nl_drop_step_eq` (:608);
  `nl_drop_total` (:620); `growth_gate_sound` (:677).
  Потребители: `Hagi.Budget.WaterFilling` (WaterFilling.lean:366),
  `Hagi.Probability.GibbsCore` (GibbsCore.lean:1416).
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
