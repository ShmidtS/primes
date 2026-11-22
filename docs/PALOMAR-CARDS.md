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

Этот файл — подготовительные карточки (draft entries) восьми
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
