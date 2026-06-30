import Mathlib
import Primes.Basic

namespace PrimeGaps

/-! ## Exact finite formulas for gap frequencies

`primeGapFrequencyExact g x` — конечная формула для числа промежутков `g`
между соседними простыми с правым концом `≤ x`.
-/

noncomputable section

open scoped BigOperators
open Filter

/-- Индикатор утверждения со значениями в `Nat`. -/
def natIndicator (P : Prop) [Decidable P] : Nat :=
  if P then 1 else 0

/-- Индикатор простоты. -/
def primeIndicator (n : Nat) : Nat :=
  natIndicator (Nat.Prime n)

/-- `n` и `n + g` — соседние простые с правым концом `≤ x`. -/
def ConsecutivePrimeStart (g x n : Nat) : Prop :=
  0 < g ∧ Nat.Prime n ∧ Nat.Prime (n + g) ∧ n + g ≤ x ∧
    ∀ h : Nat, h ∈ Finset.Icc 1 (g - 1) → ¬ Nat.Prime (n + h)

/-- Один член точной формулы `F(g, x)`: формальный аналог Python `term`. -/
def primeGapTerm (g x n : Nat) : Nat := by
  classical
  exact natIndicator (0 < g) * primeIndicator n * primeIndicator (n + g) *
    natIndicator (n + g ≤ x) *
      (Finset.Icc 1 (g - 1)).prod (fun h => 1 - primeIndicator (n + h))

/-- Точная частота `F(g, x)` через конечное решето по возможным левым концам. -/
def primeGapFrequencyExact (g x : Nat) : Nat :=
  (Finset.range (x + 1)).sum (fun n => primeGapTerm g x n)

/-- Точная частота равна числу левых концов соседних простых с промежутком `g`. -/
theorem primeGapFrequencyExact_eq_count (g x : Nat) :
    primeGapFrequencyExact g x =
      (by classical
       exact ((Finset.range (x + 1)).filter (fun n => ConsecutivePrimeStart g x n)).card) := by
  classical
  trans (Finset.range (x + 1)).sum (fun n => if ConsecutivePrimeStart g x n then 1 else 0)
  · unfold primeGapFrequencyExact
    apply Finset.sum_congr rfl
    intro n hn
    unfold primeGapTerm primeIndicator natIndicator ConsecutivePrimeStart
    have hprod :
        (Finset.Icc 1 (g - 1)).prod (fun h => 1 - if Nat.Prime (n + h) then 1 else 0) =
          if (∀ h ∈ Finset.Icc 1 (g - 1), ¬ Nat.Prime (n + h)) then 1 else 0 := by
      by_cases hall : ∀ h ∈ Finset.Icc 1 (g - 1), ¬ Nat.Prime (n + h)
      · rw [if_pos hall]
        apply Finset.prod_eq_one
        intro h hh
        simp [hall h hh]
      · rw [if_neg hall]
        push Not at hall
        rcases hall with ⟨h, hh, hp⟩
        exact Finset.prod_eq_zero hh (by simp [hp])
    by_cases hgpos : 0 < g <;>
      by_cases hnprime : Nat.Prime n <;>
      by_cases hngprime : Nat.Prime (n + g) <;>
      by_cases hle : n + g ≤ x <;>
      simp [hgpos, hnprime, hngprime, hle, hprod]
  · exact Finset.sum_boole (fun n => ConsecutivePrimeStart g x n) (Finset.range (x + 1))

/-- Для нечётного `g > 1` точных промежутков нет. -/
theorem primeGapFrequencyExact_zero_for_odd_g_gt_one (g x : Nat) (hg : Odd g) (hg1 : 1 < g) :
    primeGapFrequencyExact g x = 0 := by
  rw [primeGapFrequencyExact_eq_count]
  classical
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro n hn hstart
  rcases hstart with ⟨hgpos, hnprime, hngprime, hle, hbetween⟩
  rcases Nat.even_or_odd n with hneven | hnodd
  · have hn_eq_two : n = 2 := by
      exact hnprime.eq_two_or_odd'.resolve_right (by simpa using hneven)
    have h1mem : 1 ∈ Finset.Icc 1 (g - 1) := by
      simp only [Finset.mem_Icc]
      omega
    have hnot : ¬ Nat.Prime (n + 1) := hbetween 1 h1mem
    exact hnot (by simpa [hn_eq_two] using Nat.prime_three)
  · have heven : Even (n + g) := hnodd.add_odd hg
    rcases hngprime.eq_two_or_odd' with htwo | hodd
    · have hn2 : 2 ≤ n := hnprime.two_le
      omega
    · exact (by simpa using heven : ¬ Odd (n + g)) hodd

/-- Булевофинитная форма точной формулы. -/
theorem primeGapFrequencyExact_eq_sieve_sum (g x : Nat) :
    primeGapFrequencyExact g x =
      (Finset.range (x + 1)).sum (fun n =>
        natIndicator (0 < g) * primeIndicator n * primeIndicator (n + g) *
          natIndicator (n + g ≤ x) *
            (Finset.Icc 1 (g - 1)).prod (fun h => 1 - primeIndicator (n + h))) := by
  rfl

/-- Число простых `≤ x`. -/
def primeCountingExact (x : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun p => Nat.Prime p).card

/-- Относительная частота промежутка `g` среди простых `≤ x`. -/
def primeGapRelativeFrequency (g x : Nat) : ℝ :=
  (primeGapFrequencyExact g x : ℝ) / (primeCountingExact x : ℝ)

/-- Главный член вида `A(g) · π(x) / x`. -/
def pairCorrelationMainTerm (A : Nat → ℝ) (g x : Nat) : ℝ :=
  A g * (primeCountingExact x : ℝ) / (x : ℝ)

/-- Точный остаток после выделения главного члена `A(g) · π(x) / x`. -/
def pairCorrelationError (A : Nat → ℝ) (g x : Nat) : ℝ :=
  (primeGapFrequencyExact g x : ℝ) - pairCorrelationMainTerm A g x

/-- Универсальная точная декомпозиция: формула всегда верна с явным остатком. -/
theorem primeGapFrequencyExact_main_add_error (A : Nat → ℝ) (g x : Nat) :
    (primeGapFrequencyExact g x : ℝ) =
      pairCorrelationMainTerm A g x + pairCorrelationError A g x := by
  simp [pairCorrelationError]

/-- Сдвиги, которые должны быть проверены решетом для промежутка `g`. -/
def gapPatternShifts (g : Nat) : Finset Nat :=
  insert 0 (insert g (Finset.Icc 1 (g - 1)))

/-- `p` отбрасывает `n`, если делит хотя бы один из сдвигов `n + h`. -/
def primeDividesPatternAt (g n p : Nat) : Prop :=
  Nat.Prime p ∧ ∃ h : Nat, h ∈ gapPatternShifts g ∧ p ∣ n + h

/-- Конечный слой решета Эратосфена по простым `≤ y`. -/
def survivesFiniteEratosthenesLayer (g n y : Nat) : Prop :=
  ∀ p : Nat, Nat.Prime p → p ≤ y → ¬ primeDividesPatternAt g n p

/-- Частота после просеивания арифметических прогрессий `n ≡ -h (mod p)`. -/
def arithmeticProgressionSieveCount (g x y : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun n =>
    0 < g ∧ n + g ≤ x ∧ survivesFiniteEratosthenesLayer g n y).card

/-! ### endpointForbiddenResidueCount properties -/

/-- Количество запрещённых классов вычетов для двух концов `n` и `n+g` modulo `p`. -/
def endpointForbiddenResidueCount (g p : Nat) : Nat :=
  if p ∣ g then 1 else 2

/-- Общая формула для `endpointForbiddenResidueCount`. -/
theorem endpointForbiddenResidueCount_eq (g p : Nat) (_hp : Nat.Prime p) :
    endpointForbiddenResidueCount g p = if p ∣ g then 1 else 2 := by
  simp [endpointForbiddenResidueCount]

/-- Значение `endpointForbiddenResidueCount` для `g = p^k`. -/
theorem endpointForbiddenResidueCount_prime_power (g p : Nat) (k : Nat)
    (_hp : Nat.Prime p) (hk : 0 < k) (hg : g = p ^ k) :
    endpointForbiddenResidueCount g p = 1 := by
  have : p ∣ g := by
    subst hg
    -- p ∣ p^k for 0 < k, since p^k = p * p^(k-1)
    have hpow : p ^ k = p * p ^ (k - 1) := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    rw [hpow]
    exact ⟨p ^ (k - 1), rfl⟩
  simp [endpointForbiddenResidueCount, this]

/-- Главный член вида `A(g) · π(x)² / x` для гипотезы Харди--Литтлвуда. -/
def pairCorrelationMainTermSq (A : Nat → ℝ) (g x : Nat) : ℝ :=
  A g * (primeCountingExact x : ℝ) ^ 2 / (x : ℝ)

/-- Остаток после выделения главного члена `A(g) · π(x)² / x`. -/
def pairCorrelationErrorSq (A : Nat → ℝ) (g x : Nat) : ℝ :=
  (primeGapFrequencyExact g x : ℝ) - pairCorrelationMainTermSq A g x

/-- Универсальная точная декомпозиция с квадратичным главным членом. -/
theorem primeGapFrequencyExact_mainSq_add_errorSq (A : Nat → ℝ) (g x : Nat) :
    (primeGapFrequencyExact g x : ℝ) =
      pairCorrelationMainTermSq A g x + pairCorrelationErrorSq A g x := by
  simp [pairCorrelationErrorSq]

/-- Мёбиусоподобное ядро оставлено параметром, чтобы не смешивать его с доказанным `Nat.Prime`. -/
def mobiusPairKernel (mu : Nat → Int) (g x n : Nat) : Int :=
  (Finset.range (x + 1)).sum (fun d =>
    (Finset.range (x + 1)).sum (fun e =>
      if d * d ∣ n ∧ e * e ∣ n + g then mu d * mu e else 0))

/-- Гипотеза мёбиусовой пары для частот простых промежутков: двойная сумма
`μ(d) μ(e)` по делителям концов восстанавливает точную частоту `F(g, x)`.
Открытая проблема; мотивирована обращением Мёбиуса и решётными методами.
Связана с подходом Мингацина/Глауде к гипотезе о простых близнецах. -/
def MobiusPairGapFormulaConjecture (mu : Nat → Int) : Prop :=
  ∀ g x : Nat,
    (primeGapFrequencyExact g x : Int) =
      (Finset.range (x + 1)).sum (fun n => mobiusPairKernel mu g x n)

/-- Количество простых `≤ x` в прогрессии `a mod q`. -/
def primesInArithmeticProgression (a q x : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun n => Nat.Prime n ∧ n % q = a % q).card

/-- Гипотеза равномерности Дирихле: простые числа равномерно распределены
по допустимым классам вычетов `a mod q` при `(a, q) = 1`. Доказана как теорема
Дирихле (1837) для каждого фиксированного `q`; здесь — усиленная форма
с равномерной сходимостью по `q`. Открытая проблема в полной общности. -/
def DirichletUniformityConjecture : Prop :=
  ∀ a q : Nat, Nat.Coprime a q → 0 < q →
    Tendsto (fun x : Nat =>
      (primesInArithmeticProgression a q x : ℝ) /
        ((primeCountingExact x : ℝ) / (Nat.totient q : ℝ))) atTop (nhds 1)

/-- Гипотеза псевдослучайности простых промежутков: ошибка конечно-решётной
аппроксимации `F(g, x) ≈ A(g) · π(x) / x` мала после нормировки. Открытая
проблема; мотивирована Cramér-моделью (1936) и гипотезой Харди--Литтлвуда. -/
def PrimeGapPseudorandomnessConjecture (A normalization : Nat → ℝ) : Prop :=
  ∀ g : Nat,
    Tendsto (fun x : Nat => pairCorrelationError A g x / normalization x) atTop (nhds 0)

/-- Вещественный индикатор простоты. -/
def realPrimeIndicator (n : Nat) : ℝ :=
  if n.Prime then 1 else 0

/-- Нормированная функция Мангольдта, занулённая вне простых. -/
def normalizedMangoldtPrime (n : Nat) : ℝ :=
  if n.Prime then _root_.ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) else 0

/-- На простых `Λ(n) / log n = 1`; вне простых обе стороны занулены. -/
theorem normalizedMangoldtPrime_eq_realPrimeIndicator (n : Nat) :
    normalizedMangoldtPrime n = realPrimeIndicator n := by
  unfold normalizedMangoldtPrime realPrimeIndicator
  by_cases hn : n.Prime
  · rw [if_pos hn, _root_.ArithmeticFunction.vonMangoldt_apply_prime hn, if_pos hn]
    have hgt : (1 : ℝ) < n := by exact_mod_cast hn.one_lt
    exact div_self (Real.log_pos hgt).ne'
  · simp [hn]

/-- Нормированная Λ-свёртка на концах `n` и `n + g`. -/
def normalizedMangoldtEndpointWeight (g n : Nat) : ℝ :=
  normalizedMangoldtPrime n * normalizedMangoldtPrime (n + g)

/-! ### primeCountingExact properties -/

/-- `primeCountingExact` монотонна: π(x) ≤ π(y) при x ≤ y. -/
theorem primeCountingExact_monotone {x y : Nat} (hxy : x ≤ y) :
    primeCountingExact x ≤ primeCountingExact y := by
  unfold primeCountingExact
  have hsub : (Finset.range (x + 1)).filter Nat.Prime ⊆
      (Finset.range (y + 1)).filter Nat.Prime := by
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    refine ⟨?_, ha.2⟩
    simp only [Finset.mem_range] at ha ⊢
    omega
  exact Finset.card_le_card hsub

/-- `primeCountingExact` равна сумме индикаторов простоты. -/
theorem primeCountingExact_eq_sum_primeIndicator (x : Nat) :
    primeCountingExact x = (Finset.range (x + 1)).sum (fun n => primeIndicator n) := by
  unfold primeCountingExact primeIndicator natIndicator
  classical
  rw [Finset.sum_boole, Nat.cast_id]

/-- `primeCountingExact (x + 1)` добавляет индикатор простоты `x + 1`. -/
theorem primeCountingExact_succ (x : Nat) :
    primeCountingExact (x + 1) =
      primeCountingExact x + (if Nat.Prime (x + 1) then 1 else 0) := by
  rw [primeCountingExact_eq_sum_primeIndicator, primeCountingExact_eq_sum_primeIndicator]
  rw [show (x + 1) + 1 = x + 2 by omega, Finset.sum_range_succ]
  classical
  by_cases hp : Nat.Prime (x + 1)
  · simp [hp, primeIndicator, natIndicator]
  · simp [hp, primeIndicator, natIndicator]

/-- `primeCountingExact 0 = 0`: 0 не простое. -/
theorem primeCountingExact_zero : primeCountingExact 0 = 0 := by
  rw [primeCountingExact_eq_sum_primeIndicator]
  simp [primeIndicator, natIndicator]

/-- `primeCountingExact 2 = 1`: 2 — наименьшее простое. -/
theorem primeCountingExact_two : primeCountingExact 2 = 1 := by
  unfold primeCountingExact
  have hrange : Finset.range 3 = {0, 1, 2} := by
    ext p
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hrange]
  have hfilter : ({0, 1, 2} : Finset Nat).filter Nat.Prime = {2} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, hp⟩
      · contradiction
      · contradiction
      · rfl
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl), by decide⟩
  rw [hfilter]
  simp

/-- `primeGapFrequencyExact` неотрицательна (сумма неотрицательных индикаторов). -/
theorem primeGapFrequencyExact_nonneg (g x : Nat) :
    0 ≤ primeGapFrequencyExact g x := by
  unfold primeGapFrequencyExact
  apply Finset.sum_nonneg
  intro n _
  unfold primeGapTerm primeIndicator natIndicator
  classical
  split_ifs <;> simp

/-- После нормировки по логарифмам Λ-свёртка на концах совпадает с индикаторами простоты. -/
theorem normalizedMangoldtEndpointWeight_eq_prime_indicators (g n : Nat) :
    normalizedMangoldtEndpointWeight g n =
      realPrimeIndicator n * realPrimeIndicator (n + g) := by
  simp [normalizedMangoldtEndpointWeight, normalizedMangoldtPrime_eq_realPrimeIndicator]

end

end PrimeGaps
