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
def natIndicator (P : Prop) [Decidable P] : Nat := if P then 1 else 0

/-- Индикатор простоты. -/
def primeIndicator (n : Nat) : Nat := natIndicator (Nat.Prime n)

/-- `n` и `n + g` — соседние простые с правым концом `≤ x`. -/
def ConsecutivePrimeStart (g x n : Nat) : Prop :=
  0 < g ∧ Nat.Prime n ∧ Nat.Prime (n + g) ∧ n + g ≤ x ∧
    ∀ h : Nat, h ∈ Finset.Icc 1 (g - 1) → ¬ Nat.Prime (n + h)

/-- Один член точной формулы `F(g, x)`. -/
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
        exact Finset.prod_eq_one (fun h hh => by simp [hall h hh])
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

/-- Для нечётного `g > 1` точных промежутков нет (оба конца не могут быть простыми). -/
theorem primeGapFrequencyExact_zero_for_odd_g_gt_one (g x : Nat) (hg : Odd g) (hg1 : 1 < g) :
    primeGapFrequencyExact g x = 0 := by
  rw [primeGapFrequencyExact_eq_count]
  classical
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro n _ ⟨hgpos, hnprime, hngprime, hle, hbetween⟩
  rcases Nat.even_or_odd n with hneven | hnodd
  · have hn2 : n = 2 := hnprime.eq_two_or_odd'.resolve_right (by simpa using hneven)
    exact hbetween 1 (Finset.mem_Icc.mpr (by omega)) (by simpa [hn2] using Nat.prime_three)
  · have heven : Even (n + g) := hnodd.add_odd hg
    rcases hngprime.eq_two_or_odd' with htwo | hodd
    · have hn2 : 2 ≤ n := hnprime.two_le; omega
    · exact (by simpa using heven : ¬ Odd (n + g)) hodd

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

/-- Точный остаток после выделения главного члена. -/
def pairCorrelationError (A : Nat → ℝ) (g x : Nat) : ℝ :=
  (primeGapFrequencyExact g x : ℝ) - pairCorrelationMainTerm A g x

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

/-! ### endpointForbiddenResidueCount -/

/-- Количество запрещённых классов вычетов для двух концов `n` и `n+g` modulo `p`. -/
def endpointForbiddenResidueCount (g p : Nat) : Nat :=
  if p ∣ g then 1 else 2

/-- Значение `endpointForbiddenResidueCount` для `g = p^k`. -/
theorem endpointForbiddenResidueCount_prime_power (g p : Nat) (k : Nat)
    (_hp : Nat.Prime p) (hk : 0 < k) (hg : g = p ^ k) :
    endpointForbiddenResidueCount g p = 1 := by
  have : p ∣ g := by
    subst hg
    have hpow : p ^ k = p * p ^ (k - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    rw [hpow]; exact ⟨p ^ (k - 1), rfl⟩
  simp [endpointForbiddenResidueCount, this]

/-! ### Mobius pair and Dirichlet conjectures -/

/-- Мёбиусоподобное ядро. -/
def mobiusPairKernel (mu : Nat → Int) (g x n : Nat) : Int :=
  (Finset.range (x + 1)).sum (fun d =>
    (Finset.range (x + 1)).sum (fun e =>
      if d * d ∣ n ∧ e * e ∣ n + g then mu d * mu e else 0))

/-- Гипотеза мёбиусовой пары для частот простых промежутков. Открытая проблема;
мотивирована обращением Мёбиуса и решётными методами. -/
def MobiusPairGapFormulaConjecture (mu : Nat → Int) : Prop :=
  ∀ g x : Nat,
    (primeGapFrequencyExact g x : Int) =
      (Finset.range (x + 1)).sum (fun n => mobiusPairKernel mu g x n)

/-- Количество простых `≤ x` в прогрессии `a mod q`. -/
def primesInArithmeticProgression (a q x : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun n => Nat.Prime n ∧ n % q = a % q).card

/-- Гипотеза равномерности Дирихле: простые равномерно распределены
по допустимым классам вычетов `a mod q` при `(a, q) = 1`. Открытая проблема. -/
def DirichletUniformityConjecture : Prop :=
  ∀ a q : Nat, Nat.Coprime a q → 0 < q →
    Tendsto (fun x : Nat =>
      (primesInArithmeticProgression a q x : ℝ) /
        ((primeCountingExact x : ℝ) / (Nat.totient q : ℝ))) atTop (nhds 1)

/-- Гипотеза псевдослучайности простых промежутков. Открытая проблема;
мотивирована Cramér-моделью (1936) и гипотезой Харди--Литтлвуда. -/
def PrimeGapPseudorandomnessConjecture (A normalization : Nat → ℝ) : Prop :=
  ∀ g : Nat,
    Tendsto (fun x : Nat => pairCorrelationError A g x / normalization x) atTop (nhds 0)

/-! ### Normalized Mangoldt and prime indicators -/

/-- Вещественный индикатор простоты. -/
def realPrimeIndicator (n : Nat) : ℝ := if n.Prime then 1 else 0

/-- Нормированная функция Мангольдта, занулённая вне простых. -/
def normalizedMangoldtPrime (n : Nat) : ℝ :=
  if n.Prime then _root_.ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) else 0

/-- На простых `Λ(n) / log n = 1`; вне простых обе стороны занулены. -/
theorem normalizedMangoldtPrime_eq_realPrimeIndicator (n : Nat) :
    normalizedMangoldtPrime n = realPrimeIndicator n := by
  unfold normalizedMangoldtPrime realPrimeIndicator
  by_cases hn : n.Prime
  · rw [if_pos hn, _root_.ArithmeticFunction.vonMangoldt_apply_prime hn, if_pos hn]
    exact div_self (Real.log_pos (by exact_mod_cast hn.one_lt)).ne'
  · simp [hn]

/-- Нормированная Λ-свёртка на концах `n` и `n + g`. -/
def normalizedMangoldtEndpointWeight (g n : Nat) : ℝ :=
  normalizedMangoldtPrime n * normalizedMangoldtPrime (n + g)

/-- После нормировки по логарифмам Λ-свёртка совпадает с индикаторами простоты. -/
theorem normalizedMangoldtEndpointWeight_eq_prime_indicators (g n : Nat) :
    normalizedMangoldtEndpointWeight g n =
      realPrimeIndicator n * realPrimeIndicator (n + g) := by
  simp [normalizedMangoldtEndpointWeight, normalizedMangoldtPrime_eq_realPrimeIndicator]

/-! ### primeCountingExact properties -/

/-- `primeCountingExact` монотонна: π(x) ≤ π(y) при x ≤ y. -/
theorem primeCountingExact_monotone {x y : Nat} (hxy : x ≤ y) :
    primeCountingExact x ≤ primeCountingExact y := by
  unfold primeCountingExact
  refine Finset.card_le_card ?_
  intro a ha
  simp only [Finset.mem_filter] at ha ⊢
  refine ⟨?_, ha.2⟩
  simp only [Finset.mem_range] at ha ⊢
  omega

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
  by_cases hp : Nat.Prime (x + 1) <;> simp [hp, primeIndicator, natIndicator]

/-- `primeGapFrequencyExact` неотрицательна. -/
theorem primeGapFrequencyExact_nonneg (g x : Nat) :
    0 ≤ primeGapFrequencyExact g x := by
  unfold primeGapFrequencyExact primeGapTerm primeIndicator natIndicator
  classical
  apply Finset.sum_nonneg
  intro n _
  split_ifs <;> simp

/-! ### Consecutive prime pair injectivity

Ключевая комбинаторная теорема: отображение (g, n) ↦ n + g, сопоставляющее
паре соседних простых их правый конец, инъективно. Это означает, что
каждое простое p > 2 является правым концом не более одной пары соседних
простых. Следствие: сумма частот всех промежутков не превосходит π(x) - 1.
-/

/-- Если (n₁, n₁+g₁) и (n₂, n₂+g₂) — пары соседних простых с одним правым концом,
то n₁ = n₂. Доказательство от противного: если n₁ < n₂, то n₂ — простое,
лежящее строго между n₁ и n₁+g₁, что противоречит условию отсутствия простых
внутри первого промежутка. -/
theorem ConsecutivePrimeStart_left_injective
    {g₁ g₂ n₁ n₂ x : Nat}
    (h1 : ConsecutivePrimeStart g₁ x n₁)
    (h2 : ConsecutivePrimeStart g₂ x n₂)
    (heq : n₁ + g₁ = n₂ + g₂) : n₁ = n₂ := by
  by_cases hlt : n₁ < n₂
  · have hg₁_pos : 0 < g₁ := h1.1
    have hg₂_pos : 0 < g₂ := h2.1
    have hn₂_prime : Nat.Prime n₂ := h2.2.1
    have hdiff_pos : 0 < n₂ - n₁ := by omega
    have hdiff_lt : n₂ - n₁ < g₁ := by omega
    have hmem : n₂ - n₁ ∈ Finset.Icc 1 (g₁ - 1) := Finset.mem_Icc.mpr (by omega)
    have hforbidden : ¬ Nat.Prime (n₁ + (n₂ - n₁)) := h1.2.2.2.2 _ hmem
    have : n₁ + (n₂ - n₁) = n₂ := by omega
    rw [this] at hforbidden
    exact absurd hn₂_prime hforbidden
  · by_cases hgt : n₂ < n₁
    · have hg₂_pos : 0 < g₂ := h2.1
      have hg₁_pos : 0 < g₁ := h1.1
      have hn₁_prime : Nat.Prime n₁ := h1.2.1
      have hdiff_pos : 0 < n₁ - n₂ := by omega
      have hdiff_lt : n₁ - n₂ < g₂ := by omega
      have hmem : n₁ - n₂ ∈ Finset.Icc 1 (g₂ - 1) := Finset.mem_Icc.mpr (by omega)
      have hforbidden : ¬ Nat.Prime (n₂ + (n₁ - n₂)) := h2.2.2.2.2 _ hmem
      have : n₂ + (n₁ - n₂) = n₁ := by omega
      rw [this] at hforbidden
      exact absurd hn₁_prime hforbidden
    · omega

/-- Правый конец пары соседних простых строго больше 2:
n ≥ 2 (простое), g > 0, значит n + g > 2. -/
theorem ConsecutivePrimeStart_right_endpoint_gt_two
    {g n x : Nat} (h : ConsecutivePrimeStart g x n) :
    2 < n + g := by
  have hn_ge_2 : 2 ≤ n := Nat.Prime.two_le h.2.1
  have hg_pos : 0 < g := h.1
  omega

/-- Каждое простое p > 2 является правым концом не более одной пары соседних
простых. Это прямое следствие инъективности. -/
theorem ConsecutivePrimeStart_right_endpoint_unique
    {g₁ g₂ n₁ n₂ x : Nat}
    (h1 : ConsecutivePrimeStart g₁ x n₁)
    (h2 : ConsecutivePrimeStart g₂ x n₂)
    (heq : n₁ + g₁ = n₂ + g₂) : g₁ = g₂ ∧ n₁ = n₂ := by
  have hn : n₁ = n₂ := ConsecutivePrimeStart_left_injective h1 h2 heq
  exact ⟨by omega, hn⟩

end
end PrimeGaps
