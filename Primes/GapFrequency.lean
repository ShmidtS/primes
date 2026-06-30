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

/-- Точная частота `F(g, x)` через конечное решето. -/
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
        have hex : ∃ h ∈ Finset.Icc 1 (g - 1), Nat.Prime (n + h) := by
          by_contra hcontra
          apply hall
          intro h hh hp
          exact hcontra ⟨h, hh, hp⟩
        rcases hex with ⟨h, hh, hp⟩
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

/-- Частота после просеивания арифметических прогрессий. -/
def arithmeticProgressionSieveCount (g x y : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun n =>
    0 < g ∧ n + g ≤ x ∧ survivesFiniteEratosthenesLayer g n y).card

/-! ### endpointForbiddenResidueCount -/

/-- Количество запрещённых классов вычетов для двух концов modulo `p`. -/
def endpointForbiddenResidueCount (g p : Nat) : Nat :=
  if p ∣ g then 1 else 2

/-- Значение `endpointForbiddenResidueCount` для `g = p^k`. -/
theorem endpointForbiddenResidueCount_prime_power (g p : Nat) (k : Nat)
    (_hp : Nat.Prime p) (hk : 0 < k) (hg : g = p ^ k) :
    endpointForbiddenResidueCount g p = 1 := by
  have : p ∣ g := by
    subst hg
    have hpow : p ^ k = p * p ^ (k - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    rw [hpow]; exact ⟨p ^ (k - 1), rfl⟩
  simp [endpointForbiddenResidueCount, this]

/-! ### Mobius pair and Dirichlet conjectures -/

/-- Мёбиусоподобное ядро. -/
def mobiusPairKernel (mu : Nat → Int) (g x n : Nat) : Int :=
  (Finset.range (x + 1)).sum (fun d =>
    (Finset.range (x + 1)).sum (fun e =>
      if d * d ∣ n ∧ e * e ∣ n + g then mu d * mu e else 0))

/-- Гипотеза мёбиусовой пары. Открытая проблема. -/
def MobiusPairGapFormulaConjecture (mu : Nat → Int) : Prop :=
  ∀ g x : Nat,
    (primeGapFrequencyExact g x : Int) =
      (Finset.range (x + 1)).sum (fun n => mobiusPairKernel mu g x n)

/-- Количество простых `≤ x` в прогрессии `a mod q`. -/
def primesInArithmeticProgression (a q x : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun n => Nat.Prime n ∧ n % q = a % q).card

/-- Гипотеза равномерности Дирихле. Открытая проблема. -/
def DirichletUniformityConjecture : Prop :=
  ∀ a q : Nat, Nat.Coprime a q → 0 < q →
    Tendsto (fun x : Nat =>
      (primesInArithmeticProgression a q x : ℝ) /
        ((primeCountingExact x : ℝ) / (Nat.totient q : ℝ))) atTop (nhds 1)

/-- Гипотеза псевдослучайности простых промежутков. Открытая проблема. -/
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

/-! ### Consecutive prime pair injectivity and gap uniqueness

Ключевые комбинаторные теоремы: инъективность отображения (g, n) ↦ n + g
и единственность gap для фиксированного левого конца.
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
    have hmem : n₂ - n₁ ∈ Finset.Icc 1 (g₁ - 1) := Finset.mem_Icc.mpr (by omega)
    have hforbidden : ¬ Nat.Prime (n₁ + (n₂ - n₁)) := h1.2.2.2.2 _ hmem
    have : n₁ + (n₂ - n₁) = n₂ := by omega
    rw [this] at hforbidden
    exact absurd hn₂_prime hforbidden
  · by_cases hgt : n₂ < n₁
    · have hg₁_pos : 0 < g₁ := h1.1
      have hg₂_pos : 0 < g₂ := h2.1
      have hn₁_prime : Nat.Prime n₁ := h1.2.1
      have hmem : n₁ - n₂ ∈ Finset.Icc 1 (g₂ - 1) := Finset.mem_Icc.mpr (by omega)
      have hforbidden : ¬ Nat.Prime (n₂ + (n₁ - n₂)) := h2.2.2.2.2 _ hmem
      have : n₂ + (n₁ - n₂) = n₁ := by omega
      rw [this] at hforbidden
      exact absurd hn₁_prime hforbidden
    · omega

/-- Для фиксированного левого конца n существует не более одного g
с ConsecutivePrimeStart g x n. Если g₁ ≠ g₂, то меньший промежуток
даёт простое внутри большего — противоречие. -/
theorem ConsecutivePrimeStart_gap_unique_for_left
    {g₁ g₂ n x : Nat}
    (h1 : ConsecutivePrimeStart g₁ x n)
    (h2 : ConsecutivePrimeStart g₂ x n) : g₁ = g₂ := by
  by_cases hlt : g₁ < g₂
  · have hg₁_pos : 0 < g₁ := h1.1
    have hg₂_pos : 0 < g₂ := h2.1
    have hn_g1_prime : Nat.Prime (n + g₁) := h1.2.2.1
    have hmem : g₁ ∈ Finset.Icc 1 (g₂ - 1) := Finset.mem_Icc.mpr (by omega)
    have hforbidden : ¬ Nat.Prime (n + g₁) := h2.2.2.2.2 g₁ hmem
    exact absurd hn_g1_prime hforbidden
  · by_cases hgt : g₂ < g₁
    · have hg₁_pos : 0 < g₁ := h1.1
      have hg₂_pos : 0 < g₂ := h2.1
      have hn_g2_prime : Nat.Prime (n + g₂) := h2.2.2.1
      have hmem : g₂ ∈ Finset.Icc 1 (g₁ - 1) := Finset.mem_Icc.mpr (by omega)
      have hforbidden : ¬ Nat.Prime (n + g₂) := h1.2.2.2.2 g₂ hmem
      exact absurd hn_g2_prime hforbidden
    · omega

/-- Сумма частот всех промежутков не превосходит π(x).
Для каждого n существует не более одного g с CPS(g,x,n) (gap uniqueness),
и n должно быть простым. -/
theorem primeGapFrequencyExact_sum_le_primeCountingExact (x : Nat) :
    (Finset.range (x + 1)).sum (fun g => primeGapFrequencyExact g x) ≤
      primeCountingExact x := by
  classical
  have h_per_n : ∀ n ∈ Finset.range (x + 1),
      (Finset.range (x + 1)).sum (fun g =>
        (if ConsecutivePrimeStart g x n then (1 : Nat) else 0)) ≤
        (if Nat.Prime n then 1 else 0) := by
    intro n hn
    by_cases h : ∃ g, g ∈ Finset.range (x + 1) ∧ ConsecutivePrimeStart g x n
    · rcases h with ⟨g, hg, hcp⟩
      have huniq : ∀ g' ∈ Finset.range (x + 1),
          ConsecutivePrimeStart g' x n → g' = g := by
        intro g' hg' hcp'
        exact (ConsecutivePrimeStart_gap_unique_for_left (g₁ := g) (g₂ := g') hcp hcp').symm
      rw [Finset.sum_boole]
      have h_filter : (Finset.range (x + 1)).filter
          (fun g' => ConsecutivePrimeStart g' x n) = {g} := by
        ext g'; simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro ⟨hg', hcp'⟩; exact huniq g' hg' hcp'
        · rintro rfl; exact ⟨hg, hcp⟩
      rw [h_filter]
      have hn_prime : Nat.Prime n := hcp.2.1
      simp [hn_prime]
    · rw [Finset.sum_boole]
      have h_filter : (Finset.range (x + 1)).filter
          (fun g' => ConsecutivePrimeStart g' x n) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro g' hg' hcp'; exact h ⟨g', hg', hcp'⟩
      rw [h_filter]
      by_cases hp : Nat.Prime n <;> simp [hp]
  have h_eq_count : ∀ g, primeGapFrequencyExact g x =
      ((Finset.range (x + 1)).filter (fun n => ConsecutivePrimeStart g x n)).card := by
    intro g; exact primeGapFrequencyExact_eq_count g x
  simp only [h_eq_count, primeCountingExact]
  have h_lhs : (Finset.range (x + 1)).sum (fun g =>
      ((Finset.range (x + 1)).filter (fun n => ConsecutivePrimeStart g x n)).card) =
      (Finset.range (x + 1)).sum (fun n =>
        (Finset.range (x + 1)).sum (fun g =>
          (if ConsecutivePrimeStart g x n then (1 : Nat) else 0))) := by
    classical
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm ..
  have h_rhs : ((Finset.range (x + 1)).filter Nat.Prime).card =
      (Finset.range (x + 1)).sum (fun n => (if Nat.Prime n then (1 : Nat) else 0)) := by
    classical
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [h_lhs, h_rhs]
  exact Finset.sum_le_sum fun n hn => h_per_n n hn

end
end PrimeGaps
