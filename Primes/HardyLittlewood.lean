import Mathlib
import Primes.Basic
import Primes.GapFrequency
import Primes.SingularSeries

namespace PrimeGaps

noncomputable section

open scoped BigOperators
open Filter

/-! ## Hardy-Littlewood conjectures and Gallagher's theorem

Формализация гипотезы Харди--Литтлвуда для пар и k-кортежей простых чисел,
а также теорема Галлагера о пуассоновском пределе нормированных промежутков.
Определения и доказательства мигрированы из `GapDistribution.lean`.
`logarithmicIntegral₂` импортируется из `Primes.SingularSeries`.
-/

/-! ### Hardy-Littlewood pair conjecture -/

/-- Главный член Hardy--Littlewood для пар простых с промежутком `g`. -/
def hardyLittlewoodMainTerm (C₂ : ℝ) (g : Nat) (x : ℝ) : ℝ :=
  singularSeriesFactor C₂ g * logarithmicIntegral₂ x

/-- Число простых пар `(p, p + g)` с `p ≤ x`. -/
def primePairCount (g x : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun p => Nat.Prime p ∧ Nat.Prime (p + g)).card

/-- Отношение `f(x) / h(x) → 1` при `x → ∞`. -/
def AsymptoticEquivalentAtTop (f h : Nat → ℝ) : Prop :=
  Tendsto (fun x : Nat => f x / h x) atTop (nhds 1)

/-- Гипотеза Харди--Литтлвуда для пар (1923): число пар простых `(p, p+g)`
с `p ≤ x` асимптотически равно `𝔖(g) · li₂(x)`, где `𝔖(g)` — singular series.
Открытая проблема; для `g = 2` это гипотеза о простых близнецах. Доказана
при усреднении по `g` (Goldston--Pintz--Yıldırım, 2005). -/
def HardyLittlewoodPairConjecture (C₂ : ℝ) : Prop :=
  ∀ g : Nat, 0 < singularSeriesFactor C₂ g →
    AsymptoticEquivalentAtTop
      (fun x => (primePairCount g x : ℝ))
      (fun x => hardyLittlewoodMainTerm C₂ g (x : ℝ))

/-! ### Hardy-Littlewood k-tuple conjecture -/

/-- Множество сдвигов допустимо, если modulo каждого простого остаётся свободный класс. -/
def AdmissibleSet (H : Finset ℤ) : Prop :=
  ∀ p : Nat, Nat.Prime p → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a

/-- Сколько сдвигов из `H` попадает в запрещённый класс modulo `p`. -/
def tupleForbiddenResidueCount (H : Finset ℤ) (p : Nat) : Nat := by
  classical
  exact (H.image fun h => (h : ZMod p)).card

/-- Частичное произведение singular series для произвольного finite tuple. -/
def tupleSingularSeriesPartial (H : Finset ℤ) (y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod fun p =>
    if Nat.Prime p then
      (1 - (tupleForbiddenResidueCount H p : ℝ) / (p : ℝ)) /
        (1 - 1 / (p : ℝ)) ^ H.card
    else 1

/-- `S` является singular series для tuple `H`. -/
def IsTupleSingularSeries (H : Finset ℤ) (S : ℝ) : Prop :=
  Tendsto (tupleSingularSeriesPartial H) atTop (nhds S)

/-- Число `n ≤ x`, для которых все `n + h`, `h ∈ H`, простые. -/
def primeTupleCount (H : Finset ℤ) (x : Nat) : Nat := by
  classical
  let p : ℕ → Prop := fun n => ∀ h ∈ H, Nat.Prime ((n : ℤ) + h).toNat
  exact ((Finset.range (x + 1)).filter p).card

/-- Гипотеза Харди--Литтлвуда для k-кортежей (1923): число `n ≤ x`, для которых
все `n + h`, `h ∈ H`, простые, асимптотически равно `S · li_k(x)` для допустимого
множества `H`. Открытая проблема; обобщает гипотезу о простых близнецах и
гипотезу Диксона. Частичные результаты: Green--Tao (2004) для арифметических
прогрессий, Maynard--Tao (2013) для ограниченных промежутков. -/
def HardyLittlewoodKTupleConjecture : Prop :=
  ∀ H : Finset ℤ, AdmissibleSet H → ∀ S : ℝ, IsTupleSingularSeries H S →
    AsymptoticEquivalentAtTop
      (fun x => (primeTupleCount H x : ℝ))
      (fun x => S * logarithmicIntegral₂ (x : ℝ) / (Real.log (x : ℝ)) ^ (H.card - 2))

/-! ### Gallagher's theorem -/

/-- Промежуток `g` встречается как соседний простой промежуток с левым концом `≤ x`. -/
def PrimeGapOccursUpTo (g x : Nat) : Prop :=
  ∃ p : Nat, ConsecutivePrimeStart g (p + g) p ∧ p ≤ x

/-- Число соседних простых промежутков `≤ T log x` среди левых концов `≤ x`. -/
def normalizedPrimeGapCountLE (T : ℝ) (x : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun p =>
    ∃ g : Nat, ConsecutivePrimeStart g (p + g) p ∧ (g : ℝ) ≤ T * Real.log (x : ℝ)).card

/-- Гипотеза пуассоновского предела Галлагера: доля простых `p ≤ x`, для которых
нормированный промежуток `(p' - p) / log x ≤ T`, стремится к `1 - e^{-T}`.
Открытая проблема; доказана Галлагером (1976) при условии гипотезы
Харди--Литтлвуда для k-кортежей (см. `GallaghersTheoremFromHL`). -/
def GallaghersPoissonLimitConjecture : Prop :=
  ∀ T : ℝ, 0 ≤ T →
    Tendsto (fun x : Nat => (normalizedPrimeGapCountLE T x : ℝ) /
      (primeCountingExact x : ℝ)) atTop (nhds (1 - Real.exp (-T)))

/-- Backwards-compatible alias for `GallaghersPoissonLimitConjecture`. -/
abbrev GallaghersPoissonLimit : Prop := GallaghersPoissonLimitConjecture

/-- Теорема Галлагера (1976): гипотеза Харди--Литтлвуда для k-кортежей влечёт
пуассоновский предел нормированных простых промежутков. Доказано условно;
безусловный статус зависит от доказательства HL k-tuple conjecture. -/
def GallaghersTheoremFromHL : Prop :=
  HardyLittlewoodKTupleConjecture → GallaghersPoissonLimitConjecture

/-! ### Admissibility proofs -/

/-- Пустое множество сдвигов допустимо. -/
theorem admissibleSet_empty : AdmissibleSet (∅ : Finset ℤ) := by
  intro p hp
  exact ⟨0, by simp⟩

/-- Singleton сдвигов допустим: берём класс `1` modulo любого простого. -/
theorem admissibleSet_singleton_zero : AdmissibleSet ({0} : Finset ℤ) := by
  intro p hp
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  refine ⟨1, ?_⟩
  intro h hh
  simp at hh
  subst h
  simp [zero_ne_one]

/-- Произвольный singleton `{h}` допустим: берём класс `h + 1 mod p`. -/
theorem admissibleSet_singleton (h : ℤ) : AdmissibleSet ({h} : Finset ℤ) := by
  intro p hp
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  refine ⟨(h : ZMod p) + 1, ?_⟩
  rintro g hg
  simp only [Finset.mem_singleton] at hg
  subst g
  intro heq
  have h1 : (1 : ZMod p) = 0 := by
    have hstep : (h : ZMod p) + 0 = (h : ZMod p) + 1 :=
      (add_zero (h : ZMod p)).trans heq
    exact (add_left_cancel hstep).symm
  exact absurd h1 one_ne_zero

/-! ### Tuple cardinality bounds -/

/-- Для пустого множества сдвигов число запрещённых классов равно 0. -/
theorem tupleForbiddenResidueCount_empty (p : Nat) :
    tupleForbiddenResidueCount (∅ : Finset ℤ) p = 0 := by
  unfold tupleForbiddenResidueCount
  simp

/-! ### Tuple / pair equivalence -/

/-- For a pair tuple {0, g}, primeTupleCount equals primePairCount. -/
theorem primeTupleCount_pair_eq_primePairCount (g x : Nat) :
    primeTupleCount ({0, (g : ℤ)} : Finset ℤ) x = primePairCount g x := by
  unfold primeTupleCount primePairCount
  dsimp only
  congr 1
  apply Finset.filter_congr
  intro n _
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hcast : (↑n + ↑g : ℤ).toNat = n + g := by
    rw [← Nat.cast_add, Int.toNat_natCast]
  constructor
  · intro h
    have h0 := h 0 (by simp)
    have hg := h (↑g) (by simp)
    have hn : Nat.Prime n := by simpa [Int.toNat_natCast] using h0
    have hng : Nat.Prime (n + g) := by simpa [hcast] using hg
    exact ⟨hn, hng⟩
  · intro ⟨hn, hng⟩ h hh
    cases hh with
    | inl h0 => rw [h0]; simpa [Int.toNat_natCast] using hn
    | inr hg => rw [hg]; simpa [hcast] using hng

/-! ### primePairCount properties -/

/-- `primePairCount` не превосходит `primeCountingExact`: условие пары сильнее простоты. -/
theorem primePairCount_le_primeCountingExact (g x : Nat) :
    primePairCount g x ≤ primeCountingExact x := by
  unfold primePairCount primeCountingExact
  refine Finset.card_le_card ?_
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

/-- `primePairCount` монотонна по правому концу: x ≤ y → pair(g, x) ≤ pair(g, y). -/
theorem primePairCount_monotone {g x y : Nat} (hxy : x ≤ y) :
    primePairCount g x ≤ primePairCount g y := by
  unfold primePairCount
  have hsub : (Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + g)) ⊆
      (Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + g)) := by
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    refine ⟨?_, ha.2⟩
    simp only [Finset.mem_range] at ha ⊢
    omega
  exact Finset.card_le_card hsub

/-- `primePairCount g 0 = 0`: нет простых пар до 0. -/
theorem primePairCount_zero (g : Nat) : primePairCount g 0 = 0 := by
  unfold primePairCount
  have : Finset.range 1 = {0} := by
    ext p; simp only [Finset.mem_range, Finset.mem_singleton]; omega
  rw [this]
  simp [Nat.not_prime_zero]

/-- `primeGapFrequencyExact` не превосходит `primePairCount`
(дополнительное условие отсутствия простых внутри). -/
theorem primeGapFrequencyExact_le_primePairCount (g x : Nat) :
    primeGapFrequencyExact g x ≤ primePairCount g x := by
  rw [primeGapFrequencyExact_eq_count]
  unfold primePairCount
  classical
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn
  unfold ConsecutivePrimeStart at hn
  exact Finset.mem_filter.mpr ⟨hn.1, ⟨hn.2.2.1, hn.2.2.2.1⟩⟩

end

end PrimeGaps
