import Mathlib
import Primes.Basic
import Primes.GapFrequency
import Primes.SingularSeries

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

noncomputable section

open scoped BigOperators
open Filter

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

/-- Гипотеза Харди--Литтлвуда для пар (1923). Открытая проблема. -/
def HardyLittlewoodPairConjecture (C₂ : ℝ) : Prop :=
  ∀ g : Nat, 0 < singularSeriesFactor C₂ g →
    AsymptoticEquivalentAtTop
      (fun x => (primePairCount g x : ℝ))
      (fun x => hardyLittlewoodMainTerm C₂ g (x : ℝ))

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

/-- Гипотеза Харди--Литтлвуда для k-кортежей (1923). Открытая проблема. -/
def HardyLittlewoodKTupleConjecture : Prop :=
  ∀ H : Finset ℤ, AdmissibleSet H → ∀ S : ℝ, IsTupleSingularSeries H S →
    AsymptoticEquivalentAtTop
      (fun x => (primeTupleCount H x : ℝ))
      (fun x => S * logarithmicIntegral₂ (x : ℝ) / (Real.log (x : ℝ)) ^ (H.card - 2))

/-- Промежуток `g` встречается как соседний простой промежуток с левым концом `≤ x`. -/
def PrimeGapOccursUpTo (g x : Nat) : Prop :=
  ∃ p : Nat, ConsecutivePrimeStart g (p + g) p ∧ p ≤ x

/-- Число соседних простых промежутков `≤ T log x` среди левых концов `≤ x`. -/
def normalizedPrimeGapCountLE (T : ℝ) (x : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun p =>
    ∃ g : Nat, ConsecutivePrimeStart g (p + g) p ∧ (g : ℝ) ≤ T * Real.log (x : ℝ)).card

/-- Гипотеза пуассоновского предела Галлагера. Открытая проблема. -/
def GallaghersPoissonLimitConjecture : Prop :=
  ∀ T : ℝ, 0 ≤ T →
    Tendsto (fun x : Nat => (normalizedPrimeGapCountLE T x : ℝ) /
      (primeCountingExact x : ℝ)) atTop (nhds (1 - Real.exp (-T)))

/-- Теорема Галлагера (1976): HL k-tuple влечёт пуассоновский предел. -/
def GallaghersTheoremFromHL : Prop :=
  HardyLittlewoodKTupleConjecture → GallaghersPoissonLimitConjecture

/-- Произвольный singleton `{h}` допустим. -/
theorem admissibleSet_singleton (h : ℤ) : AdmissibleSet ({h} : Finset ℤ) := by
  intro p hp
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  refine ⟨(h : ZMod p) + 1, ?_⟩
  rintro g hg
  simp only [Finset.mem_singleton] at hg
  subst g
  exact fun heq => one_ne_zero
    ((add_left_cancel ((add_zero _).trans heq)).symm)

/-- Пара `{0, g}` допустима при чётном `g > 0`. -/
theorem admissibleSet_pair_of_even {g : Nat} (hg : Even g) (_hg0 : 0 < g) :
    AdmissibleSet ({0, (g : ℤ)} : Finset ℤ) := by
  intro p hp
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  by_cases hpg : p ∣ g
  · refine ⟨1, ?_⟩
    rintro h hh
    have h01 : (0 : ZMod p) ≠ 1 := one_ne_zero.symm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    cases hh with
    | inl h0 => subst h; simp only [Int.cast_zero]; exact h01
    | inr hg_eq =>
        subst h; simp only [Int.cast_natCast]
        have hg0 : (g : ZMod p) = 0 := by rw [ZMod.natCast_eq_zero_iff]; exact hpg
        exact fun heq => h01 (hg0.symm.trans heq)
  · have hp2 : p ≠ 2 := by
      intro h; rw [h] at hpg; exact hpg (even_iff_two_dvd.mp hg)
    have h2le : 2 ≤ p := hp.two_le
    let forbidden : Finset (ZMod p) :=
      Finset.image (fun h : ℤ => (h : ZMod p)) ({0, (g : ℤ)} : Finset ℤ)
    have hlt : forbidden.card < (Finset.univ : Finset (ZMod p)).card := by
      rw [Finset.card_univ, ZMod.card p]
      calc forbidden.card ≤ ({0, (g : ℤ)} : Finset ℤ).card := Finset.card_image_le
        _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
        _ < p := by omega
    obtain ⟨a, _, ha_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨a, ?_⟩
    rintro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    intro heq
    apply ha_not
    simp only [forbidden, Finset.mem_image]
    cases hh with
    | inl h0 => subst h; exact ⟨(0 : ℤ), by simp, heq⟩
    | inr hg_eq => subst h; exact ⟨(g : ℤ), by simp, heq⟩

/-- Пара `{0, g}` **недопустима** для нечётного `g > 0`.
Полная характеризация: `{0, g}` допустима ⟺ `g` чётно (для `g > 0`). -/
theorem not_admissibleSet_pair_of_odd {g : Nat} (hg : Odd g) (_hg0 : 0 < g) :
    ¬ AdmissibleSet ({0, (g : ℤ)} : Finset ℤ) := by
  intro hadm
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := hadm 2 (by decide)
  have h0 : (0 : ZMod 2) ≠ a := ha 0 (by simp)
  have hg_mod : (g : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hg
  have hg_ne : (g : ZMod 2) ≠ a := fun heq => ha (g : ℤ) (by simp) heq
  have ha_val : a = 0 ∨ a = 1 := by
    match a with
    | ⟨0, _⟩ => exact Or.inl rfl
    | ⟨1, _⟩ => exact Or.inr rfl
  cases ha_val with
  | inl ha0 => exact h0 (ha0.symm)
  | inr ha1 => exact hg_ne (hg_mod.trans ha1.symm)

/-- For a pair tuple {0, g}, primeTupleCount equals primePairCount. -/
theorem primeTupleCount_pair_eq_primePairCount (g x : Nat) :
    primeTupleCount ({0, (g : ℤ)} : Finset ℤ) x = primePairCount g x := by
  unfold primeTupleCount primePairCount
  dsimp only
  congr 1
  apply Finset.filter_congr
  intro n _
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hcast : (↑n + ↑g : ℤ).toNat = n + g := by rw [← Nat.cast_add, Int.toNat_natCast]
  constructor
  · intro h
    exact ⟨by simpa [Int.toNat_natCast] using h 0 (by simp),
           by simpa [hcast] using h (↑g) (by simp)⟩
  · rintro ⟨hn, hng⟩ h (h0 | hg)
    · rw [h0]; simpa [Int.toNat_natCast] using hn
    · rw [hg]; simpa [hcast] using hng

end
end PrimeGaps
