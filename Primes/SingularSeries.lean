import Mathlib
import Primes.Basic
import Primes.GapFrequency
import Primes.Wheel

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

namespace PrimeGaps

noncomputable section

open scoped BigOperators

/-! ## Singular series and twin prime constant

Singular series для пары простых (Hardy--Littlewood):
локальные множители по каждому простому, нормированные на наивные плотности.
-/

/-- Конечное произведение sieve-факторов для пары `(n, n+g)` по простым `≤ y`. -/
def finitePairSieveFactor (g y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod (fun p =>
    if Nat.Prime p then 1 - (endpointForbiddenResidueCount g p : ℝ) / (p : ℝ) else 1)

/-- Локальная плотность выживания пары modulo `p`. -/
def wheelEndpointSurvivalDensity (g p : Nat) : ℝ :=
  1 - (endpointForbiddenResidueCount g p : ℝ) / (p : ℝ)

/-- Нормированный локальный множитель singular series в wheel-модели. -/
def wheelLocalSingularFactor (g p : Nat) : ℝ :=
  wheelEndpointSurvivalDensity g p / (1 - 1 / (p : ℝ)) ^ 2

/-- Конечная wheel-версия произведения локальных множителей. -/
def finiteWheelSingularSeries (g y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod fun p =>
    if Nat.Prime p then wheelLocalSingularFactor g p else 1

/-- Частичное произведение для twin prime constant `C₂`. -/
def twinPrimeConstantPartial (y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod fun p =>
    if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

/-- `C₂` является twin prime constant как предел эйлерова произведения. -/
def IsTwinPrimeConstant (C₂ : ℝ) : Prop :=
  Filter.Tendsto twinPrimeConstantPartial Filter.atTop (nhds C₂)

/-- Конечное произведение поправок по нечётным простым делителям `k`. -/
def divisorCorrectionProduct (k : Nat) : ℝ :=
  (Finset.range (k + 1)).prod fun p =>
    if Nat.Prime p ∧ 2 < p ∧ p ∣ k then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

/-- Singular series для пары `(0, g)` при заданном `C₂`. -/
def singularSeriesFactor (C₂ : ℝ) (g : Nat) : ℝ :=
  if Even g then 2 * C₂ * divisorCorrectionProduct (g / 2) else 0

/-- Конечный wheel-ряд сходится к singular series factor. -/
def finiteWheelSingularSeriesLimit (g : Nat) (C₂ : ℝ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto (fun y => finiteWheelSingularSeries g y) Filter.atTop (nhds L) ∧
    L = singularSeriesFactor C₂ g

/-- Интеграл `li₂(x) = ∫₂ˣ dt / log² t`. -/
def logarithmicIntegral₂ (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2

/-! ### Core identity: D via primeFactors -/

/-- Конечная поправка равна произведению по нечётным простым делителям. -/
theorem divisorCorrectionProduct_eq_primeFactors (k : Nat) :
    divisorCorrectionProduct k =
      ((Nat.primeFactors k).filter (fun p => 2 < p)).prod
        (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  by_cases hk0 : k = 0
  · subst k; simp [divisorCorrectionProduct]
  · rw [divisorCorrectionProduct, ← Finset.prod_filter]
    congr 1; ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
    refine ⟨fun h => ⟨⟨h.2.1, h.2.2.2, hk0⟩, h.2.2.1⟩, ?_⟩
    · rintro ⟨⟨hprime, hdvd, _⟩, hgt⟩
      refine ⟨Nat.lt_succ_iff.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd), hprime, hgt, hdvd⟩

/-! ### Structural properties of D and S -/

/-- `divisorCorrectionProduct` мультипликативен по взаимно простым аргументам. -/
theorem divisorCorrectionProduct_mul_of_coprime {k k' : Nat}
    (_hk : k ≠ 0) (_hk' : k' ≠ 0) (hcoprime : Nat.Coprime k k') :
    divisorCorrectionProduct (k * k') =
      divisorCorrectionProduct k * divisorCorrectionProduct k' := by
  rw [divisorCorrectionProduct_eq_primeFactors, divisorCorrectionProduct_eq_primeFactors,
      divisorCorrectionProduct_eq_primeFactors, hcoprime.primeFactors_mul]
  have hfu : (Nat.primeFactors k ∪ Nat.primeFactors k').filter (fun p => 2 < p) =
      (Nat.primeFactors k).filter (fun p => 2 < p) ∪
      (Nat.primeFactors k').filter (fun p => 2 < p) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_union]; tauto
  rw [hfu, Finset.prod_union (by
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      hcoprime.disjoint_primeFactors)]

/-- `D(k^a) = D(k)` для `a > 0`. -/
theorem divisorCorrectionProduct_pow_eq (k : Nat) (ha : 0 < a) :
    divisorCorrectionProduct (k ^ a) = divisorCorrectionProduct k := by
  rw [divisorCorrectionProduct_eq_primeFactors, divisorCorrectionProduct_eq_primeFactors,
      Nat.primeFactors_pow k (Nat.ne_of_gt ha)]

/-- `D(p) = (p-1)/(p-2)` для нечётного простого `p`. -/
theorem divisorCorrectionProduct_prime (p : Nat) (hp : Nat.Prime p) (hp_odd : 2 < p) :
    divisorCorrectionProduct p = ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  rw [divisorCorrectionProduct_eq_primeFactors]
  have hpf : (Nat.primeFactors p).filter (fun q => 2 < q) = {p} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hmem, hgt2⟩
      rw [Nat.mem_primeFactors] at hmem
      exact (Nat.prime_dvd_prime_iff_eq hmem.1 hp).mp hmem.2.1
    · rintro rfl
      exact ⟨Nat.mem_primeFactors.mpr ⟨hp, dvd_rfl, hp.ne_zero⟩, hp_odd⟩
  rw [hpf, Finset.prod_singleton]

/-- **S(2p) = 2C₂ · (p-1)/(p-2)** для нечётного простого `p`. -/
theorem singularSeriesFactor_eq_for_2p (C₂ : ℝ) (p : Nat) (hp : Nat.Prime p) (hp_odd : 2 < p) :
    singularSeriesFactor C₂ (2 * p) = 2 * C₂ * (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  rw [singularSeriesFactor, if_pos (even_two_mul p),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      divisorCorrectionProduct_prime p hp hp_odd]

/-- **S(2p) = S(2p^a)** — singular series инвариантна при возведении делителя в степень. -/
theorem singularSeriesFactor_2p_eq_2p_pow (C₂ : ℝ) (p : Nat) (_hp : Nat.Prime p) (ha : 0 < a) :
    singularSeriesFactor C₂ (2 * p) = singularSeriesFactor C₂ (2 * p ^ a) := by
  rw [singularSeriesFactor, singularSeriesFactor,
      if_pos (even_two_mul p), if_pos (even_two_mul (p ^ a)),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      divisorCorrectionProduct_pow_eq p ha]

/-- **S(2pq) = 2C₂ · (p-1)/(p-2) · (q-1)/(q-2)** для различных нечётных простых p, q. -/
theorem singularSeriesFactor_eq_for_2pq (C₂ : ℝ) (p q : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hp_odd : 2 < p) (hq_odd : 2 < q)
    (hpq_ne : p ≠ q) :
    singularSeriesFactor C₂ (2 * (p * q)) =
      2 * C₂ * (((p : ℝ) - 1) / ((p : ℝ) - 2)) * (((q : ℝ) - 1) / ((q : ℝ) - 2)) := by
  rw [singularSeriesFactor, if_pos (even_two_mul (p * q)),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      divisorCorrectionProduct_mul_of_coprime hp.ne_zero hq.ne_zero
        ((Nat.coprime_primes hp hq).mpr hpq_ne),
      divisorCorrectionProduct_prime p hp hp_odd,
      divisorCorrectionProduct_prime q hq hq_odd]
  ring

/-- Singular series мультипликативна по взаимно простым половинам gap. -/
theorem singularSeriesFactor_mul_of_coprime (C₂ : ℝ) {k k' : Nat}
    (hk : k ≠ 0) (hk' : k' ≠ 0) (hcoprime : Nat.Coprime k k') :
    singularSeriesFactor C₂ (2 * (k * k')) =
      singularSeriesFactor C₂ (2 * k) * singularSeriesFactor C₂ (2 * k') / (2 * C₂) := by
  rw [singularSeriesFactor, singularSeriesFactor, singularSeriesFactor,
      if_pos (even_two_mul (k * k')), if_pos (even_two_mul k), if_pos (even_two_mul k'),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      divisorCorrectionProduct_mul_of_coprime hk hk' hcoprime]
  by_cases hC₂ : C₂ = 0
  · simp [hC₂]
  · field_simp [mul_ne_zero two_ne_zero hC₂]

/-- `D(2^a) = 1`: у степени 2 нет нечётных простых делителей. -/
theorem divisorCorrectionProduct_pow_two (a : Nat) :
    divisorCorrectionProduct (2 ^ a) = 1 := by
  rw [divisorCorrectionProduct_eq_primeFactors]
  by_cases ha : a = 0
  · subst ha; simp [Nat.primeFactors_one]
  · rw [Nat.primeFactors_prime_pow (Nat.ne_of_gt (by omega : 0 < a)) Nat.prime_two,
      show ({2} : Finset Nat).filter (fun p => 2 < p) = ∅ from by
        rw [Finset.filter_eq_empty_iff]
        intro p hp; simp only [Finset.mem_singleton] at hp; subst hp; omega]
    simp

/-- `D(2^a · m) = D(m)` для нечётного m: 2 не вносит вклад в D. -/
theorem divisorCorrectionProduct_pow_two_mul (a : Nat) (m : Nat) (hm : Odd m) :
    divisorCorrectionProduct (2 ^ a * m) = divisorCorrectionProduct m := by
  rw [divisorCorrectionProduct_eq_primeFactors, divisorCorrectionProduct_eq_primeFactors]
  by_cases ha : a = 0
  · subst ha; simp
  · have h2a_ne : (2 : Nat) ^ a ≠ 0 := by
      have : 0 < 2 ^ a := by cases a <;> simp [Nat.pow_succ, Nat.zero_lt_succ]
      omega
    have hm_ne : m ≠ 0 := by
      have hpos : 0 < m := hm.pos
      intro h; subst h; simp at hpos
    rw [Nat.primeFactors_mul h2a_ne hm_ne,
        Nat.primeFactors_prime_pow (Nat.ne_of_gt (by omega : 0 < a)) Nat.prime_two,
        Finset.filter_union,
        show ({2} : Finset Nat).filter (fun p => 2 < p) = ∅ from by
          rw [Finset.filter_eq_empty_iff]
          intro p hp; simp only [Finset.mem_singleton] at hp; subst hp; omega,
        Finset.empty_union]

/-! ### finiteWheelSingularSeries properties -/

/-- Wheel-series равна sieve-фактору, делённому на квадратичные плотности. -/
theorem finiteWheelSingularSeries_eq_finitePairSieveFactor_div_sq (g y : Nat) :
    finiteWheelSingularSeries g y =
      finitePairSieveFactor g y /
        (Finset.range (y + 1)).prod (fun p =>
          if Nat.Prime p then (1 - 1 / (p : ℝ)) ^ 2 else 1) := by
  rw [finiteWheelSingularSeries, finitePairSieveFactor, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  by_cases hprime : Nat.Prime p
  · simp [hprime, wheelLocalSingularFactor, wheelEndpointSurvivalDensity,
      endpointForbiddenResidueCount]
  · simp [hprime]

/-! ### wheelLocalSingularFactor -/

/-- Явная форма локального wheel-множителя через делимость `p ∣ g`. -/
theorem wheelLocalSingularFactor_eq_singular (g p : Nat) (_hp : Nat.Prime p) :
    wheelLocalSingularFactor g p =
      (1 - (if p ∣ g then (1 : ℝ) else (2 : ℝ)) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2 := by
  simp [wheelLocalSingularFactor, wheelEndpointSurvivalDensity, endpointForbiddenResidueCount]

/-- Алгебраическое тождество для wheel-множителя при `p > 2`. -/
private lemma algebraic_identity_wheel_div (p : ℝ) (hp : 2 < p) :
    (1 - 2 / p) / (1 - 1 / p) ^ 2 = 1 - 1 / (p - 1) ^ 2 := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hdenom : (1 - 1 / p) ≠ 0 := by
    have : 1 / p < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  field_simp [hp0, hp1, hdenom]; ring

/-- Конечный множитель для чётного gap. -/
def finiteWheelEvenFactor (k y : Nat) : ℝ :=
  ((Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ 2 < p ∧ p ∣ k)).prod
    (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- Для нечётного `g` и `y ≥ 2` wheel-серия равна нулю. -/
theorem finiteWheelSingularSeries_odd_eq_zero {g y : Nat}
    (hg : Odd g) (hy : 2 ≤ y) :
    finiteWheelSingularSeries g y = 0 := by
  rw [finiteWheelSingularSeries, ← Finset.prod_filter]
  have h2mem : 2 ∈ (Finset.range (y + 1)).filter Nat.Prime := by
    simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, by decide⟩
  have h2nd : ¬(2 : Nat) ∣ g := fun h =>
    Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h) hg
  have hf0 : wheelLocalSingularFactor g 2 = 0 := by
    rw [wheelLocalSingularFactor_eq_singular g 2 (by decide)]
    simp only [h2nd, if_false]; norm_num
  exact Finset.prod_eq_zero h2mem hf0

/-- Общая формула `finiteWheelSingularSeries` для чётного gap `g = 2k`. -/
theorem finiteWheelSingularSeries_even_eq (k y : Nat) (hy : 2 ≤ y) :
    finiteWheelSingularSeries (2 * k) y =
      2 * finiteWheelEvenFactor k y * twinPrimeConstantPartial y := by
  rw [finiteWheelSingularSeries, twinPrimeConstantPartial, finiteWheelEvenFactor]
  let s := Finset.range (y + 1)
  let oddDivs := s.filter (fun p => Nat.Prime p ∧ 2 < p ∧ p ∣ k)
  let oddNonDivs := s.filter (fun p => Nat.Prime p ∧ 2 < p ∧ ¬p ∣ k)
  let allOdd := s.filter (fun p => Nat.Prime p ∧ 2 < p)
  have h2p : Nat.Prime 2 := by decide
  have h2n : 2 ∉ allOdd := by simp [allOdd, s]
  have hsp : s.filter Nat.Prime = insert 2 allOdd := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, s, allOdd, Finset.mem_range]
    refine ⟨fun ⟨hlt, hpr⟩ => ?_, fun h => ?_⟩
    · by_cases hp2 : p = 2
      · exact Or.inl hp2
      · have h2le := Nat.Prime.two_le hpr
        exact Or.inr ⟨hlt, hpr, by omega⟩
    · cases h with
      | inl h2 => subst h2; exact ⟨by omega, h2p⟩
      | inr hodd => exact ⟨hodd.1, hodd.2.1⟩
  have hsodd : allOdd = oddDivs ∪ oddNonDivs := by
    ext p
    simp only [allOdd, oddDivs, oddNonDivs, s, Finset.mem_filter,
      Finset.mem_union, Finset.mem_range]
    refine ⟨fun ⟨hlt, hpr, hgt2⟩ => ?_, fun h => ?_⟩
    · by_cases hpk : p ∣ k
      · exact Or.inl ⟨hlt, hpr, hgt2, hpk⟩
      · exact Or.inr ⟨hlt, hpr, hgt2, hpk⟩
    · cases h with
      | inl hd => exact ⟨hd.1, hd.2.1, hd.2.2.1⟩
      | inr hnd => exact ⟨hnd.1, hnd.2.1, hnd.2.2.1⟩
  have hdisj : Disjoint oddDivs oddNonDivs := by
    rw [Finset.disjoint_left]
    intro p hp hnp
    exact (Finset.mem_filter.mp hnp).2.2.2 (Finset.mem_filter.mp hp).2.2.2
  have hf2 : wheelLocalSingularFactor (2 * k) 2 = 2 := by
    rw [wheelLocalSingularFactor_eq_singular (2 * k) 2 (by decide)]
    have h2dvd : (2 : Nat) ∣ 2 * k := Nat.dvd_mul_right 2 k
    simp only [h2dvd, if_true]; norm_num
  have hpfilt : s.prod (fun p => if Nat.Prime p then
      wheelLocalSingularFactor (2 * k) p else 1) =
      (s.filter Nat.Prime).prod (fun p => wheelLocalSingularFactor (2 * k) p) := by
    rw [← Finset.prod_filter]
  rw [hpfilt, hsp, Finset.prod_insert h2n, hf2, hsodd, Finset.prod_union hdisj]
  have hpd : oddDivs.prod (fun p => wheelLocalSingularFactor (2 * k) p) =
      oddDivs.prod (fun p =>
        ((p : ℝ) - 1) / ((p : ℝ) - 2) * (1 - 1 / ((p : ℝ) - 1) ^ 2)) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hm := Finset.mem_filter.mp hp
    have hdvd : p ∣ 2 * k := dvd_mul_of_dvd_right hm.2.2.2 2
    rw [wheelLocalSingularFactor_eq_singular (2 * k) p hm.2.1]
    simp only [hdvd, if_true]
    have hp_real : (2 : ℝ) < p := by exact_mod_cast hm.2.2.1
    field_simp [hp_real.ne', (by linarith : (p : ℝ) - 1 ≠ 0), (by linarith : (p : ℝ) - 2 ≠ 0)]
    ring
  rw [hpd]
  have hpnd : oddNonDivs.prod (fun p => wheelLocalSingularFactor (2 * k) p) =
      oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have xm := Finset.mem_filter.mp hp
    have hnd : ¬p ∣ 2 * k := by
      intro hd
      have hor : p ∣ 2 ∨ p ∣ k := (Nat.Prime.dvd_mul xm.2.1).mp hd
      cases hor with
      | inl h2 => have : p = 2 := (Nat.prime_dvd_prime_iff_eq xm.2.1 Nat.prime_two).mp h2; omega
      | inr hk => exact xm.2.2.2 hk
    rw [wheelLocalSingularFactor_eq_singular (2 * k) p xm.2.1]
    simp only [hnd, if_false]
    exact algebraic_identity_wheel_div (p : ℝ) (by exact_mod_cast xm.2.2.1)
  rw [hpnd]
  rw [show oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2) * (1 - 1 / ((p : ℝ) - 1) ^ 2)) =
        oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) from Finset.prod_mul_distrib ..]
  have h_twin_prod :
      oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) *
      oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) =
      (s.filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    have h_eq : s.filter (fun p => Nat.Prime p ∧ 2 < p) = oddDivs ∪ oddNonDivs := hsodd
    rw [h_eq, Finset.prod_union hdisj]
  have htwin : s.prod (fun p =>
      if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) =
      (s.filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    rw [Finset.prod_filter]
  rw [show 2 * ((oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
          oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ))) *
        oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ))) =
      2 * oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        (oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) *
         oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ))) from by ring,
    h_twin_prod, ← htwin]

/-! ### Bounds and characterization theorems -/

/-- `D(k) ≥ 1`: каждый множитель `(p-1)/(p-2) ≥ 1` для `p > 2`. -/
theorem divisorCorrectionProduct_ge_one (k : Nat) :
    1 ≤ divisorCorrectionProduct k := by
  rw [divisorCorrectionProduct_eq_primeFactors]
  apply Finset.one_le_prod
  rintro p hp
  have hp_real : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
  rw [le_div_iff₀ (by linarith : 0 < (p : ℝ) - 2)]; linarith

/-- `D(k) > 1` ↔ `k` имеет нечётный простой делитель. -/
theorem divisorCorrectionProduct_gt_one_iff (k : Nat) :
    1 < divisorCorrectionProduct k ↔
    ((Nat.primeFactors k).filter (fun p => 2 < p)).Nonempty := by
  rw [divisorCorrectionProduct_eq_primeFactors]
  constructor
  · intro hgt
    by_cases h : (Nat.primeFactors k).filter (fun p => 2 < p) = ∅
    · rw [h, Finset.prod_empty] at hgt
      exact absurd hgt (by linarith : ¬(1 < (1 : ℝ)))
    · exact Finset.nonempty_iff_ne_empty.mpr h
  · intro hne
    rcases hne with ⟨p, hp⟩
    have hp_real : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    have hf : 1 < ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
      rw [lt_div_iff₀ (by linarith : 0 < (p : ℝ) - 2)]; linarith
    have hrest : 1 ≤ (((Nat.primeFactors k).filter (fun q => 2 < q)).erase p).prod
        (fun q => ((q : ℝ) - 1) / ((q : ℝ) - 2)) := by
      apply Finset.one_le_prod
      rintro q hq
      have hq_real : (2 : ℝ) < q := by
        exact_mod_cast (Finset.mem_filter.mp (Finset.mem_of_mem_erase hq)).2
      rw [le_div_iff₀ (by linarith : 0 < (q : ℝ) - 2)]; linarith
    have hsplit : ((Nat.primeFactors k).filter (fun q => 2 < q)).prod
        (fun q => ((q : ℝ) - 1) / ((q : ℝ) - 2)) =
        ((p : ℝ) - 1) / ((p : ℝ) - 2) *
        (((Nat.primeFactors k).filter (fun q => 2 < q)).erase p).prod
          (fun q => ((q : ℝ) - 1) / ((q : ℝ) - 2)) := by
      conv_lhs => rw [← Finset.insert_erase hp, Finset.prod_insert (Finset.notMem_erase _ _)]
    rw [hsplit]
    nlinarith [hf, hrest]

/-- `S(2^a) = 2C₂` для `a ≥ 1`: singular series для степеней двойки равна twin prime constant. -/
theorem singularSeriesFactor_2_pow (C₂ : ℝ) (a : Nat) (ha : 1 ≤ a) :
    singularSeriesFactor C₂ (2 ^ a) = 2 * C₂ := by
  unfold singularSeriesFactor
  cases a with
  | zero => omega
  | succ n =>
    rw [@Nat.pow_succ' 2 n, if_pos (even_two_mul (2 ^ n)),
        Nat.mul_div_cancel_left _ (by omega : 0 < 2),
        divisorCorrectionProduct_pow_two n]
    ring

/-- `S(2^a · m) = S(2m)` для нечётного `m` и `a ≥ 1`: 2-adic инвариантность. -/
theorem singularSeriesFactor_2adic (C₂ : ℝ) (a : Nat) (m : Nat) (hm : Odd m) (ha : 1 ≤ a) :
    singularSeriesFactor C₂ (2 ^ a * m) = singularSeriesFactor C₂ (2 * m) := by
  unfold singularSeriesFactor
  cases a with
  | zero => omega
  | succ n =>
    rw [@Nat.pow_succ' 2 n]
    have heven1 : Even (2 * 2 ^ n * m) := by
      rw [Nat.mul_assoc 2 (2 ^ n) m]; exact even_two_mul (2 ^ n * m)
    rw [if_pos heven1, if_pos (even_two_mul m)]
    rw [Nat.mul_assoc 2 (2 ^ n) m, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
        Nat.mul_div_cancel_left _ (by omega : 0 < 2),
        divisorCorrectionProduct_pow_two_mul n m hm]

/-- `S(g) ≥ 2C₂` для чётного `g` при `C₂ ≥ 0`. -/
theorem singularSeriesFactor_ge_2C2 (C₂ : ℝ) (g : Nat) (hg : Even g) (hC₂ : 0 ≤ C₂) :
    2 * C₂ ≤ singularSeriesFactor C₂ g := by
  unfold singularSeriesFactor
  rw [if_pos hg]
  have hD : 1 ≤ divisorCorrectionProduct (g / 2) := divisorCorrectionProduct_ge_one (g / 2)
  nlinarith

/-- Алгебраическое тождество: `(p-1)/(p-2) · (1-1/(p-1)²) = p/(p-1)`. -/
private lemma euler_factor_identity (p : ℝ) (hp : 2 < p) :
    ((p - 1) / (p - 2)) * (1 - 1 / (p - 1) ^ 2) = p / (p - 1) := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hp2 : p - 2 ≠ 0 := by linarith
  field_simp [hp0, hp1, hp2]
  ring

/-- `D(k) · ∏_{p|k, p>2} (1-1/(p-1)²) = ∏_{p|k, p>2} p/(p-1)`.
Связь между divisor correction и эйлеровым произведением. -/
theorem divisorCorrectionProduct_euler_connection (k : Nat) :
    divisorCorrectionProduct k *
    ((Nat.primeFactors k).filter (fun p => 2 < p)).prod
      (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2)) =
    ((Nat.primeFactors k).filter (fun p => 2 < p)).prod
      (fun p => (p : ℝ) / ((p : ℝ) - 1)) := by
  rw [divisorCorrectionProduct_eq_primeFactors, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact euler_factor_identity (p : ℝ) (by exact_mod_cast (Finset.mem_filter.mp hp).2)

/-! ### Characterization and monotonicity theorems -/

/-- D(k) = 1 ↔ k не имеет нечётных простых делителей. -/
theorem divisorCorrectionProduct_eq_one_iff (k : Nat) :
    divisorCorrectionProduct k = 1 ↔
    (Nat.primeFactors k).filter (fun p => 2 < p) = ∅ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hcontra
    have hne : ((Nat.primeFactors k).filter (fun p => 2 < p)).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hcontra
    have : 1 < divisorCorrectionProduct k := Iff.mpr (divisorCorrectionProduct_gt_one_iff k) hne
    linarith
  · rw [divisorCorrectionProduct_eq_primeFactors, h, Finset.prod_empty]

/-- S(g) = 2C₂ iff g/2 не имеет нечётных простых делителей (для чётного g, C₂ > 0). -/
theorem singularSeriesFactor_eq_2C2_iff (C₂ : ℝ) (g : Nat) (hg : Even g) (hC₂ : 0 < C₂) :
    singularSeriesFactor C₂ g = 2 * C₂ ↔
    (Nat.primeFactors (g / 2)).filter (fun p => 2 < p) = ∅ := by
  unfold singularSeriesFactor
  rw [if_pos hg]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2ne : (2 : ℝ) * C₂ ≠ 0 := mul_ne_zero two_ne_zero hC₂.ne'
    have heq : (2 * C₂) * divisorCorrectionProduct (g / 2) = (2 * C₂) * 1 := by
      rw [h, mul_one]
    exact Iff.mp (divisorCorrectionProduct_eq_one_iff (g / 2)) (mul_left_cancel₀ h2ne heq)
  · rw [divisorCorrectionProduct_eq_primeFactors, h, Finset.prod_empty]; ring

/-- S(g) ≠ 0 для чётного g при C₂ ≠ 0. -/
theorem singularSeriesFactor_ne_zero (C₂ : ℝ) (g : Nat) (hg : Even g) (hC₂ : C₂ ≠ 0) :
    singularSeriesFactor C₂ g ≠ 0 := by
  unfold singularSeriesFactor
  rw [if_pos hg]
  have hD : 0 < divisorCorrectionProduct (g / 2) := by
    have := divisorCorrectionProduct_ge_one (g / 2); linarith
  exact mul_ne_zero (mul_ne_zero two_ne_zero hC₂) hD.ne'

/-- S(2pqr) = 2C₂ · (p-1)/(p-2) · (q-1)/(q-2) · (r-1)/(r-2) для различных нечётных простых. -/
theorem singularSeriesFactor_eq_for_2pqr (C₂ : ℝ) (p q r : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hp_odd : 2 < p) (hq_odd : 2 < q) (hr_odd : 2 < r)
    (hpq_ne : p ≠ q) (hpr_ne : p ≠ r) (hqr_ne : q ≠ r) :
    singularSeriesFactor C₂ (2 * (p * q * r)) =
      2 * C₂ * (((p : ℝ) - 1) / ((p : ℝ) - 2)) *
              (((q : ℝ) - 1) / ((q : ℝ) - 2)) *
              (((r : ℝ) - 1) / ((r : ℝ) - 2)) := by
  rw [singularSeriesFactor, if_pos (even_two_mul (p * q * r)),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  have hcopq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq_ne
  have hcoppq_r : Nat.Coprime (p * q) r := by
    have h1 : Nat.Coprime r p := (Nat.coprime_primes hr hp).mpr hpr_ne.symm
    have h2 : Nat.Coprime r q := (Nat.coprime_primes hr hq).mpr hqr_ne.symm
    exact Nat.Coprime.symm (Nat.Coprime.mul_right h1 h2)
  rw [divisorCorrectionProduct_mul_of_coprime (mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero
        hcoppq_r,
      divisorCorrectionProduct_mul_of_coprime hp.ne_zero hq.ne_zero hcopq,
      divisorCorrectionProduct_prime p hp hp_odd,
      divisorCorrectionProduct_prime q hq hq_odd,
      divisorCorrectionProduct_prime r hr hr_odd]
  ring

/-- D(k) ≤ D(k') если все нечётные простые делители k также делят k'. -/
theorem divisorCorrectionProduct_le_of_primeFactors_subset {k k' : Nat}
    (hsub : (Nat.primeFactors k).filter (fun p => 2 < p) ⊆
            (Nat.primeFactors k').filter (fun p => 2 < p)) :
    divisorCorrectionProduct k ≤ divisorCorrectionProduct k' := by
  rw [divisorCorrectionProduct_eq_primeFactors, divisorCorrectionProduct_eq_primeFactors]
  have hge1 : ∀ p ∈ (Nat.primeFactors k').filter (fun q => 2 < q),
      (1 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    rintro p hp
    have hp_real : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    rw [le_div_iff₀ (by linarith : 0 < (p : ℝ) - 2)]; linarith
  have hextra : 1 ≤ ((Nat.primeFactors k').filter (fun q => 2 < q) \
       (Nat.primeFactors k).filter (fun q => 2 < q)).prod
       (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    apply Finset.one_le_prod
    rintro p hp; exact hge1 p (Finset.mem_sdiff.mp hp).1
  have hSnn : 0 ≤ ((Nat.primeFactors k).filter (fun q => 2 < q)).prod
      (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    apply Finset.prod_nonneg
    rintro p hp
    have hp_real : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    exact div_nonneg (by linarith) (by linarith)
  rw [← Finset.prod_sdiff hsub]
  have henn : 0 ≤ ((Nat.primeFactors k').filter (fun q => 2 < q) \
       (Nat.primeFactors k).filter (fun q => 2 < q)).prod
       (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := le_trans zero_le_one hextra
  have := mul_le_mul hextra (le_refl _) hSnn henn
  rwa [one_mul] at this

/-- `S(2) = 2C₂`: singular series для twin prime gap (промежуток 2). -/
theorem singularSeriesFactor_two (C₂ : ℝ) :
    singularSeriesFactor C₂ 2 = 2 * C₂ := by
  exact singularSeriesFactor_2_pow C₂ 1 (by omega)

/-- `S(2p^a) = 2C₂ · (p-1)/(p-2)` для нечётного простого `p` и `a > 0`. -/
theorem singularSeriesFactor_2_pow_prime (C₂ : ℝ) (p : Nat) (hp : Nat.Prime p) (hp_odd : 2 < p)
    (a : Nat) (ha : 0 < a) :
    singularSeriesFactor C₂ (2 * p ^ a) = 2 * C₂ * (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  rw [← singularSeriesFactor_2p_eq_2p_pow C₂ p hp ha, singularSeriesFactor_eq_for_2p C₂ p hp hp_odd]

/-- Singular series одинакова для `2k` и `2k'`, если `k` и `k'` имеют те же нечётные простые делители. -/
theorem singularSeriesFactor_eq_of_same_odd_prime_factors (C₂ : ℝ) {k k' : Nat}
    (_hk : k ≠ 0) (_hk' : k' ≠ 0)
    (hpf : (Nat.primeFactors k).filter (fun p => 2 < p) =
           (Nat.primeFactors k').filter (fun p => 2 < p)) :
    singularSeriesFactor C₂ (2 * k) = singularSeriesFactor C₂ (2 * k') := by
  rw [singularSeriesFactor, singularSeriesFactor,
      if_pos (even_two_mul k), if_pos (even_two_mul k'),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      divisorCorrectionProduct_eq_primeFactors,
      divisorCorrectionProduct_eq_primeFactors, hpf]

/-- `D(k) ≤ D(P_m)` если `k ∣ P_m` и `k > 0`: делители primorial не превосходят primorial по D. -/
theorem divisorCorrectionProduct_le_of_dvd_primorial (k m : Nat) (_hk : 0 < k) (hdvd : k ∣ primorial m) :
    divisorCorrectionProduct k ≤ divisorCorrectionProduct (primorial m) := by
  apply divisorCorrectionProduct_le_of_primeFactors_subset
  intro p hp
  rw [Finset.mem_filter] at hp
  have hpprime : Nat.Prime p := (Nat.mem_primeFactors.mp hp.1).1
  have hp_dvd_k : p ∣ k := (Nat.mem_primeFactors.mp hp.1).2.1
  have hp_dvd_Pm : p ∣ primorial m := hp_dvd_k.trans hdvd
  have hpmem : p ∈ (Nat.primeFactors (primorial m)).filter (fun p => 2 < p) := by
    simp only [Finset.mem_filter]
    exact ⟨Nat.mem_primeFactors.mpr ⟨hpprime, hp_dvd_Pm, (primorial_pos m).ne'⟩, hp.2⟩
  exact hpmem

/-- `D(P_m) = ∏_{i=1}^{m-1} (p_i - 1)/(p_i - 2)` для `m ≥ 2`. -/
theorem divisorCorrectionProduct_primorial (m : Nat) (hm : 2 ≤ m) :
    divisorCorrectionProduct (primorial m) =
      ((Finset.range m).filter (fun i => 0 < i)).prod
        (fun i => ((Nat.nth Nat.Prime i : ℝ) - 1) / ((Nat.nth Nat.Prime i : ℝ) - 2)) := by
  rw [divisorCorrectionProduct_eq_primeFactors, primeFactors_primorial m (by omega)]
  rw [Finset.filter_image]
  have hinj : ∀ x ∈ (Finset.range m).filter (fun i => 2 < Nat.nth Nat.Prime i),
      ∀ y ∈ (Finset.range m).filter (fun i => 2 < Nat.nth Nat.Prime i),
      Nat.nth Nat.Prime x = Nat.nth Nat.Prime y → x = y := by
    intro x _ y _ hxy
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hxy
  rw [Finset.prod_image hinj]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hirange, hlt⟩
    refine ⟨hirange, ?_⟩
    by_cases hi : i = 0
    · subst hi; rw [Nat.nth_prime_zero_eq_two] at hlt; omega
    · omega
  · rintro ⟨hirange, hipos⟩
    refine ⟨hirange, ?_⟩
    have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
    have hge : 1 ≤ i := by omega
    have hle : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime i :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).le_iff_le.mpr hge
    rw [h1] at hle
    omega

/-- `S(2·P_m) = 2C₂ · ∏_{i=1}^{m-1} (p_i-1)/(p_i-2)` для `m ≥ 2`. -/
theorem singularSeriesFactor_primorial_explicit (C₂ : ℝ) (m : Nat) (hm : 2 ≤ m) :
    singularSeriesFactor C₂ (2 * primorial m) =
      2 * C₂ * ((Finset.range m).filter (fun i => 0 < i)).prod
        (fun i => ((Nat.nth Nat.Prime i : ℝ) - 1) / ((Nat.nth Nat.Prime i : ℝ) - 2)) := by
  rw [singularSeriesFactor, if_pos (even_two_mul _),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      divisorCorrectionProduct_primorial m hm]

/-- `D(P_m)` строго возрастает: каждый новый простой делитель добавляет множитель > 1. -/
theorem divisorCorrectionProduct_primorial_strictMono (m : Nat) (hm : 1 ≤ m) :
    divisorCorrectionProduct (primorial m) < divisorCorrectionProduct (primorial (m + 1)) := by
  rw [primorial_succ]
  have hcoprime : Nat.Coprime (primorial m) (Nat.nth Nat.Prime m) := by
    unfold primorial
    rw [Nat.coprime_prod_left_iff]
    intro i hi
    have hpi : Nat.Prime (Nat.nth Nat.Prime i) := Nat.prime_nth_prime i
    have hpm : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
    have hlt : Nat.nth Nat.Prime i < Nat.nth Nat.Prime m :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).lt_iff_lt.mpr (Finset.mem_range.mp hi)
    exact (Nat.coprime_primes hpi hpm).mpr (Nat.ne_of_lt hlt)
  rw [divisorCorrectionProduct_mul_of_coprime (ne_of_gt (primorial_pos m)) (Nat.prime_nth_prime m).ne_zero hcoprime]
  have hpm : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
  have hp_odd : 2 < Nat.nth Nat.Prime m := by
    by_cases hm0 : m = 0
    · subst hm0; rw [Nat.nth_prime_zero_eq_two]; omega
    · have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
      have hge : 1 ≤ m := by omega
      have hle : 3 ≤ Nat.nth Nat.Prime m := by
        rw [← h1]
        exact (Nat.nth_strictMono Nat.infinite_setOf_prime).le_iff_le.mpr hge
      omega
  rw [divisorCorrectionProduct_prime (Nat.nth Nat.Prime m) hpm hp_odd]
  have hD_pos : 0 < divisorCorrectionProduct (primorial m) := by
    have := divisorCorrectionProduct_ge_one (primorial m); linarith
  have hp_real : 2 < (Nat.nth Nat.Prime m : ℝ) := by exact_mod_cast hp_odd
  have hfactor_gt1 : 1 < ((Nat.nth Nat.Prime m : ℝ) - 1) / ((Nat.nth Nat.Prime m : ℝ) - 2) := by
    rw [lt_div_iff₀ (by linarith : 0 < (Nat.nth Nat.Prime m : ℝ) - 2)]
    linarith
  have h := mul_lt_mul_of_pos_left hfactor_gt1 hD_pos
  rw [mul_one] at h
  exact h

/-- `S(2·P_m)` строго возрастает при `C₂ > 0`: следствие строгой монотонности `D(P_m)`. -/
theorem singularSeriesFactor_primorial_strictMono (C₂ : ℝ) (hC₂ : 0 < C₂) (m : Nat) (hm : 1 ≤ m) :
    singularSeriesFactor C₂ (2 * primorial m) < singularSeriesFactor C₂ (2 * primorial (m + 1)) := by
  rw [singularSeriesFactor, singularSeriesFactor,
      if_pos (even_two_mul _), if_pos (even_two_mul _),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  have hD := divisorCorrectionProduct_primorial_strictMono m hm
  have h2C₂ : 0 < 2 * C₂ := by positivity
  exact mul_lt_mul_of_pos_left hD h2C₂

/-- `S(2k) ≤ S(2·P_m)` если `k ∣ P_m` и `C₂ > 0`: singular series максимизируется на primorial среди делителей. -/
theorem singularSeriesFactor_le_primorial (C₂ : ℝ) (hC₂ : 0 < C₂)
    (k m : Nat) (hk : 0 < k) (hdvd : k ∣ primorial m) :
    singularSeriesFactor C₂ (2 * k) ≤ singularSeriesFactor C₂ (2 * primorial m) := by
  rw [singularSeriesFactor, singularSeriesFactor,
      if_pos (even_two_mul _), if_pos (even_two_mul _),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  have h2C₂ : 0 < 2 * C₂ := by positivity
  have hD_le := divisorCorrectionProduct_le_of_dvd_primorial k m hk hdvd
  exact (mul_le_mul_of_nonneg_left hD_le (le_of_lt h2C₂))

end
end PrimeGaps
