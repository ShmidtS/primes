import Mathlib
import Primes.Basic
import Primes.GapFrequency
import Primes.Wheel

namespace PrimeGaps

noncomputable section

open scoped BigOperators

/-! ## Singular series and twin prime constant

-/

/-- Конечное произведение sieve-факторов для пары `(n, n+g)` по простым `≤ y`. -/
def finitePairSieveFactor (g y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod (fun p =>
    if Nat.Prime p then 1 - (endpointForbiddenResidueCount g p : ℝ) / (p : ℝ) else 1)

/-- Локальная плотность выживания пары `(n, n + g)` modulo `p`. -/
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

/-- `C₂` является twin prime constant как пределом эйлерова произведения. -/
def IsTwinPrimeConstant (C₂ : ℝ) : Prop :=
  Filter.Tendsto twinPrimeConstantPartial Filter.atTop (nhds C₂)

/-- Конечное произведение поправок по нечётным простым делителям `k`. -/
def divisorCorrectionProduct (k : Nat) : ℝ :=
  (Finset.range (k + 1)).prod fun p =>
    if Nat.Prime p ∧ 2 < p ∧ p ∣ k then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

/-- Singular series для пары сдвигов `(0, g)` при заданном значении `C₂`. -/
def singularSeriesFactor (C₂ : ℝ) (g : Nat) : ℝ :=
  if Even g then 2 * C₂ * divisorCorrectionProduct (g / 2) else 0

/-- Конечный wheel-ряд сходится к singular series factor при `y → ∞`. -/
def finiteWheelSingularSeriesLimit (g : Nat) (C₂ : ℝ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto (fun y => finiteWheelSingularSeries g y) Filter.atTop (nhds L) ∧
    L = singularSeriesFactor C₂ g

/-- Интеграл `li₂(x) = ∫₂ˣ dt / log² t`. -/
def logarithmicIntegral₂ (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2

/-! ### singularSeriesFactor properties -/

/-- Нечётные промежутки имеют нулевой singular series. -/
theorem singularSeriesFactor_of_odd {C₂ : ℝ} {g : Nat} (hg : Odd g) :
    singularSeriesFactor C₂ g = 0 := by
  simp [singularSeriesFactor, Nat.not_even_iff_odd.mpr hg]

/-- Для чётного gap формула сводится к произведению по простым делителям половины gap. -/
theorem singularSeriesFactor_even (C₂ : ℝ) (k : Nat) :
    singularSeriesFactor C₂ (2 * k) = 2 * C₂ * divisorCorrectionProduct k := by
  simp [singularSeriesFactor]

/-- Конечная поправка равна произведению по нечётным простым делителям. -/
theorem divisorCorrectionProduct_eq_primeFactors (k : Nat) :
    divisorCorrectionProduct k =
      ((Nat.primeFactors k).filter (fun p => 2 < p)).prod
        (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  by_cases hk0 : k = 0
  · subst k
    simp [divisorCorrectionProduct]
  · rw [divisorCorrectionProduct, ← Finset.prod_filter]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
    constructor
    · intro h
      exact ⟨⟨h.2.1, h.2.2.2, hk0⟩, h.2.2.1⟩
    · intro h
      rcases h with ⟨⟨hprime, hdvd, _⟩, hgt⟩
      have hle : p ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd
      exact ⟨Nat.lt_succ_iff.mpr hle, hprime, hgt, hdvd⟩

/-- Явная формула singular series для чётного gap через нечётные простые делители `k`. -/
theorem singularSeriesFactor_even_correct (C₂ : ℝ) (k : Nat) :
    singularSeriesFactor C₂ (2 * k) =
      2 * C₂ * ((Nat.primeFactors k).filter (fun p => 2 < p)).prod
        (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  rw [singularSeriesFactor_even, divisorCorrectionProduct_eq_primeFactors]

/-! ### Singular series positivity and exact values -/

/-- `divisorCorrectionProduct k` — произведение положительных множителей `(p-1)/(p-2) > 0`
для всех нечётных простых `p ≥ 3`. -/
theorem divisorCorrectionProduct_pos {k : Nat} (hk : 0 < k) :
    0 < divisorCorrectionProduct k := by
  rw [divisorCorrectionProduct_eq_primeFactors]
  apply Finset.prod_pos
  intro p hp
  simp only [Finset.mem_filter] at hp
  have hp_gt2 : 2 < p := hp.2
  have hp_prime : Nat.Prime p := (Nat.mem_primeFactors.mp hp.1).1
  have hp_real_gt1 : 1 < (p : ℝ) := by exact_mod_cast hp_prime.one_lt
  have hp_real_gt2 : 2 < (p : ℝ) := by exact_mod_cast hp_gt2
  have hp_sub1 : 0 < (p : ℝ) - 1 := by linarith
  have hp_sub2 : 0 < (p : ℝ) - 2 := by linarith
  exact div_pos hp_sub1 hp_sub2

/-- `singularSeriesFactor` положителен для чётного `g = 2k`, `k > 0`, при `C₂ > 0`.
Это необходимо для осмысленности гипотезы Харди–Литтлвуда. -/
theorem singularSeriesFactor_pos_of_even {C₂ : ℝ} {k : Nat}
    (hC₂ : 0 < C₂) (hk : 0 < k) :
    0 < singularSeriesFactor C₂ (2 * k) := by
  rw [singularSeriesFactor_even]
  exact mul_pos (mul_pos (by linarith) hC₂) (divisorCorrectionProduct_pos hk)

/-- Для `g = 2` (twin prime gap) `divisorCorrectionProduct(1) = 1` (пустое произведение,
так как у 1 нет простых делителей). -/
theorem divisorCorrectionProduct_one :
    divisorCorrectionProduct 1 = 1 := by
  rw [divisorCorrectionProduct_eq_primeFactors, Nat.primeFactors_one]
  simp

/-- Точное значение singular series для twin prime gap `g = 2`:
`𝔖(2) = 2 C₂`. Это фундаментальная константа гипотезы о простых близнецах. -/
theorem singularSeriesFactor_eq_2C2_for_g_2 (C₂ : ℝ) :
    singularSeriesFactor C₂ 2 = 2 * C₂ := by
  have h2 : 2 = 2 * 1 := by omega
  rw [h2, singularSeriesFactor_even, divisorCorrectionProduct_one]
  ring

/-- Для `g = 4` (cousin prime gap) `k = 2`, и у 2 нет нечётных простых делителей,
поэтому `𝔖(4) = 2 C₂`. -/
theorem singularSeriesFactor_eq_2C2_for_g_4 (C₂ : ℝ) :
    singularSeriesFactor C₂ 4 = 2 * C₂ := by
  have h4 : 4 = 2 * 2 := by omega
  rw [h4, singularSeriesFactor_even]
  have : divisorCorrectionProduct 2 = 1 := by
    rw [divisorCorrectionProduct_eq_primeFactors]
    have hpf : (Nat.primeFactors 2 : Finset Nat).filter (fun p => 2 < p) = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.notMem_empty, false_implies]
      constructor
      · intro ⟨hmem, hgt2⟩
        have hmem' : p ∈ Nat.primeFactors 2 := hmem
        rw [Nat.mem_primeFactors] at hmem'
        rcases hmem' with ⟨hprime, hdvd, hne⟩
        have : p = 2 := by
          have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
          have hge : 2 ≤ p := hprime.two_le
          omega
        omega
      · exact fun h => h.elim
    rw [hpf]
    simp
  rw [this]
  ring

/-- Для `g = 6` (sexy prime gap) `k = 3`, и единственный нечётный простой делитель
равен `3`, поэтому `𝔖(6) = 2 C₂ · (3-1)/(3-2) = 4 C₂`. -/
theorem singularSeriesFactor_eq_4C2_for_g_6 (C₂ : ℝ) :
    singularSeriesFactor C₂ 6 = 4 * C₂ := by
  have h6 : 6 = 2 * 3 := by omega
  rw [h6, singularSeriesFactor_even]
  have : divisorCorrectionProduct 3 = 2 := by
    rw [divisorCorrectionProduct_eq_primeFactors]
    have hpf : (Nat.primeFactors 3 : Finset Nat).filter (fun p => 2 < p) = {3} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro ⟨hmem, hgt2⟩
        have hmem' : p ∈ Nat.primeFactors 3 := hmem
        rw [Nat.mem_primeFactors] at hmem'
        rcases hmem' with ⟨hprime, hdvd, hne⟩
        have hle : p ≤ 3 := Nat.le_of_dvd (by omega) hdvd
        omega
      · rintro rfl
        refine ⟨?_, by omega⟩
        exact Nat.mem_primeFactors.mpr ⟨by decide, by decide, by decide⟩
    rw [hpf]
    simp
    norm_num
  rw [this]
  ring

/-- Связь с wheel: глобальная формула — базовая константа `2 C₂` и поправки по `p ∣ k`. -/
theorem singularSeriesFactor_eq_wheel_divisor_product (C₂ : ℝ) (k : Nat) :
    singularSeriesFactor C₂ (2 * k) = 2 * C₂ *
      (Finset.range (k + 1)).prod (fun p =>
        if Nat.Prime p ∧ 2 < p ∧ p ∣ k then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1) := by
  simp [singularSeriesFactor_even, divisorCorrectionProduct]

/-! ### finiteWheelSingularSeries properties -/

/-- Глобальная wheel-series равна survival-произведению с делением на наивные endpoint-плотности. -/
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

/-- Wheel-ряд, умноженный на квадратичное произведение наивных плотностей, даёт sieve-фактор. -/
theorem finiteWheelSingularSeries_eq_finitePairSieveFactor_normalized (g y : Nat) :
    finiteWheelSingularSeries g y * (Finset.range (y + 1)).prod (fun p =>
      if Nat.Prime p then (1 - 1 / (p : ℝ)) ^ 2 else 1) =
    finitePairSieveFactor g y := by
  let denom := (Finset.range (y + 1)).prod (fun p =>
    if Nat.Prime p then (1 - 1 / (p : ℝ)) ^ 2 else (1 : ℝ))
  have hdenom_ne_zero : denom ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p _
    by_cases hprime : Nat.Prime p
    · rw [if_pos hprime]
      have hp_pos : 0 < (p : ℝ) := by exact_mod_cast Nat.Prime.pos hprime
      have hp_gt_one : 1 < (p : ℝ) := by exact_mod_cast Nat.Prime.one_lt hprime
      have h_div_lt_one : 1 / (p : ℝ) < 1 := (div_lt_one hp_pos).mpr hp_gt_one
      exact pow_ne_zero 2 (sub_ne_zero_of_ne (ne_of_lt h_div_lt_one).symm)
    · rw [if_neg hprime]
      exact one_ne_zero
  rw [finiteWheelSingularSeries_eq_finitePairSieveFactor_div_sq g y]
  exact div_mul_cancel₀ _ hdenom_ne_zero

/-! ### wheelLocalSingularFactor general formula -/

/-- Явная форма локального wheel-множителя через делимость `p ∣ g`. -/
theorem wheelLocalSingularFactor_eq_singular (g p : Nat) (_hp : Nat.Prime p) :
    wheelLocalSingularFactor g p =
      (1 - (if p ∣ g then (1 : ℝ) else (2 : ℝ)) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2 := by
  simp [wheelLocalSingularFactor, wheelEndpointSurvivalDensity, endpointForbiddenResidueCount]

/-! ### Connection to twin prime constant -/

/-- Алгебраическое тождество для wheel-множителя при `p > 2`. -/
private lemma algebraic_identity_wheel (p : ℝ) (hp : 2 < p) :
    (1 - 2 * p⁻¹) / (1 - p⁻¹) ^ 2 = 1 - ((p - 1) ^ 2)⁻¹ := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hdenom : (1 - p⁻¹) ≠ 0 := by
    have : p⁻¹ < 1 := inv_lt_one₀ (by linarith) |>.2 (by linarith)
    linarith
  field_simp [hp0, hp1, hdenom]
  ring

/-- Алгебраическое тождество для wheel-множителя при `p > 2` (в форме деления). -/
private lemma algebraic_identity_wheel_div (p : ℝ) (hp : 2 < p) :
    (1 - 2 / p) / (1 - 1 / p) ^ 2 = 1 - 1 / (p - 1) ^ 2 := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hdenom : (1 - 1 / p) ≠ 0 := by
    have : 1 / p < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  field_simp [hp0, hp1, hdenom]
  ring

/-! ### New theorems for arbitrary primes and gaps -/

/-- Локальный множитель колеса через делимость:
общая формула для произвольного `g` и простого `p`. -/
theorem wheelLocalSingularFactor_dvd_iff (g p : Nat) (hp : Nat.Prime p) :
    wheelLocalSingularFactor g p = if p ∣ g then (p : ℝ) / ((p : ℝ) - 1)
      else (1 - 2 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2 := by
  rw [wheelLocalSingularFactor_eq_singular g p hp]
  by_cases h : p ∣ g
  · simp [h]
    have hp_pos : (p : ℝ) > 0 := by exact_mod_cast hp.pos
    have hp_gt_one : (p : ℝ) > 1 := by exact_mod_cast hp.one_lt
    have hsub_pos : (p : ℝ) - 1 > 0 := by linarith
    field_simp [hsub_pos.ne']
  · simp [h]

/-- Конечный множитель для чётного gap: произведение по нечётным простым делителям `k`,
не превосходящим `y`. -/
def finiteWheelEvenFactor (k y : Nat) : ℝ :=
  ((Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ 2 < p ∧ p ∣ k)).prod
    (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- Для нечётного `g` и `y ≥ 2` wheel-серия равна нулю,
так как фактор при `p = 2` зануляется. -/
theorem finiteWheelSingularSeries_odd_eq_zero {g y : Nat}
    (hg : Odd g) (hy : 2 ≤ y) :
    finiteWheelSingularSeries g y = 0 := by
  rw [finiteWheelSingularSeries]
  let s := Finset.range (y + 1)
  have h2_mem : 2 ∈ s := by simp [s]; omega
  have h2_not_dvd : ¬(2 : ℕ) ∣ g := by
    intro h
    have heven : Even g := even_iff_two_dvd.mpr h
    exact Nat.not_odd_iff_even.mpr heven hg
  have hfactor0 : wheelLocalSingularFactor g 2 = 0 := by
    rw [wheelLocalSingularFactor_eq_singular g 2 (by decide)]
    simp only [h2_not_dvd, if_false]
    norm_num
  have hsplit : s.prod (fun p => if Nat.Prime p then wheelLocalSingularFactor g p else 1)
      = (s.filter Nat.Prime).prod (fun p => wheelLocalSingularFactor g p) := by
    rw [← Finset.prod_filter]
  rw [hsplit]
  have h2_prime_mem : 2 ∈ s.filter Nat.Prime := by
    simp only [Finset.mem_filter]
    exact ⟨by omega, by decide⟩
  exact Finset.prod_eq_zero h2_prime_mem hfactor0

/-- Общая формула `finiteWheelSingularSeries` для чётного gap `g = 2k`.
Каждый нечётный простой делитель `k` вносит множитель `(p-1)/(p-2)`,
а все остальные нечётные простые дают тот же фактор,
что и в `twinPrimeConstantPartial`. -/
theorem finiteWheelSingularSeries_even_eq (k y : Nat) (hy : 2 ≤ y) :
    finiteWheelSingularSeries (2 * k) y =
      2 * finiteWheelEvenFactor k y * twinPrimeConstantPartial y := by
  rw [finiteWheelSingularSeries, twinPrimeConstantPartial, finiteWheelEvenFactor]
  let s := Finset.range (y + 1)
  let oddDivs := s.filter (fun p => Nat.Prime p ∧ 2 < p ∧ p ∣ k)
  let oddNonDivs := s.filter (fun p => Nat.Prime p ∧ 2 < p ∧ ¬p ∣ k)
  let allOdd := s.filter (fun p => Nat.Prime p ∧ 2 < p)
  have h2_mem : 2 ∈ s := by simp [s]; omega
  have h2_prime : Nat.Prime 2 := by decide
  have h2_not_odd : 2 ∉ allOdd := by simp [allOdd, s]
  -- Split all primes into {2} and odd primes
  have hsplit_prime : s.filter Nat.Prime = insert 2 allOdd := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, s, allOdd, Finset.mem_range]
    constructor
    · intro ⟨hlt, hpr⟩
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · have hp2gt : 2 < p := by
          have htwo_le : 2 ≤ p := Nat.Prime.two_le hpr
          omega
        exact Or.inr ⟨hlt, hpr, hp2gt⟩
    · intro h
      cases h with
      | inl h2 =>
        subst h2
        exact ⟨by omega, h2_prime⟩
      | inr hodd => exact ⟨hodd.1, hodd.2.1⟩
  -- Split odd primes into divisors and non-divisors of k
  have hsplit_odd : allOdd = oddDivs ∪ oddNonDivs := by
    ext p
    simp only [allOdd, oddDivs, oddNonDivs, s, Finset.mem_filter,
      Finset.mem_union, Finset.mem_range]
    constructor
    · intro ⟨hlt, hpr, hgt2⟩
      by_cases hpk : p ∣ k
      · exact Or.inl ⟨hlt, hpr, hgt2, hpk⟩
      · exact Or.inr ⟨hlt, hpr, hgt2, hpk⟩
    · intro h
      cases h with
      | inl hd => exact ⟨hd.1, hd.2.1, hd.2.2.1⟩
      | inr hnd => exact ⟨hnd.1, hnd.2.1, hnd.2.2.1⟩
  have hdisj : Disjoint oddDivs oddNonDivs := by
    rw [Finset.disjoint_left]
    intro p hp hnp
    simp only [oddDivs, oddNonDivs, s, Finset.mem_filter, Finset.mem_range] at hp hnp
    have h_dvd : p ∣ k := hp.2.2.2
    have h_not_dvd : ¬p ∣ k := hnp.2.2.2
    exact h_not_dvd h_dvd
  -- Rewrite the LHS product over primes as product over {2} ∪ oddDivs ∪ oddNonDivs
  have hlhs : s.prod (fun p => if Nat.Prime p then
      wheelLocalSingularFactor (2 * k) p else 1) =
      (s.filter Nat.Prime).prod (fun p => wheelLocalSingularFactor (2 * k) p) := by
    rw [← Finset.prod_filter]
  rw [hlhs]
  rw [hsplit_prime]
  rw [Finset.prod_insert h2_not_odd]
  -- Factor at p=2
  have hfactor2 : wheelLocalSingularFactor (2 * k) 2 = 2 := by
    rw [wheelLocalSingularFactor_eq_singular (2 * k) 2 (by decide)]
    have h2_dvd : (2 : ℕ) ∣ 2 * k := Nat.dvd_mul_right 2 k
    simp only [h2_dvd, if_true]
    norm_num
  rw [hfactor2]
  -- Split allOdd product into oddDivs and oddNonDivs
  rw [hsplit_odd]
  rw [Finset.prod_union hdisj]
  -- Product over oddDivs
  have hprod_div : oddDivs.prod (fun p => wheelLocalSingularFactor (2 * k) p) =
      oddDivs.prod (fun p =>
        ((p : ℝ) - 1) / ((p : ℝ) - 2) * (1 - 1 / ((p : ℝ) - 1) ^ 2)) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hp_prime : Nat.Prime p := by
      simp only [oddDivs, s, Finset.mem_filter, Finset.mem_range] at hp
      exact hp.2.1
    have hp_gt2 : 2 < p := by
      simp only [oddDivs, s, Finset.mem_filter, Finset.mem_range] at hp
      exact hp.2.2.1
    have hp_dvd_k : p ∣ k := by
      simp only [oddDivs, s, Finset.mem_filter, Finset.mem_range] at hp
      exact hp.2.2.2
    have hp_dvd_2k : p ∣ 2 * k := dvd_mul_of_dvd_right hp_dvd_k 2
    rw [wheelLocalSingularFactor_eq_singular (2 * k) p hp_prime]
    simp only [hp_dvd_2k, if_true]
    have hp_real : (p : ℝ) > 2 := by exact_mod_cast hp_gt2
    have hp_sub1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
    have hp_sub2_ne : (p : ℝ) - 2 ≠ 0 := by linarith
    have hp_ne0 : (p : ℝ) ≠ 0 := by linarith
    -- Simplify the equality directly
    field_simp [hp_ne0, hp_sub1_ne, hp_sub2_ne]
    ring
  rw [hprod_div]
  -- Product over oddNonDivs
  have hprod_nondiv : oddNonDivs.prod (fun p => wheelLocalSingularFactor (2 * k) p) =
      oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hp_prime : Nat.Prime p := by
      simp only [oddNonDivs, s, Finset.mem_filter, Finset.mem_range] at hp
      exact hp.2.1
    have hp_gt2 : 2 < p := by
      simp only [oddNonDivs, s, Finset.mem_filter, Finset.mem_range] at hp
      exact hp.2.2.1
    have hp_not_dvd_k : ¬p ∣ k := by
      simp only [oddNonDivs, s, Finset.mem_filter, Finset.mem_range] at hp
      exact hp.2.2.2
    have hp_not_dvd_2k : ¬p ∣ 2 * k := by
      intro hd
      have h2k : p ∣ 2 * k := hd
      have hor : p ∣ 2 ∨ p ∣ k := (Nat.Prime.dvd_mul hp_prime).mp h2k
      cases hor with
      | inl h2 =>
        have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp h2
        omega
      | inr hk => exact hp_not_dvd_k hk
    rw [wheelLocalSingularFactor_eq_singular (2 * k) p hp_prime]
    simp only [hp_not_dvd_2k, if_false]
    exact algebraic_identity_wheel_div (p : ℝ) (by exact_mod_cast hp_gt2)
  rw [hprod_nondiv]
  -- Separate the oddDivs product into finiteWheelEvenFactor part and twin part
  have hsplit_div_prod : oddDivs.prod (fun p =>
      ((p : ℝ) - 1) / ((p : ℝ) - 2) * (1 - 1 / ((p : ℝ) - 1) ^ 2)) =
      oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
      oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    rw [← Finset.prod_mul_distrib]
  rw [hsplit_div_prod]
  -- Combine oddDivs twin part with oddNonDivs twin part
  have h_twin_prod : oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) *
      oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) =
      (s.filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    have h_eq : s.filter (fun p => Nat.Prime p ∧ 2 < p) = oddDivs ∪ oddNonDivs := hsplit_odd
    rw [h_eq]
    rw [Finset.prod_union hdisj]
  -- Show twinPrimeConstantPartial = s.filter(...).prod(...)
  have htwin : s.prod (fun p =>
      if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) =
      (s.filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    rw [Finset.prod_filter]
  -- Rearrange: 2 * ((∏correction * ∏twin_div) * ∏twin_nondiv) =
  --           2 * ∏correction * (∏twin_div * ∏twin_nondiv)
  -- so we can rewrite h_twin_prod on the inner product.
  have h_rearrange :
      2 * ((oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
              oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ))) *
            oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ))) =
      2 * oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        (oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) *
         oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ))) := by
    ring
  rw [h_rearrange]
  rw [h_twin_prod]
  rw [← htwin]
  -- Goal is now definitionally equal after all rewrites.

end

end PrimeGaps
