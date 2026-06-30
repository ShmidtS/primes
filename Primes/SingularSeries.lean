import Mathlib
import Primes.Basic
import Primes.GapFrequency
import Primes.Wheel

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
    constructor
    · intro h; exact ⟨⟨h.2.1, h.2.2.2, hk0⟩, h.2.2.1⟩
    · intro h; rcases h with ⟨⟨hprime, hdvd, _⟩, hgt⟩
      have hle : p ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd
      exact ⟨Nat.lt_succ_iff.mpr hle, hprime, hgt, hdvd⟩

/-! ### Exact singular series values -/

/-- `𝔖(2) = 2 C₂` — фундаментальная константа гипотезы о простых близнецах. -/
theorem singularSeriesFactor_eq_2C2_for_g_2 (C₂ : ℝ) :
    singularSeriesFactor C₂ 2 = 2 * C₂ := by
  unfold singularSeriesFactor
  rw [if_pos even_two, show 2 / 2 = 1 from Nat.div_self (by omega),
      divisorCorrectionProduct_eq_primeFactors, Nat.primeFactors_one]
  simp

/-- `𝔖(4) = 2 C₂` (cousin prime gap). -/
theorem singularSeriesFactor_eq_2C2_for_g_4 (C₂ : ℝ) :
    singularSeriesFactor C₂ 4 = 2 * C₂ := by
  unfold singularSeriesFactor
  rw [if_pos (even_iff_two_dvd.mpr (by decide : (2:Nat) ∣ 4)), show 4 / 2 = 2 from by decide,
      divisorCorrectionProduct_eq_primeFactors]
  have hpf : (Nat.primeFactors 2 : Finset Nat).filter (fun p => 2 < p) = ∅ := by
    ext p
    simp only [Finset.mem_filter, Finset.notMem_empty]
    constructor
    · intro ⟨hmem, hgt2⟩
      rw [Nat.mem_primeFactors] at hmem
      rcases hmem with ⟨hprime, hdvd, _⟩
      have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
      have hge : 2 ≤ p := hprime.two_le
      omega
    · exact fun h => h.elim
  rw [hpf]; simp

/-- `𝔖(6) = 4 C₂` (sexy prime gap). -/
theorem singularSeriesFactor_eq_4C2_for_g_6 (C₂ : ℝ) :
    singularSeriesFactor C₂ 6 = 4 * C₂ := by
  unfold singularSeriesFactor
  rw [if_pos (even_iff_two_dvd.mpr (by decide : (2:Nat) ∣ 6)),
      show 6 / 2 = 3 from by decide,
      divisorCorrectionProduct_eq_primeFactors]
  have hpf : (Nat.primeFactors 3 : Finset Nat).filter (fun p => 2 < p) = {3} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro ⟨hmem, hgt2⟩
      rw [Nat.mem_primeFactors] at hmem
      rcases hmem with ⟨hprime, hdvd, _⟩
      have hle : p ≤ 3 := Nat.le_of_dvd (by omega) hdvd
      omega
    · rintro rfl
      refine ⟨?_, by omega⟩
      exact Nat.mem_primeFactors.mpr ⟨by decide, by decide, by decide⟩
  rw [hpf]; simp; norm_num; ring

/-! ### Structural properties of D and S — new results -/

/-- `divisorCorrectionProduct` мультипликативен по взаимно простым аргументам:
для coprime k, k', `D(k*k') = D(k) * D(k')`. -/
theorem divisorCorrectionProduct_mul_of_coprime {k k' : Nat}
    (_hk : k ≠ 0) (_hk' : k' ≠ 0) (hcoprime : Nat.Coprime k k') :
    divisorCorrectionProduct (k * k') =
      divisorCorrectionProduct k * divisorCorrectionProduct k' := by
  rw [divisorCorrectionProduct_eq_primeFactors,
      divisorCorrectionProduct_eq_primeFactors,
      divisorCorrectionProduct_eq_primeFactors,
      hcoprime.primeFactors_mul]
  have h_filter_union : (Nat.primeFactors k ∪ Nat.primeFactors k').filter
      (fun p => 2 < p) =
      (Nat.primeFactors k).filter (fun p => 2 < p) ∪
      (Nat.primeFactors k').filter (fun p => 2 < p) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_union]; tauto
  rw [h_filter_union]
  have h_disj : Disjoint ((Nat.primeFactors k).filter (fun p => 2 < p))
      ((Nat.primeFactors k').filter (fun p => 2 < p)) := by
    apply Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    exact hcoprime.disjoint_primeFactors
  rw [Finset.prod_union h_disj]

/-- `D` зависит только от множества простых делителей, не от кратностей. -/
theorem divisorCorrectionProduct_eq_of_same_primeFactors {k k' : Nat}
    (hpf : Nat.primeFactors k = Nat.primeFactors k') :
    divisorCorrectionProduct k = divisorCorrectionProduct k' := by
  rw [divisorCorrectionProduct_eq_primeFactors, divisorCorrectionProduct_eq_primeFactors, hpf]

/-- `D(k^a) = D(k)` для `a > 0`. -/
theorem divisorCorrectionProduct_pow_eq (k : Nat) (ha : 0 < a) :
    divisorCorrectionProduct (k ^ a) = divisorCorrectionProduct k := by
  apply divisorCorrectionProduct_eq_of_same_primeFactors
  exact Nat.primeFactors_pow k (Nat.ne_of_gt ha)

/-- `D(p) = (p-1)/(p-2)` для нечётного простого `p`. -/
theorem divisorCorrectionProduct_prime (p : Nat) (hp : Nat.Prime p) (hp_odd : 2 < p) :
    divisorCorrectionProduct p = ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  rw [divisorCorrectionProduct_eq_primeFactors]
  have hpf : (Nat.primeFactors p).filter (fun q => 2 < q) = {p} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro ⟨hmem, hgt2⟩
      rw [Nat.mem_primeFactors] at hmem
      rcases hmem with ⟨hprime, hdvd, _⟩
      have : q = p := (Nat.prime_dvd_prime_iff_eq hprime hp).mp hdvd
      subst this; exact rfl
    · rintro rfl
      exact ⟨Nat.mem_primeFactors.mpr ⟨hp, dvd_rfl, hp.ne_zero⟩, hp_odd⟩
  rw [hpf, Finset.prod_singleton]

/-- **S(2p) = 2C₂ · (p-1)/(p-2)** для нечётного простого `p`. -/
theorem singularSeriesFactor_eq_for_2p (C₂ : ℝ) (p : Nat) (hp : Nat.Prime p) (hp_odd : 2 < p) :
    singularSeriesFactor C₂ (2 * p) = 2 * C₂ * (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  rw [singularSeriesFactor, if_pos (even_two_mul p)]
  have hdiv : (2 * p) / 2 = p := Nat.mul_div_cancel_left _ (by omega)
  rw [hdiv, divisorCorrectionProduct_prime p hp hp_odd]

/-- **S(2p) = S(2p^a)** — singular series инвариантна при возведении делителя в степень. -/
theorem singularSeriesFactor_2p_eq_2p_pow (C₂ : ℝ) (p : Nat) (_hp : Nat.Prime p) (ha : 0 < a) :
    singularSeriesFactor C₂ (2 * p) = singularSeriesFactor C₂ (2 * p ^ a) := by
  rw [singularSeriesFactor, singularSeriesFactor,
      if_pos (even_two_mul p), if_pos (even_two_mul (p ^ a))]
  have hdiv1 : (2 * p) / 2 = p := Nat.mul_div_cancel_left _ (by omega)
  have hdiv2 : (2 * p ^ a) / 2 = p ^ a := Nat.mul_div_cancel_left _ (by omega)
  rw [hdiv1, hdiv2, divisorCorrectionProduct_pow_eq p ha]

/-- **S(2pq) = 2C₂ · (p-1)/(p-2) · (q-1)/(q-2)** для различных нечётных простых p, q. -/
theorem singularSeriesFactor_eq_for_2pq (C₂ : ℝ) (p q : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hp_odd : 2 < p) (hq_odd : 2 < q)
    (hpq_ne : p ≠ q) :
    singularSeriesFactor C₂ (2 * (p * q)) =
      2 * C₂ * (((p : ℝ) - 1) / ((p : ℝ) - 2)) * (((q : ℝ) - 1) / ((q : ℝ) - 2)) := by
  rw [singularSeriesFactor, if_pos (even_two_mul (p * q))]
  have hdiv : (2 * (p * q)) / 2 = p * q := Nat.mul_div_cancel_left _ (by omega)
  rw [hdiv]
  have hcoprime : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq_ne
  rw [divisorCorrectionProduct_mul_of_coprime hp.ne_zero hq.ne_zero hcoprime,
      divisorCorrectionProduct_prime p hp hp_odd,
      divisorCorrectionProduct_prime q hq hq_odd]
  ring

/-- Singular series мультипликативна по взаимно простым половинам gap. -/
theorem singularSeriesFactor_mul_of_coprime (C₂ : ℝ) {k k' : Nat}
    (hk : k ≠ 0) (hk' : k' ≠ 0) (hcoprime : Nat.Coprime k k') :
    singularSeriesFactor C₂ (2 * (k * k')) =
      singularSeriesFactor C₂ (2 * k) * singularSeriesFactor C₂ (2 * k') / (2 * C₂) := by
  rw [singularSeriesFactor, singularSeriesFactor, singularSeriesFactor,
      if_pos (even_two_mul (k * k')), if_pos (even_two_mul k), if_pos (even_two_mul k')]
  have hdiv1 : (2 * (k * k')) / 2 = k * k' := Nat.mul_div_cancel_left _ (by omega)
  have hdiv2 : (2 * k) / 2 = k := Nat.mul_div_cancel_left _ (by omega)
  have hdiv3 : (2 * k') / 2 = k' := Nat.mul_div_cancel_left _ (by omega)
  rw [hdiv1, hdiv2, hdiv3]
  rw [divisorCorrectionProduct_mul_of_coprime hk hk' hcoprime]
  by_cases hC₂ : C₂ = 0
  · simp [hC₂]
  · have h2C₂ : (2 : ℝ) * C₂ ≠ 0 := mul_ne_zero two_ne_zero hC₂
    field_simp [h2C₂]

/-- `D(2^a) = 1`: у степени 2 нет нечётных простых делителей. -/
theorem divisorCorrectionProduct_pow_two (a : Nat) :
    divisorCorrectionProduct (2 ^ a) = 1 := by
  rw [divisorCorrectionProduct_eq_primeFactors]
  by_cases ha : a = 0
  · subst a; simp [Nat.primeFactors_one]
  · have hpf : Nat.primeFactors (2 ^ a) = {2} :=
      Nat.primeFactors_prime_pow (Nat.ne_of_gt (by omega : 0 < a)) Nat.prime_two
    rw [hpf]
    have h_filter : ({2} : Finset Nat).filter (fun p => 2 < p) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp; simp only [Finset.mem_singleton] at hp; subst hp; omega
    rw [h_filter]; simp

/-- `D(2^a · m) = D(m)` для нечётного m: 2 не вносит вклад в D. -/
theorem divisorCorrectionProduct_pow_two_mul (a : Nat) (m : Nat) (hm : Odd m) :
    divisorCorrectionProduct (2 ^ a * m) = divisorCorrectionProduct m := by
  rw [divisorCorrectionProduct_eq_primeFactors, divisorCorrectionProduct_eq_primeFactors]
  by_cases ha : a = 0
  · subst a; simp
  · have h2a_ne : (2 : Nat) ^ a ≠ 0 := by
      have h : 0 < 2 ^ a := by cases a <;> simp [Nat.pow_succ, Nat.zero_lt_succ]
      omega
    have hm_ne : m ≠ 0 := by
      have hpos : 0 < m := hm.pos
      intro h; subst h; simp at hpos
    rw [Nat.primeFactors_mul h2a_ne hm_ne]
    have hpf_2a : Nat.primeFactors (2 ^ a) = {2} :=
      Nat.primeFactors_prime_pow (Nat.ne_of_gt (by omega : 0 < a)) Nat.prime_two
    rw [hpf_2a, Finset.filter_union]
    have h_filter_2 : ({2} : Finset Nat).filter (fun p => 2 < p) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp; simp only [Finset.mem_singleton] at hp; subst hp; omega
    rw [h_filter_2, Finset.empty_union]

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

/-- Wheel-ряд × квадратичные плотности = sieve-фактор. -/
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
      have hp_gt_one : 1 < (p : ℝ) := by exact_mod_cast Nat.Prime.one_lt hprime
      have h_div_lt_one : 1 / (p : ℝ) < 1 := (div_lt_one (by positivity)).mpr hp_gt_one
      exact pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm (ne_of_lt h_div_lt_one)))
    · rw [if_neg hprime]; exact one_ne_zero
  rw [finiteWheelSingularSeries_eq_finitePairSieveFactor_div_sq g y]
  exact div_mul_cancel₀ _ hdenom_ne_zero

/-! ### wheelLocalSingularFactor -/

/-- Явная форма локального wheel-множителя через делимость `p ∣ g`. -/
theorem wheelLocalSingularFactor_eq_singular (g p : Nat) (_hp : Nat.Prime p) :
    wheelLocalSingularFactor g p =
      (1 - (if p ∣ g then (1 : ℝ) else (2 : ℝ)) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2 := by
  simp [wheelLocalSingularFactor, wheelEndpointSurvivalDensity, endpointForbiddenResidueCount]

/-- Локальный множитель через делимость для произвольного `g` и простого `p`. -/
theorem wheelLocalSingularFactor_dvd_iff (g p : Nat) (hp : Nat.Prime p) :
    wheelLocalSingularFactor g p = if p ∣ g then (p : ℝ) / ((p : ℝ) - 1)
      else (1 - 2 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2 := by
  rw [wheelLocalSingularFactor_eq_singular g p hp]
  by_cases h : p ∣ g
  · simp [h]
    have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hsub_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    field_simp [hsub_pos.ne']
  · simp [h]

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
  rw [finiteWheelSingularSeries]
  let s := Finset.range (y + 1)
  have h2_mem : 2 ∈ s := Finset.mem_range.mpr (by omega)
  have h2_not_dvd : ¬(2 : ℕ) ∣ g := fun h =>
    Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h) hg
  have hfactor0 : wheelLocalSingularFactor g 2 = 0 := by
    rw [wheelLocalSingularFactor_eq_singular g 2 (by decide)]
    simp only [h2_not_dvd, if_false]; norm_num
  have hsplit : s.prod (fun p => if Nat.Prime p then wheelLocalSingularFactor g p else 1)
      = (s.filter Nat.Prime).prod (fun p => wheelLocalSingularFactor g p) := by
    rw [← Finset.prod_filter]
  rw [hsplit]
  exact Finset.prod_eq_zero
    (by simp only [Finset.mem_filter, Finset.mem_range, true_and]
        exact ⟨by omega, by decide⟩) hfactor0

/-- Общая формула `finiteWheelSingularSeries` для чётного gap `g = 2k`. -/
theorem finiteWheelSingularSeries_even_eq (k y : Nat) (hy : 2 ≤ y) :
    finiteWheelSingularSeries (2 * k) y =
      2 * finiteWheelEvenFactor k y * twinPrimeConstantPartial y := by
  rw [finiteWheelSingularSeries, twinPrimeConstantPartial, finiteWheelEvenFactor]
  let s := Finset.range (y + 1)
  let oddDivs := s.filter (fun p => Nat.Prime p ∧ 2 < p ∧ p ∣ k)
  let oddNonDivs := s.filter (fun p => Nat.Prime p ∧ 2 < p ∧ ¬p ∣ k)
  let allOdd := s.filter (fun p => Nat.Prime p ∧ 2 < p)
  have h2_prime : Nat.Prime 2 := by decide
  have h2_not_odd : 2 ∉ allOdd := by simp [allOdd, s]
  have hsplit_prime : s.filter Nat.Prime = insert 2 allOdd := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, s, allOdd, Finset.mem_range]
    constructor
    · intro ⟨hlt, hpr⟩
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · have htwo_le : 2 ≤ p := Nat.Prime.two_le hpr
        have hp2gt : 2 < p := by omega
        exact Or.inr ⟨hlt, hpr, hp2gt⟩
    · intro h
      cases h with
      | inl h2 => subst h2; exact ⟨by omega, h2_prime⟩
      | inr hodd => exact ⟨hodd.1, hodd.2.1⟩
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
    exact (Finset.mem_filter.mp hnp).2.2.2 (Finset.mem_filter.mp hp).2.2.2
  have hlhs : s.prod (fun p => if Nat.Prime p then
      wheelLocalSingularFactor (2 * k) p else 1) =
      (s.filter Nat.Prime).prod (fun p => wheelLocalSingularFactor (2 * k) p) := by
    rw [← Finset.prod_filter]
  rw [hlhs, hsplit_prime, Finset.prod_insert h2_not_odd]
  have hfactor2 : wheelLocalSingularFactor (2 * k) 2 = 2 := by
    rw [wheelLocalSingularFactor_eq_singular (2 * k) 2 (by decide)]
    have h2_dvd : (2 : ℕ) ∣ 2 * k := Nat.dvd_mul_right 2 k
    simp only [h2_dvd, if_true]; norm_num
  rw [hfactor2, hsplit_odd, Finset.prod_union hdisj]
  have hprod_div : oddDivs.prod (fun p => wheelLocalSingularFactor (2 * k) p) =
      oddDivs.prod (fun p =>
        ((p : ℝ) - 1) / ((p : ℝ) - 2) * (1 - 1 / ((p : ℝ) - 1) ^ 2)) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hm := Finset.mem_filter.mp hp
    have hp_prime : Nat.Prime p := hm.2.1
    have hp_gt2 : 2 < p := hm.2.2.1
    have hp_dvd_2k : p ∣ 2 * k := dvd_mul_of_dvd_right hm.2.2.2 2
    rw [wheelLocalSingularFactor_eq_singular (2 * k) p hp_prime]
    simp only [hp_dvd_2k, if_true]
    have hp_real : (2 : ℝ) < p := by exact_mod_cast hp_gt2
    field_simp [hp_real.ne', (by linarith : (p : ℝ) - 1 ≠ 0), (by linarith : (p : ℝ) - 2 ≠ 0)]
    ring
  rw [hprod_div]
  have hprod_nondiv : oddNonDivs.prod (fun p => wheelLocalSingularFactor (2 * k) p) =
      oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hm := Finset.mem_filter.mp hp
    have hp_prime : Nat.Prime p := hm.2.1
    have hp_gt2 : 2 < p := hm.2.2.1
    have hp_not_dvd_2k : ¬p ∣ 2 * k := by
      intro hd
      have hor : p ∣ 2 ∨ p ∣ k := (Nat.Prime.dvd_mul hp_prime).mp hd
      cases hor with
      | inl h2 => have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp h2; omega
      | inr hk => exact hm.2.2.2 hk
    rw [wheelLocalSingularFactor_eq_singular (2 * k) p hp_prime]
    simp only [hp_not_dvd_2k, if_false]
    exact algebraic_identity_wheel_div (p : ℝ) (by exact_mod_cast hp_gt2)
  rw [hprod_nondiv]
  have h_split_div_prod : oddDivs.prod (fun p =>
      ((p : ℝ) - 1) / ((p : ℝ) - 2) * (1 - 1 / ((p : ℝ) - 1) ^ 2)) =
      oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
      oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    exact Finset.prod_mul_distrib ..
  rw [h_split_div_prod]
  have h_twin_prod :
      oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) *
      oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) =
      (s.filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    have h_eq : s.filter (fun p => Nat.Prime p ∧ 2 < p) = oddDivs ∪ oddNonDivs := hsplit_odd
    rw [h_eq, Finset.prod_union hdisj]
  have htwin : s.prod (fun p =>
      if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) =
      (s.filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    rw [Finset.prod_filter]
  have h_rearrange :
      2 * ((oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
              oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ))) *
            oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ))) =
        2 * oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
          (oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) *
           oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ))) := by ring
  rw [h_rearrange, h_twin_prod, ← htwin]

end
end PrimeGaps
