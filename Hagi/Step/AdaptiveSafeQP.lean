/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.StochasticSafeQP
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false

/-!
# AdaptiveSafeQP — концентрация для адаптивно выбранного направления d*(ω)

Концентрация минибатч-градиента (`StochasticSafeQP` — только
фиксированное направление d) обобщается на ω-зависимое
направление d*(ω) через явную решётчатую ε-сеть.

1. `latticeNet n D epsDir M` — конечная ε_dir-сеть шара
   `{‖x‖ ≤ D}` в `EuclideanSpace ℝ (Fin n)`: точки решётки с
   шагом `h = epsDir/√n`, нормы ≤ D + epsDir; покрывает шар
   (`latticeNet_covers`), размер ≤ `(2M+1)^n`
   (`latticeNet_card_le`) при `M ≥ D·√n/epsDir + 1`;
2. `adaptive_net_concentration` — равномерная по сети и всем
   доменам i концентрация с вероятностью ≥ 1−δ при пороге
   `ε_net = σ(D+epsDir)√(2 log(2|K|N_net/δ)/m)`;
3. `adaptive_direction_concentration` — перенос на любое
   `d* : Ω → X` с `‖d*ω‖ ≤ D` (без измеримости d*):
   `|(1/m)Σⱼ ⟪ξ_{i,j}, d*⟫| ≤ ε_net + σ·epsDir`;
4. `adaptive_safeQP_feasibility` — если стохастический QP
   сертифицировал d*(ω) по минибатч-градиентам с бюджетами
   `eps i`, то истинные градиенты удовлетворяют
   `⟪g i, d*⟫ ≥ −(eps i + ε_net + σ·epsDir)`.

Ограничения: конечномерность; статистические посылки требуются
на всём шаре `‖v‖ ≤ D + epsDir`; выбор оптимального epsDir и
бесконечномерный режим — открыто.
-/

open Finset Real MeasureTheory ProbabilityTheory InnerProductSpace
open scoped NNReal

namespace Hagi.Step

section AdaptiveSafeQP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {K : Type*} [Fintype K] [Nonempty K]

/-! ### The explicit lattice ε-net -/

/-- Шаг решётки `h = epsDir/√n` — разрешение сети по каждой
из n координат. -/
noncomputable def latticeStep (n : ℕ) (epsDir : ℝ) : ℝ := epsDir / Real.sqrt n

open Classical in
/-- Явная целочисленно-решётчатая ε_dir-сеть шара `{‖x‖ ≤ D}` в
`EuclideanSpace ℝ (Fin n)`: точки `h • z` с шагом
`h = epsDir/√n`, отфильтрованные условием
`∑ (h·z_k)² ≤ (D + epsDir)²`. -/
noncomputable def latticeNet (n : ℕ) (D epsDir : ℝ) (M : ℕ) :
    Finset (EuclideanSpace ℝ (Fin n)) :=
  ((Fintype.piFinset fun _ : Fin n => Finset.Icc (-(M : ℤ)) M).filter
      fun z => ∑ k, (latticeStep n epsDir * (z k : ℝ)) ^ 2 ≤ (D + epsDir) ^ 2).image
    fun z => WithLp.toLp 2 fun k => latticeStep n epsDir * (z k : ℝ)

/-- Точки сети лежат в шаре радиуса `D + epsDir`
(при `0 ≤ D + epsDir`). -/
theorem latticeNet_norm_le {n : ℕ} {D epsDir : ℝ} (hDE : 0 ≤ D + epsDir) {M : ℕ}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ latticeNet n D epsDir M) :
    ‖v‖ ≤ D + epsDir := by
  classical
  simp only [latticeNet] at hv
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hpi, hsum⟩ := Finset.mem_filter.mp hz
  have hvk : ∀ k, (WithLp.toLp 2 (fun k => latticeStep n epsDir * (z k : ℝ)) :
      EuclideanSpace ℝ (Fin n)) k = latticeStep n epsDir * (z k : ℝ) := fun k => rfl
  have hs : ∑ k, (latticeStep n epsDir * (z k : ℝ)) ^ 2
      = ‖(WithLp.toLp 2 (fun k => latticeStep n epsDir * (z k : ℝ)) :
          EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  rw [hs] at hsum
  have habs := abs_le_of_sq_le_sq hsum hDE
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- Покрытие: при `0 < n`, `0 ≤ D`, `0 < epsDir` и
`M ≥ D·√n/epsDir + 1` каждая точка x шара `‖x‖ ≤ D` лежит
в epsDir-окрестности некоторой точки сети (покоординатное
округление вниз). -/
theorem latticeNet_covers {n : ℕ} (hn : 0 < n) {D epsDir : ℝ} (hD : 0 ≤ D)
    (hepsDir : 0 < epsDir) {M : ℕ} (hM : D * Real.sqrt n / epsDir + 1 ≤ (M : ℝ))
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ D) :
    ∃ v ∈ latticeNet n D epsDir M, ‖x - v‖ ≤ epsDir := by
  classical
  have hdef : latticeStep n epsDir = epsDir / Real.sqrt n := rfl
  have hnneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
  have hnne : ((n : ℝ)) ≠ 0 := by exact_mod_cast hn.ne'
  have hnpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hh : 0 < epsDir / Real.sqrt n := div_pos hepsDir hnpos
  have hsqn : (epsDir / Real.sqrt n) ^ 2 * (n : ℝ) = epsDir ^ 2 := by
    rw [div_pow, Real.sq_sqrt hnneg, div_mul_cancel₀ (epsDir ^ 2) hnne]
  -- coordinate bound: |x k| ≤ ‖x‖ ≤ D (Euclidean norm dominates coordinates)
  have hxk : ∀ k, |x k| ≤ D := by
    intro k
    have h1 : (x k) ^ 2 ≤ ∑ i, (x i) ^ 2 :=
      Finset.single_le_sum (f := fun i => (x i) ^ 2) (fun i _ => sq_nonneg _) (mem_univ k)
    rw [← EuclideanSpace.real_norm_sq_eq] at h1
    exact le_trans (abs_le_of_sq_le_sq h1 (norm_nonneg x)) hx
  -- the rounded lattice vector
  set z : Fin n → ℤ := fun k => Int.floor (x k / (epsDir / Real.sqrt n)) with hzdef
  set v : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 fun k => (epsDir / Real.sqrt n) * (z k : ℝ) with hvdef
  have hvk : ∀ k, v k = (epsDir / Real.sqrt n) * (z k : ℝ) := fun k => rfl
  -- per-coordinate rounding error in [0, h]
  have hround : ∀ k, 0 ≤ x k - (epsDir / Real.sqrt n) * (z k : ℝ)
      ∧ x k - (epsDir / Real.sqrt n) * (z k : ℝ) ≤ epsDir / Real.sqrt n := by
    intro k
    have hfl : ((z k : ℤ) : ℝ) ≤ x k / (epsDir / Real.sqrt n) := Int.floor_le _
    have hfs : x k / (epsDir / Real.sqrt n) < ((z k : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hlow : (epsDir / Real.sqrt n) * ((z k : ℤ) : ℝ) ≤ x k := by
      have h1 := mul_le_mul_of_nonneg_right hfl hh.le
      rwa [mul_comm, div_mul_cancel₀ (x k) hh.ne'] at h1
    have hhigh : x k < (epsDir / Real.sqrt n) * ((z k : ℤ) : ℝ)
        + epsDir / Real.sqrt n := by
      have h2 := mul_lt_mul_of_pos_right hfs hh
      rw [div_mul_cancel₀ (x k) hh.ne'] at h2
      ring_nf at h2 ⊢
      linarith
    constructor <;> linarith
  -- ‖x - v‖ ≤ epsDir
  have hdist : ‖x - v‖ ≤ epsDir := by
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        (x k - v k) ^ 2 ≤ (epsDir / Real.sqrt n) ^ 2 := by
      intro k _
      have ⟨h0, h1⟩ := hround k
      rw [hvk k]
      nlinarith [hh.le]
    have hsumle : ∑ k, (x k - v k) ^ 2 ≤ epsDir ^ 2 := by
      calc ∑ k, (x k - v k) ^ 2 ≤ ∑ k, (epsDir / Real.sqrt n) ^ 2 :=
            Finset.sum_le_sum hterm
        _ = Finset.card (Finset.univ : Finset (Fin n)) * (epsDir / Real.sqrt n) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (n : ℝ) * (epsDir / Real.sqrt n) ^ 2 := by simp
        _ = epsDir ^ 2 := by rw [mul_comm]; exact hsqn
    have hsq : (‖x - v‖) ^ 2 ≤ epsDir ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact hsumle
    have habs := abs_le_of_sq_le_sq hsq hepsDir.le
    rwa [abs_of_nonneg (norm_nonneg _)] at habs
  -- ‖v‖ ≤ D + epsDir (triangle inequality)
  have hvnorm : ‖v‖ ≤ D + epsDir := by
    have hvx : ‖v‖ = ‖x - (x - v)‖ := by
      have : x - (x - v) = v := by abel
      rw [this]
    rw [hvx]
    have ht := norm_sub_le x (x - v)
    linarith [hx, hdist, ht]
  refine ⟨v, ?_, hdist⟩
  rw [latticeNet]
  refine Finset.mem_image.mpr ⟨z, ?_, rfl⟩
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · -- z in the integer box
    have hDh : D / (epsDir / Real.sqrt n) = D * Real.sqrt n / epsDir := by
      rw [div_eq_inv_mul, inv_div, mul_div_assoc, mul_comm]
    refine Fintype.mem_piFinset.mpr fun k => Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · -- -(M:ℤ) ≤ z k
      have hfu : x k / (epsDir / Real.sqrt n) - 1 < ((z k : ℤ) : ℝ) :=
        Int.sub_one_lt_floor _
      have hkabs : -(|x k| / (epsDir / Real.sqrt n)) ≤ x k / (epsDir / Real.sqrt n) := by
        rw [← neg_div]
        exact div_le_div_of_nonneg_right (neg_abs_le _) hh.le
      have hkD : |x k| / (epsDir / Real.sqrt n) ≤ D * Real.sqrt n / epsDir := by
        rw [← hDh]
        exact div_le_div_of_nonneg_right (hxk k) hh.le
      have hz : (-(M : ℤ) : ℝ) ≤ ((z k : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hz
    · -- z k ≤ M
      have hfl : ((z k : ℤ) : ℝ) ≤ x k / (epsDir / Real.sqrt n) :=
        Int.floor_le _
      have hkabs : x k / (epsDir / Real.sqrt n) ≤ |x k| / (epsDir / Real.sqrt n) :=
        div_le_div_of_nonneg_right (le_abs_self _) hh.le
      have hkD : |x k| / (epsDir / Real.sqrt n) ≤ D * Real.sqrt n / epsDir := by
        rw [← hDh]
        exact div_le_div_of_nonneg_right (hxk k) hh.le
      have hz : ((z k : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hz
  · -- filter predicate: ∑ (h·z_k)² ≤ (D + epsDir)²
    have hvv : ∀ k, (epsDir / Real.sqrt n) * (z k : ℝ) = v k := fun k => (hvk k).symm
    have hcalc : ∑ k, ((epsDir / Real.sqrt n) * (z k : ℝ)) ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    change ∑ k, ((epsDir / Real.sqrt n) * (z k : ℝ)) ^ 2 ≤ (D + epsDir) ^ 2
    rw [hcalc]
    exact sq_le_sq' (by linarith [norm_nonneg v]) hvnorm

/-- `(latticeNet n D epsDir M).card ≤ (2 * M + 1) ^ n`. -/
theorem latticeNet_card_le (n : ℕ) (D epsDir : ℝ) (M : ℕ) :
    (latticeNet n D epsDir M).card ≤ (2 * M + 1) ^ n := by
  classical
  have hbox : (Fintype.piFinset fun _ : Fin n => Finset.Icc (-(M : ℤ)) M).card
      = (2 * M + 1) ^ n := by
    rw [Fintype.piFinset, Finset.card_map, Finset.card_pi]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
    have hnat0 : (((M : ℤ) + 1 - (-(M : ℤ))).toNat : ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega)]
      push_cast
      omega
    have hnat : ((M : ℤ) + 1 - (-(M : ℤ))).toNat = 2 * M + 1 := by
      exact_mod_cast hnat0
    rw [hnat]
  calc (latticeNet n D epsDir M).card
      ≤ ((Fintype.piFinset fun _ : Fin n => Finset.Icc (-(M : ℤ)) M).filter
          fun z => ∑ k, (latticeStep n epsDir * (z k : ℝ)) ^ 2 ≤ (D + epsDir) ^ 2).card := by
        change Finset.card (Finset.image _ _) ≤ _
        exact Finset.card_image_le
    _ ≤ (Fintype.piFinset fun _ : Fin n => Finset.Icc (-(M : ℤ)) M).card := by
        show Finset.card (Finset.filter _ _) ≤ _
        exact Finset.card_filter_le _ _
    _ = (2 * M + 1) ^ n := hbox

/-! ### Uniform concentration over the net -/

/-- Явный сетевой шумовой порог
`ε_net = σ(D+epsDir)√(2·log(2|K|·(2M+1)^n/δ)/m)`. -/
noncomputable def adaptiveNoiseEps (K : Type*) [Fintype K] (n : ℕ) (D epsDir : ℝ) (M : ℕ)
    (sigma : ℝ) (m : ℕ) (delta : ℝ) : ℝ :=
  sigma * (D + epsDir) *
    Real.sqrt (2 * Real.log (2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ n : ℝ) / delta) / (m : ℝ))

/-- Равномерная по сети концентрация: при статистических
посылках на шаре `‖v‖ ≤ D + epsDir` (измеримость,
средние нулевые, независимость, `‖ξ‖ ≤ σ`) с вероятностью
`≥ 1 − δ` одновременно для всех i и всех точек сети v
выполнено `|(1/m)Σⱼ ⟪ξ_{i,j}, v⟫| ≤ adaptiveNoiseEps`.
Доказательство: пер-точечный Hoeffding (`minibatch_inner_tail`)
+ двусторонний union bound по |K| × |net| ≤ (2M+1)^n. -/
theorem adaptive_net_concentration {m : ℕ} (hm : 0 < m) {n : ℕ}
    (sigma : ℝ) (hsigma : 0 < sigma) (D : ℝ) (hD : 0 ≤ D) (epsDir : ℝ) (hepsDir : 0 < epsDir)
    {M : ℕ}
    (xi : K → Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (h_emp_noise_meas : ∀ i j (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      Measurable fun ω => ⟪xi i j ω, v⟫_ℝ)
    (h_emp_noise_zero : ∀ i j (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      μ[fun ω => ⟪xi i j ω, v⟫_ℝ] = 0)
    (h_emp_noise_indep : ∀ i (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      iIndepFun (fun j : Fin m => fun ω => ⟪xi i j ω, v⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) :
    μ.real {ω | ∀ i, ∀ v ∈ latticeNet n D epsDir M,
      |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|
        ≤ adaptiveNoiseEps K n D epsDir M sigma m delta} ≥ 1 - delta := by
  classical
  obtain ⟨hd1, hd2⟩ := Set.mem_Ioo.mp hdelta
  set N := ((2 * M + 1) ^ n : ℝ) with hN
  set L := 2 * Real.log (2 * (Fintype.card K : ℝ) * N / delta) with hL
  set A := adaptiveNoiseEps K n D epsDir M sigma m delta with hA
  set Rmax := sigma * (D + epsDir) with hRmax
  have hcardK : (1 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcardKne : (Fintype.card K : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith
  have hNpos : (1 : ℝ) ≤ N := by
    have h2 : (1 : ℕ) ≤ (2 * M + 1) ^ n := Nat.one_le_pow n (2 * M + 1) (by omega)
    have h3 : (1 : ℝ) ≤ ((2 * M + 1) ^ n : ℝ) := by exact_mod_cast h2
    exact h3
  have hNne : N ≠ 0 := by
    have : (0 : ℝ) < N := by linarith
    linarith
  have hDE : 0 ≤ D + epsDir := by linarith
  -- the log argument exceeds 1, so the log is positive and A ≥ 0
  have harg : (1 : ℝ) < 2 * (Fintype.card K : ℝ) * N / delta := by
    rw [lt_div_iff₀ hd1]
    nlinarith [hcardK, hNpos]
  have hLpos : 0 < L := by
    have := Real.log_pos harg
    linarith
  have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (mul_nonneg hsigma.le hDE) (Real.sqrt_nonneg _)
  -- the definition unfolds to σ(D+eps)·√(L/m)
  have hAdef : A = Rmax * Real.sqrt (L / (m : ℝ)) := rfl
  -- the exponent identity: m·A² = Rmax²·L
  have hsq : (m : ℝ) * A ^ 2 = Rmax ^ 2 * L := by
    rw [hAdef, hRmax, mul_pow, Real.sq_sqrt (div_nonneg hLpos.le hmp.le)]
    field_simp
  -- the exp identity: exp(−m·A²/(2·Rmax²)) = δ/(2|K|N)
  have hRne : Rmax ≠ 0 := by
    rw [hRmax]
    positivity
  have hLdef : L = 2 * Real.log (2 * (Fintype.card K : ℝ) * N / delta) := rfl
  have h2ne : (2 * Rmax ^ 2) ≠ 0 := by positivity
  have hexp : Real.exp (- (m : ℝ) * A ^ 2 / (2 * Rmax ^ 2))
      = delta / (2 * (Fintype.card K : ℝ) * N) := by
    have hpos : (0 : ℝ) < 2 * (Fintype.card K : ℝ) * N / delta :=
      div_pos (by positivity) hd1
    have hstep : -(m : ℝ) * A ^ 2 / (2 * Rmax ^ 2) = -L / 2 := by
      have h1 : -(m : ℝ) * A ^ 2 = -(Rmax ^ 2 * L) := by
        rw [← hsq, neg_mul]
      rw [h1, div_eq_div_iff h2ne two_ne_zero]
      ring
    have hL2 : -L / 2 = -Real.log (2 * (Fintype.card K : ℝ) * N / delta) := by
      rw [hLdef]
      ring
    rw [hstep, hL2, Real.exp_neg, Real.exp_log hpos, inv_div]
  -- the per-(i, v) two-sided tail bound: ≤ δ/(|K|·N)
  have hpair : ∀ (i : K) (v : EuclideanSpace ℝ (Fin n)), v ∈ latticeNet n D epsDir M →
      μ.real {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}
        ≤ delta / ((Fintype.card K : ℝ) * N) := by
    intro i v hv
    have hvnorm : ‖v‖ ≤ D + epsDir := latticeNet_norm_le hDE hv
    by_cases hv0 : v = 0
    · subst hv0
      have hset : {ω : Ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, 0⟫_ℝ|} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, inner_zero_right,
          Finset.sum_const_zero, mul_zero, abs_zero]
        exact ⟨fun h => absurd h (not_lt.2 hAnn), fun h => h.elim⟩
      rw [hset, measureReal_empty]
      have hdenpos : (0 : ℝ) < (Fintype.card K : ℝ) * N := by
        have : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
        have hNp : (0 : ℝ) < N := by rw [hN]; positivity
        positivity
      exact div_nonneg hd1.le hdenpos.le
    · set Rv := sigma * ‖v‖ with hRv
      have hRvpos : 0 < Rv := by rw [hRv]; exact mul_pos hsigma (norm_pos_iff.mpr hv0)
      have hRvle : Rv ≤ Rmax := by
        rw [hRv, hRmax]
        exact mul_le_mul_of_nonneg_left hvnorm hsigma.le
      -- the projections are bounded by Rv = σ‖v‖ (Cauchy–Schwarz)
      have hB : ∀ j ω, |⟪xi i j ω, v⟫_ℝ| ≤ Rv := by
        intro j ω
        calc |⟪xi i j ω, v⟫_ℝ| = ‖⟪xi i j ω, v⟫_ℝ‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖xi i j ω‖ * ‖v‖ := norm_inner_le_norm _ _
          _ ≤ Rv := by
              rw [hRv]
              exact mul_le_mul_of_nonneg_right (h_emp_noise_bound i j ω) (norm_nonneg v)
      -- both one-sided Hoeffding tails (R92's minibatch_inner_tail)
      have htail_down := minibatch_inner_tail hm (fun j ω => ⟪xi i j ω, v⟫_ℝ) Rv hRvpos
        (fun j => h_emp_noise_meas i j v hvnorm) (h_emp_noise_indep i v hvnorm)
        (fun j => h_emp_noise_zero i j v hvnorm) hB hAnn
      have htail_up0 := minibatch_inner_tail hm (fun j ω => -(⟪xi i j ω, v⟫_ℝ)) Rv hRvpos
        (fun j => (h_emp_noise_meas i j v hvnorm).neg)
        ((h_emp_noise_indep i v hvnorm).comp _ (fun _ => measurable_id.neg))
        (fun j => by
          show ∫ (x : Ω), -(⟪xi i j x, v⟫_ℝ) ∂μ = 0
          rw [integral_neg, h_emp_noise_zero i j v hvnorm]
          ring)
        (fun j ω => by simpa using hB j ω) hAnn
      have htail_up : μ.real {ω : Ω | (m : ℝ) * A ≤ ∑ j, ⟪xi i j ω, v⟫_ℝ}
          ≤ Real.exp (- (m : ℝ) * A ^ 2 / (2 * Rv ^ 2)) := by
        have hseteq : {ω : Ω | (m : ℝ) * A ≤ ∑ j, -(-(⟪xi i j ω, v⟫_ℝ))}
            = {ω : Ω | (m : ℝ) * A ≤ ∑ j, ⟪xi i j ω, v⟫_ℝ} := by
          ext ω
          simp only [Set.mem_ofPred_eq, neg_neg]
        rw [← hseteq]
        exact htail_up0
      -- weaken the exponent from Rv to Rmax (Rv ≤ Rmax)
      have hex : Real.exp (- (m : ℝ) * A ^ 2 / (2 * Rv ^ 2))
          ≤ delta / (2 * (Fintype.card K : ℝ) * N) := by
        have h2 : 2 * Rv ^ 2 ≤ 2 * Rmax ^ 2 := by nlinarith [hRvle, hRvpos.le]
        have hA2nn : (0 : ℝ) ≤ (m : ℝ) * A ^ 2 := by positivity
        have hfrac : (m : ℝ) * A ^ 2 / (2 * Rmax ^ 2) ≤ (m : ℝ) * A ^ 2 / (2 * Rv ^ 2) :=
          div_le_div_of_nonneg_left hA2nn (by positivity) h2
        refine le_trans (Real.exp_le_exp.mpr ?_) (le_of_eq hexp)
        have hnege : (-(m : ℝ)) * A ^ 2 = -((m : ℝ) * A ^ 2) := by ring
        rw [hnege, neg_div, neg_div]
        linarith [hfrac]
      -- the failure event is contained in the union of the two tails
      have hsub : {ω : Ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}
          ⊆ {ω : Ω | (m : ℝ) * A ≤ ∑ j, ⟪xi i j ω, v⟫_ℝ}
            ∪ {ω : Ω | (m : ℝ) * A ≤ ∑ j, -(⟪xi i j ω, v⟫_ℝ)} := by
        rintro ω hω
        simp only [Set.mem_ofPred_eq] at hω
        have hmp2 : (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ ≠ 0 := by
          intro h0
          rw [h0, abs_zero] at hω
          exact absurd hω (not_lt.2 hAnn)
        rcases lt_or_gt_of_ne hmp2 with hneg | hpos
        · refine Or.inr ?_
          have h1 : A < -((m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ) := by
            rwa [abs_of_neg hneg] at hω
          rw [inv_mul_eq_div, ← neg_div, lt_div_iff₀ hmp] at h1
          have hnegsum : ∑ j, -(⟪xi i j ω, v⟫_ℝ)
              = -∑ j, ⟪xi i j ω, v⟫_ℝ := by simp [Finset.sum_neg_distrib]
          rw [← hnegsum] at h1
          have h2 : (m : ℝ) * A < ∑ j, -(⟪xi i j ω, v⟫_ℝ) := by
            rw [mul_comm]; exact h1
          exact le_of_lt h2
        · refine Or.inl ?_
          have h1 : A < (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ := by
            rwa [abs_of_pos hpos] at hω
          rw [inv_mul_eq_div, lt_div_iff₀ hmp] at h1
          have h2 : (m : ℝ) * A < ∑ j, ⟪xi i j ω, v⟫_ℝ := by
            rw [mul_comm]; exact h1
          exact le_of_lt h2
      calc μ.real {ω : Ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}
          ≤ μ.real ({ω : Ω | (m : ℝ) * A ≤ ∑ j, ⟪xi i j ω, v⟫_ℝ}
            ∪ {ω : Ω | (m : ℝ) * A ≤ ∑ j, -(⟪xi i j ω, v⟫_ℝ)}) := measureReal_mono hsub
        _ ≤ μ.real {ω : Ω | (m : ℝ) * A ≤ ∑ j, ⟪xi i j ω, v⟫_ℝ}
            + μ.real {ω : Ω | (m : ℝ) * A ≤ ∑ j, -(⟪xi i j ω, v⟫_ℝ)} := measureReal_union_le _ _
        _ ≤ delta / ((Fintype.card K : ℝ) * N) := by
            have hsumle := add_le_add htail_up htail_down
            have hdivpos : (0 : ℝ) < delta / ((Fintype.card K : ℝ) * N) := by
              have hdenpos : (0 : ℝ) < (Fintype.card K : ℝ) * N := by
                have : (0 : ℝ) < (Fintype.card K : ℝ) := by
                  exact_mod_cast Fintype.card_pos
                have hNp : (0 : ℝ) < N := by rw [hN]; positivity
                positivity
              exact div_pos hd1 hdenpos
            have hEq : (2 : ℝ) * (delta / (2 * (Fintype.card K : ℝ) * N))
                = delta / ((Fintype.card K : ℝ) * N) := by ring
            nlinarith [hex, hsumle, hEq]
  -- the per-domain bad event over the net
  have hBadNet : ∀ i, μ.real (⋃ v ∈ latticeNet n D epsDir M,
      {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}) ≤ delta / ((Fintype.card K : ℝ)) := by
    intro i
    calc μ.real (⋃ v ∈ latticeNet n D epsDir M,
          {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|})
        ≤ ∑ v ∈ latticeNet n D epsDir M,
            μ.real {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ v ∈ latticeNet n D epsDir M, delta / ((Fintype.card K : ℝ) * N) :=
          Finset.sum_le_sum fun v hv => hpair i v hv
      _ = (latticeNet n D epsDir M).card * (delta / ((Fintype.card K : ℝ) * N)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * (delta / ((Fintype.card K : ℝ) * N)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hN]
          exact_mod_cast latticeNet_card_le n D epsDir M
      _ = delta / ((Fintype.card K : ℝ)) := by field_simp
  -- the total bad event over all domains
  have hBad : μ.real (⋃ i : K, ⋃ v ∈ latticeNet n D epsDir M,
      {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}) ≤ delta := by
    calc μ.real (⋃ i : K, ⋃ v ∈ latticeNet n D epsDir M,
          {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|})
        ≤ ∑ i, μ.real (⋃ v ∈ latticeNet n D epsDir M,
            {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}) :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ i, delta / ((Fintype.card K : ℝ)) := Finset.sum_le_sum fun i _ => hBadNet i
      _ = delta := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          exact mul_div_cancel₀ delta hcardKne
  -- measurability of the total bad event
  have hBadMeas : MeasurableSet (⋃ i : K, ⋃ v ∈ latticeNet n D epsDir M,
      {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}) := by
    refine MeasurableSet.iUnion fun i => Finset.measurableSet_biUnion _ fun v hv => ?_
    have hvnorm : ‖v‖ ≤ D + epsDir := latticeNet_norm_le hDE hv
    have havg : Measurable fun ω => ∑ j, ⟪xi i j ω, v⟫_ℝ :=
      Finset.measurable_sum Finset.univ fun j _ => h_emp_noise_meas i j v hvnorm
    exact measurableSet_lt measurable_const
      (Measurable.abs (measurable_const.mul havg))
  -- the good event: complement of the bad, pointwise containment
  have hcomp : 1 - delta
      ≤ μ.real (⋃ i : K, ⋃ v ∈ latticeNet n D epsDir M,
          {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|})ᶜ := by
    rw [measureReal_compl hBadMeas, probReal_univ]
    linarith
  refine le_trans hcomp (measureReal_mono ?_)
  intro ω hω i v hv
  have hnot : ¬ (A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|) := by
    have h1 : ω ∈ (⋃ i : K, ⋃ v ∈ latticeNet n D epsDir M,
      {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|})ᶜ := hω
    simp only [Set.mem_compl_iff, Set.mem_iUnion] at h1
    push Not at h1
    exact h1 i v hv
  simpa using not_lt.mp hnot

/-- Для любого `dstar : Ω → EuclideanSpace ℝ (Fin n)` с
`‖dstar ω‖ ≤ D` (измеримость не требуется): при статистических
посылках `adaptive_net_concentration` с вероятностью `≥ 1 − δ`
одновременно для всех i выполнено
`|(1/m)Σⱼ ⟪ξ_{i,j}(ω), dstar ω⟫| ≤ adaptiveNoiseEps + σ·epsDir`
(покрытие d* точкой сети + σ-липшицевость ⟪ξ_avg, ·⟫). -/
theorem adaptive_direction_concentration {m : ℕ} (hm : 0 < m) {n : ℕ} (hn : 0 < n)
    (sigma : ℝ) (hsigma : 0 < sigma) (D : ℝ) (hD : 0 ≤ D) (epsDir : ℝ) (hepsDir : 0 < epsDir)
    {M : ℕ} (hM : D * Real.sqrt n / epsDir + 1 ≤ (M : ℝ))
    (xi : K → Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (h_emp_noise_meas : ∀ i j (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      Measurable fun ω => ⟪xi i j ω, v⟫_ℝ)
    (h_emp_noise_zero : ∀ i j (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      μ[fun ω => ⟪xi i j ω, v⟫_ℝ] = 0)
    (h_emp_noise_indep : ∀ i (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      iIndepFun (fun j : Fin m => fun ω => ⟪xi i j ω, v⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (dstar : Ω → EuclideanSpace ℝ (Fin n)) (h_dstar_norm : ∀ ω, ‖dstar ω‖ ≤ D)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) :
    μ.real {ω | ∀ i, |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω⟫_ℝ|
        ≤ adaptiveNoiseEps K n D epsDir M sigma m delta + sigma * epsDir} ≥ 1 - delta := by
  classical
  have hDE : 0 ≤ D + epsDir := by linarith
  have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  -- the net event, with probability ≥ 1 − δ
  have hE := adaptive_net_concentration (M := M) hm sigma hsigma D hD epsDir hepsDir xi
    h_emp_noise_meas h_emp_noise_zero h_emp_noise_indep h_emp_noise_bound delta hdelta
  -- pointwise transfer: net uniformity + Lipschitz ⟪ξ_avg, ·⟫
  refine le_trans hE (measureReal_mono ?_)
  intro ω hω i
  -- cover d*(ω) by a net point
  obtain ⟨v, hvnet, hdist⟩ :=
    latticeNet_covers hn hD hepsDir hM (dstar ω) (h_dstar_norm ω)
  -- the net bound at v
  have hv := hω i v hvnet
  -- split off the transfer term
  have hsplit : (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω⟫_ℝ
      = (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ
        + (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω - v⟫_ℝ := by
    have hterm : ∀ j, ⟪xi i j ω, dstar ω⟫_ℝ
        = ⟪xi i j ω, v⟫_ℝ + ⟪xi i j ω, dstar ω - v⟫_ℝ := by
      intro j
      have hvv : v + (dstar ω - v) = dstar ω := by abel
      rw [← inner_add_right, hvv]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hterm j]; ring
  -- |average of the transfer terms| ≤ σ·epsDir (σ-Lipschitz)
  have htransfer : |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω - v⟫_ℝ| ≤ sigma * epsDir := by
    have hbound : ∀ j, |⟪xi i j ω, dstar ω - v⟫_ℝ| ≤ sigma * epsDir := by
      intro j
      calc |⟪xi i j ω, dstar ω - v⟫_ℝ|
            = ‖⟪xi i j ω, dstar ω - v⟫_ℝ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖xi i j ω‖ * ‖dstar ω - v‖ := norm_inner_le_norm _ _
        _ ≤ sigma * epsDir :=
            mul_le_mul (h_emp_noise_bound i j ω) hdist (norm_nonneg _) hsigma.le
    have hsumbound : ∑ j, |⟪xi i j ω, dstar ω - v⟫_ℝ| ≤ (m : ℝ) * (sigma * epsDir) := by
      have hle : ∑ j, |⟪xi i j ω, dstar ω - v⟫_ℝ| ≤ ∑ j, sigma * epsDir :=
        Finset.sum_le_sum fun j _ => hbound j
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at hle
      exact hle
    calc |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω - v⟫_ℝ|
        ≤ (m : ℝ)⁻¹ * ∑ j, |⟪xi i j ω, dstar ω - v⟫_ℝ| := by
          have h1 := Finset.abs_sum_le_sum_abs (fun j => ⟪xi i j ω, dstar ω - v⟫_ℝ)
            Finset.univ
          have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hmp.le)
          simpa [← Finset.mul_sum] using h2
      _ ≤ (m : ℝ)⁻¹ * ((m : ℝ) * (sigma * epsDir)) :=
          mul_le_mul_of_nonneg_left hsumbound (inv_nonneg.mpr hmp.le)
      _ = sigma * epsDir := by field_simp
  rw [hsplit]
  calc |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ + (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω - v⟫_ℝ|
      ≤ |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|
          + |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω - v⟫_ℝ| :=
        abs_add_le _ _
    _ ≤ adaptiveNoiseEps K n D epsDir M sigma m delta + sigma * epsDir := by linarith

/-- При посылках `adaptive_direction_concentration`:
с вероятностью `≥ 1 − δ`, если стохастические ограничения
сертифицировали d*(ω) по минибатч-градиентам
(`−eps i ≤ ⟪g i + (1/m)Σⱼ ξ_{i,j}, d*⟫` для всех i),
то `⟪g i, dstar ω⟫ ≥ −(eps i + adaptiveNoiseEps + σ·epsDir)`
для всех i. -/
theorem adaptive_safeQP_feasibility {m : ℕ} (hm : 0 < m) {n : ℕ} (hn : 0 < n)
    (sigma : ℝ) (hsigma : 0 < sigma) (D : ℝ) (hD : 0 ≤ D) (epsDir : ℝ) (hepsDir : 0 < epsDir)
    {M : ℕ} (hM : D * Real.sqrt n / epsDir + 1 ≤ (M : ℝ))
    (g : K → EuclideanSpace ℝ (Fin n))
    (xi : K → Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (h_emp_noise_meas : ∀ i j (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      Measurable fun ω => ⟪xi i j ω, v⟫_ℝ)
    (h_emp_noise_zero : ∀ i j (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      μ[fun ω => ⟪xi i j ω, v⟫_ℝ] = 0)
    (h_emp_noise_indep : ∀ i (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      iIndepFun (fun j : Fin m => fun ω => ⟪xi i j ω, v⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (dstar : Ω → EuclideanSpace ℝ (Fin n)) (h_dstar_norm : ∀ ω, ‖dstar ω‖ ≤ D)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) (eps : K → ℝ) :
    μ.real {ω | (∀ i, -eps i ≤ ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, dstar ω⟫_ℝ)
        → (∀ i, -(eps i + adaptiveNoiseEps K n D epsDir M sigma m delta + sigma * epsDir)
            ≤ ⟪g i, dstar ω⟫_ℝ)} ≥ 1 - delta := by
  classical
  -- the adaptive-direction concentration event
  have hG := adaptive_direction_concentration hm hn sigma hsigma D hD epsDir hepsDir hM xi
    h_emp_noise_meas h_emp_noise_zero h_emp_noise_indep h_emp_noise_bound dstar h_dstar_norm
    delta hdelta
  refine le_trans hG (measureReal_mono ?_)
  rintro ω hω hcert i
  -- split the stochastic inner product
  have hinner : ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, dstar ω⟫_ℝ
      = ⟪g i, dstar ω⟫_ℝ + (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω⟫_ℝ := by
    rw [inner_add_left, inner_smul_left, sum_inner]
    simp
  have hnoise := hω i
  obtain ⟨hn1, hn2⟩ := abs_le.mp hnoise
  have hcerti := hcert i
  rw [hinner] at hcerti
  have hbound : -(adaptiveNoiseEps K n D epsDir M sigma m delta + sigma * epsDir)
      ≤ (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω⟫_ℝ := by
    linarith
  linarith

end AdaptiveSafeQP

end Hagi.Step

namespace Hagi
export Hagi.Step (latticeStep latticeNet latticeNet_norm_le latticeNet_covers latticeNet_card_le adaptiveNoiseEps adaptive_net_concentration adaptive_direction_concentration adaptive_safeQP_feasibility)
end Hagi
