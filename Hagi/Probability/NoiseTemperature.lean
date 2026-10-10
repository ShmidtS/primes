/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.CertifiedEstimator
import Hagi.Foundations.Recurrence

set_option linter.style.header false

/-!
# NoiseTemperature: the gradient noise is a reservoir at temperature 1/B

The second module of the thermodynamic layer (§8.8 of
FORMALIZATION_PLAN.md, round). Port of the two pure-math
cores behind the "SGD noise = reservoir temperature" reading:

* **Unbiasedness + temperature (arXiv:2606.30789 Lemma 6,
  finite form).** The mini-batch average `ĝ(ω) =
  (1/B)·Σ_{i<B} g(ω i)` over independent uniform draws is
  unbiased, and its variance is EXACTLY `Var(g)/B`: the
  reservoir temperature is `1/B` — the batch axis and the
  learning-rate axis act on different terms of the
  fluctuation scale.

* **Scale separation (arXiv:2606.28808, finite form).** For
  a step size `0 < η ≤ 1` the one-step fluctuation standard
  deviation `η·σ/√B` sits at or below the coarser `√η` scale
  `√η·σ/√B`: the noise enters at order `√η` or finer — the
  classical fluctuation–dissipation separation as an
  elementary inequality, with NO stochastic-calculus claim.

**Main theorems (pure math, no `h_emp_`).**

* `sum_coord` — coordinate sum factorization: `Σ_ω f(ω i) =
  |V|^(b−1)·Σ_v f v` (independence in the 1-padding
  disguise, via `sum_prod_factor`).

* `sum_pair` — off-diagonal pair factorization: `Σ_ω f(ω i)·
  h(ω k) = |V|^(b−2)·(Σ f)·(Σ h)` for `i ≠ k` (the two-if
  product decomposition).

* `batchMean_unbiased` — `E[ĝ] = E[g]` over the uniform
  product measure.

* `batch_variance_eq` — THE TEMPERATURE LAW: `Var(ĝ) =
  Var(g)/B`. The off-diagonal cross terms vanish by
  independence: each factors through the centered population
  sum, which is zero (`sum_centered`); the `B` diagonal terms
  give `B·Var(g)`, and the prefactor `1/B²` leaves `1/B`.

* `noise_scale_separation` — `η·θ ≤ √η·θ` for `0 < η ≤ 1`,
  `θ ≥ 0`: the fluctuation scale is controlled at the `√η`
  order.

**Honest boundary.** The Itô-diffusion reading (drift O(η),
Brownian noise O(√η) in the CLT limit), the equivalence
LR-decay ≡ batch-increase (1711.00489), and the
group-size ↔ temperature mapping for parallel-data training
are not formalized and carry no Lean claim here. This module
is the finite kernel those interpretations reference.
-/

namespace Hagi.Probability

open Finset

variable {V : Type} [Fintype V] [Nonempty V]

/-! ## Population level -/

/-- Population mean of a real function on the finite space
`V` (uniform measure). -/
noncomputable def popMean (g : V → ℝ) : ℝ := (∑ v, g v) / (Fintype.card V : ℝ)

/-- Population variance of a real function on `V` (uniform
measure): `σ² = E[(g − μ)²]`. -/
noncomputable def popVar (g : V → ℝ) : ℝ :=
  (∑ v, (g v - popMean g) ^ 2) / (Fintype.card V : ℝ)

/-- The centered part of `g`: `X v = g v − μ`. -/
noncomputable def centered (g : V → ℝ) : V → ℝ := fun v => g v - popMean g

theorem popVar_eq (g : V → ℝ) :
    popVar g = (∑ v, (centered g v) ^ 2) / (Fintype.card V : ℝ) := by
  simp [popVar, centered]

theorem sum_centered (g : V → ℝ) : ∑ v, centered g v = 0 := by
  simp only [centered, sum_sub_distrib, popMean]
  have hNpos : (0:ℝ) < (Fintype.card V : ℝ) := by positivity
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc',
    mul_div_cancel_left₀ _ hNpos.ne']
  ring

/-! ## The batch level: independent uniform draws -/

section Batch
variable {b : ℕ} [Nonempty (Fin b)]

theorem card_pos_of_nonempty : 0 < b := Fin.pos_iff_nonempty.mpr ‹_›

/-- The two-selector product: a padding factor that is `A`
on coordinate `i`, `h` on coordinate `k` (`i ≠ k`) and `1`
elsewhere — a PRODUCT of two one-selector factors. -/
theorem prod_two_sel (A h : ℝ) (i k : Fin b) (hik : i ≠ k) (ω : Fin b → V) :
    (∏ j, ((if j = i then A else 1) * (if j = k then h else 1))) = A * h := by
  classical
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq' univ i _,
    Finset.prod_ite_eq' univ k _]
  simp [Finset.mem_univ, hik]

/-- **Coordinate sum factorization**: a coordinate
functional summed over all batches factorizes through the
population sum: `Σ_ω f(ω i) = |V|^(b−1)·Σ_v f v`.
Independence in the `1`-padding disguise: pad `f` along
coordinate `i` with ones and apply `sum_prod_factor`. -/
theorem sum_coord (f : V → ℝ) (i : Fin b) :
    ∑ ω : Fin b → V, f (ω i)
      = ((Fintype.card V : ℝ) ^ (b - 1)) * ∑ v, f v := by
  classical
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hNpos : N ≠ 0 := by positivity
  have hb0 : 0 < b := Fin.pos_iff_nonempty.mpr ‹_›
  have hb : 1 ≤ b := by omega
  set ff : Fin b → V → ℝ :=
    fun j v => if j = i then f v else (1:ℝ) with hff
  have hprod : ∀ ω : Fin b → V, (∏ j, ff j (ω j)) = f (ω i) := by
    intro ω
    have hbeta : ∀ j : Fin b, ff j (ω j)
        = if j = i then f (ω j) else (1:ℝ) := fun j => rfl
    rw [Finset.prod_congr rfl (fun j _ => hbeta j)]
    rw [Finset.prod_ite_eq' univ i _]
    simp
  have hcoord : ∀ j : Fin b,
      (∑ v, ff j v) = if j = i then (∑ v, f v) else N := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp [hff]
    · simp [hff, hj]
      rw [← hN]
  have hsplit := sum_prod_factor (V := V) ff
  rw [Finset.sum_congr rfl (fun ω _ => hprod ω)] at hsplit
  rw [hsplit]
  simp only [hcoord]
  -- remaining: ∏ (if j = i then Σf else N) = Σf·N^(b−1)
  have h1 : (∏ j : Fin b, (if j = i then (∑ v, f v) else N))
      = ∏ j : Fin b, (N * (if j = i then ((∑ v, f v) / N) else 1)) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      simp only [ite_true]
      field_simp
    · simp [hj]
  rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [Finset.prod_ite_eq' univ i _, ite_eq_left (Finset.mem_univ i)]
  nth_rw 1 [show b = (b - 1) + 1 by omega]
  rw [pow_succ, mul_div_assoc']
  field_simp

/-- **Off-diagonal pair factorization**: a two-coordinate
functional summed over all batches factorizes through the
two population sums: `Σ_ω f(ω i)·h(ω k) = |V|^(b−2)·(Σ f)·
(Σ h)` for `i ≠ k` (the two-if product decomposition). -/
theorem sum_pair (f h : V → ℝ) (i k : Fin b) (hik : i ≠ k) :
    ∑ ω : Fin b → V, f (ω i) * h (ω k)
      = ((Fintype.card V : ℝ) ^ (b - 2)) * (∑ v, f v) * (∑ v, h v) := by
  classical
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hNpos : N ≠ 0 := by positivity
  have hb : 2 ≤ b := by
    have h2 : (2 : ℕ) ≤ Finset.card (insert i ({k} : Finset (Fin b))) := by
      rw [Finset.card_insert_of_notMem (by simp [hik])]
      simp
    have h3 := Finset.card_le_card (Finset.subset_univ (insert i ({k} : Finset (Fin b))))
    rw [Finset.card_univ, Fintype.card_fin] at h3
    exact Nat.le_trans h2 h3
  set ff : Fin b → V → ℝ :=
    fun j v => (if j = i then f v else (1:ℝ)) * (if j = k then h v else (1:ℝ)) with hff
  have hprod : ∀ ω : Fin b → V,
      (∏ j, ff j (ω j)) = f (ω i) * h (ω k) := by
    intro ω
    have hbeta : ∀ j : Fin b, ff j (ω j)
        = (if j = i then f (ω j) else (1:ℝ))
          * (if j = k then h (ω j) else (1:ℝ)) := fun j => rfl
    rw [Finset.prod_congr rfl (fun j _ => hbeta j), Finset.prod_mul_distrib]
    rw [Finset.prod_ite_eq' univ i _, Finset.prod_ite_eq' univ k _]
    simp [Finset.mem_univ, hik]
  have hcoord : ∀ j : Fin b, (∑ v, ff j v)
      = if j = i then (∑ v, f v) else if j = k then (∑ v, h v) else N := by
    intro j
    by_cases hj1 : j = i
    · subst hj1
      simp [hff, hik]
    · by_cases hj2 : j = k
      · subst hj2
        simp [hff, hj1]
      · simp [hff, hj1, hj2]
        rw [← hN]
  have hsplit := sum_prod_factor (V := V) ff
  rw [Finset.sum_congr rfl (fun ω _ => hprod ω)] at hsplit
  rw [hsplit]
  simp only [hcoord]
  -- remaining: the three-way selector product
  have h1 : ∀ j : Fin b,
      (if j = i then (∑ v, f v) else if j = k then (∑ v, h v) else N)
        = N * ((if j = i then ((∑ v, f v) / N) else 1)
          * (if j = k then ((∑ v, h v) / N) else 1)) := by
    intro j
    by_cases hj1 : j = i
    · subst hj1
      simp [hik]
      field_simp
    · by_cases hj2 : j = k
      · subst hj2
        simp [hj1]
        field_simp
      · simp [hj1, hj2]
  rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq' univ i _, Finset.prod_ite_eq' univ k _]
  simp only [Finset.mem_univ, ite_eq_left (Finset.mem_univ i),
    ite_eq_left (Finset.mem_univ k), true_iff]
  nth_rw 1 [show b = (b - 2) + 2 by omega]
  rw [pow_add, pow_two]
  simp only [ite_true]
  field_simp

/-- Uniform coordinate density: every draw uniform on `V`. -/
noncomputable def uniP (b : ℕ) : Fin b → V → ℝ := fun _ _ => ((Fintype.card V : ℝ) ⁻¹)

theorem uniP_isProb (b : ℕ) : IsProbSys (V := V) (uniP (V := V) b) := by
  intro i
  constructor
  · intro v
    simp [uniP]
  · simp only [uniP, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

theorem uniP_dens (b : ℕ) (ω : Fin b → V) :
    prodDens (V := V) (uniP (V := V) b) ω = ((Fintype.card V : ℝ) ^ b) ⁻¹ := by
  simp only [prodDens, uniP, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← inv_pow]

/-- The mini-batch average: `ĝ(ω) = (1/B)·Σ_{i<B} g(ω i)`. -/
noncomputable def batchMean (g : V → ℝ) (ω : Fin b → V) : ℝ :=
  (∑ i, g (ω i)) / b

/-- **Unbiasedness of the batch mean**: over independent
uniform draws, the expected mini-batch average equals the
population mean. -/
theorem batchMean_unbiased (g : V → ℝ) :
    prodE (uniP b) (batchMean g) = popMean g := by
  have hb0 : 0 < b := Fin.pos_iff_nonempty.mpr ‹_›
  have hbpos : (0 : ℝ) < b := Nat.cast_pos.mpr hb0
  have hb0' : 0 < b := Fin.pos_iff_nonempty.mpr ‹_›
  unfold prodE batchMean popMean
  simp only [uniP_dens b]
  have hmul : ∀ ω : Fin b → V,
      ((Fintype.card V : ℝ) ^ b) ⁻¹ * ((∑ i, g (ω i)) / b)
        = (((Fintype.card V : ℝ) ^ b) ⁻¹ / b) * ∑ i, g (ω i) := by
    intro ω
    field_simp
  rw [Finset.sum_congr rfl (fun ω _ => hmul ω), ← Finset.mul_sum]
  have hswap : ∑ ω : Fin b → V, ∑ i : Fin b, g (ω i)
      = ∑ i : Fin b, ∑ ω : Fin b → V, g (ω i) := Finset.sum_comm
  rw [hswap]
  have hcoord : ∀ i : Fin b, ∑ ω : Fin b → V, g (ω i)
      = ((Fintype.card V : ℝ) ^ (b - 1)) * ∑ v, g v := sum_coord g
  rw [Finset.sum_congr rfl (fun i _ => hcoord i)]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hb1 : 1 ≤ b := by omega
  have hNsplit : ((Fintype.card V : ℝ) ^ b)
      = ((Fintype.card V : ℝ) ^ (b - 1)) * (Fintype.card V : ℝ) := by
    nth_rw 1 [show b = (b - 1) + 1 by omega]
    rw [pow_succ]
  rw [hNsplit]
  field_simp

/-- **THE TEMPERATURE LAW**: the variance of the mini-batch
average is the population variance divided by the batch
size: `Var(ĝ) = Var(g)/B`. The off-diagonal cross terms
vanish by independence (each factors through the centered
population sum, which is zero), the `B` diagonal terms give
`B·Var(g)`, and the prefactor `1/B²` leaves `1/B`: the
reservoir temperature of the gradient noise is `1/B`. -/
theorem batch_variance_eq (g : V → ℝ) :
    prodE (uniP b) (fun ω => (batchMean g ω - popMean g) ^ 2) = popVar g / b := by
  classical
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hNpos : N ≠ 0 := by positivity
  have hb0 : 0 < b := Fin.pos_iff_nonempty.mpr ‹_›
  have hbpos : (0 : ℝ) < b := Nat.cast_pos.mpr hb0
  set X := centered g with hX
  have hX0 : ∑ v, X v = 0 := sum_centered g
  -- the centered batch mean
  have hshift : ∀ ω : Fin b → V,
      batchMean g ω - popMean g = (∑ i, X (ω i)) / b := by
    intro ω
    unfold batchMean
    have hx : ∀ i : Fin b, g (ω i) = X (ω i) + popMean g := by
      intro i
      simp only [hX, centered]
      ring
    have hsum : ∑ i, g (ω i) = ∑ i, (X (ω i) + popMean g) :=
      Finset.sum_congr rfl (fun i _ => hx i)
    rw [hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  -- expand the square over pairs, prefactor pulled out
  have hsq : ∀ ω : Fin b → V,
      (batchMean g ω - popMean g) ^ 2
        = (((b : ℝ) * (b : ℝ)) ⁻¹)
          * ((∑ i, X (ω i)) * (∑ k, X (ω k))) := by
    intro ω
    rw [hshift ω, div_pow, sq]
    field_simp
  unfold prodE
  simp only [uniP_dens b]
  rw [Finset.sum_congr rfl (fun ω _ => by rw [hsq ω])]
  -- the inner coordinate sums: diagonal vs off-diagonal
  have hinner : ∀ i k : Fin b, ∑ ω : Fin b → V, X (ω i) * X (ω k)
      = if i = k then N ^ (b - 1) * (∑ v, X v * X v) else 0 := by
    intro i k
    by_cases hik : i = k
    · subst hik
      simp only [ite_true]
      exact sum_coord (fun v => X v * X v) i
    · rw [if_neg hik, sum_pair X X i k hik, hX0]
      ring
  -- exchange the outer sum with the pair sums
  have hswap2 : ∑ ω : Fin b → V, (∑ i, X (ω i)) * (∑ k, X (ω k))
      = ∑ i : Fin b, ∑ k : Fin b, ∑ ω : Fin b → V, X (ω i) * X (ω k) := by
    have hstep : ∀ ω : Fin b → V, (∑ i, X (ω i)) * (∑ k, X (ω k))
        = ∑ i : Fin b, ∑ k : Fin b, X (ω i) * X (ω k) :=
      fun ω => Finset.sum_mul_sum _ _ _ _
    rw [Finset.sum_congr rfl (fun ω _ => hstep ω)]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin b → V)))
      (t := (Finset.univ : Finset (Fin b)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm (s := (Finset.univ : Finset (Fin b → V)))
      (t := (Finset.univ : Finset (Fin b)))
  -- collapse the pair sum to the diagonal
  have hsingle : ∀ i : Fin b, ∑ k : Fin b,
      (if i = k then N ^ (b - 1) * (∑ v, X v * X v) else (0:ℝ))
        = N ^ (b - 1) * (∑ v, X v * X v) := by
    intro i
    rw [Finset.sum_ite_eq univ i _]
    simp
  have hpairsum : ∑ i : Fin b, ∑ k : Fin b, ∑ ω : Fin b → V, X (ω i) * X (ω k)
      = b * N ^ (b - 1) * (∑ v, X v * X v) := by
    rw [Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun k _ => hinner i k))]
    rw [Finset.sum_congr rfl (fun i _ => hsingle i), Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    ring
  -- pull the constant out and finish
  rw [← Finset.mul_sum, ← Finset.mul_sum, hswap2, hpairsum]
  have hb1 : 1 ≤ b := by omega
  have hNsplit : N ^ b = N ^ (b - 1) * N := by
    nth_rw 1 [show b = (b - 1) + 1 by omega]
    rw [pow_succ]
  have hNpos : 0 < N := by positivity
  rw [hNsplit]
  rw [popVar_eq, hX, ← hN]
  field_simp

/-- **Scale separation** (2606.28808, finite form): for a
step size `0 < η ≤ 1` and any fluctuation amplitude `θ ≥ 0`,
the one-step contribution `η·θ` sits at or below the `√η`
scale: the noise enters at order `√η` or finer. No
stochastic-calculus claim. -/
theorem noise_scale_separation (eta theta : ℝ)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (htheta : 0 ≤ theta) :
    eta * theta ≤ Real.sqrt eta * theta :=
  mul_le_mul_of_nonneg_right (Real.le_sqrt_self_iff.mpr heta1) htheta


/-- **Annealing by batch growth ( kernel, the
1711.00489 axis choice)**: growing the batch geometrically
(`B_{t+1} = c·B_t`, `c > 1`) cools the noise reservoir
geometrically (temperature `1/B_t`, `batch_variance_eq`), and
the TOTAL noise injected over any horizon is bounded by the
geometric cooling budget `σ²·c/(B₀·(c−1))` — finite and
horizon-independent. Decaying the LR at fixed batch is the
SAME mathematics on the other axis (the equivalence of
1711.00489); the batch axis buys the cooling without
shrinking the step size. -/
theorem anneal_by_batch {sigma c : ℝ} (B : ℕ → ℝ) (n : ℕ)
    (hsigma : 0 ≤ sigma) (hc1 : 1 < c) (hB0 : 0 < B 0)
    (hgrow : ∀ t < n, B (t + 1) = c * B t) :
    ∑ t ∈ Finset.range n, sigma ^ 2 / B t
      ≤ sigma ^ 2 * c / (B 0 * (c - 1)) := by
  -- geometric batch growth: B t = B 0 * c ^ t
  have hB : ∀ t ≤ n, B t = B 0 * c ^ t := by
    intro t ht
    induction t with
    | zero => rw [pow_zero, mul_one]
    | succ t iht =>
        rw [hgrow t (Nat.lt_of_succ_le ht)]
        rw [iht (Nat.le_of_succ_le ht)]
        rw [pow_succ]
        ring
  -- termwise bound: sigma^2 / B t = (sigma^2 / B 0) * (1/c)^t
  have hterm : ∀ t < n, sigma ^ 2 / B t
      = (sigma ^ 2 / B 0) * ((1 / c) ^ t) := by
    intro t ht
    rw [hB t (Nat.le_of_lt ht), one_div_pow]
    field_simp
  -- the geometric budget
  have hgeo : ∑ t ∈ Finset.range n, (1 / c) ^ t ≤ 1 / (1 - 1 / c) := by
    have hrc : 0 ≤ 1 / c := by positivity
    have hrc1 : (1:ℝ) / c < 1 := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < c)]
      linarith
    exact Hagi.Foundations.geom_sum_le_inv (rho := 1 / c) n hrc hrc1
  calc ∑ t ∈ Finset.range n, sigma ^ 2 / B t
      = ∑ t ∈ Finset.range n, (sigma ^ 2 / B 0) * ((1 / c) ^ t) := by
        exact Finset.sum_congr rfl fun t ht => hterm t (Finset.mem_range.mp ht)
    _ = (sigma ^ 2 / B 0) * ∑ t ∈ Finset.range n, (1 / c) ^ t := by
        rw [← Finset.mul_sum]
    _ ≤ (sigma ^ 2 / B 0) * (1 / (1 - 1 / c)) :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = sigma ^ 2 * c / (B 0 * (c - 1)) := by
        field_simp

end Batch

end Hagi.Probability

namespace Hagi
export Hagi.Probability (popMean popVar centered popVar_eq sum_centered card_pos_of_nonempty prod_two_sel sum_coord sum_pair uniP uniP_isProb uniP_dens batchMean batchMean_unbiased batch_variance_eq noise_scale_separation anneal_by_batch)
end Hagi
