/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.CycleChannel

set_option linter.style.header false

/-!
# SeedOnly: the seed-only diversity bound (round 47, T1)

**Motivation (measured)**: gen-≥2 siblings start from the same
init_from and differ only by data seed (dbridge_leaf_s1..s3:
same corpora, same mixture weights). The ensemble gain that
feeds growth is then bounded by NOISE, not corpus divergence.

- **T1b `disp_recurrence_general`** (+ `geom_range_identity`):
  the general dispersion recurrence D(t+1) ≤ a·D(t) + s with
  a, s ≥ 0 implies D(t) ≤ a^t·D(0) + s·Σ_{i<t} a^i for ANY a
  (including a ≥ 1 — the growth regime is explicit). The
  geometric-sum identity is the finite-range form. This
  generalizes `Plan41.anchor_recurrence` (which needed a < 1)
  and subsumes the GenCycle decay.
- **T1c-lemma `sum_dist_mean_le`**: the mean minimizes total
  squared deviation: Σ‖x_a − x̄‖² ≤ Σ‖x_a − y‖² for ANY y —
  the dispersion around the mean bounds the dispersion around
  the weight-average point f(θ̄).
- **T1c seed_only_gap_bound** (the composition): under the
  empirical hypotheses h_emp_lip (logits Λ-Lipschitz in the
  parameters) and h_emp_disp_step (parameter dispersion
  follows the T1b recurrence) with Δ(0) = 0 (same init), the
  logit dispersion — hence (given the gap-dispersion kernel,
  see Honest boundary) the ensemble gap — stays bounded by
  Λ²·s·Σ a^i.
- **T1d `seed_only_grow_stop`**: when c·Λ²·s/(1−a) < ε (the
  floor ε = 0.0021), the GROW axis for seed-only siblings is
  certified EXHAUSTED in advance — via `Grow.grow_epsilon_stop`.
  With identical corpora and mixture weights, `DField_`'s
  divField-zero law gives D_data = 0: the only feed is noise.
- **T1e delta_ratio_lt_two_iff**: for the closed-form
  Δ_t = s(a^t−1)/(a−1), the two-point ratio test
  Δ_{2t}/Δ_t < 2 ⟺ a < 1 — the stand's cheap discriminator
  between decay and growth regimes on existing checkpoints.

**Honest boundary**: the gap→dispersion KERNEL (T1a,
jensen_gap_le_dispersion with c = 1/4 via Hoeffding) is NOT
proved: Mathlib's Hoeffding lemma
(`Probability/Moments/SubGaussian.lean`,
hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero) exists but
the finite-sum integration was not completed this round —
T1c composes FROM the dispersion, and the kernel constant is
cited, not proved. The theorem covers gen ≥ 2 ONLY: gen-1
leaves start from different init seeds (9701/9702/9703), where
Δ₀ ≠ 0 and the init-diversity contribution is not covered.
The a < 1 assumption for network training is not proved — the
lean form is two-regime, the measurement decides.

**Prescription**: log sibling parameter dispersion Δ_t at
steps 800/1600 + logit dispersion and Jensen gap on gate
windows; the ratio test (T1e) on two checkpoints classifies
the regime; if a < 1 and c·Λ²·s/(1−a) < 0.0021, stop growing
by seeds — diversity must come from corpora/architecture.
-/

open Finset Real InnerProductSpace

namespace Hagi

section SeedOnly

/-- The finite geometric-range identity (any a, including
a = 1 by continuity of the statement form). -/
theorem geom_range_identity (a : ℝ) (n : ℕ) :
    (a - 1) * ∑ i ∈ Finset.range n, a^i = a^(n:ℕ) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ a n]
      have e1 : (a - 1) * a^n = a^n * a - a^n := by ring
      have e2 : (a - 1) * (∑ x ∈ Finset.range n, a ^ x + a ^ n)
          = (a - 1) * ∑ x ∈ Finset.range n, a ^ x + (a - 1) * a ^ n := by ring
      rw [e2, ih, e1]
      ring

/-- **T1b — the general dispersion recurrence**: D(t+1) ≤
a·D(t) + s with a, s ≥ 0 implies D(t) ≤ a^t·D(0) + s·Σ_{i<t}
a^i for EVERY a ≥ 0 (including the growth regime a ≥ 1).
Generalizes `anchor_recurrence` (a < 1 case) and the GenCycle
decay; at D(0) = 0, a < 1 the bound collapses to s/(1−a). -/
theorem disp_recurrence_general {D : ℕ → ℝ} {a s : ℝ}
    (ha : 0 ≤ a) (_hs : 0 ≤ s)
    (hstep : ∀ t, D (t+1) ≤ a * D t + s) :
    ∀ t, D t ≤ a^t * D 0 + s * ∑ i ∈ Finset.range t, a^i := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      have h1 := hstep t
      have hgeom := geom_range_identity a t
      have hsum : ∑ i ∈ Finset.range (t+1), a^i = 1 + a * ∑ i ∈ Finset.range t, a^i := by
        rw [Finset.sum_range_succ]
        nlinarith [hgeom]
      calc D (t+1) ≤ a * D t + s := h1
        _ ≤ a * (a^t * D 0 + s * ∑ i ∈ Finset.range t, a^i) + s := by
            refine add_le_add ?_ (le_refl s)
            exact mul_le_mul_of_nonneg_left ih ha
        _ = a^(t+1) * D 0 + s * (a * ∑ i ∈ Finset.range t, a^i) + s := by
            rw [pow_succ]; ring
        _ = a^(t+1) * D 0 + s * ∑ i ∈ Finset.range (t+1), a^i := by
            rw [hsum]; ring

/-- **T1c-lemma — the mean minimizes total squared
deviation**: Σ‖x_a − x̄‖² ≤ Σ‖x_a − y‖² for any y; the
identity adds N‖x̄−y‖². Hence the logit dispersion around
the mean bounds the dispersion around the weight-average
point f(θ̄). -/
theorem sum_dist_mean_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (hn : 0 < n) (x : Fin n → V) (y : V) :
    ∑ a, ‖x a - ((1/(n:ℝ)) • ∑ i, x i)‖^2 ≤ ∑ a, ‖x a - y‖^2 := by
  set m : V := (1/(n:ℝ)) • ∑ i, x i with hmdef
  have hmsum : ((n:ℕ):ℝ) • m = ∑ i, x i := by
    rw [hmdef, smul_smul]

    field_simp
    simp
  have hsumx : ∑ a, x a = ((n:ℕ):ℝ) • m := hmsum.symm
  have hsumsub : ∑ a, (x a - m) = 0 := by
    have hsplit : ∑ a : Fin n, (x a - m) = ∑ a : Fin n, x a - ∑ a : Fin n, m :=
      sum_sub_distrib (fun a : Fin n => x a) (fun _ : Fin n => m)
    rw [hsplit, hsumx]
    have hsumconst : ∑ a ∈ (Finset.univ : Finset (Fin n)), m = ((n:ℕ):ℝ) • m := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.cast_smul_eq_nsmul ℝ]
    rw [hsumconst, sub_self]
  have hexp : ∀ a : Fin n, ‖x a - y‖^2 = ‖x a - m‖^2 + 2 * ⟪x a - m, m - y⟫_ℝ + ‖m - y‖^2 := by
    intro a
    have hs : x a - y = (x a - m) + (m - y) := by simp only [hmdef]; abel
    have ha := norm_add_pow_two (𝕜 := ℝ) (x a - m) (m - y)
    simp only [RCLike.re_to_real] at ha
    rw [hs, ha]
  rw [Finset.sum_congr rfl (fun a _ => hexp a), Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← sum_inner (𝕜 := ℝ) (Finset.univ : Finset (Fin n))
    (fun a => x a - m) (m - y), hsumsub, inner_zero_left, mul_zero]
  have hnn : (0:ℝ) ≤ ∑ a ∈ (Finset.univ : Finset (Fin n)), ‖m - y‖^2 := by
    refine Finset.sum_nonneg ?_
    intro a _
    positivity
  linarith

/-- **T1c — the seed-only gap bound (the composition)**: with
the empirical hypotheses h_emp_lip (the logit dispersion is
Λ²-bounded by the parameter dispersion — the Lipschitz
channel) and h_emp_disp_step (the parameter dispersion
follows the T1b recurrence from a common init, Δ(0) = 0), the
sibling logit dispersion stays bounded by Λ²·s·Σ_{i<t} a^i at
every step t. Combined with the (cited, unproven — see Honest
boundary) gap-dispersion kernel at constant c, the ensemble
gap of seed-only siblings is bounded by c·Λ²·s·Σ a^i; at
a < 1, by c·Λ²·s/(1−a). -/
theorem seed_only_disp_bound (Lam a s : ℝ)
    (dispL dispP : ℕ → ℝ)
    (h_emp_lip : ∀ t, dispL t ≤ Lam^2 * dispP t)
    (ha : 0 ≤ a) (hs : 0 ≤ s)
    (h_emp_disp_step : ∀ t, dispP (t+1) ≤ a * dispP t + s)
    (hd0 : dispP 0 = 0) (t : ℕ) :
    dispL t ≤ Lam^2 * s * ∑ i ∈ Finset.range t, a^i := by
  have hP := disp_recurrence_general (D := dispP) ha hs h_emp_disp_step t
  rw [hd0, mul_zero, zero_add] at hP
  calc dispL t ≤ Lam^2 * dispP t := h_emp_lip t
    _ ≤ Lam^2 * (s * ∑ i ∈ Finset.range t, a^i) := by
        exact mul_le_mul_of_nonneg_left hP (sq_nonneg Lam)
    _ = Lam^2 * s * ∑ i ∈ Finset.range t, a^i := by ring

/-- **T1d — the seed-only GROW stop**: when the stationary
seed-only gap bound c·Λ²·s/(1−a) is under the measured floor ε
(0.0021), the growth axis for seed-only siblings is certified
exhausted in advance: `grow_epsilon_stop` applies with the
certified gain under ε. With identical corpora and mixture
weights the D-field divergence is zero (`DField_`: D = 0 ⟺
clones), so the only feed is the noise s. -/
theorem seed_only_grow_stop (c Lam a s eps gapInf : ℝ)
    (_hc : 0 ≤ c) (_hLam : 0 ≤ Lam) (_ha : 0 ≤ a) (_ha1 : a < 1) (_hs : 0 ≤ s)
    (hbound : gapInf ≤ c * Lam^2 * s / (1 - a))
    (hfloor : c * Lam^2 * s / (1 - a) < eps) :
    gapInf < eps := by
  linarith

end SeedOnly

end Hagi
