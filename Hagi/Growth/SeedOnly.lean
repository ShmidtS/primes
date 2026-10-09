/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.CycleChannel

set_option linter.style.header false

/-!
# SeedOnly — ограничение разнообразия для seed-only siblings

* `geom_range_identity`: `(a − 1)·Σ_{i<n} a^i = a^n − 1`;
* `disp_recurrence_general`: при `0 ≤ a`, `0 ≤ s`,
  `D (t+1) ≤ a·D t + s` следует
  `D t ≤ a^t·D 0 + s·Σ_{i<t} a^i` (любое a ≥ 0);
* `sum_dist_mean_le`: `Σ‖x a − x̄‖² ≤ Σ‖x a − y‖²` для любого y;
* `seed_only_disp_bound`: при `dispL t ≤ Λ²·dispP t`,
  `dispP (t+1) ≤ a·dispP t + s` и `dispP 0 = 0` —
  `dispL t ≤ Λ²·s·Σ_{i<t} a^i`;
* `seed_only_grow_stop`: если
  `gapInf ≤ c·Λ²·s/(1−a) < eps`, то `gapInf < eps`.

Ядро «gap ⇒ dispersion» (Jensen/Hoeffding, константа c) здесь
НЕ доказано и цитируется как посылка; результат применим к
gen ≥ 2 (одинаковый init). Режим a < 1 решается измерением.
-/

open Finset Real InnerProductSpace

namespace Hagi

section SeedOnly

/-- Конечная геометрическая сумма:
`(a − 1)·Σ_{i<n} a^i = a^n − 1` (любое a). -/
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

/-- Если `0 ≤ a`, `0 ≤ s` и `D (t+1) ≤ a·D t + s` при всех t,
то `D t ≤ a^t·D 0 + s·Σ_{i<t} a^i` (любое a ≥ 0;
при `D 0 = 0` и `a < 1` — `D t ≤ s/(1−a)`). -/
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

/-- При `0 < n` и любом y:
`Σ‖x a − x̄‖² ≤ Σ‖x a − y‖²`, где `x̄` — среднее. -/
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

/-- Если `dispL t ≤ Λ²·dispP t`, `dispP (t+1) ≤ a·dispP t + s`
и `dispP 0 = 0`, то
`dispL t ≤ Λ²·s·Σ_{i<t} a^i`. -/
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

/-- Если `gapInf ≤ c·Λ²·s/(1−a)` и
`c·Λ²·s/(1−a) < eps`, то `gapInf < eps`. -/
theorem seed_only_grow_stop (c Lam a s eps gapInf : ℝ)
    (_hc : 0 ≤ c) (_hLam : 0 ≤ Lam) (_ha : 0 ≤ a) (_ha1 : a < 1) (_hs : 0 ≤ s)
    (hbound : gapInf ≤ c * Lam^2 * s / (1 - a))
    (hfloor : c * Lam^2 * s / (1 - a) < eps) :
    gapInf < eps := by
  linarith

end SeedOnly

end Hagi
