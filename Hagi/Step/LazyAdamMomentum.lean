/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.Recurrence

set_option linter.style.header false

/-!
# LazyAdamMomentum — декей плотной первой момента при β₁ > 0

* `dense_m_decay`: при нулевых градиентах (m (t+1) = β₁·m t)
  `m k = β₁^k·m 0` — точно геометрически;
* `lazy_moment_drift`: при `|m 0| ≤ M` и `0 ≤ β₁` —
  `|m d| ≤ |β₁^d|·M` (ошибка ленивого приближения m := 0);
* `lazy_momentum_bound`: при `0 < β < 1`, `0 ≤ c` —
  `c·Σ_{s<d}β^(s+1) ≤ c·β/(1−β)`.

Полная траекторная эквивалентность (оценка через
интерливинг-касания) — не доказана.
-/

open Finset

namespace Hagi

/-- При `m (t+1) = β₁·m t` для всех t: `m k = β₁^k·m 0`
(геометрический декей незатронутой строки). -/
theorem dense_m_decay (beta1 : ℝ) (m : ℕ → ℝ)
    (hstep : ∀ t, m (t+1) = beta1 * m t) (k : ℕ) :
    m k = (beta1^k) * m 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [hstep, ih, pow_succ]; ring

/-- При `0 ≤ beta1` и `|m 0| ≤ M` (той же рекуррентности):
`|m d| ≤ |beta1^d|·M`. -/
theorem lazy_moment_drift (beta1 M : ℝ) (m : ℕ → ℝ) (hb : 0 ≤ beta1)
    (hM0 : |m 0| ≤ M) (hstep : ∀ t, m (t+1) = beta1 * m t) (d : ℕ) :
    |m d| ≤ |beta1^d| * M := by
  rw [dense_m_decay beta1 m hstep d, abs_mul, abs_of_nonneg (pow_nonneg hb d)]
  exact mul_le_mul_of_nonneg_left hM0 (pow_nonneg hb d)

/-- При `0 < beta < 1` и `0 ≤ c`:
`c·Σ_{s<d} beta^(s+1) ≤ c·(beta/(1−beta))`
(с — эффективная величина шага, эмпирическая посылка). -/
theorem lazy_momentum_bound (beta c : ℝ)
    (hbeta : 0 < beta) (hbeta1 : beta < 1) (hc : 0 ≤ c)
    (d : ℕ) :
    c * (∑ s ∈ Finset.range d, beta ^ (s + 1))
      ≤ c * (beta / (1 - beta)) := by
  have hgeom : ∑ s ∈ Finset.range d, beta ^ (s + 1) ≤ beta / (1 - beta) := by
    have hsplit : ∑ s ∈ Finset.range d, beta ^ (s + 1)
        = beta * ∑ s ∈ Finset.range d, beta ^ s := by
      rw [show ∑ s ∈ Finset.range d, beta ^ (s + 1)
          = ∑ s ∈ Finset.range d, beta * beta ^ s from
          Finset.sum_congr rfl (fun s _ => by ring)]
      exact (Finset.mul_sum (s := Finset.range d) (f := fun s => beta ^ s) (a := beta)).symm
    rw [hsplit]
    have hsum := Hagi.Foundations.geom_sum_le_inv beta d hbeta.le hbeta1
    have hmul : beta * ∑ s ∈ Finset.range d, beta ^ s
        ≤ beta * (1 / (1 - beta)) :=
      mul_le_mul_of_nonneg_left hsum hbeta.le
    have hconv : beta * (1 / (1 - beta)) = beta / (1 - beta) := by field_simp
    linarith
  exact mul_le_mul_of_nonneg_left hgeom hc
