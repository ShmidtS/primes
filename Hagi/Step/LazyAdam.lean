/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Hagi.Math.Foundations.Recurrence

/-!
# LazyAdam-семейство

Базовый LazyAdam и его моментная версия.

`rowStep_inert_iterate`: неактивная строка (`p.grad == 0`) с нулевым адамовым
шагом сохраняется точно — ленивое затухание `optimal_lm.py` (`act = (p.grad != 0)`)
не трогает редкие байты. `dense_decay_loss`: плотное затухание теряет
`(1 − (1−λ)^T)·|w|` массы строки за `T` шагов неактивности.
-/

set_option linter.style.header false

/-!
# LazyAdam — точная эквивалентность ленивого и плотного Adam (β₁ = 0)

Модель: AdamW с β₁ = 0, decoupled weight decay; вторая
момента на строке таблицы обновляется только на затронутых
шагах: `v_t = β₂·v_{t−1} + (1−β₂)·g_t²`.

* `lazyDecay_exact`: за d пропущенных шагов плотная
  рекуррентность даёт `v_{τ+d} = β₂^d·v_τ` — точно
  геометрический декей (итерация `x ↦ β₂·x`);
* `lazyReplay_exact`: тождество композиции —
  `β₂^d·(v + (1−β₂)g²) = β₂^d·v + β₂^d·(1−β₂)·g²`;
  вместе с точной геометрией декея — алгебраическая основа
  эквивалентности ленивого повтора плотной траектории;
* `supportSet_bound`: `|(S_in ∪ S_tgt) ∪ S_neg|.card
  ≤ |S_in| + |S_tgt| + |S_neg|`.

Граница: эквивалентность — между ленивым β₁=0 и плотным
β₁=0; сравнение с AdamW β₁=0.9 — эмпирическое (A/B),
не теорема.
-/

open Finset

namespace Hagi.Step

section LazyAdam

/- Состояние второй момента на строку (β₁ = 0): скаляр
на строку. -/

/-- Геометрический декей за пропущенную серию: итерация
`x ↦ β₂·x` d раз даёт `(β₂^d)·v0` — точно, одним
скалярным умножением. -/
theorem lazyDecay_exact (beta2 v0 : ℝ) (d : ℕ) :
    (fun x => beta2 * x)^[d] v0 = (beta2^d) * v0 := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ]
    ring

/-- Тождество композиции повтора:
`(β₂^d)·(vstale + (1−β₂)·g²)
= (β₂^d)·vstale + (β₂^d)·(1−β₂)·g²` — алгебраическая
основа эквивалентности ленивого повтора (с
`lazyDecay_exact` — по индукции по паттерну касаний). -/
theorem lazyReplay_exact (beta2 vstale g : ℝ) (d : ℕ) :
    (beta2^d) * (vstale + (1 - beta2) * g^2)
      = (beta2^d) * vstale + (beta2^d) * (1 - beta2) * g^2 := by
  ring


/-- Шаг AdamW на строке: затухание `λ` только активной строки (`act = 1`) и
адамов шаг `u`. -/
noncomputable def rowStep (lam act u : ℝ) (w : ℝ) : ℝ := (1 - lam * act) * w - u
/-- Неактивная строка (`act = 0`) с нулевым адамовым шагом (`u = 0`) инертна. -/
theorem rowStep_inert (lam w : ℝ) : rowStep lam 0 0 w = w := by
  unfold rowStep; ring
/-- За `T` шагов неактивности строка сохраняется точно. -/
theorem rowStep_inert_iterate (lam : ℝ) (T : ℕ) (w : ℝ) :
    (rowStep lam 0 0)^[T] w = w := by
  induction T with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih]; exact rowStep_inert lam w
/-- Плотное затухание (`act = 1`, `u = 0`) за `T` шагов сжимает строку к нулю:
`(1−λ)^T·w` — источник потери редких байтов. -/
theorem rowStep_dense_decay (lam : ℝ) (hl : 0 ≤ lam) (hlam : lam < 1) (T : ℕ) (w : ℝ) :
    (rowStep lam 1 0)^[T] w = (1 - lam)^T * w := by
  induction T with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih]; unfold rowStep; ring
/-- Ленивое правило `(1−λ)^T·w` для неактивной строки — потеря массы
`|w|·(1 − (1−λ)^T)`, при λ = lr·wd малых T — ∼ `T·λ·|w|`. -/
theorem dense_decay_loss (lam : ℝ) (hl : 0 ≤ lam) (hlam : lam < 1) (T : ℕ) (w : ℝ) :
    |w - (rowStep lam 1 0)^[T] w| = (1 - (1 - lam)^T) * |w| := by
  rw [rowStep_dense_decay lam hl hlam T w]
  have h : 0 ≤ (1 - lam)^T := pow_nonneg (by linarith) T
  have hle : (1 - lam)^T ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have heq : w - (1 - lam)^T * w = (1 - (1 - lam)^T) * w := by ring
  rw [heq, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - (1 - lam)^T)]

set_option linter.unusedDecidableInType false in
-- гипотеза сохранена: документированная посылка API
/-- `((S_in ∪ S_tgt) ∪ S_neg).card ≤ S_in.card + S_tgt.card
+ S_neg.card` (union bound для затронутых строк). -/
theorem supportSet_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S_in S_tgt S_neg : Finset ι) :
    ((S_in ∪ S_tgt) ∪ S_neg).card
      ≤ S_in.card + S_tgt.card + S_neg.card := by
  have h1 : ((S_in ∪ S_tgt) ∪ S_neg).card
      ≤ (S_in ∪ S_tgt).card + S_neg.card :=
    Finset.card_union_le _ _
  have h2 : (S_in ∪ S_tgt).card ≤ S_in.card + S_tgt.card :=
    Finset.card_union_le _ _
  omega

end LazyAdam

end Hagi.Step

namespace Hagi

end Hagi

set_option linter.style.header false

/-!
# LazyAdamMomentum — декей плотной первой момента при β₁ > 0

* `dense_m_decay`: при нулевых градиентах (m (t+1) = β₁·m t)
  `m k = β₁^k·m 0` — точно геометрически;
* `lazy_moment_drift`: при `|m 0| ≤ M` и `0 ≤ β₁` —
  `|m d| ≤ |β₁^d|·M` (ошибка ленивого приближения m := 0);
* `lazy_momentum_bound`: при `0 < β < 1`, `0 ≤ c` —
  `c·Σ_{s<d}β^(s+1) ≤ c·β/(1−β)`.

* `touchStep_dense_mono`: с плотным декеем второго момента шаг касания
  редкого байта (`v_d = β₂^d·v₀`) растёт по числу пропущенных шагов `d`;
  с ленивым (`v_d = v₀`) — постоянен по построению.

Так эффект LazyAdam в optimal_lm.py (CE 1.334 → 1.183) — не потеря весов
(`dense_decay_loss` при λ = lr·wd ~ 1e-7 ничтожна), а стабильность шага
редкого байта. Полная траекторная эквивалентность не доказана.
-/

open Finset

namespace Hagi.Step

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

/-- Адамов шаг на строке при касании: `lr·g / (√v + ε)`. -/
noncomputable def touchStep (lr eps g v : ℝ) : ℝ := lr * g / (Real.sqrt v + eps)
/-- Плотный декей второго момента (`v_d = β₂^d·v₀`) уменьшает знаменатель шага
с ростом числа пропущенных шагов. -/
theorem touch_den_dense_anti (eps v0 b2 : ℝ) (hε : 0 < eps) (hv : 0 ≤ v0)
    (hb0 : 0 ≤ b2) (hb1 : b2 ≤ 1) {d e : ℕ} (hde : d ≤ e) :
    Real.sqrt (b2^e * v0) + eps ≤ Real.sqrt (b2^d * v0) + eps := by
  have hle : b2^e ≤ b2^d := pow_le_pow_of_le_one hb0 hb1 hde
  have hs : Real.sqrt (b2^e * v0) ≤ Real.sqrt (b2^d * v0) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hle hv)
  linarith
/-- Значит шаг касания редкого байта с плотным декеем растёт по `d` (при `lr·g ≥ 0`),
с ленивым (`v_d = v₀`) — постоянен. -/
theorem touchStep_dense_mono (lr eps g v0 b2 : ℝ) (h : 0 ≤ lr * g) (hε : 0 < eps)
    (hv : 0 < v0) (hb0 : 0 ≤ b2) (hb1 : b2 ≤ 1) {d e : ℕ} (hde : d ≤ e) :
    touchStep lr eps g (b2^d * v0) ≤ touchStep lr eps g (b2^e * v0) := by
  unfold touchStep
  have hd := touch_den_dense_anti eps v0 b2 hε hv.le hb0 hb1 hde
  have hpos : 0 < Real.sqrt (b2^e * v0) + eps := by
    have : 0 ≤ Real.sqrt (b2^e * v0) := Real.sqrt_nonneg _
    linarith
  exact div_le_div₀ h (le_refl _) hpos hd

end Hagi.Step
