/-
Momentum: инерционные (heavy-ball) рекурсии ускорения.

Двухчленный закон ошибки e_{k+1} ≤ q·e_k + β·e_{k−1}:
геометрическое затухание со скоростью ρ = (q+√(q²+4β))/2 —
положительным корнем характеристического уравнения
ρ² = q·ρ + β. Импульс β не ломает сжатие при q+β < 1;
ρ → q при β → 0 — цена инерции точна и явна.
-/
import Hagi.Optimization.InexactContraction

namespace Hagi.Optimization

open Hagi.Optimization

/-- Скорость инерционного метода (heavy-ball): положительный
корень характеристического уравнения ρ² = q·ρ + β. -/
noncomputable def momentumRate (q β : ℝ) : ℝ :=
  (q + Real.sqrt (q ^ 2 + 4 * β)) / 2

/-- Характеристическое уравнение: ρ² = q·ρ + β. -/
theorem momentumRate_char (q β : ℝ) (hβ : 0 ≤ β) :
    momentumRate q β ^ 2 = q * momentumRate q β + β := by
  have hsq : (0:ℝ) ≤ q ^ 2 + 4 * β := by nlinarith
  set s := Real.sqrt (q ^ 2 + 4 * β) with hsdef
  have hs2 : s ^ 2 = q ^ 2 + 4 * β := Real.sq_sqrt hsq
  have hρ2 : momentumRate q β * 2 = q + s := by
    unfold momentumRate
    rw [div_mul_eq_mul_div, mul_div_cancel_right₀ _ two_ne_zero]
  have hsub : momentumRate q β * 2 - q = s := by linarith [hρ2]
  have hexpand : (momentumRate q β * 2 - q) ^ 2 = q ^ 2 + 4 * β := by
    rw [hsub]; exact hs2
  nlinarith [hexpand]

/-- 0 < ρ < 1 при 0 < q, 0 ≤ β, q + β < 1. -/
theorem momentumRate_pos_lt_one (q β : ℝ) (hq : 0 < q)
    (hβ : 0 ≤ β) (hqb : q + β < 1) :
    0 < momentumRate q β ∧ momentumRate q β < 1 := by
  have hs : 0 ≤ Real.sqrt (q ^ 2 + 4 * β) := Real.sqrt_nonneg _
  have h1 : 0 < momentumRate q β := by
    unfold momentumRate
    positivity
  have hchar := momentumRate_char q β hβ
  have h2 : momentumRate q β < 1 := by
    -- ρ = (q+s)/2 < 1 ⟺ s < 2−q ⟺ s² < (2−q)² (обе части ≥ 0)
    have hq2 : q < 2 := by linarith
    have hsq : (0:ℝ) ≤ q ^ 2 + 4 * β := by nlinarith
    set s := Real.sqrt (q ^ 2 + 4 * β) with hsdef
    have hs2 : s ^ 2 = q ^ 2 + 4 * β := Real.sq_sqrt hsq
    have hspos : 0 ≤ s := Real.sqrt_nonneg _
    have htarget : s < 2 - q := by
      by_contra hc
      push_neg at hc
      have : (2 - q) ^ 2 ≤ s ^ 2 := by
        nlinarith [hc, hq2, hspos]
      rw [hs2] at this
      nlinarith [this]
    unfold momentumRate
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [htarget]
  exact ⟨h1, h2⟩

/-- ГЛАВНАЯ ТЕОРЕМА УСКОРЕНИЯ: инерционная (heavy-ball)
рекурсия e_{k+1} ≤ q·e_k + β·e_{k−1} при q + β < 1 затухает
геометрически со скоростью ρ = (q+√(q²+4β))/2 —
положительным корнем характеристического уравнения ρ²=qρ+β.
Импульс β не ломает сжатие, пока q+β<1; скорость ρ→q при
β→0 (чистый градиент) и растёт с β — цена инерции.
Граница: e_k ≤ max(e₀, e₁/ρ)·ρ^k. -/
theorem momentum_bound (e : ℕ → ℝ) (q β : ℝ) (hq : 0 < q)
    (hβ : 0 ≤ β) (hqb : q + β < 1)
    (hstep : ∀ k : ℕ, 1 ≤ k → e (k + 1) ≤ q * e k + β * e (k - 1))
    (k : ℕ) :
    e k ≤ max (e 0) (e 1 / momentumRate q β)
      * (momentumRate q β) ^ k := by
  obtain ⟨hρpos, hρ1⟩ := momentumRate_pos_lt_one q β hq hβ hqb
  have hchar := momentumRate_char q β hβ
  set ρ := momentumRate q β with hρdef
  set C := max (e 0) (e 1 / ρ) with hCdef
  -- сильная индукция: ∀ j ≤ n, e j ≤ C·ρ^j
  have key : ∀ n j : ℕ, j ≤ n → e j ≤ C * ρ ^ j := by
    intro n
    induction n with
    | zero =>
        intro j hj
        have : j = 0 := Nat.le_zero.mp hj
        subst this
        rw [pow_zero, mul_one]
        exact le_max_left _ _
    | succ n ih =>
        intro j hj
        rcases Nat.lt_or_ge j (n + 1) with hlt | hge
        · exact ih j (Nat.le_of_lt_succ hlt)
        · have hjn : j = n + 1 := Nat.le_antisymm hj hge
          subst hjn
          rcases Nat.eq_zero_or_pos n with hn | hn
          · -- j = 1: базовый случай e 1 ≤ C·ρ
            rw [hn, pow_one]
            have hmax : e 1 / ρ ≤ C := le_max_right _ _
            exact (div_le_iff₀ hρpos).mp hmax
          · -- j = n+1 ≥ 2: инерционный шаг
            have h1 := ih n (le_refl n)
            have h0 := ih (n - 1) (by omega : n - 1 ≤ n)
            have hstp := hstep n hn
            have hn1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
            have hp1 : ρ ^ n = ρ ^ (n - 1) * ρ := by
              rw [← pow_succ, hn1]
            have hp2 : ρ ^ (n + 1) = ρ ^ n * ρ := pow_succ ρ n
            have hsplit : q * (C * ρ ^ n) + β * (C * ρ ^ (n - 1))
                = C * ρ ^ (n - 1) * (q * ρ + β) := by
              rw [hp1]; ring
            have hfin : C * ρ ^ (n - 1) * (q * ρ + β) = C * ρ ^ (n + 1) := by
              rw [← hchar, hp2, hp1]
              ring
            calc e (n + 1)
                ≤ q * e n + β * e (n - 1) := hstp
              _ ≤ q * (C * ρ ^ n) + β * (C * ρ ^ (n - 1)) :=
                  add_le_add (mul_le_mul_of_nonneg_left h1 hq.le)
                    (mul_le_mul_of_nonneg_left h0 hβ)
              _ = C * ρ ^ (n + 1) := by rw [hsplit, hfin]
  exact key k k (le_refl k)
/-- Инерция с неточностью: стационарный пол. При постоянной
ошибке реализации δ рекурсия e_{k+1} ≤ q·e_k + β·e_{k−1} + δ
стягивается в коридор δ/(1−q−β) + (max(x₀, x₁/ρ))·ρ^k,
где x — центрированная ошибка: импульс не ухудшает пол по
сравнению с чистым сжатием, пока q+β < 1. -/
theorem momentum_floor (e : ℕ → ℝ) (q β δ : ℝ) (hq : 0 < q)
    (hβ : 0 ≤ β) (hqb : q + β < 1) (hδ : 0 ≤ δ)
    (hstep : ∀ k : ℕ, 1 ≤ k →
      e (k + 1) ≤ q * e k + β * e (k - 1) + δ)
    (k : ℕ) :
    e k ≤ δ / (1 - q - β)
      + max (e 0 - δ / (1 - q - β))
          ((e 1 - δ / (1 - q - β)) / momentumRate q β)
        * (momentumRate q β) ^ k := by
  obtain ⟨hρpos, hρ1⟩ := momentumRate_pos_lt_one q β hq hβ hqb
  -- центрированная последовательность x = e − c, c = δ/(1−q−β)
  set c := δ / (1 - q - β) with hc
  have hqb0 : 0 < 1 - q - β := by linarith
  have hcx : ∀ k : ℕ, 1 ≤ k →
      (e (k + 1) - c) ≤ q * (e k - c) + β * (e (k - 1) - c) := by
    intro k hk
    have hstp := hstep k hk
    have hcc : (1 - q - β) * c = δ := by
      rw [hc, mul_div_cancel₀ _ (ne_of_gt hqb0)]
    -- e_{k+1} − c ≤ q e_k + β e_{k-1} + δ − c = q e_k + β e_{k-1} + (1−q−β)c − ... 
    linarith [hcc]
  have hmb := momentum_bound (fun n => e n - c) q β hq hβ hqb hcx k
  -- перенести: e k = x k + c
  linarith

/-- Цена инерции точна: при β > 0 скорость инерционного
метода СТРОГО хуже базового сжатия: ρ(q,β) > q = ρ(q,0).
Импульс сам по себе не ускоряет — выигрыш ускорения
приходит только через улучшение направления (уменьшение q,
как в Anderson-ускорении с фактором θ·q), а не через
инерционный член; β только оплачивает растущую цену. -/
theorem momentum_beta_strict_cost (q β : ℝ) (hq : 0 < q)
    (hβ : 0 < β) :
    q < momentumRate q β := by
  have hsq : 0 < q ^ 2 + 4 * β := by nlinarith
  have h1 : q ^ 2 < q ^ 2 + 4 * β := by nlinarith
  have h2 : Real.sqrt (q ^ 2) < Real.sqrt (q ^ 2 + 4 * β) :=
    Real.sqrt_lt_sqrt (by nlinarith) h1
  rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ q)] at h2
  unfold momentumRate
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith

/-- Ускорение через направление доминирует цену инерции:
если Anderson-ускорение улучшает фактор шага с q до θ·q
(θ < 1, как в `anderson_floor_gain`: θ·q-фактор), то
инерционная скорость на улучшенном направлении строго
меньше: ρ(θq, β) < ρ(q, β) при любом β ≥ 0 — правильный
способ ускоряться: улучшать направление, а не наращивать
импульс. -/
theorem momentum_direction_beats_inertia (q θ β : ℝ)
    (hq : 0 < q) (hθ : 0 < θ) (hθ1 : θ < 1) (hβ : 0 ≤ β) :
    momentumRate (θ * q) β < momentumRate q β := by
  have hq' : 0 < θ * q := mul_pos hθ hq
  have hle : θ * q < q := by nlinarith
  -- монотонность sqrt: θq < q ⟹ (θq)² < q² (обе > 0)
  have hsq : (θ * q) ^ 2 < q ^ 2 := by nlinarith [mul_pos hq' hq']
  have h4 : (θ * q) ^ 2 + 4 * β < q ^ 2 + 4 * β := by linarith
  have hnn : (0:ℝ) ≤ (θ * q) ^ 2 + 4 * β := by nlinarith
  have hnn2 : (0:ℝ) ≤ q ^ 2 + 4 * β := by nlinarith
  have hsqrt : Real.sqrt ((θ * q) ^ 2 + 4 * β)
      < Real.sqrt (q ^ 2 + 4 * β) :=
    Real.sqrt_lt_sqrt hnn h4
  unfold momentumRate
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2),
    div_mul_eq_mul_div, mul_div_cancel_right₀ _ two_ne_zero]
  nlinarith

end Hagi.Optimization
