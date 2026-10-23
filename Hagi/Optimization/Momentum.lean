/-
Momentum: инерционные (heavy-ball) рекурсии ускорения.

Двухчленный закон ошибки e_{k+1} ≤ q·e_k + β·e_{k−1}:
геометрическое затухание со скоростью ρ = (q+√(q²+4β))/2 —
положительным корнем характеристического уравнения
ρ² = q·ρ + β. Импульс β не ломает сжатие при q+β < 1;
ρ → q при β → 0 — цена инерции точна и явна.
-/
import Hagi.Optimization.InexactContraction
import Hagi.Optimization.RobbinsMonro

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

/-- Достижимость качества при ускорении: любой целевой уровень
строго выше инерционного пола δ/(1−q−β) достигается за
конечное время и держится навсегда: ускоренный неточный
метод входит в коридор ширины ε над полом за геометрическое
время со скоростью ρ. -/
theorem momentum_achievability (e : ℕ → ℝ) (q β δ : ℝ) (hq : 0 < q)
    (hβ : 0 ≤ β) (hqb : q + β < 1) (hδ : 0 ≤ δ)
    (hstep : ∀ k : ℕ, 1 ≤ k →
      e (k + 1) ≤ q * e k + β * e (k - 1) + δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ s : ℕ, T ≤ s →
      e s ≤ δ / (1 - q - β) + ε := by
  obtain ⟨hρpos, hρ1⟩ := momentumRate_pos_lt_one q β hq hβ hqb
  have hbound := momentum_floor e q β δ hq hβ hqb hδ hstep
  set ρ := momentumRate q β with hρ
  set C := max (e 0 - δ / (1 - q - β))
      ((e 1 - δ / (1 - q - β)) / momentumRate q β) with hC
  by_cases hCn : C ≤ 0
  · -- C ≤ 0: C·ρ^s ≤ 0 ≤ ε — коридор уже достигнут
    refine ⟨0, fun s _ => ?_⟩
    have h1 := hbound s
    have h2 : C * ρ ^ s ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inr ⟨hCn, pow_nonneg hρpos.le s⟩)
    linarith
  · -- C > 0: ρ^s → 0, ждём C·ρ^s < ε
    have hCpos : 0 < C := by
      by_contra hc
      push_neg at hc
      linarith
    have htend : Filter.Tendsto (fun s => ρ ^ s) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hρpos.le hρ1
    have hev : ∀ᶠ s in Filter.atTop, C * ρ ^ s < ε := by
      have hmem : ∀ᶠ s in Filter.atTop, ρ ^ s < ε / C :=
        Filter.Tendsto.eventually htend (gt_mem_nhds (div_pos hε hCpos))
      refine hmem.mono fun s hs => ?_
      have := (lt_div_iff₀ hCpos).mp hs
      rw [mul_comm] at this
      exact this
    rw [Filter.eventually_atTop] at hev
    obtain ⟨T, hT⟩ := hev
    refine ⟨T, fun s hs => ?_⟩
    have h1 := hbound s
    have h2 : C * ρ ^ s < ε := hT s hs
    linarith

/-- Явный логарифмический горизонт входа: при C > 0 и
ρ < 1 существует T ≥ log(C/ε)/log(1/ρ) такое, что с шага T
ошибка инерционного метода навсегда в коридоре пол+ε:
время входа логарифмично по отношению требуемой точности к
геометрическому масштабу C/ε — скорость ускорения явна. -/
theorem momentum_entry_horizon (C ρ ε : ℝ) (hC : 0 < C)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε) :
    ∃ T : ℕ, Real.log (C / ε) / Real.log (1 / ρ) ≤ T
      ∧ ∀ s : ℕ, T ≤ s → ρ ^ s * C < ε := by
  have h1ρ : 0 < 1 / ρ := div_pos one_pos hρ0
  have hlog1ρ : 0 < Real.log (1 / ρ) :=
    Real.log_pos (one_lt_one_div hρ0 hρ1)
  -- ρ^s → 0: ждём ρ^s < ε/C
  have htend : Filter.Tendsto (fun s => ρ ^ s) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1
  have hpos : 0 < ε / C := div_pos hε hC
  have hev : ∀ᶠ s in Filter.atTop, ρ ^ s < ε / C :=
    Filter.Tendsto.eventually htend (gt_mem_nhds hpos)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨T, hT⟩ := hev
  refine ⟨T, ?_, fun s hs => ?_⟩
  · -- T ≥ log(C/ε)/log(1/ρ): из ρ^T < ε/C
    have hTT : ρ ^ T < ε / C := hT T (le_refl T)
    -- log: T·log(1/ρ) ≥ log(C/ε)
    have hlogT : Real.log (ρ ^ T) < Real.log (ε / C) :=
      Real.log_lt_log (pow_pos hρ0 T) hTT
    rw [Real.log_pow ρ T, Real.log_div (ne_of_gt hε) (ne_of_gt hC)] at hlogT
    -- T·log ρ < log ε − log C ⟺ T ≥ (log C − log ε)/log(1/ρ)
    rw [div_le_iff₀ hlog1ρ]
    -- hlogT: T·log ρ < log ε − log C; log ρ = −log(1/ρ)
    have hlinv : Real.log (1 / ρ) = -Real.log ρ := by
      rw [one_div, Real.log_inv ρ]
    rw [hlinv]
    have hge : Real.log (C / ε) = Real.log C - Real.log ε :=
      Real.log_div (ne_of_gt hC) (ne_of_gt hε)
    rw [hge]
    linarith
  · have h2 := hT s hs
    have h3 := (lt_div_iff₀ hC).mp h2
    linarith

/-- ПЕРЕКЛЮЧЕНИЕ В ТОЧНЫЙ РЕЖИМ (coarse-to-fine, фаза 2):
после момента T метод работает в точном режиме (q₂, β₂,
δ₂): дальнейшая ошибка следует инерционному закону НОВОГО
режима с начальными данными e T, e (T+1) — грубая фаза
задаёт стартовые данные, точная определяет пол и скорость
(композиция полов при смене точности). -/
theorem coarse_to_fine (e : ℕ → ℝ) (T : ℕ)
    (q₂ β₂ δ₂ : ℝ)
    (hq₂ : 0 < q₂) (hβ₂ : 0 ≤ β₂) (hqb₂ : q₂ + β₂ < 1)
    (hδ₂ : 0 ≤ δ₂)
    (hstep₂ : ∀ k : ℕ, T + 1 ≤ k →
      e (k + 1) ≤ q₂ * e k + β₂ * e (k - 1) + δ₂)
    (k : ℕ) :
    e (T + k) ≤ δ₂ / (1 - q₂ - β₂)
      + max (e T - δ₂ / (1 - q₂ - β₂))
          ((e (T + 1) - δ₂ / (1 - q₂ - β₂))
            / momentumRate q₂ β₂)
        * (momentumRate q₂ β₂) ^ k := by
  -- сдвинутая последовательность фазы 2
  set f : ℕ → ℝ := fun j => e (T + j) with hf
  have hfstep : ∀ j : ℕ, 1 ≤ j →
      f (j + 1) ≤ q₂ * f j + β₂ * f (j - 1) + δ₂ := by
    intro j hj
    have hstep := hstep₂ (T + j) (by omega)
    have h1 : T + j + 1 = T + (j + 1) := Nat.add_assoc T j 1
    have h2 : T + j - 1 = T + (j - 1) := by omega
    rw [h1, h2] at hstep
    simp only [f]
    exact hstep
  exact momentum_floor f q₂ β₂ δ₂ hq₂ hβ₂ hqb₂ hδ₂ hfstep k

/-- Грубая оценка — НИЖНЯЯ граница точной скорости:
q + β ≤ ρ(q,β) при 0 ≤ β, q + β ≤ 1 (доказательство:
ρ ≥ q+β ⟺ √(q²+4β) ≥ q+2β ⟺ β(1−q−β) ≥ 0). Характеристическая
скорость инерции всегда не дешевле грубой суммы: условие
q+β<1 из momentum_bound — не консервативная достаточность,
а точная граница устойчивости (ρ<1 ⟺ q+β<1). -/
theorem momentum_rate_ge (q β : ℝ) (hq : 0 < q) (hβ : 0 ≤ β)
    (hqb : q + β ≤ 1) :
    q + β ≤ momentumRate q β := by
  have hrhs : (0:ℝ) ≤ q + 2 * β := by nlinarith
  have hinner : (q + 2 * β) ^ 2 ≤ q ^ 2 + 4 * β := by
    nlinarith [hqb, hβ]
  have hsqrt : q + 2 * β ≤ Real.sqrt (q ^ 2 + 4 * β) := by
    have h1 : Real.sqrt ((q + 2 * β) ^ 2) ≤ Real.sqrt (q ^ 2 + 4 * β) :=
      Real.sqrt_le_sqrt hinner
    rwa [Real.sqrt_sq hrhs] at h1
  unfold momentumRate
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith

/-- КОМПОЗИЦИЯ ANDERSON × MOMENTUM: если ускорение
Anderson улучшает фактор шага с q до θ·q (θ<1) и добавлена
инерция β с неточностью δ, то ошибка следует инерционному
закону улучшенного режима: скорость ρ(θq,β), пол
δ/(1−θq−β) — полная граница ускоренного квантованного
метода: направление улучшает скорость, инерция её
оплачивает, неточность задаёт пол. -/
theorem anderson_momentum_compose (e : ℕ → ℝ)
    (θ q β δ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hq : 0 < q) (hβ : 0 ≤ β)
    (hqb : θ * q + β < 1) (hδ : 0 ≤ δ)
    (hstep : ∀ k : ℕ, 1 ≤ k →
      e (k + 1) ≤ θ * q * e k + β * e (k - 1) + δ)
    (k : ℕ) :
    e k ≤ δ / (1 - θ * q - β)
      + max (e 0 - δ / (1 - θ * q - β))
          ((e 1 - δ / (1 - θ * q - β)) / momentumRate (θ * q) β)
        * (momentumRate (θ * q) β) ^ k :=
  momentum_floor e (θ * q) β δ (mul_pos hθ hq) hβ hqb hδ hstep k

/-- Геометрическая сумма: Σ_{k<n} ρ^k = (1−ρⁿ)/(1−ρ) при ρ ≠ 1. -/
theorem geo_sum_eq (ρ : ℝ) (hρ : ρ ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, ρ ^ k = (1 - ρ ^ n) / (1 - ρ) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp
      ring

/-- СУММАРНАЯ ОШИБКА УСКОРЕННОГО МЕТОДА: геометрическое
затухание e_k ≤ C·ρ^k даёт конечный бюджет полной ошибки
Σ_{k<n} e_k ≤ C·(1−ρⁿ)/(1−ρ) ≤ C/(1−ρ): полная стоимость
ошибки на горизонте контролируется так же, как и поточечная. -/
theorem momentum_total_error (e : ℕ → ℝ) (q β : ℝ) (hq : 0 < q)
    (hβ : 0 ≤ β) (hqb : q + β < 1)
    (hstep : ∀ k : ℕ, 1 ≤ k →
      e (k + 1) ≤ q * e k + β * e (k - 1))
    (C : ℝ) (hC : 0 ≤ C)
    (hbnd : ∀ k, e k ≤ C * (momentumRate q β) ^ k)
    (n : ℕ) :
    ∑ k ∈ Finset.range n, e k
      ≤ C * (1 - (momentumRate q β) ^ n)
        / (1 - momentumRate q β) := by
  obtain ⟨hρpos, hρ1⟩ := momentumRate_pos_lt_one q β hq hβ hqb
  set ρ := momentumRate q β with hρ
  have hne : ρ ≠ 1 := ne_of_lt hρ1
  have hsplit : ∑ k ∈ Finset.range n, e k
      ≤ ∑ k ∈ Finset.range n, C * ρ ^ k :=
    Finset.sum_le_sum fun k _ => hbnd k
  have hgeo : ∑ k ∈ Finset.range n, C * ρ ^ k
      = C * (1 - ρ ^ n) / (1 - ρ) := by
    rw [← Finset.mul_sum, geo_sum_eq ρ hne n]
    ring
  rw [hgeo] at hsplit
  exact hsplit

/-- Базовая скорость: без импульса ρ(q,0) = q — чистый
градиентный закон сжатия. -/
theorem momentumRate_zero_beta (q : ℝ) (hq : 0 ≤ q) :
    momentumRate q 0 = q := by
  unfold momentumRate
  norm_num
  rw [Real.sqrt_sq hq]
  have : (q + q) / 2 = q := by ring
  rw [this]

/-- ОПТИМУМ ИМПУЛЬСА В АБСТРАКТНОЙ МОДЕЛИ: при фиксированном
базовом факторе q чистый градиент (β=0) строго быстрее
любого β>0: ρ(q,0) = q < ρ(q,β) — в рамках закона ошибки
e_{k+1} ≤ q·e_k + β·e_{k−1} импульс НЕ ускоряет (ускорение
Нестерова работает через КОРРЕКЦИЮ направления, а не через
добавку к фактору ошибки). -/
theorem momentum_optimal_beta (q β : ℝ) (hq : 0 < q)
    (hβ : 0 < β) :
    momentumRate q 0 < momentumRate q β := by
  rw [momentumRate_zero_beta q hq.le]
  exact momentum_beta_strict_cost q β hq hβ

/-- КОРРЕКЦИЯ НЕСТЕРОВА: look-ahead импульс с поправкой —
закон e_{k+1} + β·(e_{k+1} − e_k) ≤ q·e_k — даёт эффективный
фактор (q+β)/(1+β): поправка гасит нарастание инерции, и при
q < 1 метод сходится геометрически с этим фактором. Это
механизм истинного ускорения: не добавка импульса к фактору,
а деление на (1+β). -/
theorem nesterov_corrected (e : ℕ → ℝ) (q β : ℝ) (hq : 0 < q)
    (hq1 : q < 1) (hβ : 0 < β)
    (hstep : ∀ k : ℕ,
      e (k + 1) + β * (e (k + 1) - e k) ≤ q * e k)
    (k : ℕ) :
    e k ≤ ((q + β) / (1 + β)) ^ k * e 0 := by
  have hq'0 : 0 < (q + β) / (1 + β) := by
    positivity
  have hq'1 : (q + β) / (1 + β) < 1 := by
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < 1 + β)]
    nlinarith
  have hstep' : ∀ j : ℕ,
      e (j + 1) ≤ ((q + β) / (1 + β)) * e j := by
    intro j
    have h := hstep j
    have hkey : (1 + β) * e (j + 1) ≤ (q + β) * e j := by
      nlinarith [h]
    have hconv : ((q + β) / (1 + β)) * e j
        = (q + β) * e j / (1 + β) := by
      field_simp
    rw [hconv]
    exact (le_div_iff₀' (by linarith : (0:ℝ) < 1 + β)).mpr hkey
  have hstep'' : ∀ j : ℕ,
      e (j + 1) ≤ ((q + β) / (1 + β)) * e j + 0 := by
    intro j
    have := hstep' j
    linarith
  have h := inexact_contraction_bound e ((q + β) / (1 + β)) 0
    hq'0 hq'1 (le_refl 0) hstep'' k
  simpa using h

/-- ДОМИНИРОВАНИЕ КОРЕКЦИИ: эффективный фактор Нестерова
(q+β)/(1+β) СТРОГО меньше характеристической скорости сырого
импульса ρ(q,β) при β > 0, q+β ≤ 1: коррекция направления —
единственный честный механизм ускорения (сырой импульс лишь
дороже: ρ ≥ q+β). -/
theorem nesterov_beats_plain (q β : ℝ) (hq : 0 < q)
    (hβ : 0 < β) (hqb : q + β ≤ 1) :
    (q + β) / (1 + β) < momentumRate q β := by
  have hge : q + β ≤ momentumRate q β :=
    momentum_rate_ge q β hq hβ.le hqb
  have hlt : (q + β) / (1 + β) < q + β := by
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < 1 + β)]
    nlinarith
  linarith

/-- МОНОТОННОСТЬ ФАКТОРА НЕСТЕРОВА: скорректированный фактор
(q+β)/(1+β) возрастает по β при q < 1 (разность
(1−q)(β₂−β₁)/((1+β₁)(1+β₂)) > 0): и в скорректированном
законе оптимальный импульс — нулевой. Итоговый вывод модуля
ускорения: в абстрактных законах ошибки инерция НИКОГДА не
помогает — ускорение достигается только улучшением
направления (Anderson θ·q), а импульс есть цена, которую
минимизируют. -/
theorem nesterov_factor_monotone (q β₁ β₂ : ℝ) (hq : q < 1)
    (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hβ : β₁ ≤ β₂) :
    (q + β₁) / (1 + β₁) ≤ (q + β₂) / (1 + β₂) := by
  have hp1 : (0:ℝ) < 1 + β₁ := by linarith
  have hp2 : (0:ℝ) < 1 + β₂ := by linarith
  rw [div_le_div_iff₀ hp1 hp2]
  -- (q+β₁)(1+β₂) ≤ (q+β₂)(1+β₁) ⟺ β₂−β₁ ≥ ... раскрыть
  nlinarith

/-- ПОЛ НЕТОЧНОЙ КОРРЕКЦИИ НЕСТЕРОВА: закон
e_{k+1} + β·(e_{k+1} − e_k) ≤ q·e_k + δ даёт сжатие с
фактором (q+β)/(1+β) и СТАЦИОНАРНЫЙ ПОЛ δ/(1−q): инерция
улучшает только переходную скорость, но НЕ пол — пол
неточности определяется базовым q; коррекция бесплатна для
качества, платит только скоростью входа. -/
theorem nesterov_floor (e : ℕ → ℝ) (q β δ : ℝ) (hq : 0 < q)
    (hq1 : q < 1) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hstep : ∀ k : ℕ,
      e (k + 1) + β * (e (k + 1) - e k) ≤ q * e k + δ)
    (k : ℕ) :
    e k ≤ ((q + β) / (1 + β)) ^ k * e 0 + δ / (1 - q) := by
  have hq'0 : 0 < (q + β) / (1 + β) := by positivity
  have hq'1 : (q + β) / (1 + β) < 1 := by
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < 1 + β)]
    nlinarith
  -- редукция: e_{k+1} ≤ q'·e_k + δ/(1+β)
  have hstep' : ∀ j : ℕ,
      e (j + 1)
        ≤ ((q + β) / (1 + β)) * e j + δ / (1 + β) := by
    intro j
    have h := hstep j
    have hkey : (1 + β) * e (j + 1) ≤ (q + β) * e j + δ := by
      nlinarith [h]
    have hconv : ((q + β) / (1 + β)) * e j + δ / (1 + β)
        = ((q + β) * e j + δ) / (1 + β) := by
      field_simp
    rw [hconv]
    exact (le_div_iff₀' (by linarith : (0:ℝ) < 1 + β)).mpr hkey
  -- сжатие с полом δ/(1+β) при факторе q'
  have h := Hagi.Optimization.inexact_contraction_floor e
    ((q + β) / (1 + β)) (δ / (1 + β)) hq'0 hq'1
    (div_nonneg hδ (by linarith)) hstep' k
  -- δ/(1+β) / (1−q') = δ/(1−q)
  have hfloor : (δ / (1 + β)) / (1 - (q + β) / (1 + β))
      = δ / (1 - q) := by
    have hdenom : 1 - (q + β) / (1 + β)
        = (1 - q) / (1 + β) := by
      field_simp
      ring
    rw [hdenom, div_div_eq_mul_div, div_mul_cancel₀ _ (by
      linarith : ((1:ℝ) + β) ≠ 0)]
  rw [hfloor] at h
  exact h

/-- ANDERSON × НЕСТЕРОВ: Anderson улучшает базовый фактор с
q до θ·q, коррекция Нестерова делит на (1+β): итоговый
фактор (θq+β)/(1+β), пол неточности δ/(1−θq) — полная
граница ускоренного квантованного метода с коррекцией:
улучшение направления (θ) ускоряет и переходный процесс, и
уменьшает пол; инерция (β) платит только за скорость. -/
theorem nesterov_anderson (e : ℕ → ℝ) (θ q β δ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) (hq1 : q < 1)
    (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hstep : ∀ k : ℕ,
      e (k + 1) + β * (e (k + 1) - e k)
        ≤ θ * q * e k + δ)
    (k : ℕ) :
    e k ≤ ((θ * q + β) / (1 + β)) ^ k * e 0
      + δ / (1 - θ * q) :=
  nesterov_floor e (θ * q) β δ (mul_pos hθ hq)
    (by nlinarith) hβ hδ hstep k

/-- ДОСТИЖИМОСТЬ ПРИ КОРРЕКЦИИ НЕСТЕРОВА: любой целевой
уровень строго выше пола δ/(1−q) достигается за конечное
время и держится навсегда: скорректированный ускоренный
метод входит в коридор над полом геометрически с фактором
(q+β)/(1+β). -/
theorem nesterov_achievability (e : ℕ → ℝ) (q β δ : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hstep : ∀ k : ℕ,
      e (k + 1) + β * (e (k + 1) - e k) ≤ q * e k + δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ s : ℕ, T ≤ s →
      e s ≤ δ / (1 - q) + ε := by
  have hq'0 : 0 < (q + β) / (1 + β) := by positivity
  have hq'1 : (q + β) / (1 + β) < 1 := by
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < 1 + β)]
    nlinarith
  set q' := (q + β) / (1 + β) with hq'
  have hbnd := nesterov_floor e q β δ hq hq1 hβ hδ hstep
  -- геометрический член q'^s·e0 → 0: ждём q'^s·|e0| < ε
  have habs : (0:ℝ) ≤ |e 0| := abs_nonneg _
  by_cases he0 : e 0 ≤ 0
  · -- e0 ≤ 0: q'^s·e0 ≤ 0 ≤ ε всегда
    refine ⟨0, fun s _ => ?_⟩
    have h1 := hbnd s
    have h2 : q' ^ s * e 0 ≤ 0 := by
      nlinarith [pow_nonneg hq'0.le s, he0]
    linarith
  · have hpos : 0 < e 0 := by
      by_contra hc
      push_neg at hc
      exact he0 hc
    have htend : Filter.Tendsto (fun s => q' ^ s) Filter.atTop
        (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq'0.le hq'1
    have hev : ∀ᶠ s in Filter.atTop, q' ^ s * e 0 < ε := by
      have hmem : ∀ᶠ s in Filter.atTop, q' ^ s < ε / e 0 :=
        Filter.Tendsto.eventually htend
          (gt_mem_nhds (div_pos hε hpos))
      refine hmem.mono fun s hs => ?_
      have h3 := (lt_div_iff₀ hpos).mp hs
      rw [mul_comm] at h3
      rw [mul_comm]
      exact h3
    rw [Filter.eventually_atTop] at hev
    obtain ⟨T, hT⟩ := hev
    refine ⟨T, fun s hs => ?_⟩
    have h1 := hbnd s
    have h2 : q' ^ s * e 0 < ε := hT s hs
    linarith

/-- ЯВНЫЙ ГОРИЗОНТ ВХОДА ДЛЯ КОРРЕКЦИИ НЕСТЕРОВА: при e₀ > 0
существует T ≥ log(e₀/ε)/log((1+β)/(q+β)) такой, что с шага T
ошибка навсегда ≤ пол + ε: время входа логарифмично,
основание логарифма — обратный эффективный фактор
(1+β)/(q+β) > 1: ускорение коррекции выражается в явном
числе шагов. -/
theorem nesterov_entry_horizon (e : ℕ → ℝ) (q β δ : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hstep : ∀ k : ℕ,
      e (k + 1) + β * (e (k + 1) - e k) ≤ q * e k + δ)
    (ε : ℝ) (hε : 0 < ε) (he0 : 0 < e 0) :
    ∃ T : ℕ, Real.log (e 0 / ε)
        / Real.log ((1 + β) / (q + β)) ≤ T
      ∧ ∀ s : ℕ, T ≤ s → e s ≤ δ / (1 - q) + ε := by
  have hq'0 : 0 < (q + β) / (1 + β) := by positivity
  have hq'1 : (q + β) / (1 + β) < 1 := by
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < 1 + β)]
    nlinarith
  set q' := (q + β) / (1 + β) with hq'
  have hinvq : 1 / q' = (1 + β) / (q + β) := by
    rw [one_div, inv_div]
  have hbnd := nesterov_floor e q β δ hq hq1 hβ hδ hstep
  -- фильтр-ожидание q'^s·e0 < ε
  have htend : Filter.Tendsto (fun s => q' ^ s) Filter.atTop
      (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq'0.le hq'1
  have hmem : ∀ᶠ s in Filter.atTop, q' ^ s < ε / e 0 :=
    Filter.Tendsto.eventually htend (gt_mem_nhds (div_pos hε he0))
  have hev : ∀ᶠ s in Filter.atTop, q' ^ s * e 0 < ε :=
    hmem.mono fun s hs => by
      have h3 := (lt_div_iff₀ he0).mp hs
      rw [mul_comm] at h3
      rw [mul_comm]
      exact h3
  rw [Filter.eventually_atTop] at hev
  obtain ⟨T, hT⟩ := hev
  refine ⟨T, ?_, fun s hs => ?_⟩
  · -- T ≥ log(e0/ε)/log((1+β)/(q+β)) = log(e0/ε)/log(1/q')
    have hTT : q' ^ T * e 0 < ε := hT T (le_refl T)
    have hlogT : Real.log (q' ^ T * e 0) < Real.log ε :=
      Real.log_lt_log (mul_pos (pow_pos hq'0 T) he0) hTT
    rw [Real.log_mul (ne_of_gt (pow_pos hq'0 T)) (ne_of_gt he0),
      Real.log_pow q' T] at hlogT
    -- log q' = −log(1/q') = −log((1+β)/(q+β))
    have hL : 0 < Real.log (1 / q') :=
      Real.log_pos (one_lt_one_div hq'0 hq'1)
    have hlinv : Real.log q' = -Real.log (1 / q') := by
      rw [one_div, Real.log_inv q']
      norm_num
    rw [hlinv] at hlogT
    have hLL : Real.log (1 / q') = Real.log ((1 + β) / (q + β)) :=
      congrArg Real.log (by
        rw [hq', one_div, inv_div])
    rw [hLL] at hlogT
    -- цель: log(e0/ε) ≤ T·log((1+β)/(q+β))
    have hinvq : 1 / q' = (1 + β) / (q + β) := by
      rw [hq', one_div, inv_div]
    -- переименовать hL в терминах (1+β)/(q+β)
    have hL' : 0 < Real.log ((1 + β) / (q + β)) := hinvq ▸ hL
    have hge : Real.log (e 0 / ε) = Real.log (e 0) - Real.log ε :=
      Real.log_div (ne_of_gt he0) (ne_of_gt hε)
    rw [hge, div_le_iff₀ hL']
    linarith
  · have h1 := hbnd s
    have h2 : q' ^ s * e 0 < ε := hT s hs
    linarith

/-- СУММАРНАЯ ОШИБКА КОРРЕКЦИИ НЕСТЕРОВА: геометрическое
затухание с фактором (q+β)/(1+β) даёт конечный бюджет
полной ошибки: Σ_{k<n} e_k ≤ геометрическая сумма
переходной части + n·пол: полная стоимость ошибок
ускоренного метода контролируется явно. -/
theorem nesterov_total_error (e : ℕ → ℝ) (q β δ : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hstep : ∀ k : ℕ,
      e (k + 1) + β * (e (k + 1) - e k) ≤ q * e k + δ)
    (n : ℕ) :
    ∑ k ∈ Finset.range n, e k
      ≤ e 0 * (1 - ((q + β) / (1 + β)) ^ n)
          / (1 - (q + β) / (1 + β))
        + (n : ℝ) * (δ / (1 - q)) := by
  have hq'0 : 0 < (q + β) / (1 + β) := by positivity
  have hq'1 : (q + β) / (1 + β) < 1 := by
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < 1 + β)]
    nlinarith
  set q' := (q + β) / (1 + β) with hq'
  have hbnd := nesterov_floor e q β δ hq hq1 hβ hδ hstep
  -- сумма поточечных границ
  have hsplit : ∑ k ∈ Finset.range n, e k
      ≤ ∑ k ∈ Finset.range n,
          (q' ^ k * e 0 + δ / (1 - q)) :=
    Finset.sum_le_sum fun k _ => hbnd k
  -- разложение суммы: геометрия + n·пол
  have hgeo : ∑ k ∈ Finset.range n, (q' ^ k * e 0 + δ / (1 - q))
      = ∑ k ∈ Finset.range n, q' ^ k * e 0
        + ∑ k ∈ Finset.range n, (δ / (1 - q)) := by
    rw [← Finset.sum_add_distrib]
  rw [hgeo] at hsplit
  -- геометрическая часть
  have hgeopart : ∑ k ∈ Finset.range n, q' ^ k * e 0
      = e 0 * (1 - q' ^ n) / (1 - q') := by
    rw [← Finset.sum_mul, geo_sum_eq q' (ne_of_lt hq'1) n]
    ring
  -- полная часть
  have hconst : ∑ k ∈ Finset.range n, (δ / (1 - q))
      = (n : ℝ) * (δ / (1 - q)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hgeopart, hconst] at hsplit
  exact hsplit

/-- СКОБКА ШАГА ЛИНЕЙНОГО ПОИСКА: если условие приёма шага
анти-монотонно по шагу (меньшие шаги принимаются чаще: знак
Armijo/honesty), шаг s принят, а 2s отвергнут, то порог
приёма локализован в [s, 2s): всё ≤ s принимается, всё ≥ 2s
отвергается — одна двойка неопределённости; бисекция
делит её пополам за шаг (log₂ диапазона до фактора 2). -/
theorem step_bracket {P : ℝ → Prop}
    (hmono : ∀ a b, a ≤ b → P b → P a)
    (s : ℝ) (h1 : P s) (h2 : ¬ P (2 * s)) :
    (∀ t, t ≤ s → P t) ∧ (∀ t, 2 * s ≤ t → ¬ P t) := by
  refine ⟨fun t ht => hmono t s ht h1, fun t ht => ?_⟩
  intro hP
  exact h2 (hmono (2 * s) t ht hP)

/-- БИСЕКЦИЯ ДЕЛИТ СКОБКУ: при скобке [lo, hi] с принятым lo
и отвергнутым hi проверка середины оставляет скобку вдвое
короче: либо [mid, hi] (mid принят), либо [lo, mid] (mid
отвергнут) — линейный поиск локализует оптимальный шаг с
экспоненциальной скоростью. -/
theorem bracket_bisect {P : ℝ → Prop}
    (hmono : ∀ a b, a ≤ b → P b → P a)
    (lo hi mid : ℝ) (hlo : P lo) (hhi : ¬ P hi)
    (hmid1 : lo ≤ mid) (hmid2 : mid ≤ hi) :
    (P mid ∧ ¬ P hi ∧ mid ≤ hi ∧ lo ≤ mid)
      ∨ (P lo ∧ ¬ P mid ∧ lo ≤ mid ∧ mid ≤ hi) := by
  by_cases h : P mid
  · left
    exact ⟨h, hhi, hmid2, hmid1⟩
  · right
    exact ⟨hlo, h, hmid1, hmid2⟩

/-- ВРЕМЯ ВХОДА ANDERSON × НЕСТЕРОВ: полная композиция —
фактор (θq+β)/(1+β), пол δ/(1−θq), время входа в коридор
ε над полом: T ≥ log(e₀/ε)/log((1+β)/(θq+β)): улучшение
направления θ ускоряет и фактор, и пол, и время входа;
инерция β оплачивает только переходный процесс. -/
theorem nesterov_anderson_entry (e : ℕ → ℝ) (θ q β δ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) (hq1 : q < 1)
    (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hstep : ∀ k : ℕ,
      e (k + 1) + β * (e (k + 1) - e k) ≤ θ * q * e k + δ)
    (ε : ℝ) (hε : 0 < ε) (he0 : 0 < e 0) :
    ∃ T : ℕ, Real.log (e 0 / ε)
        / Real.log ((1 + β) / (θ * q + β)) ≤ T
      ∧ ∀ s : ℕ, T ≤ s → e s ≤ δ / (1 - θ * q) + ε :=
  nesterov_entry_horizon e (θ * q) β δ (mul_pos hθ hq)
    (by nlinarith) hβ hδ hstep ε hε he0

/-- КОРРЕКЦИЯ УЛУЧШАЕТ И ПОЛ: стационарный пол
скорректированного метода δ/(1−q) не выше пола сырого
импульса δ/(1−q−β): коррекция Нестерова доминирует сырой
heavy-ball по ОБЕИМ осям — и по скорости
(nesterov_beats_plain), и по полу неточности. -/
theorem nesterov_floor_beats_plain (δ q β : ℝ) (hδ : 0 ≤ δ)
    (hβ : 0 ≤ β) (hqb : q + β < 1) :
    δ / (1 - q) ≤ δ / (1 - q - β) := by
  have h1 : (0:ℝ) < 1 - q - β := by linarith
  have h2 : (0:ℝ) < 1 - q := by linarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith [hδ]

/-- ПОЛНАЯ СТОИМОСТЬ ДВУХФАЗНОЙ СТРАТЕГИИ: суммарная ошибка
coarse-to-fine = грубая фаза (измеренная сумма ≤ B₁ до
момента T) + точная фаза (нестеровская геометрия + пол):
Σ_{k<T+n} e_k ≤ B₁ + e_T·(1−q'ⁿ)/(1−q') + n·δ/(1−q) —
полный бюджет ошибок двухфазного ускоренного метода
складывается из измеренной грубой части и сертифицированной
точной части. -/
theorem two_phase_total (e : ℕ → ℝ) (T : ℕ) (B₁ q β δ : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hcoarse : ∑ k ∈ Finset.range T, e k ≤ B₁)
    (hstep₂ : ∀ k : ℕ,
      e (T + k + 1)
        + β * (e (T + k + 1) - e (T + k)) ≤ q * e (T + k) + δ)
    (n : ℕ) :
    ∑ k ∈ Finset.range (T + n), e k
      ≤ B₁ + e T * (1 - ((q + β) / (1 + β)) ^ n)
          / (1 - (q + β) / (1 + β))
        + (n : ℝ) * (δ / (1 - q)) := by
  -- разбиение суммы: [0,T) + [T, T+n)
  have hsplit : ∑ k ∈ Finset.range (T + n), e k
      = ∑ k ∈ Finset.range T, e k
        + ∑ k ∈ Finset.range n, e (T + k) := by
    rw [Finset.sum_range_add]
  -- точная фаза: сдвинутая последовательность
  set f : ℕ → ℝ := fun k => e (T + k) with hf
  have hflaw : ∀ k : ℕ,
      f (k + 1) + β * (f (k + 1) - f k) ≤ q * f k + δ := by
    intro k
    have : T + (k + 1) = T + k + 1 := by ring
    simpa [f, this] using hstep₂ k
  have hfine := nesterov_total_error f q β δ hq hq1 hβ hδ hflaw n
  simp only [f, Nat.add_zero] at hfine
  rw [hsplit]
  simp only [hf]
  linarith [hcoarse, hfine]

/-- ЗАТУХАЮЩЕЕ РАСПИСАНИЕ ИМПУЛЬСА: если ошибки неотрицательны
и инерционный коэффициент расписания β_k ограничен константой
bbar с q + bbar < 1, то ошибка затухает геометрически со
скоростью ρ(q, bbar): расписание импульса (в т.ч. затухающее
к нулю) безопасно при равномерном бюджете инерции. -/
theorem momentum_schedule (e : ℕ → ℝ) (q : ℝ) (β : ℕ → ℝ)
    (bbar : ℝ) (hq : 0 < q) (hb0 : 0 ≤ bbar)
    (hqb : q + bbar < 1)
    (he : ∀ k, 0 ≤ e k)
    (hβle : ∀ k, β k ≤ bbar)
    (hstep : ∀ k : ℕ, 1 ≤ k →
      e (k + 1) ≤ q * e k + β k * e (k - 1))
    (k : ℕ) :
    e k ≤ max (e 0) (e 1 / momentumRate q bbar)
      * (momentumRate q bbar) ^ k := by
  have hb0' : (0:ℝ) ≤ bbar := hb0
  have hstep' : ∀ j : ℕ, 1 ≤ j →
      e (j + 1) ≤ q * e j + bbar * e (j - 1) := by
    intro j hj
    have h := hstep j hj
    have hb := hβle j
    have hmono : β j * e (j - 1) ≤ bbar * e (j - 1) :=
      mul_le_mul_of_nonneg_right hb (he (j - 1))
    linarith
  exact momentum_bound e q bbar hq hb0' hqb hstep' k

/-- НУЛЕВАЯ ИНЕРЦИЯ КАК ОПТИМАЛЬНАЯ СТРАТЕГИЯ: при β = 0
скорректированный закон вырождается в чистое сжатие с
фактором θ·q и полом δ/(1−θq) — в сочетании с тезисом модуля
(импульс лишь платит, направление ускоряет) и бисекцией
шага оптимальная конфигурация ускоренного метода:
Anderson-направление (θ) + нулевая инерция (β=0) +
line-search-шаг из скобки. -/
theorem zero_inertia_optimal (e : ℕ → ℝ) (θ q δ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) (hq1 : q < 1)
    (hδ : 0 ≤ δ)
    (hstep : ∀ k : ℕ, e (k + 1) ≤ θ * q * e k + δ)
    (k : ℕ) :
    e k ≤ (θ * q) ^ k * e 0 + δ / (1 - θ * q) :=
  Hagi.Optimization.inexact_contraction_floor e (θ * q) δ
    (mul_pos hθ hq) (by nlinarith [hθ, hθ1, hq]) hδ hstep k

/-- ДОСТИЖИМОСТЬ ANDERSON × MOMENTUM: для ускоренной
неточной инерционной рекурсии (фактор θ·q, импульс β,
неточность δ) любая цель выше пола δ/(1−θq−β) достигается
за конечное геометрическое время со скоростью ρ(θq,β) —
параллель к nesterov_anderson_entry для сырого импульса. -/
theorem anderson_momentum_reach (e : ℕ → ℝ) (θ q β δ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) (hq1 : q < 1)
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (hqb : θ * q + β < 1)
    (hstep : ∀ k : ℕ, 1 ≤ k →
      e (k + 1) ≤ θ * q * e k + β * e (k - 1) + δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ s : ℕ, T ≤ s →
      e s ≤ δ / (1 - θ * q - β) + ε :=
  Hagi.Optimization.momentum_achievability e (θ * q) β δ
    (mul_pos hθ hq) hβ hqb hδ hstep ε hε


