/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.AdaptiveSuccess
set_option linter.style.header false

/-!
# P0-4 / теорема E аудита — Azuma для истории-зависимых успехов

Аудит (§12, теорема E): `AdaptiveSuccess` требует
fresh-randomness-per-cycle (итог цикла — функция только ω_t).
Настоящий self-improvement loop зависит от ВСЕЙ истории:
S_t = f(ω_0..ω_{t-1}, ω_t). Формализуем мартингальную версию.

**Модель**: приращения X_{t+1}: (Fin t → V) → ℝ — функции
ПРЕФИКСА (история + свежая случайность), условно
центрированные при каждом префиксе:

  Σ_v q(v)·X_{t+1}(snoc pref v) = 0,  |X| ≤ c.

**Теоремы:**

* `hoeffding_lemma_prefix` — условная лемма Хёфдинга для
  среднего-ноль [−c,c]-величин: Σ q e^{λx} ≤ e^{λ²c²/2}
  (хорда exp + log_cosh_le).
* `prodE_snoc` — декомпозиция prodE по последней координате
  (башня ожиданий в конечной форме).
* `azuma_mgf` — мартингальный mgf: E[e^{λ Σ X}] ≤ e^{nλ²c²/2}
  индукцией по n (условная лемма + snoc-декомпозиция).
* azuma_tail_low — двусторонний хвост: P[|ΣX| ≥ Δ] ≤
  2·exp(−Δ²/(2nc²)) (оптимизация λ = Δ/(nc), Markov).
* `adaptive_success_azuma` — история-зависимые успехи:
  S_{t+1}(префикс) ∈ [0,1], условные полы
  Σ_v q(v)·S_{t+1}(snoc pref v) ≥ p₀ ⇒ ΣS ≥ n·p₀ − Δ
  с вероятностью ≥ 1 − exp(−Δ²/(2n)). Согласовано с
  concDelta-заметкой: масштаб √(2n·log(1/δ)).

**Честные границы**: полы должны проверяться при КАЖДОМ
префиксе (это runtime-измерение, не следствие iid);
суб-Гауссовость приращений — следствие ограниченности [0,1],
Freedman-усиление (дисперсионная адаптация) — открыто.
-/

open Finset Real

namespace Hagi
open Hagi.Foundations

variable {V : Type} [Fintype V] [Nonempty V]

/-! ## Условная лемма Хёфдинга -/

/-- **Условная лемма Хёфдинга**: для взвешенного среднего-нуля
величин в [−c,c] mgf ограничен e^{λ²c²/2} (хорда exp на
[−c,c] + log_cosh_le). -/
theorem hoeffding_lemma_prefix (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (X : V → ℝ) (c : ℝ) (hc : 0 < c)
    (hb : ∀ v, -c ≤ X v ∧ X v ≤ c)
    (hmean : ∑ v, q v * X v = 0) (lam : ℝ) :
    ∑ v, q v * Real.exp (lam * X v)
      ≤ Real.exp (lam ^ 2 * c ^ 2 / 2) := by
  rcases eq_or_ne lam 0 with hlam | hlam
  · rw [hlam]
    simp [hq1]
  have hA : 0 < |lam| * c := mul_pos (abs_pos.mpr hlam) hc
  set A := |lam| * c with hAdef
  -- хорда exp на [−A, A]
  have hchord : ∀ v, Real.exp (lam * X v)
      ≤ (A - lam * X v) / (2 * A) * Real.exp (-A)
        + (lam * X v + A) / (2 * A) * Real.exp A := by
    intro v
    have hbx : |lam * X v| ≤ A := by
      rw [abs_mul, hAdef]
      exact mul_le_mul_of_nonneg_left
        (abs_le.mpr ⟨(hb v).1, (hb v).2⟩) (abs_nonneg lam)
    obtain ⟨hm, hp⟩ := abs_le.mp hbx
    have hne : (-A : ℝ) < A := by linarith
    have hch := exp_chord_ab (-A) A (lam * X v) hne (by linarith) (by linarith)
    have hden : A - (-A : ℝ) = 2 * A := by ring
    rw [hden] at hch
    have hxa : lam * X v - (-A : ℝ) = lam * X v + A := by ring
    rw [hxa] at hch
    exact hch
  -- суммирование с весами
  have hsum : ∑ v, q v * Real.exp (lam * X v)
      ≤ ∑ v, q v * ((A - lam * X v) / (2 * A) * Real.exp (-A)
        + (lam * X v + A) / (2 * A) * Real.exp A) :=
    Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hchord v) (hq0 v)
  -- веса: среднее-ноль убирает асимметрию, остаётся cosh A
  have hS1 : ∑ v, q v * (A - lam * X v) = A := by
    have hrw : ∀ v, q v * (A - lam * X v)
        = A * q v - lam * (q v * X v) := fun v => by ring
    simp only [hrw]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hq1, hmean]
    norm_num
  have hS2 : ∑ v, q v * (lam * X v + A) = A := by
    have hrw : ∀ v, q v * (lam * X v + A)
        = lam * (q v * X v) + A * q v := fun v => by ring
    simp only [hrw]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hq1, hmean]
    norm_num
  -- раскрытие суммы произведений
  have hfinal : ∑ v, q v * ((A - lam * X v) / (2 * A) * Real.exp (-A)
        + (lam * X v + A) / (2 * A) * Real.exp A)
      = Real.cosh A := by
    have hsplit : ∀ v, q v * ((A - lam * X v) / (2 * A) * Real.exp (-A)
        + (lam * X v + A) / (2 * A) * Real.exp A)
        = Real.exp (-A) * q v * (A - lam * X v) / (2 * A)
          + Real.exp A * q v * (lam * X v + A) / (2 * A) := by
      intro v
      ring
    rw [Finset.sum_congr rfl (fun v _ => hsplit v), Finset.sum_add_distrib]
    rw [← Finset.sum_div, ← Finset.sum_div]
    have hc1 : ∑ i, Real.exp (-A) * q i * (A - lam * X i)
        = Real.exp (-A) * A := by
      have hrw : ∀ i, Real.exp (-A) * q i * (A - lam * X i)
          = Real.exp (-A) * (q i * (A - lam * X i)) := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hrw i), ← Finset.mul_sum, hS1]
    have hc2 : ∑ i, Real.exp A * q i * (lam * X i + A)
        = Real.exp A * A := by
      have hrw : ∀ i, Real.exp A * q i * (lam * X i + A)
          = Real.exp A * (q i * (lam * X i + A)) := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hrw i), ← Finset.mul_sum, hS2]
    rw [hc1, hc2]
    rw [Real.cosh_eq]
    field_simp
    ring
  have hAsq : A ^ 2 = lam ^ 2 * c ^ 2 := by
    rw [hAdef, mul_pow]
    rw [show |lam| ^ 2 = lam ^ 2 by rw [pow_two, abs_mul_abs_self, ← pow_two]]
  rw [hfinal] at hsum
  refine le_trans hsum ?_
  have h1 : Real.cosh A ≤ Real.exp (A ^ 2 / 2) := by
    have h2 := Real.exp_le_exp.mpr (log_cosh_le A)
    rwa [Real.exp_log (Real.cosh_pos A)] at h2
  rw [← hAsq]
  exact h1

/-! ## Snoc-декомпозиция произведения -/

/-- **Башня ожиданий, конечная форма**: prodE по n+1 координате =
Σ по префиксам × Σ по последней координате
(через `Fin.snocEquiv` Mathlib). -/
theorem prodE_snoc {n : ℕ} (p : Fin (n + 1) → V → ℝ)
    (F : (Fin (n + 1) → V) → ℝ) :
    prodE p F
      = ∑ pref : Fin n → V, (∏ i, p i.castSucc (pref i))
        * ∑ x, p (Fin.last n) x * F (Fin.snoc (α := fun _ => V) pref x) := by
  classical
  have hpair : ∀ pref : Fin n → V, ∀ x : V,
      (∏ i, p i (Fin.snoc (α := fun _ => V) pref x i))
        * F (Fin.snoc (α := fun _ => V) pref x)
      = (∏ i, p i.castSucc (pref i))
        * (p (Fin.last n) x
          * F (Fin.snoc (α := fun _ => V) pref x)) := by
    intro pref x
    have hprod : (∏ i, p i (Fin.snoc (α := fun _ => V) pref x i))
        = (∏ i, p i.castSucc (pref i)) * p (Fin.last n) x := by
      rw [Fin.prod_univ_castSucc, Finset.prod_congr rfl
        (fun i _ => by
          rw [show Fin.snoc (α := fun _ => V) pref x i.castSucc = pref i
            from Fin.snoc_castSucc (α := fun _ => V) x pref i]), Fin.snoc_last]
    rw [hprod]
    ring
  unfold prodE
  rw [← Fintype.sum_equiv (Fin.snocEquiv (n := n) (fun _ => V))
    (fun xp => (∏ i, p i (Fin.snoc (α := fun _ => V) xp.2 xp.1 i))
      * F (Fin.snoc (α := fun _ => V) xp.2 xp.1))
    (fun ω => prodDens p ω * F ω)
    (fun xp => by
      show (∏ i, p i (Fin.snoc (α := fun _ => V) xp.2 xp.1 i))
        * F (Fin.snoc (α := fun _ => V) xp.2 xp.1)
        = prodDens p (Fin.snoc (α := fun _ => V) xp.2 xp.1)
          * F (Fin.snoc (α := fun _ => V) xp.2 xp.1)
      rw [prodDens])]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro pref _
  have hmap : ∀ x : V,
      (∏ i, p i (Fin.snoc (α := fun _ => V)
        (Prod.snd (x, pref)) (Prod.fst (x, pref)) i))
      * F (Fin.snoc (α := fun _ => V)
        (Prod.snd (x, pref)) (Prod.fst (x, pref)))
      = (∏ i, p i.castSucc (pref i))
        * (p (Fin.last n) x
          * F (Fin.snoc (α := fun _ => V) pref x)) := by
    intro x
    simpa using hpair pref x
  calc ∑ x, (∏ i, p i (Fin.snoc (x, pref).2 (x, pref).1 i))
        * F (Fin.snoc (x, pref).2 (x, pref).1)
      = ∑ x, (∏ i, p i.castSucc (pref i))
        * (p (Fin.last n) x
          * F (Fin.snoc (α := fun _ => V) pref x)) :=
          Finset.sum_congr rfl (fun x _ => hmap x)
    _ = (∏ i, p i.castSucc (pref i))
        * ∑ x, p (Fin.last n) x
          * F (Fin.snoc (α := fun _ => V) pref x) := by
          rw [Finset.mul_sum]

/-- Мартингальная сумма: snoc-рекурсия — шаг добавляет
приращение X_{n+1}, зависящее от полного префикса. -/
def azumaSum (X : ∀ t, (Fin t → V) → ℝ) :
    (n : ℕ) → (Fin n → V) → ℝ
  | 0, _ => 0
  | n + 1, ω => azumaSum X n (fun i => ω i.castSucc) + X (n + 1) ω

/-- Конгруэнтность azumaSum по функциональному равенству. -/
theorem azumaSum_congr (X : ∀ t, (Fin t → V) → ℝ) (n : ℕ)
    (ω ω' : Fin n → V) (h : ∀ i, ω i = ω' i) :
    azumaSum X n ω = azumaSum X n ω' := by
  induction n with
  | zero => simp [azumaSum]
  | succ n ih =>
      have hprefix : ∀ i, (fun j : Fin n => ω (j.castSucc)) i
          = (fun j : Fin n => ω' (j.castSucc)) i :=
        fun i => h i.castSucc
      show azumaSum X n (fun j => ω j.castSucc) + X (n + 1) ω
        = azumaSum X n (fun j => ω' j.castSucc) + X (n + 1) ω'
      rw [ih (fun j => ω j.castSucc) (fun j => ω' j.castSucc) hprefix]
      congr 1
      exact congrArg (X (n + 1)) (funext h)

/-- Snoc-разложение мартингальной суммы. -/
theorem azumaSum_snoc (X : ∀ t, (Fin t → V) → ℝ) (n : ℕ)
    (pref : Fin n → V) (v : V) :
    azumaSum X (n + 1) (Fin.snoc (α := fun _ => V) pref v)
      = azumaSum X n pref + X (n + 1) (Fin.snoc (α := fun _ => V) pref v) := by
  have hprefix : ∀ i : Fin n, (Fin.snoc (α := fun _ => V) pref v) i.castSucc = pref i := by
    intro i
    simp
  have hfun : (fun i : Fin n => (Fin.snoc (α := fun _ => V) pref v) i.castSucc) = pref :=
    funext hprefix
  show azumaSum X n (fun i : Fin n => (Fin.snoc (α := fun _ => V) pref v) i.castSucc)
    + X (n + 1) (Fin.snoc (α := fun _ => V) pref v)
    = azumaSum X n pref + X (n + 1) (Fin.snoc (α := fun _ => V) pref v)
  rw [hfun]

/-- **Мартингальный mgf (Азума)**: при условно
центрированных приращениях (|X| ≤ c, E[X_{t+1}|π] = 0 при
каждом префиксе pref) mgf суммы ограничен e^{nλ²c²/2}.
Зависимость от ВСЕЙ истории допустима — усиление
fresh-randomness модели (P0-4, теорема E аудита). -/
theorem azuma_mgf (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (X : ∀ t, (Fin t → V) → ℝ) (c : ℝ) (hc : 0 < c)
    (hbnd : ∀ t pref, |X t pref| ≤ c)
    (hmean : ∀ t pref,
      ∑ v, q v * X (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0)
    (lam : ℝ) (n : ℕ) :
    prodE (fun _ => q) (fun ω => Real.exp (lam * azumaSum X n ω))
      ≤ Real.exp (n * lam ^ 2 * c ^ 2 / 2) := by
  induction n with
  | zero => simp [azumaSum, prodE, prodDens]
  | succ n ih =>
      rw [prodE_snoc]
      -- внутренняя сумма по свежей координате: условная лемма
      have hinner : ∀ pref : Fin n → V,
          ∑ v, q v * Real.exp (lam * azumaSum X (n + 1)
            (Fin.snoc (α := fun _ => V) pref v))
            ≤ Real.exp (lam * azumaSum X n pref)
              * Real.exp (lam ^ 2 * c ^ 2 / 2) := by
        intro pref
        have hmul : ∀ v, Real.exp (lam * azumaSum X (n + 1)
              (Fin.snoc (α := fun _ => V) pref v))
            = Real.exp (lam * azumaSum X n pref)
              * Real.exp (lam * X (n + 1) (Fin.snoc (α := fun _ => V) pref v)) := by
          intro v
          rw [azumaSum_snoc, ← Real.exp_add]
          ring
        have hsub : ∑ v, q v * Real.exp
            (lam * X (n + 1) (Fin.snoc (α := fun _ => V) pref v))
            ≤ Real.exp (lam ^ 2 * c ^ 2 / 2) :=
          hoeffding_lemma_prefix q hq0 hq1
            (fun v => X (n + 1) (Fin.snoc (α := fun _ => V) pref v)) c hc
            (fun v => abs_le.mp (hbnd (n + 1)
              (Fin.snoc (α := fun _ => V) pref v)))
            (hmean n pref) lam
        calc ∑ v, q v * Real.exp (lam * azumaSum X (n + 1)
              (Fin.snoc (α := fun _ => V) pref v))
            = ∑ v, q v * (Real.exp (lam * azumaSum X n pref)
                * Real.exp (lam * X (n + 1) (Fin.snoc (α := fun _ => V) pref v))) := by
              refine Finset.sum_congr rfl ?_
              intro v _
              rw [hmul v]
          _ = Real.exp (lam * azumaSum X n pref)
              * ∑ v, q v * Real.exp
                  (lam * X (n + 1) (Fin.snoc (α := fun _ => V) pref v)) := by
              have hswap : ∑ v, q v * (Real.exp (lam * azumaSum X n pref)
                  * Real.exp (lam * X (n + 1) (Fin.snoc (α := fun _ => V) pref v)))
                = ∑ v, Real.exp (lam * azumaSum X n pref)
                  * (q v * Real.exp
                    (lam * X (n + 1) (Fin.snoc (α := fun _ => V) pref v))) :=
                Finset.sum_congr rfl fun v _ => by ring
              rw [hswap, Finset.mul_sum]
          _ ≤ Real.exp (lam * azumaSum X n pref)
              * Real.exp (lam ^ 2 * c ^ 2 / 2) :=
              mul_le_mul_of_nonneg_left hsub (by positivity)
      -- сжатие: ≤ e^{λ²c²/2} · Σ_π dens · e^{λ azumaSum n}
      have houter : ∑ pref : Fin n → V,
          (∏ i, q (pref i))
          * ∑ v, q v * Real.exp (lam * azumaSum X (n + 1)
            (Fin.snoc (α := fun _ => V) pref v))
          ≤ Real.exp (lam ^ 2 * c ^ 2 / 2)
            * prodE (fun _ => q)
              (fun ω => Real.exp (lam * azumaSum X n ω)) := by
        have h1 : ∀ pref : Fin n → V,
            (∏ i, q (pref i))
              * ∑ v, q v * Real.exp (lam * azumaSum X (n + 1)
                (Fin.snoc (α := fun _ => V) pref v))
            ≤ (∏ i, q (pref i))
              * (Real.exp (lam * azumaSum X n pref)
                * Real.exp (lam ^ 2 * c ^ 2 / 2)) :=
          fun pref => mul_le_mul_of_nonneg_left (hinner pref)
            (Finset.prod_nonneg fun i _ => hq0 (pref i))
        have h2 : ∑ pref : Fin n → V,
            (∏ i, q (pref i))
            * (Real.exp (lam * azumaSum X n pref)
              * Real.exp (lam ^ 2 * c ^ 2 / 2))
            = Real.exp (lam ^ 2 * c ^ 2 / 2)
            * prodE (fun _ => q)
              (fun ω => Real.exp (lam * azumaSum X n ω)) := by
          unfold prodE prodDens
          have hstep : ∑ pref : Fin n → V,
              (∏ i, q (pref i))
              * (Real.exp (lam * azumaSum X n pref)
                * Real.exp (lam ^ 2 * c ^ 2 / 2))
            = ∑ pref : Fin n → V, Real.exp (lam ^ 2 * c ^ 2 / 2)
              * ((∏ i, q (pref i))
                * Real.exp (lam * azumaSum X n pref)) :=
            Finset.sum_congr rfl fun pref _ => by ring
          rw [hstep, Finset.mul_sum]
        calc ∑ pref : Fin n → V,
              (∏ i, q (pref i))
              * ∑ v, q v * Real.exp (lam * azumaSum X (n + 1)
                (Fin.snoc (α := fun _ => V) pref v))
            ≤ ∑ pref : Fin n → V,
              (∏ i, q (pref i))
              * (Real.exp (lam * azumaSum X n pref)
                * Real.exp (lam ^ 2 * c ^ 2 / 2)) :=
              Finset.sum_le_sum fun pref _ => h1 pref
          _ = Real.exp (lam ^ 2 * c ^ 2 / 2)
              * prodE (fun _ => q)
              (fun ω => Real.exp (lam * azumaSum X n ω)) := h2
      refine le_trans houter ?_
      refine le_trans (mul_le_mul_of_nonneg_left ih
        (Real.exp_pos _).le) ?_
      rw [← Real.exp_add, Real.exp_le_exp]
      norm_num

      linarith

/-- Линейность azumaSum по neg-семейству. -/
theorem azumaSum_neg (X : ∀ t, (Fin t → V) → ℝ) (n : ℕ)
    (ω : Fin n → V) :
    azumaSum (fun t pref => - X t pref) n ω
      = - azumaSum X n ω := by
  induction n with
  | zero => simp [azumaSum]
  | succ n ih =>
      show azumaSum (fun t pref => - X t pref) n _
        + (- X (n + 1) ω)
        = - (azumaSum X n _ + X (n + 1) ω)
      rw [ih (fun i => ω i.castSucc)]
      ring

/-- **Хвост Азумы (нижний)**: для условно центрированных
ограниченных приращений P[ΣX ≤ −Δ] ≤ exp(−Δ²/(2nc²)) —
оптимизация λ = Δ/(nc) + Markov. -/
theorem azuma_tail_low (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (X : ∀ t, (Fin t → V) → ℝ) (c : ℝ) (hc : 0 < c)
    (hn : 0 < n)
    (hbnd : ∀ t pref, |X t pref| ≤ c)
    (hmean : ∀ t pref,
      ∑ v, q v * X (t + 1) (Fin.snoc pref v) = 0)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    prodPq (fun _ => q)
      (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ Real.exp (- Δ ^ 2 / (2 * (n : ℝ) * c ^ 2)) := by
  classical
  -- применяем mgf к (−X): то же семейство условно центрировано
  have hmgf : prodE (fun _ => q)
      (fun ω => Real.exp (Δ / ((n : ℝ) * c ^ 2)
        * (- azumaSum X n ω)))
      ≤ Real.exp (n * (Δ / ((n : ℝ) * c ^ 2)) ^ 2 * c ^ 2 / 2) := by
    have hrw : (fun ω => Real.exp (Δ / ((n : ℝ) * c ^ 2)
          * (- azumaSum X n ω)))
        = (fun ω => Real.exp (Δ / ((n : ℝ) * c ^ 2)
          * azumaSum (fun t pref => - X t pref) n ω)) :=
      funext fun ω => by rw [azumaSum_neg X n ω]
    rw [hrw]
    refine azuma_mgf q hq0 hq1 (fun t pref => -X t pref) c hc
      (fun t pref => by
        rw [abs_neg]
        exact hbnd t pref)
      (fun t pref => by
        have h0 := hmean t pref
        have hneg : ∑ v, q v * (- X (t + 1) (Fin.snoc pref v))
            = - ∑ v, q v * X (t + 1) (Fin.snoc pref v) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
        rw [hneg, h0]
        ring)
      (Δ / ((n : ℝ) * c ^ 2)) n
  -- Markov на событии {ΣX ≤ −Δ}: exp(λ·(−ΣX)) ≥ exp(λΔ)
  have hisprob : IsProbSys (fun _ : Fin n => q) :=
    fun _ => ⟨hq0, hq1⟩
  have hnc : (0:ℝ) < (n : ℝ) * c ^ 2 := by
    have hn' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hmarkov : Real.exp (Δ ^ 2 / ((n : ℝ) * c ^ 2))
      * prodPq (fun _ => q) (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ prodE (fun _ => q)
        (fun ω => Real.exp (Δ / ((n : ℝ) * c ^ 2)
          * (- azumaSum X n ω))) := by
    refine markov_ge (fun _ => q) hisprob
      (fun ω => Real.exp (Δ / ((n : ℝ) * c ^ 2)
        * (- azumaSum X n ω)))
      (fun ω => (Real.exp_pos _).le) _
      (fun ω => azumaSum X n ω ≤ -Δ)
      (fun ω hω => ?_)
    apply Real.exp_le_exp.mpr
    have hlam : (0:ℝ) ≤ Δ / ((n : ℝ) * c ^ 2) :=
      div_nonneg hΔ.le hnc.le
    have hkey : Δ ≤ - azumaSum X n ω := by
      have : azumaSum X n ω ≤ -Δ := hω
      linarith
    calc (Δ:ℝ) ^ 2 / ((n : ℝ) * c ^ 2)
        = (Δ / ((n : ℝ) * c ^ 2)) * Δ := by
          field_simp
      _ ≤ (Δ / ((n : ℝ) * c ^ 2)) * (- azumaSum X n ω) :=
          mul_le_mul_of_nonneg_left hkey hlam
  -- сведение: P ≤ e^{nλ²c²/2 − λΔ} = e^{−Δ²/(2nc²)}
  have hfinal : prodPq (fun _ => q) (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ Real.exp (- Δ ^ 2 / (2 * (n : ℝ) * c ^ 2)) := by
    have h1 : Real.exp (Δ ^ 2 / ((n : ℝ) * c ^ 2))
        * prodPq (fun _ => q) (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ Real.exp (n * (Δ / ((n : ℝ) * c ^ 2)) ^ 2 * c ^ 2 / 2) :=
        le_trans hmarkov hmgf
    have hexp : (0:ℝ) < Real.exp (Δ ^ 2 / ((n : ℝ) * c ^ 2)) :=
      Real.exp_pos _
    have h1' : prodPq (fun _ => q) (fun ω => azumaSum X n ω ≤ -Δ)
        * Real.exp (Δ ^ 2 / ((n : ℝ) * c ^ 2))
      ≤ Real.exp (n * (Δ / ((n : ℝ) * c ^ 2)) ^ 2 * c ^ 2 / 2) := by
      rw [mul_comm]
      exact h1
    have h2 : prodPq (fun _ => q) (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ Real.exp (n * (Δ / ((n : ℝ) * c ^ 2)) ^ 2 * c ^ 2 / 2)
        / Real.exp (Δ ^ 2 / ((n : ℝ) * c ^ 2)) := by
      rw [le_div_iff₀ hexp]
      exact h1'
    refine le_trans h2 ?_
    rw [← Real.exp_sub]
    have hex : n * (Δ / ((n : ℝ) * c ^ 2)) ^ 2 * c ^ 2 / 2
        - Δ ^ 2 / ((n : ℝ) * c ^ 2)
        = - Δ ^ 2 / (2 * (n : ℝ) * c ^ 2) := by
      field_simp
      ring
    rw [hex]
  exact hfinal

/-- Линейность azumaSum по разности семейств. -/
theorem azumaSum_sub (X Y : ∀ t, (Fin t → V) → ℝ) (n : ℕ)
    (ω : Fin n → V) :
    azumaSum (fun t pref => X t pref - Y t pref) n ω
      = azumaSum X n ω - azumaSum Y n ω := by
  induction n with
  | zero => simp [azumaSum]
  | succ n ih =>
      show azumaSum (fun t pref => X t pref - Y t pref) n _
        + (X (n + 1) ω - Y (n + 1) ω)
        = azumaSum X n _ + X (n + 1) ω
          - (azumaSum Y n _ + Y (n + 1) ω)
      rw [ih (fun i => ω i.castSucc)]
      ring

/-- Нижняя оценка azumaSum почленным константным полом. -/
theorem azumaSum_lower (X : ∀ t, (Fin t → V) → ℝ) (c : ℝ)
    (hX : ∀ t pref, c ≤ X (t + 1) pref) (n : ℕ)
    (ω : Fin n → V) :
    (n : ℝ) * c ≤ azumaSum X n ω := by
  induction n with
  | zero => simp [azumaSum]
  | succ n ih =>
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
        push_cast
        ring
      rw [hcast]
      show ((n : ℝ) + 1) * c
        ≤ azumaSum X n (fun i => ω i.castSucc) + X (n + 1) ω
      have h1 := ih (fun i => ω i.castSucc)
      have h2 := hX n ω
      linarith

/-- Расширение azumaSum по почленному равенству семейств. -/
theorem azumaSum_ext (X Y : ∀ t, (Fin t → V) → ℝ)
    (h : ∀ t pref, X t pref = Y t pref) (n : ℕ)
    (ω : Fin n → V) :
    azumaSum X n ω = azumaSum Y n ω := by
  induction n with
  | zero => simp [azumaSum]
  | succ n ih =>
      show azumaSum X n (fun i => ω i.castSucc) + X (n + 1) ω
        = azumaSum Y n (fun i => ω i.castSucc) + Y (n + 1) ω
      rw [ih (fun i => ω i.castSucc), h (n + 1) ω]

/-- **История-зависимые успехи (P0-4, теорема E аудита)**:
успех S_{t+1} — функция ПРЕФИКСА (вся история + свежая
случайность), значения в [0,1], условные полы при КАЖДОМ
префиксе: Σ_v q v · S_{t+1}(snoc π v) ≥ p₀. Тогда

  azumaSum S n ≥ n·p₀ − Δ  w.p.  ≥ 1 − exp(−Δ²/(2n))

— настоящая мартингальная зависимость (Азума) вместо
fresh-randomness модели. Приращения Z = S − condMean(S)
условно центрированы и |Z| ≤ 1 (обе части в [0,1]).
Согласовано с concDelta-заметкой: масштаб √(2n·log(1/δ)). -/
theorem adaptive_success_azuma (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (S : ∀ t, (Fin t → V) → ℝ)
    (hS : ∀ t pref, 0 ≤ S t pref ∧ S t pref ≤ 1)
    (p0 : ℝ)
    (hfloor : ∀ t pref,
      p0 ≤ ∑ v, q v * S (t + 1) (Fin.snoc pref v))
    (n : ℕ) (hn : 0 < n) (Δ : ℝ) (hΔ : 0 < Δ) :
    1 - Real.exp (- Δ ^ 2 / (2 * (n : ℝ)))
      ≤ prodPq (fun _ => q)
        (fun ω => n * p0 - Δ ≤ azumaSum S n ω) := by
  classical
  -- condMean и центрированные приращения
  set m : ∀ t, (Fin t → V) → ℝ := fun t pref =>
    ∑ v, q v * S (t + 1) (Fin.snoc pref v) with hmdef
  set Z : ∀ t, (Fin t → V) → ℝ := fun t pref =>
    match t with
    | 0 => 0
    | t + 1 => S (t + 1) pref
        - m t (Fin.init (α := fun _ => V) pref) with hZdef
  -- m ∈ [0,1]
  have hm01 : ∀ t pref, 0 ≤ m t pref ∧ m t pref ≤ 1 := by
    intro t pref
    constructor
    · exact Finset.sum_nonneg fun v _ =>
        mul_nonneg (hq0 v) (hS (t + 1) _).1
    · have hle : m t pref ≤ ∑ v, q v * (1 : ℝ) :=
        Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_left (hS (t + 1) _).2 (hq0 v)
      rw [hmdef] at hle
      have hrw : ∑ v, q v * (1 : ℝ) = 1 := by
        simp [Finset.mul_sum, hq1]
      rw [hrw] at hle
      exact hle
  -- |Z| ≤ 1
  have hZbnd : ∀ t pref, |Z t pref| ≤ 1 := by
    intro t pref
    match t with
    | 0 => simp [hZdef]
    | t + 1 =>
        have h1 := hS (t + 1) pref
        have h2 := hm01 t (Fin.init (α := fun _ => V) pref)
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- условная центрированность Z (t ≥ 1; t = 0 не входит)
  have hmeanZ : ∀ (t : ℕ) (pref : Fin t → V),
      ∑ v, q v * Z (t + 1) (Fin.snoc pref v) = 0 := by
    intro t pref
    have hinit : ∀ v, Fin.init (α := fun _ => V)
        (Fin.snoc (α := fun _ => V) pref v) = pref :=
      fun v => by simpa using Fin.init_snoc pref v
    -- Z(t+1)(snoc pref v) = S(t+1)(snoc pref v) − m t pref
    have hZterm : ∀ v, Z (t + 1) (Fin.snoc pref v)
        = S (t + 1) (Fin.snoc pref v) - m t pref := by
      intro v
      simp only [hZdef]
      rw [hinit v]
    rw [Finset.sum_congr rfl (fun v _ => by
      rw [hZterm v])]
    have hsplit2 : ∑ v, q v * (S (t + 1) (Fin.snoc pref v)
          - m t pref)
        = ∑ v, q v * S (t + 1) (Fin.snoc pref v)
          - ∑ v, q v * (m t pref) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hsplit2]
    have hfirst : ∑ v, q v * S (t + 1) (Fin.snoc pref v)
        = m t pref := by simp only [hmdef]
    have hsecond : ∑ v, q v * m t pref = m t pref := by
      rw [← Finset.sum_mul, hq1]
      simp
    rw [hfirst, hsecond]
    ring
  -- хвост Азумы для Z: P[azumaSum Z ≤ −Δ] ≤ exp(−Δ²/(2n))
  have hisprob : IsProbSys (fun _ : Fin n => q) :=
    fun _ => ⟨hq0, hq1⟩
  have htail0 := azuma_tail_low q hq0 hq1 Z 1 zero_lt_one
    hn hZbnd hmeanZ Δ hΔ
  have htail : prodPq (fun _ => q)
      (fun ω => azumaSum Z n ω ≤ -Δ)
      ≤ Real.exp (- Δ ^ 2 / (2 * (n : ℝ))) := by
    have hring : (2 * (n : ℝ) * 1 ^ 2) = 2 * (n : ℝ) := by ring
    rw [hring] at htail0
    exact htail0
  -- m' и разложение azumaSum Z = azumaSum S − azumaSum m'
  set m' : ∀ t, (Fin t → V) → ℝ := fun t pref =>
    match t with
    | 0 => S 0 pref
    | t + 1 => m t (Fin.init (α := fun _ => V) pref) with hm'def
  have hZeq : ∀ t pref, Z t pref = S t pref - m' t pref := by
    intro t pref
    match t with
    | 0 => simp [hZdef, hm'def]
    | t + 1 => simp [hZdef, hm'def]
  have hsplit : ∀ ω : Fin n → V,
      azumaSum Z n ω
        = azumaSum S n ω - azumaSum m' n ω := by
    intro ω
    rw [azumaSum_ext Z (fun t pref => S t pref - m' t pref)
      hZeq n ω]
    exact azumaSum_sub S m' n ω
  have hmlower : ∀ ω : Fin n → V,
      (n : ℝ) * p0 ≤ azumaSum m' n ω := by
    intro ω
    refine azumaSum_lower m' p0 ?_ n ω
    intro t pref
    rw [hm'def]
    show p0 ≤ m t (Fin.init (α := fun _ => V) pref)
    rw [hmdef]
    exact hfloor t (Fin.init (α := fun _ => V) pref)
  -- включение событий и монотонность
  have hmono : prodPq (fun _ => q)
      (fun ω => azumaSum S n ω < n * p0 - Δ)
      ≤ Real.exp (- Δ ^ 2 / (2 * (n : ℝ))) := by
    refine le_trans (prodPq_mono (fun _ => q) hisprob _ _
      (fun ω hω => ?_)) htail
    rw [hsplit]
    have h1 := hmlower ω
    linarith
  -- финал через дополнение
  have hcompl : prodPq (fun _ => q)
      (fun ω => ¬ (azumaSum S n ω < n * p0 - Δ))
      = 1 - prodPq (fun _ => q)
        (fun ω => azumaSum S n ω < n * p0 - Δ) :=
    prodPq_compl (fun _ => q) hisprob _
  calc (1:ℝ) - Real.exp (- Δ ^ 2 / (2 * (n : ℝ)))
      ≤ 1 - prodPq (fun _ => q)
        (fun ω => azumaSum S n ω < n * p0 - Δ) := by
          linarith [hmono]
    _ = prodPq (fun _ => q)
        (fun ω => ¬ (azumaSum S n ω < n * p0 - Δ)) := hcompl.symm
    _ ≤ prodPq (fun _ => q)
        (fun ω => n * p0 - Δ ≤ azumaSum S n ω) :=
          prodPq_mono (fun _ => q) hisprob _ _
            (fun ω hω => not_lt.mp hω)

end Hagi
