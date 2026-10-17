/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.CertifiedTakeoff
import Hagi.Probability.CertifiedEstimator
/-!
# UnionBoundNonneg — объединение событий для мер с нулевой массой

Стандартный `union_bound_finite` требует строго положительных
весов (hq : 0 < q v); координатные произведения `prodDens p ω`
имеют нули (`p i v = 0`). Эта лемма — та же конечная ladder
union bound, но при `0 ≤ q v`: точечная индикаторная
надстройка + перестановка сумм (R555, часть 1).
-/

open scoped BigOperators

namespace Hagi.Unified

/-- **Union bound при неотрицательных весах (R555)**. -/
theorem union_bound_nonneg {W : Type*} [Fintype W]
    (q : W → ℝ) (hq : ∀ v, 0 ≤ q v) (S : ℕ → W → Prop)
    [∀ t, DecidablePred (S t)] (T : ℕ) :
    ∑ v ∈ Finset.filter (fun v => ∃ t < T, S t v) Finset.univ, q v
      ≤ ∑ t ∈ Finset.range T,
        ∑ v ∈ Finset.filter (S t) Finset.univ, q v := by
  classical
  have hRHS : ∑ t ∈ Finset.range T,
      ∑ v ∈ Finset.filter (S t) Finset.univ, q v
      = ∑ t ∈ Finset.range T, ∑ v : W, (if S t v then q v else 0) := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.sum_filter]
  rw [Finset.sum_filter, hRHS, ← Finset.sum_comm]
  refine Finset.sum_le_sum (fun v _ => ?_)
  by_cases hE : ∃ t < T, S t v
  · have hEcopy := hE
    obtain ⟨t, ht, hSt⟩ := hEcopy
    have hmem : t ∈ Finset.range T := Finset.mem_range.mpr ht
    have hs := Finset.single_le_sum
      (f := fun t' : ℕ => (if S t' v then q v else 0))
      (fun x _ => by split <;> simp [hq v]) hmem
    rw [if_pos hSt] at hs
    simp only [if_pos hE]
    exact hs
  · rw [if_neg hE]
    refine le_trans (Finset.sum_nonneg (fun t _ => ?_)) (le_refl _)
    split <;> simp [hq v]

end Hagi.Unified

/-!
# CertifiedGains — пошаговая сертификация прироста (R555 ч.2)

Расширение R554 на T inequality-посылок. Композиция:
(1) шаговое bad-событие A_t = {margin_t ∧ μ_t-нарушение} имеет
    меру ≤ 2e^{−2nε²} (certified_premise + монотонность + compl);
(2) нарушение цели точечно покрывается ∃ t < T, A_t;
(3) лестница (R555 ч.1-формы, prodPq-версия) даёт
    P(цель) ≥ 1 − 2T·e^{−2nε²}.
-/

open scoped BigOperators

namespace Hagi.Unified

variable {n : ℕ} {V : Type} [Fintype V] [Nonempty V]

/-- **Вероятностная лестница, prodPq-форма (R555)**: если каждое
шаговое bad-событие имеет prodPq-меру ≤ M, то q (нарушаемое
только при каком-то S t) имеет меру ≥ 1 − T·M. -/
theorem prob_ladder_lower (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (q : (Fin n → V) → Prop) [DecidablePred q]
    (S : ℕ → (Fin n → V) → Prop) [instS : ∀ t, DecidablePred (S t)]
    (T : ℕ) (M : ℝ)
    (hA : ∀ t, prodPq p (S t) ≤ M)
    (hcover : ∀ ω : Fin n → V, ¬ q ω → ∃ t < T, S t ω) :
    1 - (T:ℝ) * M ≤ prodPq p q := by
  classical
  have hcompl : prodPq p (fun ω => ¬ q ω) = 1 - prodPq p q :=
    prodPq_compl p hp q
  have hsum : ∑ t ∈ Finset.range T, prodPq p (S t) ≤ (T:ℝ) * M := by
    have h1 : ∑ t ∈ Finset.range T, prodPq p (S t)
        ≤ ∑ t ∈ Finset.range T, M :=
      Finset.sum_le_sum (fun t _ => hA t)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    exact h1
  have hcover' : ∑ v ∈ Finset.filter (fun ω => ¬ q ω) Finset.univ,
      prodDens p v
      ≤ ∑ v ∈ Finset.filter (fun ω => ∃ t < T, S t ω) Finset.univ,
        prodDens p v := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun x _ hx => prodDens_nonneg hp x)
    intro ω hω
    have h1 := Finset.mem_filter.mp hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ ω, hcover ω h1.2⟩
  have hRHS : ∑ v ∈ Finset.filter (fun ω => ∃ t < T, S t ω) Finset.univ,
      prodDens p v
      ≤ ∑ t ∈ Finset.range T, prodPq p (S t) := by
    have hstep := union_bound_nonneg (prodDens p)
      (fun v => prodDens_nonneg hp v) S T
    refine le_trans hstep ?_
    have hper : ∀ t : ℕ, ∑ v ∈ Finset.filter (S t) Finset.univ,
        prodDens p v = prodPq p (S t) := by
      intro t
      unfold prodPq prodE
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl (fun v _ => by
        by_cases hq : S t v <;> simp [hq, mul_one, mul_zero])
    exact le_of_eq (Finset.sum_congr rfl
      (fun (t : ℕ) (_ : t ∈ Finset.range T) => hper t))
  have hLHS : ∑ v ∈ Finset.filter (fun ω => ¬ q ω) Finset.univ,
      prodDens p v = prodPq p (fun ω => ¬ q ω) := by
    rw [Finset.sum_filter, prodPq, prodE]
    exact Finset.sum_congr rfl (fun v _ => by
      by_cases hq : q v <;> simp [hq])
  have hchain : prodPq p (fun ω => ¬ q ω) ≤ (T:ℝ) * M := by
    rw [← hLHS]
    exact le_trans hcover' (le_trans hRHS hsum)
  linarith [hcompl, hchain]

/-- **Certified T-шаговый takeoff (R555 ч.2)**: уровень
1 − 2T·e^{−2nε²} для импликации «все margins → takeoff». -/
theorem certified_gainprod_takeoff (p : Fin n → V → ℝ)
    (hp : IsProbSys p)
    (X Y : ℕ → Fin n → V → ℝ)
    (hX : ∀ t i v, 0 ≤ X t i v ∧ X t i v ≤ 1)
    (hY : ∀ t i v, 0 ≤ Y t i v ∧ Y t i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps)
    (C G D : ℕ → ℝ) (D0 : ℝ) (alpha gamma rho beta : ℝ)
    (xi : ℕ → ℝ) (T : ℕ)
    (hbridge : ∀ t, ∑ i, coordMean p (X t) i
        ≤ ∑ i, coordMean p (Y t) i → gamma * D t ≤ G t)
    (hα : 0 < alpha) (hγ : 0 < gamma) (hρ : 0 ≤ rho)
    (hC0 : 0 < C 0)
    (hcone0 : alpha / gamma * C 0 ≤ D 0)
    (hstep : ∀ t < T, C (t + 1) = C t + G t)
    (hdyn : ∀ t < T, rho * D t + beta * C t - xi t ≤ D (t + 1))
    (hcap : ∀ t < T, C (t + 1) ≤ (1 + alpha) * C t)
    (hbeta : ∀ t < T,
      alpha / gamma * ((1 + alpha) - rho) + xi t / C t ≤ beta) :
    1 - 2 * (T:ℝ) * Real.exp (- 2 * (n : ℝ) * eps ^ 2)
      ≤ prodPq p (fun ω =>
        (∀ t < T,
          ∑ i, X t i (ω i) + 2 * (n : ℝ) * eps
            ≤ ∑ i, Y t i (ω i))
        → C 0 * (1 + alpha) ^ T ≤ C T) := by
  classical
  set M : ℝ := 2 * Real.exp (- 2 * (n : ℝ) * eps ^ 2) with hMdef
  set q : (Fin n → V) → Prop := fun ω =>
    (∀ t < T, ∑ i, X t i (ω i) + 2 * (n : ℝ) * eps
      ≤ ∑ i, Y t i (ω i))
    → C 0 * (1 + alpha) ^ T ≤ C T with hqdef
  set S : ℕ → (Fin n → V) → Prop := fun t ω =>
    (∑ i, X t i (ω i) + 2 * (n : ℝ) * eps ≤ ∑ i, Y t i (ω i))
    ∧ ¬ (∑ i, coordMean p (X t) i ≤ ∑ i, coordMean p (Y t) i)
    with hSdef
  -- детерминированный takeoff при всех прирост-посылках
  have htakeoff : (∀ t < T, gamma * D t ≤ G t) →
      C 0 * (1 + alpha) ^ T ≤ C T :=
    fun hgain => sustained_takeoff_trunc C G D alpha gamma rho beta
      xi T hα hγ hρ hC0 hcone0 hstep hgain hdyn hcap hbeta
  -- (1) шаговые меры
  have hA : ∀ t, prodPq p (S t) ≤ M := by
    intro t
    have hcert := certified_premise p hp (X t) (Y t) (hX t)
      (hY t) hn eps heps
    have hmono := prodPq_mono p hp
      (fun ω => (∑ i, X t i (ω i) + 2 * (n : ℝ) * eps
        ≤ ∑ i, Y t i (ω i))
      → ∑ i, coordMean p (X t) i ≤ ∑ i, coordMean p (Y t) i)
      (fun ω => ¬ ((∑ i, X t i (ω i) + 2 * (n : ℝ) * eps
        ≤ ∑ i, Y t i (ω i))
      ∧ ¬ (∑ i, coordMean p (X t) i ≤ ∑ i, coordMean p (Y t) i)))
      (fun ω h hA => absurd (h hA.1) hA.2)
    rw [prodPq_compl p hp] at hmono
    linarith [hmono]
  -- (2) точечное покрытие
  have hcover : ∀ ω : Fin n → V, ¬ q ω → ∃ t < T, S t ω := by
    intro ω hcon
    rw [not_imp] at hcon
    obtain ⟨hmargin, hnotake⟩ := hcon
    rw [not_le] at hnotake
    have hex : ∃ t < T, ¬ (gamma * D t ≤ G t) := by
      by_contra hcon2
      push Not at hcon2
      exact absurd (htakeoff (fun t ht => hcon2 t ht)) (not_le.mpr hnotake)
    obtain ⟨t, ht, hviol⟩ := hex
    refine ⟨t, ht, hmargin t ht, fun hmu => hviol (hbridge t hmu)⟩
  -- (3) лестница
  have hL := prob_ladder_lower p hp q S T M hA hcover
  have hMrw : M = 2 * Real.exp (- 2 * (n : ℝ) * eps ^ 2) := hMdef
  rw [hMrw] at hL
  linarith

end Hagi.Unified
