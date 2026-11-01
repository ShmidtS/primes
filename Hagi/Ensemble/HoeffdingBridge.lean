import Hagi.Ensemble.Hoeffding
import Hagi.Probability.CertifiedEstimator

/-!
# Мост между weighted-слоем и слоем произведения

Одновыборочная теорема Hoeffding, применённая к
носителю-произведению с весами-произведениями, даёт хвост
суммы. Без явной независимости экспонента слабее — мост
честно фиксирует, что покупает независимость.
-/

namespace Hagi.Ensemble

open Hagi.Probability

variable {V : Type} [Fintype V] [Nonempty V]

/-- МОСТ В WEIGHTED-СЛОЙ: хвост суммы берётся
одновыборочной теоремой на носителе-произведении с
весами-произведениями. Без явной независимости экспонента
слабее — мост честно фиксирует, что покупает
независимость. -/
theorem hoeffding_tail_via_weighted {n : ℕ} (p : Fin n → V → ℝ)
    (hp : IsProbSys p) (X : Fin n → V → ℝ)
    (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    prodPq p (fun ω => t ≤ centeredSum p X ω)
      ≤ Real.exp (- t ^ 2 / (2 * ((n : ℝ)) ^ 2)) := by
  have hnpos : (0:ℝ) < (n : ℝ) := by positivity
  have hμ : ∀ i, 0 ≤ coordMean p X i ∧ coordMean p X i ≤ 1 := by
    intro i
    refine ⟨Finset.sum_nonneg fun v _ =>
      mul_nonneg ((hp i).1 v) (hX i v).1, ?_⟩
    have hle2 : ∑ v, p i v * X i v ≤ ∑ v, p i v * 1 :=
      Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_left (hX i v).2 ((hp i).1 v)
    have hone : ∑ v, p i v * 1 = 1 := by
      rw [← Finset.sum_mul, (hp i).2, one_mul]
    rw [hone] at hle2
    exact hle2
  have hterm : ∀ (ω : Fin n → V) (i : Fin n),
      (-1:ℝ) ≤ X i (ω i) - coordMean p X i
        ∧ X i (ω i) - coordMean p X i ≤ 1 := by
    intro ω i
    constructor <;> linarith [hX i (ω i), hμ i]
  have hcs : ∀ ω : Fin n → V,
      (-1:ℝ) * (n:ℝ) ≤ centeredSum p X ω
        ∧ centeredSum p X ω ≤ 1 * (n:ℝ) := by
    intro ω
    constructor
    · have hx0 : (0:ℝ) ≤ ∑ i, X i (ω i) :=
        Finset.sum_nonneg fun i _ => (hX i (ω i)).1
      have hmus : ∑ i, coordMean p X i ≤ (n : ℝ) := by
        have hub : ∑ i, coordMean p X i ≤ ∑ i, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (hμ i).2
        simp only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul] at hub
        norm_num at hub
        exact hub
      unfold centeredSum
      linarith [hx0, hmus]
    · have hxsn : ∑ i, X i (ω i) ≤ (n : ℝ) := by
        have hub : ∑ i, X i (ω i) ≤ ∑ i, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (hX i (ω i)).2
        simp only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul] at hub
        norm_num at hub
        exact hub
      have hmu0 : (0:ℝ) ≤ ∑ i, coordMean p X i :=
        Finset.sum_nonneg fun i _ => (hμ i).1
      unfold centeredSum
      linarith [hxsn, hmu0]
  have hw1 : ∑ ω : Fin n → V, prodDens p ω = 1 := by
    have := prodE_one p hp
    unfold prodE at this
    simpa using this
  have hc0 : ∑ ω : Fin n → V,
      prodDens p ω * (centeredSum p X ω / (n : ℝ)) = 0 := by
    have hz := centeredSum_mean_zero p hp X
    unfold prodE at hz
    have hsplit : ∀ ω : Fin n → V,
        prodDens p ω * (centeredSum p X ω / (n : ℝ))
          = prodDens p ω * centeredSum p X ω / (n : ℝ) :=
      fun ω => by ring
    rw [Finset.sum_congr rfl (fun ω _ => hsplit ω)]
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hz, zero_mul]
  have hmain := hoeffding_tail
    (V := Fin n → V) (prodDens p)
    (fun ω => centeredSum p X ω / (n : ℝ)) (-1) 1
    (fun ω => prodDens_nonneg hp ω) hw1
    (by norm_num)
    (fun ω => by
      show -1 ≤ centeredSum p X ω / (n : ℝ)
        ∧ centeredSum p X ω / (n : ℝ) ≤ 1
      constructor
      · rw [le_div_iff₀ hnpos]
        linarith [(hcs ω).1]
      · rw [div_le_iff₀ hnpos]
        linarith [(hcs ω).2])
    hc0
    (ε := t / (n : ℝ)) (by
      apply div_nonneg ht <;> positivity)
  have hexp : Real.exp (-2 * (t / (n : ℝ)) ^ 2
      / (1 - (-1 : ℝ)) ^ 2)
      = Real.exp (- t ^ 2 / (2 * ((n : ℝ)) ^ 2)) := by
    have hden : (1 - (-1 : ℝ)) ^ 2 = 4 := by norm_num
    rw [hden]
    have hnum : -2 * (t / (n : ℝ)) ^ 2 / 4
        = - t ^ 2 / (2 * ((n : ℝ)) ^ 2) := by
      field_simp
      ring
    rw [hnum]
  rw [hexp] at hmain
  have hev : Finset.sum (Finset.univ.filter
      (fun ω => t / (n : ℝ)
        ≤ centeredSum p X ω / (n : ℝ)))
      (fun ω => prodDens p ω)
      = prodPq p (fun ω => t ≤ centeredSum p X ω) := by
    unfold prodPq prodE
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hq : t ≤ centeredSum p X ω
    · have hle : t / (n : ℝ)
          ≤ centeredSum p X ω / (n : ℝ) :=
        div_le_div_of_nonneg_right hq hnpos.le
      simp [hq, hle]
    · have hle : ¬ (t / (n : ℝ)
          ≤ centeredSum p X ω / (n : ℝ)) := by
        intro hcontra
        have hm : (t / (n : ℝ)) * (n : ℝ)
            ≤ (centeredSum p X ω / (n : ℝ)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hcontra hnpos.le
        rw [div_mul_cancel₀ _ hnpos.ne',
          div_mul_cancel₀ _ hnpos.ne'] at hm
        exact absurd hm hq
      simp [hq, hle]
  rw [← hev]
  exact hmain

end Hagi.Ensemble
