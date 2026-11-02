import Hagi.Probability.GibbsCore
import Hagi.Probability.GibbsCooling

/-!
# Мост: концентрация Гиббса через канон

Субтрактивная форма концентрации (традиционная) —
следствие канонической аддитивной: канон несёт более
сильное утверждение, классическая форма наследуется.
-/

namespace Hagi.Probability

open Finset Real

/-- Алгебра: аддитивная форма сильнее субтрактивной. -/
theorem one_div_ge_sub {x : ℝ} (hx : 0 ≤ x) :
    1 - x ≤ 1 / (1 + x) := by
  have hpos : (0:ℝ) < 1 + x := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith [mul_nonneg hx hx]

/-- МОСТ: традиционная субтрактивная концентрация —
следствие канонической аддитивной. Канон строго сильнее. -/
theorem gibbs_concentration_via_canon
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : V → ℝ) (δ : ℝ) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (T : ℝ) (hT : 0 < T) :
    Real.exp (-(E vstar) / T) / ∑ v, Real.exp (-(E v) / T)
      ≥ 1 - ((Fintype.card V : ℝ) - 1) * Real.exp (-δ / T) := by
  have hx : (0:ℝ)
      ≤ ((Fintype.card V : ℝ) - 1) * Real.exp (-δ / T) := by
    have hcn : (1:ℝ) ≤ (Fintype.card V : ℝ) := by
      have h1 : (1:ℕ) ≤ Fintype.card V := by
        obtain ⟨v⟩ := ‹Nonempty V›
        have hsub : ({v} : Finset V) ⊆ Finset.univ :=
          Finset.subset_univ _
        have hle := Finset.card_le_card hsub
        simpa using hle
      exact_mod_cast h1
    exact mul_nonneg (by linarith) (exp_pos _).le
  have hcanon := gibbs_concentration_canon E T hT δ vstar hgap
  have hsub := one_div_ge_sub hx
  have hchain : 1 - ((Fintype.card V : ℝ) - 1) * Real.exp (-δ / T)
      ≤ gibbsW E T vstar / gibbsZ E T := le_trans hsub hcanon
  unfold gibbsW gibbsZ at hchain
  exact hchain

end Hagi.Probability
