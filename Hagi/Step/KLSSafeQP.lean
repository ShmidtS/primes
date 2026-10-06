/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.SafeQPRobust
import Hagi.Probability.KLSBridge

set_option linter.style.header false

/-!
# KLSSafeQP: the composed certification (R180)

The composition bridge of R179: the KLS/Poincaré noise chain
(Var[⟪a, ĝ_B⟫] ≤ C·L²·‖a‖²/B) feeds the SafeQP robust margin
(`robust_feasibility`: a guard set one noise-bound tighter
absorbs the perturbation). Theorem `klsSafeQP_certified`: with
the true margin at least ε + t and the batch second moment at
most V = C·L²·‖a‖²/B, the NOISY inner-product check
certifies ε on an event of q-probability at least 1 − V/t².

geometry of data → variance → batch noise → SafeQP margin →
CERTIFIED STEP with explicit failure probability.
-/

namespace Hagi

open Finset

/-- **The composed KLS→SafeQP certification**: if the true
inner product exceeds the guard ε + t, and the KLS chain
bounds the centered batch projection's second moment by V
(e.g. V = C·L²·‖a‖²/B from `klsBatchNoise`), then the noisy
check certifies ε except on an event of q-mass ≤ V/t². The
SafeQP prescription (margins ε + m with m = t) now has a
theoretical noise budget instead of a measured constant. -/
theorem klsSafeQP_certified {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (q : Ω → ℝ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (C L : ℝ) (hC : 0 ≤ C)
    (sens : (Fin n → ℝ) → Ω → ℝ)
    (hpoincare : ∀ (g : Ω → Fin n → ℝ) (a : Fin n → ℝ),
      KLS.gradVar q g a ≤ C * KLS.expQ q (fun x => (sens a x) ^ 2))
    (hop : ∀ (a : Fin n → ℝ) (x : Ω), (sens a x) ^ 2 ≤ L ^ 2 * KLS.sqN a)
    {B : ℕ} (hB : 0 < B) (g : Fin B → Ω → Fin n → ℝ) (a : Fin n → ℝ)
    (huncorr : ∀ i j, i ≠ j →
      KLS.expQ q (fun x => (KLS.proj a (g i x)
          - KLS.expQ q (fun y => KLS.proj a (g i y)))
        * (KLS.proj a (g j x)
          - KLS.expQ q (fun y => KLS.proj a (g j y)))) = 0)
    (trueInner : Ω → ℝ) (estInner : Ω → ℝ)
    (hdev : ∀ x, estInner x - trueInner x
      = (∑ i, KLS.proj a (g i x) / B
          - (∑ i, KLS.expQ q (fun y => KLS.proj a (g i y))) / B))
    (gd : ℝ) (eps t : ℝ) (ht : 0 < t)
    (htrue : ∀ x, eps + |gd| * t ≤ gd * trueInner x) :
    (∑ x ∈ Finset.univ.filter (fun x => eps ≤ gd * estInner x), q x)
      ≥ 1 - (C * L ^ 2 * KLS.sqN a / B) / t ^ 2 := by
  -- the deviation field
  set dev : Ω → ℝ := fun x => ∑ i, KLS.proj a (g i x) / B
    - (∑ i, KLS.expQ q (fun y => KLS.proj a (g i y))) / B with hdevdef
  -- the KLS chain bounds its second moment
  set V := C * L ^ 2 * KLS.sqN a / B with hVdef
  have hnoise : KLS.expQ q (fun x => (dev x) ^ 2) ≤ V :=
    KLS.klsBatchNoise q hq0 hq1 C L hC sens hpoincare hop hB g a huncorr
  -- Chebyshev: the bad set has q-mass at most V / t^2
  have hbad : (∑ x ∈ Finset.univ.filter (fun x => t ≤ |dev x|), q x)
      ≤ V / t ^ 2 :=
    KLS.klsChebyshev q hq0 V t ht dev hnoise
  -- the certified set contains the complement of the bad set
  have hmono : (Finset.univ.filter (fun x => ¬(t ≤ |dev x|)))
      ⊆ Finset.univ.filter (fun x => eps ≤ gd * estInner x) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ x, ?_⟩
    have hlt : |dev x| < t := by
      by_contra hcon
      exact absurd (le_of_not_gt hcon) hx.2
    have hest : estInner x = trueInner x + dev x := by
      have h1 := hdev x
      linarith [h1]
    -- |dev x| <= t (non-strict is enough with a strict margin)
    have habsdev : |dev x| ≤ t := le_of_lt hlt
    -- |gd| * |dev x| <= |gd| * t
    have hbnd : |gd| * |dev x| ≤ |gd| * t :=
      mul_le_mul_of_nonneg_left habsdev (abs_nonneg gd)
    -- chain
    rw [hest]
    have htr := htrue x
    have hkey : |gd| * |dev x| ≤ |gd| * t := hbnd
    have hsplit : gd * dev x ≥ -(|gd| * t) := by
      have hEq : |gd * dev x| = |gd| * |dev x| := abs_mul gd (dev x)
      have h0 := neg_le_abs (gd * dev x)
      linarith [hkey, h0, hEq]
    nlinarith [htr, hsplit, abs_nonneg gd]
  -- the two filters partition the mass
  have hpart : (∑ x ∈ Finset.univ.filter (fun x => t ≤ |dev x|), q x)
      + (∑ x ∈ Finset.univ.filter (fun x => ¬(t ≤ |dev x|)), q x)
      = ∑ x, q x := by
    rw [Finset.sum_filter_add_sum_filter_not]
  -- the certified mass dominates the complement's mass
  have hdom : (∑ x ∈ Finset.univ.filter (fun x => ¬(t ≤ |dev x|)), q x)
      ≤ (∑ x ∈ Finset.univ.filter (fun x => eps ≤ gd * estInner x), q x) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases h1 : ¬(t ≤ |dev x|)
    · have hmem : x ∈ Finset.univ.filter (fun x => ¬(t ≤ |dev x|)) := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ x, h1⟩
      have hgood := hmono hmem
      rw [Finset.mem_filter] at hgood
      rw [ite_eq_left h1, ite_eq_left hgood.2]
    · by_cases h2 : eps ≤ gd * estInner x
      · rw [ite_eq_right h1, ite_eq_left h2]
        exact hq0 x
      · rw [ite_eq_right h1, ite_eq_right h2]
  -- assemble
  calc (∑ x ∈ Finset.univ.filter (fun x => eps ≤ gd * estInner x), q x)
      ≥ (∑ x ∈ Finset.univ.filter (fun x => ¬(t ≤ |dev x|)), q x) := hdom
    _ = 1 - (∑ x ∈ Finset.univ.filter (fun x => t ≤ |dev x|), q x) := by
        rw [hq1] at hpart
        linarith
    _ ≥ 1 - V / t ^ 2 := by
        linarith [hbad]
end Hagi
