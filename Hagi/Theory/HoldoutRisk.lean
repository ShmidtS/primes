/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.CertifiedEstimator
import Hagi.Probability.Concentration

/-!
# Holdout risk: honest finite-population statistics (W3, C435)

The statistical-generalization layer the audit W3 found missing: a
genuine distributional setup for holdout risk on a finite population,
closing the gap between `Hagi.Data.PACBayes` (deterministic
Jensen/Gibbs core, no distribution) and `Hagi.Model.CEHeldout`
(finite union bound, no population risk).

## Setup

The population is a finite nonempty type `Ω` of data points; a model
fixed BEFORE the holdout draw is a loss table `f : Ω → ℝ` (the train
split premise: the model is trained on data disjoint from the holdout
draw, hence constant in the sample — no measurability assumptions,
everything is a `Fintype` sum).  The holdout law is the `k`-fold
product of the uniform density over `Ω` (`popIsProb`), the sample
being `ωs : Fin k → Ω`:

* `popMean f` — population (true) risk, the uniform mean over `Ω`;
* `holdoutMean f ωs` — holdout estimate, the mean loss over the `k`
  sampled points.

## Main results

* `holdout_unbiased` — for FIXED `f`, `E[holdoutMean f] = popMean f`
  (every coordinate mean of the uniform product is `popMean`).
* `holdout_concentration` — for `0 ≤ f ≤ 1`, `k > 0`, `ε > 0`:
  `P[|holdoutMean f − popMean f| ≥ ε] ≤ 2·exp(−2kε²)` — the canonical
  `concConfidenceTwoSided` of the concentration tower.
* `selection_bias_holdout_eq_zero` / `selection_bias_pop_eq_half` —
  the honesty warning: if the model is selected AFTER viewing the
  holdout, unbiasedness BREAKS.  A fully computable two-point
  counterexample: selecting the model that minimizes the one-point
  holdout loss makes the holdout risk of the selected model
  identically 0 while its population risk is 1/2 — maximal bias.  The
  fixed-`f` premise of `holdout_unbiased` is essential, not
  decoration.
* `holdout_uniform_codebook` — for a finite codebook `Θ` of models
  with losses in `[0, B]`, `B > 0`: the uniform guarantee
  `P[∃ θ, |holdoutMean (ℓ θ) − popMean (ℓ θ)| ≥ ε]
    ≤ |Θ| · 2·exp(−2k(ε/B)²)` — the CEHeldout finite-codebook pattern,
  now with the population-risk tie.

## Honest boundaries (pins)

1. **With-replacement surrogate.**  The holdout law is `k` iid uniform
   draws WITH replacement (exactly the product law the concentration
   tower is built on).  A true holdout split samples WITHOUT
   replacement; by Hoeffding (1963) sampling without replacement is
   at least as concentrated, so the surrogate is the weaker honest
   side.  The without-replacement form is NOT formalized here.
2. **Fixed-before-sampling premise.**  `holdout_unbiased` and
   `holdout_concentration` hold for `f` constant in the sample; the
   selection-bias theorems show a data-dependent choice breaks them.
3. **No external-world claims.**  Uniformity over the finite
   population is the only probabilistic assumption; nothing is claimed
   about i.i.d. data-generating processes or deployment risk.
-/

set_option linter.style.header false

open Finset Real

namespace Hagi.Theory.HoldoutRisk

open Hagi.Probability

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

/-! ## The finite-population setup -/

/-- Uniform density over the finite population. -/
noncomputable def popDens (_ω : Ω) : ℝ := (Fintype.card Ω : ℝ)⁻¹

theorem popDens_sum : ∑ ω : Ω, popDens (Ω := Ω) ω = 1 := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
    mod_cast Fintype.card_ne_zero (α := Ω)
  simp only [popDens, Finset.sum_const, Finset.card_univ]
  simp [hn]

/-- The `k`-fold holdout law (uniform product) is a probability
system in the `CertifiedEstimator` sense. -/
theorem popIsProb {k : ℕ} :
    IsProbSys (fun _ : Fin k => popDens (Ω := Ω)) := by
  intro _
  exact ⟨fun _ => inv_nonneg.mpr (Nat.cast_nonneg _), popDens_sum⟩

/-- Population (true) risk of a fixed model: the uniform mean. -/
noncomputable def popMean (f : Ω → ℝ) : ℝ := (∑ ω, f ω) / (Fintype.card Ω : ℝ)

/-- Holdout estimate: the mean loss over the `k` sampled points. -/
noncomputable def holdoutMean {k : ℕ} (f : Ω → ℝ) (ωs : Fin k → Ω) : ℝ :=
  (∑ i, f (ωs i)) / (k : ℝ)

omit [Nonempty Ω] in
/-- Every coordinate mean of the uniform product system is the
population mean. -/
theorem coordMean_eq_popMean {k : ℕ} (f : Ω → ℝ) (i : Fin k) :
    coordMean (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) i
      = popMean f := by
  simp only [coordMean, popMean, popDens]
  rw [div_eq_inv_mul, Finset.mul_sum]

omit [Nonempty Ω] in
theorem coordSum_eq_popMean {k : ℕ} (f : Ω → ℝ) :
    ∑ i : Fin k, coordMean (fun _ : Fin k => popDens (Ω := Ω))
        (fun _ => f) i = ((k : ℕ) : ℝ) * popMean f := by
  rw [Finset.sum_congr rfl (fun i _ => coordMean_eq_popMean f i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-! ## (a) Unbiasedness for a fixed model -/

/-- **Holdout unbiasedness** (fixed model): under the uniform holdout
law, the expected holdout estimate equals the population risk. -/
theorem holdout_unbiased {k : ℕ} (hk : 0 < k) (f : Ω → ℝ) :
    prodE (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => holdoutMean f ωs) = popMean f := by
  have hkr : ((k : ℕ) : ℝ) ≠ 0 := mod_cast ne_of_gt hk
  have hmarg : ∑ ωs : Fin k → Ω,
      prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs * ∑ i, f (ωs i)
      = ∑ i : Fin k, coordMean
        (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) i := by
    have hexpand : ∀ ωs : Fin k → Ω,
        prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs * ∑ i, f (ωs i)
          = ∑ i, prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs
              * f (ωs i) := fun ωs => Finset.mul_sum _ _ _
    rw [Finset.sum_congr rfl (fun ωs _ => hexpand ωs), Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact marginal_prodE (fun _ : Fin k => popDens (Ω := Ω)) popIsProb i f
  calc prodE (fun _ : Fin k => popDens (Ω := Ω))
          (fun ωs => holdoutMean f ωs)
      = ∑ ωs : Fin k → Ω,
          prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs
            * ((∑ i, f (ωs i)) / (k : ℝ)) := rfl
    _ = (∑ ωs : Fin k → Ω,
          prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs
            * ∑ i, f (ωs i)) / (k : ℝ) := by
        rw [Finset.sum_congr rfl (fun ωs _ => (mul_div_assoc
          (prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs)
          (∑ i, f (ωs i)) ((k : ℝ))).symm)]
        exact (Finset.sum_div (Finset.univ)
          (fun ωs => prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs
            * ∑ i, f (ωs i)) ((k : ℝ))).symm
    _ = (((k : ℕ) : ℝ) * popMean f) / (k : ℝ) := by
        rw [hmarg, coordSum_eq_popMean]
    _ = popMean f := by simp [hkr]

/-! ## (b) Concentration for a fixed model -/

omit [Nonempty Ω] in
/-- The deviation event implies the two-sided centered event of
`hoeffding_two_sided`: `|holdout − pop| ≥ ε` forces the centered sum
outside `[−kε, kε]` (only this direction is needed for the bound). -/
theorem holdout_dev_imp {k : ℕ} (hk : 0 < k) (f : Ω → ℝ) (eps : ℝ)
    (ωs : Fin k → Ω) (hdev : eps ≤ |holdoutMean f ωs - popMean f|) :
    ((k : ℝ) * eps ≤ centeredSum (fun _ : Fin k => popDens (Ω := Ω))
            (fun _ => f) ωs
        ∨ centeredSum (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
            ≤ -((k : ℝ) * eps)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hkey : holdoutMean f ωs - popMean f
      = centeredSum (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
          / (k : ℝ) := by
    unfold holdoutMean centeredSum
    rw [coordSum_eq_popMean]
    field_simp
  have habs : eps * (k : ℝ) ≤ |centeredSum
      (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs| := by
    rw [hkey, abs_div, abs_of_pos hkpos, le_div_iff₀ hkpos] at hdev
    exact hdev
  by_cases hcs : 0 ≤ centeredSum
        (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
  · exact Or.inl (by
      rw [abs_of_nonneg hcs] at habs
      linarith)
  · exact Or.inr (by
      have hn : centeredSum (fun _ : Fin k => popDens (Ω := Ω))
          (fun _ => f) ωs < 0 := lt_of_not_ge hcs
      rw [abs_of_neg hn] at habs
      linarith)

/-- **Holdout concentration** (fixed model, [0,1] losses): the
two-sided Hoeffding guarantee at the canonical exponent. -/
theorem holdout_concentration {k : ℕ} (hk : 0 < k) {f : Ω → ℝ}
    (hf : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1) (eps : ℝ) (heps : 0 < eps) :
    prodPq (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => eps ≤ |holdoutMean f ωs - popMean f|)
      ≤ concConfidenceTwoSided eps k := by
  have hmono := prodPq_mono (fun _ : Fin k => popDens (Ω := Ω)) popIsProb
    (fun ωs => eps ≤ |holdoutMean f ωs - popMean f|)
    (fun ωs => ((k : ℝ) * eps ≤ centeredSum
        (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
      ∨ centeredSum (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
        ≤ -((k : ℝ) * eps)))
    (fun ωs hdev => holdout_dev_imp hk f eps ωs hdev)
  unfold concConfidenceTwoSided concConfidence
  have hconv : prodPq (fun _ : Fin k => popDens (Ω := Ω))
      (fun ωs => ((k : ℝ) * eps ≤ centeredSum
          (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
        ∨ centeredSum (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
          ≤ -((k : ℝ) * eps)))
    = prodPq (fun _ : Fin k => popDens (Ω := Ω))
      (fun ω => ((k : ℝ) * eps ≤ centeredSum
          (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ω
        ∨ centeredSum (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ω
          ≤ -((k : ℝ)) * eps)) := by
    refine prodPq_iff _ _ _ fun ωs => ?_
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
  exact hmono.trans ((le_of_eq hconv).trans
    (hoeffding_two_sided (fun _ : Fin k => popDens (Ω := Ω)) popIsProb
      (fun _ => f) (fun _ _ => hf _) hk eps heps))

/-! ## (c) Selection bias: the honesty warning (negative theorem) -/
/-! ## (c) Selection bias: the honesty warning (negative theorem) -/

/-- The two-point counterexample loss: model `j` (of `Fin 2`) has zero
loss on point `j` and unit loss on the other point. -/
def twoPointLoss (j ω : Fin 2) : ℝ := if ω = j then 0 else 1

/-- **Population risk of every counterexample model is 1/2** — no
model in the two-point codebook beats chance on the population. -/
theorem selection_bias_pop_eq_half (j : Fin 2) :
    popMean (twoPointLoss j) = 1 / 2 := by
  unfold popMean twoPointLoss
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  rw [hcard]
  fin_cases j
  all_goals simp [Fin.sum_univ_two]

/-- **Selection bias breaks unbiasedness**: with `k = 1`, choosing the
model AFTER viewing the holdout point (`sel ωs = ωs 0`, which
minimizes the holdout loss — the selected model has zero loss on the
observed point) makes the holdout risk of the selected model
identically ZERO, while its population risk is 1/2
(`selection_bias_pop_eq_half`).  The expectation of the data-dependent
holdout estimate is `E[holdoutRisk θ*] = 0 ≠ 1/2 = E[popRisk θ*]` —
maximal bias; the fixed-`f` premise of `holdout_unbiased` is
essential. -/
theorem selection_bias_holdout_eq_zero (ωs : Fin 1 → Fin 2) :
    holdoutMean (twoPointLoss (ωs 0)) ωs = 0 := by
  unfold holdoutMean twoPointLoss
  simp

/-- The full negative statement: the expected holdout risk of the
holdout-selected model is ZERO while every model's population risk is
ONE HALF — unbiasedness fails by the maximal margin 1/2. -/
theorem selection_bias_expected_gap :
    prodE (fun _ : Fin 1 => popDens (Ω := Fin 2))
        (fun ωs => holdoutMean (twoPointLoss (ωs 0)) ωs) = 0
      ∧ ∀ j : Fin 2, popMean (twoPointLoss j) = 1 / 2 :=
  ⟨by
    unfold prodE
    refine Finset.sum_eq_zero fun ωs _ => ?_
    show prodDens (fun _ : Fin 1 => popDens (Ω := Fin 2)) ωs
      * holdoutMean (twoPointLoss (ωs 0)) ωs = 0
    rw [selection_bias_holdout_eq_zero, mul_zero],
  fun j => selection_bias_pop_eq_half j⟩

/-! ## (d) Uniform guarantee over a finite codebook -/

omit [Nonempty Ω] in
/-- Both the holdout and the population mean scale linearly, so the
deviation event for `g` at radius `eps` IS the deviation event for
`g / B` at radius `eps / B`. -/
theorem holdout_dev_rescale {k : ℕ} {B : ℝ} (hB : 0 < B) (g : Ω → ℝ)
    (ωs : Fin k → Ω) (eps : ℝ) :
    (eps ≤ |holdoutMean g ωs - popMean g|
      ↔ eps / B ≤ |holdoutMean (fun ω => g ω / B) ωs
          - popMean (fun ω => g ω / B)|) := by
  have h1 : holdoutMean (fun ω => g ω / B) ωs
      = holdoutMean g ωs / B := by
    rw [holdoutMean, holdoutMean, ← Finset.sum_div, div_div, div_div,
      mul_comm B ((k : ℝ))]
  have h2 : popMean (fun ω => g ω / B) = popMean g / B := by
    rw [popMean, popMean, ← Finset.sum_div, div_div, div_div,
      mul_comm B ((Fintype.card Ω : ℝ))]
  have hsub : holdoutMean g ωs / B - popMean g / B
      = (holdoutMean g ωs - popMean g) / B :=
    div_sub_div_same (holdoutMean g ωs) (popMean g) B
  rw [h1, h2, hsub, abs_div, abs_of_pos hB]
  constructor
  · intro h
    rw [le_div_iff₀ hB, mul_comm, mul_div_cancel₀ _ hB.ne']
    exact h
  · intro h
    have h' := (le_div_iff₀ hB).mp h
    rwa [mul_comm, mul_div_cancel₀ _ hB.ne'] at h'

/-- **Uniform holdout guarantee for a finite codebook**: losses bounded
by `B > 0`, codebook `Θ` fixed before sampling.  The CEHeldout
finite-codebook pattern, now with the population-risk tie: every model
in the codebook is simultaneously within `eps` of its population risk
except with probability at most `|Θ| · 2·exp(−2k(eps/B)²)`. -/
theorem holdout_uniform_codebook {Θ : Type} [Fintype Θ] {k : ℕ} (hk : 0 < k)
    (ℓ : Θ → Ω → ℝ) {B : ℝ} (hB : 0 < B)
    (hℓ : ∀ θ ω, 0 ≤ ℓ θ ω ∧ ℓ θ ω ≤ B) (eps : ℝ) (heps : 0 < eps) :
    prodPq (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => ∃ θ : Θ,
          eps ≤ |holdoutMean (ℓ θ) ωs - popMean (ℓ θ)|)
      ≤ (Fintype.card Θ : ℝ) * concConfidenceTwoSided (eps / B) k := by
  -- mono: the raw exist-event implies the scaled exist-event
  have himp : ∀ ωs : Fin k → Ω,
      (∃ θ : Θ, eps ≤ |holdoutMean (ℓ θ) ωs - popMean (ℓ θ)|)
        → ∃ θ : Θ, eps / B ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
            - popMean (fun ω => ℓ θ ω / B)| :=
    fun ωs ⟨θ, hθ⟩ => ⟨θ, (holdout_dev_rescale hB (ℓ θ) ωs eps).mp hθ⟩
  have hmono := prodPq_mono (fun _ : Fin k => popDens (Ω := Ω)) popIsProb
    (fun ωs => ∃ θ : Θ, eps ≤ |holdoutMean (ℓ θ) ωs - popMean (ℓ θ)|)
    (fun ωs => ∃ θ : Θ, eps / B ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
        - popMean (fun ω => ℓ θ ω / B)|)
    himp
  -- bridge to the ∃ ∈ univ form of the union bound
  have hmono2 := prodPq_mono (fun _ : Fin k => popDens (Ω := Ω)) popIsProb
    (fun ωs => ∃ θ : Θ, eps / B ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
        - popMean (fun ω => ℓ θ ω / B)|)
    (fun ωs => ∃ θ ∈ (Finset.univ : Finset Θ), eps / B
        ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
            - popMean (fun ω => ℓ θ ω / B)|)
    (fun ωs ⟨θ, hθ⟩ => ⟨θ, Finset.mem_univ θ, hθ⟩)
  have hunion := prodPq_union_finset
    (fun _ : Fin k => popDens (Ω := Ω)) popIsProb (Finset.univ : Finset Θ)
    (fun θ ωs => eps / B
      ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
          - popMean (fun ω => ℓ θ ω / B)|)
  -- per-model concentration at the scaled radius
  have hbound : ∀ θ : Θ,
      prodPq (fun _ : Fin k => popDens (Ω := Ω))
          (fun ωs => eps / B
            ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
                - popMean (fun ω => ℓ θ ω / B)|)
        ≤ concConfidenceTwoSided (eps / B) k := by
    intro θ
    have hunit : ∀ ω : Ω, 0 ≤ ℓ θ ω / B ∧ ℓ θ ω / B ≤ 1 := by
      intro ω
      constructor
      · exact div_nonneg (hℓ θ ω).1 hB.le
      · exact (div_le_one hB).2 (hℓ θ ω).2
    exact holdout_concentration (f := fun ω => ℓ θ ω / B) hk hunit
      (eps / B) (div_pos heps hB)
  calc prodPq (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => ∃ θ : Θ,
          eps ≤ |holdoutMean (ℓ θ) ωs - popMean (ℓ θ)|)
      ≤ prodPq (fun _ : Fin k => popDens (Ω := Ω))
          (fun ωs => ∃ θ : Θ, eps / B
            ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
                - popMean (fun ω => ℓ θ ω / B)|) := hmono
    _ ≤ prodPq (fun _ : Fin k => popDens (Ω := Ω))
          (fun ωs => ∃ θ ∈ (Finset.univ : Finset Θ), eps / B
            ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
                - popMean (fun ω => ℓ θ ω / B)|) := hmono2
    _ ≤ ∑ θ : Θ, prodPq (fun _ : Fin k => popDens (Ω := Ω))
          (fun ωs => eps / B
            ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
                - popMean (fun ω => ℓ θ ω / B)|) := hunion
    _ ≤ ∑ θ : Θ, concConfidenceTwoSided (eps / B) k :=
          Finset.sum_le_sum fun θ _ => hbound θ
    _ = (Fintype.card Θ : ℝ) * concConfidenceTwoSided (eps / B) k := by
          rw [Finset.sum_const, Finset.card_univ]
          simp

end Hagi.Theory.HoldoutRisk
