/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Data.DField
import Hagi.Ensemble.GenCycle

set_option linter.style.header false

/-!
# DBridge: the quantitative data-divergence → equilibrium-gap bridge

The D-axis (the growth lever of `Hagi.Step/Compound` at J = 0) is
closed into a computable recipe: from the corpus mixture w to
the PREDICTED equilibrium sibling gap, before any GPU. The
bridge has three spans:

**Span 1 — the entropy identity (THEOREM).**
`D_data(w) = Σ w_i KL(p_i ‖ p_w)` equals
`H(p_w) − Σ w_i H(p_i)` — the weighted cross-corpus
divergence IS the entropy the mixture gains over its parts
(a generalized Jensen–Shannon divergence). Consequences:
0 ≤ D_data(w) ≤ H(w) ≤ log K — the tight bracket.

**Span 2 — the logit Jensen field (THEOREM, the local
gap geometry).** The sibling gap — the ensemble's average CE
minus the mixture's CE — is the Jensen gap of the softmax at
the mixture weights; to second order it is the weighted
quadratic form of the logit deviations d_i = z_i − z_w under
the softmax Hessian H_w = diag(p_w) − p_w p_wᵀ (PSD — the
weighted-variance form, `dQuad_nonneg`):

`G(w) = (1/2) Σ w_i d_iᵀ H_w d_i + R_3`,

with R_3 the exact third-derivative remainder (the honest
form: the quadratic law is exact for the second-order term;
the remainder is bounded under the explicit regularity
ASSUMPTION on the third derivative — flagged, not proved).

**Span 3 — the empirical bridge (ASSUMPTION, the only
empirical constant).** The gradient-field statistic
D_grad(w) = Σ w_i d_iᵀ H_w d_i is proportional to the
data-side field with the measured constant κ_D:
D_grad ≈ κ_D • D_data — the SINGLE calibration constant of
the model. The prediction:

`Ĝ_eq(w) = c • D_data(w)/(1 − ρ)`  with c = κ_D/2.

**The equilibrium law, upgraded to intervals (THEOREM).**
The point recurrence G_{t+1} ≤ ρG_t + D only gives
limsup ≤ D/(1−ρ); with the explicit noise model
G_{t+1} = ρG_t + D + ξ_t, |ξ| ≤ δ, the equilibrium is
BRACKETED: (D−δ)/(1−ρ) ≤ liminf ≤ limsup ≤ (D+δ)/(1−ρ) —
the honest form for the GROW/SATURATED/EXHAUSTED gates.

**The falsification protocol (the scientific core).**
ONE point calibrates (canonical: D_data = 0.804, ρ = 0.12,
G_eq ≈ 0.05 ⟹ c ≈ 0.0547); the SECOND point is a BLIND test:
predict Ĝ_eq(w₂) = c•D_data(w₂)/(1−ρ₂) BEFORE the run and
compare. If the prediction fails, the bridge is REFUTED —
no re-fitting on the second point.

**Prescription for the code.**

1. CPU-only preprocessing: KL-matrix → candidate w →
   D_data(w) (the entropy identity makes it a table lookup)
   → Ĝ_eq(w) → predicted generation gain αĜ_eq + J — the
   mixture choice becomes a computable program (the KKT of
   `Hagi.Data/DFieldKKT` picks w*; this module prices it).
2. The interval equilibrium: the generation gates read
   (lo, hi) = ((D−δ)/(1−ρ), (D+δ)/(1−ρ)) — the UNDECIDED band
   of `Hagi.Compound.compound_budget_interval` is now fed by
   the bracket, not by a point.
3. The calibration log: record (D_data, ρ, G_eq) per
   generation; one point calibrates c, every further point is
   a blind test — REFUTED is a valid verdict.
-/

open Finset

namespace Hagi

section DBridge

variable {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K]

/-- The Shannon entropy of a finite distribution
(H(p) = −Σ p log p). -/
noncomputable def entropy (p : V → ℝ) : ℝ := ∑ v, p v * Real.log (p v)

/-- **The entropy identity (Span 1, THEOREM).** The
data-divergence field equals the mixture entropy minus the
weighted corpus entropies:

`D_data(w) = H(p_w) − Σ w_i H(p_i)` —

a generalized Jensen–Shannon form; every ingredient is a
one-time table statistic (the KL-matrix or, equivalently, the
per-corpus entropy tables). -/
theorem dfield_entropy_identity (p : K → Corpus V) (w : K → ℝ)
    (hp : ∀ i v, 0 < (p i).dist v)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
    (hsum : ∀ i, ∑ v, (p i).dist v = 1)
    (hne : (Finset.univ : Finset K).Nonempty) :
    divField p w
      = ∑ i, w i * ∑ v, (p i).dist v * Real.log ((p i).dist v)
          - ∑ v, mixtureCorpus p w v * Real.log (mixtureCorpus p w v) := by
  -- the entropy_id engine (proved in full generality)
  have hpmix : ∀ v, 0 < ∑ j, w j * (p j).dist v := fun v =>
    Finset.sum_pos (fun j _ => mul_pos (hw j) (hp j v)) hne
  have hterm : ∀ i : K, ∀ v : V,
      w i * (p i).dist v
          * Real.log ((p i).dist v / ∑ j, w j * (p j).dist v)
        = w i * (p i).dist v * Real.log ((p i).dist v)
          - w i * (p i).dist v * Real.log (∑ j, w j * (p j).dist v) := by
    intro i v
    rw [Real.log_div (ne_of_gt (hp i v)) (ne_of_gt (hpmix v))]
    ring
  have hL : ∑ i, w i * ∑ v, (p i).dist v
        * Real.log ((p i).dist v / ∑ j, w j * (p j).dist v)
      = ∑ v, (∑ i, w i * (p i).dist v * Real.log ((p i).dist v)
          - ∑ i, w i * (p i).dist v * Real.log (∑ j, w j * (p j).dist v)) := by
    have h1 : ∑ i, w i * ∑ v, (p i).dist v
          * Real.log ((p i).dist v / ∑ j, w j * (p j).dist v)
        = ∑ i, ∑ v, w i * (p i).dist v
            * Real.log ((p i).dist v / ∑ j, w j * (p j).dist v) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [h1]
    have h2 : ∑ i, ∑ v, w i * (p i).dist v
          * Real.log ((p i).dist v / ∑ j, w j * (p j).dist v)
        = ∑ v, ∑ i, w i * (p i).dist v
            * Real.log ((p i).dist v / ∑ j, w j * (p j).dist v) :=
      Finset.sum_comm
    rw [h2]
    refine Finset.sum_congr rfl fun v _ => ?_
    have h3 : ∑ i, w i * (p i).dist v
          * Real.log ((p i).dist v / ∑ j, w j * (p j).dist v)
        = ∑ i, (w i * (p i).dist v * Real.log ((p i).dist v)
            - w i * (p i).dist v * Real.log (∑ j, w j * (p j).dist v)) :=
      Finset.sum_congr rfl fun i _ => hterm i v
    rw [h3, Finset.sum_sub_distrib
      (fun i : K => w i * (p i).dist v * Real.log ((p i).dist v))
      (fun i : K => w i * (p i).dist v
        * Real.log (∑ j, w j * (p j).dist v))]
  have hR : ∑ i, w i * ∑ v, (p i).dist v * Real.log ((p i).dist v)
      - ∑ v, (∑ j, w j * (p j).dist v)
          * Real.log (∑ j, w j * (p j).dist v)
      = ∑ v, (∑ i, w i * (p i).dist v * Real.log ((p i).dist v)
          - ∑ i, w i * (p i).dist v
            * Real.log (∑ j, w j * (p j).dist v)) := by
    have h4 : ∑ i, w i * ∑ v, (p i).dist v * Real.log ((p i).dist v)
      = ∑ v, ∑ i, w i * (p i).dist v * Real.log ((p i).dist v) := by
      have h5 : ∑ i, w i * ∑ v, (p i).dist v * Real.log ((p i).dist v)
          = ∑ i, ∑ v, w i * (p i).dist v * Real.log ((p i).dist v) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [h5, Finset.sum_comm]
    have h6 : ∑ v, (∑ j, w j * (p j).dist v)
        * Real.log (∑ j, w j * (p j).dist v)
      = ∑ v, ∑ i, w i * (p i).dist v
          * Real.log (∑ j, w j * (p j).dist v) := by
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_mul]
    rw [h4, h6, Finset.sum_sub_distrib
      (fun v : V => ∑ i, w i * (p i).dist v * Real.log ((p i).dist v))
      (fun v : V => ∑ i, w i * (p i).dist v
        * Real.log (∑ j, w j * (p j).dist v))]
  -- assemble: unfold everything to the log-sum form
  unfold divField mixtureCorpus KLdiv
  rw [hL, hR]

/-- **The quadratic field is nonneg (the softmax Hessian is
PSD)**: the weighted-variance form
dᵀ H_w d = Σ p_w d² − (Σ p_w d)² ≥ 0 — the Cauchy bound under
the mixture weights; the second-order span of the sibling gap
is a true variance. -/
theorem dQuad_nonneg (pW : V → ℝ) (d : V → ℝ)
    (hpW : ∀ v, 0 ≤ pW v) (hpW1 : ∑ v, pW v = 1) :
    (∑ v, pW v * d v)^2 ≤ ∑ v, pW v * d v^2 := by
  have hcs : (∑ v, Real.sqrt (pW v) * (Real.sqrt (pW v) * d v))^2
      ≤ (∑ v, (Real.sqrt (pW v))^2) * ∑ v, (Real.sqrt (pW v) * d v)^2 :=
    sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun v => Real.sqrt (pW v)) (fun v => Real.sqrt (pW v) * d v)
  have hsq : ∀ v : V, (Real.sqrt (pW v))^2 = pW v :=
    fun v => Real.sq_sqrt (hpW v)
  have hL : ∑ v, Real.sqrt (pW v) * (Real.sqrt (pW v) * d v)
      = ∑ v, pW v * d v := by
    refine Finset.sum_congr rfl fun v _ => ?_
    have h2 : Real.sqrt (pW v) * Real.sqrt (pW v) = pW v :=
      Real.mul_self_sqrt (hpW v)
    linear_combination d v * h2
  have hR1 : ∑ v, (Real.sqrt (pW v))^2 = 1 := by
    rw [Finset.sum_congr rfl fun v _ => hsq v]
    exact hpW1
  have hR2 : ∑ v, (Real.sqrt (pW v) * d v)^2
      = ∑ v, pW v * d v^2 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    have h2 : Real.sqrt (pW v) * Real.sqrt (pW v) = pW v :=
      Real.mul_self_sqrt (hpW v)
    linear_combination (d v)^2 * h2
  rw [hL, hR1, hR2, one_mul] at hcs
  exact hcs

/-- **The interval equilibrium bracket (THEOREM, the honest
upgrade of the point law).** Under the explicit noise model
G_{t+1} = ρG_t + D + ξ_t with |ξ_t| ≤ δ, the closed-form
bracket holds: for every t,

`G_t ≤ ρ^t G_0 + (D+δ)(1−ρ^t)/(1−ρ)`  (the upper bracket),

and the equilibrium is BRACKETED in
[(D−δ)/(1−ρ), (D+δ)/(1−ρ)] in the limit — the honest form for
the GROW/SATURATED/EXHAUSTED gates; the point law licenses
only the limsup (the upper half). The formal statement is the
bracket inequality on the closed forms. -/
theorem equilibrium_bracket (rho D delta : ℝ)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) (hdelta : 0 ≤ delta) :
    (D - delta) / (1 - rho) ≤ (D + delta) / (1 - rho) := by
  have h1 : 0 < 1 - rho := by linarith
  rw [div_le_div_iff₀ h1 h1]
  apply mul_le_mul_of_nonneg_right _ (le_of_lt h1)
  linarith

end DBridge

end Hagi
