/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.AnytimeValid
import Hagi.Step.StochasticSafeQP
import Mathlib.Probability.Martingale.OptionalStopping
set_option linter.style.header false

/-!
# R93: martingale anytime-valid control (Ville form) + the composed anytime safety theorem

Round-63's honest boundary said: the union-of-geometric skeleton
`anytime_valid_budget` is proven, but the Ville-martingale e-process
form (E[L_τ] ≤ 1 for stopping times) remains open. This module
closes the bounded-stopping-time form of that boundary, using
mathlib's optional stopping theorem
(`MeasureTheory.Submartingale.expected_stoppedValue_mono`), and then
composes the stochastic SafeQP per-step concentration
(`Hagi.Step.StochasticSafeQP`) with the geometric budget into the
roadmap's target anytime-safety theorem.

* `eprocess_stopped_budget` — a nonnegative supermartingale L
  satisfies E[L_τ] ≤ E[L_0] for EVERY bounded stopping time τ
  (optional stopping; the bound is honest about boundedness —
  unbounded τ is left open).
* `ville_supermartingale` — Ville's inequality for nonnegative
  supermartingales over any FINITE horizon n, with the constant
  INDEPENDENT of n (hence anytime-valid):
  Pr[∃ t ≤ n, c ≤ L_t] ≤ E[L_0]/c.  Markov + the stopped process
  at the first crossing of level c, stopped at n.
* `ville_anytime_false_alarm` — the e-process budget corollary:
  E[L_0] ≤ 1 and c = 1/δ gives Pr[∃ t ≤ n, L_t ≥ 1/δ] ≤ δ,
  uniformly in n.
* `anytime_failure_budget` — the union-of-geometric budget over
  failure events (no measurability needed: pure outer union bound).
* `anytime_safety` — the good-event form: measurable certificate
  events whose per-step failure mass obeys the geometric schedule
  δₜ = δ₀·ρᵗ with δ₀/(1−ρ) ≤ δ satisfy
  Pr[∀ t ≤ T, certificate valid] ≥ 1 − δ, uniformly in T.
* `anytime_safety_stochastic` — the roadmap target: each step t
  uses the stochastic SafeQP transfer
  (`stochastic_safeQP_feasibility`) at confidence δₜ = δ₀·ρᵗ;
  then with probability ≥ 1 − δ, at EVERY step t ≤ T, if the
  realized stochastic constraints certify d_t against ĝ, then the
  TRUE gradients satisfy the safety margin inflated by
  ε_noise(δₜ). All empirical conditions inherited as h_emp_*.

**Honest boundaries.** (1) Optional stopping here is for BOUNDED
stopping times (mathlib's `expected_stoppedValue_mono`); the
unbounded-horizon Ville form (sup over all t ∈ ℕ, via monotone
convergence) is left open. (2) `anytime_safety_stochastic` uses
per-step UNCONDITIONAL failure masses (the union-bound skeleton);
the fully conditional (filtration-adapted, e-process-per-step)
composition — where each step's guarantee holds conditionally on
the past, matching the martingale route — is left open. (3) d_t
is a fixed per-step direction (as in StochasticSafeQP); a
data-dependent measurable selection d_t*(ω) is not formalized.
-/

open Finset Real MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Hagi

section Ville

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝒢 : Filtration ℕ m0}

/-- **The e-process stopped budget (optional stopping, bounded
stopping times)**: if L is a supermartingale w.r.t. the filtration
𝒢, then for any stopping time τ bounded by N, the expected
stopped value is at most the initial expectation E[L_0]. With
E[L_0] ≤ 1 this is the e-process budget E[L_τ] ≤ 1 — the
Ville-martingale skeleton promised in R63, for bounded τ.

Proof: `Supermartingale.neg` turns L into a submartingale −L;
mathlib's optional stopping (`expected_stoppedValue_mono`) applied
between the constant stopping time 0 and τ gives
E[(−L)_0] ≤ E[(−L)_τ], i.e. E[L_τ] ≤ E[L_0]. -/
theorem eprocess_stopped_budget {L : ℕ → Ω → ℝ} (hL : Supermartingale L 𝒢 μ)
    {τ : Ω → ℕ∞} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hτbdd : ∀ ω, τ ω ≤ N) :
    μ[stoppedValue L τ] ≤ μ[L 0] := by
  have hsub : Submartingale (-L) 𝒢 μ := hL.neg
  have h := hsub.expected_stoppedValue_mono (isStoppingTime_const 𝒢 0) hτ
    (fun _ => zero_le) (fun ω => hτbdd ω)
  rw [stoppedValue_const] at h
  have h' : -μ[L 0] ≤ -μ[stoppedValue L τ] := by
    have h1 : ∫ (x : Ω), (-L) 0 x ∂μ = -μ[L 0] := by
      simp only [Pi.neg_apply, integral_neg]
    have h2 : ∫ (x : Ω), stoppedValue (-L) τ x ∂μ = -μ[stoppedValue L τ] := by
      simp only [stoppedValue, Pi.neg_apply, integral_neg]
    rw [h1, h2] at h
    exact h
  linarith

/-- **Ville's maximal inequality for nonnegative supermartingales
(finite horizon, constant independent of the horizon)**: for a
nonnegative supermartingale L and any level c > 0,

  Pr[ ∃ t ≤ n, c ≤ L_t ] ≤ E[L_0] / c.

The bound does not depend on n — this is what makes it
anytime-valid: it holds uniformly over every finite horizon.

Proof: let τ be the first time L crosses level c, stopped at n
(τ = the least t ≤ n with c ≤ L_t, or n if none). τ is a bounded
stopping time (first-crossage sets are in the filtration since L
is adapted); on the crossing event the stopped value is ≥ c, so
Markov's inequality (`setIntegral_ge_of_const_le_real`) plus
`eprocess_stopped_budget` gives c·Pr[cross] ≤ E[L_τ] ≤ E[L_0]. -/
theorem ville_supermartingale {L : ℕ → Ω → ℝ} (hL : Supermartingale L 𝒢 μ)
    (hLnn : 0 ≤ L) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1), c ≤ L t ω} ≤ μ[L 0] / c := by
  classical
  -- the crossing predicate and the (bounded) first-crossing stopping time
  set P : Ω → ℕ → Prop := fun ω t => t ≤ n ∧ c ≤ L t ω with hPdef
  set τ : Ω → ℕ∞ := fun ω =>
    if h : ∃ t, P ω t then ((Nat.find h : ℕ) : ℕ∞) else (n : ℕ∞) with hτdef
  -- τ is bounded by n
  have hτbdd : ∀ ω, τ ω ≤ (n : ℕ∞) := by
    intro ω
    simp only [hτdef]
    split
    · next h => exact_mod_cast (Nat.find_spec h).1
    · exact le_rfl
  -- τ is a stopping time: {τ ≤ k} splits into the (≤ k)-crossage union
  -- and the no-crossage ∩ {n ≤ k} corner
  have hτstop : IsStoppingTime 𝒢 τ := by
    intro k
    -- the (≤ k)-crossage union: finite union of filtration-measurable sets
    have hmeasfirst : MeasurableSet[𝒢 k] {ω | ∃ t, t ≤ k ∧ P ω t} := by
      have hrw : {ω | ∃ t, t ≤ k ∧ P ω t}
          = ⋃ t ∈ Finset.range (k + 1), {ω | P ω t} := by
        ext ω
        simp only [Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨t, htk, ht⟩; exact ⟨t, htk, ht⟩
        · rintro ⟨t, htk, ht⟩; exact ⟨t, htk, ht⟩
      rw [hrw]
      refine Finset.measurableSet_biUnion _ ?_
      intro t ht
      by_cases htn : t ≤ n
      · have hset : {ω | P ω t} = {ω | c ≤ L t ω} := by ext ω; simp [hPdef, htn]
        rw [hset]
        exact (𝒢.mono' (by simpa using ht)) _
          (measurableSet_le measurable_const (hL.stronglyMeasurable t).measurable)
      · have hset : {ω | P ω t} = ∅ := by ext ω; simp [hPdef, htn]
        rw [hset]
        exact @MeasurableSet.empty Ω (𝒢 k)
    -- the no-crossage corner: in 𝒢 n ⊆ 𝒢 k, or the intersection is empty
    have hmeassecond :
        MeasurableSet[𝒢 k] ({ω | ¬ ∃ t, P ω t} ∩ {ω | (n : ℕ∞) ≤ (k : ℕ∞)}) := by
      by_cases hnk : n ≤ k
      · have huk : {ω : Ω | (n : ℕ∞) ≤ (k : ℕ∞)} = Set.univ := by
          ext ω; simp [ hnk]
        rw [huk, Set.inter_univ]
        have hnc : {ω | ¬ ∃ t, P ω t}
            = (⋃ t ∈ Finset.range (n + 1), {ω | c ≤ L t ω})ᶜ := by
          ext ω
          simp only [Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff,
            Set.mem_ofPred_eq, not_exists, not_and, hPdef]
        rw [hnc]
        exact (𝒢.mono' hnk) _ (MeasurableSet.compl (Finset.measurableSet_biUnion _ fun t ht =>
          (𝒢.mono' (by simpa using ht)) _
            (measurableSet_le measurable_const (hL.stronglyMeasurable t).measurable)))
      · have huk : {ω : Ω | (n : ℕ∞) ≤ (k : ℕ∞)} = ∅ := by
          ext ω; simp [ hnk]
        rw [huk, Set.inter_empty]
        exact @MeasurableSet.empty Ω (𝒢 k)
    have hmem : {ω | τ ω ≤ (k : ℕ∞)}
        = {ω | ∃ t, t ≤ k ∧ P ω t} ∪ ({ω | ¬ ∃ t, P ω t} ∩ {ω | (n : ℕ∞) ≤ (k : ℕ∞)}) := by
      ext ω
      simp only [hτdef, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff]
      by_cases hex : ∃ t, P ω t
      · rw [dite_eq_left hex, ENat.natCast_le_natCast, Nat.find_le_iff hex]
        constructor
        · exact Or.inl
        · rintro (⟨t, htk, ht⟩ | h)
          · exact ⟨t, htk, ht⟩
          · exact absurd hex h.1
      · rw [dite_eq_right hex]
        constructor
        · intro h
          exact Or.inr ⟨hex, h⟩
        · rintro (⟨t, htk, ht⟩ | ⟨hex', hnk⟩)
          · exact absurd ⟨t, ht⟩ hex
          · exact hnk
    exact hmem ▸ hmeasfirst.union hmeassecond
  -- on the crossing event the stopped value is at least c
  have hcross : ∀ ω ∈ {ω | ∃ t ∈ Finset.range (n + 1), c ≤ L t ω},
      c ≤ stoppedValue L τ ω := by
    rintro ω ⟨t, htmem, ht⟩
    have hex : ∃ s, P ω s := ⟨t, by simpa using Finset.mem_range.mp htmem, ht⟩
    have hval : τ ω = ((Nat.find hex : ℕ) : ℕ∞) := by simp [hτdef, hex]
    change c ≤ L ((τ ω).untopA) ω
    rw [hval]
    have hun : (((Nat.find hex : ℕ) : ℕ∞)).untopA = Nat.find hex :=
      untopD_coe_enat (Classical.arbitrary ℕ) _
    rw [hun]
    exact (Nat.find_spec hex).2
  -- the stopped value is nonnegative and integrable
  have hSVnn : ∀ ω, 0 ≤ stoppedValue L τ ω := fun ω => hLnn _ _
  have hint : Integrable (stoppedValue L τ) μ := by
    have hsub : Submartingale (-L) 𝒢 μ := hL.neg
    have heq : stoppedValue L τ = fun ω => -(stoppedValue (-L) τ ω) := by
      funext ω; simp only [stoppedValue, Pi.neg_apply, neg_neg]
    rw [heq]
    exact (hsub.integrable_stoppedValue hτstop hτbdd).neg
  -- Markov on the crossing set: c · Pr[cross] ≤ ∫_cross L_τ
  have hMeasA : MeasurableSet {ω | ∃ t ∈ Finset.range (n + 1), c ≤ L t ω} := by
    have hE : {ω | ∃ t ∈ Finset.range (n + 1), c ≤ L t ω}
        = ⋃ t ∈ Finset.range (n + 1), {ω | c ≤ L t ω} := by
      ext ω; simp
    rw [hE]
    exact Finset.measurableSet_biUnion _ fun t _ =>
      measurableSet_le measurable_const
        (fun s hs => (𝒢.le' t) _ ((hL.stronglyMeasurable t).measurable hs))
  have hM := setIntegral_ge_of_const_le_real
    (s := {ω | ∃ t ∈ Finset.range (n + 1), c ≤ L t ω})
    hMeasA (measure_ne_top _ _) hcross hint.integrableOn
  -- ∫_cross L_τ ≤ ∫ L_τ ≤ E[L_0] (optional stopping)
  have hMono : ∫ ω in {ω | ∃ t ∈ Finset.range (n + 1), c ≤ L t ω}, stoppedValue L τ ω ∂μ
      ≤ μ[stoppedValue L τ] :=
    setIntegral_le_integral hint (ae_of_all μ hSVnn)
  have hbud := eprocess_stopped_budget hL hτstop hτbdd
  rw [le_div_iff₀ hc]
  nlinarith [hM, hMono, hbud]


/-- **The anytime false-alarm bound (Ville, e-process budget form)**:
a nonnegative supermartingale likelihood ratio L with E[L_0] ≤ 1
gives, at level δ ∈ (0,1),

  Pr[ ∃ t ≤ n, L_t ≥ 1/δ ] ≤ δ

for EVERY horizon n at once (the constant does not depend on n) —
anytime validity without any correction beyond the e-process
budget itself. -/
theorem ville_anytime_false_alarm {L : ℕ → Ω → ℝ} (hL : Supermartingale L 𝒢 μ)
    (hLnn : 0 ≤ L) (hL0 : μ[L 0] ≤ 1) (n : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1), delta⁻¹ ≤ L t ω} ≤ delta := by
  have hV := ville_supermartingale hL hLnn n (inv_pos.mpr hdelta)
  have hdiv : μ[L 0] / delta⁻¹ ≤ delta := by
    rw [div_inv_eq_mul]
    nlinarith [hL0, hdelta.le]
  exact le_trans hV hdiv

end Ville

section Composition

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The union-of-geometric budget over failure events** (no
measurability needed — a pure outer union bound): if the
per-step failure events Bad t have masses obeying the geometric
schedule δₜ = δ₀·ρᵗ (ρ < 1), the total failure mass over ANY
horizon T is at most δ₀/(1−ρ), uniformly in T. This is
`anytime_valid_budget` (R63) applied to measures. -/
theorem anytime_failure_budget (delta0 rho : ℝ) (hdelta0 : 0 ≤ delta0) (hrho : 0 ≤ rho)
    (hrho1 : rho < 1) (Bad : ℕ → Set Ω)
    (h_step : ∀ t, μ.real (Bad t) ≤ delta0 * rho ^ t) (T : ℕ) :
    μ.real (⋃ t ∈ Finset.range (T + 1), Bad t) ≤ delta0 / (1 - rho) := by
  calc μ.real (⋃ t ∈ Finset.range (T + 1), Bad t)
      ≤ ∑ t ∈ Finset.range (T + 1), μ.real (Bad t) :=
        measureReal_biUnion_finset_le _ Bad
    _ ≤ ∑ t ∈ Finset.range (T + 1), delta0 * rho ^ t :=
        Finset.sum_le_sum (fun t _ => h_step t)
    _ ≤ delta0 / (1 - rho) :=
        anytime_valid_budget delta0 rho (T + 1) hdelta0 hrho hrho1
          (fun n => delta0 * rho ^ n) (fun n => rfl)

/-- **The anytime safety theorem (the roadmap's target shape)**:
if each step t has a measurable certificate event Good t whose
failure mass obeys the geometric schedule δₜ = δ₀·ρᵗ, and the
geometric budget δ₀/(1−ρ) fits the global δ, then with
probability ≥ 1 − δ EVERY certificate up to any horizon T is
valid — uniformly in T:

  Pr[ ∀ t ≤ T, certificate valid at t ] ≥ 1 − δ.

This composes per-step stochastic guarantees (e.g. the SafeQP
concentration of `Hagi.Step.StochasticSafeQP`) with the
union-of-geometric budget: no multiple-testing correction beyond
the schedule itself. -/
theorem anytime_safety (delta0 rho : ℝ) (hdelta0 : 0 ≤ delta0) (hrho : 0 ≤ rho)
    (hrho1 : rho < 1) (Good : ℕ → Set Ω) (hGood : ∀ t, MeasurableSet (Good t))
    (h_step : ∀ t, μ.real (Good t)ᶜ ≤ delta0 * rho ^ t)
    (delta : ℝ) (h_budget : delta0 / (1 - rho) ≤ delta) (T : ℕ) :
    μ.real {ω | ∀ t ∈ Finset.range (T + 1), ω ∈ Good t} ≥ 1 - delta := by
  have hBig : MeasurableSet {ω | ∀ t ∈ Finset.range (T + 1), ω ∈ Good t} := by
    have hE : {ω | ∀ t ∈ Finset.range (T + 1), ω ∈ Good t}
        = ⋂ t ∈ Finset.range (T + 1), Good t := by ext ω; simp
    rw [hE]
    exact Finset.measurableSet_biInter _ fun t _ => hGood t
  have hcompl : ({ω | ∀ t ∈ Finset.range (T + 1), ω ∈ Good t} : Set Ω)ᶜ
      = ⋃ t ∈ Finset.range (T + 1), (Good t)ᶜ := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range,
      not_forall]
  have hbad := anytime_failure_budget delta0 rho hdelta0 hrho hrho1
    (fun t => (Good t)ᶜ) h_step T
  have h1 : μ.real ({ω | ∀ t ∈ Finset.range (T + 1), ω ∈ Good t} : Set Ω)ᶜ
      = 1 - μ.real {ω | ∀ t ∈ Finset.range (T + 1), ω ∈ Good t} := by
    rw [measureReal_compl hBig, probReal_univ]
  rw [hcompl] at h1
  linarith


section Stochastic

open InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {K : Type*} [Fintype K] [Nonempty K]

/-- **The composed anytime safety theorem (roadmap §9 target)**:
the controller runs stochastic SafeQP steps; step t certifies the
direction d_t against the minibatch gradients ĝ_{t,i} with
budgets ε_{t,i} at confidence δₜ = δ₀·ρᵗ (the geometric
anytime-valid schedule, δ₀/(1−ρ) ≤ δ). Then, with probability
≥ 1 − δ, at EVERY step t ≤ T (uniformly in T): whenever the
stochastic constraints certify d_t (the premise the stochastic
QP enforces by construction), the TRUE gradients satisfy the
safety margin inflated by the explicit noise term

  ε_noise(δₜ) = σ·‖d_t‖·√(2·log(|K|/δₜ)/m_t).

Per step this is `stochastic_safeQP_feasibility` (R92); the
"every step at once" is `anytime_safety` with the geometric
budget. All statistical conditions are inherited as h_emp_*
hypotheses, per step. -/
theorem anytime_safety_stochastic (m : ℕ → ℕ) (hm : ∀ t, 0 < m t)
    (g : ℕ → K → X) (d : ℕ → X) (hd : ∀ t, d t ≠ 0)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (xi : ∀ t, K → Fin (m t) → Ω → X)
    (h_emp_noise_meas : ∀ t i j, Measurable (fun ω => ⟪xi t i j ω, d t⟫_ℝ))
    (h_emp_noise_zero : ∀ t i j, μ[fun ω => ⟪xi t i j ω, d t⟫_ℝ] = 0)
    (h_emp_noise_indep :
      ∀ t i, iIndepFun (fun j : Fin (m t) => fun ω => ⟪xi t i j ω, d t⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ t i j ω, ‖xi t i j ω‖ ≤ sigma)
    (eps : ℕ → K → ℝ)
    (delta0 rho : ℝ) (hdelta0 : 0 < delta0) (hrho : 0 < rho) (hrho1 : rho < 1)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1)
    (h_budget : delta0 / (1 - rho) ≤ delta) (T : ℕ) :
    μ.real {ω | ∀ t ∈ Finset.range (T + 1),
      (∀ i, -eps t i ≤ ⟪g t i + (m t : ℝ)⁻¹ • ∑ j, xi t i j ω, d t⟫_ℝ)
        → (∀ i, -(eps t i + noiseEps K sigma (d t) (m t) (delta0 * rho ^ t))
            ≤ ⟪g t i, d t⟫_ℝ)} ≥ 1 - delta := by
  classical
  -- the per-step certificate event
  set Good : ℕ → Set Ω := fun t =>
    {ω | (∀ i, -eps t i ≤ ⟪g t i + (m t : ℝ)⁻¹ • ∑ j, xi t i j ω, d t⟫_ℝ)
        → (∀ i, -(eps t i + noiseEps K sigma (d t) (m t) (delta0 * rho ^ t))
            ≤ ⟪g t i, d t⟫_ℝ)} with hGooddef
  -- per-step concentration: δₜ = δ₀·ρᵗ ∈ (0,1) and the SafeQP transfer
  have hdelta_t : ∀ t, delta0 * rho ^ t ∈ Set.Ioo 0 1 := by
    intro t
    obtain ⟨hd1, hd2⟩ := Set.mem_Ioo.mp hdelta
    refine ⟨mul_pos hdelta0 (pow_pos hrho t), ?_⟩
    have h1 : rho ^ t ≤ 1 := pow_le_one₀ hrho.le hrho1.le
    have hpos : (0:ℝ) < 1 - rho := by linarith
    rw [div_le_iff₀ hpos] at h_budget
    have h3 : delta * (1 - rho) < 1 := by nlinarith
    nlinarith
  -- measurability of the certificate events
  have hinner : ∀ t i (ω : Ω),
      ⟪g t i + (m t : ℝ)⁻¹ • ∑ j, xi t i j ω, d t⟫_ℝ
        = ⟪g t i, d t⟫_ℝ + (m t : ℝ)⁻¹ * ∑ j, ⟪xi t i j ω, d t⟫_ℝ := by
    intro t i ω
    rw [inner_add_left, inner_smul_left, sum_inner]
    simp
  have hmeasA : ∀ t i, Measurable
      (fun ω => ⟪g t i, d t⟫_ℝ + (m t : ℝ)⁻¹ * ∑ j, ⟪xi t i j ω, d t⟫_ℝ) := by
    intro t i
    exact measurable_const.add (measurable_const.mul
      (Finset.measurable_sum Finset.univ fun j _ => h_emp_noise_meas t i j))
  have hCert : ∀ t i, MeasurableSet
      {ω | -eps t i ≤ ⟪g t i + (m t : ℝ)⁻¹ • ∑ j, xi t i j ω, d t⟫_ℝ} := by
    intro t i
    have hset : {ω | -eps t i ≤ ⟪g t i + (m t : ℝ)⁻¹ • ∑ j, xi t i j ω, d t⟫_ℝ}
        = {ω | -eps t i
            ≤ ⟪g t i, d t⟫_ℝ + (m t : ℝ)⁻¹ * ∑ j, ⟪xi t i j ω, d t⟫_ℝ} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [hinner t i ω]
    rw [hset]
    exact measurableSet_le measurable_const (hmeasA t i)
  have hMargin : ∀ t i, MeasurableSet
      {ω : Ω | -(eps t i + noiseEps K sigma (d t) (m t) (delta0 * rho ^ t))
        ≤ ⟪g t i, d t⟫_ℝ} := fun t i =>
    MeasurableSet.const (-(eps t i + noiseEps K sigma (d t) (m t) (delta0 * rho ^ t))
      ≤ ⟪g t i, d t⟫_ℝ)
  have hGoodMeas : ∀ t, MeasurableSet (Good t) := by
    intro t
    have hEq2 : Good t
        = (⋂ i : K, {ω | -eps t i ≤ ⟪g t i + (m t : ℝ)⁻¹ • ∑ j, xi t i j ω, d t⟫_ℝ})ᶜ
          ∪ ⋂ i : K, {ω : Ω | -(eps t i + noiseEps K sigma (d t) (m t) (delta0 * rho ^ t))
            ≤ ⟪g t i, d t⟫_ℝ} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iInter, Set.mem_union]
      tauto
    rw [hEq2]
    refine MeasurableSet.union ?_ (MeasurableSet.iInter fun i => hMargin t i)
    exact MeasurableSet.compl (MeasurableSet.iInter fun i => hCert t i)
  -- per-step concentration: the SafeQP transfer at δₜ = δ₀·ρᵗ
  have h_step : ∀ t, μ.real ((Good t)ᶜ) ≤ delta0 * rho ^ t := by
    intro t
    have hgood := stochastic_safeQP_feasibility (m := m t) (hm t) (g := g t)
      (d := d t) (hd t) sigma hsigma (xi := xi t)
      (fun i j => h_emp_noise_meas t i j) (fun i j => h_emp_noise_zero t i j)
      (fun i => h_emp_noise_indep t i) (fun i j ω => h_emp_noise_bound t i j ω)
      (delta0 * rho ^ t) (hdelta_t t) (eps := eps t)
    have hcomp : μ.real ((Good t)ᶜ) = 1 - μ.real (Good t) := by
      rw [measureReal_compl (hGoodMeas t), probReal_univ]
    rw [hcomp]
    linarith
  exact anytime_safety delta0 rho hdelta0.le hrho.le hrho1 Good hGoodMeas h_step
    delta h_budget T

end Stochastic

end Composition

end Hagi


