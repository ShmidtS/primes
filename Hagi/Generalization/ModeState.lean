/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.FrontierScaling
import Hagi.Foundations.Potential
import Hagi.Unified.GrowthState

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# Generalization mode state

Definitions: `GenMetrics`/`Qvec`/`Qgen` (a five-probe
generalization telemetry vector, all values measured —
h_emp_G — and its nonnegative-weight scalarization), `GenState`
(`GrowthState` plus the probe vector), the Lyapunov object
`hagiPotential` = energy + lam * protectedRisk +
nu * max(0, Qtarget - Qgen), and the predicate `ModeDrop`
(energy improves while `Qgen` drops).

Results:
* `Qgen_le`, `Qgen_drop_bound` — componentwise monotonicity
  and per-probe drop bookkeeping of the scalarization.
* `generalization_safe_step`,
  `generalization_safe_step_at_target` — Φ_HAGI decreases by
  the fit amount minus `lam * budget` minus (general case)
  `nu * ε_Q`, under measured fit/probe premises and a bounded
  protected-risk regression.
* `modeDrop_rejected` — a certified probe tolerance strictly
  below the mode-drop threshold contradicts `ModeDrop`.
* Pareto checkpoint selection (`scalarized_argmin_pareto`,
  `pareto_frontier_nonempty`, `selector_skips_dominated`) —
  strictly-positive weighted scalarized argmins are
  Pareto-optimal and never return a strictly dominated
  checkpoint. The converse direction needs convexity and is
  not claimed.
* `qgen_frontier_bridge`(_invariant) — the cone step/invariant
  under ΔQ-boosted injection dynamics with the eased
  β-threshold.

Open: the Pareto ⟹ ∃ weights direction (needs a convex
objective space); probe dynamics are not derived — every
consumer carries an h_emp_G/h_emp_dyn premise.
-/

open Real Finset

namespace Hagi

section ModeState

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-! ## The probe vector and its scalarization -/

/-- Five measured generalization probes: `transfer`,
`shallowCue`, `truthSeeking`, `reflective`, `multiHop`. All
fields are measured telemetry (h_emp_G), not derived. -/
structure GenMetrics where
  /-- Transfer-probe score (measured). -/
  transfer : ℝ
  /-- Shallow-cue reliance (measured; higher = more shortcut). -/
  shallowCue : ℝ
  /-- Truth-seeking probe score (measured). -/
  truthSeeking : ℝ
  /-- Reflective-reasoning probe score (measured). -/
  reflective : ℝ
  /-- Multi-hop probe score (measured). -/
  multiHop : ℝ

/-- The probe vector of `m`; per-probe bookkeeping (see
`Qgen_drop_bound`, `ModeDrop`) uses this, since the
scalarization `Qgen` can hide a single probe's drop. -/
def Qvec (m : GenMetrics) : Fin 5 → ℝ :=
  ![m.transfer, m.shallowCue, m.truthSeeking, m.reflective, m.multiHop]

/-- The weighted scalarization ∑ w i * Qvec m i with
nonnegative weights; a weighted sum can hide a single probe's
drop (see `Qvec`). -/
def Qgen (m : GenMetrics) (w : Fin 5 → ℝ) : ℝ :=
  ∑ i, w i * Qvec m i

/-- **Componentwise monotonicity of the scalarization**: with
nonnegative weights, pointwise probe domination implies
scalarized domination. -/
theorem Qgen_le {m m' : GenMetrics} {w : Fin 5 → ℝ}
    (hw : ∀ i, 0 ≤ w i) (h : ∀ i, Qvec m i ≤ Qvec m' i) :
    Qgen m w ≤ Qgen m' w :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i)

/-- If `Qvec m i - ε i ≤ Qvec m' i` for every probe `i`
(measured, h_emp_G) and weights are nonnegative, then
`Qgen m w - ∑ w i * ε i ≤ Qgen m' w`. -/
theorem Qgen_drop_bound {m m' : GenMetrics} {w : Fin 5 → ℝ}
    {ε : Fin 5 → ℝ} (hw : ∀ i, 0 ≤ w i)
    (h_emp_G : ∀ i, Qvec m i - ε i ≤ Qvec m' i) :
    Qgen m w - ∑ i, w i * ε i ≤ Qgen m' w := by
  have hsplit : Qgen m' w - Qgen m w = ∑ i, w i * (Qvec m' i - Qvec m i) := by
    simp only [Qgen, mul_sub, Finset.sum_sub_distrib]
  have hle : ∑ i, w i * (-(ε i)) ≤ ∑ i, w i * (Qvec m' i - Qvec m i) :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (by linarith [h_emp_G i]) (hw i)
  have hsl : ∑ i, w i * (-(ε i)) = -∑ i, w i * ε i := by
    simp [mul_neg, Finset.sum_neg_distrib]
  have hsr : ∑ i, w i * (Qvec m' i - Qvec m i) = Qgen m' w - Qgen m w := hsplit.symm
  linarith

/-! ## The state and Φ_HAGI -/

/-- `GrowthState` extended with the measured generalization
probe vector `gen`. -/
structure GenState (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] extends GrowthState X where
  /-- The measured generalization-probe vector (h_emp_G). -/
  gen : GenMetrics

/-- The Lyapunov potential `energy + lam * protectedRisk +
nu * max(0, Qtarget - Qgen S.gen w)`. -/
noncomputable def hagiPotential (S : GenState X) (lam nu Qtarget : ℝ) (w : Fin 5 → ℝ) : ℝ :=
  -- R263 dedup: the canonical scalar potential (Foundations.Potential)
  -- applied to the projected state fields.
  Hagi.Foundations.hagiPotential S.toGrowthState.energy
    S.toGrowthState.protectedRisk nu Qtarget (Qgen S.gen w) lam

/-! ## ModeDrop: the named failure mode -/

/-- Predicate: the energy improves by at least `ε_E` while the
scalarized probe drops by at least `ε_Q`. A named failure mode,
not a theorem; a controller certifying `ΔQ ≥ −ε_Q` with
`ε_Q < ε_Q^mode` rules it out (`modeDrop_rejected`).
(source: arXiv:2609.33150) -/
def ModeDrop (S S' : GenState X) (ε_E ε_Q : ℝ) (w : Fin 5 → ℝ) : Prop :=
  S'.toGrowthState.energy ≤ S.toGrowthState.energy - ε_E
    ∧ Qgen S'.gen w ≤ Qgen S.gen w - ε_Q

/-! ## The gen-safe step -/

/-- The hinge-shift lemma: if a' ≥ a − ε (with ε ≥ 0) then the
hinge at a' exceeds the hinge at a by at most ε. -/
private theorem relu_shift_le (t a a' ε : ℝ) (hε : 0 ≤ ε) (h : a - ε ≤ a') :
    max 0 (t - a') ≤ max 0 (t - a) + ε := by
  have hle : t - a' ≤ (t - a) + ε := by linarith
  have h1 : max 0 (t - a') ≤ max 0 ((t - a) + ε) :=
    max_le_max (le_refl _) hle
  -- max 0 (x + ε) ≤ max 0 x + ε for ε ≥ 0
  have h2 : max 0 ((t - a) + ε) ≤ max 0 (t - a) + ε := by
    rcases le_total 0 (t - a) with hx | hx
    · rw [max_eq_right hx, max_eq_right (by linarith)]
    · rcases le_total 0 ((t - a) + ε) with hy | hy
      · rw [max_eq_right hy, max_eq_left hx]; linarith
      · rw [max_eq_left hy, max_eq_left hx]; linarith
  linarith

/-- If the measured fit improves by `ε_E` (h_emp_fit), the
protected-risk regression is at most `budget` (h_risk), and the
probe is certified `Qgen S.gen w - ε_Q ≤ Qgen S'.gen w`
(h_emp_G, with `ε_Q ≥ 0`), then Φ_HAGI decreases by at least
`ε_E - lam * budget - nu * ε_Q`. -/
theorem generalization_safe_step (S S' : GenState X)
    (lam nu Qtarget : ℝ) (w : Fin 5 → ℝ)
    (hlam : 0 ≤ lam) (hnu : 0 ≤ nu)
    (ε_E ε_Q budget : ℝ) (hε_Q : 0 ≤ ε_Q)
    (h_emp_fit : S'.toGrowthState.energy
      ≤ S.toGrowthState.energy - ε_E)
    (h_risk : S'.toGrowthState.protectedRisk
      - S.toGrowthState.protectedRisk ≤ budget)
    (h_emp_G : Qgen S.gen w - ε_Q ≤ Qgen S'.gen w) :
    hagiPotential S' lam nu Qtarget w
      ≤ hagiPotential S lam nu Qtarget w - ε_E + lam * budget + nu * ε_Q := by
  -- the penalty can GROW by at most ν·ε_Q (never assumed down)
  have hpen : max 0 (Qtarget - Qgen S'.gen w)
      ≤ max 0 (Qtarget - Qgen S.gen w) + ε_Q :=
    relu_shift_le Qtarget (Qgen S.gen w) (Qgen S'.gen w) ε_Q
      hε_Q h_emp_G
  have hνm : nu * max 0 (Qtarget - Qgen S'.gen w)
      ≤ nu * (max 0 (Qtarget - Qgen S.gen w) + ε_Q) :=
    mul_le_mul_of_nonneg_left hpen hnu
  have hrisks : S'.toGrowthState.protectedRisk
      ≤ S.toGrowthState.protectedRisk + budget := by linarith
  have hlamM : lam * S'.toGrowthState.protectedRisk
      ≤ lam * (S.toGrowthState.protectedRisk + budget) :=
    mul_le_mul_of_nonneg_left hrisks hlam
  unfold hagiPotential Hagi.Foundations.hagiPotential
  linarith

/-- As `generalization_safe_step`, but assuming additionally
`Qtarget ≤ Qgen S'.gen w`: the penalty is zero at `S'`, so the
bound drops the `nu * ε_Q` term. -/
theorem generalization_safe_step_at_target (S S' : GenState X)
    (lam nu Qtarget : ℝ) (w : Fin 5 → ℝ)
    (hlam : 0 ≤ lam) (hnu : 0 ≤ nu)
    (ε_E ε_Q budget : ℝ)
    (h_emp_fit : S'.toGrowthState.energy
      ≤ S.toGrowthState.energy - ε_E)
    (h_risk : S'.toGrowthState.protectedRisk
      - S.toGrowthState.protectedRisk ≤ budget)
    (_h_emp_G : Qgen S.gen w - ε_Q ≤ Qgen S'.gen w)
    (htgt : Qtarget ≤ Qgen S'.gen w) :
    hagiPotential S' lam nu Qtarget w
      ≤ hagiPotential S lam nu Qtarget w - ε_E + lam * budget := by
  have h0 : max 0 (Qtarget - Qgen S'.gen w) = 0 :=
    max_eq_left (by linarith)
  have hge : (0:ℝ) ≤ max 0 (Qtarget - Qgen S.gen w) :=
    le_max_left 0 _
  unfold hagiPotential Hagi.Foundations.hagiPotential
  rw [h0, mul_zero, add_zero]
  have hνm : (0:ℝ) ≤ nu * max 0 (Qtarget - Qgen S.gen w) :=
    mul_nonneg hnu hge
  have hrisks : S'.toGrowthState.protectedRisk
      ≤ S.toGrowthState.protectedRisk + budget := by linarith
  have hlamM : lam * S'.toGrowthState.protectedRisk
      ≤ lam * (S.toGrowthState.protectedRisk + budget) :=
    mul_le_mul_of_nonneg_left hrisks hlam
  linarith

/-- If the accumulated risk is `S'.protectedRisk =
S.protectedRisk + ∑ dL i` with `dL i ≤ eps i` for every `i`,
then the risk regression is at most `∑ eps i`. -/
theorem safeqp_risk_bound_compose {K : Type*} [Fintype K]
    (S S' : GenState X) (dL eps : K → ℝ)
    (hacc : S'.toGrowthState.protectedRisk
      = S.toGrowthState.protectedRisk + ∑ i, dL i)
    (hqp : ∀ i, dL i ≤ eps i) :
    S'.toGrowthState.protectedRisk - S.toGrowthState.protectedRisk
      ≤ ∑ i, eps i := by
  rw [hacc]
  have hle : (∑ i, dL i) ≤ (∑ i, eps i) :=
    Finset.sum_le_sum fun i _ => hqp i
  simp only [add_sub_cancel_left]
  exact hle

/-- A `ModeDrop` with threshold `ε_Qmode` contradicts a
certificate `Qgen S.gen w - ε_Q ≤ Qgen S'.gen w` whenever
`ε_Q < ε_Qmode`. -/
theorem modeDrop_rejected (S S' : GenState X) (ε_E ε_Q ε_Qmode : ℝ)
    (w : Fin 5 → ℝ)
    (hmd : ModeDrop S S' ε_E ε_Qmode w)
    (h_emp_G : Qgen S.gen w - ε_Q ≤ Qgen S'.gen w)
    (hstrict : ε_Q < ε_Qmode) : False := by
  obtain ⟨_, hQ⟩ := hmd
  linarith

end ModeState

/-! ## Pareto checkpoint selection -/

section CheckpointPareto

variable {Ck : Type*} [Fintype Ck] [Nonempty Ck]

/-- **Weak dominance on the three checkpoint objectives**:
E ↓ (fit), Q ↑ (generalization probe), cost ↓. `dominates x y`
reads "x is at least as good as y on ALL three". -/
def dominates (E Q cost : Ck → ℝ) (x y : Ck) : Prop :=
  E x ≤ E y ∧ Q y ≤ Q x ∧ cost x ≤ cost y

/-- **Pareto frontier membership**: x is a frontier point when
nothing weakly dominates it without being dominated back — i.e.
no checkpoint is strictly better on all fronts. -/
def IsPareto (E Q cost : Ck → ℝ) (x : Ck) : Prop :=
  ∀ y, dominates E Q cost y x → dominates E Q cost x y

/-- The strictly-positive weighted scalarization (minimized):
w_E·E − w_Q·Q + w_C·cost with w_E, w_Q, w_C > 0. -/
private def scalarScore (E Q cost : Ck → ℝ) (wE wQ wC : ℝ) (x : Ck) : ℝ :=
  wE * E x - wQ * Q x + wC * cost x

/-- Any minimizer of the strictly-positive weighted score
`scalarScore` is Pareto-optimal. The converse needs convexity
and is not claimed. -/
theorem scalarized_argmin_pareto (E Q cost : Ck → ℝ) (wE wQ wC : ℝ)
    (hwE : 0 < wE) (hwQ : 0 < wQ) (hwC : 0 < wC) (x : Ck)
    (hmin : ∀ y, scalarScore E Q cost wE wQ wC x
      ≤ scalarScore E Q cost wE wQ wC y) :
    IsPareto E Q cost x := by
  intro y hy
  obtain ⟨h1, h2, h3⟩ := hy
  -- dominance forces σ y ≤ σ x; minimality forces equality
  have hσy : scalarScore E Q cost wE wQ wC y
      ≤ scalarScore E Q cost wE wQ wC x := by
    unfold scalarScore
    nlinarith [mul_le_mul_of_nonneg_left h1 hwE.le,
      mul_le_mul_of_nonneg_right h2 hwQ.le,
      mul_le_mul_of_nonneg_left h3 hwC.le]
  have hσx : scalarScore E Q cost wE wQ wC x
      ≤ scalarScore E Q cost wE wQ wC y := hmin y
  -- σ y = σ x forces the weighted-gap sum to zero; each gap
  -- is nonpositive by dominance, hence each is exactly zero
  have hd : wE * (E y - E x) + wQ * (Q x - Q y) + wC * (cost y - cost x)
      = (wE * E y - wQ * Q y + wC * cost y)
        - (wE * E x - wQ * Q x + wC * cost x) := by ring
  have hzero : wE * (E y - E x) + wQ * (Q x - Q y)
      + wC * (cost y - cost x) = 0 := by
    unfold scalarScore at hσy hσx
    linarith
  -- extraction helper: multiplying by a positive weight is
  -- injective
  have hext : ∀ u v : ℝ, 0 < v → v * u = 0 → u = 0 := by
    intro u v hv hvu
    rcases mul_eq_zero.mp hvu with h | h
    · exact absurd h (ne_of_gt hv)
    · exact h
  have hA : wE * (E y - E x) ≤ 0 := by nlinarith
  have hB : wQ * (Q x - Q y) ≤ 0 := by nlinarith
  have hC : wC * (cost y - cost x) ≤ 0 := by nlinarith
  have e1 : E y - E x = 0 := by
    have hz : wE * (E y - E x) = 0 := le_antisymm hA (by linarith)
    exact hext _ _ hwE hz
  have e2 : Q x - Q y = 0 := by
    have hz : wQ * (Q x - Q y) = 0 := le_antisymm hB (by linarith)
    exact hext _ _ hwQ hz
  have e3 : cost y - cost x = 0 := by
    have hz : wC * (cost y - cost x) = 0 := le_antisymm hC (by linarith)
    exact hext _ _ hwC hz
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **The frontier is nonempty** over any finite nonempty
checkpoint set: the unit-weight scalarized argmin exists
(finiteness) and is Pareto by
`scalarized_argmin_pareto`. -/
theorem pareto_frontier_nonempty (E Q cost : Ck → ℝ) :
    ∃ x, IsPareto E Q cost x := by
  obtain ⟨x, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun x => scalarScore E Q cost 1 1 1 x) Finset.univ_nonempty
  exact ⟨x, scalarized_argmin_pareto E Q cost 1 1 1
    (by norm_num) (by norm_num) (by norm_num) x
    (fun y => hmin y (Finset.mem_univ y))⟩

/-- If `last` is strictly dominated by `y` (weakly on all
three objectives, strictly on one), no minimizer `x` of a
strictly-positive weighted score equals `last`. -/
theorem selector_skips_dominated (E Q cost : Ck → ℝ) (wE wQ wC : ℝ)
    (hwE : 0 < wE) (hwQ : 0 < wQ) (hwC : 0 < wC)
    (last y : Ck)
    (hdom : dominates E Q cost y last)
    (hstrict : E y < E last ∨ Q last < Q y ∨ cost y < cost last)
    (x : Ck) (hmin : ∀ z, scalarScore E Q cost wE wQ wC x
      ≤ scalarScore E Q cost wE wQ wC z) :
    x ≠ last := by
  intro heq
  obtain ⟨h1, h2, h3⟩ := hdom
  -- strict dominance with positive weights is a strict score drop
  have hstrict' : scalarScore E Q cost wE wQ wC y
      < scalarScore E Q cost wE wQ wC last := by
    unfold scalarScore
    rcases hstrict with hs | hs | hs
    · nlinarith
    · nlinarith
    · nlinarith
  have hsx := hmin y
  rw [heq] at hsx
  linarith

end CheckpointPareto

/-! ## The Qgen → frontier bridge (audit §8) -/

section QgenFrontier

/-! The ΔQ-boosted injection dynamics ease the cone
condition's β-threshold: with injection
`ρ·D_t + β·C_t + η_Q·max(0, ΔQ_t) − ξ_t ≤ D_{t+1}`, the
threshold `α/γ·((1+α) − ρ) + ξ_t/C_t ≤ β` becomes
`α/γ·((1+α) − ρ) + (ξ_t − η_Q·max(0, ΔQ_t))/C_t ≤ β`. -/

/-- One cone step under the ΔQ-boosted dynamics: given
`h_emp_dyn`, `h_C_cap`, `0 < C t`, and the eased threshold
`hβ_eased`, the cone `α/γ * C (t+1) ≤ D (t+1)` holds. -/
theorem qgen_frontier_bridge (C D ξ ΔQ : ℕ → ℝ) (α γ ρ β ηQ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ) (hηQ : 0 ≤ ηQ)
    (t : ℕ) (hCpos : 0 < C t)
    (hcone : α / γ * C t ≤ D t)
    (h_emp_dyn : ρ * D t + β * C t + ηQ * max 0 (ΔQ t) - ξ t
      ≤ D (t + 1))
    (h_C_cap : C (t + 1) ≤ (1 + α) * C t)
    (hβ_eased : α / γ * ((1 + α) - ρ)
      + (ξ t - ηQ * max 0 (ΔQ t)) / C t ≤ β) :
    α / γ * C (t + 1) ≤ D (t + 1) := by
  -- the effective production rate and its two identities
  have hmul : (β + ηQ * max 0 (ΔQ t) / C t) * C t
      = β * C t + ηQ * max 0 (ΔQ t) := by
    field_simp
  have hdiv : (ξ t - ηQ * max 0 (ΔQ t)) / C t
      = ξ t / C t - ηQ * max 0 (ΔQ t) / C t :=
    sub_div _ _ _
  -- R107 dynamics with β_eff
  have h_dyn_eff : ρ * D t + (β + ηQ * max 0 (ΔQ t) / C t) * C t - ξ t
      ≤ D (t + 1) := by
    rw [hmul]; linarith
  -- the R107 threshold holds for β_eff
  have hβ_eff : α / γ * ((1 + α) - ρ) + ξ t / C t
      ≤ β + ηQ * max 0 (ΔQ t) / C t := by
    rw [hdiv] at hβ_eased
    linarith
  exact frontier_cone_inductive C D ξ α γ ρ
    (β + ηQ * max 0 (ΔQ t) / C t)
    hα hγ hρ t hCpos hcone h_dyn_eff h_C_cap hβ_eff

/-- If the cone holds at `t = 0` and the hypotheses of
`qgen_frontier_bridge` hold at every `t`, then
`α/γ * C t ≤ D t` for every `t`. -/
theorem qgen_frontier_bridge_invariant (C D ξ ΔQ : ℕ → ℝ)
    (α γ ρ β ηQ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ) (hηQ : 0 ≤ ηQ)
    (hCpos : ∀ t, 0 < C t)
    (h_cone0 : α / γ * C 0 ≤ D 0)
    (h_emp_dyn : ∀ t, ρ * D t + β * C t + ηQ * max 0 (ΔQ t) - ξ t
      ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (hβ_eased : ∀ t, α / γ * ((1 + α) - ρ)
      + (ξ t - ηQ * max 0 (ΔQ t)) / C t ≤ β) :
    ∀ t, α / γ * C t ≤ D t := by
  intro t
  induction t with
  | zero => exact h_cone0
  | succ t ih =>
      exact qgen_frontier_bridge C D ξ ΔQ α γ ρ β ηQ hα hγ hρ hηQ t
        (hCpos t) ih (h_emp_dyn t) (h_C_cap t) (hβ_eased t)

end QgenFrontier

end Hagi
