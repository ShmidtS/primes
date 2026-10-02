/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.GrowthState
import Hagi.Growth.FrontierScaling
import Hagi.Step.SafeQPStep

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# R109: generalization mode state — vector Q-certificate, Φ_HAGI,
the gen-safe step, Pareto checkpoint selection, Qgen→frontier bridge

Motivated by arXiv:2609.33150 ("Generalization Dynamics of LM
Pre-training"): training CE can improve while the generalization
REGIME (shallow-cue computation vs transferable computation)
switches or degrades — the mode-hopping phenomenon. The paper's
empirical signature is the answer+1 probe: a checkpoint family
scores 81% → 0% → 81.7% on the same probe across consecutive
checkpoints while CE monotonically improves. Two consequences the
audit extracts and this module formalizes:

1. **No step is an improvement on CE grounds alone.** The
   controller state must carry a SECOND level — cheap
   generalization probes — and the Lyapunov object must be the
   two-level potential Φ_HAGI (fit + protected risk + a
   generalization-gap penalty), not the energy alone.
2. **Checkpoint averaging does not fix mode-hopping; selection
   can.** The checkpoint choice must be a Pareto selection over
   (E ↓, Q ↑, cost ↓) — never a default to the latest checkpoint.

## Contents

* `GenMetrics` / `Qvec` / `Qgen` — the GDsuite-style cheap probe
  vector (transfer, shallowCue, truthSeeking, reflective,
  multiHop) and its weighted scalarization. **Honest note**: the
  VECTOR certificate `Qvec` is the real object; `Qgen` is a
  lossy scalarization — a weighted sum can hide a mode drop on
  one probe behind gains on others (this is exactly why the
  `ModeDrop` predicate and the per-probe bookkeeping of
  `Qgen_drop_bound` are stated componentwise). All probe values
  are MEASURED telemetry (h_emp_G), never derived.
* `ModeDrop` — a PREDICATE, not a theorem: the empirical fact
  "E↓ does not imply Q↑" cannot be proven, only named. It names
  the situation the controller must detect and reject.
* `hagiPotential` — Φ_HAGI S := energy + λ·protectedRisk +
  ν·max(0, Q_target − Qgen S): the audit's extended Lyapunov
  object on top of R91's `potential` (energy + protectedRisk).
* `generalization_safe_step` (both cases, max(0,·) case
  analysis done explicitly): above target the penalty is inert
  and Φ decreases by the fit + risk amounts; below/at-dip the
  penalty growth is bounded by ν·ε_Q. The theorem NEVER silently
  assumes the penalty decreases.
* `scalarized_argmin_pareto` / `pareto_frontier_nonempty` /
  `selector_skips_dominated` — checkpoint Pareto selection over
  a finite checkpoint set. The PROVABLE direction of the
  weighted-sum/Pareto duality: the strictly-positive-weighted
  scalarized argmin IS Pareto-optimal. The converse (Pareto ⟹
  ∃ weights) needs convexity and is stated as OPEN, not faked.
  `selector_skips_dominated`: a strictly dominated checkpoint —
  in particular a dominated LATEST one — is never returned by
  any strictly-positive scalarized selector: recency is not a
  criterion.
* `qgen_frontier_bridge` — the audit's §8 production law
  inj_t ≥ β·C_t + η_Q·max(0, ΔQ_t) − ξ_t: data selection
  targeting a generalization-probe gain ΔQ > 0 adds to the
  frontier injection. The composition lemma: with this inj form
  the R107 cone condition's β-threshold
  `β ≥ (α/γ)(1+α−ρ) + ξ_t/C_t` is EASED to
  `β ≥ (α/γ)(1+α−ρ) + (ξ_t − η_Q·max(0,ΔQ_t))/C_t`
  — the effective production rate is β + η_Q·max(0,ΔQ_t)/C_t.

## Honest gaps

* The probes are telemetry: every theorem that consumes them
  carries an `h_emp_G` hypothesis; nothing about their dynamics
  is derived.
* The Pareto⟹∃weights direction of the duality needs a convex
  objective space — open (finite checkpoint sets are generic).
* `ModeDrop` is detectable but not predictable: the predicate
  names the failure mode; the paper's claim that data selection
  steers ΔQ > 0 enters `qgen_frontier_bridge` as the h_emp_dyn
  hypothesis on the measured ΔQ_t.
-/

open Real Finset

namespace Hagi

section ModeState

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-! ## The probe vector and its scalarization -/

/-- **The GDsuite-style cheap probe vector** — five scalar probes
of the generalization regime: `transfer` (held-out transfer),
`shallowCue` (shortcut-probe reliance — the shallow-regime
marker), `truthSeeking`, `reflective`, `multiHop`. ALL FIELDS ARE
MEASURED TELEMETRY (h_emp_G): they are carriers of an empirical
measurement, not derived quantities. The real certificate object
is the VECTOR `Qvec`; `Qgen` below is the lossy scalarization. -/
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

/-- The raw probe vector — the REAL certificate object (the
scalarization `Qgen` can hide a per-probe mode drop behind
compensating gains on other probes; see `ModeDrop`). -/
def Qvec (m : GenMetrics) : Fin 5 → ℝ :=
  ![m.transfer, m.shallowCue, m.truthSeeking, m.reflective, m.multiHop]

/-- **The weighted scalarization** of the probe vector with
nonnegative weights. HONEST NOTE: this is a bookkeeping
convenience for the Φ_HAGI penalty term; the VECTOR `Qvec` is
the real object — a weighted sum is exactly the kind of surrogate
that can mask mode-hopping (the repo's `selection_hurts`
precedent: a surrogate metric misleads when it is treated as the
target). -/
def Qgen (m : GenMetrics) (w : Fin 5 → ℝ) : ℝ :=
  ∑ i, w i * Qvec m i

/-- **Componentwise monotonicity of the scalarization**: with
nonnegative weights, pointwise probe domination implies
scalarized domination. -/
theorem Qgen_le {m m' : GenMetrics} {w : Fin 5 → ℝ}
    (hw : ∀ i, 0 ≤ w i) (h : ∀ i, Qvec m i ≤ Qvec m' i) :
    Qgen m w ≤ Qgen m' w :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i)

/-- **Componentwise drop bookkeeping** (the anti-masking lemma):
if every probe drops by at most ε_i (measured, h_emp_G), then
the scalarization drops by at most Σ_i w_i·ε_i — with the bound
computed PER PROBE, so no single probe's drop can hide. This is
the honest form: the controller certifies ΔQ ≥ −ε_Q with
ε_Q := Σ w_i ε_i for the DECLARED per-probe tolerances. -/
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

/-- **The growth-loop state extended with the generalization
telemetry**: R91's `GrowthState` (energy = the reverse-KL/CE
certificate, protectedRisk = the protected-domain regression
budget) plus the measured probe vector `gen`. -/
structure GenState (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] extends GrowthState X where
  /-- The measured generalization-probe vector (h_emp_G). -/
  gen : GenMetrics

/-- **The extended Lyapunov object** (the audit's Φ_HAGI):
R91's `potential` (energy + protectedRisk) with the risk weight
λ and the generalization-gap penalty ν·max(0, Q_target − Qgen).
The max(0,·) makes the penalty INERT above target and ACTIVE
below — the gen-safe step theorem does this case analysis
explicitly. -/
def hagiPotential (S : GenState X) (lam nu Qtarget : ℝ) (w : Fin 5 → ℝ) : ℝ :=
  S.toGrowthState.energy + lam * S.toGrowthState.protectedRisk
    + nu * max 0 (Qtarget - Qgen S.gen w)

/-! ## ModeDrop: the named failure mode -/

/-- **The mode-drop predicate** — NOT a theorem: the empirical
fact "training CE improves ⇏ generalization improves" cannot be
proven, only NAMED. `ModeDrop S S' ε_E ε_Q w` holds when the fit
improved by at least ε_E (E S' ≤ E S − ε_E) while the
scalarized generalization probe DROPPED by at least ε_Q. This is
the situation the controller must DETECT and REJECT (see
`modeDrop_rejected`: a certified ΔQ ≥ −ε_Q tolerance strictly
below ε_Q^mode makes the mode drop impossible to miss).

Empirical signature (arXiv:2609.33150, the answer+1 example):
consecutive checkpoints score 81% → 0% → 81.7% on the answer+1
probe while CE improves throughout — the middle checkpoint is a
`ModeDrop` (the shallow regime took over the probe), and the
paper's finding is that checkpoint AVERAGING does not repair it
while data SELECTION does — hence the Pareto selector below and
the ΔQ-targeted frontier injection of `qgen_frontier_bridge`. -/
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

/-- **THE GEN-SAFE STEP (general case — the honest bound).**
If the fit improves by at least ε_E (h_emp_fit: the measured
post-step energy certificate), the protected-risk regression is
bounded by the budget (h_risk: the SafeQP guarantee —
`safeqp_eta_max` supplies exactly this per-domain budget,
composed into aggregate form by `safeqp_risk_bound_compose`
below), and the generalization probe is certified within
tolerance (h_emp_G: ΔQ ≥ −ε_Q, MEASURED telemetry), then Φ_HAGI
decreases up to the honest error terms: the fit amount minus
the risk spend minus the worst-case penalty growth ν·ε_Q.

The max(0,·) is handled WITHOUT assuming the penalty decreases:
`relu_shift_le` bounds the penalty growth by ν·ε_Q in ALL cases
(including the below-target dip). The clean at-target form is
`generalization_safe_step_at_target`. -/
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
  unfold hagiPotential
  linarith

/-- **THE GEN-SAFE STEP (at-target case — the penalty is
inert).** With the SAME fit/risk/probe hypotheses, if the
post-step probe stays at or above target (Qgen S' ≥ Q_target),
the penalty term contributes ZERO at S' and is nonnegative at
S, so Φ_HAGI decreases by the certified fit amount minus the
risk spend — NO ν·ε_Q term: the penalty never bites while the
probe is above target. This and `generalization_safe_step` are
the two cases of the case analysis; neither silently assumes
the other's regime. -/
theorem generalization_safe_step_at_target (S S' : GenState X)
    (lam nu Qtarget : ℝ) (w : Fin 5 → ℝ)
    (hlam : 0 ≤ lam) (hnu : 0 ≤ nu)
    (ε_E ε_Q budget : ℝ)
    (h_emp_fit : S'.toGrowthState.energy
      ≤ S.toGrowthState.energy - ε_E)
    (h_risk : S'.toGrowthState.protectedRisk
      - S.toGrowthState.protectedRisk ≤ budget)
    (h_emp_G : Qgen S.gen w - ε_Q ≤ Qgen S'.gen w)
    (htgt : Qtarget ≤ Qgen S'.gen w) :
    hagiPotential S' lam nu Qtarget w
      ≤ hagiPotential S lam nu Qtarget w - ε_E + lam * budget := by
  have h0 : max 0 (Qtarget - Qgen S'.gen w) = 0 :=
    max_eq_left (by linarith)
  have hge : (0:ℝ) ≤ max 0 (Qtarget - Qgen S.gen w) :=
    le_max_left 0 _
  unfold hagiPotential
  rw [h0, mul_zero, add_zero]
  have hνm : (0:ℝ) ≤ nu * max 0 (Qtarget - Qgen S.gen w) :=
    mul_nonneg hnu hge
  have hrisks : S'.toGrowthState.protectedRisk
      ≤ S.toGrowthState.protectedRisk + budget := by linarith
  have hlamM : lam * S'.toGrowthState.protectedRisk
      ≤ lam * (S.toGrowthState.protectedRisk + budget) :=
    mul_le_mul_of_nonneg_left hrisks hlam
  linarith

/-- **The SafeQP composition**: the per-domain budget guarantee
of `safeqp_eta_max` (ΔL_i ≤ ε_i for every protected domain i)
aggregates to the protectedRisk budget of the gen-safe step when
the accumulated risk is the per-domain sum — the h_risk
hypothesis is the SafeQP guarantee in aggregate form. -/
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

/-- **The controller's detection guarantee**: a certified probe
tolerance ε_Q strictly below the mode-drop threshold ε_Q^mode
makes `ModeDrop` IMPOSSIBLE to coexist with the certificate —
the predicate situation is DETECTED (contradiction), not
swallowed. The ε_E side is untouched: the fit improvement is
exactly what makes the mode drop dangerous (E↓ while Q↓↓). -/
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

/-- **The PROVABLE direction of the weighted-sum/Pareto duality**:
any minimizer of a STRICTLY-POSITIVE weighted scalarization is
Pareto-optimal. (The converse — every Pareto point maximizes
some nonnegative scalarization — needs convexity of the
achievable objective set and is OPEN here; finite checkpoint
sets are generic, so only this direction is honest.) -/
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

/-- **`not_latest_is_best_allowed`, the real form**: the selector
output is characterized by the SCORE, not by recency. Concretely:
if the LATEST checkpoint is strictly dominated (some y is at
least as good on all three objectives and strictly better on
one), then NO strictly-positive scalarized selector ever returns
it — recency alone is never a tiebreak, and a dominated latest
checkpoint is structurally excluded. -/
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

/-! The audit's §8 production law: the frontier injection is
`inj_t ≥ β·C_t + η_Q·max(0, ΔQ_t) − ξ_t` — data selection
targeting a positive generalization-probe change ΔQ_t > 0 ADDS
to the injection rate. The R107 cone condition's β-threshold is
then EASED: the effective production rate is
`β_eff,t = β + η_Q·max(0, ΔQ_t)/C_t`, and the exact threshold
`α/γ·((1+α) − ρ) + ξ_t/C_t ≤ β` becomes
`α/γ·((1+α) − ρ) + (ξ_t − η_Q·max(0,ΔQ_t))/C_t ≤ β`. -/

/-- **The bridge step lemma**: with the ΔQ-boosted injection
dynamics `D_{t+1} ≥ ρ·D_t + β·C_t + η_Q·max(0, ΔQ_t) − ξ_t`
(h_emp_dyn: the dynamics including the MEASURED probe change
ΔQ_t), the R107 cone step holds under the EASED threshold
`α/γ·((1+α) − ρ) + (ξ_t − η_Q·max(0,ΔQ_t))/C_t ≤ β` —
i.e. a sustained ΔQ_t > 0 at rate η_Q buys exactly
η_Q·max(0,ΔQ_t)/C_t of production rate. Proof: rewrite the
dynamics as R107's form with β_eff := β + η_Q·max(0,ΔQ_t)/C_t
(an exact identity when C_t > 0) and apply
`frontier_cone_inductive`. -/
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

/-- **The bridge invariant**: the cone holds at EVERY t under
the ΔQ-boosted dynamics with the per-step eased threshold —
sustained ΔQ > 0 keeps the cone invariant with a β that R107
alone would reject (any β ≥ (α/γ)(1+α−ρ) +
(ξ_t − η_Q·max(0,ΔQ_t))/C_t suffices, versus R107's ξ_t/C_t
term). -/
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
