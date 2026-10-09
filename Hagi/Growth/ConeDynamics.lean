/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.FrontierScaling
import Hagi.Foundations.ConeTakeoff

/-!
# ConeDynamics — ONE abstract cone theorem (R260;
architecture audit P1: "the most important duplicate in
Growth" — unification stage 0)

The same mathematical core — cone invariant + takeoff under
frontier dynamics — lives in several APIs:

* `Foundations.ConeTakeoff` (the zero-error canonical form);
* `Growth.FrontierScaling` (the ξ-forcing form, exact
  threshold);
* `Growth.RatioTakeoff`, `Growth.StateClosedRenewal`,
  `Growth.GainRenewal` (specializations).

Stage 0 of the unification: ONE abstract data structure and
ONE general cone law with the forcing/error term (the
StateClosedRenewal insight — the OLD zero-error versions
become corollaries at ξ ≡ 0):

* `ConeData` — the abstract carrier: capability C, frontier
  D, forcing ξ, and the four law constants;
* `cone_data_invariant` — THE general step law: with the
  cone k·C_t ≤ D_t, the frontier dynamics ρ·D + β·C − ξ ≤
  D', the capability cap C' ≤ (1+γk)·C, and the EXACT
  threshold k((1+γk) − ρ) + ξ/C ≤ β, the cone survives the
  step;
* `frontier_cone_inductive_is_cone_data` — the bridge:
  FrontierScaling's theorem IS the abstract law at
  k = α/γ (same hypotheses, same conclusion — a thin
  wrapper, no new mathematics, proving the unification
  instead of asserting it).

Later stages re-express RatioTakeoff / StateClosedRenewal /
GainRenewal as further specializations and thin their
private proofs to delegations.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- The abstract cone-dynamics carrier: capability,
frontier, forcing, and the law constants. -/
structure ConeData where
  /-- capability channel. -/
  C : ℕ → ℝ
  /-- frontier channel. -/
  D : ℕ → ℝ
  /-- the forcing/friction term (losses that drain the
  frontier; ξ ≡ 0 recovers the zero-error cone). -/
  ξ : ℕ → ℝ
  γ : ℝ
  ρ : ℝ
  β : ℝ

/-- **THE general cone step law** (with forcing): if the
cone k·C_t ≤ D_t holds, the frontier obeys
ρ·D_t + β·C_t − ξ_t ≤ D_{t+1}, the capability grows at most
by the cone factor (C_{t+1} ≤ (1+γk)·C_t), and the EXACT
threshold

  k·((1+γk) − ρ) + ξ_t/C_t ≤ β

holds (production covers the cone's widening plus
friction), then the cone survives the step. Zero-error
version: ξ ≡ 0 and the threshold collapses to
k((1+γk) − ρ) ≤ β. -/
theorem cone_data_invariant (cd : ConeData) (k : ℝ) (t : ℕ)
    (hk : 0 ≤ k) (hγ : 0 ≤ cd.γ) (hρ : 0 ≤ cd.ρ)
    (hCpos : 0 < cd.C t)
    (hcone : k * cd.C t ≤ cd.D t)
    (h_dyn : cd.ρ * cd.D t + cd.β * cd.C t - cd.ξ t
      ≤ cd.D (t + 1))
    (h_C_cap : cd.C (t + 1) ≤ (1 + cd.γ * k) * cd.C t)
    (hβ : k * ((1 + cd.γ * k) - cd.ρ) + cd.ξ t / cd.C t
      ≤ cd.β) :
    k * cd.C (t + 1) ≤ cd.D (t + 1) := by
  have h1 : cd.ρ * (k * cd.C t) ≤ cd.ρ * cd.D t :=
    mul_le_mul_of_nonneg_left hcone hρ
  have h2 : (k * ((1 + cd.γ * k) - cd.ρ)) * cd.C t
      + cd.ξ t ≤ cd.β * cd.C t := by
    have hm := mul_le_mul_of_nonneg_right hβ hCpos.le
    have e : (k * ((1 + cd.γ * k) - cd.ρ)
        + cd.ξ t / cd.C t) * cd.C t
        = (k * ((1 + cd.γ * k) - cd.ρ)) * cd.C t + cd.ξ t := by
      field_simp
    rw [← e]
    exact hm
  have hkγ : 0 ≤ k * cd.γ := mul_nonneg hk hγ
  have h3 : k * cd.C (t + 1) ≤ k * ((1 + cd.γ * k) * cd.C t) :=
    mul_le_mul_of_nonneg_left h_C_cap hk
  have h4 : k * ((1 + cd.γ * k) * cd.C t)
      = (k * ((1 + cd.γ * k) - cd.ρ)) * cd.C t
        + cd.ρ * (k * cd.C t) := by ring
  linarith

/-- **The unification bridge**: FrontierScaling's
`frontier_cone_inductive` IS the abstract cone law at
k = α/γ — same hypotheses, same conclusion. The bridge
PROVES the unification instead of asserting it: the
specialized theorem is a thin instantiation of
`cone_data_invariant`. -/
theorem frontier_cone_inductive_is_cone_data
    (C D ξ : ℕ → ℝ) (α γ ρ β : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ) (t : ℕ)
    (hCpos : 0 < C t)
    (hcone : α / γ * C t ≤ D t)
    (h_dyn : ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : C (t + 1) ≤ (1 + α) * C t)
    (hβ : α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β) :
    α / γ * C (t + 1) ≤ D (t + 1) := by
  have hcap : C (t + 1) ≤ (1 + γ * (α / γ)) * C t := by
    have hgg : γ * (α / γ) = α := by
      field_simp
    rw [hgg]
    exact h_C_cap
  have hthr : α / γ * ((1 + γ * (α / γ)) - ρ) + ξ t / C t ≤ β := by
    have hgg : γ * (α / γ) = α := by field_simp
    rw [hgg]
    exact hβ
  exact cone_data_invariant
    { C := C, D := D, ξ := ξ, γ := γ, ρ := ρ, β := β }
    (α / γ) t
    (div_nonneg hα.le hγ.le)
    hγ.le hρ hCpos hcone h_dyn hcap hthr

end Hagi.Growth
