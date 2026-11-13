/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.AnytimeMartingale

/-!
# Stitching of e-processes into a master e-process

Finite-family stitching for the slow-loop 3b commit gate: given a
finite family of nonnegative supermartingales `E i` (anytime
e-processes) and nonnegative prior weights `w i`, the weighted master
process `M := ∑ i, w i • E i` is again a nonnegative supermartingale,
and when the prior mass `∑ i, w i ≤ 1` the master inherits the
Ville time-uniform false-alarm control
`μ.real {∃ t ≤ n, δ⁻¹ ≤ M t} ≤ δ` for every horizon `n` at once.

* `stitching_master_supermartingale` — closure of nonnegative
  supermartingales under nonneg finite weighted sums (Mathlib canon
  `Supermartingale.add` / `Supermartingale.smul_nonneg`, Finset
  induction; empty-family case gated by `[Nonempty k]` since the
  zero-process certificate needs a norm instance unavailable on the
  bare `ℕ → Ω → ℝ` Pi type — the repo-wide convention).
* `stitching_master_nonneg` — the master is nonnegative.
* `stitching_master_initial_mass` — `μ[M 0] = ∑ i, w i * μ[E i 0]`.
* `stitching_eprocess_anytime` — MAIN: with `∑ i, w i ≤ 1` and
  `0 < δ`: `μ.real {ω | ∃ t ≤ n, δ⁻¹ ≤ M t ω} ≤ δ` uniformly in `n`,
  by the existing `ville_anytime_false_alarm` (cited by exact name;
  the Ville stopping-time argument is NOT duplicated here).

Honesty boundaries (documented deferrals):

* Countable-family stitching (countable weights, tsum closure with
  a.e. summability) is DEFERRED — it adds genuine measure-theoretic
  noise, and the slow-loop consumer commits against finitely many
  e-processes. The finite family is the honest primary form.
* Each `E i` is a hypothesis (premise-form): this file proves the
  stitching closure and the budget transfer, not the construction of
  the per-expert e-processes (those come from the Freedman anytime
  family results, e.g. `Hagi/Probability/Freedman*.lean`); the
  initial-mass normalization `μ[E i 0] ≤ 1` of each expert is a
  premise (`hE0`) — it is part of what makes each `E i` an
  anytime-valid unit-budget e-process.
-/

open Finset MeasureTheory ProbabilityTheory

namespace Hagi.Unified

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}
  {k : Type} [Fintype k] [DecidableEq k] [Nonempty k]

/-- The stitched master process of a finite e-process family:
`M = ∑ i, w i • E i`. -/
def stitchedMaster (w : k → ℝ) (E : k → ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  ∑ i, w i • E i

/-- **Stitching closure**: a finite nonneg-weighted sum of
supermartingales is a supermartingale (Finset induction over the
family; singleton steps are `Supermartingale.smul_nonneg`, joins are
`Supermartingale.add`). -/
theorem stitching_master_supermartingale (w : k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (E : k → ℕ → Ω → ℝ) (hE : ∀ i, Supermartingale (E i) 𝒢 μ) :
    Supermartingale (stitchedMaster w E) 𝒢 μ := by
  have key : ∀ s : Finset k, s.Nonempty →
      Supermartingale (∑ i ∈ s, w i • E i) 𝒢 μ := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro hne
      exact absurd rfl hne.ne_empty.symm
    · intro a s ha hs hne
      rw [Finset.sum_insert ha]
      rcases s.eq_empty_or_nonempty with hse | hsne
      · rw [hse, Finset.sum_empty, add_zero]
        exact (hE a).smul_nonneg (hw a)
      · rw [add_comm]
        exact (hs hsne).add ((hE a).smul_nonneg (hw a))
  exact key Finset.univ Finset.univ_nonempty

/-- The stitched master of nonnegative e-processes is nonnegative. -/
theorem stitching_master_nonneg (w : k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (E : k → ℕ → Ω → ℝ) (hEnn : ∀ i, 0 ≤ E i) :
    0 ≤ stitchedMaster w E := by
  unfold stitchedMaster
  intro t ω
  simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hEnn i t ω)

/-- Initial mass of the master: `μ[M 0] = ∑ i, w i * μ[E i 0]`
(integrability from `Supermartingale.integrable`). -/
theorem stitching_master_initial_mass (w : k → ℝ) (E : k → ℕ → Ω → ℝ)
    (hE : ∀ i, Supermartingale (E i) 𝒢 μ) :
    μ[stitchedMaster w E 0] = ∑ i, w i * μ[E i 0] := by
  have hint : ∀ i, Integrable (E i 0) μ := fun i => (hE i).integrable 0
  have happ : stitchedMaster w E 0 = fun ω => ∑ i, w i * E i 0 ω := by
    funext ω
    simp [stitchedMaster, Finset.sum_apply, Pi.smul_apply]
  show ∫ x, stitchedMaster w E 0 x ∂μ = ∑ i, w i * ∫ x, E i 0 x ∂μ
  rw [happ]
  change ∫ x, ∑ i, w i * E i 0 x ∂μ = ∑ i, w i * ∫ x, E i 0 x ∂μ
  calc ∫ x, ∑ i, w i * E i 0 x ∂μ
      = ∑ i, ∫ x, w i * E i 0 x ∂μ :=
        integral_finsetSum Finset.univ (fun i _ => (hint i).const_mul (w i))
    _ = ∑ i, w i * ∫ x, E i 0 x ∂μ :=
        Finset.sum_congr rfl fun i _ => integral_const_mul (w i) (fun ω => E i 0 ω)

/-- **Stitched anytime validity (MAIN)**: a finite family of
nonnegative supermartingales with prior weights summing to at most 1
stitches into a master e-process with the Ville time-uniform bound
`μ.real {∃ t ≤ n, δ⁻¹ ≤ M t} ≤ δ`, for every horizon `n` at once.
Direct corollary of `ville_anytime_false_alarm` — the Ville
stopping-time argument itself is not repeated. -/
theorem stitching_eprocess_anytime (w : k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i ≤ 1) (E : k → ℕ → Ω → ℝ)
    (hE : ∀ i, Supermartingale (E i) 𝒢 μ) (hEnn : ∀ i, 0 ≤ E i)
    (hE0 : ∀ i, μ[E i 0] ≤ 1)
    {delta : ℝ} (hdelta : 0 < delta) (n : ℕ) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1), delta⁻¹ ≤ stitchedMaster w E t ω}
      ≤ delta := by
  have hM := stitching_master_supermartingale w hw E hE
  have hMnn : 0 ≤ stitchedMaster w E :=
    stitching_master_nonneg w hw E hEnn
  have hmass : μ[stitchedMaster w E 0] ≤ 1 := by
    rw [stitching_master_initial_mass w E hE]
    calc ∑ i, w i * μ[E i 0] ≤ ∑ i, w i * 1 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hE0 i) (hw i)
      _ = ∑ i, w i := Finset.sum_congr rfl fun i _ => mul_one _
      _ ≤ 1 := hwsum
  exact ville_anytime_false_alarm hM hMnn hmass n hdelta

end Hagi.Unified
