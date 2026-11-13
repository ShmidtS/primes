/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.OrthoInjection

/-!
# Space decoupling: orthogonal I/R fiber decomposition of updates

For an orthonormal cortex basis `U` (`IsOrthoCol U`, reusing the
`OrthoInjection` carrier), the identity splits into the orthogonal
projections `P_I = U * Uᵀ` onto the invariant subspace
`I = span(cols U)` and `P_R = 1 − U * Uᵀ` onto its orthogonal
complement `R`:

* `projI_add_projR` — `P_I + P_R = 1` exactly.
* `projI_idem` / `projR_idem` — both projections are idempotent.
* `spaceDecoupling_zero_drift` — an update `Δ` in the complement
  (`Uᵀ * Δ = 0`, i.e. `Δ = P_R Δ` direction) leaves the
  I-coordinates of every state exactly: `Uᵀ *ᵥ (x + Δ) = Uᵀ *ᵥ x`.
* `exists_orth_direction` — whenever `rank(I) = c < d`, the
  complement is nontrivial: there is `v ≠ 0` with `Uᵀ *ᵥ v = 0`
  (finrank contradiction: an injective `Fin d → Fin c` linear map
  cannot exist for `c < d`).
* `spaceDecoupling_capacity` — for such a direction `v`, the
  R-coordinates genuinely move: `P_R *ᵥ v = v ≠ 0`.

Jointly: under `rank(I) < d` the pair (zero drift on I, nonzero
capacity on R) is nonvacuous — R-directions exist, and updates in
them leave the invariant subspace exactly fixed. This is the
projection-level form of the GPM `gpm_zero_forgetting` action
statement (cited; different carrier) and the Space-Decoupled
orthogonal fibers of the model architecture.
-/

namespace Hagi.Architecture

open Finset Matrix

variable {d c : ℕ}

/-- Orthogonal projection onto the invariant subspace
`I = span(columns U)`. -/
def projI (U : Matrix (Fin d) (Fin c) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  U * Uᵀ

/-- Orthogonal projection onto the complement `R` of `I`. -/
def projR (U : Matrix (Fin d) (Fin c) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  1 - U * Uᵀ

/-- The two projections sum to the identity exactly. -/
theorem projI_add_projR (U : Matrix (Fin d) (Fin c) ℝ) :
    projI U + projR U = 1 := by
  unfold projI projR
  rw [eq_comm, add_comm, sub_add_cancel]

/-- `P_I` is idempotent. -/
theorem projI_idem (U : Matrix (Fin d) (Fin c) ℝ) (hU : IsOrthoCol U) :
    projI U * projI U = projI U := by
  unfold projI
  rw [Matrix.mul_assoc U Uᵀ (U * Uᵀ), ← Matrix.mul_assoc Uᵀ U Uᵀ, hU,
    Matrix.one_mul]

/-- `P_R` is idempotent. -/
theorem projR_idem (U : Matrix (Fin d) (Fin c) ℝ) (hU : IsOrthoCol U) :
    projR U * projR U = projR U := by
  have hPP : (U * Uᵀ) * (U * Uᵀ) = U * Uᵀ := projI_idem U hU
  unfold projR
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, hPP, sub_self, sub_zero, one_mul]

/-- **Zero drift on I**: an update `Δ` orthogonal to the cortex
(`Uᵀ * Δ = 0`) leaves the I-coordinates of every state exactly. -/
theorem spaceDecoupling_zero_drift (U : Matrix (Fin d) (Fin c) ℝ)
    (hU : IsOrthoCol U) (x : Fin d → ℝ) (Δ : Fin d → ℝ)
    (hΔ : Uᵀ *ᵥ Δ = 0) :
    Uᵀ *ᵥ (x + Δ) = Uᵀ *ᵥ x := by
  rw [Matrix.mulVec_add, hΔ, add_zero]

/-- If `rank(I) = c < d`, the orthogonal complement is nontrivial:
there exists `v ≠ 0` with `Uᵀ *ᵥ v = 0` (an injective linear map
`Fin d → ℝ → Fin c → ℝ` would force `d ≤ c`). -/
theorem exists_orth_direction (hcd : c < d) (U : Matrix (Fin d) (Fin c) ℝ) :
    ∃ v : Fin d → ℝ, v ≠ 0 ∧ Uᵀ *ᵥ v = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hker : LinearMap.ker (Matrix.toLin' Uᵀ) = ⊥ := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_bot, Matrix.toLin'_apply]
    constructor
    · intro hv
      by_contra v0
      exact hcon v v0 hv
    · intro h
      rw [show v = 0 from h]
      simp
  have hinj : Function.Injective ⇑(Matrix.toLin' Uᵀ) :=
    LinearMap.ker_eq_bot.mp hker
  have h2 : Module.finrank ℝ ↥(Matrix.toLin' Uᵀ).range
      = Module.finrank ℝ (Fin d → ℝ) :=
    LinearMap.finrank_range_of_inj hinj
  have h1 : Module.finrank ℝ ↥(Matrix.toLin' Uᵀ).range
      ≤ Module.finrank ℝ (Fin c → ℝ) :=
    Submodule.finrank_le _
  have hd : Module.finrank ℝ (Fin d → ℝ) = d := by simp
  have hc : Module.finrank ℝ (Fin c → ℝ) = c := by simp
  rw [h2, hd, hc] at h1
  omega

/-- **Nonzero capacity on R**: a nonzero complement direction `v`
is fixed by `P_R`, so the R-coordinates genuinely move under such an
update. -/
theorem spaceDecoupling_capacity (U : Matrix (Fin d) (Fin c) ℝ)
    (hU : IsOrthoCol U) (v : Fin d → ℝ) (hv : v ≠ 0)
    (horth : Uᵀ *ᵥ v = 0) :
    projR U *ᵥ v = v ∧ v ≠ 0 := by
  constructor
  · unfold projR
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec v U Uᵀ,
      horth, Matrix.mulVec_zero, sub_zero]
  · exact hv

end Hagi.Architecture
