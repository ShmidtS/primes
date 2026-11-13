/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.ErrorProp
import Hagi.Core.RootContrast
import Hagi.Architecture.SpaceDecoupling

/-!
# Cascade leak bound for projected adapters (A8 F1)

Over the abstract linear-cascade carrier of `Hagi.Core.ErrorProp`
(`propagate` over `List (Matrix n n ℝ × (n → ℝ))`), an additive
adapter entering one layer through the complement projection leaks
to the output by at most the router weight times the stack gain
times the adapter operator norm times the reachable input component:

* `cascade_leak_bound` — generic entering-vector form:
  `‖propagate S (x + w • ε) − propagate S x‖ ≤ |w| · cascadeGain S · ‖ε‖`.
* `cascade_leak_bound_op` — the adapter form
  `ε = ΔR *ᵥ (projR U *ᵥ x)`:
  `≤ |w| · cascadeGain S · ‖ΔR‖ · ‖projR U *ᵥ x‖`, i.e.
  `‖net(W + w·Δ_R, x) − net(W, x)‖ ≤ |w| · L_stack · ‖Δ_R‖_op · ‖P_R x‖`
  with `L_stack = ∏ L_m` (`cascadeGain`) and `P_R = projR U`
  (`Hagi.Architecture.SpaceDecoupling`).
* `cascade_leak_bound_contractive` — non-expansive stack
  (`‖p.1‖ ≤ 1`, the `propagate_bound_contractive` shape): the gain
  drops out.
* `cascade_leak_router_linear` — the leak is EXACTLY linear in the
  router weight `w`: the leak at `w` is `w •` the leak at `1`.
* `cascade_leak_eq_empty` — tightness: at the empty stack the bound
  is attained with equality.
* `tailDiag_mulVec_norm_le` + `cascade_leak_bound_rhoTail` — the
  spectral-tail tie: for the tail-spectrum adapter `tailDiag m r s`
  (rank-`r` capture leaves indices `j ≥ r` live), the leak scales as
  `sqrt (rhoTail m s r · ∑ (s j)^2)` (`Hagi.Core.RootContrast`).
* `readback_noise_witness` — the one-sided-isolation caveat witness:
  in-span noise `n` with `Uᵀ *ᵥ n ≠ 0` exists whenever `0 < c`, so
  `Uᵀ * A_orth = 0` (`fiberSplitOrtho`) protects the injection
  (`fiber_injection_preserves_cortex`) but NOT the fiber readback
  `Uᵀ h`, which needs gating (`w → 0`) or the
  `spaceDecoupling_zero_drift` premise `Uᵀ *ᵥ Δ = 0`.

Model boundary (honest): this is the LINEAR-cascade slice of the A8
empirical verdict — `w = 0.1` gives exactly one tenth of the `w = 1`
leak here (`cascade_leak_router_linear`), and projection alone never
zeroes the bound (only the router `w → 0` or rank capture
`rhoTail → 0` do). The nonlinear-net behavior (measured ForgettingCE
gap at `w = 1`) is motivation, not a premise; see `ALGORITHMS.md`.
-/

namespace Hagi.Architecture

open Finset Matrix
open scoped Matrix Matrix.Norms.Operator

/-! ## The composition bound -/

/-- Main composition lemma (entering-vector form): the output leak
of an input perturbation `w • ε` through the cascade `S` is at most
`|w| * cascadeGain S * ‖ε‖`. No hypotheses beyond the carrier. -/
theorem cascade_leak_bound {d : ℕ}
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ)))
    (w : ℝ) (ε : Fin d → ℝ) (x : Fin d → ℝ) :
    ‖Hagi.Core.propagate S (x + w • ε) - Hagi.Core.propagate S x‖
      ≤ |w| * Hagi.Core.cascadeGain S * ‖ε‖ := by
  have hx : x + w • ε - x = w • ε := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Hagi.Core.propagate_sub, hx, Hagi.Core.propagateLin_smul,
    show ‖w • Hagi.Core.propagateLin S ε‖ = |w| * ‖Hagi.Core.propagateLin S ε‖ from
      norm_smul w (Hagi.Core.propagateLin S ε), mul_assoc]
  exact mul_le_mul_of_nonneg_left (Hagi.Core.propagateLin_norm_le S ε)
    (abs_nonneg w)

/-- The A8 F1 target form: with the adapter path
`ε = ΔR *ᵥ (projR U *ᵥ x)` (adapter applied to the reachable,
complement-projected input component),
`‖propagate S (x + w • ε) − propagate S x‖ ≤
|w| * cascadeGain S * ‖ΔR‖ * ‖projR U *ᵥ x‖` — i.e.
`|w_route| · L_stack · ‖Δ_R‖_op · ‖P_R x‖` with the honest
per-layer product `L_stack = cascadeGain S` and `P_R = projR U`. -/
theorem cascade_leak_bound_op {d c : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ)))
    (w : ℝ) (ΔR : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    ‖Hagi.Core.propagate S (x + w • (ΔR *ᵥ (projR U *ᵥ x)))
        - Hagi.Core.propagate S x‖
      ≤ |w| * Hagi.Core.cascadeGain S * ‖ΔR‖ * ‖projR U *ᵥ x‖ := by
  have h1 := cascade_leak_bound S w (ΔR *ᵥ (projR U *ᵥ x)) x
  have h2 : ‖ΔR *ᵥ (projR U *ᵥ x)‖ ≤ ‖ΔR‖ * ‖projR U *ᵥ x‖ :=
    (Matrix.linfty_opNorm_mulVec ΔR (projR U *ᵥ x)).trans
      (mul_le_mul_of_nonneg_right le_rfl (norm_nonneg _))
  have hG : 0 ≤ Hagi.Core.cascadeGain S :=
    List.prod_nonneg (by
      intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨q, _, rfl⟩ := hz
      exact norm_nonneg q.1)
  calc ‖Hagi.Core.propagate S (x + w • (ΔR *ᵥ (projR U *ᵥ x)))
        - Hagi.Core.propagate S x‖
      ≤ |w| * Hagi.Core.cascadeGain S * ‖ΔR *ᵥ (projR U *ᵥ x)‖ := h1
    _ ≤ |w| * Hagi.Core.cascadeGain S * (‖ΔR‖ * ‖projR U *ᵥ x‖) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg w) hG)
    _ = |w| * Hagi.Core.cascadeGain S * ‖ΔR‖ * ‖projR U *ᵥ x‖ := by ring

/-- Non-expansive stack (`‖p.1‖ ≤ 1` for every layer, the
`Hagi.Core.propagate_bound_contractive` hypothesis shape): the stack
gain drops out of the leak bound. -/
theorem cascade_leak_bound_contractive {d c : ℕ}
    (U : Matrix (Fin d) (Fin c) ℝ)
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ)))
    (hα : ∀ p ∈ S, ‖p.1‖ ≤ 1)
    (w : ℝ) (ΔR : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    ‖Hagi.Core.propagate S (x + w • (ΔR *ᵥ (projR U *ᵥ x)))
        - Hagi.Core.propagate S x‖
      ≤ |w| * ‖ΔR‖ * ‖projR U *ᵥ x‖ := by
  have h := cascade_leak_bound_op U S w ΔR x
  have h1 := Hagi.Core.cascadeGain_le_one S hα
  have hG : 0 ≤ Hagi.Core.cascadeGain S :=
    List.prod_nonneg (by
      intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨q, _, rfl⟩ := hz
      exact norm_nonneg q.1)
  calc ‖Hagi.Core.propagate S (x + w • (ΔR *ᵥ (projR U *ᵥ x)))
        - Hagi.Core.propagate S x‖
      ≤ |w| * Hagi.Core.cascadeGain S * ‖ΔR‖ * ‖projR U *ᵥ x‖ := h
    _ ≤ |w| * 1 * ‖ΔR‖ * ‖projR U *ᵥ x‖ := by gcongr
    _ = |w| * ‖ΔR‖ * ‖projR U *ᵥ x‖ := by ring

/-- The leak is EXACTLY linear in the router weight: the output
difference at weight `w` is `w •` the difference at weight `1`
(the linear-cascade form of the router scaling: at `w` a tenth of
`1`, the leak is exactly a tenth). -/
theorem cascade_leak_router_linear {d : ℕ}
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ)))
    (w : ℝ) (ΔR : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    Hagi.Core.propagate S (x + w • (ΔR *ᵥ x)) - Hagi.Core.propagate S x
      = w • (Hagi.Core.propagate S (x + ΔR *ᵥ x)
          - Hagi.Core.propagate S x) := by
  have hw : x + w • (ΔR *ᵥ x) - x = w • (ΔR *ᵥ x) := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 : x + ΔR *ᵥ x - x = ΔR *ᵥ x := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [Hagi.Core.propagate_sub, Hagi.Core.propagate_sub, hw, h1,
    Hagi.Core.propagateLin_smul]

/-- Tightness: at the empty stack the leak is exactly the entering
vector, so `cascade_leak_bound` is attained (equality) — the bound
is nonzero and informative whenever `|w| * ‖ε‖ > 0`. -/
theorem cascade_leak_eq_empty {d : ℕ} (w : ℝ) (ε x : Fin d → ℝ) :
    Hagi.Core.propagate
        ([] : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ)))
        (x + w • ε)
      - Hagi.Core.propagate [] x = w • ε := by
  simp [Hagi.Core.propagate]

/-! ## The spectral-tail tie (`rhoTail`) -/

/-- The tail-spectrum adapter: the diagonal matrix that leaves
spectral indices `j ≥ r` live (rank-`r` capture) and zeroes the
captured indices `j < r`. -/
def tailDiag (m r : ℕ) (s : ℕ → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal fun j => if r ≤ (j : ℕ) then s j else 0

/-- Index transfer between the `Finset.range` filter of
`Hagi.Core.rhoTail` and the `Finset.univ` filter over `Fin m`. -/
theorem sum_range_filter_eq_univ_filter (m r : ℕ) (s : ℕ → ℝ) :
    ∑ j ∈ Finset.filter (fun j : ℕ => r ≤ j) (Finset.range m), (s j)^2
      = ∑ j ∈ Finset.filter (fun j : Fin m => r ≤ (j : ℕ)) Finset.univ,
          (s ↑j)^2 := by
  have hR : ∑ j ∈ Finset.filter (fun j : Fin m => r ≤ (j : ℕ)) Finset.univ,
        (s ↑j)^2
      = ∑ j : Fin m, if r ≤ (j : ℕ) then (s ↑j)^2 else 0 :=
    Finset.sum_filter _ _
  rw [hR, Fin.sum_univ_eq_sum_range (f := fun j => if r ≤ j then (s j)^2 else 0),
    ← Finset.sum_filter (fun j : ℕ => r ≤ j) (fun j => (s j)^2)]

/-- The tail-spectrum adapter acts by at most the tail `ℓ₂` mass:
`‖tailDiag m r s *ᵥ y‖ ≤ sqrt (rhoTail m s r * ∑ (s j)^2) * ‖y‖`
(the largest live tail entry is at most the square root of the tail
spectral energy; `Hagi.Core.rhoTail` supplies the normalization). -/
theorem tailDiag_mulVec_norm_le (m r : ℕ) (s : ℕ → ℝ)
    (htot : 0 < ∑ j ∈ Finset.range m, (s j)^2) (y : Fin m → ℝ) :
    ‖tailDiag m r s *ᵥ y‖
      ≤ Real.sqrt (Hagi.Core.rhoTail m s r * ∑ j ∈ Finset.range m, (s j)^2)
          * ‖y‖ := by
  have hnn : 0 ≤ Real.sqrt (Hagi.Core.rhoTail m s r
      * ∑ j ∈ Finset.range m, (s j)^2) :=
    Real.sqrt_nonneg _
  have hmemsq : ∀ i : Fin m,
      ((if r ≤ (i : ℕ) then s i else 0))^2
        ≤ ∑ j ∈ Finset.filter (fun j : ℕ => r ≤ j) (Finset.range m), (s j)^2 := by
    intro i
    by_cases hi : r ≤ (i : ℕ)
    · simp only [hi, ite_true]
      have hle : (s i)^2
          ≤ ∑ j ∈ Finset.filter (fun j : Fin m => r ≤ (j : ℕ)) Finset.univ,
              (s ↑j)^2 := by
        refine Finset.single_le_sum (fun (j : Fin m) _ => sq_nonneg (s ↑j)) ?_
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [← sum_range_filter_eq_univ_filter] at hle
      exact hle
    · simp only [hi, ite_false]
      have h0 : (0:ℝ)^2 = 0 := by ring
      rw [h0]
      exact Finset.sum_nonneg (fun j _ => sq_nonneg (s j))
  have hsq : ∀ i : Fin m,
      |(if r ≤ (i : ℕ) then s i else 0)|
        ≤ Real.sqrt (Hagi.Core.rhoTail m s r
            * ∑ j ∈ Finset.range m, (s j)^2) := by
    intro i
    refine Real.le_sqrt_of_sq_le ?_
    rw [sq_abs]
    have heq : Hagi.Core.rhoTail m s r * ∑ j ∈ Finset.range m, (s j)^2
        = ∑ j ∈ Finset.filter (fun j : ℕ => r ≤ j) (Finset.range m), (s j)^2 := by
      unfold Hagi.Core.rhoTail
      rw [div_mul_cancel₀ _ (ne_of_gt htot)]
    rw [heq]
    exact hmemsq i
  have hyi : ∀ i : Fin m, |y i| ≤ ‖y‖ := fun i =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mp (le_refl _) i
  have hentry : ∀ i : Fin m,
      ‖(tailDiag m r s *ᵥ y) i‖
        ≤ Real.sqrt (Hagi.Core.rhoTail m s r
            * ∑ j ∈ Finset.range m, (s j)^2) * ‖y‖ := by
    intro i
    have hd : (tailDiag m r s *ᵥ y) i
        = (if r ≤ (i : ℕ) then s i else 0) * y i := by
      simp only [tailDiag, Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
        mul_ite, zero_mul, Finset.sum_ite_eq']
      simp
    rw [hd, Real.norm_eq_abs, abs_mul]
    calc |(if r ≤ (i : ℕ) then s i else 0)| * |y i|
        ≤ Real.sqrt (Hagi.Core.rhoTail m s r
            * ∑ j ∈ Finset.range m, (s j)^2) * |y i| :=
            mul_le_mul_of_nonneg_right (hsq i) (abs_nonneg _)
      _ ≤ Real.sqrt (Hagi.Core.rhoTail m s r
            * ∑ j ∈ Finset.range m, (s j)^2) * ‖y‖ :=
            mul_le_mul_of_nonneg_left (hyi i) hnn
  exact (pi_norm_le_iff_of_nonneg (mul_nonneg hnn (norm_nonneg y))).mpr hentry

/-- The F1 bound with the adapter specialized to the tail spectrum:
the leak is at most `|w| * cascadeGain S * sqrt (rhoTail m s r *
∑ (s j)^2) * ‖projR U *ᵥ x‖` — projection alone leaves the
`sqrt rhoTail · router` product; rank capture (`rhoTail → 0`) or the
router (`w → 0`) kill it. -/
theorem cascade_leak_bound_rhoTail (m r : ℕ) (s : ℕ → ℝ)
    (htot : 0 < ∑ j ∈ Finset.range m, (s j)^2) (c : ℕ)
    (U : Matrix (Fin m) (Fin c) ℝ)
    (S : List (Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ)))
    (w : ℝ) (x : Fin m → ℝ) :
    ‖Hagi.Core.propagate S (x + w • (tailDiag m r s *ᵥ (projR U *ᵥ x)))
        - Hagi.Core.propagate S x‖
      ≤ |w| * Hagi.Core.cascadeGain S
          * Real.sqrt (Hagi.Core.rhoTail m s r
              * ∑ j ∈ Finset.range m, (s j)^2)
          * ‖projR U *ᵥ x‖ := by
  have h1 := cascade_leak_bound S w (tailDiag m r s *ᵥ (projR U *ᵥ x)) x
  have h2 := tailDiag_mulVec_norm_le m r s htot (projR U *ᵥ x)
  have hG : 0 ≤ Hagi.Core.cascadeGain S :=
    List.prod_nonneg (by
      intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨q, _, rfl⟩ := hz
      exact norm_nonneg q.1)
  calc ‖Hagi.Core.propagate S (x + w • (tailDiag m r s *ᵥ (projR U *ᵥ x)))
        - Hagi.Core.propagate S x‖
      ≤ |w| * Hagi.Core.cascadeGain S
          * ‖tailDiag m r s *ᵥ (projR U *ᵥ x)‖ := h1
    _ ≤ |w| * Hagi.Core.cascadeGain S
          * (Real.sqrt (Hagi.Core.rhoTail m s r
              * ∑ j ∈ Finset.range m, (s j)^2) * ‖projR U *ᵥ x‖) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg w) hG)
    _ = |w| * Hagi.Core.cascadeGain S
          * Real.sqrt (Hagi.Core.rhoTail m s r
              * ∑ j ∈ Finset.range m, (s j)^2)
          * ‖projR U *ᵥ x‖ := by ring

/-! ## One-sided isolation caveat (readback) -/

/-- The one-sided-isolation caveat witness: whenever the cortex is
nontrivial (`0 < c`) there is state noise `n ≠ 0` whose readback
`Uᵀ *ᵥ n` is nonzero (take the in-span direction
`U *ᵥ Pi.single 0 1`). So the adapter-side isolation
`Uᵀ * A_orth = 0` (`fiberSplitOrtho`,
`fiber_injection_preserves_cortex`) does NOT protect the fiber
readback `Uᵀ h` from state noise with an invariant-subspace
component: readback protection needs gating (router weight `0`) or
the noise premise of `spaceDecoupling_zero_drift`
(`Uᵀ *ᵥ Δ = 0`). -/
theorem readback_noise_witness {d c : ℕ} (hc : 0 < c)
    (U : Matrix (Fin d) (Fin c) ℝ) (hU : IsOrthoCol U) :
    ∃ n : Fin d → ℝ, n ≠ 0 ∧ Uᵀ *ᵥ n ≠ 0 := by
  have h1 : Uᵀ *ᵥ (U *ᵥ (Pi.single (⟨0, hc⟩ : Fin c) 1))
      = (Pi.single (⟨0, hc⟩ : Fin c) 1 : Fin c → ℝ) := by
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  have h2 : (Pi.single (⟨0, hc⟩ : Fin c) 1 : Fin c → ℝ) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hc⟩
    simp at this
  refine ⟨U *ᵥ (Pi.single (⟨0, hc⟩ : Fin c) 1), ?_, ?_⟩
  · intro h0
    apply h2
    rw [← h1, h0, Matrix.mulVec_zero]
  · rw [h1]
    exact h2

end Hagi.Architecture
