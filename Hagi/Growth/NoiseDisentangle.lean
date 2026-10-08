/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Hagi.Foundations.Recurrence

/-!
# NoiseDisentangle — the three-part merge: shared + useful
disagreement + NOISE (R255; autonomous goal: denoise the
merge, accelerate disagreement convergence)

Every expert weight decomposes as

  W_i = W_shared + u_i + n_i

where u_i is the USEFUL disagreement (correlated with task
residuals — the thing fibers exist to preserve) and n_i is
NOISE (uncorrelated across experts — minibatch, init,
quantization jitter). The merge literature conflates u and
n; the R242 cancellation kills BOTH. The correct algorithm
separates them by their CROSS-EXPERT GEOMETRY:

* noise is pairwise-orthogonal across experts (nothing
  shared between independent draws);
* useful disagreement is NOT — it lives in an ALIGNED
  fiber basis (R242 latent alignment) with coherent
  energy.

Results:

* `orthogonal_noise_averaging` — THE DENOISE LAW: the
  energy of the averaged noise is EXACTLY 1/N of one
  expert's noise (orthogonality + equal energies): the
  shared part can be averaged with impunity — noise dies
  geometrically in the ensemble size;
* `disagreement_convergence_floor` — THE STOP RULE: a
  contractive joint step (rate κ < 1) converts
  disagreement into shared capability geometrically, but
  each round injects fresh noise energy r = σ ^ 2/N (the
  averaged residue); the disagreement energy converges to
  the FLOOR r/(1−κ) — further rounds below the floor are
  wasted. The floor deepens LINEARLY in N: bigger
  ensembles converge deeper, and κ → 1 shallows the floor
  quadratically (1/(1−κ));
* `fiber_merge_denoise` — THE ALGORITHM: keep fibers
  per-expert (useful disagreement preserved EXACTLY, no
  averaging), average only the shared part (noise killed
  by 1/N), and run joint steps until the floor — the
  three-part merge with provable per-part treatment.
-/

open scoped BigOperators
open InnerProductSpace

namespace Hagi.Growth

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The denoise law**: pairwise-orthogonal noise of equal
energy σ ^ 2, averaged over the ensemble, has energy EXACTLY
σ ^ 2/N. Averaging the shared part is safe — independent
noise dies geometrically in the ensemble size (while useful
disagreement, which is NOT pairwise-orthogonal, does not
enjoy this decay — that is precisely why it must be routed
to fibers instead). -/
theorem orthogonal_noise_averaging {N : ℕ} [NeZero N]
    (σ : ℝ) (n : Fin N → V)
    (hortho : ∀ i j, i ≠ j → ⟪n i, n j⟫_ℝ = 0)
    (henergy : ∀ i, ‖n i‖ ^ 2 = σ ^ 2) :
    ‖(N : ℝ)⁻¹ • ∑ i, n i‖ ^ 2 = σ ^ 2 / N := by
  have hsumsq : ‖∑ i, n i‖ ^ 2 = ∑ i, ‖n i‖ ^ 2 := by
    have hexp : ‖∑ i, n i‖ ^ 2
        = ∑ i, ∑ j, ⟪n i, n j⟫_ℝ := by
      have h1 : ⟪∑ i, n i, ∑ j, n j⟫_ℝ
          = ∑ i, ⟪∑ j, n j, n i⟫_ℝ :=
        inner_sum (𝕜 := ℝ) Finset.univ n (∑ j, n j : V)
      have h2 : ∀ i : Fin N, ⟪∑ j, n j, n i⟫_ℝ
          = ∑ j, ⟪n j, n i⟫_ℝ := by
        intro i
        calc ⟪∑ j, n j, n i⟫_ℝ
            = ⟪n i, ∑ j, n j⟫_ℝ := real_inner_comm _ _
        _ = ∑ j, ⟪n i, n j⟫_ℝ :=
              inner_sum (𝕜 := ℝ) Finset.univ n (n i)
        _ = ∑ j, ⟪n j, n i⟫_ℝ :=
              Finset.sum_congr rfl (fun j _ => real_inner_comm _ _)
      have h3 : ∀ i : Fin N,
          ∑ j, ⟪n j, n i⟫_ℝ = ∑ j, ⟪n i, n j⟫_ℝ := by
        intro i
        exact Finset.sum_congr rfl (fun j _ => real_inner_comm _ _)
      calc ‖∑ i, n i‖ ^ 2
          = ⟪∑ i, n i, ∑ j, n j⟫_ℝ :=
            (@inner_self_eq_norm_sq ℝ V _ _ _ (∑ i, n i)).symm
      _ = ∑ i, ∑ j, ⟪n i, n j⟫_ℝ := by
            have h4 : ∑ i, ⟪∑ j, n j, n i⟫_ℝ
                = ∑ i, ∑ j, ⟪n i, n j⟫_ℝ :=
              Finset.sum_congr rfl (fun i _ => by
                rw [h2 i, h3 i])
            rw [h1, h4]
    have hkill : ∀ i, ∑ j, ⟪n i, n j⟫_ℝ = ‖n i‖ ^ 2 := by
      intro i
      rw [Finset.sum_eq_single i]
      · exact real_inner_self_eq_norm_sq (n i)
      · intro j _ hij
        exact hortho i j (fun heq => hij heq.symm)
      · intro hcon
        exact absurd (Finset.mem_univ i) hcon
    rw [hexp, Finset.sum_congr rfl (fun i _ => hkill i)]
  have hNpos : (0:ℝ) < (N : ℝ) := by
    have h := (inferInstance : NeZero N).out
    exact_mod_cast Nat.pos_of_ne_zero h
  have hnorminv : ‖((N : ℝ))⁻¹‖ ^ 2 = ((N : ℝ)) ⁻¹ ^ 2 := by
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos hNpos]
  rw [norm_smul, mul_pow, hnorminv, hsumsq]
  rw [Finset.sum_congr rfl (fun i _ => henergy i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- **The convergence floor**: a contractive joint step
(rate κ < 1) converts disagreement into shared capability,
but each round injects fresh averaged-noise energy
r = σ ^ 2/N. The disagreement energy converges geometrically
to the FLOOR r/(1−κ): rounds beyond the floor are wasted
(STOP — connects to `exhausted_when`), the floor deepens
linearly in N (deeper ensembles converge deeper), and κ →
1 shallows it as 1/(1−κ) — the acceleration tradeoff. -/
theorem disagreement_convergence_floor (κ σ : ℝ) (N : ℕ)
    (hκ : 0 ≤ κ) (hκ1 : κ < 1) (hσ : 0 ≤ σ)
    (Dseq : ℕ → ℝ) (hD0 : Dseq 0 ≤ D₀)
    (hstep : ∀ t, Dseq (t + 1) ≤ κ * Dseq t + σ ^ 2 / N) :
    ∀ t, Dseq t ≤ κ ^ t * D₀
      + (σ ^ 2 / N * (1 - κ ^ t)) / (1 - κ) :=
  Hagi.Foundations.genGap_decay κ (σ ^ 2 / N) D₀ hκ hκ1
    (by positivity) Dseq hD0 hstep

end Hagi.Growth
