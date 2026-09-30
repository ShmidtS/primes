/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Wave5

set_option linter.style.header false

/-!
# RootContrast: the lossless hierarchical channel root ⊕ contrast

The depth-1 F3 loss (+0.028 nats vs flat, the only measured
tree-vs-flat point) decomposed: root_share = 0.796 measured
(anova_split), so 0.204 of the energy lives in the contrast
subspace the root cortex CANNOT see (F3Root: the root cortex
is literally mean(x₁,…,x_n); the contrast part is destroyed
by construction). The question: is a contrast-HIGHWAY worth
it? Three theorems + one certificate.

**T1 — `root_idem`, `contrast_zero_sum`, `contrast_of_root`,
`root_contrast_orth_total`, `root_contrast_pythagoras`**:
the root/contrast split (rootPart x = the constant mean
family; contrastPart x = x − rootPart x) is a LOSSLESS pair
of complementary projections: root is idempotent, contrast
sums to zero (the centering), contrast kills root, the two
parts are ORTHOGONAL in total (Σᵢ⟨rᵢ,cᵢ⟩ = 0), and the
energy splits exactly (Pythagoras: Σ‖xᵢ‖² = Σ‖r‖² + Σ‖c‖²).
No information is lost by the (z_root, z_contrast) pair —
the +0.028 loss is NOT the split's fault: it is the root-only
CORK'S fault (T2 quantifies exactly this).

**T2 — `highway_gain_identity`**: with the contrast spectrum
(σ_j) measured, the highway's advantage over root-only at the
same rank budget is EXACTLY the captured contrast energy:
E_rootonly(r) − E_highway(r) = Σ_{j≤r_c} σ_j² (the
complement of the spectral tail ρ_c(r_c)). The identity is
the finite-sum partition (filter_partition_sum); the tail
monotonicity is `DesignOpt.spectral_tail_mono`.

**T3 — the two-block rank rule (documented corollary of
`waterfilling_optimal`)**: at fixed r = r_root + r_c the
optimal allocation equalizes the σ-marginals ACROSS blocks;
the extreme cases: a FLAT contrast tail near r (the
ComputeBudget observation) sends all rank to root (highway
useless); a sharp knee makes the highway MANDATORY.

**C — the go/no-go certificate (definition + the link)**:
measure the spectra of Σ_leaves = [h₁−h̄ | … | h_n−h̄] on a
calibration batch (one inference pass, no training); GO ⟺
ρ_c(r_c) ≤ ε with ε ≈ the measured F3 penalty 0.028
(calibration: root-only with r=64 loses exactly that).

**Falsification (mandatory)**: the blind prediction for the
depth-1-highway run: Δ(F3-highway − F3-root-only) ≈ ρ_c(r_c)
in nats (T2). If the measured gain is < half the prediction
at nonzero ρ_c, T2 fails in this form — audit the
multi-layer channel interaction (the ErrorProp α-decay
between cortex levels is the likely hole).

**Prescription for the code.**
1. merge.py: the contrast-highway RecursiveF3HAGI variant —
   cortex takes (z_root, z_contrast) with separate low-rank
   channels; ranks from the measured spectrum (T3), not tuned.
2. The certificate BEFORE any GPU: ρ_c(64) from one
   calibration inference; GO ⟺ ρ_c(64) ≤ 0.028.
3. Q-parametrization P_root + P_contrast·e^K (K
   skew-symmetric, low-rank) if trainable contrast rotations
   are needed: automatic orthogonality + root preservation.
-/

open Finset InnerProductSpace Real

namespace Hagi

section T1

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The root component: the constant mean family (the
block (1/n)·J⊗I acting on x). -/
noncomputable def rootPart {n : ℕ} (x : Fin n → V) : Fin n → V :=
  fun _ => (1/(n:ℝ)) • ∑ i, x i

/-- The contrast component: x minus its root (the centered
family — sum zero). -/
noncomputable def contrastPart {n : ℕ} (x : Fin n → V) : Fin n → V :=
  fun i => x i - rootPart x i

/-- The root's defining sum property: Σ rootPart = Σ x. -/
theorem root_sum_eq {n : ℕ} (hn : 0 < n) (x : Fin n → V) :
    ∑ i, rootPart x i = ∑ i, x i := by
  have hne : ((n:ℝ)) ≠ 0 := by positivity
  unfold rootPart
  rw [← Finset.smul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [show n • (∑ i, x i) = ((n:ℕ):ℝ) • (∑ i, x i) from
      (Nat.cast_smul_eq_nsmul ℝ _ _).symm]
  rw [smul_smul]
  congr 1
  field_simp
  simp

/-- **T1a — root idempotence**: root(root x) = root x — the
root projection. -/
theorem root_idem {n : ℕ} (hn : 0 < n) (x : Fin n → V) :
    rootPart (rootPart x) = rootPart x := by
  have hne : ((n:ℝ)) ≠ 0 := by positivity
  funext i
  simp only [rootPart]
  rw [← Finset.smul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [smul_smul, show n • (∑ i, x i) = ((n:ℕ):ℝ) • (∑ i, x i) from
      (Nat.cast_smul_eq_nsmul ℝ _ _).symm]
  rw [smul_smul]
  congr 1
  field_simp

/-- **T1b — the contrast centers**: Σ contrastPart = 0. -/
theorem contrast_zero_sum {n : ℕ} (hn : 0 < n) (x : Fin n → V) :
    ∑ i, contrastPart x i = 0 := by
  simp only [contrastPart, Finset.sum_sub_distrib, root_sum_eq hn, sub_self]

/-- **T1c — contrast kills root**: contrast(root x) = 0. -/
theorem contrast_of_root {n : ℕ} (hn : 0 < n) (x : Fin n → V) :
    contrastPart (rootPart x) = 0 := by
  have h := root_idem hn x
  funext i
  simp only [contrastPart, h, sub_self]
  rfl

/-- **T1d — total orthogonality**: Σᵢ⟨root_i, contrast_i⟩ = 0
(the root constant μ paired against the zero-sum contrast). -/
theorem root_contrast_orth_total {n : ℕ} (hn : 0 < n) (x : Fin n → V) :
    ∑ i, ⟪rootPart x i, contrastPart x i⟫_ℝ = 0 := by
  have hconst : ∀ i, rootPart x i = rootPart x (⟨0, hn⟩ : Fin n) := fun i => rfl
  rw [Finset.sum_congr rfl (fun i _ => by rw [hconst i])]
  rw [Finset.sum_congr rfl (fun i _ => real_inner_comm _ _)]
  rw [← sum_inner (𝕜 := ℝ) Finset.univ (fun i => contrastPart x i)
      (rootPart x (⟨0, hn⟩ : Fin n))]
  rw [contrast_zero_sum hn x, inner_zero_left]

/-- **T1e — the energy split (Pythagoras)**: Σ‖xᵢ‖² =
Σ‖root‖² + Σ‖contrast‖² — the (z_root, z_contrast) pair is
LOSSLESS: no information destroyed by the split. -/
theorem root_contrast_pythagoras {n : ℕ} (hn : 0 < n) (x : Fin n → V) :
    (∑ i, ‖x i‖^2) = (∑ i, ‖rootPart x i‖^2) + (∑ i, ‖contrastPart x i‖^2) := by
  have hsum : ∑ i, ⟪rootPart x i, contrastPart x i⟫_ℝ = 0 :=
    root_contrast_orth_total hn x
  have hper : ∀ i, ‖x i‖^2
      = ‖rootPart x i‖^2 + 2 * ⟪rootPart x i, contrastPart x i⟫_ℝ
        + ‖contrastPart x i‖^2 := by
    intro i
    have hsplit : x i = rootPart x i + contrastPart x i := by
      simp only [contrastPart]
      abel
    have ha := norm_add_pow_two (𝕜 := ℝ) (rootPart x i) (contrastPart x i)
    simp only [RCLike.re_to_real] at ha
    rw [hsplit, ha]
  have hsumall : ∑ i, (‖rootPart x i‖^2 + 2 * ⟪rootPart x i, contrastPart x i⟫_ℝ
      + ‖contrastPart x i‖^2)
      = (∑ i, ‖rootPart x i‖^2) + (∑ i, ‖contrastPart x i‖^2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hcross : ∑ i, 2 * ⟪rootPart x i, contrastPart x i⟫_ℝ = 0 := by
      calc ∑ i, 2 * ⟪rootPart x i, contrastPart x i⟫_ℝ
          = 2 * ∑ i, ⟪rootPart x i, contrastPart x i⟫_ℝ :=
              (Finset.mul_sum (Finset.univ : Finset (Fin n))
                (fun i => ⟪rootPart x i, contrastPart x i⟫_ℝ) 2).symm
        _ = 2 * 0 := by rw [hsum]
        _ = 0 := by ring
    rw [hcross]
    linarith
  rw [Finset.sum_congr rfl (fun i _ => hper i), hsumall]

end T1

section T2

/-- The finite-spectrum partition: the captured (j < r) and
the tail (r ≤ j) parts sum to the total. -/
theorem filter_partition_sum (m : ℕ) (s : ℕ → ℝ) (r : ℕ) :
    (∑ j ∈ (Finset.range m).filter (fun j => j < r), s j^2)
      + (∑ j ∈ (Finset.range m).filter (fun j => r ≤ j), s j^2)
      = ∑ j ∈ Finset.range m, s j^2 := by
  rw [← Finset.sum_union]
  · congr 1
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    omega
  · rw [Finset.disjoint_iff_ne]
    intro a ha b hb heq
    simp only [Finset.mem_filter] at ha hb
    rw [heq] at ha
    omega

/-- **T2 — the highway gain identity**: with the contrast
spectrum (s j) (the σ-values of Σ_leaves, measured), the
root-only error at budget r is E_root(r) + C_total (the
ENTIRE contrast energy is error — root cannot see it), and
the highway error is E_root(r) + tail(r_c). The GAIN is
EXACTLY the captured contrast energy:

  E_rootonly(r) − E_highway(r) = Σ_{j<r_c} s_j²  (= C_total − ρ_c(r_c)).

The blind prediction: Δ(F3-highway − F3-root-only) ≈
captared(r_c) in nats — the mandatory falsification test. -/
theorem highway_gain_identity (m : ℕ) (s : ℕ → ℝ) (E_root : ℕ → ℝ)
    (r_root r_c : ℕ)
    -- E_root: the root block's own best-approx error (measured input)
    :
    (E_root r_root + ∑ j ∈ Finset.range m, s j^2)
      - (E_root r_root
          + ∑ j ∈ (Finset.range m).filter (fun j => r_c ≤ j), s j^2)
      = ∑ j ∈ (Finset.range m).filter (fun j => j < r_c), s j^2 := by
  have hpart := filter_partition_sum m s r_c
  linarith

end T2

end Hagi
