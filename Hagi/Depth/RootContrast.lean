/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# RootContrast: the lossless hierarchical channel root ⊕ contrast

The root/contrast split: `rootPart x` is the constant mean
family, `contrastPart x = x - rootPart x` the centered part.

* T1 (`root_idem`, `contrast_zero_sum`, `contrast_of_root`,
  `root_contrast_orth_total`, `root_contrast_pythagoras`) —
  the split is a lossless pair of complementary projections:
  root idempotent, contrast zero-sum, parts orthogonal, energy
  splits exactly (Pythagoras).
* T2 (`filter_partition_sum`, `highway_gain_identity`) — the
  highway's advantage over root-only at the same rank budget
  is exactly the captured contrast energy
  `∑_{j < r_c} s j ^ 2`.
* `rhoCaptured` / `rhoTail` / `rho_partition` — the captured
  and tail fractions of the contrast spectral energy sum to 1.
-/

open Finset InnerProductSpace Real

namespace Hagi.Depth

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

/-- The highway gain identity: the root-only error
`E_root r_root + ∑ s j ^ 2` minus the highway error
`E_root r_root + tail(r_c)` equals exactly the captured
contrast energy `∑_{j < r_c} s j ^ 2`. -/
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

section RhoDefs

/-- The contrast spectral energy captured by rank r
(normalized). -/
noncomputable def rhoCaptured (m : ℕ) (s : ℕ → ℝ) (r : ℕ) : ℝ :=
  (∑ j ∈ (Finset.range m).filter (fun j => j < r), s j^2)
    / (∑ j ∈ Finset.range m, s j^2)

/-- The contrast spectral TAIL fraction at rank r (the
uncaptured remainder). -/
noncomputable def rhoTail (m : ℕ) (s : ℕ → ℝ) (r : ℕ) : ℝ :=
  (∑ j ∈ (Finset.range m).filter (fun j => r ≤ j), s j^2)
    / (∑ j ∈ Finset.range m, s j^2)

/-- The two normalized fractions sum to one:
`rhoCaptured m s r + rhoTail m s r = 1`. -/
theorem rho_partition (m : ℕ) (s : ℕ → ℝ) (r : ℕ)
    (hpos : (0:ℝ) < ∑ j ∈ Finset.range m, s j^2) :
    rhoCaptured m s r + rhoTail m s r = 1 := by
  have hpart := filter_partition_sum m s r
  unfold rhoCaptured rhoTail
  change (∑ j ∈ (Finset.range m).filter (fun j => j < r), s j^2) / (∑ j ∈ Finset.range m, s j^2)
      + (∑ j ∈ (Finset.range m).filter (fun j => r ≤ j), s j^2) / (∑ j ∈ Finset.range m, s j^2) = 1
  field_simp
  linarith [hpart]

end RhoDefs

end Hagi.Depth

namespace Hagi
export Hagi.Depth (rootPart contrastPart root_sum_eq root_idem contrast_zero_sum contrast_of_root root_contrast_orth_total root_contrast_pythagoras filter_partition_sum highway_gain_identity rhoCaptured rhoTail rho_partition)
end Hagi
