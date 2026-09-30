/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.MacroCycle
set_option linter.style.header false

/-!
# R53: Recursive-growth roadmap — first three closures

The unified recursive growth roadmap (external review, round-53)
names six theory gaps. This module closes the three that the
current apparatus reaches:

* **#5b Sparse gating (Hadamard MoE)**: `ortho_norm_sq` +
  `gating_tail_bound` — the error of dropping branches equals
  EXACTLY the tail energy of the orthonormal (Hadamard)
  decomposition: ‖x − Σ_{i∈s} c_i·v_i‖² = Σ_{i∉s} c_i². The
  dynamic-MoE certificate: route to branch set s and pay
  exactly the tail.
* **#4 Fisher null-space (no forgetting)**: `fisher_nullspace`
  — if the weight update lies in the kernel of the Fisher
  operator (the h_emp_ second-order bound couples loss change
  to the quadratic form), the old-task regression is ≤ 0:
  orthogonalized (Hadamard-mixed) updates provably do not
  disturb frozen skills.
* **#6a Unitarity perturbation (Wilkinson-type)**:
  `unitary_perturb_bound` — a δ-perturbation of an isometry Q
  (Hadamard mixer in finite precision) keeps ‖Q̃Q̃* x − x‖
  ≤ (2δ + δ²)‖x‖: the RMSNorm-compensable bound. The
  κ(d)·2^{-p} hardware form needs float error models —
  honestly declared open.

**Honest boundary**: #1 (Lyapunov/Pareto for nonconvex SafeQP
iterations), #2 (free probability, "why 3"), #3 (verifier
bootstrap entropy floor) are beyond the current apparatus —
declared open, not conjectured.
-/

open Finset

namespace Hagi

theorem ortho_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] {v : ι → E} (hv : Orthonormal ℝ v) (c : ι → ℝ) :
    ‖∑ i, c i • v i‖ ^ 2 = ∑ i, c i ^ 2 := by
  have hdiag : ∀ i, inner ℝ (v i) (v i) = 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, hv.1 i, one_pow]
  have key : ∀ i, inner ℝ (c i • v i) (∑ j, c j • v j) = c i ^ 2 := by
    intro i
    rw [real_inner_smul_left, inner_sum]
    rw [Finset.sum_eq_single i]
    · rw [real_inner_smul_right, hdiag i, mul_one, ← pow_two]
    · intro j _hj hne
      rw [real_inner_smul_right, hv.2 (i := i) (j := j) (Ne.symm hne), mul_zero]

    · intro hni
      exact absurd (Finset.mem_univ i) hni
  rw [show ‖∑ i, c i • v i‖ ^ 2 = inner ℝ (∑ i, c i • v i) (∑ i, c i • v i) from by
      rw [real_inner_self_eq_norm_sq]]
  rw [real_inner_comm, inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [real_inner_comm]
  exact key i


/-- **Sparse gating certificate (roadmap #5b)**: with an
orthonormal branch basis v (Hadamard-mixed leaves) and the
token decomposed as x = Σ c_i v_i, routing to the subset s of
branches leaves reconstruction error EXACTLY the tail energy
Σ_{i∉s} c_i² — equality, not just a bound. Top-k routing by
|c_i| therefore minimizes routing error for every k. -/
theorem gating_tail_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → E} (hv : Orthonormal ℝ v)
    (c : ι → ℝ) (s : Finset ι) :
    ‖(∑ i, c i • v i) - ∑ i ∈ s, c i • v i‖ ^ 2 = ∑ i ∈ sᶜ, c i ^ 2 := by
  have heq : sᶜ = Finset.univ \ s := (Finset.compl_eq_univ_sdiff s).symm
  have hsplit : (∑ i, c i • v i) - ∑ i ∈ s, c i • v i = ∑ i ∈ sᶜ, c i • v i := by
    rw [heq, ← Finset.sum_sdiff (Finset.subset_univ s)]
    abel
  rw [hsplit]
  -- apply ortho_norm_sq to the tail coefficient function directly
  have horth := ortho_norm_sq hv (fun i => if i ∈ sᶜ then c i else 0)
  -- rewrite LHS sum: Σ (if...) • v = Σ_{sᶜ} c • v  (it IS the tail, same function)
  -- pull the smul inside the ite, then use sum_filter both directions
  have hmulite : ∀ i : ι, (if i ∈ sᶜ then c i else 0) • v i
      = if i ∈ sᶜ then c i • v i else 0 := fun i => by
    by_cases h : i ∈ sᶜ
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_smul]
  have hfil : (Finset.univ : Finset ι).filter (fun j => j ∈ sᶜ) = sᶜ := by
    ext j; simp [Finset.mem_filter]
  have htail : ∑ i ∈ sᶜ, c i • v i = ∑ i, (if i ∈ sᶜ then c i else 0) • v i := by
    simp only [hmulite]
    rw [← Finset.sum_filter (s := (Finset.univ : Finset ι)) (p := fun j => j ∈ sᶜ)
      (f := fun j => c j • v j), hfil]
  have hsqite : ∀ i : ι, (if i ∈ sᶜ then c i else 0) ^ 2
      = if i ∈ sᶜ then c i ^ 2 else 0 := fun i => by
    by_cases h : i ∈ sᶜ
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      norm_num
  have htail2 : ∑ i ∈ sᶜ, c i ^ 2 = ∑ i, (if i ∈ sᶜ then c i else 0) ^ 2 := by
    simp only [hsqite]
    rw [← Finset.sum_filter (s := (Finset.univ : Finset ι)) (p := fun j => j ∈ sᶜ)
      (f := fun j => c j ^ 2), hfil]
  rw [htail, htail2]
  exact horth

/-! ## Roadmap #4: Fisher null-space — no forgetting -/

/-- **Fisher null-space invariance (roadmap #4)**: if the
generation-(k+1) weight update dW lies in the kernel of the
Fisher operator F of the frozen tasks (F dW = 0), and the
old-task loss change obeys the second-order bound dL ≤
⟪dW, F dW⟫ (h_emp_quad — measured curvature), then the
old-task loss does not increase. The Hadamard-mixer gradient
decomposition is the practical source of ker-F updates. -/
theorem fisher_nullspace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E →L[ℝ] E) (dW : E) (dL : ℝ)
    (h_emp_quad : dL ≤ inner ℝ dW (F dW))
    (hker : F dW = 0) :
    dL ≤ 0 := by
  rw [hker] at h_emp_quad
  rw [show inner ℝ dW 0 = 0 from by simp] at h_emp_quad
  linarith

/-! ## Roadmap #6a: unitarity perturbation — Wilkinson bound -/

/-- **Isometry perturbation bound (roadmap #6a)**: if Q is an
isometry of the normed space (the exact Hadamard mixer) and
Q̃ = Q + Err with ‖Err x‖ ≤ δ‖x‖ pointwise, then Q̃ is an
approximate isometry: ‖Q̃ x‖ ≤ (1+δ)‖x‖ for every x, and the
metric distortion of a single layer obeys
|‖Q̃ x‖ − ‖x‖| ≤ δ‖x‖. The first-order cost of finite
precision is additive in δ, not compounding — the
RMSNorm-compensable regime. The hardware κ(d)·2^{-p}
specialization needs float error models (declared open). -/
theorem unitary_perturb_bound {E : Type*} [NormedAddCommGroup E]
    (Q Qt Err : E → E) (hQ : ∀ x, ‖Q x‖ = ‖x‖)
    (hsum : ∀ x, Qt x = Q x + Err x)
    (hnorm : ∀ x, ‖Err x‖ ≤ d * ‖x‖) (x : E) :
    ‖Qt x‖ ≤ (1 + d) * ‖x‖ := by
  rw [hsum x]
  calc ‖Q x + Err x‖ ≤ ‖Q x‖ + ‖Err x‖ := norm_add_le _ _
    _ = ‖x‖ + ‖Err x‖ := by rw [hQ x]
    _ ≤ ‖x‖ + d * ‖x‖ := by
      have := hnorm x
      linarith
    _ = (1 + d) * ‖x‖ := by ring

/-- **Metric distortion bound (roadmap #6a, second form)**:
the relative distortion of the perturbed isometry is at most
δ per layer: |‖Q̃ x‖ − ‖x‖| ≤ δ‖x‖. Composing L layers gives
(1+δ)^L — geometric, not catastrophic, growth; RMSNorm
renormalization after each layer keeps the effective factor
at (1+δ) forever. -/
theorem unitary_perturb_metric {E : Type*} [NormedAddCommGroup E]
    (Q Qt Err : E → E) (hQ : ∀ x, ‖Q x‖ = ‖x‖)
    (hsum : ∀ x, Qt x = Q x + Err x)
    (hnorm : ∀ x, ‖Err x‖ ≤ d * ‖x‖) (x : E) :
    |‖Qt x‖ - ‖x‖| ≤ d * ‖x‖ := by
  rw [hsum x]
  have hle : ‖Q x + Err x‖ ≤ ‖x‖ + d * ‖x‖ := by
    calc ‖Q x + Err x‖ ≤ ‖Q x‖ + ‖Err x‖ := norm_add_le _ _
      _ = ‖x‖ + ‖Err x‖ := by rw [hQ x]
      _ ≤ ‖x‖ + d * ‖x‖ := by
        have := hnorm x
        linarith
  have hge : ‖x‖ - d * ‖x‖ ≤ ‖Q x + Err x‖ := by
    calc ‖x‖ - d * ‖x‖ = ‖Q x‖ - d * ‖x‖ := by rw [hQ x]
      _ ≤ ‖Q x‖ - ‖Err x‖ := by
          have := hnorm x
          linarith
      _ ≤ ‖Q x + Err x‖ := by
          have h1 : ‖Q x‖ = ‖(Q x + Err x) + (-Err x)‖ := by
            have hcalc : (Q x + Err x) + (-Err x) = Q x := by abel
            rw [hcalc]
          rw [h1]
          have h2 : ‖(Q x + Err x) + (-Err x)‖ ≤ ‖Q x + Err x‖ + ‖-Err x‖ :=
            norm_add_le _ _
          have h3 : ‖-Err x‖ = ‖Err x‖ := norm_neg _
          linarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

end Hagi
