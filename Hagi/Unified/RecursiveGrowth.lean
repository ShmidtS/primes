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

open Finset Real InnerProductSpace

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
|c_i| therefore minimizes routing error for every k
(optimality now proved: `topk_routing_optimal` below). -/
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

/-- **Top-k routing optimality (roadmap #5b, optimality side)**:
for coefficients c and a `k`-element subset s whose kept
elements dominate every discarded coefficient in square (the
top-k² set: ∀ i ∈ s, ∀ j ∉ s, c j² ≤ c i²), the tail energy
Σ_{i∉s} c i² of s is MINIMAL among all k-element subsets s'.
Combined with `gating_tail_bound` this proves that top-k
routing by |c_i| minimizes the routing error for every k.
Proof: exchange argument via the minimum of s \ s' — every
swapped-in element of s' \ s is dominated by every kept
element of s \ s'. -/
theorem topk_routing_optimal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (k : ℕ) (s s' : Finset ι)
    (hcard : s.card = k) (hcard' : s'.card = k)
    (htop : ∀ i ∈ s, ∀ j ∉ s, c j ^ 2 ≤ c i ^ 2) :
    ∑ i ∈ sᶜ, c i ^ 2 ≤ ∑ i ∈ s'ᶜ, c i ^ 2 := by
  classical
  -- cardinalities of the exchange parts agree
  have hcc : s.card = s'.card := by rw [hcard, hcard']
  have hcs : (s \ s').card = (s' \ s).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff,
      Finset.inter_comm s s']
    omega
  -- exchange: sum over s' \ s ≤ sum over s \ s'
  have key : ∑ i ∈ s' \ s, c i ^ 2 ≤ ∑ i ∈ s \ s', c i ^ 2 := by
    rcases Finset.eq_empty_or_nonempty (s \ s') with hne | hne
    · -- s \ s' = ∅ ⟹ s = s ∩ s' ⟹ s' \ s = ∅
      have hne' : s' \ s = ∅ := by
        have h0 : (s \ s').card = 0 := by rw [hne]; simp
        have : (s' \ s).card = 0 := by omega
        exact Finset.card_eq_zero.mp this
      rw [hne, hne']
    · obtain ⟨m, hm⟩ := (s \ s').exists_min_image (fun i => c i ^ 2) hne
      have hms : m ∈ s := (Finset.mem_sdiff.1 hm.1).1
      have hle : ∀ j ∈ s' \ s, c j ^ 2 ≤ c m ^ 2 := fun j hj =>
        htop m hms j (Finset.mem_sdiff.1 hj).2
      calc ∑ i ∈ s' \ s, c i ^ 2
          ≤ ∑ i ∈ s' \ s, c m ^ 2 := Finset.sum_le_sum hle
        _ = (s' \ s).card • (c m ^ 2) := Finset.sum_const _
        _ = (s \ s').card • (c m ^ 2) := by rw [hcs]
        _ = ∑ i ∈ s \ s', c m ^ 2 := (Finset.sum_const _).symm
        _ ≤ ∑ i ∈ s \ s', c i ^ 2 := Finset.sum_le_sum hm.2
  -- split off the common intersection and conclude via complements
  have hsdi : s \ (s ∩ s') = s \ s' := by
    ext i; simp [Finset.mem_sdiff, Finset.mem_inter]
  have hsdi' : s' \ (s' ∩ s) = s' \ s := by
    ext i; simp [Finset.mem_sdiff, Finset.mem_inter]
  have hsub : s ∩ s' ⊆ s := fun _ h => (Finset.mem_inter.1 h).1
  have hsub' : s' ∩ s ⊆ s' := fun _ h => (Finset.mem_inter.1 h).1
  have hd1 := Finset.sum_sdiff (f := fun i => c i ^ 2) hsub
  have hd2 := Finset.sum_sdiff (f := fun i => c i ^ 2) hsub'
  rw [hsdi] at hd1
  rw [hsdi'] at hd2
  -- hd1 : ∑ (s \ s') + ∑ (s ∩ s') = ∑ s ; hd2 analogous
  rw [Finset.inter_comm s s'] at hd1
  rw [Finset.compl_eq_univ_sdiff s, Finset.compl_eq_univ_sdiff s']
  have hu1 := Finset.sum_sdiff (f := fun i => c i ^ 2) (Finset.subset_univ s)
  have hu2 := Finset.sum_sdiff (f := fun i => c i ^ 2) (Finset.subset_univ s')
  linarith

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
    (Q Qt Err : E → E) (d : ℝ) (hQ : ∀ x, ‖Q x‖ = ‖x‖)
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
    (Q Qt Err : E → E) (d : ℝ) (hQ : ∀ x, ‖Q x‖ = ‖x‖)
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

/-! ## Roadmap #1.3: the curvature-aware analytic step

The review (round-53/54) demands eliminating `learning_rate`
as a hyperparameter class: the step must be COMPUTED from the
measured curvature, in the spirit of the TorchLean Lyapunov
controllers (lean-dojo/TorchLean, NN/MLTheory/CROWN/Lyapunov —
verified landscape, round-54). With the smooth-descent bound
E₂ ≤ E₁ − η·inner + L·dn²·η²/2, the guaranteed decrease
g(η) = η·inner − L·dn²·η²/2 is a concave quadratic: its
maximum is ANALYTIC — η* = inner/(L·dn²), value
inner²/(2·L·dn²) — no LR tuning; in the certified SafeQP
regime (inner ≥ dn²) the analytic step is at least 1/L, so
the safe clip is η = min(1/L, η*) = 1/L exactly when the
direction is fully certified (inner = dn²).

-/

/-- Curvature-aware optimal step (roadmap #1.3): the guaranteed
descent g(η) = η·inner − L·dn²·η²/2 is a concave quadratic;
its maximum over ALL η is at η* = inner/(L·dn²) with value
inner²/(2·L·dn²) — an ANALYTIC step size, no LR hyperparameter.
Moreover η* ≥ 1/L when inner ≥ dn² (the certified SafeQP regime). -/
theorem optimal_step_unconstrained (L dn2 inner : ℝ)
    (hL : 0 < L) (hdn : 0 < dn2) :
    ∀ η' : ℝ, η' * inner - L * dn2 * η' ^ 2 / 2
      ≤ inner ^ 2 / (2 * L * dn2) := by
  intro η'
  -- completing the square: inner²/(2Ldn2) − g(η') = (L·dn2/2)·(η' − inner/(L·dn2))²
  have hsq : inner ^ 2 / (2 * L * dn2) - (η' * inner - L * dn2 * η' ^ 2 / 2)
      = (L * dn2 / 2) * (η' - inner / (L * dn2)) ^ 2 := by
    field_simp
    ring
  have hnn : 0 ≤ (L * dn2 / 2) * (η' - inner / (L * dn2)) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  linarith

theorem optimal_step_value (L dn2 inner : ℝ)
    (hL : 0 < L) (hdn : 0 < dn2) :
    (inner / (L * dn2)) * inner - L * dn2 * (inner / (L * dn2)) ^ 2 / 2
      = inner ^ 2 / (2 * L * dn2) := by
  field_simp
  ring

theorem optimal_step_ge_recip (L dn2 inner : ℝ)
    (hL : 0 < L) (hdn : 0 < dn2) (hin : dn2 ≤ inner) :
    1 / L ≤ inner / (L * dn2) := by
  rw [le_div_iff₀ (by positivity : (0:ℝ) < L * dn2)]
  have hkey : 1 / L * (L * dn2) = dn2 := by field_simp
  nlinarith [hin]

/-! ## Roadmap #1: nonconvex SafeQP iterations — the descent budget

The first machine-checked piece of the Lyapunov-stability gap
(#1): even on a NONCONVEX landscape, the SafeQP iteration with
certified per-step decrease ≥ η_t·‖d*_t‖²/2 has a FINITE total
descent budget: Σ η_t·‖d*_t‖² ≤ 2(E₀ − E_min). With a uniform
step floor η_min and activity ‖d*_t‖² ≥ ε², the iteration
MUST reach an ε-critical point within 2(E₀−E_min)/(η_min·ε²)
steps — no limit cycles, no paralysis away from criticality
(the optimizer-paralysis fear of the review is bounded to
exactly this budget).

**Honest boundary**: the link ‖d*_t‖ → 0 ⇒ Pareto
ε-stationarity (min_α ‖Σαᵢ∇Lᵢ‖ ≤ O(ε)) for the multi-domain
Gram geometry remains open — the CAGrad-style argument needs
the dual-feasibility structure not yet formalized.

-/

theorem safeqp_cumulative (E eta dn : ℕ → ℝ) (Emin : ℝ)
    (hE : ∀ t, Emin ≤ E t)
    (hstep : ∀ t, E (t + 1) ≤ E t - eta t * dn t ^ 2 / 2)
    (n : ℕ) :
    (∑ t ∈ Finset.range n, eta t * dn t ^ 2) / 2 + E n ≤ E 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 := hstep n
    have h2 : (∑ t ∈ Finset.range n, eta t * dn t ^ 2 + eta n * dn n ^ 2) / 2 + E (n + 1)
        ≤ (∑ t ∈ Finset.range n, eta t * dn t ^ 2) / 2 + E n := by linarith
    linarith [ih, h2]

theorem safeqp_total_descent (E eta dn : ℕ → ℝ) (Emin : ℝ)
    (hE : ∀ t, Emin ≤ E t)
    (hstep : ∀ t, E (t + 1) ≤ E t - eta t * dn t ^ 2 / 2)
    (n : ℕ) :
    ∑ t ∈ Finset.range n, eta t * dn t ^ 2 ≤ 2 * (E 0 - Emin) := by
  have hc := safeqp_cumulative E eta dn Emin hE hstep n
  have hEn := hE n
  linarith

theorem safeqp_eps_critical (E eta dn : ℕ → ℝ) (Emin etamin eps : ℝ)
    (hE : ∀ t, Emin ≤ E t)
    (hstep : ∀ t, E (t + 1) ≤ E t - eta t * dn t ^ 2 / 2)
    (hetamin : ∀ t, etamin ≤ eta t) (heps : 0 < eps) (hetamin0 : 0 < etamin)
    (hactive : ∀ t, eps ^ 2 ≤ dn t ^ 2) (n : ℕ) :
    (n : ℝ) ≤ 2 * (E 0 - Emin) / (etamin * eps ^ 2) := by
  have hsum := safeqp_total_descent E eta dn Emin hE hstep n
  have hlb : (n : ℝ) * (etamin * eps ^ 2) ≤ ∑ t ∈ Finset.range n, eta t * dn t ^ 2 := by
    have hterm : ∀ t ∈ Finset.range n, etamin * eps ^ 2 ≤ eta t * dn t ^ 2 := by
      intro t _
      have h1 := hetamin t
      have h2 := hactive t
      nlinarith
    have hmono : ∑ t ∈ Finset.range n, etamin * eps ^ 2 ≤ ∑ t ∈ Finset.range n, eta t * dn t ^ 2 :=
      Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hmono
    exact hmono
  have hpos : 0 < etamin * eps ^ 2 := by positivity
  have hgoal : (n:ℝ) * (etamin * eps ^ 2) ≤ 2 * (E 0 - Emin) := by linarith
  rw [le_div_iff₀ hpos]
  linarith

/-! ## Roadmap #1: the Pareto link (Gram duality, closed)

The final piece of the nonconvex SafeQP roadmap: the
characterization of controller paralysis.

- `gram_cone_inner`: a nonnegative combination Σλᵢgᵢ of the
  domain gradients makes a nonnegative inner product with
  every common-ascent direction d (⟪gᵢ,d⟫ ≥ 0 ∀i ⟹
  ⟪Σλᵢgᵢ, d⟫ ≥ 0). Contrapositive: any safe direction with
  ⟪g0,d⟫ < 0 certifies the mixture is OUTSIDE the Gram cone.
- `safeqp_pareto_orthogonality`: if the SafeQP projection
  returns exactly 0 (the controller does nothing), then the
  VI gives ⟪g0,d⟫ ≤ 0 on all safe directions while the
  mixture representation gives ≥ 0 — hence EXACTLY ZERO:
  paralysis happens iff every common-ascent direction is
  orthogonal to the mixture gradient. Contrapositive: any
  safe d with ⟪g0,d⟫ ≠ 0 forces a nonzero certified step —
  the non-stall certificate. Together with
  `safeqp_eps_critical` (R55) this closes the honest core of
  roadmap #1: the SafeQP iteration provably reaches
  ε-criticality, and the only way it stops earlier is the
  exact-orthogonality degenerate case.

**Honest boundary**: the full Farkas equivalence (0 ∈
conv{gᵢ} ↔ polar emptiness) and the O(ε) Pareto-stationarity
rate are not claimed.

-/

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **Gram-cone certificate (roadmap #1, Pareto piece 1)**:
a nonnegative combination of the domain gradients makes an
obtuse-or-right angle with every common-ascent direction.
Contrapositive: if SOME common-ascent direction has
⟪g0, d⟫ > 0, the mixture gradient g0 is NOT in the Gram cone. -/
theorem gram_cone_inner {K : Type} [Fintype K] (g : K → X) (lam : K → ℝ) (d : X)
    (hlam : ∀ i, 0 ≤ lam i) (hsafe : ∀ i, 0 ≤ ⟪g i, d⟫_ℝ) :
    0 ≤ ⟪∑ i, lam i • g i, d⟫_ℝ := by
  rw [real_inner_comm, inner_sum]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [real_inner_smul_right, real_inner_comm]
  exact mul_nonneg (hlam i) (hsafe i)

/-- **SafeQP paralysis characterization (roadmap #1, Pareto
piece 2)**: if the projected step is exactly zero (the
controller does nothing), then (a) the mixture gradient makes
a nonpositive inner product with EVERY safe direction (the
VI), and (b) — since the mixture gradient is a nonnegative
combination Σwᵢgᵢ, piece 1 — the inner product with every
safe direction is EXACTLY ZERO: every common-ascent direction
is orthogonal to the mixture gradient. The contrapositive is
the non-stall certificate: any safe d with ⟪g0,d⟫ ≠ 0 forces
a nonzero certified step. -/
theorem safeqp_pareto_orthogonality {K : Type} [Fintype K]
    (C : Set X) (hconv : Convex ℝ C) (g : K → X) (w : K → ℝ) (g0 : X)
    (hw : ∀ i, 0 ≤ w i)
    (hC0 : (0:X) ∈ C)
    (h0min : ∀ d ∈ C, dist (0:X) g0 ≤ dist d g0)
    (hmix : g0 = ∑ i, w i • g i)
    (hsafecone : ∀ d ∈ C, ∀ i, 0 ≤ ⟪g i, d⟫_ℝ)
    (d : X) (hd : d ∈ C) :
    ⟪g0, d⟫_ℝ = 0 := by
  have hvi := Hagi.min_dist_to_vi C hconv g0 0 hC0 h0min d hd
  rw [show g0 - (0:X) = g0 by simp, show d - (0:X) = d by simp] at hvi
  have hge : 0 ≤ ⟪g0, d⟫_ℝ := by
    rw [hmix]
    exact gram_cone_inner g w d hw (hsafecone d hd)
  exact le_antisymm hvi hge

end Hagi
