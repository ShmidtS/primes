/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.MacroCycle
import Hagi.Step.ProjectionDescent
set_option linter.style.header false

/-!
# Recursive growth: sparse gating, Fisher null space, isometry
perturbation, analytic steps, SafeQP descent budget

* `ortho_norm_sq` / `gating_tail_bound` / `topk_routing_optimal`:
  Parseval identity for orthonormal coefficients; the routing
  error equals the tail energy `Σ_{i∉s} c i ^ 2`; a top-k set
  minimizes the tail among k-element subsets.
* `fisher_nullspace`: a step in the Fisher kernel with the
  h_emp_ quadratic bound has `dL ≤ 0`.
* `unitary_perturb_bound` / `unitary_perturb_metric`: a
  δ-perturbed isometry satisfies `‖Q̃x‖ ≤ (1+δ)‖x‖` and
  `|‖Q̃x‖ − ‖x‖| ≤ δ‖x‖`.
* `optimal_step_*`: the guaranteed-descent quadratic
  `g(η) = η·inner − L·dn2·η²/2` is maximized at
  `η* = inner/(L·dn2)` with value `inner²/(2·L·dn2)`.
* `safeqp_cumulative` / `safeqp_total_descent` /
  `safeqp_eps_critical`: per-step decrease ≥ `η_t·dn_t²/2`
  gives `Σ η_t·dn_t² ≤ 2(E 0 − Emin)` and an ε-criticality
  step bound.
* `gram_cone_inner` / `safeqp_pareto_orthogonality`: a
  nonnegative gradient mixture is nonnegative on the safe
  cone; a zero SafeQP step forces exact orthogonality of the
  mixture gradient to every safe direction.

Not claimed: the Farkas equivalence, the O(ε)
Pareto-stationarity rate, and float-error specializations.
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


/-- For orthonormal `v`, the squared reconstruction error of
routing to `s` equals the tail energy:
`‖(∑ i, c i • v i) − ∑ i ∈ s, c i • v i‖ ^ 2 = ∑ i ∈ sᶜ, c i ^ 2`. -/
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
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, zero_smul]
  have hfil : (Finset.univ : Finset ι).filter (fun j => j ∈ sᶜ) = sᶜ := by
    ext j; simp [Finset.mem_filter]
  have htail : ∑ i ∈ sᶜ, c i • v i = ∑ i, (if i ∈ sᶜ then c i else 0) • v i := by
    simp only [hmulite]
    rw [← Finset.sum_filter (s := (Finset.univ : Finset ι)) (p := fun j => j ∈ sᶜ)
      (f := fun j => c j • v j), hfil]
  have hsqite : ∀ i : ι, (if i ∈ sᶜ then c i else 0) ^ 2
      = if i ∈ sᶜ then c i ^ 2 else 0 := fun i => by
    by_cases h : i ∈ sᶜ
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      norm_num
  have htail2 : ∑ i ∈ sᶜ, c i ^ 2 = ∑ i, (if i ∈ sᶜ then c i else 0) ^ 2 := by
    simp only [hsqite]
    rw [← Finset.sum_filter (s := (Finset.univ : Finset ι)) (p := fun j => j ∈ sᶜ)
      (f := fun j => c j ^ 2), hfil]
  rw [htail, htail2]
  exact horth

/-- If `s` has `k` elements and every kept coefficient
dominates every discarded one in square
(`∀ i ∈ s, ∀ j ∉ s, c j ^ 2 ≤ c i ^ 2`), then the tail
`∑ i ∈ sᶜ, c i ^ 2` is minimal among all k-element subsets. -/
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
    ext i; simp [Finset.mem_sdiff]
  have hsdi' : s' \ (s' ∩ s) = s' \ s := by
    ext i; simp [Finset.mem_sdiff]
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

/-- If `dL ≤ ⟪dW, F dW⟫` (h_emp_quad) and `F dW = 0`, then
`dL ≤ 0`. -/
theorem fisher_nullspace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E →L[ℝ] E) (dW : E) (dL : ℝ)
    (h_emp_quad : dL ≤ inner ℝ dW (F dW))
    (hker : F dW = 0) :
    dL ≤ 0 := by
  rw [hker] at h_emp_quad
  rw [show inner ℝ dW 0 = 0 from by simp] at h_emp_quad
  linarith

/-! ## Roadmap #6a: unitarity perturbation — Wilkinson bound -/

/-- If `Q` is an isometry, `Qt x = Q x + Err x`, and
`‖Err x‖ ≤ d * ‖x‖` for all `x`, then `‖Qt x‖ ≤ (1 + d) * ‖x‖`. -/
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

/-- Under the hypotheses of `unitary_perturb_bound`:
`|‖Qt x‖ − ‖x‖| ≤ d * ‖x‖`. -/
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

/-! ## The curvature-aware analytic step

The guaranteed decrease `g(η) = η·inner − L·dn2·η²/2` is a
concave quadratic maximized at `η* = inner/(L·dn2)`.
-/

/-- For `0 < L` and `0 < dn2`, every `η'` satisfies
`η' * inner − L * dn2 * η' ^ 2 / 2 ≤ inner ^ 2 / (2 * L * dn2)`;
the maximum is attained at `η* = inner / (L * dn2)`
(`optimal_step_value`), and `1 / L ≤ η*` when `dn2 ≤ inner`
(`optimal_step_ge_recip`). -/
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

/-! ## SafeQP iterations — the descent budget

With per-step decrease `E (t+1) ≤ E t − eta t * dn t ^ 2 / 2`
and `E ≥ Emin`: `safeqp_cumulative` telescopes,
`safeqp_total_descent` gives
`Σ eta t * dn t ^ 2 ≤ 2 (E 0 − Emin)`, and
`safeqp_eps_critical` bounds the number of steps with
`eta t ≥ etamin` and `dn t ^ 2 ≥ eps ^ 2` by
`2 (E 0 − Emin) / (etamin * eps ^ 2)`. The Pareto
ε-stationarity link is not claimed.
-/

theorem safeqp_cumulative (E eta dn : ℕ → ℝ) (Emin : ℝ)
    (_hE : ∀ t, Emin ≤ E t)
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

/-! ## The Pareto link (Gram duality)

`gram_cone_inner`: a nonnegative mixture of gradients is
nonnegative on the safe cone. `safeqp_pareto_orthogonality`:
a zero SafeQP step forces the mixture gradient to be exactly
orthogonal to every safe direction. The Farkas equivalence
and the O(ε) Pareto-stationarity rate are not claimed.
-/

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- If `lam i ≥ 0` and `0 ≤ ⟪g i, d⟫_ℝ` for all `i`, then
`0 ≤ ⟪∑ i, lam i • g i, d⟫_ℝ`. -/
theorem gram_cone_inner {K : Type} [Fintype K] (g : K → X) (lam : K → ℝ) (d : X)
    (hlam : ∀ i, 0 ≤ lam i) (hsafe : ∀ i, 0 ≤ ⟪g i, d⟫_ℝ) :
    0 ≤ ⟪∑ i, lam i • g i, d⟫_ℝ := by
  rw [real_inner_comm, inner_sum]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [real_inner_smul_right, real_inner_comm]
  exact mul_nonneg (hlam i) (hsafe i)

/-- If 0 minimizes the distance to `g0` over a convex safe
cone on which every gradient `g i` is nonnegative, `g0` is
the nonnegative mixture `∑ w i • g i`, and `d` is safe, then
`⟪g0, d⟫_ℝ = 0`. -/
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
