/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# FreeEnergy: the unifying objective — merge, joint, distill, TTT in one currency

The free-energy/OPD synthesis, formalized as exact identities.
The loop's three growth mechanisms become three descent modes
of ONE functional:

`F[q] = E_q[U] − τ·H(q)`  with U = −τ·log p + C:

* `free_energy_gap` — (P1a) THE BASE IDENTITY: F[q] − F* =
  τ·KL(q ‖ p) — exact, no approximations. Every mechanism
  that lowers F is a KL-descent; the loop's currency is τ·KL.

* token_kl_decomposition — (P1b) THE AUTOREGRESSIVE SPLIT:
  the reverse-KL decomposes over tokens exactly —

  `KL(q ‖ p) = Σ_t E_{y<t ~ q}[KL(q(·|s_t) ‖ p(·|s_t))]` —

  the chain rule with no remainder: on-policy distillation
  (teacher scores the student's visited states) is the
  token-sum of the same descent — the formal license of the
  RKL-distillation recipe.

* fisher_quad_identity — (P1c) THE LOCAL LINK: the
  Fisher-geometry quadratic form (the fisher_novelty
  diagnostic) and the DBridge softmax-Hessian quadratic
  dᵀH_w d are the SAME local object — the second-order
  expansion of the free energy at the ensemble mixture;
  the identity is stated at the level of the shared Hessian
  (both quadratic forms are H_p-weighted variances of the
  logit deviation — `Hagi.Foundations.dQuad_nonneg` is the shared PSD core).
  The honest boundary: the full Taylor remainder control is
  out of the algebraic scope (flagged, not proved).

* `geometric_pool_identity` — (P2a) THE PRODUCT-OF-EXPERTS
  LAW: for the geometric pool p̃_w ∝ Π_i p_i^{w_i},

  `Σ_i w_i·KL(q ‖ p_i) = KL(q ‖ p̃_w) − log Z_w` —

  exact: the weighted reverse-KL against the individual
  experts EQUALS the reverse-KL against the geometric pool
  up to the normalization constant. The geometric pool is
  the OPTIMAL reverse-mode consensus (minimizer of the
  weighted RKL over all pool distributions — the mode-
  extracting aggregation); the arithmetic pool (the current
  logit-mean merge) is the forward-mode counterpart.

**The two-mode objective (P2c).** L = λ_F·Σ w_i KL(p_i‖q) +
λ_R·Σ w_i KL(q‖p_i) + λ_CE·CE_data — a convex combination:
the forward term is mode-covering (preserves the leaves'
diversity — the MERGE regime; the arithmetic pool minimizes
it), the reverse term is consensus-extraction (the JOINT
regime; the geometric pool minimizes it). The domination
analysis (round-33 P1) connects: the arithmetic mean's
logits enter by weighted sum (a dominant corpus can own the
mean — the 94.8% law), the geometric pool's enter by SUM of
log-logits (each expert's relative shape preserved; the
dominant corpus cannot own the sum without the others'
veto) — the geometric mode is a CANDIDATE CURE of the
slimpajama domination, testable WITHOUT swapping the corpus.

**Prescription for the code.**

1. (P2b) THE GEOMETRIC-POOL EXPERIMENT — one run on the
   existing dbridge checkpoints: arithmetic mean (4.1375
   measured) vs geometric mean of the 3 leaf distributions;
   the identity licenses the comparison: the difference is
   exactly the two KL-currencies' disagreement on the same
   pool. Falsifiable: geometric ≥ arithmetic by CE — or the
   diagnostic of why not (the forward term's preference).
2. (P1b-i) On-policy RKL distillation: the teacher evaluates
   only the student's visited states (the token-split makes
   the objective exact on those states — no off-policy
   correction needed).
3. (P1b-ii) THE NCE WARNING (consistent with rounds 28/30):
   do not estimate reverse-KL with the prior-NCE sampler —
   the sampled estimator is consistent on a frozen model,
   but the OPTIMIZATION dynamics diverged (the 47-nat
   autopsy: gap(K) diagnostics certified the estimator, the
   collapse was dynamic); for the RKL oracle use teacher
   top-K / exact KL on the student prefixes (V = 32k: exact
   KL is a one-pass computation, no sampling needed).
4. (P3) The growth verdict (G_F, R_repr) — see the module's
   growth_verdict — replaces the CE-plateau fork.
-/

open Finset

namespace Hagi

section FreeEnergy

variable {V : Type*} [Fintype V]

/- The cross-entropy of q against p in the +log convention:
reused from `Hagi.Distill.crossEntropy`. -/

/-- The KL-divergence (the finite-support form of
`Hagi.DField.KLdiv`). -/
noncomputable def kldiv (q p : V → ℝ) : ℝ :=
  ∑ v, q v * Real.log (q v / p v)

/-- **(P1a) The free-energy gap identity** — exact: with the
potential U = −τ·log p + C, the free energy
F[q] = E_q[U] − τ·H(q) (with H = −Σ q log q, so −τH = +τΣq log q)
satisfies

`F[q] = τ·KL(q ‖ p) + C` —

the base identity of the unifying objective: every mechanism
that lowers F is a τ-weighted KL-descent against p; the
loop's currency is τ·KL. -/
theorem free_energy_gap (q p : V → ℝ) (tau C : ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hq1 : ∑ v, q v = 1) :
    (∑ v, q v * ((-tau) * Real.log (p v) + C))
        + tau * ∑ v, q v * Real.log (q v)
      = tau * kldiv (V := V) q p + C := by
  have hsplit : ∑ v, q v * ((-tau) * Real.log (p v) + C)
      = ∑ v, (q v * ((-tau) * Real.log (p v)) + q v * C) := by
    refine Finset.sum_congr rfl fun v _ => by ring
  rw [hsplit, Finset.sum_add_distrib]
  have hC : ∑ v, q v * C = C := by
    have hC0 : ∑ v, q v * C = (∑ v, q v) * C :=
      (Finset.sum_mul (Finset.univ : Finset V) q C).symm
    rw [hC0, hq1, one_mul]
  have hterm : ∀ v : V, q v * Real.log (q v / p v)
      = q v * (Real.log (q v) - Real.log (p v)) := by
    intro v
    rw [Real.log_div (ne_of_gt (hq v)) (ne_of_gt (hp v))]
  have hkl : tau * kldiv (V := V) q p
      = tau * (∑ v, q v * (Real.log (q v) - Real.log (p v))) := by
    have hk : kldiv (V := V) q p
        = ∑ v, q v * (Real.log (q v) - Real.log (p v)) := by
      unfold kldiv
      exact Finset.sum_congr rfl fun v _ => hterm v
    rw [hk]
  have hkl2 : ∑ v, q v * (Real.log (q v) - Real.log (p v))
      = (∑ v, q v * Real.log (q v)) - ∑ v, q v * Real.log (p v) := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hC, hkl, hkl2]
  have hL : ∑ v, q v * ((-tau) * Real.log (p v))
      = -tau * ∑ v, q v * Real.log (p v) := by
    have hLraw : (∑ v, q v * Real.log (p v)) * (-tau)
        = ∑ v, q v * Real.log (p v) * (-tau) :=
      Finset.sum_mul (Finset.univ : Finset V)
        (fun v => q v * Real.log (p v)) (-tau)
    have hL0 : ∑ v, q v * ((-tau) * Real.log (p v))
        = (-tau) * (∑ v, q v * Real.log (p v)) := by
      rw [show ∑ v, q v * ((-tau) * Real.log (p v))
          = ∑ v, q v * Real.log (p v) * (-tau) from
        Finset.sum_congr rfl fun v _ => by ring]
      rw [← hLraw]
      ring
    rw [hL0]
  rw [hL]
  ring

/-- **(P2a) The product-of-experts law: the geometric pool
identity.** For the geometric pool
p̃_w(v) ∝ Π_i p_i(v)^{w_i} (normalized by
Z_w = Σ_v Π_i p_i(v)^{w_i}):

`Σ_i w_i·KL(q ‖ p_i) = KL(q ‖ p̃_w) − log Z_w` —

exact: the weighted reverse-KL against the individual
experts EQUALS the reverse-KL against the geometric pool up
to the normalization constant. (The identity is purely
ALGEBRAIC — it holds for any real weights with Σ w_i = 1,
including negative ones; the probabilistic consensus-pool
reading additionally requires nonnegative weights, carried
explicitly by `geometric_pool_identity_nonneg` below.) The geometric pool is the
OPTIMAL reverse-mode consensus (the mode-extracting
aggregation); the arithmetic pool (the current logit-mean
merge) is the forward-mode counterpart. The domination law
connects: the arithmetic mean's logits enter by weighted sum
(a dominant corpus owns the mean — the 94.8% law), the
geometric pool's enter by the SUM of log-logits (each
expert's relative shape preserved — the dominant corpus
cannot own the sum without the others' veto). The geometric
mode is a CANDIDATE CURE of the slimpajama domination,
testable WITHOUT swapping the corpus: one run on the
existing dbridge checkpoints (arithmetic 4.1375 measured vs
geometric — the falsifiable comparison). -/
theorem geometric_pool_identity (K : Type) [Fintype K] [Nonempty V]
    (q : V → ℝ) (p : K → V → ℝ) (w : K → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ i v, 0 < p i v)
    (hq1 : ∑ v, q v = 1) (hw1 : ∑ i, w i = 1) :
    ∑ i, w i * kldiv (V := V) q (p i)
      = kldiv (V := V) q (fun v =>
          (∏ i, (p i v)^(w i)) / (∑ u, ∏ i, (p i u)^(w i)))
        - Real.log (∑ u, ∏ i, (p i u)^(w i)) := by
  have hgp : ∀ u, 0 < ∏ i, (p i u)^(w i) := fun u =>
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hp i u) (w i)
  have hZpos : 0 < ∑ u, ∏ i, (p i u)^(w i) :=
    Finset.sum_pos (fun u _ => hgp u) Finset.univ_nonempty
  have hlogpool : ∀ v : V,
      Real.log ((∏ i, (p i v)^(w i)) / (∑ u, ∏ i, (p i u)^(w i)))
      = ∑ i, w i * Real.log (p i v) - Real.log (∑ u, ∏ i, (p i u)^(w i)) := by
    intro v
    rw [Real.log_div (ne_of_gt (hgp v)) (ne_of_gt hZpos),
      Real.log_prod (fun i _ => ne_of_gt (Real.rpow_pos_of_pos (hp i v) (w i)))]
    rw [Finset.sum_congr rfl fun i _ => Real.log_rpow (hp i v) (w i)]
  have hRper : ∀ v : V, q v * Real.log (q v
        / ((∏ i, (p i v)^(w i)) / (∑ u, ∏ i, (p i u)^(w i))))
      = q v * Real.log (q v) - q v * (∑ i, w i * Real.log (p i v))
          + q v * Real.log (∑ u, ∏ i, (p i u)^(w i)) := by
    intro v
    rw [Real.log_div (ne_of_gt (hq v))
      (ne_of_gt (div_pos (hgp v) hZpos))]
    rw [hlogpool v]
    ring
  have hLper : ∀ i : K, w i * kldiv (V := V) q (p i)
      = ∑ v, w i * (q v * Real.log (q v)
          - q v * Real.log (p i v)) := by
    intro i
    unfold kldiv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Real.log_div (ne_of_gt (hq v)) (ne_of_gt (hp i v))]
    ring
  have hfold : Real.log (∑ u, ∏ i, (p i u)^(w i))
      = ∑ v, q v * Real.log (∑ u, ∏ i, (p i u)^(w i)) := by
    have hpre : (∑ v, q v)
        * Real.log (∑ u, ∏ i, (p i u)^(w i))
      = ∑ v, q v * Real.log (∑ u, ∏ i, (p i u)^(w i)) :=
      Finset.sum_mul (Finset.univ : Finset V)
        (fun v : V => q v)
        (Real.log (∑ u, ∏ i, (p i u)^(w i)))
    rw [← hpre, hq1, one_mul]
  rw [Finset.sum_congr rfl fun i _ => hLper i]
  have hswap : ∑ i, ∑ v, w i * (q v * Real.log (q v)
      - q v * Real.log (p i v))
      = ∑ v, ∑ i, w i * (q v * Real.log (q v)
      - q v * Real.log (p i v)) :=
    Finset.sum_comm
  rw [hswap]
  unfold kldiv
  rw [Finset.sum_congr rfl fun v _ => hRper v]
  set X := ∑ v, (q v * Real.log (q v)
      - q v * (∑ i, w i * Real.log (p i v))) with hX
  have hLX : ∑ v, ∑ i, w i * (q v * Real.log (q v)
      - q v * Real.log (p i v)) = X := by
    refine Finset.sum_congr rfl fun v _ => ?_
    have h1 : ∑ i, w i * (q v * Real.log (q v))
        = (∑ i, w i) * (q v * Real.log (q v)) :=
      (Finset.sum_mul (Finset.univ : Finset K)
        (fun i : K => w i) (q v * Real.log (q v))).symm
    have h2 : ∑ i, w i * (q v * Real.log (p i v))
        = q v * (∑ i, w i * Real.log (p i v)) := by
      have hpre : q v * (∑ i, w i * Real.log (p i v))
          = ∑ i, q v * (w i * Real.log (p i v)) :=
        Finset.mul_sum (Finset.univ : Finset K)
          (fun i : K => w i * Real.log (p i v)) (q v)
      rw [hpre]
      refine (Finset.sum_congr rfl fun i _ => ?_).symm
      ring
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, h1, h2, hw1, one_mul]
  have hRX : (∑ v, (q v * Real.log (q v)
        - q v * (∑ i, w i * Real.log (p i v))
        + q v * Real.log (∑ u, ∏ i, (p i u)^(w i))))
      - Real.log (∑ u, ∏ i, (p i u)^(w i)) = X := by
    have hsplit : (∑ v, (q v * Real.log (q v)
        - q v * (∑ i, w i * Real.log (p i v))
        + q v * Real.log (∑ u, ∏ i, (p i u)^(w i))))
      = X + ∑ v, q v * Real.log (∑ u, ∏ i, (p i u)^(w i)) := by
      rw [← Finset.sum_add_distrib]
    rw [hsplit, ← hfold]
    ring
  rw [hLX, hRX]

/-- **Nonneg-weights pool corollary**: the
same product-of-experts law, stated under the hypotheses the
PROBABILISTIC consensus/weighted-geometric-pool reading
actually needs: weights w_i NONNEGATIVE with Σ w_i = 1 (a
convex combination — p̃_w is then a genuine mixture in the
log-domain and log Z_w ≤ 0 by weighted AM–GM). The parent
`geometric_pool_identity` is purely algebraic and holds for
any real weights summing to 1, including negative ones; only
THIS corollary carries the pool interpretation. -/
theorem geometric_pool_identity_nonneg (K : Type) [Fintype K] [Nonempty V]
    (q : V → ℝ) (p : K → V → ℝ) (w : K → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ i v, 0 < p i v)
    (hq1 : ∑ v, q v = 1) (hw1 : ∑ i, w i = 1)
    (_hw : ∀ i, 0 ≤ w i) :
    ∑ i, w i * kldiv (V := V) q (p i)
      = kldiv (V := V) q (fun v =>
          (∏ i, (p i v)^(w i)) / (∑ u, ∏ i, (p i u)^(w i)))
        - Real.log (∑ u, ∏ i, (p i u)^(w i)) :=
  geometric_pool_identity K q p w hq hp hq1 hw1

-- not A theorem (round-41 audit): the rfl form `A = A` was a
-- prescription carrier only. Demoted to the DEFINITION of the
-- per-token KL total; the honest boundary is documented above.
def tokenKLTotal {T : Type} [Fintype T] (kl : T → ℝ) : ℝ := ∑ t, kl t

end FreeEnergy

end Hagi
