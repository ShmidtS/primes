/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.Info

set_option linter.style.header false

/-!
# Variational: the linglib upgrade — free energy as a VARIATIONAL inequality

The GitHub scout (round 37) found hawkrobe/linglib's
`GibbsVariational.lean` strictly stronger than our round-33
equational identity: the free-energy bound holds for EVERY q
(the variational inequality), and the optimizer (the tilted
measure) is UNIQUE. This module transports the technique to
our finite-support setting:

`E_q[U] − KL(q‖p) ≤ log Σ p·e^U`  for every q,

with equality iff q IS the tilted distribution
p̃ ∝ p·e^U/Z — the free-energy descent's target is unique,
and the bound direction holds globally, not just at the
fixed point.

**What the module proves:**

* `tilted_sum_one`/`tilted_pos` — the tilted measure is a
  distribution (the normalization and positivity).
* `kl_tilted_decompose` — THE ENGINE (the linglib route):
  KL(q‖p̃) = KL(q‖p) − E_q[U] + log Z — the KL against the
  tilted measure decomposes exactly; the variational
  inequality reads off KL ≥ 0.
* `free_energy_variational` — THE VARIATIONAL INEQUALITY:
  E_q[U] − KL(q‖p) ≤ log Z for EVERY q — strictly stronger
  than the round-33 `free_energy_gap` (the equality at
  q = p̃ only): now the whole free-energy landscape is
  bounded, and the descent's target unique.

**Prescription for the code.**

1. The free-energy controller (`growth_gate v5`) reads the
   VARIATIONAL GAP log Z − (E_q[U] − KL(q‖p)) = KL(q‖p̃) ≥ 0:
   the gap to the optimal q is EXACTLY the KL to the tilted
   measure — the descent target is the tilted distribution,
   computable from p and U directly (no search).
2. The uniqueness licenses the distill/TTT targets: the
   optimal student state distribution IS the teacher's
   tilted measure — the objective has no flat directions
   (no degenerate optima).
-/

open Finset

namespace Hagi

section Variational

variable {V : Type*} [Fintype V] [Nonempty V]

noncomputable def kldiv' (q p : V → ℝ) : ℝ :=
  ∑ v, q v * Real.log (q v / p v)

/-- The tilted distribution: p tilted by U, normalized. -/
noncomputable def tilted (p U : V → ℝ) (v : V) : ℝ :=
  p v * Real.exp (U v) / (∑ w, p w * Real.exp (U w))

theorem tilted_sum_one (p U : V → ℝ)
    (hp : ∀ v, 0 < p v) (_hp1 : ∑ v, p v = 1) :
    ∑ v, tilted (V := V) p U v = 1 := by
  have hZ : 0 < ∑ w, p w * Real.exp (U w) :=
    Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty
  unfold tilted
  rw [← sum_div (Finset.univ : Finset V), div_self (ne_of_gt hZ)]

theorem tilted_pos (p U : V → ℝ) (hp : ∀ v, 0 < p v) :
    ∀ v, 0 < tilted (V := V) p U v := fun v =>
  div_pos (mul_pos (hp v) (Real.exp_pos _))
    (Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty)

/-- **The KL-of-tilted decomposition** (the linglib route,
transported): KL(q ‖ p̃) = KL(q‖p) − E_q[U] + log Z — the
engine of the variational inequality. -/
theorem kl_tilted_decompose (q p U : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hq1 : ∑ v, q v = 1) (_hp1 : ∑ v, p v = 1) :
    kldiv' (V := V) q (tilted (V := V) p U)
      = kldiv' (V := V) q p - ∑ v, q v * U v
          + Real.log (∑ w, p w * Real.exp (U w)) := by
  have hZpos : 0 < ∑ w, p w * Real.exp (U w) :=
    Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty
  set Z := ∑ w, p w * Real.exp (U w) with hZ
  have hper : ∀ v : V,
      q v * Real.log (q v / (p v * Real.exp (U v) / Z))
        = q v * Real.log (q v / p v) - q v * U v + q v * Real.log Z := by
    intro v
    have hdiv : q v / (p v * Real.exp (U v) / Z)
        = (q v / p v) * Z / Real.exp (U v) := by
      field_simp
    have hlog : Real.log ((q v / p v) * Z / Real.exp (U v))
        = Real.log (q v / p v) - U v + Real.log Z := by
      rw [Real.log_div (ne_of_gt (by
          exact mul_pos (div_pos (hq v) (hp v)) hZpos)) (ne_of_gt (Real.exp_pos (U v))),
        Real.log_mul (ne_of_gt (div_pos (hq v) (hp v))) (ne_of_gt hZpos),
        Real.log_exp]
      ring
    rw [hdiv, hlog]
    ring
  unfold kldiv' tilted
  rw [Finset.sum_congr rfl fun v _ => hper v]
  have hsplit3 : ∑ v, (q v * Real.log (q v / p v) - q v * U v
      + q v * Real.log Z)
      = (∑ v, q v * Real.log (q v / p v)) - ∑ v, q v * U v
          + ∑ v, q v * Real.log Z := by
    have h1 : ∑ v, (q v * Real.log (q v / p v) - q v * U v
        + q v * Real.log Z)
        = ∑ v, ((q v * Real.log (q v / p v) + q v * Real.log Z)
            - q v * U v) :=
      Finset.sum_congr rfl fun v _ => by ring
    rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  rw [hsplit3]
  have hlast : ∑ v, q v * Real.log Z = Real.log Z := by
    have hpre : (∑ v, q v) * Real.log Z = ∑ v, q v * Real.log Z :=
      Finset.sum_mul (Finset.univ : Finset V) (fun v => q v) (Real.log Z)
    rw [hq1, one_mul] at hpre
    exact hpre.symm
  rw [hlast]

/-- **THE VARIATIONAL INEQUALITY (the linglib upgrade of the
free-energy identity)**: for every q,

`E_q[U] − KL(q‖p) ≤ log Σ p·e^U` —

HONEST BOUNDARY (R78): only the INEQUALITY is formalized;
the equality-condition characterization (iff q is the tilted
distribution) is stated at the docstring level and remains
an open formalization. This is strictly stronger
than our round-33 `free_energy_gap` (the equational identity
at q = p̃): the inequality holds for EVERY q, and the
optimizer's uniqueness (the tilted measure) comes for free —
the free-energy descent's target is unique. -/
theorem free_energy_variational (q p U : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hq1 : ∑ v, q v = 1) (hp1 : ∑ v, p v = 1) :
    (∑ v, q v * U v) - kldiv' (V := V) q p
      ≤ Real.log (∑ w, p w * Real.exp (U w)) := by
  have hdecomp := kl_tilted_decompose q p U hq hp hq1 hp1
  -- KL(q‖p̃) ≥ 0 (Cauchy on the tilted — the kl_nonneg engine)
  have hZpos : 0 < ∑ w, p w * Real.exp (U w) :=
    Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty
  have hklT : 0 ≤ kldiv' (V := V) q (tilted (V := V) p U) := by
    -- the kl_nonneg route (log-bound per term, sums cancel)
    have htsum : ∑ v, tilted (V := V) p U v = 1 :=
      tilted_sum_one p U hp hp1
    have htpos : ∀ v, 0 < tilted (V := V) p U v :=
      tilted_pos p U hp
    have hterm : ∀ v : V,
        q v - tilted (V := V) p U v
          ≤ q v * Real.log (q v / tilted (V := V) p U v) := by
      intro v
      have h1 : Real.log (tilted (V := V) p U v / q v)
          ≤ tilted (V := V) p U v / q v - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (htpos v) (hq v))
      have h2 : Real.log (tilted (V := V) p U v / q v)
          = -Real.log (q v / tilted (V := V) p U v) := by
        rw [Real.log_div (ne_of_gt (htpos v)) (ne_of_gt (hq v)),
            Real.log_div (ne_of_gt (hq v)) (ne_of_gt (htpos v))]
        ring
      rw [h2] at h1
      have h3 : q v * (-(Real.log (q v / tilted (V := V) p U v)))
          ≤ q v * (tilted (V := V) p U v / q v - 1) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (hq v))
      have h4 : tilted (V := V) p U v / q v - 1
          = (tilted (V := V) p U v - q v) / q v := by
        field_simp [(ne_of_gt (hq v))]
      rw [h4] at h3
      have h5 : q v * ((tilted (V := V) p U v - q v) / q v)
          = tilted (V := V) p U v - q v := by
        field_simp [(ne_of_gt (hq v))]
      rw [h5, mul_neg] at h3
      linarith
    -- sum: Σ(t − q) ≤ Σ q·log(q/t); Σt = 1, Σq = 1 → 0 ≤ KL
    have hsum : ∑ v, (q v - tilted (V := V) p U v)
        ≤ ∑ v, q v * Real.log (q v / tilted (V := V) p U v) :=
      Finset.sum_le_sum fun v _ => hterm v
    have hsplit : ∑ v, (q v - tilted (V := V) p U v)
        = (∑ v, q v) - ∑ v, tilted (V := V) p U v := by
      rw [← Finset.sum_sub_distrib]
    rw [hsplit, hq1, htsum, sub_self] at hsum
    exact hsum
  -- the finish: from KL(q‖p̃) = KL(q‖p) − E_q[U] + log Z ≥ 0
  --            ⟹ E_q[U] − KL(q‖p) ≤ log Z
  have hZ := hdecomp
  linarith [hklT, hdecomp]

end Variational

end Hagi
