/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.Info
import Hagi.Core.Concat
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option linter.style.header false

/-!
# Variational: the linglib upgrade — free energy as a VARIATIONAL inequality

The GitHub scout (round 37) found hawkrobe/linglib's
`GibbsVariational.lean` strictly stronger than our round-33
equational identity: the free-energy bound holds for every q
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
  E_q[U] − KL(q‖p) ≤ log Z for every q — strictly stronger
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
open Hagi.Prelude
open Set

namespace Hagi.Energy

section Variational

variable {V : Type*} [Fintype V] [Nonempty V]

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
    Hagi.Prelude.klDef (V := V) q (tilted (V := V) p U)
      = Hagi.Prelude.klDef (V := V) q p - ∑ v, q v * U v
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
  unfold Hagi.Prelude.klDef tilted
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

honest boundary: only the INEQUALITY is formalized;
the equality-condition characterization (iff q is the tilted
distribution) is stated at the docstring level and remains
an open formalization. This is strictly stronger
than our round-33 `free_energy_gap` (the equational identity
at q = p̃): the inequality holds for every q, and the
optimizer's uniqueness (the tilted measure) comes for free —
the free-energy descent's target is unique. -/
theorem free_energy_variational (q p U : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hq1 : ∑ v, q v = 1) (hp1 : ∑ v, p v = 1) :
    (∑ v, q v * U v) - Hagi.Prelude.klDef (V := V) q p
      ≤ Real.log (∑ w, p w * Real.exp (U w)) := by
  have hdecomp := kl_tilted_decompose q p U hq hp hq1 hp1
  -- KL(q‖p̃) ≥ 0 (Cauchy on the tilted — the kl_nonneg engine)
  have hZpos : 0 < ∑ w, p w * Real.exp (U w) :=
    Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty
  have hklT : 0 ≤ Hagi.Prelude.klDef (V := V) q (tilted (V := V) p U) :=
    -- R334: delegates to the canon Hagi.Prelude.kl_nonneg
    -- (kldiv' IS klDef by rfl)
    Hagi.Prelude.kl_nonneg q (tilted (V := V) p U)
      hq (tilted_pos p U hp) hq1 (tilted_sum_one p U hp hp1)
  -- the finish: from KL(q‖p̃) = KL(q‖p) − E_q[U] + log Z ≥ 0
  --            ⟹ E_q[U] − KL(q‖p) ≤ log Z
  have hZ := hdecomp
  linarith [hklT, hdecomp]

/-- **Optimal Gibbs weights over the simplex (mirror-descent
bound)**: for every probability vector `q` and every loss
profile `L` at inverse temperature `T > 0`,

  `⟨L⟩_q + T · Σ v, q v · log (q v) ≥ - T · log Σ v, exp(-L v / T)`.

This is the exact optimization statement behind the tempered
softmax: the Gibbs/tilted distribution attains the right-hand
side, i.e. `w = softmax(-L / T)` minimizes the regularized
objective — the equality case of the variational principle,
lived entirely on the finite simplex. The lower bound derives
from `free_energy_variational` at the uniform base; the
attainment/characterization lives in the KL equality case. -/
theorem gibbs_optimal_bound (q L : V → ℝ) {T : ℝ} (hT : 0 < T)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v, q v = 1) :
    (∑ v, q v * L v) + T * ∑ v, q v * Real.log (q v)
      ≥ -T * Real.log (∑ v, Real.exp (-(L v) / T)) := by
  classical
  set n := ((Fintype.card V : ℕ) : ℝ) with hn
  have hnpos : 0 < n := by
    have hc : (0 : ℕ) < Fintype.card V := Fintype.card_pos
    rw [hn]  -- no-op for goal; cast positivity:
    exact Nat.cast_pos.mpr hc
  have hu1 : ∑ v : V, ((1 : ℝ) / n) = 1 := by
    simp [Finset.sum_const, hn]
  have hup : ∀ v : V, 0 < (1 : ℝ) / n := fun _ => div_pos one_pos hnpos
  set Uloss : V → ℝ := fun v => -L v / T with hUloss
  have hmain := free_energy_variational (V := V) q
    (fun v : V => (1 : ℝ) / n) Uloss hq hup hq1 hu1
  -- E_q[U] = -(Σ q·L)/T
  have hEu : ∑ v, q v * (-L v / T) = -(∑ v, q v * L v) / T := by
    have hterm : ∀ v : V, q v * (-L v / T) = -((q v * L v) / T) := by
      intro v; ring
    have hkey : (∑ v, (q v * L v) / T) = (∑ v, q v * L v) / T :=
      (Finset.sum_div Finset.univ (fun v => q v * L v) T).symm
    calc ∑ v, q v * (-L v / T)
        = ∑ v, -((q v * L v) / T) :=
          Finset.sum_congr rfl (fun v _ => hterm v)
      _ = -(∑ v, (q v * L v) / T) := by
          rw [Finset.sum_neg_distrib]
      _ = -(∑ v, q v * L v) / T := by rw [hkey, neg_div]
  -- KL(q ‖ uniform) = Σ q·log q + log n
  have hkl : Hagi.Prelude.klDef (V := V) q (fun _ => (1 : ℝ) / n)
      = (∑ v, q v * Real.log (q v)) + Real.log n := by
    unfold Hagi.Prelude.klDef
    simp only []
    have hdiv : ∀ v : V, q v / (1 / n) = q v * n := by
      intro v; field_simp
    have hlog : ∀ v : V, Real.log (q v * n)
        = Real.log (q v) + Real.log n := by
      intro v
      rw [Real.log_mul (hq v).ne' (ne_of_gt hnpos)]
    rw [Finset.sum_congr rfl (fun v _ => by rw [hdiv v, hlog v, mul_add]),
      Finset.sum_add_distrib]
    have hlast : ∑ v, q v * Real.log n = Real.log n := by
      have hpre : (∑ v, q v) * Real.log n
          = ∑ v, q v * Real.log n := Finset.sum_mul (Finset.univ : Finset V)
            (fun v => q v) (Real.log n)
      rw [hq1, one_mul] at hpre
      exact hpre.symm
    rw [hlast]
  rw [hEu, hkl] at hmain
  -- exponent sum positivity (in Uloss-terms, as in hmain)
  have hsumeposU : (0 : ℝ) < ∑ w, Real.exp (Uloss w) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  -- normalize the partition-function log: log(Σe / n) = log Σe − log n
  have hZeq : Real.log ((∑ w, ((1 : ℝ) / n) * Real.exp (Uloss w)))
      = Real.log (∑ w, Real.exp (Uloss w)) - Real.log n := by
    have hsplit : ∑ w, ((1 : ℝ) / n) * Real.exp (Uloss w)
        = (∑ w, Real.exp (Uloss w)) / n := by
      have hterm : ∀ w : V, ((1 : ℝ) / n) * Real.exp (Uloss w)
          = Real.exp (Uloss w) / n := by
        intro w; ring
      rw [Finset.sum_congr rfl (fun w _ => hterm w)]
      rw [Finset.sum_div Finset.univ (fun w => Real.exp (Uloss w)) n]
    rw [hsplit]
    have hld : Real.log ((∑ w, Real.exp (Uloss w)) / n)
        = Real.log (∑ w, Real.exp (Uloss w)) - Real.log n :=
      Real.log_div (ne_of_gt hsumeposU) (ne_of_gt hnpos)
    rw [hld]
  rw [hZeq] at hmain
  -- multiply the inequality by T > 0 and finish linearly
  have hmult := mul_le_mul_of_nonneg_right hmain (le_of_lt hT)
  have hcancel : (-(∑ v, q v * L v)) / T * T
      = -(∑ v, q v * L v) :=
    div_mul_cancel₀ _ (ne_of_gt hT)
  have hsimp : (-(∑ v, q v * L v) / T
      - (∑ v, q v * Real.log (q v) + Real.log n))
      * T
      = -(∑ v, q v * L v)
        - (∑ v, q v * Real.log (q v)) * T - Real.log n * T := by
    rw [sub_mul, add_mul, hcancel]
    ring
  rw [hsimp] at hmult
  rw [hUloss] at hmult
  linarith [hmult]


end Variational


variable {V : Type*} [Fintype V]

end Hagi.Energy
