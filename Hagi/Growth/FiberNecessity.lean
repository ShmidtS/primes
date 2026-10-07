/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Information.MemoryCapacity
import Hagi.Architecture.ConfigurationCost

/-!
# FiberNecessity — the parameter floor of separability

The LOWER side of the minimal-sufficient-size program,
closed for the configuration architecture: pairwise
2ε-separated task families cannot share configurations —
separability is paid in FIBERS.

* `configs_injective_on_separated`: the config router is
  INJECTIVE on a separated family served ε-well (two
  separated tasks cannot share a configuration: the shared
  serve output would be good for both, violating the 2ε
  separation);
* `used_configs_lower_bound`: the used-config count is at
  least the task count (the R200 counting floor, config
  form);
* `fiber_params_floor`: with rank ≥ r_min per used
  configuration over a d-dim cortex, the total fiber bill
  ≥ K·r_min·d — separability is paid linearly in the number
  of separated task families: the necessity floor of the
  switchable architecture.
-/

namespace Hagi

open Finset

/-- **Separation forbids sharing**: on a pairwise separated
family where every task is served ε-well by its routed
configuration, the config map is injective — two separated
tasks cannot land on the same configuration. -/
theorem configs_injective_on_separated {A Q : Type}
    (eps : ℝ) (good : A → A → Prop) (tasks : Finset A)
    (hsep : Hagi.Information.SepSeparated eps good tasks)
    (cfg : A → Q) (serve : Q → A)
    (hcover : ∀ x ∈ tasks, good (serve (cfg x)) x)
    {x y : A} (hx : x ∈ tasks) (hy : y ∈ tasks)
    (hne : x ≠ y) (hcfg : cfg x = cfg y) : False := by
  have hxgood : good (serve (cfg x)) x := hcover x hx
  have hbad : ¬ good (serve (cfg x)) y :=
    hsep x hx y hy hne (serve (cfg x)) hxgood
  rw [hcfg] at hbad
  exact hbad (hcover y hy)

/-- **Used-config count floor**: the used configurations
number at least the separated task count. -/
theorem used_configs_lower_bound {A Q : Type} [DecidableEq Q]
    (eps : ℝ) (good : A → A → Prop) (tasks : Finset A)
    (hsep : Hagi.Information.SepSeparated eps good tasks)
    (cfg : A → Q) (serve : Q → A)
    (hcover : ∀ x ∈ tasks, good (serve (cfg x)) x) :
    tasks.card ≤ (Finset.image cfg tasks).card := by
  have hinj : Set.InjOn cfg ↑(tasks : Finset A) := by
    intro x hx y hy hxy
    by_contra hne
    have hx' : x ∈ tasks := by simpa using hx
    have hy' : y ∈ tasks := by simpa using hy
    exact configs_injective_on_separated eps good tasks hsep cfg
      serve hcover hx' hy' hne hxy
  exact (Finset.card_image_of_injOn hinj).ge

/-- **The fiber parameter floor**: K pairwise separated
tasks, every used configuration carrying a fiber of rank
≥ rmin over a d-dim cortex, force the total fiber parameter
bill ≥ K·rmin·d — separability is paid in fibers, linearly
in the number of separated task families. -/
theorem fiber_params_floor {A Q : Type} [DecidableEq Q]
    (eps : ℝ) (good : A → A → Prop) (tasks : Finset A)
    (hsep : Hagi.Information.SepSeparated eps good tasks)
    (cfg : A → Q) (serve : Q → A)
    (hcover : ∀ x ∈ tasks, good (serve (cfg x)) x)
    (rank : Q → ℕ) (rmin d : ℕ)
    (hrank : ∀ q ∈ Finset.image cfg tasks, rmin ≤ rank q) :
    tasks.card * rmin * d
      ≤ ∑ q ∈ Finset.image cfg tasks, rank q * d := by
  have hcount : tasks.card * rmin * d
      ≤ (Finset.image cfg tasks).card * rmin * d :=
    Nat.mul_le_mul (Nat.mul_le_mul
      (used_configs_lower_bound eps good tasks hsep cfg serve
        hcover) (le_refl rmin)) (le_refl d)
  have hsum : (Finset.image cfg tasks).card * rmin * d
      ≤ ∑ q ∈ Finset.image cfg tasks, rank q * d := by
    calc (Finset.image cfg tasks).card * rmin * d
        = ∑ _q ∈ Finset.image cfg tasks, rmin * d := by
          rw [Finset.sum_const, smul_eq_mul]
          ring
      _ ≤ ∑ q ∈ Finset.image cfg tasks, rank q * d := by
          refine Finset.sum_le_sum fun q hq => ?_
          exact Nat.mul_le_mul_right d (hrank q hq)
  exact le_trans hcount hsum

end Hagi
