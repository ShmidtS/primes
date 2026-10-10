/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Information.MemoryCapacity

/-!
# FiberNecessity — parameter floor of separability

* `configs_injective_on_separated`: on a pairwise
  2ε-separated family where every task is served ε-well by its
  routed configuration, the config map is injective on the family
  (two tasks sharing a configuration is contradictory);
* `used_configs_lower_bound`: the number of used configurations is
  at least the task count;
* `fiber_params_floor`: if every used configuration has rank at
  least `rmin` over a `d`-dim cortex, the total fiber parameter sum
  is at least `tasks.card * rmin * d`.
-/

namespace Hagi.Growth

open Finset

/-- On a pairwise 2ε-separated family where every task is
served ε-well by its routed configuration, two distinct
tasks in the family cannot have equal `cfg` values. -/
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

/-- Under the hypotheses of `configs_injective_on_separated`,
`tasks.card ≤ (Finset.image cfg tasks).card`. -/
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

/-- Under the hypotheses of `configs_injective_on_separated`,
if every used configuration has `rmin ≤ rank q`, then
`tasks.card * rmin * d ≤ ∑ q, rank q * d`. -/
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

end Hagi.Growth

namespace Hagi
export Hagi.Growth (configs_injective_on_separated used_configs_lower_bound fiber_params_floor)
end Hagi
