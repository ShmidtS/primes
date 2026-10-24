import Hagi.Prelude.Info
-- Cortex (arXiv 2610.20399v1) Appx A: MoE shared expansion.
open Finset

namespace Hagi.Model

/-!
Cortex (arXiv 2610.20399v1), Appx A.4/A.5: shared expansion в MoE.
Тождество (18): при Σ a_e(x) = 1 общая ветка S сворачивается в
каждого эксперта без изменения выхода: F + S = Σ a_e·(E_e + S).
-/

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

/-- Тождество сворачивания shared-ветки (Prop A.5, eq. 18). -/
theorem moe_shared_expansion_identity
    {ι : Type*} [Fintype ι] (E : ι → V) (S : V) (a : ι → ℝ)
    (ha : ∑ e, a e = 1) :
    (∑ e, a e • E e) + S = ∑ e, a e • (E e + S) := by
  calc (∑ e, a e • E e) + S
      = (∑ e, a e • E e) + (∑ e, a e) • S := by rw [ha, one_smul]
    _ = (∑ e, a e • E e) + ∑ e, a e • S := by rw [Finset.sum_smul]
    _ = ∑ e, (a e • E e + a e • S) := Finset.sum_add_distrib.symm
    _ = ∑ e, a e • (E e + S) :=
          Finset.sum_congr rfl fun e _ => (smul_add (a e) (E e) S).symm

end Hagi.Model
