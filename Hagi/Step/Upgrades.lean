/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Data.SinkCost

set_option linter.style.header false

/-!
# Upgrades — геометрическая оболочка NS-невязки

* `ns_geometric_envelope`: при `0 < ρ`, шаге
  `e (s+1) ≤ ρ·e s` и `e 0 = e0` — `e s ≤ ρ^s·e0`
  (счётчик итераций вычислим из измеренной контракции);
* `sinkReceptiveField` — определение точного рецептивного
  поля режима window+sinks (структурный объект, не теорема);
* `nce_per_sample_corrected` — определение пер-сэмпльной
  NCE-коррекции (нотация, не теорема).
-/

open Finset

namespace Hagi.Step

section Upgrades

/-- При `0 < rho`, `e (s+1) ≤ rho·e s` и `e 0 = e0`:
`e s ≤ rho^s·e0` для всех s. -/
theorem ns_geometric_envelope (e : ℕ → ℝ) (rho : ℝ)
    (hrho : 0 < rho) (e0 : ℝ)
    (hstep : ∀ s : ℕ, e (s+1) ≤ rho * e s) (he0 : e 0 = e0) :
    ∀ s : ℕ, e s ≤ (rho^s) * e0 := by
  intro s
  induction s with
  | zero => rw [pow_zero, one_mul, he0]
  | succ n ih =>
    have h1 := hstep n
    rw [pow_succ]
    calc e (n+1) ≤ rho * e n := h1
      _ ≤ rho * ((rho^n) * e0) := mul_le_mul_of_nonneg_left ih (le_of_lt hrho)
      _ = (rho^n) * rho * e0 := by ring

-- НЕ ТЕОРЕМА: прежняя rfl-форма была носителем предписания;
-- ниже — честное определение точного рецептивного поля.
def sinkReceptiveField (W S i : ℕ) : Finset ℕ :=
    Finset.range (min S i) ∪ (Finset.range (i+1)).filter (fun k => k + W > i)

/-- Пер-сэмпльная NCE-коррекция
`Σ_v q v·(f v − log (q v))` — определение (нотация,
не теорема). -/
-- Снято ранее: пер-сэмпльная коррекция — нотация, не
-- теорема; оставлена как определение.
private noncomputable def nce_per_sample_corrected {V : Type} [Fintype V] (f q : V → ℝ) : ℝ :=
  ∑ v, q v * (f v - Real.log (q v))

end Upgrades

end Hagi.Step

namespace Hagi
export Hagi.Step (ns_geometric_envelope sinkReceptiveField)
end Hagi
