/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Information.MemoryCapacity

/-!
# GainRecoverability — disagreement is EXTRACTABLE, not just present

The ProjectionMoments-inspired brick (openai/math 140 branch):
positive deviation energy does not merely EXIST — it is
RECOVERABLE by a linear readout. This closes the conceptual
gap between `devEnergy > 0` (MergeCancellation: the pool
carries diversity) and `G > 0` (GainOperator: the diversity
can be converted): between them stands the question whether a
readout exists that extracts nonzero signal. Here it always
does: the deviation directions themselves are such readouts.

Main results (finite Euclidean vocabulary of DustAlign):

* `devEnergyF_pos_iff`: total deviation energy is positive
  iff some expert deviates — the existence form;
* `recoverable_avg`: if total deviation energy E > 0 then SOME
  deviation carries at least E/N of it (pigeonhole: the best
  expert is never below the average) — the extractability
  lower bound on what the readout pool has to work with;
* `devSignal_self`: a nonzero deviation has strictly positive
  self-signal d ⬝ᵥ d > 0 — the linear readout ⟨d, ·⟩ extracts
  the deviation: recoverable signal is REAL, not a norm
  artifact.
-/

namespace Hagi.Information

open Finset

variable {N d : ℕ}

/-- Total deviation energy of an expert pool (finite form of
the GainOperator `devEnergy`, in the Dust Euclidean
vocabulary). -/
def devEnergyF (dev : Fin N → Fin d → ℝ) : ℝ :=
  ∑ k, dev k ⬝ᵥ dev k

private theorem dotSelf_nonneg {d : ℕ} (v : Fin d → ℝ) :
    0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct]
  exact sum_nonneg (fun i _ => mul_self_nonneg (v i))

/-- **Existence form**: total deviation energy is positive iff
some expert deviates. -/
theorem devEnergyF_pos_iff (dev : Fin N → Fin d → ℝ) :
    0 < devEnergyF dev ↔ ∃ k : Fin N, dev k ≠ 0 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    apply absurd h (not_lt.mpr (le_of_eq ?_))
    have : devEnergyF dev = 0 := by
      apply sum_eq_zero
      intro k _
      rw [hne k, dotProduct_zero]
    rw [this]
  · rintro ⟨k, hk⟩
    refine sum_pos' (fun _ _ => dotSelf_nonneg _) ⟨k, mem_univ k, ?_⟩
    have hz : dev k ⬝ᵥ dev k ≠ 0 := fun he =>
      hk (dotProduct_self_eq_zero.mp he)
    exact lt_of_le_of_ne (dotSelf_nonneg (dev k)) hz.symm

/-- **The pigeonhole extractability bound**: if the total
deviation energy E is positive, some single deviation carries
at least E/N of it — the readout pool never has to work below
the average. -/
theorem recoverable_avg (dev : Fin N → Fin d → ℝ)
    (hN : 0 < N) (h : 0 < devEnergyF dev) :
    ∃ k : Fin N, devEnergyF dev / N ≤ dev k ⬝ᵥ dev k := by
  obtain ⟨k, -⟩ := (devEnergyF_pos_iff dev).mp h
  by_contra hcon
  push_neg at hcon
  have hsum : devEnergyF dev < ∑ k : Fin N, devEnergyF dev / N := by
    show (∑ j : Fin N, dev j ⬝ᵥ dev j) < _
    apply sum_lt_sum _ ⟨k, mem_univ k, hcon k⟩
    intro j _
    exact le_of_lt (hcon j)
  have hconst : ∑ k : Fin N, devEnergyF dev / N = devEnergyF dev := by
    rw [sum_const]
    simp
    field_simp
  rw [hconst] at hsum
  exact lt_irrefl _ hsum

/-- **Self-signal**: a nonzero deviation has strictly positive
self-signal — the linear readout ⟨d, ·⟩ extracts d with
strength ‖d‖²: disagreement is not only present but linearly
readable. -/
theorem devSignal_self {d : ℕ} (v : Fin d → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ v := by
  have hz : v ⬝ᵥ v ≠ 0 := fun he => hv (dotProduct_self_eq_zero.mp he)
  exact lt_of_le_of_ne (dotSelf_nonneg v) hz.symm

end Hagi.Information
