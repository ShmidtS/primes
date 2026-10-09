/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Information.InformationRetention

/-!
# RepresentationRate — the information density of a representation

The entropy-rate/contraction analogy of openai/math result 148
(dim μ = min{1, h/χ}: the surviving dimension is the injection
rate over the contraction rate), lifted to HAGI as an exact
finite statement about representations:

  ρ_info:= retained information / representation bits.

Three regimes (proved as a total trichotomy):

* ρ_info = 1 — the representation is SATURATED: every bit
  carries one bit of retained information (a perfect code;
  MemoryCapacity's counting floor is tight);
* 0 < ρ_info < 1 — the GROWTH regime: slack exists, a strictly
  better packing is possible in principle;
* ρ_info = 0 — the DEGENERATE regime: retained information is
  zero (or bits infinite): no capability survives.

All statements are exact finite algebra — no analogy is claimed
about the 148 dynamics themselves; only the RATIO STRUCTURE is
imported (honest boundary).
-/

namespace Hagi.Information

open Finset

/-- Information density of a representation: retained
information (in bits, a real ≥ 0) per representation bit. -/
noncomputable def repRate (retained bits : ℝ) : ℝ := retained / bits

/-- The three regimes of ρ_info UNDER THE COUNTING CAP
retained ≤ bits (MemoryCapacity: information cannot exceed
the bits that carry it): every representation is saturated,
or in the growth regime, or degenerate — a total trichotomy. -/
theorem repRate_trichotomy (retained bits : ℝ) (hbits : 0 < bits)
    (hret : 0 ≤ retained) (hcap : retained ≤ bits) :
    repRate retained bits = 1 ∨
      (0 < repRate retained bits ∧ repRate retained bits < 1) ∨
      repRate retained bits = 0 := by
  rcases lt_trichotomy retained bits with h | h | h
  · rcases eq_or_ne retained 0 with hr | hr
    · right; right
      rw [repRate, hr, zero_div]
    · right; left
      have hpos : 0 < retained := lt_of_le_of_ne hret hr.symm
      constructor
      · rw [repRate]; exact div_pos hpos hbits
      · rw [repRate]; exact (div_lt_one hbits).mpr h
  · left; rw [repRate, h, div_self hbits.ne']
  · exact absurd h (not_lt.mpr hcap)

end Hagi.Information
