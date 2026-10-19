/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Hagi.Prelude.Info
set_option linter.style.header false

/-!
# Landauer — the thermodynamic price of discarded information

Physical background (research round, ask.sciencemadereadable.com):
* Landauer / Sagawa–Ueda (PRL 2009, arXiv:0809.4098): erasing
  information carries a fundamental lower bound on dissipated
  work — `k_B T ln 2` per bit for a symmetric memory;
* Janzing et al. (quant-ph/0002048): the reliability of erasure
  is priced by the KL-divergence of the resource state — KL is
  THE thermodynamic currency of a bit erasure;
* Tkachenko (arXiv:2503.09980, 2025): for neural networks the
  thermodynamic price is set by MEMORY (writing/rounding the
  parameters), not arithmetic — exactly the compress stage of a
  HAGI cycle (ternary rounding of weights = bit erasure).

**What is proven here (pure math over the canonical `klDef`)**:
with the empirical premise `h_emp_landauer` (the dissipation of a
weight-erasure step is at least `c_unit` times the discarded KL
— the conditional physics bridge, same status as every `h_emp_`),
the discarded information of one compression step is bounded by
the energy ledger budget over the thermodynamic price of a bit:

```
KL(w_pre ‖ w_post) <= (compressEnergy - jointEnergy) / c_unit
                    <= kappa * s * quantErr / c_unit   (honest ledger)
```

i.e. THE QUANTIZATION BUDGET CAPS THE DISCARDED INFORMATION — a
thermodynamic reading of the compress stage: less energy budget ⇒
less information may be destroyed per cycle. Boundary honesty: the
thermodynamic interpretation of `c_unit` is not proven here; the
module proves the conditional implication chain only.

Combined with `Energy.EntropyProduction.second_law`
(`E_p[Σ] = KL ≥ 0`, the IFT layer) this sandwiches the compress
stage: entropy production is nonnegative AND its information
content is budget-capped.
-/

namespace Hagi.Energy

open Hagi.Prelude

variable {V : Type*} [Fintype V]

/-- The thermodynamic price of one erased bit: `c_unit` stands for
`k_B * T * ln 2` of the runtime (an `h_emp_`-calibrated constant:
the runtime bridge measures T and the physical unit). -/
noncomputable def landauerUnit (cUnit : ℝ) : ℝ := cUnit

/-- **Landauer sandwich (conditional)**: with the physics bridge
`h_emp_landauer` — the dissipation of one weight-erasure
(compress) step is at least `cUnit` times the discarded KL — and
the honest compression ledger (`Dissipation <= kappa*s*quantErr`),
the information destroyed by one ternary-rounding step is
budget-capped:

`KL(w_pre ‖ w_post) <= kappa * s * quantErr / cUnit`.

Reading: the SMALLER the energy budget of a compress step, the
LESS information the step may destroy — thermodynamic pressure
toward minimal-volume architectures at fixed fidelity, the
"maximum quality at minimum volume" constraint of the HAGI goal,
made formal. -/
theorem landauer_sandwich {wPre wPost : V → ℝ}
    (hp : ∀ v, 0 < wPre v) (hq : ∀ v, 0 < wPost v)
    (hsumPre : ∑ v, wPre v = 1) (hsumPost : ∑ v, wPost v = 1)
    (dissipation cUnit kappa s quantErr : ℝ)
    (hcUnit : 0 < cUnit)
    (h_emp_landauer : cUnit * klDef wPost wPre ≤ dissipation)
    (hledger : dissipation ≤ kappa * s * quantErr) :
    klDef wPost wPre ≤ kappa * s * quantErr / cUnit :=
  by
    have h2 : klDef wPost wPre * cUnit ≤ dissipation := by
      rw [mul_comm]; exact h_emp_landauer
    exact (le_div_iff₀ hcUnit).mpr (le_trans h2 hledger)

/-- **Budget-capped erasure at the certified quantization level**:
with the certified window `quantErr <= 1/2` and `0 <= kappa`,
`s`, the discarded information per compress step is at most
`kappa*s/(2*cUnit)` — the thermodynamic cap on per-cycle容量
loss, purely from the certified ledger. -/
theorem landauer_cap_certified {wPre wPost : V → ℝ}
    (hp : ∀ v, 0 < wPre v) (hq : ∀ v, 0 < wPost v)
    (hsumPre : ∑ v, wPre v = 1) (hsumPost : ∑ v, wPost v = 1)
    (dissipation cUnit kappa s quantErr : ℝ)
    (hcUnit : 0 < cUnit) (hkappa : 0 ≤ kappa) (hs : 0 ≤ s)
    (h_emp_landauer :
      cUnit * klDef wPost wPre ≤ dissipation)
    (hledger : dissipation ≤ kappa * s * quantErr)
    (hq2 : quantErr ≤ 1 / 2) :
    klDef wPost wPre ≤ kappa * s / (2 * cUnit) := by
  have h1 := landauer_sandwich hp hq hsumPre hsumPost dissipation cUnit
    kappa s quantErr hcUnit h_emp_landauer hledger
  have hle : kappa * s * quantErr ≤ kappa * s * (1 / 2) :=
    mul_le_mul_of_nonneg_left hq2 (mul_nonneg hkappa hs)
  have hdiv : kappa * s * quantErr / cUnit ≤ kappa * s / (2 * cUnit) := by
    have hmul : kappa * s * quantErr ≤ kappa * s / 2 := by linarith [hle]
    have hstep : kappa * s * quantErr / cUnit
        ≤ kappa * s / 2 / cUnit :=
      (div_le_div_iff_of_pos_right hcUnit).mpr hmul
    have hrw : kappa * s / 2 / cUnit = kappa * s / (2 * cUnit) := by
      field_simp
    calc kappa * s * quantErr / cUnit
        ≤ kappa * s / 2 / cUnit := hstep
      _ = kappa * s / (2 * cUnit) := hrw
  linarith [h1, hdiv]

end Hagi.Energy
