/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# CapabilityGain — перенос внутреннего спуска во внешний прирост

Условная бухгалтерия переноса (настоящий мост — в
эмпирических посылках, открыт):

* `capability_gain_transfer`: при декомпозициях
  `Rext1 = E1 + g1`, `Rext2 = E2 + g2`, внутреннем
  сертификате `E2 ≤ E1 − Γ` и неухудшении зазора `g2 ≤ g1` —
  `Rext2 ≤ Rext1 − Γ`;
* `pb_gap_bound_mono`: при `KL2 ≤ KL1` —
  `KL2 + base ≤ KL1 + base` (монотонность оценки зазора
  PAC-Bayes по бюджету KL; актуальный зазор — h_emp_
  до моста CertifiedEstimator).
-/

open Real Finset

namespace Hagi.Dynamics

/-- При `Rext1 = E1 + g1`, `Rext2 = E2 + g2`, `E2 ≤ E1 − Gamma`
и `g2 ≤ g1` — `Rext2 ≤ Rext1 − Gamma` (бухгалтерская
лемма; эмпирическое содержание — в посылках hcert и hgap). -/
theorem capability_gain_transfer (E1 E2 g1 g2 Rext1 Rext2 Gamma : ℝ)
    (hR1 : Rext1 = E1 + g1) (hR2 : Rext2 = E2 + g2)
    (hcert : E2 ≤ E1 - Gamma)
    (hgap : g2 ≤ g1) :
    Rext2 ≤ Rext1 - Gamma := by
  rw [hR1, hR2]
  linarith

/-- При `KL2 ≤ KL1` — `KL2 + base ≤ KL1 + base`. -/
theorem pb_gap_bound_mono (KL1 KL2 base : ℝ)
    (hKL : KL2 ≤ KL1) :
    KL2 + base ≤ KL1 + base := by linarith

end Hagi.Dynamics

namespace Hagi
export Hagi.Dynamics (capability_gain_transfer pb_gap_bound_mono)
end Hagi
