/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Step.LRWidth
set_option linter.style.header false

/-!
# Muon — спектральный прекондиционер и совместимость с SafeQP

* `muon_step_bound`: при контракции `‖P z‖ ≤ ‖z‖` для всех z
  — `‖muonDir P g‖ ≤ ‖g‖` (направление Muon не превышает
  сырой градиент по норме — совместимо с SafeQP);
* `muon_pl_rate`: `‖muonDir P g‖² ≤ ‖g‖²` при той же
  контракции.

Свойство `‖P‖_op ≤ 1` Newton-Schulz — гипотеза hP
(полярное разложение — вне этого модуля).
-/

namespace Hagi.Step

variable {V : Type} [NormedAddCommGroup V]

/-- Направление Muon: `muonDir P g = P g` —
прекондиционированный градиент. -/
def muonDir {W : Type} [NormedAddCommGroup W]
    (P : W → W) (g : W) : W := P g

/-- Если `‖P z‖ ≤ ‖z‖` для всех z, то `‖muonDir P g‖ ≤ ‖g‖`. -/
theorem muon_step_bound {W : Type} [NormedAddCommGroup W]
    (P : W → W) (g : W)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) :
    ‖muonDir P g‖ ≤ ‖g‖ :=
  hP g

/-- Если `‖P z‖ ≤ ‖z‖` для всех z, то
`‖muonDir P g‖^2 ≤ ‖g‖^2`. -/
theorem muon_pl_rate {W : Type} [NormedAddCommGroup W]
    (P : W → W) (g : W)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) :
    ‖muonDir P g‖^2 ≤ ‖g‖^2 := by
  rw [sq, sq]
  exact mul_self_le_mul_self (norm_nonneg _) (hP g)

end Hagi.Step

namespace Hagi
export Hagi.Step (muonDir muon_step_bound muon_pl_rate)
end Hagi
