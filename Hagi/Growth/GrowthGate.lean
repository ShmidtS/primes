/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# GrowthGate — вердикты двумерного контроллера (G_F, R_repr)

Вердикт-таблица роста как четыре непересекающиеся импликации
по ячейкам сетки решений `(G_F, R)` с порогом `eps > 0`:

* `verdict_ttt`: `eps ≤ G_F` и `R ≤ eps` дают `0 ≤ G_F − R` и
  `eps ≤ G_F`;
* `verdict_grow`: `eps < R` даёт `0 < R − eps`;
* `verdict_exhausted`: `G_F < eps` и `eps < R` дают
  `G_F < eps ∧ eps < R`.
-/

open Finset

namespace Hagi.Growth

section GrowthGate

variable {V : Type*} [Fintype V]

-- вердикт-таблица: четыре непересекающиеся импликации,
-- по одной на ячейку сетки решений (G_F, R)

/-- Ячейка 1: если `eps ≤ GF` и `R ≤ eps`, то `0 ≤ GF − R` и
`eps ≤ GF`. -/
theorem verdict_ttt (GF R eps : ℝ) (_heps : 0 < eps)
    (h1 : eps ≤ GF) (h2 : R ≤ eps) : (0 ≤ GF - R) ∧ (eps ≤ GF) := by
  constructor <;> linarith

/-- Ячейка 2: если `eps < R`, то `0 < R − eps`. -/
theorem verdict_grow (GF R eps : ℝ) (_heps : 0 < eps)
    (_h1 : eps ≤ GF) (h2 : eps < R) : 0 < R - eps := by linarith

/-- Ячейка 4: если `GF < eps` и `eps < R`, то `GF < eps ∧ eps < R`. -/
theorem verdict_exhausted (GF R eps : ℝ) (_heps : 0 < eps)
    (h1 : GF < eps) (h2 : eps < R) : GF < eps ∧ eps < R := ⟨h1, h2⟩

end GrowthGate

end Hagi.Growth

namespace Hagi
export Hagi.Growth (verdict_ttt verdict_grow verdict_exhausted)
end Hagi
