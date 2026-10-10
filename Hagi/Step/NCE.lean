/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# NCE — декомпозиция prior-NCE и её несмещённое ядро

Разложение `log p = log q + log(p/q)` с предложением q
(юниграммная таблица) и коррекцией p/q.

* `nce_decomposition`: при `0 < q v` всюду, где `0 < p v`, —
  тождество `log p = log q + log(p/q)` поточечно на
  носителе p (декомпозиция точна; смещение — только в
  оценщике коррекции);
* `nce_correction_pos`: при тех же посылках `0 < p v / q v`
  на носителе p (нормализованная коррекция — сэмплирующий
  вес NCE; вторая момента p/q под q управляет дисперсией
  K-негативной оценки — эмпирический якорь, не теорема
  здесь).

Полный NCE bias-bound (K-зависимая константа) — классическая
теория, вне этого модуля.
-/

open scoped Matrix

namespace Hagi.Step

section NCE

variable {V : Type*} [Fintype V]

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- При `0 < p v → 0 < q v` для всех v и `0 < p v`:
`log (p v) = log (q v) + log (p v / q v)` — точное
разложение на носителе p. -/
theorem nce_decomposition (p q : V → ℝ)
    (hpos : ∀ v, 0 < p v → 0 < q v) :
    ∀ v, 0 < p v →
      Real.log (p v) = Real.log (q v) + Real.log (p v / q v) := by
  intro v hp
  have hq := hpos v hp
  rw [Real.log_div (by exact ne_of_gt hp) (by exact ne_of_gt hq)]
  ring

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- При `0 < p v → 0 < q v` для всех v и `0 < p v`:
`0 < p v / q v` (позитивная коррекция — сэмплирующий вес). -/
theorem nce_correction_pos (p q : V → ℝ)
    (hpos : ∀ v, 0 < p v → 0 < q v) :
    ∀ v, 0 < p v → 0 < p v / q v :=
  fun v hp => div_pos hp (hpos v hp)

end NCE

end Hagi.Step

namespace Hagi
export Hagi.Step (nce_decomposition nce_correction_pos)
end Hagi
