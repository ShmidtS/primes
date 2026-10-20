/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic

set_option linter.style.header false

namespace Hagi.Optimization

open InnerProductSpace

/-!
# SphericalDamping — угловое демпфирование и хордовый остаток

Мост к сферическим фиксированным решателям (SFPRM,
arXiv:2610.25646): обучение/вывод как угловые операции на
гиперсфере. Два формализованных ингредиента оптимального
сферического оптимизатора HAGI:

* `chordal_residual_eq` — хордовый остаток остановки
  `ρ = 1 − ⟪u,v⟫ = ½‖u−v‖²` для единичных векторов;
* `angular_damping_window` — окно устойчивости углового
  демпфирования `|1 − η + ηζ| < 1 ↔ 0 < η < 2/(1−ζ)` для
  действительных мод спектра ζ < 1 (действительный случай
  Thm 1 SFPRM).

Связка с R520 (пик телесного угла Ω_n при n = 7): в
пик-размерности угловое разрешение между направлениями
максимально — сферическая параметризация шага (η как доля
угла) согласована с максимумом Ω_7.
-/

/-- **Хордовый остаток остановки**: для единичных векторов
`ρ = 1 − ⟪u, v⟫_ℝ = ½·‖u − v‖²` — масштабно-инвариантный
критерий остановки фиксированной итерации на сфере
(SFPRM eq. 9). -/
theorem chordal_residual_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (u v : F) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (1:ℝ) - ⟪u, v⟫_ℝ = (1/2) * ‖u - v‖^2 := by
  rw [norm_sub_sq_real, hu, hv]
  ring

/-- **Окно углового демпфирования** (действительный спектр):
для моды ζ < 1 линеаризованный шаг `(1 − η) + η·ζ` устойчив
(`|(1−η) + ηζ| < 1`) тогда и только тогда, когда

  `0 < η < 2 / (1 − ζ)`

(действительный случай Thm 1 SFPRM, arXiv:2610.25646):
демпфирование усмиряет осциллирующие/расходящиеся моды,
окно шага явно; совместно с геометрическим охлаждением
(`geometric_cooling_steps`) задаёт устойчивое расписание
углового шага оптимизатора HAGI. -/
theorem angular_damping_window (ζ η : ℝ) (hζ : ζ < 1) :
    |1 - η + η * ζ| < 1 ↔ 0 < η ∧ η < 2 / (1 - ζ) := by
  have hpos : 0 < 1 - ζ := by linarith
  constructor
  · intro h
    rw [abs_lt] at h
    constructor
    · have hnn : (1:ℝ) - η + η * ζ < 1 := h.2
      nlinarith [hpos]
    · rw [lt_div_iff₀ hpos]
      nlinarith [hpos, h.left]
  · rintro ⟨h1, h2⟩
    rw [abs_lt]
    have hk : η * (1 - ζ) < 2 := (lt_div_iff₀ hpos).mp h2
    constructor <;> nlinarith [h1, hpos]

end Hagi.Optimization
