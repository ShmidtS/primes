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


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Норма смеси на сфере** (SFPRM Lemma 3-ядро):
`‖α•u + β•v‖² = α² + 2αβ⟪u,v⟫ + β²` для единичных u, v. -/
theorem mixture_norm_sq (u v : F) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (α β : ℝ) :
    ‖α • u + β • v‖^2 = α^2 + 2*α*β*⟪u, v⟫_ℝ + β^2 := by
  rw [show ‖α • u + β • v‖^2
      = ⟪α • u + β • v, α • u + β • v⟫_ℝ from (real_inner_self_eq_norm_sq _).symm]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  have huu : ⟪u, u⟫_ℝ = 1 := (inner_eq_one_iff_of_norm_eq_one hu hu).mpr rfl
  have hvv : ⟪v, v⟫_ℝ = 1 := (inner_eq_one_iff_of_norm_eq_one hv hv).mpr rfl
  rw [huu, hvv, real_inner_comm v u]; ring

/-- **Нормализованная смесь на дуге**: внутреннее
произведение нормализованной смеси с u в точности
`(α + β·⟪u,v⟫)/‖α•u + β•v‖` — угол нормализованной
евклидовой смеси зависит только от α/β и угла между u и v:
аддитивная инъекция (FPRM) и геодезическая (SFPRM Slerp λ)
двигают состояние по ОДНОЙ И ТОЙ ЖЕ дуге — сферическая
параметризация шага совместима с аддитивной. -/
theorem normalized_mixture_inner (u v : F) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (α β : ℝ) :
    ⟪(‖α • u + β • v‖⁻¹) • (α • u + β • v), u⟫_ℝ
      = (α + β * ⟪u, v⟫_ℝ) / ‖α • u + β • v‖ := by
  rw [real_inner_smul_left]
  have h1 : ⟪α • u + β • v, u⟫_ℝ = α + β * ⟪v, u⟫_ℝ := by
    simp only [inner_add_left, real_inner_smul_left]
    rw [show ⟪u, u⟫_ℝ = 1 from (inner_eq_one_iff_of_norm_eq_one hu hu).mpr rfl]
    ring
  rw [div_eq_inv_mul, h1, real_inner_comm v u]


/-- **Нормализованная смесь на сфере**: при ненулевой смеси
`‖(‖α•u + β•v‖⁻¹)•(α•u + β•v)‖ = 1` — нормализованный шаг
остаётся на единичной сфере (структурная ограниченность
SFPRM: расходимость невозможна по построению, никаких
связанных коэффициентов FPRM не требуется). -/
theorem mixture_normalize_unit {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (u v : F) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (α β : ℝ)
    (hnz : ‖α • u + β • v‖ ≠ 0) :
    ‖(‖α • u + β • v‖⁻¹) • (α • u + β • v)‖ = 1 := by
  rw [norm_smul]
  rw [show ‖(‖α • u + β • v‖⁻¹ : ℝ)‖ = ‖α • u + β • v‖⁻¹ from by
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    ]
  rw [inv_mul_cancel₀ hnz]

/-- **Явная хордовая дистанция шага**: расстояние
нормализованной смеси до исходной точки u в явных α, β и
угле:

  `½‖step − u‖² = 1 − (α + β·⟪u,v⟫)/‖α•u + β•v‖`

Композиция `chordal_residual_eq` × `normalized_mixture_inner`
× `mixture_normalize_unit`: критерий останова SFPRM получает
явную формулу через параметры шага — хордовый остаток
аддитивной инъекции вычислим напрямую из α, β, c. -/
theorem normalized_mixture_distance {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (u v : F) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (α β : ℝ)
    (hnz : ‖α • u + β • v‖ ≠ 0) :
    (1/2) * ‖(‖α • u + β • v‖⁻¹) • (α • u + β • v) - u‖^2
      = 1 - (α + β * ⟪u, v⟫_ℝ) / ‖α • u + β • v‖ := by
  rw [← chordal_residual_eq _ _ (mixture_normalize_unit u v hu hv α β hnz) hu]
  rw [normalized_mixture_inner u v hu hv α β]
end Hagi.Optimization
