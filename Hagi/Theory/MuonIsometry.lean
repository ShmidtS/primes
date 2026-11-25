/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.MuonSpectral

/-!
# MuonIsometry — полный шаг Muon оптимален на группе изометрий

C672. Продолжение `Hagi.Theory.MuonSpectral` (rank-one срез). Полный шаг
Muon — это полярный фактор `U Vᵀ` градиента `G = U Σ Vᵀ`: идеальный
Newton–Schulz (hagi/core.py:1350 @ca52eb4, итерация
`X ← X(3I − XᵀX)/2`, core.py:1363) выдаёт матрицу с ортонормальными
столбцами — изометрию `ΔᵀΔ = 1`. Здесь доказано без неравенства фон
Неймана: среди всех изометрий `Δ` максимум `⟨G, Δ⟩` равен сумме
сингулярных чисел и достигается на `Δ = U Vᵀ`.

Ключ: `⟨G, Δ⟩ = tr(GᵀΔ) = tr(Σ·Q) = Σ_i σ i·Q i i` с `Q = UᵀΔV`; `Q` —
изометрия, поэтому `Q i i ≤ 1`, и `σ i ≥ 0`.

* `ssum G` — сумма сингулярных чисел (ядерная норма `‖G‖_*`).
* `isometry_diag_le_one` — (T1) `ΔᵀΔ = 1 ⇒ Δ i i ≤ 1`.
* `fdot_eq_trace`, `inner_eq_sigma_weighted_diag` — носители:
  `⟨G, Δ⟩ = tr(GᵀΔ) = Σ_i σ i·(UᵀΔV) i i`.
* `isometry_inner_le_ssum` — (T2) `ΔᵀΔ = 1 ⇒ ⟨G, Δ⟩ ≤ ssum G`.
* `uv_transpose_isometry`, `uv_transpose_attains_ssum` — (T3)
  `U Vᵀ` — изометрия и `⟨G, U Vᵀ⟩ = ssum G`.
* `muon_step_optimal_in_isometry_group` — (T4) итог: граница + достижимость.

Честная граница: код нормирует `G` на `‖G‖_F` (`np.linalg.norm`,
core.py:1353) и делает `iters = 3` (core.py:1755), поэтому реальный
выход — приближённая изометрия (нижняя граница `σ_min` за 3 итерации не
формализована); прямоугольный `G` (транспонирование core.py:1358) не
формализован; связь `⟨G, Δ⟩` с фактическим обновлением `W1` (core.py:1755)
— мост lm.py:586, не формализована.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.MuonIsometry

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Изометрия: ортонормальные столбцы `ΔᵀΔ = 1` (для квадратной `Δ` —
ортогональная матрица). -/
def Isometry (Δ : Matrix n n ℝ) : Prop := Δᵀ * Δ = 1

/-- Сумма сингулярных чисел `Σ_i σ i = ‖G‖_*`. -/
noncomputable def ssum (G : Matrix n n ℝ) : ℝ :=
  ∑ i, Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i

lemma ssum_nonneg (G : Matrix n n ℝ) : 0 ≤ ssum G :=
  Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _

lemma ssum_eq (G : Matrix n n ℝ) (σ : n → ℝ)
    (hσ : σ = Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G) :
    ssum G = ∑ i, σ i := by rw [ssum, hσ]

/-- **`isometry_diag_le_one`** (T1): у изометрии диагональный элемент
не превосходит 1 (столбец единичный). -/
theorem isometry_diag_le_one (Q : Matrix n n ℝ) (hQ : Isometry Q) (i : n) :
    Q i i ≤ 1 := by
  have h1 : ∑ j, Q j i ^ 2 = 1 := by
    have h : ∑ j, Q j i * Q j i = 1 := by
      have h' : ∑ j, Q j i * Q j i = (Qᵀ * Q) i i := by
        simp [Matrix.mul_apply, Matrix.transpose_apply]
      rw [h', hQ, Matrix.one_apply]
      simp
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => (sq (Q j i))
  have h2 : Q i i ^ 2 ≤ 1 := by
    calc Q i i ^ 2 ≤ ∑ j, Q j i ^ 2 :=
        Finset.single_le_sum (f := fun j => Q j i ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)
      _ = 1 := h1
  have h3 : |Q i i| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 h2
  exact le_trans (le_abs_self _) h3

omit [DecidableEq n] in
/-- `⟨G, Δ⟩ = tr(GᵀΔ)`. -/
lemma fdot_eq_trace (G Δ : Matrix n n ℝ) :
    Hagi.Theory.MuonSpectral.fdot G Δ = (Gᵀ * Δ).trace := by
  simp only [Hagi.Theory.MuonSpectral.fdot, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]


/-- Носитель: `⟨G, Δ⟩ = Σ_i σ i·Q i i`, где `Q = UᵀΔV`. -/
lemma inner_eq_sigma_weighted_diag (U V : Matrix n n ℝ) (σ : n → ℝ)
    (G Δ : Matrix n n ℝ)
    (hG : G = U * Matrix.diagonal σ * Vᵀ) :
    Hagi.Theory.MuonSpectral.fdot G Δ
      = ∑ i, σ i * (Uᵀ * Δ * V) i i := by
  rw [fdot_eq_trace]
  have h1 : Gᵀ * Δ = V * Matrix.diagonal σ * (Uᵀ * Δ) := by
    rw [hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose]
    noncomm_ring
  rw [h1, Matrix.mul_assoc, Matrix.trace_mul_comm V, Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have h2 : ∀ (Q : Matrix n n ℝ) (i : n), (Matrix.diagonal σ * Q) i i
      = σ i * Q i i := by
    intro Q i
    simp only [Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun j _ hj => by rw [if_neg (Ne.symm hj), zero_mul])]
    simp
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_assoc, h2]

/-- `UᵀΔV` — изометрия, если `U`, `V` ортогональны, `Δ` — изометрия. -/
lemma isometry_conj (U V Δ : Matrix n n ℝ) (hU : U * Uᵀ = 1)
    (hVt : Vᵀ * V = 1) (hΔ : Isometry Δ) :
    Isometry (Uᵀ * Δ * V) := by
  have h1 : (Uᵀ * Δ * V)ᵀ * (Uᵀ * Δ * V) = Vᵀ * Δᵀ * (U * Uᵀ) * Δ * V := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    noncomm_ring
  rw [Isometry, h1]
  have h2 : Vᵀ * Δᵀ * Δ = Vᵀ := by
    rw [Matrix.mul_assoc, hΔ, Matrix.mul_one]
  simp only [Matrix.mul_one, hU, h2, hVt]

/-- **`isometry_inner_le_ssum`** (T2): для всякой изометрии `Δ`
`⟨G, Δ⟩ ≤ ssum G` — без неравенства фон Неймана. -/
theorem isometry_inner_le_ssum (G Δ : Matrix n n ℝ) (hΔ : Isometry Δ) :
    Hagi.Theory.MuonSpectral.fdot G Δ ≤ ssum G := by
  classical
  obtain ⟨U, V, σ, hUo, hVo, hσdef, hG⟩ := Hagi.Theory.MuonSpectral.smax_svd G
  have hUt : Uᵀ * U = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl n)).1
    ((mem_orthogonalGroup_iff n ℝ).1 hUo)
  have hU : U * Uᵀ = 1 := (mem_orthogonalGroup_iff n ℝ).1 hUo
  have hVt : Vᵀ * V = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl n)).1
    ((mem_orthogonalGroup_iff n ℝ).1 hVo)
  have hV : V * Vᵀ = 1 := (mem_orthogonalGroup_iff n ℝ).1 hVo
  rw [inner_eq_sigma_weighted_diag U V σ G Δ hG, ssum_eq G σ hσdef]
  have hs : ∀ i, 0 ≤ σ i := fun i => by rw [hσdef]; exact Real.sqrt_nonneg _
  refine Finset.sum_le_sum fun i _ => ?_
  have h := mul_le_mul_of_nonneg_left
    (isometry_diag_le_one _ (isometry_conj U V Δ hU hVt hΔ) i) (hs i)
  rwa [mul_one] at h

/-- `U Vᵀ` — изометрия для ортогональных `U`, `V`. -/
lemma uv_transpose_isometry (U V : Matrix n n ℝ) (hUt : Uᵀ * U = 1)
    (hV : V * Vᵀ = 1) : Isometry (U * Vᵀ) := by
  have h1 : (U * Vᵀ)ᵀ * (U * Vᵀ) = V * (Uᵀ * U) * Vᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    noncomm_ring
  rw [Isometry, h1]
  simp only [Matrix.mul_one, hUt, hV]

/-- **`uv_transpose_attains_ssum`** (T3): полярный фактор `U Vᵀ` —
изометрия, дающая `⟨G, U Vᵀ⟩ = ssum G`. -/
theorem uv_transpose_attains_ssum (G : Matrix n n ℝ) :
    ∃ Δ : Matrix n n ℝ, Isometry Δ ∧ Hagi.Theory.MuonSpectral.fdot G Δ = ssum G := by
  classical
  obtain ⟨U, V, σ, hUo, hVo, hσdef, hG⟩ := Hagi.Theory.MuonSpectral.smax_svd G
  have hUt : Uᵀ * U = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl n)).1
    ((mem_orthogonalGroup_iff n ℝ).1 hUo)
  have hU : U * Uᵀ = 1 := (mem_orthogonalGroup_iff n ℝ).1 hUo
  have hVt : Vᵀ * V = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl n)).1
    ((mem_orthogonalGroup_iff n ℝ).1 hVo)
  have hV : V * Vᵀ = 1 := (mem_orthogonalGroup_iff n ℝ).1 hVo
  refine ⟨U * Vᵀ, uv_transpose_isometry U V hUt hV, ?_⟩
  have hQ : Uᵀ * (U * Vᵀ) * V = 1 := by
    simp only [Matrix.mul_assoc, hVt, hUt, Matrix.mul_one]
  rw [inner_eq_sigma_weighted_diag U V σ G (U * Vᵀ) hG, ssum_eq G σ hσdef, hQ]
  simp

/-- **`muon_step_optimal_in_isometry_group`** (T4): среди изометрий
`Δ` (`ΔᵀΔ = 1` — то, что выдаёт идеальный Newton–Schulz) максимум
`⟨G, Δ⟩` равен сумме сингулярных чисел `‖G‖_*`, и он достигается. -/
theorem muon_step_optimal_in_isometry_group (G : Matrix n n ℝ) :
    (∀ Δ : Matrix n n ℝ, Isometry Δ →
        Hagi.Theory.MuonSpectral.fdot G Δ ≤ ssum G) ∧
      ∃ Δ : Matrix n n ℝ, Isometry Δ ∧
        Hagi.Theory.MuonSpectral.fdot G Δ = ssum G :=
  ⟨fun Δ hΔ => isometry_inner_le_ssum G Δ hΔ, uv_transpose_attains_ssum G⟩

end Hagi.Theory.MuonIsometry
