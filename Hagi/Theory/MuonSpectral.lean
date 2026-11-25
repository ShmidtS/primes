/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.External.Flywheel.SVD

/-!
# MuonSpectral — rank-one спектральный шаг и `σ_max`

C670. Спектральный срез шага Muon (hagi/core.py:1755 @ca52eb4):
`newton_schulz_orthogonalize(G, iters=3)` (core.py:1350 @ca52eb4)
приближает полярный фактор `U Vᵀ` градиента. Здесь — rank-one ядро:
среди шагов `Δ = u ⊗ v` с единичными `u`, `v` (у такого шага
`‖Δ‖₂ = 1`) максимум `⟨G, Δ⟩ = Σ_{ij} G i j·Δ i j` равен `σ_max(G)`
и достигается на топ-паре `(u₁, v₁)`.

* `smax G` — наибольшее сингулярное число (`max_i √(λᵢ(GᵀG))`).
* `rank_one_inner` — `⟨G, u ⊗ v⟩ = Σ_i u i·(G v) i`.
* `rank_one_norm_bound` — `‖G v‖² ≤ σ_max(G)²·‖v‖²` (Courant–Fischer
  для `GᵀG` в форме SVD).
* `rank_one_inner_le` — (T1) для единичных `u`, `v`:
  `⟨G, u ⊗ v⟩ ≤ smax G`.
* `rank_one_spectral_norm` — (T2) `‖u ⊗ v‖₂ = 1` при единичных `u`, `v`.
* `rank_one_attains` — (T3) на топ-паре (столбцы `U`, `V` с индексом
  топ-σ) шаг `u₁ ⊗ v₁` единичный и `⟨G, u₁ ⊗ v₁⟩ = smax G`.
* `rank_one_spectral_step_optimal` — (T4) итог: всякий rank-one шаг
  нормы 1 даёт `⟨G, Δ⟩ ≤ smax G`, и граница достигается.

Честная граница (down-scope): полный шаг Muon `U Vᵀ` (все ранги;
`⟨G, Δ⟩ ≤ ‖G‖_*·‖Δ‖₂`) требует неравенства фон Неймана о следе /
дуальности спектральной и ядерной норм — в Mathlib v4.36 pin их нет
(диагональный срез — `Hagi.Step.MuonAlign.muon_alignment_optimal`).
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.MuonSpectral

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Frobenius-спаривание `Σ_{ij} G i j·Δ i j`. -/
noncomputable def fdot (G Δ : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, G i j * Δ i j

/-- Rank-one матрица `u ⊗ v`: `(u ⊗ v) i j = u i·v j`. -/
noncomputable def r1 (u v : n → ℝ) : Matrix n n ℝ :=
  fun i j => u i * v j

/-- Наибольшее сингулярное число: `σ_max(G) = max_i √(λᵢ(GᵀG))`. -/
noncomputable def smax [Nonempty n] (G : Matrix n n ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty
    (Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G)

/-- Единичный (по `l2`) вектор. -/
def Unit (x : n → ℝ) : Prop := ∑ i, x i ^ 2 = 1

/-- `σ_max ≥ 0`. -/
lemma smax_nonneg [Nonempty n] (G : Matrix n n ℝ) : 0 ≤ smax G := by
  show 0 ≤ Finset.sup' Finset.univ Finset.univ_nonempty
    (Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G)
  exact Finset.sup'_induction (Finset.univ_nonempty : (Finset.univ : Finset n).Nonempty)
    (Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G)     (fun a₁ ha a₂ _ => le_trans ha le_sup_left) (fun b _ => Real.sqrt_nonneg _)

omit [DecidableEq n] in
/-- `‖M v‖² = Σ_i v i·(Mᵀ(M v)) i`. -/
lemma sum_sq_mulVec (M : Matrix n n ℝ) (w : n → ℝ) :
    ∑ k, (M *ᵥ w) k ^ 2 = ∑ k, w k * (Mᵀ *ᵥ (M *ᵥ w)) k := by
  have h1 : ∀ k, ((M *ᵥ w) k ^ 2) = ∑ j, (M k j * w j) * (M *ᵥ w) k := by
    intro k
    rw [sq, show (M *ᵥ w) k = ∑ j, M k j * w j from rfl, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => by ring

omit [DecidableEq n] in
/-- **`rank_one_inner`**: `⟨G, u ⊗ v⟩ = Σ_i u i·(G v) i`. -/
theorem rank_one_inner (G : Matrix n n ℝ) (u v : n → ℝ) :
    fdot G (r1 u v) = ∑ i, u i * (G *ᵥ v) i := by
  simp only [fdot, r1, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Ортогональная (по столбцам) матрица сохраняет квадрат нормы. -/
lemma ortho_preserves_sq (M : Matrix n n ℝ) (hM : Mᵀ * M = 1) (w : n → ℝ) :
    ∑ k, (M *ᵥ w) k ^ 2 = ∑ k, w k ^ 2 := by
  rw [sum_sq_mulVec, Matrix.mulVec_mulVec w Mᵀ M, hM, Matrix.one_mulVec]
  exact Finset.sum_congr rfl fun k _ => (sq (w k)).symm

/-- Явный носитель SVD: `G = U·Σ·Vᵀ`, `σ = realSingularValues G`. -/
lemma smax_svd (G : Matrix n n ℝ) :
    ∃ U V : Matrix n n ℝ, ∃ σ : n → ℝ,
      U ∈ Matrix.orthogonalGroup n ℝ ∧ V ∈ Matrix.orthogonalGroup n ℝ ∧
      σ = Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G ∧
      G = U * Matrix.diagonal σ * Vᵀ := by
  refine ⟨(Hagi.External.Flywheel.Matrix.SVD.Real.constructedU_real G : Matrix n n ℝ),
    ((Hagi.External.Flywheel.Matrix.SVD.Real.rightOrthogonal G) : Matrix n n ℝ),
    Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G,
    (Hagi.External.Flywheel.Matrix.SVD.Real.constructedU_real G).2,
    (Hagi.External.Flywheel.Matrix.SVD.Real.rightOrthogonal G).2, rfl, ?_⟩
  have hV : (Hagi.External.Flywheel.Matrix.SVD.Real.rightOrthogonal G : Matrix n n ℝ) *
      (Hagi.External.Flywheel.Matrix.SVD.Real.rightOrthogonal G : Matrix n n ℝ)ᵀ = 1 :=
    (mem_orthogonalGroup_iff n ℝ).1 (Hagi.External.Flywheel.Matrix.SVD.Real.rightOrthogonal G).2
  have hAV := Hagi.External.Flywheel.Matrix.SVD.Real.realAV_eq_constructedU_real_mul_sigma G
  refine Eq.trans (mul_one G).symm ?_
  rw [← hV]
  refine Eq.trans (mul_assoc G _ _).symm ?_
  have hAV : G * (Hagi.External.Flywheel.Matrix.SVD.Real.rightOrthogonal G : Matrix n n ℝ) = _ :=
    Hagi.External.Flywheel.Matrix.SVD.Real.realAV_eq_constructedU_real_mul_sigma G
  rw [hAV, mul_assoc]

/-- **`rank_one_norm_bound`**: `‖G v‖² ≤ σ_max(G)²·‖v‖²` —
Courant–Fischer для `GᵀG` в форме SVD (`G = U Σ Vᵀ`). -/
theorem rank_one_norm_bound [Nonempty n] (G : Matrix n n ℝ) (v : n → ℝ) :
    ∑ k, (G *ᵥ v) k ^ 2 ≤ (smax G) ^ 2 * ∑ k, v k ^ 2 := by
  classical
  obtain ⟨U, V, σ, hUo, hVo, hσdef, hG⟩ := smax_svd G
  have hUt : Uᵀ * U = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl n)).1
    ((mem_orthogonalGroup_iff n ℝ).1 hUo)
  have hVt : Vᵀ * V = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl n)).1
    ((mem_orthogonalGroup_iff n ℝ).1 hVo)
  have hGv : G *ᵥ v = U *ᵥ (Matrix.diagonal σ *ᵥ (Vᵀ *ᵥ v)) := by
    rw [hG]
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  have h3 : ∀ k, (σ k) ^ 2 ≤ (smax G) ^ 2 := by
    intro k
    have hle : σ k ≤ smax G := by
      rw [hσdef]
      exact Finset.le_sup' _ (Finset.mem_univ k)
    have hs' : 0 ≤ smax G := smax_nonneg G
    have hsk : 0 ≤ σ k := by
      rw [hσdef]; exact Real.sqrt_nonneg _
    nlinarith [sq_nonneg (smax G - σ k), hsk]
  have hdiag : ∀ k, (Matrix.diagonal σ *ᵥ (Vᵀ *ᵥ v)) k
      = σ k * (Vᵀ *ᵥ v) k := fun k => by
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [hGv, ortho_preserves_sq _ hUt]
  calc ∑ k, (Matrix.diagonal σ *ᵥ (Vᵀ *ᵥ v)) k ^ 2
      ≤ ∑ k, (smax G) ^ 2 * ((Vᵀ *ᵥ v) k) ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [hdiag k, mul_pow]
        exact mul_le_mul_of_nonneg_right (h3 k) (sq_nonneg _)
    _ = (smax G) ^ 2 * ∑ k, v k ^ 2 := by
      have ho := ortho_preserves_sq Vᵀ (by
        rw [Matrix.transpose_transpose]; exact (mem_orthogonalGroup_iff n ℝ).1 hVo) v
      calc ∑ k, (smax G) ^ 2 * ((Vᵀ *ᵥ v) k) ^ 2
          = (smax G) ^ 2 * ∑ k, (Vᵀ *ᵥ v) k ^ 2 := (Finset.mul_sum _ _ _).symm
        _ = (smax G) ^ 2 * ∑ k, v k ^ 2 := by rw [ho]

/-- **`rank_one_inner_le`** (T1, граница): для единичных `u`, `v`
`⟨G, u ⊗ v⟩ ≤ σ_max(G)`. -/
theorem rank_one_inner_le [Nonempty n] (G : Matrix n n ℝ) (u v : n → ℝ)
    (hu : Unit u) (hv : Unit v) :
    fdot G (r1 u v) ≤ smax G := by
  rw [rank_one_inner]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n) u (G *ᵥ v)
  have hb := rank_one_norm_bound G v
  rw [hv, mul_one] at hb
  rw [hu, one_mul] at hcs
  have h1 : (∑ i, u i * (G *ᵥ v) i) ^ 2 ≤ (smax G) ^ 2 := by linarith
  have h2 : |∑ i, u i * (G *ᵥ v) i| ≤ smax G := by
    have hsq2 : |∑ i, u i * (G *ᵥ v) i| ^ 2 ≤ (smax G) ^ 2 := by
      rw [sq_abs]; exact h1
    have hs0 : 0 ≤ smax G := smax_nonneg G
    rcases le_or_gt |∑ i, u i * (G *ᵥ v) i| (smax G) with h | h
    · exact h
    · exfalso
      have hm : 0 < (|∑ i, u i * (G *ᵥ v) i| - smax G) *
          (|∑ i, u i * (G *ᵥ v) i| + smax G) := mul_pos (sub_pos.mpr h) (by linarith [hs0])
      nlinarith
  exact le_trans (le_abs_self _) h2

/-- **`rank_one_spectral_norm`** (T2): при единичных `u`, `v` rank-one шаг
`u ⊗ v` имеет спектральную (операторную `l2`) норму 1. -/
theorem rank_one_spectral_norm (u v : n → ℝ) (hu : Unit u) (hv : Unit v) :
    ‖r1 u v‖ = 1 := by
  rw [Matrix.l2_opNorm_def]
  set L := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) (fun i j => u i * v j) with hL
  have hmul (x : EuclideanSpace ℝ n) (i : n) : (L x) i = u i * ∑ j, v j * x j := by
    rw [hL]
    show Matrix.toLin' (Matrix.of fun i j => u i * v j) (WithLp.ofLp x) i = _
    rw [Matrix.toLin'_apply]
    simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsq (x : EuclideanSpace ℝ n) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
    rw [EuclideanSpace.norm_eq, sq, Real.mul_self_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp
  have hupper : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    have hLx : ∑ i, (L x) i ^ 2 ≤ ∑ j, x j ^ 2 := by
      calc (∑ i, (L x) i ^ 2) = (∑ i, u i ^ 2) * (∑ j, v j * x j) ^ 2 := by
            rw [Finset.sum_congr rfl fun i _ => by rw [hmul x i],
              Finset.sum_congr rfl fun i _ => mul_pow _ _ 2]
            rw [← Finset.sum_mul]
        _ ≤ 1 * ∑ j, x j ^ 2 := by
          have h2 : (∑ j, v j * x j) ^ 2 ≤ (∑ j, v j ^ 2) * ∑ j, x j ^ 2 :=
            Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n) v x
          rw [hv, one_mul] at h2
          rw [hu, one_mul, one_mul]
          exact h2
        _ = ∑ j, x j ^ 2 := one_mul _
    rw [← hsq x, ← hsq (L x)] at hLx
    have h3 := Real.sqrt_le_sqrt hLx
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

  have hlower : 1 ≤ ‖L‖ := by
    have hvv : ∑ j, v j * v j = 1 := by
      rw [← hv]; exact Finset.sum_congr rfl fun j _ => (sq (v j)).symm
    have hLv : L (WithLp.toLp 2 v) = WithLp.toLp 2 u := by
      ext i
      rw [hmul _ i]
      show u i * (∑ j, v j * (WithLp.toLp 2 v) j) = WithLp.toLp 2 u i
      rw [hvv, mul_one]
    have hn1 : ‖WithLp.toLp 2 v‖ ^ 2 = 1 := by rw [hsq]; exact hv
    have hn2 : ‖WithLp.toLp 2 u‖ ^ 2 = 1 := by rw [hsq]; exact hu
    have h := ContinuousLinearMap.le_opNorm L (WithLp.toLp 2 v)
    have e1 : ‖WithLp.toLp 2 v‖ = 1 := by nlinarith [norm_nonneg (WithLp.toLp 2 v)]
    have e2 : ‖WithLp.toLp 2 u‖ = 1 := by nlinarith [norm_nonneg (WithLp.toLp 2 u)]
    rw [hLv, e2, e1, mul_one] at h
    exact h
  exact le_antisymm hupper hlower

/-- **`rank_one_attains`** (T3, достижимость): топ-пара — столбцы `U`, `V`
с индексом `k`, на котором `σ` достигает `σ_max`, — даёт единичные
`u₁`, `v₁` и `⟨G, u₁ ⊗ v₁⟩ = σ_max(G)`. -/
theorem rank_one_attains [Nonempty n] (G : Matrix n n ℝ) :
    ∃ u v : n → ℝ, Unit u ∧ Unit v ∧ fdot G (r1 u v) = smax G := by
  classical
  obtain ⟨U, V, σ, hUo, hVo, hσdef, hG⟩ := smax_svd G
  have hUt : Uᵀ * U = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl n)).1
    ((mem_orthogonalGroup_iff n ℝ).1 hUo)
  have hVt : Vᵀ * V = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl n)).1
    ((mem_orthogonalGroup_iff n ℝ).1 hVo)
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ σ
    (Finset.univ_nonempty : Finset.univ.Nonempty)
  have hSk : smax G = σ k := by
    show Finset.sup' Finset.univ Finset.univ_nonempty
      (Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G) = σ k
    rw [← hσdef]
    exact le_antisymm ((Finset.sup'_le_iff Finset.univ_nonempty σ).2 fun a _ => hk a (Finset.mem_univ a))
      (Finset.le_sup' _ (Finset.mem_univ k))
  have hcol (M : Matrix n n ℝ) (hM : Mᵀ * M = 1) : ∑ i, M i k ^ 2 = 1 := by
    have h1 : ∑ i, M i k ^ 2 = (Mᵀ * M) k k := by
      simp [Matrix.mul_apply, Matrix.transpose_apply, sq]
    simp [h1, hM]
  have hVk : ∀ l, ∑ m, V m l * V m k = if l = k then 1 else 0 := by
    intro l
    have h1 : ∑ m, V m l * V m k = (Vᵀ * V) l k := by
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    simp only [h1, hVt, Matrix.one_apply]
  have hGv : ∀ i, (G *ᵥ (fun m => V m k)) i = σ k * U i k := by
    intro i
    have h1 : G *ᵥ (fun m => V m k)
        = (U * Matrix.diagonal σ * Vᵀ) *ᵥ (fun m => V m k) := by rw [hG]
    rw [h1]
    show ∑ c, (∑ a, (∑ b, U i b * Matrix.diagonal σ b a) * V c a) * V c k = σ k * U i k
    simp only [Finset.sum_mul, Matrix.diagonal_apply]
    have key : ∀ x y : n, ∑ a, ((U i a * if a = y then σ a else 0) * V x y) * V x k
        = U i y * σ y * (V x y * V x k) := by
      intro x y
      rw [Finset.sum_congr rfl fun a _ => show
        ((U i a * if a = y then σ a else 0) * V x y) * V x k
          = if a = y then U i a * σ a * (V x y * V x k) else 0 by split <;> ring]
      rw [Finset.sum_ite_eq']
      simp
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => key x y, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun y _ => show ∑ x, U i y * σ y * (V x y * V x k)
        = U i y * σ y * ∑ x, V x y * V x k from (Finset.mul_sum _ _ _).symm]
    rw [Finset.sum_congr rfl fun y _ => show U i y * σ y * (∑ x, V x y * V x k)
        = U i y * σ y * (if y = k then 1 else 0) by rw [hVk y]]
    simp
    ring
  refine ⟨fun i => U i k, fun m => V m k, hcol _ hUt, hcol _ hVt, ?_⟩
  rw [rank_one_inner, hSk]
  have hstep : ∑ i, U i k * (G *ᵥ (fun m => V m k)) i = ∑ i, U i k * (σ k * U i k) :=
    Finset.sum_congr rfl fun i _ => by rw [hGv i]
  rw [hstep, show ∑ i, U i k * (σ k * U i k) = σ k * ∑ i, U i k ^ 2 by
      simp only [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
  rw [hcol _ hUt, mul_one]

/-- **`rank_one_spectral_step_optimal`** (T4): всякий rank-one шаг
`Δ = u ⊗ v` со скалярными коэффициентами при единичных `u`, `v` имеет
спектральную норму 1 и даёт `⟨G, Δ⟩ ≤ σ_max(G)`; граница достигается. -/
theorem rank_one_spectral_step_optimal [Nonempty n] (G : Matrix n n ℝ) :
    (∀ u v : n → ℝ, Unit u → Unit v →
        fdot G (r1 u v) ≤ smax G ∧ ‖r1 u v‖ = 1) ∧
      ∃ u v : n → ℝ, Unit u ∧ Unit v ∧ fdot G (r1 u v) = smax G :=
  ⟨fun u v hu hv => ⟨rank_one_inner_le G u v hu hv, rank_one_spectral_norm u v hu hv⟩,
    rank_one_attains G⟩

end Hagi.Theory.MuonSpectral
