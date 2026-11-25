/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.MuonAlignment
import Hagi.Theory.FunctionPreservingGrowth

/-!
# MuonDescent — нормировка градиента и сертификат спуска Muon-шага

C675. Замыкает цепочку C668–C674. Обновление слоя `W1 -= η·X₃`
(core.py:1755 @ca52eb4), где `X₃ = ns_iter 3 Ĝ`, `Ĝ = G/‖G‖_F`
(нормировка core.py:1353).

* `smax_smul` — (S1) `smax (c • G) = |c|·smax G` (через `smax_eq_opNorm`).
* `normed_sigma_le_one` — (S1) `G ≠ 0 ⇒ ∀ i, σ i (Ĝ) ≤ 1`: гипотеза
  `σ ≤ 1` теорем C674 снята для нормированного градиента.
* `muon_step_inner_ge_frob` — (S1) `1 ≤ ⟨Ĝ, ns_iter k Ĝ⟩` и
  `‖G‖_F ≤ ⟨G, ns_iter k Ĝ⟩`.
* `useful_of_neg_fderiv` — (S2) абстрактный сертификат: дифференциал
  в направлении отрицателен ⇒ малый шаг строго убывает.
* `muon_step_useful` — (S2) Muon-шаг: `f'(W)[Δ] = ⟨g, Δ⟩`, `g ≠ 0` ⇒
  `∃ η > 0, f (W − η•X₃) < f W`.
* `muon_vs_sign_first_order` — (S3) first-order спуск Muon-шага и
  sign-шага не меньше `‖G‖_F`.

Честная граница: в `muon_step_useful` носитель — `Matrix n n ℝ` со
sup-нормой Mathlib (на утверждение не влияет: дифференцируемость —
гипотеза) и связь `f'(W)[Δ] = ⟨g, Δ⟩` — ГИПОТЕЗА (C668/C669 доказывают
её для функционального носителя `ι → δ → ℝ` в виде
`f'(W)[Δ] = −⟨batchGrad, Δ⟩`, т.е. `g = −batchGrad`); существование
`η` — локальное, величина шага `η = cos_lr·0.7` не выводится; сходимость
и оценка числа шагов — вне теории.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.MuonDescent

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Frobenius-норма в квадрате: `Σ_{ij} G i j²`. -/
noncomputable def frobSq (G : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, G i j ^ 2

/-- Нормированный градиент кода: `Ĝ = G/‖G‖_F` (core.py:1353 @ca52eb4). -/
noncomputable def normed (G : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / Real.sqrt (frobSq G)) • G

/-- Muon-направление кода: `X₃ = ns_iter 3 Ĝ` (core.py:1755 @ca52eb4). -/
noncomputable def muonStep (G : Matrix n n ℝ) (k : ℕ) : Matrix n n ℝ :=
  Hagi.Theory.MuonAlignment.ns_iter k (normed G)

/-- Sign-шаг (Adam-sign без момента): `sign G`. -/
noncomputable def sgn (G : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j => if 0 < G i j then 1 else if G i j < 0 then -1 else 0

omit [DecidableEq n] in
lemma fdot_smul_left (G Δ : Matrix n n ℝ) (c : ℝ) :
    Hagi.Theory.MuonSpectral.fdot (c • G) Δ = c * Hagi.Theory.MuonSpectral.fdot G Δ := by
  simp only [Hagi.Theory.MuonSpectral.fdot, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq n] in
lemma frobSq_smul (G : Matrix n n ℝ) (c : ℝ) : frobSq (c • G) = c ^ 2 * frobSq G := by
  simp [frobSq, Finset.mul_sum, mul_pow]

omit [DecidableEq n] in
lemma frobSq_nonneg (G : Matrix n n ℝ) : 0 ≤ frobSq G :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq n] in
lemma frobSq_pos {G : Matrix n n ℝ} (hG : G ≠ 0) : 0 < frobSq G := by
  by_contra h0
  have h1 : frobSq G = 0 := le_antisymm (by linarith) (frobSq_nonneg G)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp h1
  have h2 : ∀ i, G i = fun _ => (0 : ℝ) := by
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => sq_nonneg _)).mp (hz i (Finset.mem_univ i))
    funext j
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hi j (Finset.mem_univ j))
  exact hG (funext h2)

omit [DecidableEq n] in
lemma fdot_normed_self {G : Matrix n n ℝ} (hG : G ≠ 0) :
    Hagi.Theory.MuonSpectral.fdot (normed G) (normed G) = 1 := by
  have hs : Real.sqrt (frobSq G) ^ 2 = frobSq G := Real.sq_sqrt (frobSq_nonneg G)
  rw [Hagi.Theory.MuonSpectral.fdot, normed]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have e : ∑ i, ∑ j, (1 / Real.sqrt (frobSq G)) * G i j * ((1 / Real.sqrt (frobSq G)) * G i j)
      = (1 / Real.sqrt (frobSq G)) ^ 2 * ∑ i, ∑ j, G i j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, div_pow, one_pow, hs]
  exact div_mul_cancel₀ 1 (ne_of_gt (frobSq_pos hG))

/-- **(S1)** `smax` однороден: `smax (c • G) = |c|·smax G`. -/
theorem smax_smul [Nonempty n] (G : Matrix n n ℝ) (c : ℝ) :
    Hagi.Theory.MuonSpectral.smax (c • G) = |c| * Hagi.Theory.MuonSpectral.smax G := by
  rw [Hagi.Theory.MuonSpectral.smax_eq_opNorm, Hagi.Theory.MuonSpectral.smax_eq_opNorm,
    Matrix.l2_opNorm_def, Matrix.l2_opNorm_def]
  have h : (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) (c • G)
      = c • (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) G := by
    simp
  rw [h, norm_smul, Real.norm_eq_abs, mul_comm]

/-- Каждое сингулярное значение не превосходит `smax`. -/
theorem sigma_le_smax [Nonempty n] (G : Matrix n n ℝ) (i : n) :
    Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues G i
      ≤ Hagi.Theory.MuonSpectral.smax G :=
  Finset.le_sup' _ (Finset.mem_univ i)

/-- **(S1) `normed_sigma_le_one`**: для `G ≠ 0` все сингулярные значения
нормированного градиента `≤ 1` — гипотеза `σ ≤ 1` (C674 T3/T4) снята. -/
theorem normed_sigma_le_one [Nonempty n] {G : Matrix n n ℝ} (hG : G ≠ 0) (i : n) :
    Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues (normed G) i ≤ 1 := by
  have hs : 0 < Real.sqrt (frobSq G) := Real.sqrt_pos.2 (frobSq_pos hG)
  calc Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues (normed G) i
      ≤ Hagi.Theory.MuonSpectral.smax (normed G) := sigma_le_smax _ i
    _ = |(1 / Real.sqrt (frobSq G))| * Hagi.Theory.MuonSpectral.smax G := smax_smul _ _
    _ ≤ 1 / Real.sqrt (frobSq G) * Real.sqrt (frobSq G) := by
        rw [abs_of_pos (one_div_pos.2 hs)]
        exact mul_le_mul_of_nonneg_left (Hagi.Theory.MuonSpectral.smax_le_frobenius G)
          (one_div_pos.2 hs).le
    _ = 1 := div_mul_cancel₀ _ (ne_of_gt hs)

/-- **(S1) `muon_step_inner_ge_frob`**: `1 ≤ ⟨Ĝ, ns_iter k Ĝ⟩ = ⟨Ĝ,Ĝ⟩`;
в единицах `G`: `‖G‖_F ≤ ⟨G, ns_iter k Ĝ⟩`. -/
theorem muon_step_inner_ge_frob [Nonempty n] {G : Matrix n n ℝ} (hG : G ≠ 0) (k : ℕ) :
    1 ≤ Hagi.Theory.MuonSpectral.fdot (normed G) (muonStep G k) ∧
      Real.sqrt (frobSq G) ≤ Hagi.Theory.MuonSpectral.fdot G (muonStep G k) := by
  have hσ := normed_sigma_le_one hG
  have h1 := Hagi.Theory.MuonAlignment.muon_alignment_ge_gradient (normed G) k hσ
  rw [fdot_normed_self hG] at h1
  refine ⟨h1, ?_⟩
  have hs : 0 < Real.sqrt (frobSq G) := Real.sqrt_pos.2 (frobSq_pos hG)
  have he : Hagi.Theory.MuonSpectral.fdot (normed G) (Hagi.Theory.MuonAlignment.ns_iter k (normed G))
      = (1 / Real.sqrt (frobSq G)) * Hagi.Theory.MuonSpectral.fdot G (muonStep G k) :=
    fdot_smul_left G _ _
  rw [he] at h1
  have hu := mul_le_mul_of_nonneg_left h1 hs.le
  have hd : Real.sqrt (frobSq G) * (1 / Real.sqrt (frobSq G)) = 1 := by
    field_simp
  rw [← mul_assoc, hd, one_mul, mul_one] at hu
  exact hu

/-- **(S1) `normed_near_optimal`**: T3 (C674) на нормированном градиенте
без гипотезы `σ ≤ 1`. -/
theorem normed_near_optimal [Nonempty n] {G : Matrix n n ℝ} (hG : G ≠ 0) :
    39 / 40 * ∑ i ∈ Hagi.Theory.MuonAlignment.kept (normed G),
        Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues (normed G) i
      ≤ Hagi.Theory.MuonSpectral.fdot (normed G) (muonStep G 3) :=
  Hagi.Theory.MuonAlignment.muon_near_optimal (normed G) (normed_sigma_le_one hG)

/-- **(S2) `useful_of_neg_fderiv`**: `f` дифференцируема в `x`, дифференциал
в направлении `d` отрицателен ⇒ `∃ η > 0, f (x + η•d) < f x`. -/
theorem useful_of_neg_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x d : E} {φ : E →L[ℝ] ℝ} (hL : HasFDerivAt f φ x) (h : φ d < 0) :
    ∃ η : ℝ, 0 < η ∧ f (x + η • d) < f x := by
  refine Hagi.Theory.FunctionPreservingGrowth.useful_step_of_fderiv f x d (-φ d)
    hL.differentiableAt (neg_pos.mpr h) ?_
  rw [hL.fderiv]
  ring

/-- **(S2) `muon_step_useful`** — сертификат спуска Muon-шага: если `f`
дифференцируема в `W` с дифференциалом `φ`, `φ Δ = ⟨g, Δ⟩` (связь с
градиентом — гипотеза; для носителя C669 `g = −batchGrad`), и `g ≠ 0`,
то для малого `η` шаг кода `W ← W − η·X₃` строго убывает `f`. -/
theorem muon_step_useful [Nonempty n] (G W : Matrix n n ℝ) (f : Matrix n n ℝ → ℝ)
    (φ : Matrix n n ℝ →L[ℝ] ℝ) (hL : HasFDerivAt f φ W)
    (hφ : ∀ Δ, φ Δ = Hagi.Theory.MuonSpectral.fdot G Δ) (hG : G ≠ 0) (k : ℕ) :
    ∃ η : ℝ, 0 < η ∧ f (W - η • muonStep G k) < f W := by
  have h1 := (muon_step_inner_ge_frob hG k).2
  have hpos : 0 < Hagi.Theory.MuonSpectral.fdot G (muonStep G k) :=
    lt_of_lt_of_le (Real.sqrt_pos.2 (frobSq_pos hG)) h1
  have hneg : φ (-(muonStep G k)) < 0 := by
    have hm : φ (-(muonStep G k)) = -φ (muonStep G k) := map_neg φ _
    rw [hm, hφ (muonStep G k)]
    linarith
  obtain ⟨η, hη, hlt⟩ := useful_of_neg_fderiv hL hneg
  refine ⟨η, hη, ?_⟩
  have heq : W + η • (-(muonStep G k)) = W - η • muonStep G k := by
    rw [smul_neg, sub_eq_add_neg]
  rwa [heq] at hlt

/-- **(S3) `muon_vs_sign_first_order`**: first-order спуск обоих шагов не
меньше `‖G‖_F`: Muon — `⟨G, ns_iter k Ĝ⟩ ≥ ‖G‖_F`; sign —
`⟨G, sign G⟩ = Σ|G i j| ≥ ‖G‖_F`. -/
theorem muon_vs_sign_first_order [Nonempty n] {G : Matrix n n ℝ} (hG : G ≠ 0) (k : ℕ) :
    Real.sqrt (frobSq G) ≤ Hagi.Theory.MuonSpectral.fdot G (muonStep G k) ∧
      Real.sqrt (frobSq G) ≤ Hagi.Theory.MuonSpectral.fdot G (sgn G) := by
  refine ⟨(muon_step_inner_ge_frob hG k).2, ?_⟩
  have habs : frobSq G = ∑ q : n × n, (|G q.1 q.2| ^ 2) := by
    simp [frobSq, Fintype.sum_prod_type]
  have hsq : frobSq G ≤ (∑ q : n × n, (|G q.1 q.2|)) ^ 2 := by
    rw [habs, sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [sq]
    exact Finset.single_le_sum (s := Finset.univ) (a := a)
      (f := fun b => |G a.1 a.2| * |G b.1 b.2|)
      (fun b _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ a)
  have h4 : Real.sqrt (frobSq G) ≤ ∑ q : n × n, (|G q.1 q.2|) := by
    have hn : 0 ≤ ∑ q : n × n, (|G q.1 q.2|) :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact (Real.sqrt_le_iff).2 ⟨hn, hsq⟩
  apply le_trans h4
  simp only [Hagi.Theory.MuonSpectral.fdot, sgn, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases h : 0 < G i j
  · simp [h, abs_of_pos h]
  · by_cases h' : G i j < 0
    · simp [h, h', abs_of_neg h']
    · have hz : G i j = 0 := le_antisymm (not_lt.mp h) (not_lt.mp h')
      simp [hz]

end Hagi.Theory.MuonDescent
