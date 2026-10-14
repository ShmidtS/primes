import Mathlib

/-!
# MWU — мост к multiplicative weights (R433–)

Одношаговый потенциал-анализ экспоненциальных весов
(hedge-ядро без рядов, RAG-опора: arXiv 2608.09389,
EW-regret ≤ M√(2 ln A·T)). База: R432
(gibbs_energy_gap_crude). Здесь: логарифм
нормировочной константы после одного обновления
весов контролируется потерями:
ln Z' ≥ −2η·⟨ℓ⟩_w при η·ℓ ≤ 1/2.
Ключ: (1+2x)(1−x) ≥ 1 при x ≤ 1/2 ⟹
e^{−2x} ≤ 1−x (без calculus).
-/

open Finset Real

theorem mwu_potential_step {V : Type*} [Fintype V]
    [Nonempty V] (w : V → ℝ) (ℓ : V → ℝ) (η : ℝ)
    (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    Real.log (∑ v, w v * Real.exp (-(η * ℓ v)))
      ≥ -2 * η * (∑ v, w v * ℓ v) := by
  set L : ℝ := ∑ v, w v * ℓ v with hL
  -- per-v: 1 - ηℓ v <= exp(-(η ℓ v))
  have hper : ∀ v : V, 1 - η * ℓ v ≤ Real.exp (-(η * ℓ v)) :=
    fun v => Real.one_sub_le_exp_neg (η * ℓ v)
  -- weighted: sum w (1 - ηℓ) <= Z'
  have hsum1 : ∑ v, w v * (1 - η * ℓ v)
      ≤ ∑ v, w v * Real.exp (-(η * ℓ v)) :=
    Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hper v) (le_of_lt (hw v)))
  -- sum w (1 - ηℓ) = 1 - η L
  have hterm : ∀ v : V, w v * (1 - η * ℓ v)
      = w v - w v * (η * ℓ v) := fun v => by ring
  have hsplit : ∑ v, w v * (1 - η * ℓ v)
      = ∑ v, w v - ∑ v, w v * (η * ℓ v) := by
    rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_sub_distrib]
  have hmul : ∑ v, w v * (η * ℓ v) = η * L := by
    rw [hL, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [hw1] at hsplit
  rw [hsplit, hmul] at hsum1
  -- x := η L in [0, 1/2]
  have hLnn : (0:ℝ) ≤ L :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (le_of_lt (hw v)) (hℓ v))
  have hx : (0:ℝ) ≤ η * L := mul_nonneg (le_of_lt hη) hLnn
  have hxle : η * L ≤ 1/2 := by
    -- η L = Σ w (η ℓ) <= Σ w (1/2) = 1/2
    have hterm2 : ∀ v : V, w v * (η * ℓ v) ≤ w v * (1/2) :=
      fun v => mul_le_mul_of_nonneg_left (hsmall v) (le_of_lt (hw v))
    calc η * L = ∑ v, w v * (η * ℓ v) := hmul.symm
      _ ≤ ∑ v, w v * (1/2) := Finset.sum_le_sum (fun v _ => hterm2 v)
      _ = 1/2 := by
          rw [Finset.sum_congr rfl (fun v _ => mul_comm (w v) ((1:ℝ)/2)),
            ← Finset.mul_sum, hw1, mul_one]
  -- exp(-2x) <= 1 - x for x in [0, 1/2]
  have he2 : Real.exp (-(2*(η*L))) ≤ 1 - η*L := by
    have h1 := Real.add_one_le_exp (2*(η*L))
    have hmul2 : (1 + 2*(η*L)) * (1 - η*L) ≥ 1 := by
      have hxs : (η*L)^2 ≤ (η*L)/2 := by nlinarith [hxle, hx]
      nlinarith [hxs, hx]
    rw [Real.exp_neg]
    exact (inv_le_iff_one_le_mul₀ (exp_pos (2*(η*L)))).mpr
      (by nlinarith [h1, hmul2,
        mul_nonneg (exp_pos (2*(η*L))).le (show (0:ℝ) ≤ 1 - η*L by linarith)])
  -- log chain
  have hlog := Real.log_le_log (exp_pos (-(2*(η*L)))) (le_trans he2 hsum1)
  rw [Real.log_exp] at hlog
  linarith

