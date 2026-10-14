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

/-- **Нижняя грань потенциала (R434)**:
ln Z' ≤ −η·ℓ_min — вклад минимизатора
потерь доминирует:
e^{−ηℓ_v} ≤ e^{−ηℓ_min} почленно ⟹
Z' ≤ e^{−ηℓ_min}. Вместе с R433
(верхняя грань): −η·ℓ_min
≤ −ln Z' ≤ 2η·⟨ℓ⟩_w — потенциал
зажат с обеих сторон. -/
theorem mwu_potential_lower {V : Type*} [Fintype V]
    [Nonempty V] (w : V → ℝ) (ℓ : V → ℝ) (η : ℝ)
    (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hη : 0 < η) :
    ∃ vmin : V, Real.log (∑ v, w v * Real.exp (-(η * ℓ v)))
      ≤ -(η * ℓ vmin) := by
  obtain ⟨vmin, hvmin⟩ : ∃ vmin : V, ∀ v : V, ℓ vmin ≤ ℓ v := by
    obtain ⟨a, _, ha⟩ := Finset.exists_min_image (Finset.univ : Finset V) ℓ
      Finset.univ_nonempty
    exact ⟨a, fun v => ha v (Finset.mem_univ v)⟩
  refine ⟨vmin, ?_⟩
  -- per-v: exp(-(η ℓ v)) <= exp(-(η ℓ vmin))
  have hper : ∀ v : V, Real.exp (-(η * ℓ v)) ≤ Real.exp (-(η * ℓ vmin)) := by
    intro v
    apply Real.exp_le_exp.mpr
    have h1 : ℓ vmin ≤ ℓ v := hvmin v
    have h2 : -(η * ℓ v) ≤ -(η * ℓ vmin) := by
      have : η * ℓ vmin ≤ η * ℓ v :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hη)
      linarith
    exact h2
  -- weighted sum bound
  have hsum : ∑ v, w v * Real.exp (-(η * ℓ v))
      ≤ ∑ v, w v * Real.exp (-(η * ℓ vmin)) :=
    Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hper v) (le_of_lt (hw v)))
  -- = exp(...) * sum w = exp(...)
  have hsplit : ∑ v, w v * Real.exp (-(η * ℓ vmin))
      = Real.exp (-(η * ℓ vmin)) * ∑ v, w v := by
    rw [Finset.sum_congr rfl (fun v _ => mul_comm (w v) (Real.exp (-(η * ℓ vmin)))),
      Finset.mul_sum]
  rw [hw1, mul_one] at hsplit
  rw [hsplit] at hsum
  -- log mono
  have hZpos : (0:ℝ) < ∑ v, w v * Real.exp (-(η * ℓ v)) :=
    Finset.sum_pos (fun v _ => mul_pos (hw v) (exp_pos _))
      ⟨vmin, Finset.mem_univ _⟩
  have hlog := Real.log_le_log hZpos hsum
  rwa [Real.log_exp] at hlog

/-- **Сертификат зажатия потенциала
(R435)**: η·ℓ_min ≤ −ln Z' ≤ 2η·⟨ℓ⟩_w —
одна теорема для потребителя
(композиция R434 + R433).
Следствие: ℓ_min ≤ 2⟨ℓ⟩_w —
одношаговая гарантия
без-регретности; многошаговый
телескоп построится на
ней индукцией. -/
theorem mwu_potential_squeeze {V : Type*} [Fintype V]
    [Nonempty V] (w : V → ℝ) (ℓ : V → ℝ) (η : ℝ)
    (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    ∃ vmin : V, η * ℓ vmin
      ≤ -(Real.log (∑ v, w v * Real.exp (-(η * ℓ v))))
      ∧ -(Real.log (∑ v, w v * Real.exp (-(η * ℓ v))))
        ≤ 2 * η * (∑ v, w v * ℓ v) := by
  obtain ⟨vmin, hlow⟩ := mwu_potential_lower w ℓ η hw hw1 hη
  have hhigh := mwu_potential_step w ℓ η hw hw1 hℓ hη hsmall
  refine ⟨vmin, ?_, ?_⟩
  · linarith
  · linarith

/-- **MWU с uniform-стартом (R436)**:
специализация R435 на веса
1/n — классический hedge с
равномерным начальным
распределением над
экспертами V. Кумулятивные
потери ℓ := L (сумма по шагам)
дают телескопический
потенциал: η·L_min ≤ −ln W ≤
2η·⟨L⟩_{unif}. -/
theorem mwu_uniform_squeeze {V : Type*} [Fintype V]
    [Nonempty V] (ℓ : V → ℝ) (η : ℝ)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    ∃ vmin : V, η * ℓ vmin
      ≤ -(Real.log (∑ v : V, (1/(Fintype.card V : ℝ))
          * Real.exp (-(η * ℓ v))))
      ∧ -(Real.log (∑ v : V, (1/(Fintype.card V : ℝ))
          * Real.exp (-(η * ℓ v))))
        ≤ 2 * η * (∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v) := by
  have hw : ∀ v : V, (0:ℝ) < 1/(Fintype.card V : ℝ) := by
    intro v
    apply div_pos (by norm_num)
    exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
  have hw1 : ∑ v : V, (1/(Fintype.card V : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ]
    have hn : (0:ℝ) < (Fintype.card V : ℝ) :=
      Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
    rw [nsmul_eq_mul, one_div, mul_inv_cancel₀ (ne_of_gt hn)]
  exact mwu_potential_squeeze (fun _ => 1/(Fintype.card V : ℝ)) ℓ η hw hw1 hℓ hη hsmall

/-- **Классический ln n-член (R437)**:
−ln W ≤ ln n + η·L_min для uniform-hedge
(W ≥ (1/n)·e^{−ηL_min} через
один член суммы).
Вместе с R436 (верхняя
2η-грань): полная regret-пара
для экспоненциальных
весов: ln n + ηL_min ≥ −ln W ≥ ηL_min —
запас на инициализацию ровно
ln n. -/
theorem mwu_potential_upper_uniform {V : Type*} [Fintype V]
    [Nonempty V] (ℓ : V → ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ vmin : V, -(Real.log (∑ v : V, (1/(Fintype.card V : ℝ))
        * Real.exp (-(η * ℓ v))))
      ≤ Real.log (Fintype.card V : ℝ) + η * ℓ vmin := by
  obtain ⟨vmin, hvmin⟩ : ∃ vmin : V, ∀ v : V, ℓ vmin ≤ ℓ v := by
    obtain ⟨a, _, ha⟩ := Finset.exists_min_image (Finset.univ : Finset V) ℓ
      Finset.univ_nonempty
    exact ⟨a, fun v => ha v (Finset.mem_univ v)⟩
  refine ⟨vmin, ?_⟩
  have hn : (0:ℝ) < (Fintype.card V : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
  have hZpos : (0:ℝ) < ∑ v : V, (1/(Fintype.card V : ℝ))
      * Real.exp (-(η * ℓ v)) :=
    Finset.sum_pos (fun v _ => mul_pos (by positivity) (exp_pos _))
      ⟨vmin, Finset.mem_univ _⟩
  have hsingle : (1/(Fintype.card V : ℝ)) * Real.exp (-(η * ℓ vmin))
      ≤ ∑ v : V, (1/(Fintype.card V : ℝ)) * Real.exp (-(η * ℓ v)) :=
    single_le_sum (f := fun v => (1/(Fintype.card V : ℝ))
      * Real.exp (-(η * ℓ v)))
      (fun v _ => mul_nonneg (by positivity) (exp_pos _).le)
      (Finset.mem_univ vmin)
  have hpos2 : (0:ℝ) < (1/(Fintype.card V : ℝ))
      * Real.exp (-(η * ℓ vmin)) :=
    mul_pos (by positivity) (exp_pos _)
  have hlog := Real.log_le_log hpos2 hsingle
  have hsplit : Real.log ((1/(Fintype.card V : ℝ))
      * Real.exp (-(η * ℓ vmin)))
      = -(Real.log (Fintype.card V : ℝ) + η * ℓ vmin) := by
    have hne1 : (1/(Fintype.card V : ℝ)) ≠ 0 := by positivity
    have hne2 : Real.exp (-(η * ℓ vmin)) ≠ 0 := by positivity
    rw [Real.log_mul hne1 hne2, Real.log_exp,
      Real.log_div (one_ne_zero) (ne_of_gt hn), Real.log_one,
      zero_sub, neg_add_eq_sub]
    ring
  rw [hsplit] at hlog
  linarith

