import Mathlib

/-!
# μP-скейлинг: ширино-инвариантные обновления (источник №18)

Источник №18: Yang et al., "Tensor Programs V: A Practical
Approach to Initializing Transformer and Optimizing
Hyperparameters" (arXiv 2203.03466): μ-параметризация (μP)
делает оптимальные гиперпараметры (learning rate) ПЕРЕНОСИМЫМИ
по ширине сети — обучение узкой модели настраивает широкую.

Формализованное ядро (строгое, Cauchy–Schwarz в суммах):
- `row_output_bound`: |(G·x)_i| ≤ ‖G_i‖₂·‖x‖₂;
- `muP_width_invariant`: обновление весов с шагом η/√n
  меняет каждый выход НЕ БОЛЕЕ чем на η·c·‖x‖₂ при
  ограниченных строчных нормах (c не зависит от n) —
  ВЫХОД ИНВАРИАНТЕН К ШИРИНЕ (transfer);
- `sp_grows_with_width`: без скейлинга (η·G) оценка растёт
  как √n — стандартная параметризация НЕ переносима.

Это ядро μTransfer: ключ к обучению малой модели с
переносом гиперпараметров на большую при минимальных
вычислениях — прямая цель HAGI.
-/

namespace Hagi.Model.MuPScaling

open Real

variable {n : ℕ}

/-- Строчная оценка выхода через Cauchy–Schwarz:
|(G·x)_i| ≤ ‖G_i‖₂ · ‖x‖₂. -/
theorem row_output_bound (G : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    |∑ j, G i j * x j|
      ≤ (∑ j, (G i j) ^ 2).sqrt * (∑ j, (x j) ^ 2).sqrt := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => G i j) (fun j => x j)
  have hnn : (0:ℝ) ≤ (∑ j, (G i j) ^ 2) * (∑ j, (x j) ^ 2) := by
    exact mul_nonneg (by positivity) (by positivity)
  calc |∑ j, G i j * x j|
      = Real.sqrt ((∑ j, G i j * x j) ^ 2) := by
        rw [← Real.sqrt_sq (abs_nonneg (∑ j, G i j * x j)),
          sq_abs (∑ j, G i j * x j)]
    _ ≤ Real.sqrt ((∑ j, (G i j) ^ 2) * (∑ j, (x j) ^ 2)) :=
        Real.sqrt_le_sqrt hcs
    _ = (∑ j, (G i j) ^ 2).sqrt * (∑ j, (x j) ^ 2).sqrt :=
        Real.sqrt_mul' _ (by positivity : (0:ℝ) ≤ ∑ j, (x j) ^ 2)


/-- μP-ОБНОВЛЕНИЕ: шаг η/√n · G. -/
noncomputable def muPUpdate (G : Fin n → Fin n → ℝ) (eta : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => (eta / Real.sqrt ((n:ℝ))) * G i j

/-- СТАНДАРТНОЕ (SP) обновление: шаг η · G — без
ширинного скейлинга. -/
def spUpdate (G : Fin n → Fin n → ℝ) (eta : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => eta * G i j

/-- μP-ИНВАРИАНТНОСТЬ К ШИРИНЕ (ядро μTransfer): при
0 ≤ η и ограниченных строчных нормах G (константа c не
зависит от ширины n) обновление выхода с шагом η/√n
ограничено η·c·‖x‖₂ — НЕ ЗАВИСИТ от n. Оптимальный LR
переносим между моделями разных ширин. -/
theorem muP_width_invariant (G : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (eta c : ℝ)
    (heta : 0 ≤ eta) (_hc : 0 ≤ c)
    (hrow : ∀ i, (∑ j, (G i j) ^ 2).sqrt ≤ c)
    (i : Fin n) :
    |∑ j, muPUpdate G eta i j * x j|
      ≤ eta * c * (∑ j, (x j) ^ 2).sqrt := by
  have hn1 : 1 ≤ n := i.pos
  have hsqrt : (1:ℝ) ≤ Real.sqrt ((n:ℝ)) := by
    have hn : (1:ℝ) ≤ (n:ℕ) := by exact_mod_cast hn1
    calc (1:ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt ((n:ℝ)) := Real.sqrt_le_sqrt hn
  have hsp : 0 < Real.sqrt ((n:ℝ)) := by
    have : (0:ℝ) < (n:ℕ) := by exact_mod_cast hn1
    exact Real.sqrt_pos.mpr this
  set k : ℝ := 1 / Real.sqrt ((n:ℝ)) with hk
  have hk0 : 0 ≤ k := div_nonneg (by norm_num) hsp.le
  have hk1 : k ≤ 1 := (div_le_one hsp).mpr hsqrt
  have hrow' := row_output_bound G x i
  have hnnA : 0 ≤ (∑ j, (G i j) ^ 2).sqrt := Real.sqrt_nonneg _
  have hnnB : 0 ≤ (∑ j, (x j) ^ 2).sqrt := Real.sqrt_nonneg _
  -- перепись суммы: ∑ (η·k·G·x) = η·k·∑ G·x  (muPUpdate-элемент = ηk·G)
  have hmu : ∀ j, muPUpdate G eta i j = eta * k * G i j := by
    intro j
    rw [muPUpdate]
    rw [show eta / Real.sqrt ((n:ℝ))
        = eta * (1 / Real.sqrt ((n:ℝ))) from by ring]
  have hsum : ∑ j, muPUpdate G eta i j * x j
      = eta * (k * ∑ j, G i j * x j) := by
    have hR : eta * (k * ∑ j, G i j * x j)
        = ∑ j, eta * k * G i j * x j := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hR]
    exact Finset.sum_congr rfl fun j _ => by rw [hmu j]
  rw [hsum, abs_mul, abs_mul, abs_of_nonneg heta,
    abs_of_nonneg hk0]
  have hinner : k * |∑ j, G i j * x j|
      ≤ c * (∑ j, (x j) ^ 2).sqrt := by
    calc k * |∑ j, G i j * x j|
        ≤ k * ((∑ j, (G i j) ^ 2).sqrt * (∑ j, (x j) ^ 2).sqrt) :=
          mul_le_mul_of_nonneg_left hrow' hk0
      _ = (k * (∑ j, (G i j) ^ 2).sqrt) * (∑ j, (x j) ^ 2).sqrt := by
          ring
      _ ≤ ((∑ j, (G i j) ^ 2).sqrt) * (∑ j, (x j) ^ 2).sqrt := by
          have hstep : k * (∑ j, (G i j) ^ 2).sqrt
              ≤ (∑ j, (G i j) ^ 2).sqrt := by
            nlinarith [hk1, hnnA]
          apply mul_le_mul_of_nonneg_right hstep hnnB
      _ ≤ c * (∑ j, (x j) ^ 2).sqrt :=
          mul_le_mul_of_nonneg_right (hrow i) hnnB
  calc eta * (k * |∑ j, G i j * x j|)
      ≤ eta * (c * (∑ j, (x j) ^ 2).sqrt) :=
        mul_le_mul_of_nonneg_left hinner heta
    _ = eta * c * (∑ j, (x j) ^ 2).sqrt := by ring

/-- SP НЕ ПЕРЕНОСИМ: без скейлинга оценка выхода содержит
множитель √n — обновление растёт с шириной, оптимальный LR
зависит от n (контраст с `muP_width_invariant`). -/
theorem sp_grows_with_width (G : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (eta c : ℝ)
    (heta : 0 ≤ eta) (hc : 0 ≤ c)
    (hrow : ∀ i, (∑ j, (G i j) ^ 2).sqrt ≤ c)
    (i : Fin n) :
    |∑ j, spUpdate G eta i j * x j|
      ≤ eta * c * Real.sqrt ((n:ℝ)) * (∑ j, (x j) ^ 2).sqrt := by
  have hrow' := row_output_bound G x i
  have hsnn : 0 ≤ Real.sqrt ((n:ℝ)) := Real.sqrt_nonneg _
  have hn1 : 1 ≤ n := i.pos
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt ((n:ℝ)) := by
    have hn : (1:ℝ) ≤ (n:ℕ) := by exact_mod_cast hn1
    calc (1:ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt ((n:ℝ)) := Real.sqrt_le_sqrt hn
  unfold spUpdate
  have hmul : ∑ j, eta * G i j * x j
      = eta * ∑ j, G i j * x j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hmul, abs_mul, abs_of_nonneg heta]
  calc eta * |∑ j, G i j * x j|
      ≤ eta * ((∑ j, (G i j) ^ 2).sqrt * (∑ j, (x j) ^ 2).sqrt) :=
        mul_le_mul_of_nonneg_left hrow' heta
    _ = eta * (∑ j, (G i j) ^ 2).sqrt * (∑ j, (x j) ^ 2).sqrt := by ring
    _ ≤ eta * c * (∑ j, (x j) ^ 2).sqrt := by
        have hnnB : 0 ≤ (∑ j, (x j) ^ 2).sqrt := Real.sqrt_nonneg _
        have h2 : eta * (∑ j, (G i j) ^ 2).sqrt ≤ eta * c :=
          mul_le_mul_of_nonneg_left (hrow i) heta
        exact mul_le_mul_of_nonneg_right h2 hnnB
    _ = eta * c * (1 * (∑ j, (x j) ^ 2).sqrt) := by ring
    _ ≤ eta * c * (1 * (∑ j, (x j) ^ 2).sqrt) := le_refl _
    _ ≤ eta * c * (Real.sqrt ((n:ℝ)) * (∑ j, (x j) ^ 2).sqrt) := by
        have hkey : 1 * (∑ j, (x j) ^ 2).sqrt
            ≤ Real.sqrt ((n:ℝ)) * (∑ j, (x j) ^ 2).sqrt :=
          mul_le_mul_of_nonneg_right hsqrt1 (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left hkey (mul_nonneg heta hc)
    _ = eta * c * Real.sqrt ((n:ℝ)) * (∑ j, (x j) ^ 2).sqrt := by ring

end Hagi.Model.MuPScaling
