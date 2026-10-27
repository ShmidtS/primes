import Hagi.Autonomy.Hedge

/-!
# HedgeSurvivor — склейка (a) аудита v5

Вывод посылки выживания `hsurv` из САМИХ hedge_step +
hedge_telescope: строится экспоненциально-взвешенный процесс
(веса w, потенциал W, нормированные p), шаг связывается с
hedge_step, произведение — с монотонностью exp, и получается
`(1/K)·exp(-η·L*) ≤ exp(-η·A + T·η²/2)`.
-/

namespace Hagi.Autonomy

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- Веса экспоненциальных весов: w 0 = 1, мультипликативное
обновление. -/
noncomputable def ewWeight (l : ℕ → ι → ℝ) (eta : ℝ) :
    ℕ → ι → ℝ
  | 0, _ => 1
  | t + 1, i => ewWeight l eta t i * Real.exp (-eta * l t i)

/-- Потенциал (суммарная масса весов). -/
noncomputable def ewPot (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) : ℝ :=
  ∑ i, ewWeight l eta t i

/-- Нормированные веса (распределение алгоритма). -/
noncomputable def ewNorm (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) (i : ι) : ℝ :=
  ewWeight l eta t i / ewPot l eta t

theorem ewWeight_nonneg (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) (i : ι) :
    0 ≤ ewWeight l eta t i := by
  induction t with
  | zero => simp [ewWeight]
  | succ t ih =>
      simp only [ewWeight]
      exact mul_nonneg ih (Real.exp_pos _).le

/-- Явная форма веса: w T i = exp (-η · Σ_{t<T} l t i). -/
theorem ewWeight_exp (l : ℕ → ι → ℝ) (eta : ℝ) (T : ℕ) (i : ι) :
    ewWeight l eta T i
      = Real.exp (-eta * ∑ t ∈ Finset.range T, l t i) := by
  induction T with
  | zero => simp [ewWeight]
  | succ T ih =>
      rw [Finset.sum_range_succ, ewWeight, ih, ← Real.exp_add]
      congr 1
      ring

theorem ewWeight_pos (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) (i : ι) :
    0 < ewWeight l eta t i := by
  rw [ewWeight_exp]
  positivity

theorem ewPot_pos (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) :
    0 < ewPot l eta t := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  unfold ewPot
  exact Finset.sum_pos' (fun i _ => ewWeight_nonneg l eta t i)
    ⟨j, Finset.mem_univ _, ewWeight_pos l eta t j⟩

theorem ewNorm_nonneg (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) (i : ι) :
    0 ≤ ewNorm l eta t i :=
  div_nonneg (ewWeight_nonneg l eta t i) (ewPot_pos l eta t).le

theorem ewNorm_sum (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) :
    ∑ i, ewNorm l eta t i = 1 := by
  have h : (∑ i ∈ Finset.univ, ewWeight l eta t i)
      / ewPot l eta t
      = ∑ i ∈ Finset.univ, ewWeight l eta t i / ewPot l eta t :=
    Finset.sum_div Finset.univ (fun i => ewWeight l eta t i)
      (ewPot l eta t)
  unfold ewNorm at h ⊢
  rw [← h]
  exact div_self (ne_of_gt (ewPot_pos l eta t))

/-- Потенциальный шаг: W(t+1) = W t · Σ p t i exp(-η l t i). -/
theorem ewPot_step (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) :
    ewPot l eta (t + 1)
      = ewPot l eta t
        * ∑ i, ewNorm l eta t i * Real.exp (-eta * l t i) := by
  unfold ewPot ewNorm
  simp only [ewWeight]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hW : ewPot l eta t = ∑ i, ewWeight l eta t i := rfl
  rw [hW]
  have hsum_ne : (∑ i, ewWeight l eta t i) ≠ 0 := by
    have := ewPot_pos l eta t
    rw [hW] at this
    exact ne_of_gt this
  field_simp


/-- ВЕРХНИЙ ТЕЛЕСКОП: W T ≤ card ι · exp (-η·A + T·η²/2),
где A = Σ_t a_t, a_t = Σ_i p t i · l t i — потери алгоритма.
Шаг — hedge_step, переход 1+u ≤ exp u, связка — индукция. -/
theorem ewPot_upper (l : ℕ → ι → ℝ) (eta : ℝ) (T : ℕ)
    (hl : ∀ t < T, ∀ i, 0 ≤ l t i ∧ l t i ≤ 1)
    (heta : 0 ≤ eta ∧ eta ≤ 1) :
    ewPot l eta T ≤ (Fintype.card ι : ℝ)
      * Real.exp (-eta * (∑ t ∈ Finset.range T,
          ∑ i, ewNorm l eta t i * l t i) + T * eta ^ 2 / 2) := by
  have hbase : ewPot l eta 0 = (Fintype.card ι : ℝ) := by
    simp [ewPot, ewWeight]
  induction T with
  | zero => rw [hbase]; simp
  | succ T ih =>
      have hlT : ∀ i, 0 ≤ l T i ∧ l T i ≤ 1 := hl T (by omega)
      have hstep : ewPot l eta (T + 1)
          ≤ ewPot l eta T * (1 - eta * (∑ i, ewNorm l eta T i * l T i)
            + eta ^ 2 / 2) := by
        rw [ewPot_step l eta T]
        exact mul_le_mul_of_nonneg_left
          (hedge_step (ewNorm l eta T) (l T) eta
            (ewNorm_nonneg l eta T) (ewNorm_sum l eta T) hlT heta)
          (ewPot_pos l eta T).le
      -- шаг через hedge_step и 1+u ≤ exp u
      have hexp : (1:ℝ) + (-eta * (∑ i, ewNorm l eta T i * l T i)
          + eta ^ 2 / 2) ≤ Real.exp (-eta * (∑ i, ewNorm l eta T i * l T i)
          + eta ^ 2 / 2) := by
        have := Real.add_one_le_exp (-eta * (∑ i, ewNorm l eta T i * l T i)
          + eta ^ 2 / 2)
        linarith
      have hW := ih (fun t ht => hl t (by omega))
      calc ewPot l eta (T + 1)
          ≤ ewPot l eta T * (1 - eta * (∑ i, ewNorm l eta T i * l T i)
            + eta ^ 2 / 2) := by
              rw [ewPot_step l eta T]
              exact mul_le_mul_of_nonneg_left
                (hedge_step (ewNorm l eta T) (l T) eta
                  (ewNorm_nonneg l eta T) (ewNorm_sum l eta T) hlT heta)
                (ewPot_pos l eta T).le
        _ ≤ ewPot l eta T * Real.exp (-eta * (∑ i, ewNorm l eta T i * l T i)
            + eta ^ 2 / 2) := by
              have hnn : (0:ℝ) ≤ ewPot l eta T := (ewPot_pos l eta T).le
              have hnn1 : (0:ℝ) ≤ Real.exp (-eta * (∑ i, ewNorm l eta T i * l T i)
                + eta ^ 2 / 2) := Real.exp_nonneg _
              have h1 : (1:ℝ) - eta * (∑ i, ewNorm l eta T i * l T i)
                  + eta ^ 2 / 2
                  = 1 + (-eta * (∑ i, ewNorm l eta T i * l T i)
                    + eta ^ 2 / 2) := by ring
              rw [h1]
              exact mul_le_mul_of_nonneg_left hexp hnn
        _ ≤ ((Fintype.card ι : ℝ)
            * Real.exp (-eta * (∑ t ∈ Finset.range T,
              ∑ i, ewNorm l eta t i * l t i) + (T:ℝ) * eta ^ 2 / 2))
            * Real.exp (-eta * (∑ i, ewNorm l eta T i * l T i)
              + eta ^ 2 / 2) := by
              apply mul_le_mul_of_nonneg_right hW
              exact Real.exp_nonneg _
        _ = (Fintype.card ι : ℝ)
            * (Real.exp (-eta * (∑ t ∈ Finset.range T,
              ∑ i, ewNorm l eta t i * l t i) + (T:ℝ) * eta ^ 2 / 2)
              * Real.exp (-eta * (∑ i, ewNorm l eta T i * l T i)
                + eta ^ 2 / 2)) := by ring
        _ = (Fintype.card ι : ℝ)
            * Real.exp ((-eta * (∑ t ∈ Finset.range T,
              ∑ i, ewNorm l eta t i * l t i) + (T:ℝ) * eta ^ 2 / 2)
              + (-eta * (∑ i, ewNorm l eta T i * l T i)
                + eta ^ 2 / 2)) := by rw [← Real.exp_add]
        _ = (Fintype.card ι : ℝ)
            * Real.exp (-eta * (∑ t ∈ Finset.range (T + 1),
              ∑ i, ewNorm l eta t i * l t i)
              + ((T:ℝ) + 1) * eta ^ 2 / 2) := by
              congr 2
              rw [Finset.sum_range_succ]
              ring
        _ = (Fintype.card ι : ℝ)
            * Real.exp (-eta * (∑ t ∈ Finset.range (T + 1),
              ∑ i, ewNorm l eta t i * l t i)
              + ((T + 1 : ℕ) : ℝ) * eta ^ 2 / 2) := by
              congr 2
              push_cast
              ring


/-- НИЖНЯЯ ГРАНИЦА: потенциал доминирует любую экспорту —
W T ≥ exp (-η·L i*). -/
theorem ewPot_lower (l : ℕ → ι → ℝ) (eta : ℝ) (T : ℕ) (i : ι) :
    Real.exp (-eta * ∑ t ∈ Finset.range T, l t i) ≤ ewPot l eta T := by
  have hterm : Real.exp (-eta * ∑ t ∈ Finset.range T, l t i)
      ≤ ewWeight l eta T i :=
    (ewWeight_exp l eta T i).symm ▸ le_refl _
  have hsum : ewWeight l eta T i ≤ ∑ j, ewWeight l eta T j :=
    Finset.single_le_sum (f := fun j => ewWeight l eta T j)
      (fun j _ => ewWeight_nonneg l eta T j) (Finset.mem_univ i)
  exact hterm.trans hsum

/-- СКЛЕЙКА (a) — ПОСЫЛКА ВЫЖИВАНИЯ ВЫВЕДЕНА: для EW-процесса
hsurv из router_regret_bound выполняется С АЛГОРИТМИЧЕСКИМИ
потерями A = Σ_t Σ_i p t i l t i. Больше не гипотеза. -/
theorem hsurv_derived (l : ℕ → ι → ℝ) (eta : ℝ) (T : ℕ) (i : ι)
    (hl : ∀ t < T, ∀ i, 0 ≤ l t i ∧ l t i ≤ 1)
    (heta : 0 ≤ eta ∧ eta ≤ 1) :
    (1:ℝ) / (Fintype.card ι : ℕ)
      * Real.exp (-eta * ∑ t ∈ Finset.range T, l t i)
      ≤ Real.exp (-eta * (∑ t ∈ Finset.range T,
        ∑ i, ewNorm l eta t i * l t i) + ((T:ℝ)) * eta ^ 2 / 2) := by
  have hlow := ewPot_lower l eta T i
  have hhigh := ewPot_upper l eta T hl heta
  -- exp(-η L i) ≤ W T ≤ card · exp(-η A + Tη²/2)
  have hkey : Real.exp (-eta * ∑ t ∈ Finset.range T, l t i)
      ≤ (Fintype.card ι : ℝ)
        * Real.exp (-eta * (∑ t ∈ Finset.range T,
          ∑ i, ewNorm l eta t i * l t i) + T * eta ^ 2 / 2) :=
    hlow.trans hhigh
  have hcardpos : (0:ℝ) < (Fintype.card ι : ℕ) := by
    exact_mod_cast Fintype.card_pos
  rw [div_mul_eq_mul_div, one_mul]
  refine (div_le_iff₀ hcardpos).mpr ?_
  calc Real.exp (-eta * ∑ t ∈ Finset.range T, l t i)
      ≤ (Fintype.card ι : ℝ)
        * Real.exp (-eta * ∑ t ∈ Finset.range T,
          ∑ i, ewNorm l eta t i * l t i + (T:ℝ) * eta ^ 2 / 2) := hkey
    _ = Real.exp (-eta * ∑ t ∈ Finset.range T,
          ∑ i, ewNorm l eta t i * l t i + (T:ℝ) * eta ^ 2 / 2)
        * (Fintype.card ι : ℝ) := by ring

/-- ИТОГ — REGRET СКЛЕЕН: A − L* ≤ ln K/η + ηT/2, где A —
реальные EW-потери. Полная цепочка hedge_step →
hedge_telescope-монотонность → hsurv → router_regret_bound. -/
theorem ew_regret (l : ℕ → ι → ℝ) (eta : ℝ) (T : ℕ) (i : ι)
    (heta : 0 < eta ∧ eta ≤ 1)
    (hl : ∀ t < T, ∀ i, 0 ≤ l t i ∧ l t i ≤ 1) :
    (∑ t ∈ Finset.range T, ∑ i, ewNorm l eta t i * l t i)
      - ∑ t ∈ Finset.range T, l t i
      ≤ Real.log (Fintype.card ι) / eta + eta * T / 2 := by
  have hsurv := hsurv_derived l eta T i hl ⟨heta.1.le, heta.2⟩
  exact router_regret_bound (Fintype.card ι) T eta
    (∑ t ∈ Finset.range T, ∑ i, ewNorm l eta t i * l t i)
    (∑ t ∈ Finset.range T, l t i)
    (Fintype.card_pos) heta.1 hsurv

end Hagi.Autonomy

