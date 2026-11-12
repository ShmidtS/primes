import Hagi.Autonomy.Hedge
import Hagi.Optimization.MirrorDescent

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


/-- АНТИ-ЛОК-ИН: при неотрицательных потерях и η ≥ 0
нормированный вес ЛЮБОГО ключа после T шагов удовлетворяет
экспоненциальной нижней оценке выживания
`ewNorm ≥ (1/K)·exp(−η·Σ_{t<T} ℓ t i)`. Вес может убывать не
быстрее, чем экспоненциально по собственной накопленной потере —
он никогда не ноль: роутер не может навсегда shut out ключ с
ограниченными потерями. (Обёртка над `ewWeight_exp`; посылки
слабее, чем у `hsurv_derived` — только ℓ ≥ 0, регрет-сторона при
этом НЕ утверждается.) -/
theorem ewNorm_survivor_lower (l : ℕ → ι → ℝ) (eta : ℝ) (T : ℕ) (i : ι)
    (heta : 0 ≤ eta) (hl : ∀ t, ∀ j, 0 ≤ l t j) :
    (1 / (Fintype.card ι : ℝ))
      * Real.exp (-eta * ∑ t ∈ Finset.range T, l t i)
      ≤ ewNorm l eta T i := by
  have hwle1 : ∀ j, ewWeight l eta T j ≤ 1 := by
    intro j
    rw [ewWeight_exp]
    have hL : 0 ≤ ∑ t ∈ Finset.range T, l t j :=
      Finset.sum_nonneg fun t _ => hl t j
    calc Real.exp (-eta * ∑ t ∈ Finset.range T, l t j)
        ≤ Real.exp (0:ℝ) := (Real.exp_le_exp).2 (by nlinarith [mul_nonneg heta hL])
      _ = 1 := Real.exp_zero
  have hWpos : 0 < ewPot l eta T := ewPot_pos l eta T
  have hcardpos : (0:ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hEpos : 0 < Real.exp (-eta * ∑ t ∈ Finset.range T, l t i) :=
    Real.exp_pos _
  have hW : ewPot l eta T ≤ (Fintype.card ι : ℝ) := by
    calc ewPot l eta T = ∑ j, ewWeight l eta T j := rfl
      _ ≤ ∑ j : ι, (1:ℝ) := Finset.sum_le_sum fun j _ => hwle1 j
      _ = (Fintype.card ι : ℝ) := by simp
  have hone : (1:ℝ) / (Fintype.card ι : ℝ) ≤ 1 / ewPot l eta T := by
    rw [le_div_iff₀ hWpos, div_mul_eq_mul_div, div_le_one]
    · rw [one_mul]; exact hW
    · exact_mod_cast Fintype.card_pos
  calc (1 / (Fintype.card ι : ℝ))
      * Real.exp (-eta * ∑ t ∈ Finset.range T, l t i)
      ≤ (1 / ewPot l eta T)
        * Real.exp (-eta * ∑ t ∈ Finset.range T, l t i) :=
        mul_le_mul_of_nonneg_right hone hEpos.le
    _ = ewNorm l eta T i := by
        unfold ewNorm
        rw [ewWeight_exp, div_mul_eq_mul_div, one_mul]

open Hagi.Optimization

variable {ι : Type} [Fintype ι] [Nonempty ι]

theorem ewNorm_as_mirror (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) (i : ι) :
    ewNorm l eta t i
      = mirrorStep (fun _ => (1:ℝ))
          (fun j => ∑ s ∈ Finset.range t, l s j) (1 / eta) i := by
  unfold ewNorm mirrorStep
  have hw : ∀ j, ewWeight l eta t j
      = (1:ℝ) * Real.exp (-((∑ s ∈ Finset.range t, l s j)) / (1/eta)) := by
    intro j
    rw [ewWeight_exp]
    field_simp
  have hWpot : ewPot l eta t
      = ∑ x, (1:ℝ) * Real.exp (-((∑ s ∈ Finset.range t, l s x)) / (1/eta)) :=
    Finset.sum_congr rfl (fun x _ => hw x)
  rw [hw i, hWpot]

end Hagi.Autonomy
