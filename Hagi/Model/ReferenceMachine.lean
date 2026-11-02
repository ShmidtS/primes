import Hagi.Model.StageSemantics
import Hagi.Energy.Quantizer

/-!
# Эталонный исполнитель цикла обучения (аудит v7 §5 + этап 6)

Ответ на разрыв «доказательства не связаны с операциями над
весами» (joint менял params, но не weights; compress не
квантовал): носитель, в котором операции ДЕЙСТВИТЕЛЬНО
вычисляют веса, а ВСЕ измерения — функции весов.

Модель: квадратичная энергия E(w) = ‖w − a‖²₂/2 на Fin n → ℝ
(евклидова структура через Finset-суммы, Cauchy–Schwarz).

- `jointStep` — РЕАЛЬНЫЙ градиентный шаг над весами;
- `compressQ` — РЕАЛЬНОЕ квантование (решётка Δ·round);
- `jointStep_energy`: вычисленная энергия = (1−η)²·E(w);
- `jointStep_energy_decrease`: при 0<η<2 строгое снижение
  без единого постулата;
- `machine_quant_err_bound`: вычисленная ошибка ≤ √n·Δ/2;
- `machine_energy_bound`: полная оценка цикла (шаг+квантование)
  через Cauchy–Schwarz; все величины вычислены из весов.

Это «ref.Machine»-слой в смысле qwenputer: эталонная
семантика, с которой сравнивается формальная модель.
-/

namespace Hagi.Model.ReferenceMachine

open Real

variable {n : ℕ}

/-- Квадратичная энергия как функция весов: E = Σ(wᵢ−aᵢ)²/2. -/
noncomputable def energy (a w : Fin n → ℝ) : ℝ := ∑ i, (w i - a i) ^ 2 / 2

/-- Градиент как функция весов: ∇E = w − a. -/
def grad (a w : Fin n → ℝ) : Fin n → ℝ := fun i => w i - a i

/-- РЕАЛЬНЫЙ градиентный шаг: w' = w − η∇E(w). -/
def jointStep (a w : Fin n → ℝ) (eta : ℝ) : Fin n → ℝ :=
  fun i => w i - eta * (w i - a i)

/-- РЕАЛЬНОЕ квантование весов на решётку Δ·ℤ. -/
noncomputable def compressQ (Delta : ℝ) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Delta * round (w i / Delta)

/-- Полный машинный цикл: joint-шаг, затем квантование. -/
noncomputable def machineStep (a w : Fin n → ℝ) (eta Delta : ℝ) :
    Fin n → ℝ := compressQ Delta (jointStep a w eta)

/-- Вычисленная ошибка квантования: √Σ(Q(w)ᵢ−wᵢ)². -/
noncomputable def quantErr (Delta : ℝ) (w : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (compressQ Delta w i - w i) ^ 2)

/-- Зазор как измерение: вычислен из весов. -/
noncomputable def machineGap (a w : Fin n → ℝ) (eta : ℝ) : ℝ :=
  energy a w - energy a (jointStep a w eta)

/-! ### Измеренные законы эталонной машины — без постулатов -/

/-- Градиентный шаг сжимает остаток: энергия = (1−η)²·E(w). -/
theorem jointStep_energy (a w : Fin n → ℝ) (eta : ℝ) :
    energy a (jointStep a w eta) = (1 - eta) ^ 2 * energy a w := by
  unfold energy jointStep
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (w i - eta * (w i - a i)) - a i
      = (1 - eta) * (w i - a i) := by ring
  rw [h]
  ring

/-- При 0 < η < 2 вычисленная энергия СТРОГО убывает на
активном шаге (w ≠ a): без единого постулата. -/
theorem jointStep_energy_decrease (a w : Fin n → ℝ) (eta : ℝ)
    (heta : 0 < eta) (heta2 : eta < 2) (hne : a ≠ w) :
    energy a (jointStep a w eta) < energy a w := by
  rw [jointStep_energy]
  have hpos : 0 < energy a w := by
    unfold energy
    have hex : ∃ i, w i - a i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (funext fun i => by
        have := hc i
        linarith [sub_eq_zero.mp (hc i)])
    obtain ⟨i, hi⟩ := hex
    exact Finset.sum_pos' (fun j _ => by positivity)
      ⟨i, Finset.mem_univ i, by positivity⟩
  have hsq : (1 - eta) ^ 2 < 1 := by
    have h1 : -1 < 1 - eta := by linarith
    have h2 : 1 - eta < 1 := by linarith
    nlinarith [h1, h2, sq_nonneg (1 - eta)]
  nlinarith [hpos]

/-- Вычисленная ошибка квантования ≤ √n·Δ/2 (Δ>0):
per-coordinate |round err| ≤ 1/2, затем sqrt-монотонность. -/
theorem machine_quant_err_bound (Delta : ℝ) (hD : 0 < Delta)
    (w : Fin n → ℝ) :
    quantErr Delta w ≤ Real.sqrt ((n : ℝ)) * Delta / 2 := by
  have hper : ∀ i, (compressQ Delta w i - w i) ^ 2 ≤ (Delta / 2) ^ 2 := by
    intro i
    have h1 : compressQ Delta w i - w i
        = Delta * (round (w i / Delta) - w i / Delta) := by
      unfold compressQ
      field_simp
    have h2 : |Delta * (round (w i / Delta) - w i / Delta)|
        ≤ Delta / 2 := by
      have hr : |round (w i / Delta) - w i / Delta| ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      rw [abs_mul, abs_of_pos hD]
      exact (mul_le_mul_of_nonneg_left hr hD.le).trans
        (le_of_eq (by ring : Delta * ((1:ℝ)/2) = Delta / 2))
    have h12 : |compressQ Delta w i - w i| ≤ Delta / 2 := by
      rw [h1]
      exact h2
    calc (compressQ Delta w i - w i) ^ 2
        = |compressQ Delta w i - w i| * |compressQ Delta w i - w i| := by
          rw [← sq_abs, sq]
      _ ≤ Delta / 2 * (Delta / 2) :=
            mul_self_le_mul_self (abs_nonneg _) h12
      _ = (Delta / 2) ^ 2 := by ring
  have hsum : ∑ i, (compressQ Delta w i - w i) ^ 2
      ≤ ((n : ℝ)) * (Delta / 2) ^ 2 := by
    calc ∑ i, (compressQ Delta w i - w i) ^ 2
        ≤ ∑ i, (Delta / 2) ^ 2 := Finset.sum_le_sum fun i _ => hper i
      _ = ((n : ℝ)) * (Delta / 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          exact nsmul_eq_mul n ((Delta / 2) ^ 2)
  have hRHS : Real.sqrt ((n : ℝ)) * Delta / 2
      = Real.sqrt (((n : ℝ)) * (Delta / 2) ^ 2) := by
    have h1 : Real.sqrt (((n : ℝ)) * (Delta / 2) ^ 2)
        = Real.sqrt ((n : ℝ)) * Real.sqrt ((Delta / 2) ^ 2) :=
      Real.sqrt_mul' ((n : ℝ))
        (show (0:ℝ) ≤ (Delta / 2) ^ 2 by positivity)
    rw [h1, Real.sqrt_sq (by positivity : (0:ℝ) ≤ Delta / 2)]
    ring
  unfold quantErr
  rw [hRHS]
  exact Real.sqrt_le_sqrt hsum

/-- Полный машинный цикл: E(шаг+квантование) ограничена
через Cauchy–Schwarz:
E ≤ (√(2E(w))·|1−η| + √n·Δ/2)²/2. Всё вычислено из весов. -/
theorem machine_energy_bound (a w : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) :
    energy a (machineStep a w eta Delta)
      ≤ (Real.sqrt (∑ i, (jointStep a w eta i - a i) ^ 2)
          + Real.sqrt ((n:ℝ)) * Delta / 2) ^ 2 / 2 := by
  set d : Fin n → ℝ := fun i => jointStep a w eta i - a i with hd
  set e : Fin n → ℝ := fun i => compressQ Delta (jointStep a w eta) i
    - jointStep a w eta i with he
  have hsplit : ∀ i, machineStep a w eta Delta i - a i = d i + e i := by
    intro i
    unfold machineStep d e
    ring
  set Sd : ℝ := ∑ i, d i ^ 2 with hSd
  set Se : ℝ := ∑ i, e i ^ 2 with hSe
  -- Se ≤ n·(Δ/2)² (per-coordinate, как в quant_err_bound)
  have hSe_le : Se ≤ ((n:ℝ)) * (Delta / 2) ^ 2 := by
    have hper : ∀ i, e i ^ 2 ≤ (Delta / 2) ^ 2 := by
      intro i
      have h1 : e i = Delta * (round (jointStep a w eta i / Delta)
          - jointStep a w eta i / Delta) := by
        unfold e compressQ
        field_simp
      have h2 : |Delta * (round (jointStep a w eta i / Delta)
          - jointStep a w eta i / Delta)| ≤ Delta / 2 := by
        have hr : |round (jointStep a w eta i / Delta)
            - jointStep a w eta i / Delta| ≤ 1 / 2 := by
          rw [abs_sub_comm]
          exact abs_sub_round _
        rw [abs_mul, abs_of_pos hD]
        exact (mul_le_mul_of_nonneg_left hr hD.le).trans
          (le_of_eq (by ring : Delta * ((1:ℝ)/2) = Delta / 2))
      have habs : |e i| ≤ Delta / 2 := by rw [h1]; exact h2
      calc e i ^ 2 = |e i| * |e i| := by rw [← sq_abs, sq]
        _ ≤ Delta / 2 * (Delta / 2) :=
              mul_self_le_mul_self (abs_nonneg _) habs
        _ = (Delta / 2) ^ 2 := by ring
    calc Se = ∑ i, e i ^ 2 := rfl
      _ ≤ ∑ i, (Delta / 2) ^ 2 := Finset.sum_le_sum fun i _ => hper i
      _ = ((n:ℝ)) * (Delta / 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          exact nsmul_eq_mul n ((Delta / 2) ^ 2)
  -- Sd = (1−η)²·2E(w)
  have hSd : Sd = (1 - eta) ^ 2 * (2 * energy a w) := by
    have hj := jointStep_energy a w eta
    unfold energy at hj
    have hexp : ∑ i, d i ^ 2 = (1 - eta) ^ 2 * ∑ i, (w i - a i) ^ 2 := by
      have hd' : ∀ i, d i = (1 - eta) * (w i - a i) := by
        intro i
        unfold d jointStep
        ring
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd' i]
      ring
    calc Sd = ∑ i, d i ^ 2 := rfl
      _ = (1 - eta) ^ 2 * ∑ i, (w i - a i) ^ 2 := hexp
      _ = (1 - eta) ^ 2 * (2 * ((∑ i, (w i - a i) ^ 2) / 2)) := by ring
      _ = (1 - eta) ^ 2 * (2 * energy a w) := by
          have hEdef : energy a w = ∑ i, (w i - a i) ^ 2 / 2 := rfl
          rw [hEdef, Finset.sum_div]
  -- разложение энергии цикла
  have hE : energy a (machineStep a w eta Delta)
      = (Sd + 2 * ∑ i, d i * e i + Se) / 2 := by
    have hsum : ∑ i, (machineStep a w eta Delta i - a i) ^ 2
        = ∑ i, (d i + e i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hsplit i]
    have hexpand : ∀ i, (d i + e i) ^ 2
        = d i ^ 2 + 2 * d i * e i + e i ^ 2 := fun i => by ring
    have hsplit_sum : ∑ i, (d i + e i) ^ 2
        = ∑ i, (d i ^ 2 + 2 * d i * e i + e i ^ 2) :=
      Finset.sum_congr rfl fun i _ => hexpand i
    have hdistr : ∑ i, (d i ^ 2 + 2 * d i * e i + e i ^ 2)
        = ∑ i, d i ^ 2 + ∑ i, (2 * d i * e i) + ∑ i, e i ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hmul2 : ∑ i, (2 * d i * e i) = 2 * ∑ i, d i * e i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hE1 : ∑ i, (machineStep a w eta Delta i - a i) ^ 2
        = Sd + 2 * ∑ i, d i * e i + Se := by
      rw [hsum, hsplit_sum, hdistr, hmul2]
    unfold energy
    rw [← Finset.sum_div]
    exact congrArg (· / 2) hE1
  -- Cauchy–Schwarz: ∑ d·e ≤ √(Sd·Se)
  have hcs : ∑ i, d i * e i ≤ Real.sqrt (Sd * Se) := by
    have h2 : (∑ i, d i * e i) ^ 2 ≤ Sd * Se :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ d e
    calc ∑ i, d i * e i ≤ |∑ i, d i * e i| := le_abs_self _
      _ = Real.sqrt ((∑ i, d i * e i) ^ 2) := by
          rw [← sq_abs (∑ i, d i * e i)]
          exact (Real.sqrt_sq (abs_nonneg _)).symm
      _ ≤ Real.sqrt (Sd * Se) := Real.sqrt_le_sqrt h2
  -- сборка: 2∑de ≤ 2√(SdSe) ≤ ... цель через (√Sd+√Se)²
  have hSdnn : 0 ≤ Sd := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSenn : 0 ≤ Se := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hse : Real.sqrt Se ≤ Real.sqrt (((n:ℝ)) * (Delta / 2) ^ 2) :=
    Real.sqrt_le_sqrt hSe_le
  have hfinal : Sd + 2 * ∑ i, d i * e i + Se
      ≤ (Real.sqrt Sd + Real.sqrt Se) ^ 2 := by
    have hAM : 2 * ∑ i, d i * e i ≤ 2 * Real.sqrt (Sd * Se) := by
      linarith
    have hsqr : (Real.sqrt Sd + Real.sqrt Se) ^ 2
        = Sd + 2 * Real.sqrt (Sd * Se) + Se := by
      have hA : Real.sqrt Sd * Real.sqrt Sd = Sd := by
        have hh := Real.sq_sqrt (hSdnn)
        rw [sq] at hh
        exact hh
      have hB : Real.sqrt Se * Real.sqrt Se = Se := by
        have hh := Real.sq_sqrt hSenn
        rw [sq] at hh
        exact hh
      have hM : Real.sqrt Sd * Real.sqrt Se = Real.sqrt (Sd * Se) :=
        (Real.sqrt_mul' Sd hSenn).symm
      nlinarith [hA, hB, hM]
    rw [hsqr]
    linarith
  have hmono : (Real.sqrt Sd + Real.sqrt Se) ^ 2
      ≤ (Real.sqrt Sd + Real.sqrt (((n:ℝ)) * (Delta / 2) ^ 2)) ^ 2 := by
    have habs1 : 0 ≤ Real.sqrt Sd + Real.sqrt Se := add_nonneg
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have habs2 : 0 ≤ Real.sqrt Sd + Real.sqrt (((n:ℝ)) * (Delta / 2) ^ 2) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [sq_le_sq, abs_of_nonneg habs1, abs_of_nonneg habs2]
    gcongr
  have hRHS : (Real.sqrt (∑ i, (jointStep a w eta i - a i) ^ 2)
      + Real.sqrt ((n:ℝ)) * Delta / 2) ^ 2 / 2
      = (Real.sqrt Sd + Real.sqrt (((n:ℝ)) * (Delta / 2) ^ 2)) ^ 2 / 2 := by
    have hSddef : Sd = ∑ i, (jointStep a w eta i - a i) ^ 2 := rfl
    have hnD : Real.sqrt (((n:ℝ)) * (Delta / 2) ^ 2)
        = Real.sqrt ((n:ℝ)) * (Delta / 2) := by
      rw [Real.sqrt_mul' ((n:ℝ))
        (show (0:ℝ) ≤ (Delta / 2) ^ 2 by positivity),
        Real.sqrt_sq (show (0:ℝ) ≤ Delta / 2 by positivity)]
    rw [hSddef, hnD]
    ring
  rw [hE, hRHS]
  linarith [hfinal, hmono]

/-- Энергия на евклидовом носителе. -/
noncomputable def energyE (a w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, (w.ofLp i - a.ofLp i) ^ 2 / 2

/-- Разложение разности энергий: E(y) − E(x) =
⟨x−a, y−x⟩ + ‖y−x‖²/2 — точное координатное
тождество. -/
theorem energy_diff_expansion (a x y : EuclideanSpace ℝ (Fin n)) :
    energyE a y - energyE a x
      = (inner ℝ (x - a) (y - x))
        + ‖y - x‖ ^ 2 / 2 := by
  have hexpand : energyE a y - energyE a x
      = ∑ i, ((y.ofLp i - a.ofLp i) ^ 2
        - (x.ofLp i - a.ofLp i) ^ 2) / 2 := by
    unfold energyE
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hper : ∀ i, ((y.ofLp i - a.ofLp i) ^ 2
      - (x.ofLp i - a.ofLp i) ^ 2) / 2
      = (y.ofLp i - x.ofLp i) * (x.ofLp i - a.ofLp i)
        + (y.ofLp i - x.ofLp i) ^ 2 / 2 := by
    intro i
    have h1 : (y.ofLp i - a.ofLp i) ^ 2
        = ((x.ofLp i - a.ofLp i) + (y.ofLp i - x.ofLp i)) ^ 2 := by
      congr 1; ring
    rw [h1]; ring
  have hinner : (inner ℝ (x - a) (y - x))
      = ∑ i, (x.ofLp i - a.ofLp i) * (y.ofLp i - x.ofLp i) := by
    simp only [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hnorm : ‖y - x‖ ^ 2 = ∑ i, (y.ofLp i - x.ofLp i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp
  rw [hexpand, hinner, hnorm]
  simp only [hper, Finset.sum_add_distrib, Finset.sum_div]
  congr 1

/-- Квантование на евклидовом носителе (координатное). -/
noncomputable def compressQE (Delta : ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => Delta * round (w.ofLp i / Delta))

/-- Координаты compressQE. -/
theorem compressQE_ofLp (Delta : ℝ) (w : EuclideanSpace ℝ (Fin n))
    (i : Fin n) :
    (compressQE Delta w).ofLp i = Delta * round (w.ofLp i / Delta) := rfl

/-- Норма ошибки координатного квантования = √(Σ ошибок²). -/
theorem distQE (Delta : ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    ‖compressQE Delta w - w‖ ^ 2
      = ∑ i, (Delta * round (w.ofLp i / Delta) - w.ofLp i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, compressQE_ofLp]

/-- ЛЕДЖЕР СЖАТИЯ В n: превышение энергии после квантования
не больше (‖x−a‖ + q/2)·q, где q = ‖Q(x)−x‖ — вычисленная
ошибка квантования. Через energy_diff_expansion и
Коши–Буняковского; ни одного постулата. -/
theorem compress_energy_ledger
    (a x : EuclideanSpace ℝ (Fin n)) (Delta : ℝ) :
    energyE a (compressQE Delta x) - energyE a x
      ≤ (‖x - a‖ + ‖compressQE Delta x - x‖ / 2)
        * ‖compressQE Delta x - x‖ := by
  have hexp := energy_diff_expansion a x (compressQE Delta x)
  have habs : |(inner ℝ (x - a) (compressQE Delta x - x))|
      ≤ ‖x - a‖ * ‖compressQE Delta x - x‖ :=
    abs_real_inner_le_norm (x - a) (compressQE Delta x - x)
  have hle1 : (inner ℝ (x - a) (compressQE Delta x - x))
      ≤ ‖x - a‖ * ‖compressQE Delta x - x‖ :=
    le_trans (le_abs_self _) habs
  set q := ‖compressQE Delta x - x‖ with hq
  have hcalc : energyE a (compressQE Delta x) - energyE a x
      = (inner ℝ (x - a) (compressQE Delta x - x)) + q ^ 2 / 2 := by
    rw [hexp, hq]
  calc energyE a (compressQE Delta x) - energyE a x
      = (inner ℝ (x - a) (compressQE Delta x - x)) + q ^ 2 / 2 := hcalc
    _ ≤ ‖x - a‖ * q + q * q / 2 := by
        have h2 : q ^ 2 / 2 = q * q / 2 := by ring
        rw [h2]
        gcongr
    _ = (‖x - a‖ + q / 2) * q := by
        field_simp

/-- Градиентный шаг на евклидовом носителе. -/
def jointStepE (a w : EuclideanSpace ℝ (Fin n)) (eta : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  w - eta • (w - a)

/-- Координаты градиентного шага. -/
theorem jointStepE_ofLp (a w : EuclideanSpace ℝ (Fin n)) (eta : ℝ)
    (i : Fin n) :
    (jointStepE a w eta).ofLp i
      = w.ofLp i - eta * (w.ofLp i - a.ofLp i) := by
  simp [jointStepE]

/-- Градиент E на евклидовом носителе: w − a. -/
def jointGradE (a w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := w - a

/-- Энергия шага: (1−η)²·E(w) — вычислено. -/
theorem jointStepE_energy (a w : EuclideanSpace ℝ (Fin n)) (eta : ℝ) :
    energyE a (jointStepE a w eta) = (1 - eta) ^ 2 * energyE a w := by
  unfold energyE
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [jointStepE_ofLp]
  have h : (w.ofLp i - eta * (w.ofLp i - a.ofLp i)) - a.ofLp i
      = (1 - eta) * (w.ofLp i - a.ofLp i) := by ring
  rw [h]
  ring


/-- ШУМОВОЙ ПОЛ ЭТАЛОННОЙ МАШИНЫ: один полный шаг сжатия
(eta = 1: градиентный шаг до якоря, затем квантование с
сеткой Delta) опускает энергию до n*Delta^2/8 НЕЗАВИСИМО от
текущей энергии — corollary machine_energy_bound при Sd = 0.
Квантование задаёт аппаратный пол точности: дальнейшие
полные шаги не улучшают гарантию ниже него (certified stop
в терминах ReferenceMachine; пол 3*m^2/(2*mu) из NoisyPL —
та же форма, m = квантователь). -/
theorem machine_step_floor (a w : Fin n → ℝ) (Delta : ℝ)
    (hD : 0 < Delta) :
    energy a (machineStep a w 1 Delta) ≤ (n : ℝ) * Delta ^ 2 / 8 := by
  have hbound := machine_energy_bound a w 1 Delta hD
  have hzero : (∑ i, (jointStep a w 1 i - a i) ^ 2) = 0 := by
    have h1 : ∀ i, jointStep a w 1 i - a i = 0 := by
      intro i
      unfold jointStep
      simp
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h1 i]
    ring
  rw [hzero] at hbound
  rw [Real.sqrt_zero, zero_add] at hbound
  have hsq2 : (Real.sqrt ((n : ℝ)) * Delta / 2) ^ 2
      = (n : ℝ) * Delta ^ 2 / 4 := by
    have hsq3 : ((Real.sqrt ((n : ℝ)) * Delta) / 2) ^ 2
        = (Real.sqrt ((n : ℝ)) * Delta) ^ 2 / 2 ^ 2 := by
      field_simp
    rw [hsq3, mul_pow]
    rw [Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ) by positivity)]
    norm_num
  have hnD : (Real.sqrt ((n : ℝ)) * Delta / 2) ^ 2 / 2
      ≤ (n : ℝ) * Delta ^ 2 / 8 := by
    rw [hsq2]
    linarith
  linarith

end Hagi.Model.ReferenceMachine
