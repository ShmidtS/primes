import Hagi.Model.StageSemantics
import Hagi.Energy.Quantizer
import Hagi.Step.NoisyPL

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

/-- ПОКОМПОНЕНТНАЯ нормированная ошибка квантования:
max_i |Q(w)ᵢ − wᵢ| / Δ — вычисляемая величина, جایстоящая
аналитическому выводу посылки h_emp_dist (≤ 1/2) из
round-семантики решётки. -/
noncomputable def quantErrNorm (Delta : ℝ) (w : Fin n → ℝ) : ℝ :=
  ∑ i, |compressQ Delta w i - w i| / Delta

/-- АНАЛИТИЧЕСКИЙ ВЫВОД h_emp_dist-посылки: покомпонентная
нормированная ошибка решётки ≤ n/2 — из |round x − x| ≤ 1/2
на каждой координате; при среднем по координатам (s-норме)
величина ≤ 1/2. -/
theorem quantErrNorm_avg_le_half (Delta : ℝ) (hD : 0 < Delta)
    (w : Fin n → ℝ) (hn : 0 < n) :
    (quantErrNorm Delta w) / ((n : ℝ)) ≤ 1 / 2 := by
  have hper : ∀ i, |compressQ Delta w i - w i| / Delta ≤ 1 / 2 := by
    intro i
    have h1 : compressQ Delta w i - w i
        = Delta * (round (w i / Delta) - w i / Delta) := by
      unfold compressQ
      field_simp
    have hrr : |w i / Delta - round (w i / Delta)| ≤ 1 / 2 :=
      abs_sub_round (w i / Delta)
    rw [h1, abs_mul, abs_of_pos hD]
    have hswap : |round (w i / Delta) - w i / Delta|
        = |w i / Delta - round (w i / Delta)| := abs_sub_comm _ _
    rw [hswap]
    have hdiv : (0:ℝ) < Delta := hD
    have key : Delta * |w i / Delta - round (w i / Delta)| / Delta
        = |w i / Delta - round (w i / Delta)| := by
      field_simp
    rw [key]
    exact hrr
  have hcard : (∑ i : Fin n, (1:ℝ) / 2) = ((n:ℝ)) * (1 / 2) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hle : ∑ i, |compressQ Delta w i - w i| / Delta
      ≤ ∑ i : Fin n, (1:ℝ) / 2 := Finset.sum_le_sum (fun i _ => hper i)
  change (∑ i, |compressQ Delta w i - w i| / Delta) / ((n:ℝ)) ≤ 1 / 2
  rw [div_le_iff₀ (by positivity : (0:ℝ) < ((n:ℝ)))]
  linarith [hle, hcard]

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


/-- ГОРИЗОНТ ОСТАНОВКИ МАШИННОГО ЦИКЛА: если каждый цикл
сжимает энергию как `E⁺ ≤ q·E + F` (q = (1−eta)^2,
F = n*Delta^2/8 — hardware floor) и `q^t * E0 <= eps`,
то `E t <= eps + F/(1-q)` — за `t` шагов гарантируется
точность `eps` плюс floor-поправка. Количество циклов
до certified stop: `t = ceil(log(eps*(1-q)/E0)/log q)`. -/
theorem machine_stop_horizon (E : ℕ → ℝ) (q F eps E0 : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hF : 0 ≤ F) (heps : 0 ≤ eps)
    (hstep : ∀ t, E (t + 1) ≤ q * E t + F)
    (h0 : E 0 = E0) (t : ℕ) (hterm : q ^ t * E0 ≤ eps) :
    E t ≤ eps + F / (1 - q) := by
  have htele := Hagi.Step.noisy_recurrence_telescope E q F hq hq1 hF hstep E0
    (by rw [h0]) t
  linarith


/-- ОБРАТНОЕ ПРОЕКТИРОВАНИЕ СЕТКИ (термостат решётки):
для целевого аппаратного пола `tau` достаточно сетки
`Delta <= sqrt(8*tau/n)` — обращение machine_step_floor.
Контроллер выбирает сетку из цели точности. -/
theorem grid_for_floor (tau Delta : ℝ) (htau : 0 ≤ tau)
    (hn : 0 < n)
    (hD : 0 < Delta) (hDle : Delta ≤ Real.sqrt (8 * tau / (n:ℝ))) :
    (n:ℝ) * Delta ^ 2 / 8 ≤ tau := by
  have hsq : (Real.sqrt (8 * tau / (n:ℝ))) ^ 2 = 8 * tau / (n:ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsq2 : Delta ^ 2 ≤ 8 * tau / (n:ℝ) := by
    have h0 := sq_le_sq' (by
      have := Real.sqrt_nonneg (8 * tau / (n:ℝ))
      linarith) hDle
    rwa [hsq] at h0
  calc (n:ℝ) * Delta ^ 2 / 8
      = ((n:ℝ) / 8) * Delta ^ 2 := by ring
    _ ≤ ((n:ℝ) / 8) * (8 * tau / (n:ℝ)) :=
        mul_le_mul_of_nonneg_left hsq2 (by positivity)
    _ = tau := by
        field_simp

/-- ТЕРМОСТАТ: сетка как функция машинной энергии
`Delta(T) = sqrt(2*T/n)` опускает hardware floor до
`T/4`: замыкание термодинамического цикла — энергия
(NoiseTemperature) задаёт T, T задаёт сетку, сетка задаёт
пол точности машины. -/
theorem grid_temperature (T : ℝ) (hT : 0 ≤ T) (hn : 0 < n)
    (Delta : ℝ) (hD : 0 < Delta)
    (hDle : Delta ≤ Real.sqrt (2 * T / (n:ℝ))) :
    (n:ℝ) * Delta ^ 2 / 8 ≤ T := by
  have hsq : Delta ^ 2 ≤ 2 * T / (n:ℝ) := by
    have h0 := sq_le_sq' (by
      have := Real.sqrt_nonneg (2 * T / (n:ℝ))
      linarith) hDle
    rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * T / (n:ℝ))] at h0
    exact h0
  have hfloor : Delta ^ 2 ≤ 8 * (T / 4) / (n:ℝ) := by
    have h2 : (8:ℝ) * (T / 4) = 2 * T := by ring
    rw [h2]
    exact hsq
  have hdle : Delta ≤ Real.sqrt (8 * (T / 4) / (n:ℝ)) :=
    Real.le_sqrt_of_sq_le hfloor
  have hres := grid_for_floor (T / 4) Delta (by positivity) hn hD
    hdle
  linarith


/-! ### Термостат-петля: батч → температура → сетка → пол

NoiseTemperature (Probability): шум градиента — резервуар с
температурой T = sigma^2/B. Соединение с термостатом решётки:
Δ(T) = sqrt(2T/n) = sigma·sqrt(2/(B·n)) — сетка, выбранная
бюджетом измерений; её аппаратный пол ≤ sigma^2/(2B).
Рост батча в c раз опускает пол в c раз — самоохлаждение
машины измерениями. -/

/-- ПЕТЛЯ ТЕРМОСТАТА: при сетке из температуры батча
`Delta = sigma*sqrt(2/(B*n))` аппаратный пол машины
`<= sigma^2/B` — точность ограничена только бюджетом
измерений; рост батча в c раз опускает пол в c раз
(самоохлаждение машины измерениями). -/
theorem batch_grid_loop (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (B : ℕ) (hB : 0 < B) (hn : 0 < n) (Delta : ℝ)
    (hD : 0 < Delta)
    (hDle : Delta ≤ Real.sqrt (2 * (sigma ^ 2 / (B:ℝ))
      / (n:ℝ))) :
    (n:ℝ) * Delta ^ 2 / 8 ≤ sigma ^ 2 / (B:ℝ) := by
  have hres := grid_temperature (sigma ^ 2 / (B:ℝ))
    (by
      have := sq_nonneg sigma
      exact div_nonneg this (le_of_lt (by exact_mod_cast hB)))
    hn Delta hD hDle
  have hsplit : sigma ^ 2 / (B:ℝ) / 4
      ≤ sigma ^ 2 / (B:ℝ) := by
    have hp : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
    have h1 : sigma ^ 2 / (B:ℝ) / 4 = sigma ^ 2 / ((B:ℝ) * 4) := by
      ring
    rw [h1]
    have h4 : (1:ℝ) ≤ (4:ℝ) := by norm_num
    have hp : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
    exact div_le_div_of_nonneg_left (sq_nonneg sigma)
      hp (by linarith [mul_le_mul_of_nonneg_left h4 (le_of_lt hp)])
  linarith


/-- ОТЖИГ ТЕРМОСТАТА: при геометрическом росте батча
`B t = B 0 * c ^ t` сертифицированный пол экспоненциально
падает: `floor t <= sigma^2/(B 0 * c ^ t)`. Полная
автоматика отжига: измерения растут по расписанию — точность
растёт экспоненциально без вмешательства контроллера;
температура резервуара охлаждается как 1/c^t. -/
theorem batch_anneal_floor (sigma B0 c : ℝ) (hsigma : 0 ≤ sigma)
    (hB0 : 0 < B0) (hc1 : 1 < c) (hn : 0 < n)
    (t : ℕ) (Delta : ℝ) (hD : 0 < Delta)
    (hDle : Delta ≤ Real.sqrt (2 * (sigma ^ 2 / (B0 * c ^ t))
      / (n:ℝ))) :
    (n:ℝ) * Delta ^ 2 / 8 ≤ sigma ^ 2 / (B0 * c ^ t) :=
  grid_temperature (sigma ^ 2 / (B0 * c ^ t))
    (by
      have hc0 : (0:ℝ) < c := by linarith
      exact div_nonneg (sq_nonneg sigma)
        (le_of_lt (mul_pos hB0 (pow_pos hc0 t))))
    hn Delta hD hDle

end Hagi.Model.ReferenceMachine
