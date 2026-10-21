/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic

set_option linter.style.header false

namespace Hagi.Optimization

/-!
# InexactContraction — неточное сжатие и пол квантования

Внутренняя индукция геометрически адаптивной HAGI
(проект «три геометрии»: упаковка направлений, рост
подпространства по остатку проекции, спектральное
управление рекурсией). Если итерационный шаг — сжатие с
фактором q < 1, испорченное пошаговой ошибкой ε
(квантование `gridQ`, приближённые вычисления), то

  `x(k) ≤ q^k·x₀ + ε·(1 − q^k)/(1 − q)`

и, следовательно, предельный пол ошибки —

  `x(k) ≤ q^k·x₀ + ε/(1 − q)`.

Квантование не позволяет приблизиться к неподвижной точке
ближе чем ε/(1−q): для останова по допуску τ необходимо
ε/(1−q) < τ (связка с `quantized_descent_telescope`:
ε = Δ/2 за шаг ⟹ требование к шагу решётки Δ < 2τ(1−q)).
-/

/-- **Граница неточного сжатия**: рекурсия
`x(k+1) ≤ q·x(k) + ε` с фактором сжатия q ∈ (0,1) и
пошаговой ошибкой ε ≥ 0 удовлетворяет точной геометрической
оценке с суммой ошибок. -/
theorem inexact_contraction_bound (x : ℕ → ℝ) (q ε : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 ≤ ε)
    (hstep : ∀ k : ℕ, x (k+1) ≤ q * x k + ε) (k : ℕ) :
    x k ≤ q^k * x 0 + ε * (1 - q^k) / (1 - q) := by
  induction k with
  | zero => norm_num
  | succ n ih =>
      have h1 := hstep n
      have hqpos : (0:ℝ) < 1 - q := by linarith
      have h2 : q * (q^n * x 0 + ε * (1 - q^n)/(1 - q)) + ε
          = q^(n+1) * x 0 + ε * (1 - q^(n+1))/(1 - q) := by
        rw [pow_succ]
        field_simp
        ring
      calc x (n+1) ≤ q * x n + ε := h1
        _ ≤ q * (q^n * x 0 + ε * (1 - q^n)/(1 - q)) + ε :=
            add_le_add (mul_le_mul_of_nonneg_left ih (le_of_lt hq0)) (le_refl ε)
        _ = q^(n+1) * x 0 + ε * (1 - q^(n+1))/(1 - q) := h2

/-- **Предельный пол неточного сжатия**: ошибка не может
стать меньше ε/(1−q), сколько ни итерируй — квантование
ставит пол сходимости. Совместно с
`quantized_descent_telescope` (ε = Δ/2): пол = Δ/(2(1−q)),
для останова по допуску τ достаточно шага решётки
Δ < 2·τ·(1−q). -/
theorem inexact_contraction_floor (x : ℕ → ℝ) (q ε : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 ≤ ε)
    (hstep : ∀ k : ℕ, x (k+1) ≤ q * x k + ε) (k : ℕ) :
    x k ≤ q^k * x 0 + ε / (1 - q) := by
  have hqpos : (0:ℝ) < 1 - q := by linarith
  have h := inexact_contraction_bound x q ε hq0 hq1 hε hstep k
  have hle : ε * (1 - q^k) / (1 - q) ≤ ε / (1 - q) := by
    have hqk : (0:ℝ) ≤ q^k := by positivity
    have h1 : (1:ℝ) - q^k ≤ 1 := by linarith
    have h2 : ε * (1 - q^k) ≤ ε * 1 := mul_le_mul_of_nonneg_left h1 hε
    rw [mul_one] at h2
    exact (div_le_div_iff_of_pos_right hqpos).mpr h2
  linarith


/-- **Критерий останова неточного сжатия**: если пол ошибки
ниже допуска (ε/(1−q) < τ, встроено в строгость hK) и
начальное отклонение ограничено x 0 ≤ B, то любой горизонт K
с q^K < (τ − ε/(1−q))/B даёт останов по допуску: x K < τ.
Внутренняя индукция «трёх геометрий» замкнута: сжатие +
квантование + явный K-горизонт останова (логарифмический по
1/(τ − ε/(1−q)) при геометрическом убывании q^K). -/
theorem inexact_contraction_halt (x : ℕ → ℝ) (q ε τ : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 ≤ ε)
    (hstep : ∀ k : ℕ, x (k+1) ≤ q * x k + ε)
    (B : ℝ) (hB0 : 0 < B) (hB : x 0 ≤ B) (K : ℕ)
    (hK : q ^ (K : ℝ) < (τ - ε / (1 - q)) / B) :
    x K < τ := by
  have hfloor := inexact_contraction_floor x q ε hq0 hq1 hε hstep K
  rw [show (q^(K:ℕ):ℝ) = q ^ (K:ℝ) from (Real.rpow_natCast q K).symm] at hfloor
  have hqpos : (0:ℝ) < 1 - q := by linarith
  have hqK : (0:ℝ) < q ^ (K:ℝ) := by positivity
  have h1 : q ^ (K:ℝ) * B < τ - ε / (1 - q) := (lt_div_iff₀ hB0).mp hK
  have h2 : q ^ (K:ℝ) * x 0 ≤ q ^ (K:ℝ) * B :=
    mul_le_mul_of_nonneg_left hB (le_of_lt hqK)
  have h3 : q ^ (K:ℝ) * x 0 < τ - ε / (1 - q) := lt_of_le_of_lt h2 h1
  linarith

/-- **Ускорение Андерсона: пол квантования улучшается на
gain-фактор** (мост к Evans–Pollock–Rebholz 2020, SIAM J.
Numer. Anal.: AA улучшает скорость сжатия на фактор gain
θ ≤ 1 за шаг): если ускоренная итерация поддерживает
per-step gain θ — `x(k+1) ≤ θ·q·x(k) + ε` — то эффективный
фактор сжатия θ·q и

* точная граница: `x(k) ≤ (θq)^k·x₀ + ε(1−(θq)^k)/(1−θq)`;
* пол квантования улучшается: `ε/(1−θq) ≤ ε/(1−q)`.

Ускорение снижает предельную ошибку квантованной рекурсии —
явный выигрыш ускорения в нашей floor-семантике. -/
theorem anderson_floor_gain (x : ℕ → ℝ) (θ q ε : ℝ) (hθ : 0 < θ)
    (hθ1 : θ < 1) (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 ≤ ε)
    (hAA : ∀ k : ℕ, x (k+1) ≤ θ * q * x k + ε) (k : ℕ) :
    x k ≤ (θ*q)^k * x 0 + ε * (1 - (θ*q)^k) / (1 - θ*q)
      ∧ ε / (1 - θ*q) ≤ ε / (1 - q) := by
  have hq'0 : 0 < θ * q := by positivity
  have hq'1 : θ * q < 1 := by nlinarith
  refine ⟨inexact_contraction_bound x (θ*q) ε hq'0 hq'1 hε hAA k, ?_⟩
  rw [div_le_div_iff₀ (by nlinarith : (0:ℝ) < 1 - θ*q) (by nlinarith : (0:ℝ) < 1 - q)]
  have hle : θ * q ≤ q := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hle hε]

/-- **AA-горизонт останова**: ускоренная рекурсия с gain θ
останавливается по допуску τ при
(θ·q)^K < (τ − ε/(1−θq))/B — объединение
`anderson_floor_gain` (улучшенный фактор и пол) и
`inexact_contraction_halt` (явный горизонт): ускорение
сокращает не только пол, но и K-горизонт останова
(логарифмический по 1/(τ − улучшенный пол)). -/
theorem anderson_halt (x : ℕ → ℝ) (θ q ε τ : ℝ) (hθ : 0 < θ)
    (hθ1 : θ < 1) (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 ≤ ε)
    (hAA : ∀ k : ℕ, x (k+1) ≤ θ * q * x k + ε)
    (B : ℝ) (hB0 : 0 < B) (hB : x 0 ≤ B) (K : ℕ)
    (hK : (θ*q) ^ (K : ℝ) < (τ - ε / (1 - θ*q)) / B) :
    x K < τ := by
  have hq'0 : 0 < θ * q := by positivity
  have hq'1 : θ * q < 1 := by nlinarith
  exact inexact_contraction_halt x (θ*q) ε τ hq'0 hq'1 hε hAA B hB0 hB K hK
end Hagi.Optimization
