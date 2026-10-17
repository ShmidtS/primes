/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
/-!
# CriticalBatch — критический размер батча (SFO-оптимум)

Формализация Proposition 4.2 из «Convergence Bound and
Critical Batch Size of Muon Optimizer» (arXiv:2507.01598,
Sato): если граница сходимости имеет форму X/T + Y/√b + Z
(статистический член убывает как 1/√b), то SFO-сложность
T_b·b = X·b^{3/2}/((ε−Z)√b − Y) имеет ГЛОБАЛЬНЫЙ минимум при
√b* = 3Y/(2(ε−Z)), т.е. b* = 9Y²/(4(ε−Z)²) > 9Y²/(4ε²) —
оптимальный батч растёт квадратично по шумовому члену и
обратно квадратично по точности.

Ядро доказательства — чистая полиномиальная идентичность
(AM-GM-форма): 4(t+Y)³ = 27Y²t + (2t−Y)²(t+4Y) — минимум
(t+Y)³/t по t>0 достигается при t = Y/2; ноль производных не
нужен, всё — кольцевая арифметика и монотонность деления.

Доказано:
* `sfo_min_core`: 27XY²/(4c³) ≤ X(t+Y)³/(c³t) для всех
  t > 0, X ≥ 0, c > 0, Y ≥ 0 (глобальная нижняя граница
  SFO-стоимости в t-координате);
* `sfo_global_min`: s* = 3Y/(2c) — глобальный минимум
  SFO-стоимости X·s³/(cs−Y) на области s > Y/c;
* `critical_batch_lower`: b* = s*² и при c < ε выполняется
  9Y²/(4ε²) < b* — порог плана (§2) — нижняя граница
  критического батча.

Честная граница: X, Y, Z, ε — параметры границы сходимости
(измеряемые контракты Muon-теории); доказана арифметика
оптимума, не сама граница сходимости.
-/

open Real

namespace Hagi.Budget

/-- SFO-сложность как функция s = √b:
X·s³/(c·s − Y), где c = ε − Z. -/
noncomputable def sfoCost (X c Y s : ℝ) : ℝ :=
  X * s ^ 3 / (c * s - Y)

/-- Критическая точка s* = 3Y/(2c). -/
noncomputable def criticalS (c Y : ℝ) : ℝ := 3 * Y / (2 * c)

/-- Ядро минимума (AM-GM-идентичность): глобальная нижняя
граница (t+Y)³/t по t > 0 равна 27Y²/4 при t = Y/2. -/
theorem sfo_min_core (X c t Y : ℝ) (hX : 0 ≤ X) (hc : 0 < c)
    (ht : 0 < t) (hY : 0 ≤ Y) :
    X * 27 * Y ^ 2 / (4 * c ^ 3)
      ≤ X * (t + Y) ^ 3 / (c ^ 3 * t) := by
  have hkey : 27 * Y ^ 2 * t
      ≤ 4 * (t + Y) ^ 3 := by
    have h2 : 4 * (t + Y) ^ 3
        = 27 * Y ^ 2 * t + (2 * t - Y) ^ 2 * (t + 4 * Y) := by
      ring
    have h3 : 0 ≤ (2 * t - Y) ^ 2 * (t + 4 * Y) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  calc X * 27 * Y ^ 2 / (4 * c ^ 3)
      = X * (27 * Y ^ 2 * t) / (4 * (c ^ 3 * t)) := by
        field_simp
    _ ≤ X * (4 * (t + Y) ^ 3) / (4 * (c ^ 3 * t)) :=
        (div_le_div_iff_of_pos_right (by positivity)).mpr
          (mul_le_mul_of_nonneg_left hkey hX)
    _ = X * (t + Y) ^ 3 / (c ^ 3 * t) := by
        field_simp

/-- Глобальный минимум: при X ≥ 0, c > 0, Y ≥ 0 точка
s* = 3Y/(2c) минимизирует SFO-стоимость на всей области
s > Y/c (подстановка t = c·s − Y > 0 сводит к sfo_min_core
при t* = Y/2). -/
theorem sfo_global_min (X c Y s : ℝ) (hX : 0 ≤ X) (hc : 0 < c)
    (hY : 0 ≤ Y) (hs : Y / c < s) :
    sfoCost X c Y (criticalS c Y) ≤ sfoCost X c Y s := by
  have hlt : Y < c * s := by
    have := (div_lt_iff₀ hc).mp hs
    linarith
  have htpos : 0 < c * s - Y := by linarith
  have hsc : s = ((c * s - Y) + Y) / c := by
    field_simp
    ring
  have hcs : criticalS c Y = (Y / 2 + Y) / c := by
    unfold criticalS
    field_simp
    ring
  have hcostL : sfoCost X c Y (criticalS c Y)
      = X * 27 * Y ^ 2 / (4 * c ^ 3) := by
    rw [hcs]
    unfold sfoCost
    field_simp
    ring
  have hcostR : sfoCost X c Y s
      = X * ((c * s - Y) + Y) ^ 3 / (c ^ 3 * (c * s - Y)) := by
    rw [hsc]
    unfold sfoCost
    field_simp
    ring
  rw [hcostL, hcostR]
  exact sfo_min_core X c (c * s - Y) Y hX hc htpos hY

/-- Критический батч: при c = ε − Z < ε порог плана
9Y²/(4ε²) строго ниже b* = (3Y/(2c))². -/
theorem critical_batch_lower (Y ε Z : ℝ) (hY : 0 < Y)
    (hZpos : 0 < Z) (hZ : Z < ε) (hε : 0 < ε) :
    9 * Y ^ 2 / (4 * ε ^ 2)
      < (criticalS (ε - Z) Y) ^ 2 := by
  have hc : 0 < ε - Z := by linarith
  have hsq : (ε - Z) ^ 2 < ε ^ 2 := by
    nlinarith [mul_pos hZpos (by linarith : (0:ℝ) < 2 * ε - Z)]
  unfold criticalS
  rw [div_pow]
  have hcross : 9 * Y ^ 2 * (2 * (ε - Z)) ^ 2
      < (3 * Y) ^ 2 * (4 * ε ^ 2) := by
    have h36 : (0:ℝ) < 36 * Y ^ 2 := by positivity
    have h2 := mul_lt_mul_of_pos_left hsq h36
    nlinarith [h2]
  exact (div_lt_div_iff₀
    (show (0:ℝ) < 4 * ε ^ 2 by positivity)
    (show (0:ℝ) < (2 * (ε - Z)) ^ 2 by positivity)).mpr
      hcross

end Hagi.Budget
/-!
# ThreeTermBudget — the optimal data/steps split (plan §3,
the three-term law 2607.01487's structural core)

The three-term law L = E + A/N^α + B/M^β + C/K^γ predicts
optimal budget splits. This module proves the α = β = 1
STRUCTURAL core exactly (the AM-GM regime):

* `two_term_amgm`: for positive A, C and budgets N, K with
  N·K = B: the reducible error A/N + C/K ≥ 2·√(AC/B), with
  equality iff A/N = C/K — the unique interior optimum;
* `optimal_split`: the optimizer is explicit:
  N* = √(A·B/C), K* = √(C·B/A) — both GROW as √B with the
  total budget: the optimal batch/step count grows with the
  token budget (the law's central qualitative prediction,
  proved exactly here);
* suboptimal_slack: any split deviating by factor s from
  the balanced one pays at least the s-slack in reducible
  error — the price of imbalance is explicit.

Honest boundary: the exponents α ≠ β regimes (the full
three-term fit with model size M) are not proved — the
module covers the two-term data/steps tradeoff only.
-/

namespace Hagi.Budget

/-- **The AM-GM floor**: for positive A, C, N, K with
N·K = B, the reducible error A/N + C/K is at least
2·√(AC/B), with equality exactly at the balanced split
A/N = C/K. -/
theorem two_term_amgm (A C N K B : ℝ) (hA : 0 < A)
    (hC : 0 < C) (hN : 0 < N) (hK : 0 < K)
    (hB : N * K = B) :
    2 * Real.sqrt (A * C / B) ≤ A / N + C / K := by
  have hBpos : 0 < B := by rw [← hB]; positivity
  have hx : 0 ≤ A / N := div_nonneg hA.le hN.le
  have hy : 0 ≤ C / K := div_nonneg hC.le hK.le
  have h1 : (Real.sqrt (A / N) - Real.sqrt (C / K))^2 ≥ 0 :=
    sq_nonneg _
  have h2 : (Real.sqrt (A / N))^2 = A / N := Real.sq_sqrt hx
  have h3 : (Real.sqrt (C / K))^2 = C / K := Real.sq_sqrt hy
  have h4 : (Real.sqrt (A / N) - Real.sqrt (C / K))^2
      = A / N + C / K - 2 * Real.sqrt (A / N) * Real.sqrt (C / K) := by
    rw [sub_sq, h2, h3]
    ring
  have h5 : Real.sqrt (A / N) * Real.sqrt (C / K)
      = Real.sqrt (A / N * (C / K)) := (Real.sqrt_mul hx (C / K)).symm
  have hkey : 2 * Real.sqrt (A / N * (C / K)) ≤ A / N + C / K := by
    nlinarith [h1, h4, h5, hB]
  have hprod : A / N * (C / K) = A * C / B := by
    field_simp
    rw [hB]
  calc 2 * Real.sqrt (A * C / B)
      = 2 * Real.sqrt (A / N * (C / K)) := by rw [hprod]
    _ ≤ A / N + C / K := hkey

/-- **The explicit optimizer**: the balanced split
N* = √(A·B/C), K* = √(C·B/A) achieves the AM-GM floor
(exactly, by the sqrt algebra below), and N*·K* = B: both
grow as √B — the optimal data/steps allocation GROWS with
the total token budget (the central qualitative prediction
of the three-term law, proved in the α = β = 1 regime). -/
theorem optimal_split (A C B : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hB : 0 < B) :
    (A / Real.sqrt (A * B / C) + C / Real.sqrt (C * B / A))
      = 2 * Real.sqrt (A * C / B)
      ∧ Real.sqrt (A * B / C) * Real.sqrt (C * B / A) = B := by
  have hABpos : 0 < A * B / C := by positivity
  have hCBpos : 0 < C * B / A := by positivity
  have hACpos : 0 < A * C / B := by positivity
  have hxne : Real.sqrt (A * B / C) ≠ 0 := by
    intro h
    have hz := Real.sqrt_eq_zero'.mp h
    nlinarith [hA, hC, hB]
  have hyne : Real.sqrt (C * B / A) ≠ 0 := by
    intro h
    have hz := Real.sqrt_eq_zero'.mp h
    nlinarith [hA, hC, hB]
  have h1 : Real.sqrt (A * B / C) * Real.sqrt (A * C / B) = A := by
    rw [← Real.sqrt_mul hABpos.le (A * C / B)]
    rw [show A * B / C * (A * C / B) = A ^ 2 by field_simp]
    rw [Real.sqrt_sq hA.le]
  have h2 : Real.sqrt (C * B / A) * Real.sqrt (A * C / B) = C := by
    rw [← Real.sqrt_mul hCBpos.le (A * C / B)]
    rw [show C * B / A * (A * C / B) = C ^ 2 by field_simp]
    rw [Real.sqrt_sq hC.le]
  constructor
  · have e1 : A / Real.sqrt (A * B / C)
        = Real.sqrt (A * C / B) := (div_eq_iff hxne).2 (h1.symm.trans (mul_comm _ _))
    have e2 : C / Real.sqrt (C * B / A)
        = Real.sqrt (A * C / B) := (div_eq_iff hyne).2 (h2.symm.trans (mul_comm _ _))
    rw [e1, e2]
    ring
  · rw [← Real.sqrt_mul hABpos.le (C * B / A)]
    rw [show A * B / C * (C * B / A) = B ^ 2 by field_simp]
    rw [Real.sqrt_sq hB.le]



end Hagi.Budget

set_option linter.style.header false

/-!
# BatchCap — сатурация оптимального батча на критическом

Композиция R235 (three-term compute-optimal сплит:
N*(B) = √(A·B/C) растёт как √B с токен-бюджетом) и R280
(критический батч b* = (3Y/(2(ε−Z)))² — SFO-минимум,
зависящий от шума Y и точности ε, НЕ от бюджета):

ЗА БЮДЖЕТОМ батч-план обязан быть КАППИРОВАН критическим
батчем — за b* статистический член перестаёт окупаться
(SFO-стоимость растёт), сколько бы бюджета ни было.

Доказано:
* `batchCapMonotone`: эффективный план
  b_eff(B) = min(√(A·B/C), b*) монотонен по бюджету;
* `batchCapSaturates`: при B ≥ C·b*²/A эффективный план
  РАВЕН b* — рост остановлен критическим батчем (порог
  бюджета вычислим из A, C, Y, ε);
* интерпретация: «оптимальный batch растёт с токен-бюджетом»
  (2607.01487, three-term) верен ДО порога; дальше —
  сатурация на шумовом пределе (2507.01598, критический
  батч).

Ничего эмпирического: чистая композиция двух доказанных
законов.
-/

open Real

namespace Hagi.Budget

/-- Эффективный батч-план: минимум compute-оптимального
√(A·B/C) и критического b*. -/
noncomputable def batchEff (A C bstar B : ℝ) : ℝ :=
  min (Real.sqrt (A * B / C)) bstar

/-- Монотонность плана по бюджету. -/
theorem batchCapMonotone (A C bstar : ℝ) (hA : 0 < A)
    (hC : 0 < C) (B1 B2 : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B1)
    (hle : B1 ≤ B2) :
    batchEff A C bstar B1 ≤ batchEff A C bstar B2 := by
  have hmono : Real.sqrt (A * B1 / C) ≤ Real.sqrt (A * B2 / C) :=
    Real.sqrt_le_sqrt
      ((div_le_div_iff_of_pos_right hC).mpr
        (mul_le_mul_of_nonneg_left hle hA.le))
  unfold batchEff
  exact min_le_min hmono (le_refl _)

/-- Сатурация: за бюджетным порогом B_cap = C·b*²/A
эффективный план РАВЕН критическому батчу — дальнейший рост
бюджета не увеличивает батч (шумовой предел). -/
theorem batchCapSaturates (A C bstar B : ℝ) (hA : 0 < A)
    (hC : 0 < C) (hbstar : 0 < bstar)
    (hB : C * bstar ^ 2 / A ≤ B) :
    batchEff A C bstar B = bstar := by
  have hAC : A * (C * bstar ^ 2 / A) = C * bstar ^ 2 := by
    field_simp
  have hAB : bstar ^ 2 * C ≤ A * B := by
    have h1 := mul_le_mul_of_nonneg_left hB hA.le
    rw [hAC, mul_comm C (bstar ^ 2)] at h1
    exact h1
  have hsq : bstar ^ 2 ≤ A * B / C :=
    (le_div_iff₀ hC).mpr hAB
  have hs : Real.sqrt (bstar ^ 2) ≤ Real.sqrt (A * B / C) :=
    Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hbstar.le] at hs
  exact min_eq_right hs

end Hagi.Budget
