/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Budget.ThreeTermBudget
import Hagi.Budget.CriticalBatch

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

namespace Hagi.BatchCap

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

end Hagi.BatchCap
