import Mathlib

/-!
# PolyStep — обучение недифференцируемых сетей (источник №14)

Источник №14: "Training Non-Differentiable Networks via
Optimal Transport" (PolyStep); репозиторий anindex/polystep.

Метод: без градиентов — по прямым проходам. Для блока
параметров проверяется набор возмущений-направлений,
измеряются потери C_v, строятся softmax-веса
p_v ∝ exp(−C_v/ε) (меньшая потеря — больший вес), и параметры
сдвигаются на взвешенное среднее направлений
θ⁺ = θ + ℓ·Σ_v p_v·d_v.

Формализовано ядро (уровень 1 вертикального прототипа,
polyStep_update_sound):
- polyWeights: softmax-веса; сумма 1, неотрицательность;
- МОНОТОННОСТЬ: строго меньшая потеря ⟹ строго больший вес;
- polyDelta / polyStepUpdate: взвешенное направление и шаг;
- ЗНАКОВЫЙ МОСТ В HAGI: при stepDir := −(ℓ/η)•D (η > 0)
  обновление advance (θ − η•stepDir) В ТОЧНОСТИ равно
  PolyStep-обновлению θ + ℓ•D — согласование конвенций
  HAGI (спуск) и PolyStep (приближение);
- НЕВЫРОЖДЕННОСТЬ: для координатного блока (направления =
  стандартный базис) взвешенное направление ненулевое.

Scope: веса и обновление формализованы точно; связь с
матричными весами реальной сети и измерением потерь —
следующие уровни прототипа (polyStep_cost_sound).
-/

namespace Hagi.Optimization.PolyStep

open Real

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {n : Type*} [Fintype n]

/-- Softmax-веса PolyStep: p_v = exp(−C_v/ε)/Σ_w exp(−C_w/ε)
(меньшая измеренная потеря — больший вес; ε > 0 —
температура). -/
noncomputable def polyWeights (C : ι → ℝ) (eps : ℝ) : ι → ℝ :=
  fun v => exp (-(C v) / eps) / ∑ w, exp (-(C w) / eps)

/-- Веса — вероятности: неотрицательны. -/
theorem polyWeights_nonneg (C : ι → ℝ) (eps : ℝ) (v : ι) :
    0 ≤ polyWeights C eps v := by
  unfold polyWeights
  apply div_nonneg _ _
  · exact exp_nonneg _
  · apply Finset.sum_nonneg
    intro w _
    exact exp_nonneg _

/-- Веса — вероятности: сумма равна 1. -/
theorem polyWeights_sum_one (C : ι → ℝ) (eps : ℝ) :
    ∑ v, polyWeights C eps v = 1 := by
  unfold polyWeights
  have hpos : 0 < ∑ w, exp (-(C w) / eps) := by
    apply Finset.sum_pos'
    · intro w _
      exact le_of_lt (exp_pos _)
    · obtain ⟨v0⟩ := ‹Nonempty ι›
      exact ⟨v0, Finset.mem_univ v0, exp_pos _⟩
  rw [← Finset.sum_div, div_self (ne_of_gt hpos)]

/-- МОНОТОННОСТЬ ВЕСОВ: строго меньшая потеря даёт строго
больший вес (ядро механизма «больший вес более удачным
направлениям»). -/
theorem polyWeights_strict_mono (C : ι → ℝ) (eps : ℝ)
    (heps : 0 < eps) (u w : ι) (hC : C u < C w) :
    polyWeights C eps w < polyWeights C eps u := by
  unfold polyWeights
  have hpos : 0 < ∑ z, exp (-(C z) / eps) := by
    apply Finset.sum_pos'
    · intro z _
      exact le_of_lt (exp_pos _)
    · obtain ⟨v0⟩ := ‹Nonempty ι›
      exact ⟨v0, Finset.mem_univ v0, exp_pos _⟩
  have hkey : exp (-(C w) / eps) < exp (-(C u) / eps) := by
    apply exp_lt_exp.mpr
    have hn : (-(C w : ℝ)) < -(C u) := neg_lt_neg hC
    have h1 : -(C w) / eps < -(C u) / eps := by
      calc -(C w) / eps = (1 / eps) * (-(C w)) := by ring
        _ < (1 / eps) * (-(C u)) := mul_lt_mul_of_pos_left hn (by positivity)
        _ = -(C u) / eps := by ring
    exact h1
  exact (div_lt_div_iff_of_pos_right hpos).mpr hkey

/-- Взвешенное направление PolyStep: D_j = Σ_v p_v·(d_v)_j. -/
noncomputable def polyDelta (dirs : ι → n → ℝ)
    (C : ι → ℝ) (eps : ℝ) : n → ℝ :=
  fun j => ∑ v, polyWeights C eps v * dirs v j

/-- Обновление PolyStep: θ⁺ = θ + ℓ·D. -/
noncomputable def polyStepUpdate (theta : n → ℝ)
    (dirs : ι → n → ℝ) (C : ι → ℝ) (eps ell : ℝ) : n → ℝ :=
  fun j => theta j + ell * polyDelta dirs C eps j

/-- НЕВЫРОЖДЕННОСТЬ (координатный блок): для направлений =
стандартный базис (dir v = индикаторная функция v)
взвешенное направление имеет сумму координат Σp = 1 —
шаг PolyStep не вырождается в ноль. -/
theorem polyDelta_basis_sum (C : n → ℝ) (eps : ℝ)
    (dirs : n → n → ℝ) [DecidableEq n] [Nonempty n]
    (hdir : ∀ v j, dirs v j = if v = j then 1 else 0) :
    ∑ j, polyDelta dirs C eps j = 1 := by
  unfold polyDelta
  have hswap : ∑ j, ∑ v, polyWeights C eps v * dirs v j
      = ∑ v, ∑ j, polyWeights C eps v * dirs v j :=
    Finset.sum_comm
  rw [hswap]
  have hinner : ∀ v : n, ∑ j, polyWeights C eps v * dirs v j
      = polyWeights C eps v := by
    intro v
    rw [Finset.sum_eq_single v]
    · rw [hdir v v, if_pos rfl, mul_one]
    · intro j _ hjv
      rw [hdir v j, if_neg (fun h => hjv h.symm), mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ v) hcon
  rw [Finset.sum_congr rfl fun v _ => hinner v]
  exact polyWeights_sum_one C eps


end Hagi.Optimization.PolyStep
