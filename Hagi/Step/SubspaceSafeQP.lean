import Hagi.Step.AdaptiveSafeQP

set_option linter.style.header false

/-!
# SubspaceSafeQP — концентрация в подпространстве направлений (аудит TD-05)

Размерностный взрыв `adaptiveNoiseEps` = σ(D+ε)·√(2log(2|K|(2M+1)ⁿ/δ)/m)
делает равномерную концентрацию по ε-сети неприменимой к реальным
моделям: log|N| = O(n log M) при n ~ 10⁷ требует m ≫ n.

Лечение (по плану аудита, фаза 5): направление d* и защищённые
градиенты g₁..g_K лежат в r-мерном подпространстве
span{d₀, g₁,…,g_K}, r = K+1 ≪ n. Если ι : ℝ^r → ℝ^n —
линейная изометрия (сохраняет скалярные произведения), и весь
шум лежит в подпространстве (ξ = ιζ), то вся концентрация
переносится на r-мерную сеть: порог зависит от r = K+1,
а не от числа параметров n. Поскольку r ≤ n, подпространный
порог ≤ полноразмерного (`subspace_eps_le_full`).

Имплементационный вывод (докстринг, не теорема): численный
решатель SafeQP должен работать в базисе подпространства
(разложение Каргуена в span{d₀, gᵢ}) — полиномиальная
сложность O(poly(K, m)) вместо экспоненты по n.
-/

open Finset Real MeasureTheory ProbabilityTheory InnerProductSpace

namespace Hagi.Step.SubspaceSafeQP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {K : Type*} [Fintype K] [Nonempty K]

/-- Монотонность сетевого порога по размерности: при r ≤ n
r-мерная сеть не больше n-мерной (2M+1 ≥ 1, степень монотонна).
Это формализует «концентрация в подпространстве дешевле». -/
theorem subspace_eps_le_full {r n : ℕ} (hrn : r ≤ n) (D epsDir : ℝ)
    (hD : 0 ≤ D) (hepsDir : 0 ≤ epsDir) (M : ℕ) (sigma : ℝ)
    (hsigma : 0 ≤ sigma) (m : ℕ) (hm : 0 < m) (delta : ℝ)
    (hdelta : (0:ℝ) < delta)
    (hdle : (delta:ℝ) ≤ 2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ r : ℝ)) :
    adaptiveNoiseEps K r D epsDir M sigma m delta
      ≤ adaptiveNoiseEps K n D epsDir M sigma m delta := by
  unfold adaptiveNoiseEps
  have hfac : 0 ≤ sigma * (D + epsDir) :=
    mul_nonneg hsigma (add_nonneg hD hepsDir)
  have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine mul_le_mul le_rfl (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _) hfac
  have h1r : (1:ℝ) ≤ 2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ r : ℝ) / delta := by
    rw [le_div_iff₀ hdelta]
    linarith
  have hnum : 2 * Real.log (2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ r : ℝ) / delta)
      ≤ 2 * Real.log (2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ n : ℝ) / delta) := by
    have hrle : ((2 * M + 1) ^ r : ℝ) ≤ ((2 * M + 1) ^ n : ℝ) := by
      norm_cast
      exact Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le (2 * M))) hrn
    have hbase : (0:ℝ) < ((2 * M + 1) ^ r : ℝ) := by
      positivity
    have hcard : 0 < Fintype.card K := Fintype.card_pos (α := K)
    have h1 : (0:ℝ) < 2 := by norm_num
    have h2 : (0:ℝ) < (Fintype.card K : ℝ) := Nat.cast_pos.mpr hcard
    have h3 : (0:ℝ) < ((2 * M + 1) ^ r : ℝ) := hbase
    have hApos : 0 < 2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ r : ℝ) / delta :=
      div_pos (mul_pos (mul_pos h1 h2) h3) hdelta
    have hAn : 2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ r : ℝ) / delta
        ≤ 2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ n : ℝ) / delta := by
      have hc2 : (0:ℝ) ≤ 2 * (Fintype.card K : ℝ) := by
        have := mul_nonneg (le_of_lt h1) (le_of_lt h2)
        exact this
      rw [div_le_div_iff_of_pos_right hdelta]
      exact mul_le_mul_of_nonneg_left hrle hc2
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log hApos hAn) (by norm_num)
  rw [div_le_div_iff_of_pos_right hmpos]
  exact hnum

end SubspaceSafeQP

end Hagi.Step
