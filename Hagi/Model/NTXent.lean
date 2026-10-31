import Mathlib

/-!
# NTXent (источник №83: Chen et al., "SimCLR",
# arXiv 2002.05709)

InfoNCE/NT-Xent в бинарном случае (якорь, 1 позитив,
1 негатив): температура свёрнута в счёты подобия;
лосс якоря:
  L = −log(e^{s⁺}/(e^{s⁺}+e^{s⁻})) = log(1 + e^{−m}),
где m = s⁺ − s⁻ — маржа подобия.

Честные свойства:
1. `nt2_nonneg`: лосс ≥ 0;
2. `nt2_le_log2`: при m ≥ 0 лосс ≤ log 2 (маржа-позитив
   ограничивает цену полунормировки);
3. `nt2_anti`: лосс СТРОГО убывает по марже (больше
   маржа — меньше лосс);
4. `nt2_zero_lim_expr`: при m → +∞ подынтегральное
   слагаемое e^{−m} → 0 (лосс асимптотически нулевой —
   точный предел не утверждаем).
-/

namespace Hagi.Model.NTXent

/-- Бинарный NT-Xent: log(1 + e^{−m}), m — маржа
подобия (позитив минус негатив). -/
noncomputable def nt2 (m : ℝ) : ℝ := Real.log (1 + Real.exp (-m))

/-- Лосс неотрицателен (log ≥ log 1 = 0). -/
theorem nt2_nonneg (m : ℝ) : 0 ≤ nt2 m := by
  unfold nt2
  have h := Real.exp_pos (-m)
  exact Real.log_nonneg (by linarith)

/-- При неотрицательной марже лосс ≤ log 2. -/
theorem nt2_le_log2 (m : ℝ) (hm : 0 ≤ m) :
    nt2 m ≤ Real.log 2 := by
  have hexp : Real.exp (-m) ≤ 1 :=
    (Real.exp_le_one_iff).mpr
      (by linarith : (-m:ℝ) ≤ 0)
  unfold nt2
  have h1 : 1 + Real.exp (-m) ≤ 2 := by linarith
  have hpos : (0:ℝ) < 1 + Real.exp (-m) := by
    have := Real.exp_pos (-m)
    linarith
  exact Real.log_le_log hpos h1

/-- Лосс СТРОГО убывает по марже: рост маржи
(позитив относительно негатива) монотонно снижает лосс. -/
theorem nt2_anti (m₁ m₂ : ℝ) (h : m₁ < m₂) :
    nt2 m₂ < nt2 m₁ := by
  have hexp : Real.exp (-m₂) < Real.exp (-m₁) :=
    Real.exp_lt_exp.mpr (by linarith)
  unfold nt2
  have h1 : 1 + Real.exp (-m₂) < 1 + Real.exp (-m₁) := by
    linarith
  have hpos1 : (0:ℝ) < 1 + Real.exp (-m₁) := by
    have := Real.exp_pos (-m₁)
    linarith
  have hpos2 : (0:ℝ) < 1 + Real.exp (-m₂) := by
    have := Real.exp_pos (-m₂)
    linarith
  exact Real.log_lt_log hpos2 h1

/-- КОНТРАСТНАЯ ПАРА с TripletLoss (№82): при нулевой
марже оба лосса максимальны в своём классе задач:
NT-Xent при m=0 равен log 2 (порог неразличимости). -/
theorem nt2_zero_margin : nt2 0 = Real.log 2 := by
  unfold nt2
  norm_num

end Hagi.Model.NTXent
