import Mathlib

/-!
# TripletLoss (источник №82: Schroff et al., "FaceNet",
# arXiv 1503.03832)

Triplet loss: якорь a, позитив p (тот же класс), негатив n
(чужой класс): L = max 0 (d(a,p) − d(a,n) + m), m ≥ 0 —
маржа. Тянет позитивы к якорю, отталкивает негативи.

Честные свойства:
1. `tl_nonneg`: лосс неотрицателен (hinge);
2. `tl_zero`: если негатив дальше позитива на маржу
   (d(a,n) ≥ d(a,p) + m) — лосс НОЛЬ (требование
   выполнено, градиент исчез);
3. `tl_pos`: если d(a,n) < d(a,p) + m — лосс СТРОГО
   положителен (нарушение маржи сигналит обучению);
4. `tl_le_hinge`: лосс ≤ d(a,p) + m (равномерная граница);
5. `tl_mono`: лосс монотонно не убывает по d(a,p) и не
   возрастает по d(a,n) (правильные направления тяги).
-/

namespace Hagi.Model.TripletLoss

variable (m : ℝ)

/-- Triplet loss с маржей m: hinge от разности
расстояний + маржа. -/
noncomputable def tl (m dap dan : ℝ) : ℝ :=
  max 0 (dap - dan + m)

/-- Hinge неотрицателен. -/
theorem tl_nonneg (m dap dan : ℝ) : 0 ≤ tl m dap dan :=
  le_max_left 0 _

/-- Маржа выполнена ⟹ лосс ноль (позитив достаточно
ближе негатива). -/
theorem tl_zero (m dap dan : ℝ) (hm : 0 ≤ m)
    (h : dap + m ≤ dan) : tl m dap dan = 0 := by
  unfold tl
  have hle : dap - dan + m ≤ 0 := by linarith
  rw [max_eq_left hle]

/-- Маржа нарушена ⟹ лосс строго положителен. -/
theorem tl_pos (m dap dan : ℝ)
    (h : dan < dap + m) : 0 < tl m dap dan := by
  unfold tl
  rw [max_eq_right (by linarith : (0:ℝ) ≤ dap - dan + m)]
  linarith

/-- Равномерная верхняя граница: лосс ≤ d⁺ + m. -/
theorem tl_le_hinge (m dap dan : ℝ) (hm : 0 ≤ m)
    (hdp : 0 ≤ dap) (hdn : 0 ≤ dan) :
    tl m dap dan ≤ dap + m := by
  unfold tl
  by_cases h : dap - dan + m ≤ 0
  · rw [max_eq_left h]
    linarith [hm, hdp]
  · rw [max_eq_right (by linarith : (0:ℝ) ≤ dap - dan + m)]
    linarith [hdn]

/-- Монотонность по позитив-расстоянию: ближе позитив —
меньше лосс. -/
theorem tl_mono_pos (m dap₁ dap₂ dan : ℝ)
    (h : dap₁ ≤ dap₂) :
    tl m dap₁ dan ≤ tl m dap₂ dan := by
  unfold tl
  exact max_le_max (le_refl _) (by linarith)

/-- Антимонотонность по негатив-расстоянию: дальше
негатив — меньше лосс. -/
theorem tl_mono_neg (m dap dan₁ dan₂ : ℝ)
    (h : dan₁ ≤ dan₂) :
    tl m dap dan₂ ≤ tl m dap dan₁ := by
  unfold tl
  exact max_le_max (le_refl _) (by linarith)

end Hagi.Model.TripletLoss
