import Mathlib
import Hagi.Unified.DescentCore

/-!
# DescentCoreQuad (такт №263, аудит #3/#8): первый
НЕПОСТУЛИРОВАННЫЙ инстанс Objective — квадратичная
машина E(w) = ½·Σ(wᵢ−aᵢ)².

Контракт DescentCore.descentLemma здесь НЕ поле, а
ТЕОРЕМА: для квадратичной цели L-гладкость с L = 1
ВЫВОДИТСЯ алгебраически (точное равенство, не неравенство):
  E(x+d) = E(x) + ⟨x−a, d⟩ + ½‖d‖².

Следствия:
1. `quadObjective`: реальный Objective с доказанной
   гладкостью;
2. `quadAligned`: направление dir = x − a (сам градиент)
   выровнено — alignment НЕ гипотеза, а вычисление;
3. `quad_one_step`: при η = 1/L = 1 шаг попадает в оптимум
   a за ОДИН шаг (E(a) = 0) — нетривиальный сквозной
   witness: реальный алгоритм изменяет параметры и
   ДОКАЗАННО достигает минимума (не «idle»-нулевая
   траектория и не hand-made эффекты);
4. `quad_drop`: специализация descent_drop — убывание
   строгое при x ≠ a.
-/

namespace Hagi.Unified.DescentCoreQuad

open Hagi.Unified.DescentCore

variable {k : Type*} [Fintype k]

/-- Цель: E(w) = ½Σ(w−a)² (расстояние до цели a). -/
noncomputable def quadE (a w : k → ℝ) : ℝ :=
  (∑ i, (w i - a i)^2) / 2

/-- Градиент квадратичной цели: w − a. -/
def quadGrad (a w : k → ℝ) : k → ℝ := fun i => w i - a i

/-- КЛЮЧЕВОЙ ВЫВОД ГЛАДКОСТИ: для квадратичной цели
descent-лемма — ТОЧНОЕ РАВЕНСТВО с L = 1 (алгебра, не
постулат). -/
theorem quad_descent_eq (a x d : k → ℝ) :
    quadE a (x + d) = quadE a x + inprod (quadGrad a x) d
      + (1:ℝ) / 2 * nrm2 d := by
  have hexp : ∀ i, ((x + d) i - a i)^2
      = (x i - a i)^2 + 2*(x i - a i)*d i + (d i)^2 := by
    intro i
    have h : (x + d) i - a i = (x i - a i) + d i := by
      simp [Pi.add_apply]; ring
    rw [h]
    ring
  have hsum : ∑ i, ((x + d) i - a i)^2
      = ∑ i, (x i - a i)^2 + ∑ i, 2*(x i - a i)*d i
        + ∑ i, (d i)^2 := by
    rw [Finset.sum_congr rfl (fun i _ => hexp i),
      Finset.sum_add_distrib, Finset.sum_add_distrib]
  unfold quadE quadGrad inprod nrm2
  rw [hsum]
  have h2 : ∑ i, 2*(x i - a i)*d i
      = 2 * ∑ i, (x i - a i)*d i := by
    rw [show (2 * ∑ i, (x i - a i)*d i)
      = ∑ i, 2*((x i - a i)*d i) from Finset.mul_sum _ _ 2]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h2]
  ring

/-- РЕАЛЬНЫЙ OBJECTIVE: квадратичная машина — все поля
контракта (включая descentLemma) ДОКАЗАНЫ. -/
noncomputable def quadObjective (a : k → ℝ) : Objective k where
  f := quadE a
  grad := quadGrad a
  L := 1
  hL := by norm_num
  descentLemma := fun x d => (quad_descent_eq a x d).le

/-- Направление «сам градиент» выровнено — БЕЗ гипотез. -/
theorem quadAligned (a x : k → ℝ) :
    aligned (quadObjective a) x (quadGrad a x) := by
  unfold aligned quadObjective
  have h : inprod (quadGrad a x) (quadGrad a x)
      = nrm2 (quadGrad a x) := by
    unfold inprod nrm2 quadGrad
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h]

/-- ОДНОШАГОВАЯ СХОДИМОСТЬ: при η = 1/L = 1 и направлении
«градиент» шаг попадает ТОЧНО в оптимум a (E(a) = 0) —
алгоритм реально изменяет параметры и доказанно достигает
цели (сквозной witness без ручных эффектов). -/
theorem quad_one_step (a x : k → ℝ) :
    (quadObjective a).f (x - quadGrad a x) = 0
    ∧ quadE a x = nrm2 (quadGrad a x) / 2 := by
  have hsub : ∀ i, (x - quadGrad a x) i = a i := by
    intro i
    unfold quadGrad
    simp only [Pi.sub_apply]
    ring
  have hzero : ∑ i, ((x - quadGrad a x) i - a i)^2 = 0 := by
    simp [hsub]
  constructor
  · show quadE a (x - quadGrad a x) = 0
    unfold quadE
    rw [hzero]
    norm_num
  · unfold quadE quadGrad nrm2
    congr 1

/-- СТРОГОЕ УБЫВАНИЕ: специализация descent_drop — при
x ≠ a шаг строго уменьшает цель (нетривиальный прогресс,
не «idle»). -/
theorem quad_drop (a x : k → ℝ) (hx : quadGrad a x ≠ 0) :
    (quadObjective a).f (x - quadGrad a x)
      < (quadObjective a).f x := by
  have hdrop := descent_drop (quadObjective a) x
    (quadGrad a x) (quadAligned a x) 1 (by norm_num)
    (by have hL1 : (quadObjective a).L = 1 := rfl
        rw [hL1]; norm_num)
  have hpos : (0:ℝ) < nrm2 (quadGrad a x) := by
    unfold nrm2
    by_contra h0
    push_neg at h0
    apply hx
    funext i
    by_contra hne
    have h1 : (0:ℝ) < (quadGrad a x i)^2 :=
      sq_pos_iff.mpr hne
    have hle : (quadGrad a x i)^2 ≤ ∑ j, (quadGrad a x j)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    linarith
  have hhalf : (1:ℝ) * (1 - (quadObjective a).L * 1 / 2)
      * nrm2 (quadGrad a x) = nrm2 (quadGrad a x) / 2 := by
    have : (quadObjective a).L = 1 := rfl
    rw [this]; ring
  rw [hhalf] at hdrop
  have hone : (fun i => 1 * quadGrad a x i) = quadGrad a x :=
    funext fun i => one_mul _
  rw [hone] at hdrop
  linarith

end Hagi.Unified.DescentCoreQuad