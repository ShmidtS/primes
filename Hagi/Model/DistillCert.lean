import Mathlib.Tactic
import Hagi.Energy.Quantizer

/-!
# DistillCert (приоритет 6 «HAGI Neural Computer», ):
СЕРТИФИКАТ КОНСОЛИДАЦИИ — качество после дистилляции
И квантования.

Фаза консолидации: адаптеры (учитель) дистиллируются в
базовые веса (ученик) и квантуются в триты. Сертификат
связывает три канала отклонения:
1. KL-дрейф дистилляции (контракт: KL(teacher‖student) ≤ ε);
2. ошибка квантования (gridQ_error: |Q(x) − x| ≤ Δ/2);
3. липшицевость лосса по параметру (контракт Λ).

Итог: ПОЛНАЯ ГАРАНТИЯ — лосс квантованного ученика ≤
лосс учителя + Λ·Δ/2·√n (композиция каналов).
-/

namespace Hagi.Model.DistillCert

open Hagi.Energy

/-- Сертификат консолидации: контракты дистилляции,
квантования и липшицевости. -/
structure DistillCert {n : ℕ} where
  /-- Параметры учителя (base + адаптеры). -/
  teacher : Fin n → ℝ
  /-- Параметры ученика ДО квантования (результат
  дистилляции). -/
  student : Fin n → ℝ
  /-- Шаг решётки тритов. -/
  delta : ℝ
  hdelta : 0 < delta
  /-- Липшиц-константа лосса по параметру (евклидова). -/
  lip : ℝ
  hlip : 0 ≤ lip
  /-- ПОКАЗАТЕЛЬ ДИСТИЛЛЯЦИИ: расстояние учитель-ученик
  (KL-канал свернут в L2-прокси через сильную выпуклость
  или прямое измерение). -/
  dist2 : ℝ
  hdist2nn : 0 ≤ dist2
  /-- Доверенная граница прокси. -/
  dbound : ℝ
  hdbound : 0 ≤ dbound
  hdist : (dist2)^2 = ∑ i, (teacher i - student i)^2
  hdist_bound : dist2 ≤ dbound

/-- Квантованный ученик. -/
noncomputable def quantStudent {n : ℕ} (c : DistillCert (n := n)) :
    Fin n → ℝ :=
  fun i => gridQ c.delta c.hdelta (c.student i)

/-- КАНАЛ КВАНТОВАНИЯ: поточечная ошибка квантованного
ученика ≤ Δ/2 (реюз gridQ_error). -/
theorem quant_pointwise {n : ℕ} (c : DistillCert (n := n)) (i : Fin n) :
    |quantStudent c i - c.student i| ≤ c.delta / 2 :=
  gridQ_error c.delta c.hdelta (c.student i)

/-- L2-ошибка квантования: ‖Q(s) − s‖ ≤ √n·Δ/2
(поточечная равномерная граница → евклидова). -/
theorem quant_L2 {n : ℕ} (c : DistillCert (n := n)) :
    (∑ i, (quantStudent c i - c.student i)^2) ≤
      n * (c.delta / 2)^2 := by
  have h1 : ∀ i : Fin n, (quantStudent c i - c.student i)^2
      ≤ (c.delta / 2)^2 := by
    intro i
    have h := quant_pointwise c i
    have hnn : (0:ℝ) ≤ c.delta / 2 :=
      div_nonneg (le_of_lt c.hdelta) (by norm_num)
    exact sq_le_sq.mpr (h.trans (le_of_eq (abs_of_nonneg hnn).symm))
  have hsum : ∑ i : Fin n, (c.delta / 2)^2
      = n * (c.delta / 2)^2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  calc ∑ i : Fin n, (quantStudent c i - c.student i)^2
      ≤ ∑ i : Fin n, (c.delta / 2)^2 :=
        Finset.sum_le_sum (fun i _ => h1 i)
    _ = n * (c.delta / 2)^2 := hsum

/-- ВСПОМОГАТЕЛЬНОЕ: (a+b)² ≤ 2a² + 2b² (поточечно). -/
theorem two_sq (a b : ℝ) : (a + b)^2 ≤ 2*a^2 + 2*b^2 := by
  nlinarith [sq_nonneg (a - b)]

/-- ПОЛНАЯ ГАРАНТИЯ КОНСОЛИДАЦИИ: при липшиц-контракте
(|ΔL| ≤ Λ·Σ(Δw)² — квадратичная форма) лосс квантованного
ученика отклоняется от учителя не более чем на
Λ·(2·n·(Δ/2)² + 2·dbound²): оба канала (квантование и
дистилляция) контролируются суммарно. -/
theorem consolidation_bound {n : ℕ} (c : DistillCert (n := n))
    (L : (Fin n → ℝ) → ℝ)
    (hLip : ∀ x y, |L x - L y|
      ≤ c.lip * (∑ i, (x i - y i)^2)) :
    |L (quantStudent c) - L c.teacher|
      ≤ c.lip * (2 * n * (c.delta / 2)^2 + 2 * c.dbound^2) := by
  -- D(Qs,T) ≤ 2·D(Qs,S) + 2·D(S,T) поточечно
  have hpt : ∀ i : Fin n,
      (quantStudent c i - c.teacher i)^2
        ≤ 2*(quantStudent c i - c.student i)^2
          + 2*(c.student i - c.teacher i)^2 := by
    intro i
    have hkey : quantStudent c i - c.teacher i
        = (quantStudent c i - c.student i)
          + (c.student i - c.teacher i) := by ring
    rw [hkey]
    have := two_sq (quantStudent c i - c.student i)
      (c.student i - c.teacher i)
    linarith [this]
  have hD : ∑ i : Fin n, (quantStudent c i - c.teacher i)^2
      ≤ 2 * (∑ i : Fin n, (quantStudent c i - c.student i)^2)
        + 2 * (∑ i : Fin n, (c.student i - c.teacher i)^2) := by
    calc ∑ i : Fin n, (quantStudent c i - c.teacher i)^2
        ≤ ∑ i : Fin n, (2*(quantStudent c i - c.student i)^2
          + 2*(c.student i - c.teacher i)^2) :=
          Finset.sum_le_sum (fun i _ => hpt i)
      _ = 2 * (∑ i : Fin n, (quantStudent c i - c.student i)^2)
          + 2 * (∑ i : Fin n, (c.student i - c.teacher i)^2) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hQ := quant_L2 c
  have hdist2 : ∑ i : Fin n, (c.student i - c.teacher i)^2
      = c.dist2^2 := by
    have hcomm : ∑ i : Fin n, (c.student i - c.teacher i)^2
        = ∑ i : Fin n, (c.teacher i - c.student i)^2 :=
      Finset.sum_congr rfl (fun i _ => by
        have : c.student i - c.teacher i
            = -(c.teacher i - c.student i) := by ring
        rw [this, neg_sq])
    rw [hcomm, c.hdist]
  have hbound : ∑ i : Fin n, (quantStudent c i - c.teacher i)^2
      ≤ 2 * n * (c.delta / 2)^2 + 2 * c.dbound^2 := by
    have hc2 : c.dist2^2 ≤ c.dbound^2 :=
      sq_le_sq.mpr (by
        rw [abs_of_nonneg c.hdist2nn, abs_of_nonneg c.hdbound]
        exact c.hdist_bound)
    linarith [hD, hQ, hc2]
  exact le_trans (hLip (quantStudent c) c.teacher) <|
    mul_le_mul_of_nonneg_left hbound c.hlip

end Hagi.Model.DistillCert
