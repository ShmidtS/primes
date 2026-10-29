import Mathlib

/-!
# H-Net: иерархическая byte-level токенизация (источник №37)

Источник №37: Cartesia, "From Tokens to Bytes I/II"
(cartesia.ai/blog, 2026-10-29); Merrill et al.,
"H-Net: Hierarchical Network" (arXiv 2509.06784). Ключевой
тезис: внешний BPE-токенизатор заморожен при обучении и слеп
к модели; H-Net переносит токенизацию ВНУТРЬ модели
(иерархический пул r байтов в латентные сегменты). На
данных Cartesia BPE-токен покрывает ≈4.57 байта — но
заморожен; иерархия обучает покрытие.

Формализованное ядро (строгое):
- `hier_seq_shorten`: пул r байтов в 1 латент сжимает
  последовательность ровно в r раз (T → T/r);
- `hier_attn_saving`: КВАДРАТИЧНАЯ экономия — attention на
  латентах m = T/r стоит ровно 1/r² от byte-level attention
  (c·m² = c·T²/r²): иерархия конвертирует линейное
  сокращение длины в квадратичную экономию вычислений;
- `hier_attn_saving_lt`: при r > 1, T > 0 экономия строгая.
-/

namespace Hagi.Model.HNet

/-- Пул r байтов в 1 латент сжимает длину строго
(при T > 0 < r < T). -/
theorem hier_seq_shorten (T r : ℝ) (hr : 1 < r)
    (hT : 0 < T) :
    0 < T / r ∧ T / r < T := by
  constructor
  · exact div_pos hT (by linarith)
  · rw [div_lt_iff₀ (by linarith : (0:ℝ) < r)]
    nlinarith

/-- КВАДРАТИЧНАЯ экономия: attention на латентах стоит ровно
1/r² от byte-level. -/
theorem hier_attn_saving (T r c : ℝ) (hr : 0 < r)
    (_hc : 0 ≤ c) :
    c * (T / r) ^ 2 = c * T ^ 2 / r ^ 2 := by
  field_simp

/-- При r > 1 и T > 0 экономия строгая. -/
theorem hier_attn_saving_lt (T r c : ℝ) (hr1 : 1 < r)
    (hT : 0 < T) (hc : 0 < c) :
    c * (T / r) ^ 2 < c * T ^ 2 := by
  rw [hier_attn_saving T r c (by linarith : (0:ℝ) < r) hc.le]
  have hr2 : 1 < r ^ 2 := by nlinarith
  rw [div_lt_iff₀ (by positivity : (0:ℝ) < r ^ 2)]
  have hbase : 0 < c * T ^ 2 := by positivity
  nlinarith [hbase, hr1]

/-- AM-GM для трёх неотриц чисел (выведен из взвешенного
geom_mean_le_arith_mean_weighted). -/
theorem amgm3 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x * y * z) ^ ((3:ℝ)⁻¹) ≤ (x + y + z) / 3 := by
  have hw := Real.geom_mean_le_arith_mean_weighted
    (Finset.univ : Finset (Fin 3))
    (fun _ => (1 / 3 : ℝ))
    (fun i => if i = 0 then x else if i = 1 then y else z)
    (fun i _ => by norm_num)
    (by simp)
    (fun i _ => by fin_cases i <;> simp [hx, hy, hz])
  rw [Fin.prod_univ_three, Fin.sum_univ_three] at hw
  simp at hw
  rw [show (x * y * z : ℝ) = x * (y * z) from by ring,
    Real.mul_rpow hx (mul_nonneg hy hz), Real.mul_rpow hy hz]
  field_simp
  ring_nf at hw ⊢
  linarith

/-- УРОВЕНЬ 2 No37: ОПТИМАЛЬНЫЙ РАНГ ПУЛА. Полная стоимость
иерархии cost(r) = a*T*r (локальные пулы) + b*T^2/r^2
(латентный attention) ограничена снизу
3*(a^2*b*T^4/4)^(1/3) — НЕ зависит от r (AM-GM-3 с
x = y = aTr/2, z = bT^2/r^2: r сокращается в произведении).
Оптимум r* = (2bT/a)^(1/3) пропорционален T^(1/3). -/
theorem hnet_cost_floor (a b T r : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hT : 0 < T) (hr : 0 < r) :
    3 * ((a * T * r / 2) * (a * T * r / 2) * (b * T ^ 2 / r ^ 2))
        ^ ((3:ℝ)⁻¹) ≤ a * T * r + b * T ^ 2 / r ^ 2 := by
  have ham := amgm3 (a * T * r / 2) (a * T * r / 2) (b * T ^ 2 / r ^ 2)
    (by positivity) (by positivity) (by positivity)
  have hsplit : a * T * r / 2 + a * T * r / 2 + b * T ^ 2 / r ^ 2
      = a * T * r + b * T ^ 2 / r ^ 2 := by ring
  rw [hsplit] at ham
  have hstep : 3 * ((a * T * r / 2 * (a * T * r / 2) * (b * T ^ 2 / r ^ 2)) ^ ((3:ℝ)⁻¹))
      ≤ 3 * ((a * T * r + b * T ^ 2 / r ^ 2) / 3) :=
    mul_le_mul_of_nonneg_left ham (by norm_num)
  have hcancel : 3 * ((a * T * r + b * T ^ 2 / r ^ 2) / 3)
      = a * T * r + b * T ^ 2 / r ^ 2 := by
    field_simp
  rw [hcancel] at hstep
  linarith [hstep]

end Hagi.Model.HNet

