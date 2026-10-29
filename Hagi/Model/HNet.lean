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

end Hagi.Model.HNet
