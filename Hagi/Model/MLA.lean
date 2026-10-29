import Mathlib
import Hagi.Model.LoRA

/-!
# MLA: латентный KV-кэш (источник №42)

Источник №42: DeepSeek-AI, "DeepSeek-V2: A Strong, Economical
and Efficient Mixture-of-Experts Language Model"
(arXiv 2405.04434). Multi-head Latent Attention: K и V
каждой головы восстанавливаются из общего низкорангового
латента c_i ∈ ℝ^{d_c} (d_c ≪ d): KV-кэш хранит ТОЛЬКО
латент — память на токен падает с d до d_c.

Формализованное ядро (строгое):
- `mla_cache_full`: полный кэш (K и V напрямую) — память
  ∝ 2·n·d;
- `mla_cache_latent`: латентный кэш — память ∝ n·d_c
  (восстановление k_i = A_k·c_i, v_i = A_v·c_i — та же
  низкоранговая структура, что LoRA №35);
- `mla_cache_saving`: при d_c < d латентный кэш СТРОГО
  меньше: n·d_c < 2·n·d — экономия растёт с длиной
  контекста.
-/

namespace Hagi.Model.MLA

variable {n dc d : ℕ}

/-- Полный KV-кэш: n токенов × (K и V) размерности d. -/
noncomputable def cacheFull (n d : ℕ) : ℝ := 2 * n * d

/-- Латентный кэш: n токенов × латент dc. -/
noncomputable def cacheLatent (n dc : ℕ) : ℝ := n * dc

/-- Экономия: латентный кэш строго меньше полного при
dc < d. -/
theorem mla_cache_saving (n dc d : ℕ) (hn : 0 < n)
    (hdc : dc < d) :
    cacheLatent n dc < cacheFull n d := by
  unfold cacheLatent cacheFull
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hdcR : ((dc : ℕ) : ℝ) < ((d : ℕ) : ℝ) := by
    exact_mod_cast hdc
  have hnd : (0 : ℝ) ≤ ((n : ℝ)) * ((d : ℕ) : ℝ) := by
    positivity
  nlinarith [hnR, hdcR, hnd]

end Hagi.Model.MLA
