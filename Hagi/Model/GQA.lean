import Mathlib

/-!
# Grouped-Query Attention (источник №57: Ainslie et al.,
# "GQA: Training Generalized Multi-Query Transformer
# Models from Multi-Head Checkpoints", arXiv 2305.13248)

Идея: запросных голов n_h больше, чем KV-голов n_kv
(MQA — крайний случай n_kv = 1): KV-кэш падает в n_h/n_kv
раз при сохранении качества (эмпирический факт источника);
формализуем строгую экономию кэша и её отношение к MLA.
-/

namespace Hagi.Model.GQA

/-- KV-кэш full multi-head: длина × голов × dim. -/
def mhaKVCost (T n_h d : ℕ) : ℕ := T * n_h * d

/-- KV-кэш GQA: только n_kv KV-голов. -/
def gqaKVCost (T n_kv d : ℕ) : ℕ := T * n_kv * d

/-- ИСТОЧНИК №57, УРОВЕНЬ 1: при n_kv < n_h и T, d ≥ 1 GQA
кэш СТРОГО меньше MHA. -/
theorem gqa_kv_lt (T n_h n_kv d : ℕ) (hlt : n_kv < n_h)
    (hT : 1 ≤ T) (hd : 1 ≤ d) :
    gqaKVCost T n_kv d < mhaKVCost T n_h d := by
  have hd0 : 0 < d := by omega
  have h1 : n_kv * d < n_h * d :=
    (Nat.mul_lt_mul_right hd0).mpr hlt
  have hTpos : 0 < T := by omega
  unfold gqaKVCost mhaKVCost
  rw [Nat.mul_assoc, Nat.mul_assoc]
  exact (Nat.mul_lt_mul_left hTpos).mpr h1

/-- УРОВЕНЬ 1b: отношение кэшей = n_kv/n_h < 1. -/
theorem gqa_kv_ratio (T n_h n_kv d : ℕ) (hlt : n_kv < n_h)
    (hT : 1 ≤ T) (hd : 1 ≤ d) :
    (gqaKVCost T n_kv d : ℝ) / (mhaKVCost T n_h d : ℝ)
      = (n_kv:ℝ) / (n_h:ℝ) := by
  have hn : (0:ℝ) < (n_h:ℝ) := by
    exact_mod_cast (by omega : 1 ≤ n_h)
  have hT0 : (0:ℝ) < (T:ℝ) := by
    exact_mod_cast (by omega : 1 ≤ T)
  have hd0 : (0:ℝ) < (d:ℝ) := by
    exact_mod_cast (by omega : 1 ≤ d)
  unfold gqaKVCost mhaKVCost
  push_cast
  field_simp

/-- УРОВЕНЬ 2: MQA-КРАЙНИЙ СЛУЧАЙ — минимальный кэш при
n_kv = 1: GQA-кэш с любой группировкой ≥ MQA-кэша
(монотонность по числу KV-голов). -/
theorem gqa_kv_mono (T d n_kv n_kv' : ℕ)
    (hle : n_kv' ≤ n_kv) :
    gqaKVCost T n_kv' d ≤ gqaKVCost T n_kv d := by
  have h1 : n_kv' * d ≤ n_kv * d :=
    Nat.mul_le_mul_right d hle
  unfold gqaKVCost
  rw [Nat.mul_assoc, Nat.mul_assoc]
  exact Nat.mul_le_mul_left T h1

end Hagi.Model.GQA
