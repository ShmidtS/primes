/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Model.LoRA
import Hagi.Model.Perceiver

/-!
# Семейство внимания (объединённое)

GQA, MLA, MoD, FlashAttention, ALiBi, SWA, StreamingLLM,
RoPE — механизмы и позиции внимания. Слит из восьми
модулей; namespace-блоки и имена деклараций сохранены.
-/

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

/-!
# Mixture-of-Depths (источник №55: Raposo et al.,
# "Mixture-of-Depths: Dynamically allocating compute in
# transformer LMs", arXiv 2404.02258)

Идея: каждый слой обрабатывает только top-k из n токенов
(остальные — residual-обход). Стоимость слоя падает с n до
k; на L слоях экономия ЛИНЕЙНА по глубине. Формализуем:
строгую экономию слоя и её накопление по глубине.
-/

namespace Hagi.Model.MoD

/-- Стоимость dense-слоя: все n токенов. -/
def denseLayerCost (n d : ℕ) : ℕ := n * d

/-- Стоимость MoD-слоя: k отобранных токенов. -/
def modLayerCost (k d : ℕ) : ℕ := k * d

/-- Полная стоимость L dense-слоёв. -/
def denseStackCost (L n d : ℕ) : ℕ := L * denseLayerCost n d

/-- Полная стоимость L MoD-слоёв. -/
def modStackCost (L k d : ℕ) : ℕ := L * modLayerCost k d

/-- ИСТОЧНИК №55, УРОВЕНЬ 1: MoD-слой строго дешевле dense
при k < n и d ≥ 1. -/
theorem mod_layer_cost_lt (n k d : ℕ) (hk : k < n)
    (hd : 1 ≤ d) :
    modLayerCost k d < denseLayerCost n d := by
  unfold modLayerCost denseLayerCost
  exact Nat.mul_lt_mul_of_lt_of_le hk (le_refl d)
    (by omega)

/-- УРОВЕНЬ 2: ГЛУБИНА УМНОЖАЕТ ЭКОНОМИЮ — на стеке из L ≥ 1
слоёв экономия MoD-стека равна L-кратной послойной экономии
и строго положительна при k < n, d ≥ 1. -/
theorem mod_stack_saving (L n k d : ℕ) (hL : 1 ≤ L)
    (hk : k < n) (hd : 1 ≤ d) :
    0 < denseStackCost L n d - modStackCost L k d
      ∧ denseStackCost L n d - modStackCost L k d
        = L * (denseLayerCost n d - modLayerCost k d) := by
  have hlayer := mod_layer_cost_lt n k d hk hd
  unfold denseLayerCost modLayerCost at hlayer
  unfold denseStackCost modStackCost denseLayerCost
    modLayerCost
  have hnd : 0 < n * d - k * d := by omega
  have hdistr : L * (n * d - k * d)
      = L * (n * d) - L * (k * d) := Nat.mul_sub L _ _
  have hpos : 0 < L * (n * d - k * d) :=
    Nat.mul_pos hL hnd
  constructor
  · omega
  · omega

end Hagi.Model.MoD

/-!
# FlashAttention — IO-awareness (источник №63: Dao et
# al., "FlashAttention: Fast and Memory-Efficient Exact
# Attention with IO-Awareness", arXiv 2205.14135)

Идея: точное внимание БЕЗ материализации N×N-матрицы —
tiling с headdim d и SRAM-размером M. HBM-IO падает с
Θ(N·d + N²) стандартного внимания к Θ(N²d²/M) у
FlashAttention. Формализуем честную арифметику IO-выигрыша
при M > d (SRAM вмещает тайл) и монотонность по M: больше
быстрой памяти — меньше IO.
-/

namespace Hagi.Model.FlashAttention

/-- IO стандартного внимания: N·d + N² (материализация). -/
noncomputable def stdIO (N d : ℝ) : ℝ := N * d + N * N

/-- IO FlashAttention: N²·d²/M. -/
noncomputable def flashIO (N d M : ℝ) : ℝ := N * N * (d * d) / M

/-- ИСТОЧНИК №63, УРОВЕНЬ 1 (честная гипотеза): при
M > d² ≥ 1, N ≥ 1: IO FlashAttention СТРОГО меньше IO
стандартного внимания. Оговорка честности: при M лишь
слегка больше d (M ∈ (d, d²)) и больших N tiling НЕ даёт
выигрыша против материализации — выгодность требует
SRAM-размера больше КВАДРАТА headdim (эмпирика источника:
M на порядки больше d²). -/
theorem flash_io_lt (N d M : ℝ) (hd : 1 ≤ d)
    (hM : d * d < M) (hN : 1 ≤ N) :
    flashIO N d M < stdIO N d := by
  have hN0 : 0 < N := by linarith
  have hM0 : 0 < M := lt_of_le_of_lt (by
    have : 0 ≤ d * d := mul_nonneg (by linarith) (by linarith)
    linarith) hM
  have hkey : N * N * (d * d) < N * N * M := by
    have hnn : 0 < N * N := by nlinarith
    exact mul_lt_mul_of_pos_left hM hnn
  have h1 : flashIO N d M < N * N := by
    rw [flashIO, div_lt_iff₀ hM0]
    exact hkey
  unfold stdIO
  have hnd : 0 < N * d := by nlinarith
  linarith

/-- УРОВЕНЬ 2: МОНОТОННОСТЬ ПО M — IO FlashAttention НЕ
растёт с размером быстрой памяти (больше SRAM — не хуже). -/
theorem flash_io_antitone (N d M M' : ℝ) (hpos : 0 < N * N * (d * d))
    (hM : 0 < M) (hM' : M ≤ M') :
    flashIO N d M' ≤ flashIO N d M := by
  have hM'0 : 0 < M' := lt_of_lt_of_le hM hM'
  rw [flashIO, flashIO, div_le_div_iff₀ hM'0 hM]
  nlinarith [hpos]

end Hagi.Model.FlashAttention

/-!
# ALiBi — Attention with Linear Biases (источник №60:
# Press et al., "Train Short, Test Long", arXiv 2108.12409)

Идея: вместо обучаемых позиционных эмбеддингов —
ДОБАВКА к логитам внимания, линейно убывающая по
расстоянию: bias(d) = −m·d. Формализуем монотонность
bias и экспоненциальное затухание вклада дальних позиций
в attention-вес (через softmax-ядро exp).
-/

namespace Hagi.Model.ALiBi

/-- Линейный bias по расстоянию d с наклоном m. -/
def alibiBias (m d : ℝ) : ℝ := -m * d

/-- ИСТОЧНИК №60, УРОВЕНЬ 1: bias МОНОТОННО УБЫВАЕТ по
расстоянию — дальние позиции получают строго меньший
(более отрицательный) сдвиг логита. -/
theorem alibi_bias_anti (m d1 d2 : ℝ) (hm : 0 ≤ m)
    (hd : d1 ≤ d2) :
    alibiBias m d2 ≤ alibiBias m d1 := by
  unfold alibiBias
  have hdm : 0 ≤ m * (d2 - d1) := mul_nonneg hm (by linarith)
  nlinarith [hdm]

/-- УРОВЕНЬ 1b: НЕПОЛОЖИТЕЛЬНОСТЬ bias при неотрицательных
наклоне и расстоянии. -/
theorem alibi_bias_nonpos (m d : ℝ) (hm : 0 ≤ m)
    (hd : 0 ≤ d) :
    alibiBias m d ≤ 0 := by
  unfold alibiBias
  nlinarith [mul_nonneg hm hd]

/-- УРОВЕНЬ 2: ЭКСПОНЕНЦИАЛЬНОЕ ЗАТУХАНИЕ attention-ядра —
softmax-вклад позиции на расстоянии d2 не превосходит
вклада более близкой d1 (нормировочный знаменатель общий):
exp(−m·d2) ≤ exp(−m·d1) при d1 ≤ d2, m ≥ 0. Дальние
токены экспоненциально подавляются — экстраполяция
длины «бесплатна» (train short, test long). -/
theorem alibi_kernel_decay (m d1 d2 : ℝ) (hm : 0 ≤ m)
    (hd : d1 ≤ d2) :
    Real.exp (alibiBias m d2) ≤ Real.exp (alibiBias m d1) := by
  exact (Real.exp_le_exp).mpr (alibi_bias_anti m d1 d2 hm hd)

/-- УРОВЕНЬ 2b: СТРОГОЕ затухание при положительном
наклоне и строгом росте расстояния. -/
theorem alibi_kernel_decay_lt (m d1 d2 : ℝ) (hm : 0 < m)
    (hd : d1 < d2) :
    Real.exp (alibiBias m d2) < Real.exp (alibiBias m d1) := by
  refine (Real.exp_lt_exp).mpr ?_
  unfold alibiBias
  have hdm : 0 < m * (d2 - d1) := mul_pos hm (by linarith)
  nlinarith [hdm]

end Hagi.Model.ALiBi

/-!
# Sliding Window Attention (источник №56: Jiang et al.,
# "Mistral 7B", arXiv 2310.06825)

Идея: каждый токен посещает только окно из w предыдущих
(и себя): стоимость внимания ~ n·(2w+1) вместо n². При
2w+1 < n — строгая экономия, линейная по длине окна;
монотонность: уменьшение окна строго уменьшает стоимость.
-/

namespace Hagi.Model.SWA

/-- Полная стоимость dense self-attention: n² пар. -/
def denseAttnCost (n : ℕ) : ℕ := n * n

/-- Стоимость sliding-window: каждый токен ≤ (2w+1) пар. -/
def swaCost (n w : ℕ) : ℕ := n * (2 * w + 1)

/-- ИСТОЧНИК №56, УРОВЕНЬ 1: при окне меньше входа
(2w + 1 < n) SWA строго дешевле dense self-attention. -/
theorem swa_cost_lt (n w : ℕ) (h : 2 * w + 1 < n) :
    swaCost n w < denseAttnCost n := by
  unfold swaCost denseAttnCost
  rw [Nat.mul_comm n (2 * w + 1), Nat.mul_comm n n]
  exact (Nat.mul_lt_mul_right
    (Nat.pos_of_ne_zero (by omega))).mpr h

/-- УРОВЕНЬ 1b: отношение стоимостей < 1 (нормированная
форма экономии). -/
theorem swa_cost_ratio_lt (n w : ℕ) (h : 2 * w + 1 < n)
    (hn : 1 ≤ n) :
    (swaCost n w : ℝ) / (denseAttnCost n : ℝ) < 1 := by
  have hlt := swa_cost_lt n w h
  have hpos : (0:ℝ) < (denseAttnCost n : ℝ) := by
    unfold denseAttnCost
    norm_num
    omega
  exact (div_lt_one hpos).mpr (by exact_mod_cast hlt)

/-- УРОВЕНЬ 2: МОНОТОННОСТЬ ПО ОКНУ — уменьшение окна
СТРОГО уменьшает стоимость: w' < w → SWA(w') < SWA(w).
Роутинг вычислений окном управляет стоимостью монотонно. -/
theorem swa_cost_mono (n w w' : ℕ) (hn : 1 ≤ n)
    (hw' : w' < w) :
    swaCost n w' < swaCost n w := by
  unfold swaCost
  have h1 : 2 * w' + 1 < 2 * w + 1 := by omega
  rw [Nat.mul_comm n (2 * w' + 1), Nat.mul_comm n (2 * w + 1)]
  exact (Nat.mul_lt_mul_right
    (Nat.pos_of_ne_zero (by omega))).mpr h1

end Hagi.Model.SWA

/-!
# StreamingLLM — attention sinks (источник №61: Xiao et
# al., "Efficient Streaming Language Models with
# Attention Sinks", arXiv 2309.17453)

Идея: KV-кэш = несколько первых токенов-«якорей» (sink) +
скользящее окно последних позиций (ограничено w). Память
НЕ растёт с длиной обрабатываемой последовательности:
стриминг сколь угодно длинного входа при кэше ≤ n_s + w.
Формализуем: равномерная ограниченность кэша (для ЛЮБОГО
горизонта T), строгая экономия против полного кэша и
линейный рост сэкономленной памяти по длине.
-/

namespace Hagi.Model.StreamingLLM

/-- KV-кэш StreamingLLM на горизонте T: n_s якорей +
окно min(w, T). -/
def streamCache (T n_s w : ℕ) : ℕ := n_s + min w T

/-- Полный KV-кэш длины T. -/
def fullCache (T : ℕ) : ℕ := T

/-- ИСТОЧНИК №61, УРОВЕНЬ 1: кэш РАВНОМЕРНО ОГРАНИЧЕН —
при ЛЮБОМ горизонте T размер кэша не превосходит n_s + w:
память не растёт с длиной входа (стриминг неограниченного
входа при фиксированной памяти). -/
theorem stream_bounded (T n_s w : ℕ) :
    streamCache T n_s w ≤ n_s + w := by
  have hmin := Nat.min_le_right w T
  unfold streamCache
  omega

/-- УРОВЕНЬ 1b: при T > n_s + w StreamingLLM СТРОГО
экономит память против полного кэша. -/
theorem stream_mem_lt (T n_s w : ℕ) (h : n_s + w < T) :
    streamCache T n_s w < fullCache T := by
  have hmin : min w T = w := Nat.min_eq_left (by omega)
  unfold streamCache fullCache
  rw [hmin]
  omega

/-- УРОВЕНЬ 2: ЭКОНОМИЯ РАСТЁТ ЛИНЕЙНО по длине (при
T ≥ n_s + w): каждый новый токен увеличивает
сэкономленную память ровно на 1. -/
theorem stream_saving_step (T n_s w : ℕ)
    (hT : n_s + w ≤ T) :
    fullCache (T + 1) - streamCache (T + 1) n_s w
      = (fullCache T - streamCache T n_s w) + 1 := by
  have hmin1 : min w T = w := Nat.min_eq_left (by omega)
  have hmin2 : min w (T + 1) = w :=
    Nat.min_eq_left (by omega)
  unfold fullCache streamCache
  rw [hmin1, hmin2]
  omega

end Hagi.Model.StreamingLLM

/-!
# RoPE: вращательное позиционное кодирование (источник №24)

Источник №24: Su et al., "RoFormer" (arXiv 2104.09864):
позиционное кодирование вращением (комплексное
представление: 2D-вращение ≅ умножение на e^{iθ}).

Формализованное ядро:
- `rot`: вращение позиции k — (e^{iθ})^k;
- `rot_normSq_one`: единичность вращения (normSq = 1,
  через cos²+sin²);
- `rope_normSq_preserved`: вращение сохраняет normSq
  вектора — позиционное кодирование ИЗОМЕТРИчно: меняется
  только фаза, информация токена не искажается.
-/

namespace Hagi.Model.RoPE

open Complex

/-- Вращение на угол k·θ. -/
noncomputable def rot (k : ℕ) (theta : ℝ) : ℂ :=
  (exp (theta * I)) ^ k

/-- Единичность вращения: normSq (rot k θ) = 1. -/
theorem rot_normSq_one (k : ℕ) (theta : ℝ) :
    normSq (rot k theta) = 1 := by
  have h1 : normSq (exp (theta * I)) = 1 := by
    simp only [Complex.normSq_apply, Complex.exp_re, Complex.exp_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    nlinarith [Real.cos_sq_add_sin_sq theta]
  unfold rot
  induction k with
  | zero => simp
  | succ t ih =>
      rw [pow_succ, Complex.normSq_mul, h1, ih, mul_one]

/-- ИЗОМЕТРИЧНОСТЬ: вращение сохраняет normSq вектора —
ядро корректности RoPE (фаза меняется, модуль нет). -/
theorem rope_normSq_preserved (u : ℂ) (k : ℕ) (theta : ℝ) :
    normSq (rot k theta * u) = normSq u := by
  rw [Complex.normSq_mul, rot_normSq_one, one_mul]


/-- «Внутреннее произведение» RoPE-пары на позициях (m,n):
Re-часть (star w_m·u)·(w_n·v). -/
noncomputable def ropeInner (u v : ℂ) (m n : ℕ) (theta : ℝ) : ℝ :=
  re (star (rot m theta * u) * (rot n theta * v))

/-- Локальная связь: star z * z = normSq z. -/
private theorem star_mul_self (z : ℂ) :
    star z * z = normSq z := by
  have hstar : star z = Complex.mk z.re (-z.im) := rfl
  rw [hstar, Complex.normSq_apply]
  refine Complex.ext ?_ ?_
  · simp only [Complex.mul_re, Complex.ofReal_re]
    simp
  · simp only [Complex.mul_im, Complex.ofReal_im]
    simp
    ring

/-- ОТНОСИТЕЛЬНОСТЬ (ядро RoPE, уровень 2): одновременный
сдвиг d обеих позиций НЕ меняет внутреннего произведения —
взаимодействие токенов зависит только от их ВЗАИМНОГО
расположения. star w_d·w_d = 1 (вращение единично) —
d-экспоненты сокращаются. -/
theorem rope_shift_invariant (u v : ℂ) (m n d : ℕ) (theta : ℝ) :
    ropeInner u v (m + d) (n + d) theta
      = ropeInner u v m n theta := by
  have hexp : (exp (theta * I)) ^ (m + d)
      = (exp (theta * I)) ^ m * (exp (theta * I)) ^ d :=
    pow_add _ m d
  have hexp2 : (exp (theta * I)) ^ (n + d)
      = (exp (theta * I)) ^ n * (exp (theta * I)) ^ d :=
    pow_add _ n d
  set W : ℂ := (exp (theta * I)) with hW
  -- единичность вращения d
  have hunit : star (W ^ d) * W ^ d = 1 := by
    have hrd : W ^ d = rot d theta := by rw [hW, rot]
    rw [hrd, star_mul_self, rot_normSq_one]
    norm_num
  unfold ropeInner
  rw [rot, rot, rot, rot, hexp, hexp2]
  simp only [star_mul]
  calc (star u * (star (W ^ d) * star (W ^ m)) * (W ^ n * W ^ d * v)).re
      = ((star u * star (W ^ m) * (W ^ n * v))
          * (star (W ^ d) * W ^ d)).re := by
        apply congrArg Complex.re
        ring
    _ = ((star u * star (W ^ m) * (W ^ n * v)) * 1).re := by
        rw [hunit]
    _ = (star u * star (W ^ m) * (W ^ n * v)).re := by
        simp

end Hagi.Model.RoPE
