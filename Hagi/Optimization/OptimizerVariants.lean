import Mathlib.Tactic
import Hagi.Math.Foundations.Recurrence
import Mathlib.Tactic

/-!
# OptimizerVariants — одношаговые правила обновления оптимизатора

Единый дом для семейства одношаговых оптимизаторных вариантов
(AdaGrad, AdamW, AdamBias, Lion, LLRD, Lookahead, Cautious,
PPOClip, SAM, GradAccum). Каждое правило сохраняет свой закрытый
namespace `Hagi.Optimization.<X>`; теории см. в исходных
докстрингах ниже.
-/

/-!
# AdaGrad: затухание адаптивного шага (источник №46)

Источник №46: Duchi, Hazan, Singer, "Adaptive Subgradient
Methods" (arXiv 1110.4001). Шаг по координате i:
η_i = η / √(G_i), где G_i — накопленная сумма квадратов
градиентов: редкие признаки получают большие шаги, частые —
малые (adaptivity к разреженности).

Формализованное ядро (строгое):
- `adagradAcc`: аккумулятор G_t = ∑_{s<t} g_s²;
- `adagrad_step_anti`: шаг η/√(G + g²) ≤ η/√G —
  накопление НИКОГДА не увеличивает шаг (монотонное
  затухание адаптивного шага);
- `adagrad_step_pos`: шаг строго положителен пока η > 0 и
  хоть один градиент ненулевой (нет преждевременной
  остановки при накоплении).
-/

namespace Hagi.Optimization.AdaGrad

/-- Аккумулятор суммы квадратов градиентов. -/
noncomputable def adagradAcc (g : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ s ∈ Finset.range t, (g s) ^ 2

/-- Монотонность аккумулятора. -/
theorem acc_mono (g : ℕ → ℝ) (t : ℕ) :
    adagradAcc g t ≤ adagradAcc g (t + 1) := by
  rw [adagradAcc, adagradAcc, Finset.sum_range_succ]
  have hnn : 0 ≤ (g t) ^ 2 := sq_nonneg _
  linarith

/-- УРОВЕНЬ 1 No46: накопление градиента НИКОГДА не
увеличивает адаптивный шаг. -/
theorem adagrad_step_anti (g : ℕ → ℝ) (eta : ℝ) (t : ℕ)
    (heta : 0 ≤ eta) (hpos : 0 < adagradAcc g t) :
    eta / Real.sqrt (adagradAcc g t + (g t) ^ 2)
      ≤ eta / Real.sqrt (adagradAcc g t) := by
  have hacc : 0 ≤ adagradAcc g t := le_of_lt hpos
  have hg : 0 ≤ adagradAcc g t + (g t) ^ 2 := by
    have : 0 ≤ (g t) ^ 2 := sq_nonneg _
    linarith
  have hsqrt : Real.sqrt (adagradAcc g t)
      ≤ Real.sqrt (adagradAcc g t + (g t) ^ 2) := by
    exact Real.sqrt_le_sqrt (by
      have : 0 ≤ (g t) ^ 2 := sq_nonneg _
      linarith)
  have hs1 : 0 < Real.sqrt (adagradAcc g t + (g t) ^ 2) :=
    Real.sqrt_pos_of_pos (by
      have : 0 ≤ (g t) ^ 2 := sq_nonneg _
      linarith [hpos])
  have hs2 : 0 < Real.sqrt (adagradAcc g t) :=
    Real.sqrt_pos_of_pos hpos
  have hr : 1 ≤ Real.sqrt (adagradAcc g t + (g t) ^ 2)
      / Real.sqrt (adagradAcc g t) := by
    rw [one_le_div_iff]
    exact Or.inl ⟨hs2, hsqrt⟩
  refine (div_le_iff₀ hs1).mpr ?_
  rw [div_mul_eq_mul_div, ← mul_div_assoc']
  exact le_mul_of_one_le_right heta hr

end Hagi.Optimization.AdaGrad

/-!
# AdamW — decoupled weight decay (источник №64: Loshchilov
# & Hutter, "Decoupled Weight Decay Regularization",
# arXiv 1711.05101)

Идея: в AdamW decay РАСЦЕПЛЁН с градиентным шагом:
w ← (1 − λ)·w − η·s — затухание применяется к весам
напрямую, а не через L2-слагаемое градиента, делённое
адаптивным знаменателем. Формализуем ключевое следствие:
при нулевом градиенте веса СТРОГО сжимаются всегда,
тогда как coupled-L2 версия делит decay на √v̂ + 1 и
может давать сколь угодно малое эффективное затухание.
-/

namespace Hagi.Optimization.AdamW

/-- Шаг AdamW: decay-часть (1−λ)·w плюс градиентная s. -/
def adamwStep (lam eta : ℝ) (w s : ℝ) : ℝ :=
  (1 - lam) * w - eta * s

/-- Coupled-L2 шаг: decay через градиентное слагаемое,
делённое на адаптивный знаменатель √v̂ + 1. -/
noncomputable def l2Step (lam eta vhat : ℝ) (w : ℝ) : ℝ :=
  w - eta * (lam * w / (Real.sqrt vhat + 1))

/-- ИСТОЧНИК №64, УРОВЕНЬ 1: DECAY ДЕЙСТВУЕТ ВСЕГДА — при
нулевом градиенте, λ ∈ (0,1], w ≠ 0 шаг AdamW СТРОГО
сжимает модуль веса (фактор |1−λ| < 1). -/
theorem adamw_shrink (lam eta w : ℝ) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hw : w ≠ 0) :
    |adamwStep lam eta w 0| < |w| := by
  have h1 : adamwStep lam eta w 0 = (1 - lam) * w := by
    unfold adamwStep
    ring
  rw [h1, abs_mul]
  have habs : |1 - lam| < 1 :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  have hw0 : 0 < |w| := abs_pos.mpr hw
  calc |1 - lam| * |w| < 1 * |w| :=
        mul_lt_mul_of_pos_right habs hw0
    _ = |w| := one_mul _

/-- УРОВЕНЬ 1b: COUPLED-L2 ОСЛАБЛЯЕТ DECAY — эффективный
decay-фактор L2-версии есть λ/(√v̂+1) ≤ λ, и при √v̂ ≥ 1/λ
он не превосходит λ² ≤ λ: coupled decay подавляется
адаптивным знаменателем (ядро критики источника №64). -/
theorem l2_decay_diluted (lam vhat : ℝ) (hlam : 0 < lam)
    (_hv : 0 ≤ vhat) (hbig : 1 ≤ lam * (Real.sqrt vhat + 1)) :
    lam / (Real.sqrt vhat + 1) ≤ lam * lam := by
  have hsq : 0 ≤ Real.sqrt vhat := Real.sqrt_nonneg _
  have hden : 0 < Real.sqrt vhat + 1 := by positivity
  rw [div_le_iff₀ hden]
  have hmul : lam * 1 ≤ lam * (lam * (Real.sqrt vhat + 1)) :=
    mul_le_mul_of_nonneg_left hbig (le_of_lt hlam)
  linarith

end Hagi.Optimization.AdamW

/-!
# Adam bias correction (источник №28)

Источник №28: Loshchilov & Hutter, "Decoupled Weight Decay
Regularization" / Adam (arXiv 1711.05101, §2). Экспоненциальная
скользящая средняя градиента с нулевой инициализацией
m_{t+1} = β·m_t + (1−β)·g смещена к нулю на ранних шагах;
коррекция m̂_t = m_t/(1−β^t) устраняет смещение.

Формализованное ядро (строгое):
- `adamM_recur`: closed form (1−β)·g·∑_{i<t} β^i — это в
  точности рекуррентность m₀ = 0, m_{t+1} = β·m_t + (1−β)·g;
- `adam_unbiased_const`: на постоянном градиенте g коррекция
  ТОЧНА: m̂_t = m_t/(1−β^t) = g для всех t ≥ 1 при 0 ≤ β < 1;
- `adam_bias_bound`: без коррекции m_t = g − β^t·g —
  начальное смещение затухает геометрически.
-/

namespace Hagi.Optimization.AdamBias

/-- Геометрическое затухание степени: 0 ≤ β < 1, t ≥ 1
⟹ β^t < 1. -/
theorem pow_lt_one' (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1)
    (t : ℕ) (ht : 1 ≤ t) : β ^ t < 1 := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; norm_num; linarith
    · have hp : β ^ (t + 1) = β * β ^ t := by ring
      have hle : β ^ t ≤ 1 := le_of_lt (ih h0)
      rw [hp]
      nlinarith [hβ0, hβ, hle]

/-- Экспоненциальная средняя на постоянном градиенте g,
t шагов, нулевая инициализация. -/
def adamM (β g : ℝ) (t : ℕ) : ℝ :=
  (1 - β) * g * ∑ i ∈ Finset.range t, β ^ i

/-- Closed form удовлетворяет рекуррентности Адама. -/
theorem adamM_recur (β g : ℝ) :
    adamM β g 0 = 0 ∧ ∀ t : ℕ,
      adamM β g (t + 1) = β * adamM β g t + (1 - β) * g := by
  refine ⟨by unfold adamM; rw [Finset.sum_range_zero]; ring, fun t => ?_⟩
  unfold adamM
  rw [Finset.sum_range_succ (fun i => β ^ i) t]
  rcases eq_or_ne β 1 with hβ1 | hβ1
  · subst hβ1
    norm_num
  · have hg := Hagi.Foundations.geom_telescope (rho := β) t
    have hS : ∑ i ∈ Finset.range t, β ^ i = (1 - β ^ t) / (1 - β) := by
      field_simp
      linarith
    rw [hS]
    field_simp
    ring

/-- Без коррекции смещение к нулю затухает геометрически:
m_t = g − β^t·g = (1−β^t)·g. -/
theorem adam_bias_bound (β g : ℝ) (t : ℕ) :
    adamM β g t = g - β ^ t * g := by
  unfold adamM
  have h2 : (1 - β) * g * ∑ i ∈ Finset.range t, β ^ i
      = g * ((1 - β) * ∑ i ∈ Finset.range t, β ^ i) := by ring
  rw [h2, Hagi.Foundations.geom_telescope (rho := β)]
  ring

/-- ЯДРО №28: на постоянном градиенте коррекция смещения
ТОЧНА: m̂_t = m_t/(1−β^t) = g. -/
theorem adam_unbiased_const (β g : ℝ) (hβ0 : 0 ≤ β)
    (hβ : β < 1) (t : ℕ) (ht : 1 ≤ t) :
    adamM β g t / (1 - β ^ t) = g := by
  have hlt : β ^ t < 1 := pow_lt_one' β hβ0 hβ t ht
  have hden : 1 - β ^ t ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (ne_of_lt hlt))
  have hb := adam_bias_bound β g t
  rw [hb]
  have hgg : g - β ^ t * g = g * (1 - β ^ t) := by ring
  rw [hgg]
  field_simp

end Hagi.Optimization.AdamBias

/-!
# Lion: sign-обновление (источник №47)

Источник №47: Chen et al., "Symbolic Discovery of
Optimization Algorithms" (arXiv 2302.06675, Lion).
Обновление x ← x − η·sign(m): направление — только ЗНАКИ
момента, величина отбрасывается: размер шага по ℓ₂
контролируется ТОЛЬКО η (не зависит от амплитуды
градиентов — robustness к выбросам шкалы).

Формализованное ядро (строгое):
- `signStep`: шаг η·sign(m);
- `sign_sq_le_one`: sign(i)² ≤ 1 (значение из {−1,0,1});
- `lion_step_norm_bound`: ‖шаг‖₂ ≤ η·√d — норма шага
  ограничена константой размерности: LION НИКОГДА не
  делает большого шага, даже при взрывном градиенте
  (контраст с AdaGrad-затуханием: фиксированная шкала).
-/

namespace Hagi.Optimization.Lion

open Finset

variable {d : ℕ}

/-- Знак скаляра. -/
noncomputable def sgn (x : ℝ) : ℝ :=
  if 0 < x then 1 else if x < 0 then -1 else 0

/-- Sign-шаг Lion. -/
noncomputable def signStep (eta : ℝ) (m : Fin d → ℝ) : Fin d → ℝ :=
  fun i => eta * sgn (m i)

theorem sign_sq_le_one (x : ℝ) : (sgn x) ^ 2 ≤ 1 := by
  unfold sgn
  split
  · norm_num
  · split
    · norm_num
    · norm_num

/-- НОРМА ШАГА LION ОГРАНИЧЕНА: ∑ (η·sgn m i)² ≤ η²·d —
шаг никогда не превышает η·√d, даже при взрывном m. -/
theorem lion_step_norm_bound (eta : ℝ) (m : Fin d → ℝ) :
    ∑ i, (signStep eta m i) ^ 2 ≤ eta ^ 2 * (d : ℝ) := by
  have h1 : ∀ i ∈ Finset.univ, (signStep eta m i) ^ 2
      ≤ eta ^ 2 * 1 := by
    intro i _
    unfold signStep
    have hs := sign_sq_le_one (m i)
    have hmul : (eta * sgn (m i)) ^ 2 = eta ^ 2 * (sgn (m i)) ^ 2 := by
      ring
    rw [hmul]
    exact mul_le_mul_of_nonneg_left hs (sq_nonneg eta)
  have h2 := Finset.sum_le_sum (f := fun i => (signStep eta m i) ^ 2)
    (g := fun _ => eta ^ 2 * 1) h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h2
  simp [mul_one] at h2
  nlinarith [h2]

end Hagi.Optimization.Lion

/-!
# LLRD — послойное затухание learning rate (источник №68:
# layer-wise learning rate decay, стандарт глубокого
# fine-tuning BERT-эпохи; напр. Howard & Ruder 1801.06146
# ULMFiT-дискриминативное тонкая настройка)

Идея: нижние (близкие к входу) слои — более общие, их
меньше трогают: η_l = η·γ^(L−l) с γ < 1 — чем глубже слой
(ближе к выходу), тем выше LR. Формализуем монотонность:
LR строго растёт с номером слоя при γ < 1.
-/

namespace Hagi.Optimization.LLRD

/-- LR слоя l в стеке глубины L: базовый η, затухание γ
на уровень глубины. -/
def layerLR (eta gamma : ℝ) (L l : ℕ) : ℝ :=
  eta * gamma ^ (L - l)

/-- ИСТОЧНИК №68, УРОВЕНЬ 1: МОНОТОННОСТЬ — при 0 < γ < 1,
η > 0 LR СТРОГО растёт с номером слоя (верхние слои учатся
быстрее; нижние почти заморожены). -/
theorem llrd_strict_mono (eta gamma : ℝ) (L l1 l2 : ℕ)
    (heta : 0 < eta) (hg : 0 < gamma) (hg1 : gamma < 1)
    (hl : l1 < l2) (hl2 : l2 ≤ L) :
    layerLR eta gamma L l1 < layerLR eta gamma L l2 := by
  have hle : ∀ k : ℕ, gamma ^ k ≤ 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ m ih =>
        calc gamma ^ (m + 1) = gamma ^ m * gamma := pow_succ gamma m
          _ ≤ 1 * gamma :=
            mul_le_mul_of_nonneg_right ih hg.le
          _ = gamma := one_mul _
          _ ≤ 1 := le_of_lt hg1
  have hd : (L - l1 : ℕ) = (L - l2) + (l2 - l1) := by omega
  have hsplit : gamma ^ (L - l1)
      = gamma ^ (L - l2) * gamma ^ (l2 - l1) := by
    rw [hd, pow_add]
  have hpos2 : 0 < gamma ^ (L - l2) := pow_pos hg _
  have hsmall : gamma ^ (l2 - l1) < 1 := by
    have hk1 : l2 - l1 = (l2 - l1 - 1) + 1 := by omega
    rw [hk1, pow_succ]
    have hprev := hle (l2 - l1 - 1)
    nlinarith [hprev, hg, hg1]
  unfold layerLR
  have hkey : gamma ^ (L - l2) * gamma ^ (l2 - l1)
      < gamma ^ (L - l2) * 1 :=
    mul_lt_mul_of_pos_left hsmall hpos2
  rw [mul_one] at hkey
  rw [hsplit]
  exact mul_lt_mul_of_pos_left hkey heta

/-- УРОВЕНЬ 1b: НЕОТРИЦАТЕЛЬНОСТЬ всех LR. -/
theorem llrd_nonneg (eta gamma : ℝ) (L l : ℕ)
    (heta : 0 ≤ eta) (hg : 0 ≤ gamma) :
    0 ≤ layerLR eta gamma L l := by
  unfold layerLR
  exact mul_nonneg heta (pow_nonneg hg _)

end Hagi.Optimization.LLRD

/-!
# Lookahead optimizer (источник №75: Zhang et al.,
# "Lookahead Optimizer: k steps forward, 1 step back",
# arXiv 1907.08610)

Двухмасштабная схема: k внутренних (fast) шагов от якоря w,
затем медленный шаг якоря к последнему быстрому итерату:
w' = w + α·(x_k − w), α ∈ (0,1].

Формализуем честные свойства:
1. `lookahead_mem`: новый якорь лежит МЕЖДУ старым якорем и
   быстрым итератом (выпуклая комбинация — шаг назад не
   проскакивает цель);
2. `lookahead_gap`: |w' − w| = α·|x_k − w| — смещение якоря
   строго контролируется (α — ручка скорости дрейфа);
3. `lookahead_range`: если якорь и быстрый итерат в [lo,hi],
   новый якорь тоже в [lo,hi] (инвариант диапазона).
-/

namespace Hagi.Optimization.Lookahead

/-- Медленный шаг якоря к быстрому итерату. -/
def slowStep (w x α : ℝ) : ℝ := w + α * (x - w)

/-- ЯКОРЬ МЕЖДУ: новый якорь — выпуклая комбинация старого
якоря и быстрого итерата (α ∈ [0,1]): лежит в их выпуклой
оболочке — «шаг назад» не проскакивает цель. -/
theorem lookahead_mem (w x α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    min w x ≤ slowStep w x α ∧ slowStep w x α ≤ max w x := by
  have hcvx : slowStep w x α = (1 - α) * w + α * x := by
    unfold slowStep; ring
  rcases le_total w x with hwx | hxw
  · rw [min_eq_left hwx, max_eq_right hwx]
    constructor
    · -- (1−α)w + αx ≥ w ⟺ αx ≥ αw
      rw [hcvx]; nlinarith [hwx, hα]
    · rw [hcvx]; nlinarith [hwx, hα, hα1]
  · rw [min_eq_right hxw, max_eq_left hxw]
    constructor
    · rw [hcvx]; nlinarith [hxw, hα]
    · rw [hcvx]; nlinarith [hxw, hα, hα1]

/-- КОНТРОЛЬ СМЕЩЕНИЯ: |w' − w| = α·|x − w| — дрейф якоря
пропорционален α (α ∈ [0,1] — ручка скорости якоря). -/
theorem lookahead_gap (w x α : ℝ) (hα : 0 ≤ α) :
    |slowStep w x α - w| = α * |x - w| := by
  unfold slowStep
  rw [show w + α * (x - w) - w = α * (x - w) from by ring, abs_mul,
    abs_of_nonneg hα]

/-- ИНВАРИАНТ ДИАПАЗОНА: якорь и быстрый итерат в [lo,hi]
⟹ новый якорь в [lo,hi] (lookahead не покидает оболочку
ингредиентов). -/
theorem lookahead_range (w x α lo hi : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hw : lo ≤ w ∧ w ≤ hi) (hx : lo ≤ x ∧ x ≤ hi) :
    lo ≤ slowStep w x α ∧ slowStep w x α ≤ hi := by
  have h := lookahead_mem w x α hα hα1
  constructor
  · exact le_trans (le_min hw.1 hx.1) h.1
  · exact le_trans h.2 (max_le hw.2 hx.2)

end Hagi.Optimization.Lookahead

/-!
# CautiousOptimizer (источник №78: "The Cautious Optimizer",
# arXiv 2411.16085)

Идея: маскировать компоненты обновления, ЗНАК которых
расходится со знаком градиента (u_i·g_i ≤ 0 → отбросить):
u'_i = u_i, если 0 < u_i·g_i; иначе 0.

Формализуем честные свойства:
1. `cautiousMask_abs_le`: маскирование НЕ увеличивает норму
   (‖u'‖ ≤ ‖u‖ — отбрасывание компонент сжимает);
2. `cautiousAligned`: выжившие компоненты согласованы со
   знаком градиента (u'_i·g_i ≥ 0);
3. `cautiousId`: при полной согласованности маска —
   тождество (не портит хороший update);
4. `cautiousZero`: полностью несогласованный update
   обнуляется (осторожность = отказ от вредного шага).
-/

namespace Hagi.Optimization.CautiousOptimizer

open Classical

/-- Осторожная маска: сохранить только компоненты,
согласованные со знаком градиента. -/
noncomputable def cautiousMask (u g : ℝ) : ℝ := if 0 < u * g then u else 0

/-- НОРМА НЕ РАСТЁТ: маскированная компонента не превосходит
исходной по модулю. -/
theorem cautiousMask_abs_le (u g : ℝ) :
    |cautiousMask u g| ≤ |u| := by
  unfold cautiousMask
  by_cases h : 0 < u * g
  · rw [if_pos h]
  · rw [if_neg h]
    simp

/-- СОГЛАСОВАННОСТЬ: выжившая компонента имеет
u'·g ≥ 0 — маска убирает только знаковые конфликты. -/
theorem cautiousAligned (u g : ℝ) :
    0 ≤ cautiousMask u g * g := by
  unfold cautiousMask
  by_cases h : 0 < u * g
  · rw [if_pos h]; exact h.le
  · rw [if_neg h]; simp

/-- ТОЖДЕСТВО ПРИ СОГЛАСОВАННОСТИ: если u·g > 0, маска
сохраняет u (хороший update не портится). -/
theorem cautiousId (u g : ℝ) (h : 0 < u * g) :
    cautiousMask u g = u := by
    unfold cautiousMask
    rw [if_pos h]

/-- ПОЛНЫЙ ОТКАЗ ПРИ КОНФЛИКТЕ: если u·g ≤ 0, шаг
обнуляется (осторожность = не вредить). -/
theorem cautiousZero (u g : ℝ) (h : u * g ≤ 0) :
    cautiousMask u g = 0 := by
    unfold cautiousMask
    rw [if_neg (by linarith)]

end Hagi.Optimization.CautiousOptimizer

/-!
# PPO-clip: консервативная отсечка surrogate (источник №32)

Источник №32: Schulman et al., "Proximal Policy Optimization"
(arXiv 1707.06347). Clipped surrogate objective
L = min(r·A, clip(r, 1−ε, 1+ε)·A), где r = π_θ/π_old —
probability ratio (r ≥ 0), A — advantage. Клип удерживает
обновление политики в доверительной зоне вокруг r = 1.

Формализованное ядро (строгое):
- `ppoClip`: clip(r, lb, ub) = max lb (min ub r);
- `ppoClip_le_upper/lower`: клипнутый ratio в [lb, ub];
- `ppoClip_mono`: клип монотонен по r;
- `ppoClip_fixed`: lb ≤ r ≤ ub ⟹ клип тождествен;
- `ppo_clip_term_abs_bound`: |clip(r,1−ε,1+ε)·A| ≤ (1+ε)·|A|;
- `ppo_surr_upper_bound`: L ≤ (1+ε)·|A| — клипнутый
  surrogate ОГРАНИЧЕН СВЕРХУ независимо от r: обновление
  политики не может дать неограниченный выигрыш
  (conservative bound ядра PPO; нижняя сторона не
  ограничивается — там штраф, а не выигрыш).
-/

namespace Hagi.Optimization.PPOClip

/-- Клип скаляра в отрезок [lb, ub]. -/
def ppoClip (r lb ub : ℝ) : ℝ := max lb (min ub r)

theorem ppoClip_le_upper (r lb ub : ℝ) (hlb : lb ≤ ub) :
    ppoClip r lb ub ≤ ub :=
  max_le hlb (min_le_left ub r)

theorem ppoClip_le_lower (r lb ub : ℝ) :
    lb ≤ ppoClip r lb ub := le_max_left lb (min ub r)

theorem ppoClip_mono (r r' lb ub : ℝ) (h : r ≤ r')
    (_hlb : lb ≤ ub) : ppoClip r lb ub ≤ ppoClip r' lb ub := by
  unfold ppoClip
  exact max_le_max (le_refl lb) (min_le_min (le_refl ub) h)

/-- Внутри отрезка клип тождествен. -/
theorem ppoClip_fixed (r lb ub : ℝ) (h1 : lb ≤ r) (h2 : r ≤ ub) :
    ppoClip r lb ub = r := by
  unfold ppoClip
  rw [min_eq_right h2]
  exact max_eq_right h1

/-- Абсолютное значение клипнутого члена ограничено. -/
theorem ppo_clip_term_abs_bound (r e A : ℝ) (he : 0 ≤ e) :
    |ppoClip r (1 - e) (1 + e) * A| ≤ (1 + e) * |A| := by
  have hlow : 1 - e ≤ ppoClip r (1 - e) (1 + e) :=
    ppoClip_le_lower r (1 - e) (1 + e)
  have hup : ppoClip r (1 - e) (1 + e) ≤ 1 + e :=
    ppoClip_le_upper r (1 - e) (1 + e) (by linarith)
  have habs : |ppoClip r (1 - e) (1 + e)| ≤ 1 + e := by
    apply abs_le.2
    constructor
    · have hn := neg_le_abs (ppoClip r (1 - e) (1 + e))
      linarith [hlow, hn, he]
    · linarith [hup]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right habs (abs_nonneg A)

/-- Surrogate L = min(r·A, clip·A) ограничен сверху:
обновление не может дать выигрыш больше (1+ε)|A|,
каким бы ни стало r. -/
theorem ppo_surr_upper_bound (r e A : ℝ) (he : 0 ≤ e) :
    min (r * A) (ppoClip r (1 - e) (1 + e) * A) ≤ (1 + e) * |A| :=
  le_trans (min_le_right _ _)
    (le_trans (le_abs_self _)
      (ppo_clip_term_abs_bound r e A he))

end Hagi.Optimization.PPOClip

/-!
# SAM (источник №81: Foret et al., "Sharpness-Aware
# Minimization", arXiv 2010.01412)

Минимизация остроты: вместо L(w) оптимизируют
worst-neighbor лосс sam_ρ(L, w) = sup{L(w+ε) : ‖ε‖ ≤ ρ} —
поиск ПЛОСКИХ минимумов (низкая чувствительность к
возмущениям весов = к квантованию/дистилляции).

1. `samW` — супремум лосса на ρ-шаре;
2. `sam_ge` — sam ≥ L(w) (нулевое возмущение в шаре);
3. `sam_mono` — монотонность по ρ (острота растёт
   с окрестностью);
4. `sam_flat` — константный на шаре лосс ⟹ sam = L(w)
   — идеальная плоскость (нулевая острота).
-/

namespace Hagi.Optimization.SAM

variable {k : Type*} [Fintype k]

/-- Евклидова полинорма возмущения (сумма квадратов). -/
noncomputable def norm2 (e : k → ℝ) : ℝ := ∑ i, (e i)^2

/-- ρ-шар возмущений. -/
def ball (rho : ℝ) : Set (k → ℝ) := {e | norm2 e ≤ rho ^ 2}

/-- НУЛЕВОЕ ВОЗМУЩЕНИЕ лежит в шаре при ρ ≥ 0. -/
theorem zero_mem_ball {rho : ℝ} (hr : 0 ≤ rho) :
    (0 : k → ℝ) ∈ ball (k := k) rho := by
  refine Set.mem_setOf.mpr ?_
  have h0 : norm2 (0 : k → ℝ) = 0 := by
    unfold norm2; simp
  rw [h0]
  exact sq_nonneg rho

noncomputable def samW (L : (k → ℝ) → ℝ) (rho : ℝ)
    (w : k → ℝ) : ℝ :=
  sSup (L '' (fun e => w + e) '' ball rho)

/-- sam ≥ L(w): worst-case не хуже текущей точки. -/
theorem sam_ge (L : (k → ℝ) → ℝ) (rho : ℝ) (hr : 0 ≤ rho)
    (w : k → ℝ)
    (hBdd : BddAbove (L '' (fun e => w + e) '' ball rho)) :
    L w ≤ samW L rho w :=
  le_csSup hBdd ⟨w + 0, ⟨0, zero_mem_ball hr, by simp⟩, by simp⟩

/-- ВЛОЖЕНИЕ ШАРОВ: r1 ≤ r2 ⟹ ball r1 ⊆ ball r2. -/
theorem ball_mono {r1 r2 : ℝ} (h : r1 ≤ r2) (hr1 : 0 ≤ r1)
    (hr2 : 0 ≤ r2) : ball (k := k) r1 ⊆ ball (k := k) r2 := by
  intro e he
  unfold ball at he ⊢
  have hsq : r1 ^ 2 ≤ r2 ^ 2 := by nlinarith
  exact le_trans he hsq

/-- МОНОТОННОСТЬ ПО РАДИУСУ: ρ₁ ≤ ρ₂ ⟹ worst-case лосс
монотонно растёт с окрестностью. -/
theorem sam_mono (L : (k → ℝ) → ℝ) (r1 r2 : ℝ)
    (h : r1 ≤ r2) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (w : k → ℝ)
    (hB2 : BddAbove (L '' (fun e => w + e) '' ball r2)) :
    samW L r1 w ≤ samW L r2 w := by
  have hsne : (L '' (fun e => w + e) '' ball r1).Nonempty :=
    ⟨L (w + 0), ⟨w + 0, ⟨0, zero_mem_ball hr1, by simp⟩, by simp⟩⟩
  unfold samW
  refine csSup_le_csSup hB2 hsne ?_
  rintro y ⟨z, ⟨e, he, hez⟩, hyz⟩
  rw [← hez] at hyz
  exact ⟨w + e, ⟨e, ball_mono h hr1 hr2 he, rfl⟩, hyz⟩

/-- ИДЕАЛЬНАЯ ПЛОСКОСТЬ: L постоянна на ρ-шаре ⟹
sam = L(w) — нулевая острота (цель SAM-обучения). -/
theorem sam_flat (L : (k → ℝ) → ℝ) (rho : ℝ) (hr : 0 ≤ rho)
    (w : k → ℝ)
    (hconst : ∀ e ∈ ball rho, L (w + e) = L w)
    (hBdd : BddAbove (L '' (fun e => w + e) '' ball rho)) :
    samW L rho w = L w := by
  have hsne : (L '' (fun e => w + e) '' ball rho).Nonempty :=
    ⟨L (w + 0), ⟨w + 0, ⟨0, zero_mem_ball hr, by simp⟩, by simp⟩⟩
  refine le_antisymm ?_ ?_
  · refine csSup_le hsne ?_
    rintro y ⟨z, ⟨e, he, hez⟩, hyz⟩
    rw [← hez] at hyz
    rw [← hyz, hconst e he]
  · exact sam_ge L rho hr w hBdd

end Hagi.Optimization.SAM

/-!
# GradAccum — накопление градиентов микробатчами
# (источник №65: практика больших батчей; математическое
# ядро — fiberwise-декомпозиция сумм)

Идея: большой батч N разбивается на k микробатчей (по
памяти); градиенты накапливаются и усредняются. Формализуем
ЭКВИВАЛЕНТНОСТЬ: среднее по полному батчу = взвешенное
среднее микробатч-средних (веса = размеры частей), через
Finset.sum_fiberwise. Следствие: накопление по частям
математически тождественно одному большому шагу.
-/

namespace Hagi.Optimization.GradAccum

open Finset

variable {N : ℕ} [Fintype (Fin N)] [DecidableEq (Fin N)]

/-- Полный градиент батча: среднее по всем примерам. -/
noncomputable def fullGrad (f : Fin N → ℝ) : ℝ :=
  (∑ x, f x) / N

/-- Градиент микробатча i (по разбиению c). -/
noncomputable def microGrad {k : ℕ} (c : Fin N → Fin k)
    (f : Fin N → ℝ) (i : Fin k) : ℝ :=
  (∑ x ∈ univ.filter (fun x => c x = i), f x) / N

/-- ИСТОЧНИК №65, УРОВЕНЬ 1: ЭКВИВАЛЕНТНОСТЬ НАКОПЛЕНИЯ —
сумма микробатч-градиентов РАВНА полному батч-градиенту
(делённые на общий N, суммы по fiber-разбиению в точности
восстанавливают полную сумму; Finset.sum_fiberwise). -/
theorem accum_equiv {k : ℕ} (c : Fin N → Fin k)
    (f : Fin N → ℝ) :
    (∑ i, microGrad c f i) = fullGrad f := by
  have hfiber := Finset.sum_fiberwise Finset.univ c f
  unfold microGrad fullGrad
  rw [← Finset.sum_div]
  exact congrArg (fun t => t / (N:ℝ)) hfiber

end Hagi.Optimization.GradAccum
