import Hagi.Optimization.Momentum
import Hagi.Theory.SelfEditGate
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# KnobMomentum — momentum в knob-space: сертифицированное расширение

Формализация momentum-ручки в объявленном knob-space HAGI_v2.

Честный вердикт по коду (READ-ONLY `C:\HAGI_v2`): momentum-динамики в
knob-space в ПРОИЗВОДСТВЕННОМ коде НЕТ — `rg -i momentum hagi/` даёт
только комментарий о torch-оптимизаторе (`hagi/controller.py:190`,
momentum применяется к НЕПРЕРЫВНЫМ параметрам через `optimizer.step()`)
и учебную задачу физики (`hagi/core.py:5606`). Momentum-ручка —
ЗАЯВЛЕННОЕ расширение с точной формулой (source-anchors):

* cfg-формула: heavy-ball параметры (β,η) = (ρ²,(1−ρ)²) при ρ ∈ (0,1),
  «операционально: это формула для genesis-расширения momentum knob
  (фронт: сейчас у нас нет momentum в knob-space — сертифицированное
  добавление по cfg-формула безопасно)» — THEORY_ALIGNMENT.md:856-861
  (Цикл 11, чисерная валидация ρ∈{0.3,0.5,0.7,0.9}; волна 62 HBRate:
  «momentum knob сертифицируем», THEORY_ALIGNMENT.md:1119-1127);
* характеристическое уравнение momentumRate: ρ² = qρ + β для
  ρ = (q+√(q²+4β))/2 — THEORY_ALIGNMENT.md:1220-1224 (волна 72,
  momentumRate_char, чисерно точно на (q,β) ∈ {(.5,.9),(1,0),(−.3,.5)});
* knob-space — объявленные конечные домены (`hagi/selfedit.py:42-46`
  KNOBS), а добавление любой ручки проходит ТОТ ЖЕ сертифицирующий
  adopt-гейт (`hagi/selfedit.py:221-223`, строгий `>`; формализован
  в C457 — `Hagi.Theory.SelfEditGate`).

Что утверждается здесь: свойства динамики (клип-инвариант, ускорение на
согласованном сигнале, перелёт при смене знака) и то, что
momentum-кандидаты НЕ обходят certify (мост к `adopt_chain_terminates`).
Характеристическое тождество НЕ пере-доказывается: в Lean-арсенале
проекта уже есть точный анкер — `Hagi.Optimization.Momentum.momentumRate_char`
(ρ² = qρ + β, Hagi/Optimization/Momentum.lean:23; dup по DupLint/STMDUP
намеренно исключён).

Honest limits (не утверждается):
* динамика `idxTraj` — модель целевой семантики «упорядоченный конечный
  домен + текущий индекс + heavy-ball скорость»: шаг
  `idx ← clamp(idx + round(η·v))` НЕ является строкой кода (в коде
  значения выбирает RNG, selfedit.py:113-120); round смоделирован как
  `floor(x+1/2)`;
* score-функция конфигурации — эмпирическая посылка (fixed-seed
  бенчмарк; сам код это заявляет, selfedit.py:217-220);
* сходимость/оптимальность momentum НЕ утверждаются — только
  качественные свойства (следование сигналу, перелёт, гейт).
-/

namespace Hagi.Theory.KnobMomentum

open Hagi.Theory.SelfEditGate

/-! ### cfg-формула momentum-ручки -/

/-- Параметр momentum-ручки: ρ ∈ (0,1). Семантика по cfg-формуле
(THEORY_ALIGNMENT.md:856-861, Цикл 11): momentum-ручка задаётся ОДНИМ
скаляром ρ, из которого выводятся оба heavy-ball параметра. -/
abbrev Rho := ℝ

/-- Heavy-ball коэффициент инерции из ρ: β = ρ².
source: THEORY_ALIGNMENT.md:856-861 (cfg_stability/cfg_descent:
(β,η) = (ρ²,(1−ρ)²)); волна 62 (THEORY_ALIGNMENT.md:1119-1127):
β = ρ² держит характеристику на границе стабильности. -/
def betaOf (ρ : Rho) : ℝ := ρ ^ 2

/-- Шаг обучения из ρ: η = (1−ρ)².
source: THEORY_ALIGNMENT.md:856-861 (cfg-формула; ημ = (1−ρ)² —
нижняя граница интервала, волна 62). -/
def etaOf (ρ : Rho) : ℝ := (1 - ρ) ^ 2

/-- cfg-параметризация валидна при ρ ∈ (0,1): β ∈ (0,1) и η ∈ (0,1)
(условие чисерной валидации Цикла 11: ρ∈{0.3,0.5,0.7,0.9} ⊂ (0,1)). -/
theorem beta_eta_mem_Ioo (ρ : Rho) (h0 : 0 < ρ) (h1 : ρ < 1) :
    betaOf ρ ∈ Set.Ioo 0 1 ∧ etaOf ρ ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold betaOf etaOf
  constructor
  · constructor <;> nlinarith
  · constructor <;> nlinarith

/-! ### Heavy-ball скорость на сигнале Δscore -/

/-- Скорость heavy-ball по последовательному сигналу (приращениям
score): v₀ = g₀, v_{t+1} = β·v_t + g_{t+1}. Непрерывная «память» о
сигнале — стандартная heavy-ball рекурсия heavy-ball методов; здесь
она управляет knob-индексом через `idxTraj` ниже. -/
noncomputable def vel (β : ℝ) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => g 0
  | (t + 1) => β * vel β g t + g (t + 1)

/-- Точная закрытая форма скорости на ПОСТОЯННОМ сигнале g ≡ c:
v_t = c·(1−β^{t+1})/(1−β) — конечная сумма геометрической свёртки
Σ_{i≤t} β^{t−i}·c. Лемма для `momentum_monotone_follows`. -/
theorem vel_const (β c : ℝ) (hβ : β ≠ 1) (g : ℕ → ℝ) (h : ∀ i, g i = c)
    (t : ℕ) : vel β g t = c * (1 - β ^ (t + 1)) / (1 - β) := by
  have h1 : (1 - β) ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  induction t with
  | zero => rw [vel, h 0]; field_simp; ring
  | succ t ih =>
      rw [vel, ih, h (t + 1)]
      field_simp
      ring

/-- ГЛАВНОЕ СВОЙСТВО (ускорение на согласованном сигнале): при
постоянном положительном сигнале c > 0 и инерции β ∈ (0,1) скорость
momentum в каждый момент НЕ МЕНЬШЕ чистого шага: v_t ≥ c. Momentum
накапливает согласованный сигнал, а не просто реагирует на последний.
source-семантика: THEORY_ALIGNMENT.md:856-861 — cfg-настройка
(β,η)=(ρ²,(1−ρ)²) «даёт строгий спуск» именно за счёт накопления. -/
theorem momentum_monotone_follows {β c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hc : 0 < c) {g : ℕ → ℝ} (h : ∀ i, g i = c) (t : ℕ) :
    c ≤ vel β g t := by
  rw [vel_const β c (by linarith) g h t]
  have hden : 0 < 1 - β := by linarith
  have hβt : β ^ (t + 1) ≤ β := by
    have h1 : β ^ t ≤ 1 := by
      induction t with
      | zero => norm_num
      | succ t ih =>
          have hp : β ^ (t + 1) = β * β ^ t := by ring
          have hnn : 0 ≤ β ^ t := pow_nonneg (by linarith) t
          rw [hp]
          nlinarith
    calc β ^ (t + 1) = β * β ^ t := by ring
    _ ≤ β * 1 := by nlinarith
    _ = β := by ring
  rw [le_div_iff₀ hden]
  nlinarith

/-! ### Негатив: перелёт при смене знака сигнала -/

/-- ОБЩИЙ НЕГАТИВ: если накопленная скорость положительна (v_T > 0,
инерция β > 0), а текущий сигнал уже ОТРИЦАТЕЛЕН и слаб (β·v_T +
g_{T+1} > 0), то скорость остаётся положительной ПРИ отрицательном
сигнале: knob-индекс двинется ВВЕРХ, когда сигнал говорит ВНИЗ.
Это честная цена momentum — перелёт/осцилляция на смене знака: почему
β ограничивают и почему momentum-кандидат обязан проходить certify-гейт
(selfedit.py:221), а не приниматься по самой динамике. -/
theorem momentum_overshoot_negative {β : ℝ} (hβ : 0 < β) {g : ℕ → ℝ} {T : ℕ}
    (hv : 0 < vel β g T) (hg : g (T + 1) < 0)
    (hstay : 0 < β * vel β g T + g (T + 1)) :
    0 < vel β g (T + 1) ∧ g (T + 1) < 0 := by
  refine ⟨?_, hg⟩
  rw [vel]; linarith [hβ, hv, hstay]

/-- КОНКРЕТНЫЙ WITNESS перелёта: β = 1/2, сигнал g₀ = 1, g₁ = −1/10.
Скорость v₁ = (1/2)·1 + (−1/10) = 2/5 > 0 — положительна, хотя текущий
сигнал g₁ = −1/10 < 0 отрицателен. Чистый шаг пошёл бы вниз; momentum
идёт вверх. -/
theorem overshoot_witness : (0 : ℝ) < vel (1 / 2)
    (fun i => if i = 0 then 1 else -1 / 10) 1 ∧ -1 / 10 < 0 := by
  refine ⟨by rw [vel, vel]; norm_num, by norm_num⟩

/-! ### Клип-инвариант траектории knob-индекса -/

/-- Округление к ближайшему целому (модель квантования непрерывной
скорости в дискретный сдвиг индекса): round(x) = floor(x + 1/2). -/
noncomputable def qround (x : ℝ) : ℤ := Int.floor (x + 1 / 2)

/-- Клип в упорядоченный конечный домен индексов {0, …, n−1}:
модель «knob = упорядоченный конечный домен + текущий индекс»
(домены selfedit.py:42-46 конечны и упорядочены). -/
noncomputable def clampIdx (n : ℕ) : ℤ → ℤ := fun z => max 0 (min z ((n : ℤ) - 1))

/-- Клип всегда возвращает значение внутри домена. -/
theorem clampIdx_mem (n : ℕ) (z : ℤ) (hn : 0 < n) :
    0 ≤ clampIdx n z ∧ clampIdx n z < (n : ℤ) := by
  have h0 : (0 : ℤ) < n := by exact_mod_cast hn
  unfold clampIdx
  constructor <;> omega

/-- Траектория knob-индекса под momentum-динамикой:
idx₀ = 0, idx_{t+1} = clampIdx n (idx_t + round(η · v_t)), где v_t —
heavy-ball скорость `vel`. Целевая семантика заявленного расширения
(см. module docstring: honest limits — в производственном коде этого
шага нет, значения выбирает RNG). -/
noncomputable def idxTraj (n : ℕ) (η β : ℝ) (g : ℕ → ℝ) : ℕ → ℤ
  | 0 => 0
  | (t + 1) => clampIdx n (idxTraj n η β g t + qround (η * vel β g t))

/-- КЛИП-ИНВАРИАНТ: при непустом домене (n > 0) траектория knob-индекса
НИКОГДА не покидает домен {0, …, n−1}, каковы бы ни были сигнал, инерция
и шаг. Momentum не может «выбросить» конфигурацию из объявленного
пространства ручек — свойство, которое делает предложение momentum-ручки
легальным кандидатом (значение всегда из домена, selfedit.py:113-120). -/
theorem momentum_clip_bounds (n : ℕ) (η β : ℝ) (g : ℕ → ℝ) (hn : 0 < n)
    (t : ℕ) : 0 ≤ idxTraj n η β g t ∧ idxTraj n η β g t < (n : ℤ) := by
  have h0 : (0 : ℤ) < n := by exact_mod_cast hn
  induction t with
  | zero => simp [idxTraj]; omega
  | succ t ih => unfold idxTraj; unfold clampIdx; omega

/-! ### Мост к C457: momentum НЕ обходит certify -/

variable {κ : Type*} [DecidableEq κ] {V : Type*} [DecidableEq V]
variable (score : Config κ V → ℝ)

/-- Цепочка конфигураций, каждый шаг которой — momentum-кандидат,
принятый ЧЕРЕЗ гейт: значение v_i получено momentum-динамикой
(обобщённо: любое V-значение — гипотеза «proposed by momentum» не
меняет математику гейта), и adopted по `adoptGate`. -/
def MomentumChain (f : ℕ → Config κ V) : Prop :=
  ∀ i, ∃ (k : κ) (v : V), f (i + 1) = applyPatch (f i) k v ∧
    adoptGate score (f i) k v

/-- Каждый принятый momentum-патч даёт СТРОГИЙ рост score — momentum не
имеет собственного канала принятия: та же гипотеза, что и для любого
патча (selfedit.py:221-223). -/
theorem momentum_adopt_gated (f : ℕ → Config κ V) (h : MomentumChain score f)
    (i : ℕ) : score (f (i + 1)) > score (f i) := by
  obtain ⟨k, v, hf, hg⟩ := h i
  rw [hf]
  exact hg

/-- МОСТ К C457: в конечном knob-space бесконечная цепочка принятых
momentum-патчей НЕВОЗМОЖНА — прямое следствие `adopt_chain_terminates`
(SelfEditGate.lean:139). Momentum-динамика не расширяет пространство
принятий: сколько бы скорость ни накапливала сигнал, принятия идут
только через строгий certify-гейт, и их число конечно. -/
theorem momentum_chain_terminates [Fintype κ] [Fintype V]
    (f : ℕ → Config κ V) (h : MomentumChain score f) : False :=
  adopt_chain_terminates score f (fun i => momentum_adopt_gated score f h i)

end Hagi.Theory.KnobMomentum
