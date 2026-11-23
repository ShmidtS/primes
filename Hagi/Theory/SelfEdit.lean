/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Optimization.Momentum
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# SelfEdit — the adopt-gate / knob canon (→)

One canonical module for the self-edit loop family; each concept
is described ONCE here. The two sections keep their historical
namespaces, so every fully-qualified name is stable (Continual.lean
precedent, v4 T1).

* The adopt gate (`Hagi.Theory.SelfEditGate`): a self-edit patch is
  adopted only if its score strictly improves — a strict-monotone
  functional on a FINITE configuration space. Termination
  (`adopt_chain_terminates`) is pure finiteness: no strictly
  monotone chain revisits a score, so its length is bounded by the
  number of configurations; a weak (non-strict) gate can cycle
  (`weak_gate_cycles`), and bounded reject series are trimmable.
* The momentum knob (`Hagi.Theory.KnobMomentum`): the heavy-ball
  knob `(β, η) = (betaOf ρ, etaOf ρ)` over the SAME gate; momentum
  follows monotone steps, overshoot is certified negative, and the
  quantized trajectory stays clipped — adoption stays gated by the
  SelfEditGate canon (`momentum_adopt_gated`).
-/

/-! ## SelfEditGate — the adopt gate (canonical owner) -/

namespace Hagi.Theory.SelfEditGate

variable {κ : Type*} [DecidableEq κ] {V : Type*} [DecidableEq V]

/-- Knob configuration: a value for every declared knob name.
source: hagi/selfedit.py:78-101 "current_settings" — snapshot of the
current knob values (loop defaults overridden by gate-adopted ones). -/
abbrev Config (κ V) := κ → V

/-- A patch overwrites exactly ONE knob with a new value.
source: hagi/selfedit.py:157-159 "apply_patch" —
`out[patch["knob"]] = patch["value"]` on a settings overlay (the
source code is never edited). -/
def applyPatch (cfg : Config κ V) (k : κ) (v : V) : Config κ V :=
  Function.update cfg k v

omit [DecidableEq V] in
/-- Structural lemma: a patch leaves every other knob untouched.
source: hagi/selfedit.py:157-159 (overlay semantics). -/
theorem applyPatch_ne (cfg : Config κ V) {k k' : κ} (v : V)
    (h : k' ≠ k) : applyPatch cfg k v k' = cfg k' := by
  simp [applyPatch, Function.update, h]

omit [DecidableEq V] in
/-- Structural lemma: a patch sets its own knob to the new value.
source: hagi/selfedit.py:157-159. -/
theorem applyPatch_self (cfg : Config κ V) (k : κ) (v : V) :
    applyPatch cfg k v k = v := by
  simp [applyPatch, Function.update]

variable (score : Config κ V → ℝ)

/-- Deterministic benchmark score of a configuration (fixed-seed
mini-suite: adopted rounds / final experts).
source: hagi/selfedit.py:56-68 "run_benchmark" — deterministic
fixture; honest limit: fixed-seed test, not a statistical bound
(hagi/selfedit.py:217-220: 2 rounds give no eta guarantee). -/
abbrev Score (κ V) := Config κ V → ℝ

/-- The adopt gate: a patch is adopted ONLY on strict positive
evidence — the candidate benchmark STRICTLY exceeds the incumbent's.
source: hagi/selfedit.py:221-223 `no_regress = cand.adopted >
baseline.adopted ∨ cand.experts > baseline.experts` (strict `>` on
each disjunct; one-score model, see module docstring). -/
def adoptGate (cfg : Config κ V) (k : κ) (v : V) : Prop :=
  score (applyPatch cfg k v) > score cfg

/-- A no-op patch: the proposed value equals the incumbent setting
on its knob (so the patched config equals the incumbent config).
source: hagi/selfedit.py:124-130 "is_noop". -/
def isNoop (cfg : Config κ V) (k : κ) (v : V) : Prop :=
  applyPatch cfg k v = cfg

omit [DecidableEq V] in
/-- No-op patches can NEVER pass the strict adopt gate: the score is
deterministic in the configuration, so a no-op candidate scores
exactly the incumbent's value. This formally justifies the code's
"noop-skipped" fast path — skipping a no-op without spending gate
runs loses nothing, because it could never be adopted.
source: hagi/selfedit.py:190 (skip), 221 (strict `>`). -/
theorem noop_not_adopted (cfg : Config κ V) (k : κ) (v : V)
    (h : isNoop cfg k v) : ¬ adoptGate score cfg k v := by
  intro hg
  unfold adoptGate isNoop at *
  rw [h] at hg
  exact lt_irrefl _ hg

/-! ### Termination of the adopt chain in a finite knob-space -/

/-- A pointwise strict gain along a chain makes the score chain
strictly monotone. Auxiliary for `adopt_chain_terminates`;
the gain hypothesis is exactly one adoption per step
(`adoptGate`, hagi/selfedit.py:221). -/
theorem chain_strictMono {g : ℕ → ℝ} (h : ∀ i, g (i + 1) > g i) :
    StrictMono g := by
  intro i j hij
  induction j with
  | zero => exact absurd hij (Nat.not_lt_zero _)
  | succ j ih =>
    have h1 : i ≤ j := Nat.lt_succ_iff.mp hij
    have h2 : g j < g (j + 1) := h j
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact (ih hlt).trans h2
    · have heq : i = j := Nat.le_antisymm h1 hge
      subst heq; exact h2

set_option linter.unusedFintypeInType false in
/-- MAIN THEOREM: in a finite knob-space the certified self-edit
search TERMINATES — an infinite chain of adoptions is impossible:
each adoption strictly increases a deterministic score over a finite
set of configurations, and an infinite strictly ascending chain
would inject ℕ into a finite type (cardinality contradiction).
source: knob-space finiteness — hagi/selfedit.py:42-46 (three knobs,
enumerated candidate values); strict gain per adoption —
hagi/selfedit.py:221. Honest limits: termination of ADOPTIONS is
claimed, not optimality of the final configuration, and not
termination of proposal attempts (those can continue, being
rejected/no-op-skipped). -/
theorem adopt_chain_terminates [Fintype κ] [Fintype V]
    (f : ℕ → Config κ V)
    (h : ∀ i, score (f (i + 1)) > score (f i)) : False := by
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt2 : score (f a) < score (f b) := chain_strictMono h hlt
      rw [hab] at hlt2
      exact lt_irrefl _ hlt2
    · have hgt2 : score (f b) < score (f a) := chain_strictMono h hgt
      rw [hab] at hgt2
      exact lt_irrefl _ hgt2
  have hcard : ∀ n : ℕ, n ≤ Fintype.card (Config κ V) := fun n => by
    simpa using Fintype.card_le_of_injective (fun (i : Fin n) => f i)
      (fun a b hab2 => Fin.ext (hinj hab2))
  have := hcard (Fintype.card (Config κ V) + 1)
  omega

/-! ### Negative result: the strictness of `>` is necessary -/

/-- NEGATIVE THEOREM: a WEAK gate (non-strict `≥`) admits an
infinite adoption chain of non-no-op patches: with a constant score
and a single boolean knob, the value can be flipped forever — every
step "does not regress" (score equal) and every patch changes the
incumbent (not a no-op), so the gate budget is consumed eternally
and no progress accumulates. This is the formal justification for
the STRICT `>` in hagi/selfedit.py:221 (adopt only on strict
positive evidence, comment at selfedit.py:217-222). -/
theorem weak_gate_cycles : ∃ (weak : Config Bool Bool → ℝ)
    (f : ℕ → Config Bool Bool),
    (∀ i, weak (f (i + 1)) ≥ weak (f i)) ∧
    (∀ i, ∃ (k : Bool) (v : Bool),
      applyPatch (f i) k v = f (i + 1) ∧ applyPatch (f i) k v ≠ f i) := by
  refine ⟨fun _ => 0, fun i k => if k then decide (i % 2 == 1) else false,
    fun i => le_refl 0, ?_⟩
  intro i
  have key : ((i + 1) % 2 == 1) = !(i % 2 == 1) := by
    rcases Nat.lt_or_ge (i % 2) 1 with h | h
    · have h0 : i % 2 = 0 := by omega
      have h1 : (i + 1) % 2 = 1 := by omega
      simp [h0, h1]
    · have h1 : i % 2 = 1 := by omega
      have h0 : (i + 1) % 2 = 0 := by omega
      simp [h0, h1]
  refine ⟨true, (i + 1) % 2 == 1, ?_, ?_⟩
  · funext k
    by_cases hk : k = true
    · subst hk
      simp only [applyPatch, Function.update]
      rw [key]
      by_cases hq : i % 2 = 1 <;> simp_all
    · simp [applyPatch, hk]
  · intro hc
    have h0 : ((i + 1) % 2 == 1) = decide (i % 2 == 1) := by
      have := congrFun hc true
      simpa [applyPatch] using this
    rw [key] at h0
    by_cases hq : i % 2 = 1 <;> simp_all

/-! ### Rejection-series budget invariant -/

/-- "MAX_GATE_RUNS" — maximum rejections kept per series before the
reset. source: hagi/selfedit.py:167 `MAX_GATE_RUNS = 6` (tied to the
GatePipeline delta-schedule bound Σ_{k≤6} 6/(π²k²) ≤ 1). -/
def maxGateRuns : ℕ := 6

/-- Rejection-series trim: at `≥ maxGateRuns` accumulated rejections
the log is truncated to the LAST `maxGateRuns` entries (a fresh
series re-enters the budget-covered range).
source: hagi/selfedit.py:180-182 `if len(rejected) >= MAX_GATE_RUNS:
log["rejected"] = log["rejected"][-MAX_GATE_RUNS:]`. -/
def rejectSeriesTrim (L : List α) : List α :=
  if L.length ≥ maxGateRuns then L.drop (L.length - maxGateRuns) else L

/-- INVARIANT: after the trim performed at the top of each
self-edit cycle, the rejection series is bounded by `maxGateRuns`
(the certified-regime range of the delta schedule).
source: hagi/selfedit.py:180-182. -/
theorem reject_series_bounded (L : List α) :
    (rejectSeriesTrim L).length ≤ maxGateRuns := by
  unfold rejectSeriesTrim
  split
  · rw [List.length_drop]; omega
  · omega

end Hagi.Theory.SelfEditGate

/-! ## KnobMomentum — the momentum knob over the gate -/

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

/-! ### Мост к momentum НЕ обходит certify -/

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

/-- МОСТ К в конечном knob-space бесконечная цепочка принятых
momentum-патчей НЕВОЗМОЖНА — прямое следствие `adopt_chain_terminates`
(SelfEditGate.lean:139). Momentum-динамика не расширяет пространство
принятий: сколько бы скорость ни накапливала сигнал, принятия идут
только через строгий certify-гейт, и их число конечно. -/
theorem momentum_chain_terminates [Fintype κ] [Fintype V]
    (f : ℕ → Config κ V) (h : MomentumChain score f) : False :=
  adopt_chain_terminates score f (fun i => momentum_adopt_gated score f h i)

end Hagi.Theory.KnobMomentum

