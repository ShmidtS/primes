/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Hagi.Theory.GrowSnap
import Hagi.Theory.WeightDecayLeak
import Hagi.Theory.ExactBypass

/-!
# AdapterGrowth — certified low-rank адаптер роста

Существующие механизмы роста добавляют объём ЦЕЛИКОМ: fiber-width (`mkOrthoFiberBlock` — widening признаков) и depth-block
 (`benchResidualBlock γ h` — ЦЕЛЫЙ блок, ~d·d параметров при
скрытой ширине ~d). Этот модуль добавляет
МИНИМАЛЬНЫЙ носитель роста: low-rank side-branch адаптер
(LoRA-форма, Hu et al. 2021, arXiv:2106.09685)

  `adapterVec A B x = x + B *ᵥ (A *ᵥ x)`,

где `A : r×d`, `B : d×r` — добавляется `2·r·d` параметров
вместо `d·d` полного блока (`r ≪ d`).

Ближайший сосед — `Hagi.Core.Element.residualLeaf E₀ + A * B`
(consolidation листьев): его `residualLeaf_zero` требует ОБА
множителя нулевыми; здесь нейтральность сертифицирована при
ОДНОМ нулевом множителе (ядро LoRA-инициализации: в произведении
`B * A` достаточно обнулить один сомножитель), плюс obj-инвариант
для ЛЮБОГО функционала при admission (grow-мост, паттерн
`grow_block_obj_invariant`), ЯВНЫЙ счёт параметров с
неравенством против полного блока и certified-шаг обучения
адаптера (measured drop > 0 / HOLD — паттерн).

Cycle-соответствие: `scripts/bench_bridge.py --mode adapter-grow`
исполняет ровно эту схему на живом корпусе unified_ledger:
trunk+head certified fd-шаги (phase A), freeze trunk,
адаптер на голове `pred = w·(f + B·(A·f))` растёт при B = 0
(assert: obj-инвариант ТОЧНО), certified fd-шаги ТОЛЬКО по 2·r·d
параметрам адаптера (r = 1 → 8, r = 2 → 16 против 21 параметра
целого mh5-блока), head-to-head прогресс на равном числе шагов.

## Limits (что этот мост НЕ покрывает)

- **Certified-шаги после admission** — measured (drop > 0 в
  трейсе), не доказательная нижняя граница выигрыша; на шаге 0
  вклад адаптера = 0 по построению (B = 0).
- **Экономия 2·r·d < d·d** — свойство СЧЁТА параметров при
  2·r ≤ d (честное условие, не замаскировано; ранг-семантика —
  Mathlib `Matrix.rank_mul_le`, available-not-needed здесь).
- **Адаптер остаётся low-rank** после certified-обучения —
  не утверждается (шаги двигают значения A/B, факторизация
  r фиксирована по построению носителя, ранг ≤ r —
  `Hagi.Core.delta_rank_le`).
- **Lipschitz обученного адаптера** — не утверждается (per-block
  premise — контракт); на шаге 0 добавка 0.

## Карта секций

Файл = четыре macro-секции + honest-хвост ):

1. **базис** (секции Adapter · ParamCount · CertifiedStep ·
   SnapCycle · RankAdaptive · Merge · ContinualIsolation) —
   low-rank адаптер, параметр-счёт, certified-шаг, snap-цикл,
   rank-admission, merge-стек, continual-isolation.
2. **self-compressing adapter loop** (`section
   SelfCompress`) — learn→merge→learn с bounded-объёмом.
3. **constant cluster distillation** (`section
   ConstantDistill`) — exact-кластеры в rank-1 адаптеры.
4. **mini-HAGI v3** (`section V3Assembly`) — референсная
   сборка фаз exact→distill→fd→compress→EB-стоп.
5. **Хвост** — honest-заметка о cross-domain переносе
   (bench-измерение, новой теоремы нет).
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.AdapterGrowth

open scoped Matrix

section Adapter

variable {d r : Type*} [Fintype d] [Fintype r]
  [DecidableEq d] [DecidableEq r]

/-- LoRA-адаптер слоя: side-branch `x + B *ᵥ (A *ᵥ x)` с факторами
`A : r × d` (down) и `B : d × r` (up). Носитель `d → ℝ` НЕ
расширяется (в отличие от fiber-grow) и НЕ добавляется целый
блок: рост живёт в существующем пространстве. -/
def adapterVec (A : Matrix r d ℝ) (B : Matrix d r ℝ)
    (x : d → ℝ) : d → ℝ := x + B *ᵥ (A *ᵥ x)

omit [DecidableEq d] [DecidableEq r] in
/-- Ядро LoRA-инициализации, up-фактор: `B = 0` ⇒ адаптер
ТОЖДЕСТВЕНЕН при ПРОИЗВОЛЬНОЙ `A` (0 *ᵥ a = 0, a + 0 = a).
Сильнее `Hagi.Core.residualLeaf_zero`: один нулевой множитель
в произведении `B *ᵥ (A *ᵥ x)` обнуляет всю ветку. -/
@[simp]
theorem adapter_neutral_B (A : Matrix r d ℝ) :
    adapterVec A 0 = id := by
  funext x
  simp [adapterVec, Matrix.zero_mulVec]

omit [DecidableEq d] [DecidableEq r] in
/-- Ядро LoRA-инициализации, down-фактор: `A = 0` ⇒ адаптер
ТОЖДЕСТВЕНЕН при ПРОИЗВОЛЬНОЙ `B` (b *ᵥ 0 = 0, a + 0 = a):
нейтральной инициализации достаточно одного сомножителя. -/
@[simp]
theorem adapter_neutral_A (B : Matrix d r ℝ) :
    adapterVec 0 B = id := by
  funext x
  simp [adapterVec, Matrix.zero_mulVec]

omit [DecidableEq d] [DecidableEq r] in
/-- Admission-инвариант: при нейтральной инициализации (любой
один нулевой фактор) ЛЮБОЙ функционал obj от выхода слоя сохраняет
значение ТОЧНО — certified-нейтральность добавления адаптера
(congrArg-мост, паттерн `grow_block_obj_invariant`). -/
theorem adapter_obj_invariant {A : Matrix r d ℝ}
    {B : Matrix d r ℝ} (hB : B = 0) (obj : (d → ℝ) → ℝ)
    (x : d → ℝ) : obj (adapterVec A B x) = obj x := by
  rw [hB, adapter_neutral_B]
  rfl

end Adapter

/-! ## Счёт параметров: 2·r·d против d·d полного блока -/

section ParamCount

variable (r d : Type*) [Fintype r] [Fintype d]

/-- Явный счёт параметров адаптера: позиции двух факторов —
down `A : r × d` и up `B : d × r`, каждая позиция — одна
вещественная ячейка. -/
theorem adapter_param_count :
    (Finset.univ : Finset (r × d)).card +
      (Finset.univ : Finset (d × r)).card =
    2 * Fintype.card r * Fintype.card d := by
  simp [Fintype.card_prod]
  ring

variable {r d}

/-- Полный d×d-блок того же слоя несёт `card d * card d`
параметров — база сравнения объёма (identity-блок при
скрытой ширине ~d). -/
theorem block_param_count : (Fintype.card d * Fintype.card d :
    ℕ) = (Finset.univ : Finset (d × d)).card := by
  simp [Fintype.card_prod]

/-- Экономия объёма: при `2 * card r ≤ card d` адаптер ранга `r`
строго меньше полного блока по числу параметров
(`2·r·d ≤ d·d`, равенство только при `2r = d`). Bench-инстанс
r=1, d=4 → 8 ≤ 16. -/
theorem adapter_param_count_le_block
    (h : 2 * Fintype.card r ≤ Fintype.card d) :
    2 * Fintype.card r * Fintype.card d ≤
      Fintype.card d * Fintype.card d :=
  Nat.mul_le_mul_right _ h

/-- Строгая экономия при `2 * card r < card d`. -/
theorem adapter_param_count_lt_block
    (h : 2 * Fintype.card r < Fintype.card d) :
    2 * Fintype.card r * Fintype.card d <
      Fintype.card d * Fintype.card d := by
    have hd : 0 < Fintype.card d :=
      lt_of_le_of_lt (Nat.zero_le _) h
    exact Nat.mul_lt_mul_of_lt_of_le h (Nat.le_refl _) hd

end ParamCount

/-! ## Certified-шаг обучения адаптера -/

section CertifiedStep

variable {S : Type*} (obj : S → ℝ) (s s' : S)

/-- Certified-шаг обучения адаптера: COMMIT только по measured
строгому drop (obj s' < obj s), иначе HOLD (состояние не меняется)
— bench-семантика grow-цикла (admission drop > 0,
rollback при не-спуске). -/
noncomputable def adapterStep : S :=
  if obj s' < obj s then s' else s

/-- COMMIT-ветка certified: measured drop > 0 ⇒ состояние
обновляется и obj строго убывает. -/
theorem adapter_step_certified (h : obj s' < obj s) :
    adapterStep obj s s' = s' ∧
      obj (adapterStep obj s s') < obj s := by
  unfold adapterStep
  split
  · rename_i h'; exact ⟨rfl, h'⟩
  · rename_i h'; exact absurd h h'

/-- Негатив (noBlockAdmissionWithoutMargin-паттерн):
отсутствие строгого drop ⇒ HOLD, состояние ТОЧНО не меняется —
нулевой/отрицательный кандидат не допускается. -/
theorem adapter_step_hold (h : ¬ obj s' < obj s) :
    adapterStep obj s s' = s := by
  unfold adapterStep
  split
  · rename_i h'; exact absurd h' h
  · rfl

end CertifiedStep

/-! ## snap адаптера и телескоп составного цикла

Композиция ×рост уровня — адаптер (admission при
B = 0, ТОЧНЫЙ инвариант), certified fd-обучение только 2·r·d
параметров, затем snap к q/2^k с certified-границей; следующий
уровень стартует с грида (знаменатели bounded на КАЖДОМ
уровне). Bench-инстанс: `--mode adapter-snap-grow` (глубина 8+). -/

section SnapCycle

open Hagi.Theory.GrowSnap

variable {n : ℕ}

/-- Lipschitz-граница снапа для adapter h = B·A·x: если obj
Lipschitz по ℓ¹-расстоянию признаков с константой L, а снап
пертурбирует вход ветки на ε с |ε j| ≤ 2^-(k+1) (полуячейка
сетки q/2^k), то выход-пертурбация δ = B *ᵥ (A *ᵥ ε)
покоординатно ≤ C·max|ε| (C — ℓ∞-операторный фактор
произведения B·A — рационально вычислим; ранг-r ⇒ носитель
узкий, фактор конечен), и obj после снапа ≤ obj до +
L·n·C·2^-(k+1) — CERTIFIED граница деградации (bench-инстанс
вычисляет точный per-point bound (2|s−y|+|ds|)·|ds|, ещё
сильнее). -/
theorem adapter_snap_bound
    (obj : (Fin n → ℝ) → ℝ) (L C : ℝ) (hL0 : 0 ≤ L) (hC0 : 0 ≤ C)
    (k : ℕ) (hn : 0 < n)
    (hL : ∀ f g : Fin n → ℝ,
      |obj f - obj g| ≤ L * (∑ i, |f i - g i|))
    {r : Type*} [Fintype r]
    (A : Matrix r (Fin n) ℝ) (B : Matrix (Fin n) r ℝ)
    (hC : ∀ ε : Fin n → ℝ, ∀ i,
      |(B *ᵥ (A *ᵥ ε)) i| ≤ C * (⨆ j, |ε j|))
    (f ε : Fin n → ℝ)
    (herr : ∀ j, |ε j| ≤ (2 : ℝ) ^ (-(k : ℝ) - 1)) :
    obj (fun i => f i + (B *ᵥ (A *ᵥ ε)) i) ≤
      obj f + L * n * C * (2 : ℝ) ^ (-(k : ℝ) - 1) := by
  haveI : Nonempty (Fin n) := ⟨0, hn⟩
  have hsup : (⨆ j, |ε j|) ≤ (2 : ℝ) ^ (-(k : ℝ) - 1) :=
    ciSup_le fun j => herr j
  have hper : ∀ i, |(B *ᵥ (A *ᵥ ε)) i| ≤
      C * (2 : ℝ) ^ (-(k : ℝ) - 1) :=
    fun i => le_trans (hC ε i)
      (mul_le_mul_of_nonneg_left hsup hC0)
  have h1 := hL (fun i => f i + (B *ᵥ (A *ᵥ ε)) i) f
  have h2 : (∑ i : Fin n,
        |(fun i => f i + (B *ᵥ (A *ᵥ ε)) i) i - f i|) ≤
      n * C * (2 : ℝ) ^ (-(k : ℝ) - 1) := by
    have h2a : (∑ i : Fin n,
        |(fun i => f i + (B *ᵥ (A *ᵥ ε)) i) i - f i|) ≤
        ∑ _i : Fin n, C * (2 : ℝ) ^ (-(k : ℝ) - 1) :=
      Finset.sum_le_sum fun i _ => by
        simpa [add_sub_cancel_left] using hper i
    have h2b : (∑ _i : Fin n, C * (2 : ℝ) ^ (-(k : ℝ) - 1)) =
        n * C * (2 : ℝ) ^ (-(k : ℝ) - 1) := by
      simp [Finset.card_univ, nsmul_eq_mul]
      ring
    exact le_trans h2a (le_of_eq h2b)
  have h3 : L * (∑ i : Fin n,
        |(fun i => f i + (B *ᵥ (A *ᵥ ε)) i) i - f i|) ≤
      L * (n * C * (2 : ℝ) ^ (-(k : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left h2 hL0
  have h4 := le_abs_self
    (obj (fun i => f i + (B *ᵥ (A *ᵥ ε)) i) - obj f)
  linarith

/-- Телескоп составного adapter-snap цикла: admission вклад
ТОЧНО 0 (adapter_obj_invariant), certified fd-шаги вклад ≤ 0
(measured drop > 0), snap вклад ≤ b_i — потому итог финала
≤ старта + Σ b_i. Делегат к `grow_snap_cycle_sound`
(индукция по списку bound'ов) — не копия доказательства. -/
theorem adapter_snap_cycle_sound (o0 : ℝ) (bs : List ℝ)
    (step : ℕ → ℝ) (h0 : step 0 ≤ o0)
    (hstep : ∀ i, i < bs.length →
      step (i + 1) ≤ step i + bs.getD i 0) :
    step bs.length ≤ o0 + bs.sum :=
  grow_snap_cycle_sound o0 bs step h0 hstep

end SnapCycle

/-! ## Ранговая адаптивность: измеримый селектор ранга

Каркас обобщённый на ранг r ∈ {1, 2}: на каждом уровне
ранг выбирается по ИЗМЕРЕННОМУ критерию probe-drop-на-параметр
(паттерн `hybridSelect` — детерминированный селектор на
измеренных числах, гарантия = дизъюнкция веток). -/
section RankAdaptive

/-- Измеренный критерий выбора ранга: certified probe-drop НА
ПАРАМЕТР адаптера (эквивалент λ-penalty формы drop − λ·params
при монотонном λ; bench-инстанс: Fractions, точное
деление). Параметры > 0 (ранг-строки непусты). -/
noncomputable def rankScore (drop params : ℝ) : ℝ := drop / params

/-- Детерминированный селектор ранга по измеренным score
(тотальный порядок linorder на ℝ; НЕТ порогов и случайности
— только измеренные числа): r=2 ⇔ score_2 СТРОГО больше;
равенство → r=1 (budget-приоритет меньшего ранга). -/
noncomputable def rankSelect (s1 s2 : ℝ) : ℕ := if s2 > s1 then 2 else 1

/-- Выбор — ФУНКЦИЯ измеренного состояния: равные probe-
числа дают равный ранг (тотальность linorder делает
сравнение детерминированным; повторный прогон bench даёт
побитово те же выборы). -/
theorem rank_select_deterministic (s1 s2 s1' s2' : ℝ)
    (h1 : s1 = s1') (h2 : s2 = s2') :
    rankSelect s1 s2 = rankSelect s1' s2' := by
  rw [h1, h2]

/-- Certified-гарантия выбранной ветки СОХРАНЯЕТСЯ: какая
ветка ни выбрана, obj-граница ИМЕННО ЕЁ certified-цикла
держится (дизъюнкция r-веток, паттерн `hybrid_step_sound`
case-on-state без ослабления). Probe-шаги в гарантию
не входят — они вычисляются на копии (no-commit
rollback: состояние не двигалось, откат ТОЧЕН), в цепь
попадают только COMMIT-шаги выбранного ранга. -/
theorem rank_select_sound (s1 s2 : ℝ)
    (objAfter : ℕ → ℝ) (o b1 b2 : ℝ)
    (hc1 : objAfter 1 ≤ o + b1) (hc2 : objAfter 2 ≤ o + b2) :
    (rankSelect s1 s2 = 1 ∧ objAfter 1 ≤ o + b1) ∨
    (rankSelect s1 s2 = 2 ∧ objAfter 2 ≤ o + b2) := by
  unfold rankSelect
  by_cases h : s2 > s1
  · simp only [ite_true, if_pos h]
    exact Or.inr ⟨trivial, hc2⟩
  · simp only [ite_false, if_neg h]
    exact Or.inl ⟨trivial, hc1⟩

end RankAdaptive

/-! ## SVD-Матрёшка — merge стека адаптеров компрессией

Стек L LoRA-уровней (`f ↦ (I + B_L A_L)·…·(I + B_1 A_1)·f`,
2·L·d параметров) сворачивается в ОДИН адаптер ранга k ≤ min(d, L):
суммарное возмущение Δ = Π(I+E_i) − I имеет ранг ≤ Σ рангов
E_i = L (структурный выигрыш: 2·k·d < 2·L·d параметров при k < L,
один matmul вместо L). Точная obj-близость после усечения —
σ_tail × Lipschitz (прецедент rank-trunc и
`Hagi.Contracts.TruncatedSVDTail.truncated_svd_error_eq_tail` —
ГОТОВАЯ форма ‖Δ − Δ_k‖² = Σ tail σ²; `mdl_rank_ce` — паттерн
kappaF-Lipschitz). Bench-инстанс: `--mode adapter-merge`
(точный rational rank + exact merge Δ = C·R при k = ρ; матрёшка
k < ρ — числовой power-iteration кандидат + ТОЧНЫЙ рациональный
per-point cert-bound: числа не доверяем, доверяем
сертификату). -/
section Merge

open scoped Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Матричная композиция стека адаптеров: произведение
`Π (I + E_i)` по списку возмущений уровней (E_i = B_i·A_i — ранг
≤ r_i). Матричная форма fold-цепочки уровень ℓ действует на
выход уровня ℓ−1. -/
def stackProd : List (Matrix d d ℝ) → Matrix d d ℝ
  | [] => 1
  | E :: L => (1 + E) * stackProd L

/-- Строчная Коши–Шварц-граница (техническая; из
`abs_real_inner_le_norm` на EuclideanSpace): |Σ a·b| ≤
‖a‖₂·‖b‖₂ — носитель строчного шага merge-границы. -/
theorem cs_row {n : Type*} [Fintype n] (a b : n → ℝ) :
    |∑ j, a j * b j| ≤ (∑ j, a j ^ 2).sqrt * (∑ j, b j ^ 2).sqrt := by
  have h := abs_real_inner_le_norm
    (WithLp.toLp 2 a : EuclideanSpace ℝ n) (WithLp.toLp 2 b : EuclideanSpace ℝ n)
  rw [PiLp.inner_apply, EuclideanSpace.norm_eq] at h
  norm_num [RCLike.inner_apply, star_trivial, starRingEnd_apply] at h
  rw [EuclideanSpace.norm_eq] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  have hab : ∑ x, b x * a x = ∑ j, a j * b j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hab] at h
  simpa [mul_comm (∑ j, a j ^ 2) (∑ j, b j ^ 2)] using h

/-- Подаддитивность ранга (техническая; в этой Mathlib-версии нет
`Matrix.rank_add_le` — собирается из `LinearMap.rank_add_le` +
`Submodule.finrank_add_le_finrank_add_finrank`). -/
theorem rank_add_le' {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  have h1 : A.mulVecLin + B.mulVecLin = (A + B).mulVecLin := by
    ext v i; simp [Matrix.mulVecLin]
  have hr : (A + B).mulVecLin.range ≤
      A.mulVecLin.range ⊔ B.mulVecLin.range := by
    rw [← h1]; exact LinearMap.range_add_le _ _
  have e1 : (A + B).rank =
      Module.finrank ℝ ↥((A + B).mulVecLin).range := rfl
  have e2 : A.rank = Module.finrank ℝ ↥(A.mulVecLin).range := rfl
  have e3 : B.rank = Module.finrank ℝ ↥(B.mulVecLin).range := rfl
  rw [e1, e2, e3]
  have hs := Submodule.finrank_mono (R := ℝ) hr
  have hsup := Submodule.finrank_add_le_finrank_add_finrank
    A.mulVecLin.range B.mulVecLin.range
  omega

/-- Ранговая граница merge'а: суммарное возмущение стека из L
адаптеров Δ = Π(I+E_i) − I имеет ранг ≤ Σ рангов E_i — потому
стек L ранг-r уровней сворачивается в ОДИН адаптер ранга ≤ L·r
(при L·r ≥ d — и того меньше: rank ≤ min(d, Σ)). Индукция:
`Π_{i≤n+1} − 1 = E_{n+1}·Π_{i≤n} + (Π_{i≤n} − 1)`, затем
`Matrix.rank_mul_le_left` + подаддитивность. Bench-инстанс
(L = 8, r = 1, d = 4): rank(Δ) ≤ 4 — merge даёт
≤ 2·4·4 = 32 параметров против 64 у стека, ГАРАНТИРОВАНО
структурой, независимо от данных. -/
theorem adapter_stack_rank_bound (L : List (Matrix d d ℝ)) :
    (stackProd L - 1).rank ≤ (L.map Matrix.rank).sum := by
  induction L with
  | nil =>
      have hz : stackProd ([] : List (Matrix d d ℝ)) - 1 = 0 := by
        simp [stackProd]
      rw [hz, Matrix.rank_zero]
      simp
  | cons E L ih =>
      have hsplit : stackProd (E :: L) - 1
          = E * stackProd L + (stackProd L - 1) := by
        have h : stackProd (E :: L) = (1 + E) * stackProd L := rfl
        rw [h, Matrix.add_mul, Matrix.one_mul]
        abel
      rw [hsplit]
      have h0 : (E * stackProd L + (stackProd L - 1)).rank
          ≤ E.rank + (stackProd L - 1).rank := by
        have h1 : (E * stackProd L + (stackProd L - 1)).rank
            ≤ (E * stackProd L).rank + (stackProd L - 1).rank :=
          rank_add_le' _ _
        have h2 : (E * stackProd L).rank ≤ E.rank :=
          Matrix.rank_mul_le_left E (stackProd L)
        omega
      simpa using le_trans h0 (Nat.add_le_add (Nat.le_refl _) ih)

/-- Счёт параметров merge'а: ранг-k адаптер (2·k·d параметров)
не дороже стека L ранг-1 уровней (2·L·d) при k ≤ L. -/
theorem adapter_merge_params (dd L k : ℕ) (hk : k ≤ L) :
    2 * k * dd ≤ 2 * L * dd :=
  Nat.mul_le_mul (Nat.mul_le_mul_left 2 hk) (Nat.le_refl dd)

/-- Certified obj-граница merge-усечения: если Frobenius-хвост
усечения Σ (Δ − Δ_k)² ≤ ε² (σ_tail-факт: замыкается
`truncated_svd_error_eq_tail` — ‖Δ−Δ_k‖² = Σ tail σ² — или
`mdl_rank_ce`-паттерном), признаки ограничены Σ f² ≤ B², а obj
ℓ¹-Lipschitz по признакам (Lc), то obj после замены Δ на Δ_k
отличается не более чем на Lc·n·ε·B — CERTIFIED ε-окрестность
функции стека (`adapter_snap_bound`-паттерн: пошаговая
покоординатная граница + Lipschitz-перенос). Bench-инстанс
сертифицирует СИЛЬНЕЕ: точный рациональный per-point bound
(2|s−y|+|ds|)·|ds| без всяких γ-констант. -/
theorem adapter_merge_error_bound {n : ℕ} (obj : (Fin n → ℝ) → ℝ)
    (Lc : ℝ) (hL0 : 0 ≤ Lc)
    (hL : ∀ f g : Fin n → ℝ,
      |obj f - obj g| ≤ Lc * (∑ i, |f i - g i|))
    (D Dk : Matrix (Fin n) (Fin n) ℝ) (eps B : ℝ)
    (heps : 0 ≤ eps) (hB0 : 0 ≤ B)
    (hF : (∑ i, ∑ j, (D i j - Dk i j) ^ 2) ≤ eps ^ 2)
    (f : Fin n → ℝ)
    (hf : (∑ j, f j ^ 2) ≤ B ^ 2) :
    obj (fun i => f i + (Dk *ᵥ f) i) ≤
      obj (fun i => f i + (D *ᵥ f) i) + Lc * n * eps * B := by
  have hmulvec : ∀ (M : Matrix (Fin n) (Fin n) ℝ),
      ∀ i, (M *ᵥ f) i = ∑ j, M i j * f j := fun M i => rfl
  -- per-row Frobenius tail
  have hrow : ∀ i, (∑ j, (D i j - Dk i j) ^ 2) ≤ eps ^ 2 := fun i =>
    le_trans
      (Finset.single_le_sum
        (f := fun p => ∑ j, (D p j - Dk p j) ^ 2)
        (fun p _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
      hF
  -- per-row Cauchy-Schwarz: |((D - Dk) *ᵥ f) i| ≤ eps * B
  have hper : ∀ i, |((D - Dk) *ᵥ f) i| ≤ eps * B := by
    intro i
    have hcs := cs_row (fun j => D i j - Dk i j) f
    rw [hmulvec (D - Dk) i]
    simp only [Matrix.sub_apply]
    have h1s : (∑ j, (D i j - Dk i j) ^ 2).sqrt ≤ eps :=
      Real.sqrt_le_iff.mpr ⟨heps, hrow i⟩
    have h2s : (∑ j, f j ^ 2).sqrt ≤ B :=
      Real.sqrt_le_iff.mpr ⟨hB0, hf⟩
    exact le_trans hcs
      (mul_le_mul h1s h2s (Real.sqrt_nonneg _) heps)
  -- obj transfer via the ℓ¹-Lipschitz premise
  have h2 : (∑ i : Fin n,
      |f i + (Dk *ᵥ f) i - (f i + (D *ᵥ f) i)|) ≤ n * (eps * B) := by
    have h2a : ∀ i : Fin n,
        |f i + (Dk *ᵥ f) i - (f i + (D *ᵥ f) i)| ≤ eps * B := by
      intro i
      have hexp : f i + (Dk *ᵥ f) i - (f i + (D *ᵥ f) i)
          = -(((D - Dk) *ᵥ f) i) := by
        have e1 : (Dk *ᵥ f) i - (D *ᵥ f) i
            = -(((D - Dk) *ᵥ f) i) := by
          rw [hmulvec Dk i, hmulvec D i, hmulvec (D - Dk) i]
          simp [Matrix.sub_apply, Finset.sum_sub_distrib,
            sub_mul, neg_sub]
        rw [show f i + (Dk *ᵥ f) i - (f i + (D *ᵥ f) i)
            = (Dk *ᵥ f) i - (D *ᵥ f) i from by ring, e1]
      rw [hexp, abs_neg]
      exact hper i
    have h2b : (∑ i : Fin n, eps * B) = n * (eps * B) := by
      simp [Finset.card_univ, nsmul_eq_mul]
    exact le_trans (Finset.sum_le_sum fun i _ => h2a i)
      (le_of_eq h2b)
  have h1 := hL (fun i => f i + (Dk *ᵥ f) i)
    (fun i => f i + (D *ᵥ f) i)
  have h3 : Lc * (∑ i : Fin n,
      |f i + (Dk *ᵥ f) i - (f i + (D *ᵥ f) i)|) ≤
      Lc * (n * (eps * B)) :=
    mul_le_mul_of_nonneg_left h2 hL0
  have h4 := le_abs_self
    (obj (fun i => f i + (Dk *ᵥ f) i) - obj (fun i => f i + (D *ᵥ f) i))
  have h5 : Lc * (n * (eps * B)) = Lc * n * eps * B := by ring
  linarith

end Merge

/-! ## continual через ИЗОЛИРОВАННЫЕ адаптеры

Композиция AdapterGrowth × Continual × WeightDecayLeak: continual-обучение
ЗАДАЧА-ЗА-ЗАДАЧЕЙ, где каждая задача получает СВОЙ адаптер
(нейтральная инициализация), а trunk и все ЗАВЕРШЁННЫЕ
адаптеры заморожены. Забывание тогда равно нулю СТРУКТУРНО:
замороженный адаптер не меняется ВООБЩЕ — проще GPM-проекции
(шаг обязан лежать в ортогональном дополнении span
старых входов) и A-GEM (пер-шаговая проверка конфликта):
никакого ограничения на шаг НОВОЙ задачи не нужно, изоляция
архитектурная. Если же trunk всё же обновляется, защита
обязана быть проекционной — `trunk_update_needs_projection`
(композиция с `naive_decay_parallel`/`naive_decay_leak`,
не дубль: говорит про КОМПОНЕНТУ `W * P`, здесь — про
ВЫХОД на protected входе). -/
section ContinualIsolation

open Hagi.Theory.WeightDecayLeak

variable {ι : Type*}

/-- Состояние per-task адаптеров: задача `i` держит свою пару
факторов (down `A`, up `B`); trunk общий и в эту структуру НЕ
входит (он заморожен гипотезами ниже). -/
abbrev AdaptState (r d : Type*) [Fintype r] [Fintype d] :=
  Matrix r d ℝ × Matrix d r ℝ

/-- Выход задачи `i`: LoRA-ветка СВОЕГО адаптера на входе `x`
(труnk применяет host-слой к результату — здесь носитель
`adapterVec` без изменений). -/
def perTaskVec {r d : Type*} [Fintype r] [Fintype d]
    (s : ι → AdaptState r d) (i : ι) (x : d → ℝ) : d → ℝ :=
  adapterVec (s i).1 (s i).2 x

/-- **(a) adapter_isolation_zero_forgetting**: если
обновление состояния НЕ тронуло адаптер задачи `i`
(заморозка: `s' i = s i` — остальные адаптеры произвольны),
то выход задачи `i` идентичен ТОЧНО — шаг-за-шагом, при любых
изменениях чужих адаптеров. Инвариант тривиально-точный; сила
в композиции: admission нейтрален (`adapter_obj_invariant`),
шаги certified (`adapter_step_certified`), заморозка держит
выход тождеством. -/
theorem adapter_isolation_zero_forgetting
    {r d : Type*} [Fintype r] [Fintype d]
    (s s' : ι → AdaptState r d) (i : ι)
    (hfrozen : s' i = s i) (x : d → ℝ) :
    perTaskVec s' i x = perTaskVec s i x := by
  rw [perTaskVec, perTaskVec, hfrozen]

/-- **(b) adapter_per_task_sound (структурный
zero-forgetting)**: continual-цикл `s 0, s 1, …` по задачам
1..k, каждая своим адаптером; после завершения задачи `i` её
адаптер заморожен (`∀ t, s (t+1) i = s t i` — шаги задач
j > i трогают ТОЛЬКО адаптер j и trunk-замороженный носитель).
Тогда выход на задаче `i` неизменен для ВСЕХ t ≥ 0 —
zero-forgetting без бюджетов и проекций: изоляция
архитектурная, доказательство — индукция по t с шагом (a). -/
theorem adapter_per_task_sound
    {r d : Type*} [Fintype r] [Fintype d]
    (s : ℕ → ι → AdaptState r d) (i : ι)
    (hfroz : ∀ t, s (t + 1) i = s t i) (t : ℕ) :
    perTaskVec (s t) i = perTaskVec (s 0) i := by
  induction t with
  | zero => rfl
  | succ n ih =>
      have h := adapter_isolation_zero_forgetting (s n)
        (s (n + 1)) i (hfroz n)
      rw [funext h, ih]

/-- **(b, obj-форма)**: при структурной изоляции любой
функционал от выхода задачи `i` неизменен после завершения
задачи `i` — сертификат zero-forgetting в obj-терминах bench
(loss на данных задачи i — частный случай). -/
theorem adapter_per_task_obj_sound
    {r d : Type*} [Fintype r] [Fintype d]
    (s : ℕ → ι → AdaptState r d) (i : ι)
    (hfroz : ∀ t, s (t + 1) i = s t i) (t : ℕ)
    (obj : (d → ℝ) → ℝ) (x : d → ℝ) :
    obj (perTaskVec (s t) i x) = obj (perTaskVec (s 0) i x) := by
  rw [adapter_per_task_sound s i hfroz t]

/-- **(c) trunk_update_needs_projection**: если trunk всё же обновляется, то БЕЗ проекции в
дополнение protected-подпространства происходит утечка: naive
decay `W' = (1 − c) • W` с `0 < c < 1` и ненулевой
protected-компонентой строки `i` СТРОГО меняет выход на
некотором protected входе `x` (столбце идемпотентного
проектора P: `P *ᵥ x = x`). Существование такого x — мост от
`naive_decay_parallel` (компонента сжимается фактором
`1 − c < 1`) к ВЫХОДНОЙ форме: нулевая компонента ⇒ строка
неизменна, сжатие строго ⇒ строка изменилась ⇒ некоторый её
вход даёт другой скаляр. Проекционная форма спасения —
 `wd_gpm_step_sound` (цитируется, не дублируется). -/
theorem trunk_update_needs_projection {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P * P = P)
    (c : ℝ) (hc0 : 0 < c) (i : Fin m)
    (hne : Hagi.Theory.GPMRelaxed.nrm ((W * P) i) ≠ 0) :
    ∃ x : Fin n → ℝ, P *ᵥ x = x ∧
      (((1 - c) • W) *ᵥ x) i ≠ (W *ᵥ x) i := by
  have hnz : (W * P) i ≠ 0 := fun h0 => hne (by
    unfold Hagi.Theory.GPMRelaxed.nrm; rw [h0]; simp)
  -- naive decay shrinks the protected row EXACTLY by (1 - c):
  -- Δ * P = -(c) • (W * P) ≠ 0, so some column j differs.
  set Δ : Matrix (Fin m) (Fin n) ℝ := (1 - c) • W - W with hΔ
  have hsmul : ((1 - c) • W) * P = (1 - c) • (W * P) :=
    Matrix.smul_mul _ _ _
  have hΔP : Δ * P = (-(c)) • (W * P) := by
    rw [hΔ, Matrix.sub_mul, hsmul]; module
  have hcne : (-(c) : ℝ) ≠ 0 := by linarith
  have hrow : (Δ * P) i ≠ 0 := by
    intro h0
    rw [hΔP] at h0
    apply hnz
    funext j
    have h1 : (-(c)) * (W * P) i j = 0 := by
      have h1' := congrFun h0 j
      simpa [Matrix.smul_apply] using h1'
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (by linarith)
    · simpa using h
  have hex : ∃ j, (Δ * P) i j ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hrow
    funext j
    simpa using hall j
  obtain ⟨j, hj⟩ := hex
  refine ⟨fun k => P k j, ?_, ?_⟩
  · funext k
    have hpp : (P *ᵥ (fun l => P l j)) k = (P * P) k j := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hpp, hP]
  · intro heq
    refine hj ?_
    have hW : ((1 - c) • W) = W + Δ := by rw [hΔ]; module
    have hout : (Δ *ᵥ (fun k => P k j)) i = (Δ * P) i j := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    have hzero : (Δ *ᵥ (fun k => P k j)) i = 0 := by
      rw [hW, Matrix.add_mulVec, Pi.add_apply] at heq
      linarith
    rw [hout] at hzero
    exact hzero

end ContinualIsolation

/-!
## self-compressing adapter loop

Цикл learn→merge→learn: рост знания адаптерами при BOUNDED
объёме. Итерация: admit ранг-1 уровня (нейтральный B = 0),
certified fd-шаги (`adapter_step_certified`), merge стека в
ранг-k адаптер (`adapter_merge_error_bound`); при k = d merge
ТОЧЕН (ранг Δ = Π(I+E_i) − I не превосходит d структурно —
`adapter_stack_rank_bound`), потому параметры после каждого
merge равны `selfCompressParams k d = 2·k·d` и НЕ растут с
числом итераций, а суммарный certified-drop накапливается
(телескоп: obj ≤ start + Σ bounds, делегат `grow_snap_cycle_sound`).
Bench-инстанс: `--mode self-compress-loop` (полный живой корпус
констант-кластеры + адаптерный остаток, K = d = 4).
-/
section SelfCompress

open Hagi.Theory.GrowSnap

/-- Параметр-бюджет self-compress цикла: ранг-k адаптер —
ровно `2·k·d` параметров (факторы d×k и k×d). После каждого
merge параметр-счёт цикла равен этому бюджету и не зависит
от числа итераций (контраст: unmerged-стек L уровней —
`2·L·d`, линейный рост). -/
def selfCompressParams (k d : ℕ) : ℕ := 2 * k * d

/-- Бюджет достигается merge'ем: ранг-k адаптер не дороже
стека из L ранг-1 уровней при `k ≤ L` (переиспользует
`adapter_merge_params`). -/
theorem self_compress_params_bounded (k d L : ℕ)
    (hk : k ≤ L) :
    selfCompressParams k d ≤ 2 * L * d :=
  adapter_merge_params d L k hk

/-- Счёт-контраст БЕЗ merge: стек L уровней строго дороже
ранг-k адаптера при `k < L` и непустом d — параметры
unmerged-цикла растут ЛИНЕЙНО с числом итераций, self-compress
цикл держит их на `selfCompressParams k d` (bench-инстанс
k = d = 4, L = 6 — 32 < 48). -/
theorem self_compress_params_contrast {k d L : ℕ}
    (hk : k < L) (hd : 0 < d) :
    selfCompressParams k d < 2 * L * d := by
  unfold selfCompressParams
  exact Nat.mul_lt_mul_of_lt_of_le (by omega)
    (Nat.le_refl d) hd

/-- **Soundness self-compress цикла**: композиция
(admit + certified-шаг + merge) × n итераций даёт
(а) телескоп-границу `step n ≤ o0 + bs.sum` (admit вклад 0,
шаги вклад ≤ 0, merge вклад b_i — делегат `grow_snap_cycle_sound`,
обобщение `adapter_snap_cycle_sound`-телескопа на цикл с merge) и (б) параметр-бюджет:
после каждого merge счёт = `selfCompressParams k d` — потому
`params n ≤ 2·k·d` при ЛЮБОМ n (знание растёт, объём — нет).
Первая компонента та же, что у `adapter_snap_cycle_sound`
(общий делегат), вторая — новая: цикл-инвариант параметров. -/
theorem self_compress_loop_sound (k d : ℕ) (o0 : ℝ)
    (bs : List ℝ) (step params : ℕ → ℝ)
    (h0 : step 0 ≤ o0)
    (hstep : ∀ i, i < bs.length →
      step (i + 1) ≤ step i + bs.getD i 0)
    (hparams : ∀ i, i ≤ bs.length →
      params i = selfCompressParams k d) :
    step bs.length ≤ o0 + bs.sum ∧
      params bs.length ≤ 2 * k * d :=
  ⟨grow_snap_cycle_sound o0 bs step h0 hstep, by
    have h := hparams bs.length (Nat.le_refl _)
    rw [h]
    exact le_of_eq (by simp [selfCompressParams])⟩

end SelfCompress

/-!
## constant cluster distillation (exact → adapter)

Дистилляция констант-кластеров (6 констант,
106/113 exact-покрытия) из символьного exact-гейта (ExactBypass) в АДАПТЕРНЫЕ веса: символьное знание живёт в
нейро-слое, ветвление exact-bypass отключается, контуры
унифицируются БЕЗ потерь CE.

Носитель — rank-1 ветка с внутренней bias-единицей:
`distillAdapter A B x = B *ᵥ (A *ᵥ x + 1)`, где единица —
конструктор ветки (не обучаемый вес). Конструкция θ(c) :=
(A := 0, B := const c): A-проекция игнорируется, внутренняя
координата ≡ 1, выход ≡ c на ЛЮБЫХ входах ТОЧНО — rank-1
адаптер МОЖЕТ представлять константу, `adapterVec` не
может (его выход содержит x). distill-условие: p = 1 на
кластере ⇒ ceSum = 0 — переносится КОМПОЗИЦИЕЙ с
`exact_gate_sound`, не копией доказательства.

Параметр-контраст ЧЕСТЕН в обе стороны: дистиллянт = 2d
параметров на кластер (Σ = 2·J·d), символьное хранение = J
констант-ЗНАЧЕНИЙ — дешевле (`symbolic_storage_cheaper`);
ценность дистилляции — унификация контуров (0 ветвлений,
единый matmul-путь), не экономия памяти. Bench-инстанс:
`--mode distill` (J = 6 кластеров, d = 4). -/
section ConstantDistill

open Hagi.Theory.ExactBypass

variable {d : Type*} [Fintype d] [Nonempty d]

/-- Rank-1 дистилл-ветка: down-фактор `A`, up-фактор `B`,
внутренняя координата с bias-единицей (конструктор ветки,
не вес). При A = 0 внутренняя координата ≡ 1 независимо от
входа — ветка может выдавать КОНСТАНТУ (в отличие от
`adapterVec`, чей выход содержит x). -/
def distillAdapter (A : Matrix (Fin 1) d ℝ)
    (B : Matrix d (Fin 1) ℝ) (x : d → ℝ) : d → ℝ :=
  B *ᵥ (A *ᵥ x + 1)

omit [Nonempty d] in
/-- **(точность конструкции)** θ(c) = (A := 0, B := const c):
выход дистилл-адаптера ≡ c на ЛЮБОМ входе, ТОЧНО (0·x + 1
= 1, c·1 = c). Символьная константа представима rank-1
адаптером с 2d параметрами без единого обучающего шага. -/
theorem constant_distill_exact (c : ℝ) (x : d → ℝ) :
    distillAdapter (0 : Matrix (Fin 1) d ℝ)
      (fun _ _ => c) x = fun _ => c := by
  funext i
  unfold distillAdapter
  simp [Matrix.mulVec, dotProduct]

open Classical in
/-- Вероятность, назначенная дистиллянтом (readout по
координате j): точное совпадение с целью ⇒ 1, иначе 0 —
мост от адаптерного выхода к p-семантике ExactBypass. -/
noncomputable def distillProb {ι : Type} (t : ι → ℝ)
    (f : ι → d → ℝ) (j : d)
    (A : Matrix (Fin 1) d ℝ) (B : Matrix d (Fin 1) ℝ) :
    ι → ℝ :=
  fun x => if (distillAdapter A B (f x)) j = t x then 1 else 0

omit [Nonempty d] in
/-- Кластер (t x = c на xs) покрыт дистиллянтом: p = 1 на
КАЖДОЙ позиции кластера — конструируется из
`constant_distill_exact` (выход ≡ c ⇒ readout = c = t x). -/
theorem distill_prob_one {ι : Type} (c : ℝ) (t : ι → ℝ)
    (f : ι → d → ℝ) (j : d) (xs : List ι)
    (hcl : ∀ x ∈ xs, t x = c) :
    ∀ x ∈ xs, distillProb t f j (0 : Matrix (Fin 1) d ℝ)
      (fun _ _ => c) x = 1 := by
  intro x hx
  unfold distillProb
  rw [constant_distill_exact]
  simp [hcl x hx]

open Classical in
/-- **(distill-условие / сохранение покрытия)**: после
дистилляции кластера CE на нём = 0 РОВНО — та же теорема
`ce_pointwise_of_prob_one` (переносится композицией:
constant_distill_exact → distill_prob_one → exact_gate_sound).
Exact-гейт можно отключить: нулевой CE обеспечивают веса. -/
theorem distill_coverage_preserved {ι : Type} (c : ℝ)
    (t : ι → ℝ) (f : ι → d → ℝ) (j : d) (xs : List ι)
    (hcl : ∀ x ∈ xs, t x = c) :
    ceSum (distillProb t f j (0 : Matrix (Fin 1) d ℝ)
      (fun _ _ => c)) xs = 0 :=
  exact_gate_sound _ xs
    (distill_prob_one c t f j xs hcl)

omit [Nonempty d] in
/-- Счёт параметров дистиллянта: rank-1 θ(c) несет РОВНО
2·card d параметров (down 1×d + up d×1) — делегат
`adapter_param_count` при r = Fin 1 (bias-единица —
конструктор, не вес). -/
theorem distill_param_count :
    (Finset.univ : Finset (Fin 1 × d)).card +
      (Finset.univ : Finset (d × Fin 1)).card =
    2 * Fintype.card d := by
  simpa using adapter_param_count (Fin 1) d

/-- J кластеров → Σ 2·d = 2·J·d параметров дистиллянта. -/
theorem distill_params_total (J d : ℕ) :
    (∑ _j ∈ Finset.range J, 2 * d) = 2 * J * d := by
  simp; ring

/-- **Честный контраст**: символьное хранение J констант-
ЗНАЧЕНИЙ дешевле дистиллянта (J < 2·J·d при d ≥ 2, J ≥ 1).
Ценность дистилляции — НЕ память, а унификация контуров
(0 ветвлений exact-гейта, единый adapter-путь) и слияние
exact-bypass с адаптерным остатком. -/
theorem symbolic_storage_cheaper (J d : ℕ)
    (hJ : 0 < J) (hd : 1 < d) : J < 2 * J * d := by
  have h1 : J * 2 ≤ J * d := Nat.mul_le_mul_left J hd
  have h2 : J < J * 2 := by nlinarith
  have h3 : J * d ≤ 2 * J * d := by nlinarith
  omega

end ConstantDistill

/-!
## mini-HAGI v3 — референсная сборка (universal
self-compressing distill loop)

Финальная композиция в ОДНОМ bench-прогоне
(`scripts/bench_bridge.py --mode mini-hagi-v3`, один трейс на
замороженном снапшоте живого корпуса): Ф1 exact-bypass
(констант-кластеры) → Ф2 distill (θ(c) rank-1 адаптеры,
CE = 0 бит-в-бит) → Ф3 certified fd-голова остатка →
Ф4 self-compress merge-цикл (параметры bounded) → Ф5 EB-стоп.
Новых глубоких фактов НЕТ — только корректная сборка уже
доказанных компонент.
-/

section V3Assembly

variable {d : Type*} [Fintype d] [Nonempty d]

/-- **(мини-HAGI v3, референсная сборка)**: единая
адаптерная машина = J дистиллированных констант-кластеров
(`distill_coverage_preserved` ⇒ CE = 0 на каждом кластере
ТОЧНО) + self-compress цикл (`self_compress_loop_sound` ⇒
obj-телескоп `step bs.length ≤ o0 + bs.sum` И параметр-бюджет
`params bs.length ≤ 2 * k * dd`). Конъюнкция компонент БЕЗ
ослабления их гипотез: каждый certified-шаг цикла сохраняет
телескоп, каждый merge сохраняет объём ≤ 2·k·dd, каждая
дистиллированная ветка сохраняет CE = 0. -/
theorem v3_assembly_sound {ι : Type} (k dd : ℕ)
    (hcard : Fintype.card d = dd)
    (t : ι → ℝ) (f : ι → d → ℝ) (j : d) (c : ℝ)
    (xs : List ι) (hcl : ∀ x ∈ xs, t x = c)
    (o0 : ℝ) (bs : List ℝ) (step params : ℕ → ℝ)
    (h0 : step 0 ≤ o0)
    (hstep : ∀ i, i < bs.length →
      step (i + 1) ≤ step i + bs.getD i 0)
    (hparams : ∀ i, i ≤ bs.length →
      params i = selfCompressParams k dd) :
    Hagi.Theory.ExactBypass.ceSum
      (distillProb t f j (0 : Matrix (Fin 1) d ℝ)
        (fun _ _ => c)) xs = 0 ∧
      step bs.length ≤ o0 + bs.sum ∧
      params bs.length ≤ 2 * k * dd := by
  have hsc := self_compress_loop_sound k dd o0 bs step
    params h0 hstep hparams
  exact ⟨distill_coverage_preserved c t f j xs hcl,
    hsc.1, hsc.2⟩

end V3Assembly

/-! ## cross-domain перенос адаптеров (honest-заметка)

Bench `--mode adapter-transfer`: warm-start домена B
копией обученного адаптера домена A vs холодный нулевой
старт, равные certified-бюджеты. Измерение на живом
корпусе: 3/3 пары (близкая/средняя/далёкая, близость
зарегистрирована ДО прогона) — T1-positive по AUC
CE-трейектории (drop-скорость), poisoned-инициализация хуже
по drop-скорости. НОВОЙ теоремы НЕ нужно: гарантия шага
`adapter_step_certified` сформулирована над произвольными
`s s'` — инициализация в неё не входит, поэтому warm-start
наслаждается той же certified-гарантией (переносимая теорема
тривиальна). Ценность — bench-измерение, не новый Lean-
факт (KISS). -/

end Hagi.Theory.AdapterGrowth
