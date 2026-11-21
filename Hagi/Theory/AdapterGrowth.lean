/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Hagi.Theory.GrowSnap

/-!
# AdapterGrowth — certified low-rank адаптер роста (C532)

Существующие механизмы роста добавляют объём ЦЕЛИКОМ: fiber-width
C494 (`mkOrthoFiberBlock` — widening признаков) и depth-block
C504/C506/C521 (`benchResidualBlock γ h` — ЦЕЛЫЙ блок,
~d·d параметров при скрытой ширине ~d). C532 добавляет
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
`grow_block_obj_invariant` C504), ЯВНЫЙ счёт параметров с
неравенством против полного блока и certified-шаг обучения
адаптера (measured drop > 0 / HOLD — паттерн C506/C521).

Cycle-соответствие: `scripts/bench_bridge.py --mode adapter-grow`
исполняет ровно эту схему на живом корпусе unified_ledger:
trunk+head certified fd-шаги (C521 phase A), freeze trunk,
адаптер на голове `pred = w·(f + B·(A·f))` растёт при B = 0
(assert: obj-инвариант ТОЧНО), certified fd-шаги ТОЛЬКО по 2·r·d
параметрам адаптера (r = 1 → 8, r = 2 → 16 против 21 параметра
целого mh5-блока), head-to-head прогресс на равном числе шагов.

## Honest pins (что этот мост НЕ покрывает)

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
  premise — контракт C436); на шаге 0 добавка 0.
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
расширяется (в отличие от fiber-grow C494) и НЕ добавляется целый
блок (C504): рост живёт в существующем пространстве. -/
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
(congrArg-мост, паттерн `grow_block_obj_invariant` C504). -/
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
параметров — база сравнения объёма (identity-блок C504 при
скрытой ширине ~d). -/
theorem block_param_count : (Fintype.card d * Fintype.card d :
    ℕ) = (Finset.univ : Finset (d × d)).card := by
  simp [Fintype.card_prod]

/-- Экономия объёма: при `2 * card r ≤ card d` адаптер ранга `r`
строго меньше полного блока по числу параметров
(`2·r·d ≤ d·d`, равенство только при `2r = d`). Bench-инстанс
C532: r=1, d=4 → 8 ≤ 16. -/
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
— bench-семантика grow-цикла C506/C521 (admission drop > 0,
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

/-- Негатив (noBlockAdmissionWithoutMargin-паттерн C444):
отсутствие строгого drop ⇒ HOLD, состояние ТОЧНО не меняется —
нулевой/отрицательный кандидат не допускается. -/
theorem adapter_step_hold (h : ¬ obj s' < obj s) :
    adapterStep obj s s' = s := by
  unfold adapterStep
  split
  · rename_i h'; exact absurd h' h
  · rfl

end CertifiedStep

/-! ## C533: snap адаптера и телескоп составного цикла

Композиция C532×C521: рост уровня — адаптер (admission при
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
≤ старта + Σ b_i. Делегат к `grow_snap_cycle_sound` (C521,
индукция по списку bound'ов) — не копия доказательства. -/
theorem adapter_snap_cycle_sound (o0 : ℝ) (bs : List ℝ)
    (step : ℕ → ℝ) (h0 : step 0 ≤ o0)
    (hstep : ∀ i, i < bs.length →
      step (i + 1) ≤ step i + bs.getD i 0) :
    step bs.length ≤ o0 + bs.sum :=
  grow_snap_cycle_sound o0 bs step h0 hstep

end SnapCycle

/-! ## Ранговая адаптивность (C535): измеримый селектор ранга

Каркас C533, обобщённый на ранг r ∈ {1, 2}: на каждом уровне
ранг выбирается по ИЗМЕРЕННОМУ критерию probe-drop-на-параметр
(паттерн `hybridSelect` C510 — детерминированный селектор на
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
C510: case-on-state без ослабления). Probe-шаги в гарантию
не входят — они вычисляются на копии (C530 no-commit
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

/-! ## C536: SVD-Матрёшка — merge стека адаптеров компрессией

Стек L LoRA-уровней (C533/C535: `f ↦ (I + B_L A_L)·…·(I + B_1 A_1)·f`,
2·L·d параметров) сворачивается в ОДИН адаптер ранга k ≤ min(d, L):
суммарное возмущение Δ = Π(I+E_i) − I имеет ранг ≤ Σ рангов
E_i = L (структурный выигрыш: 2·k·d < 2·L·d параметров при k < L,
один matmul вместо L). Точная obj-близость после усечения —
σ_tail × Lipschitz (прецедент rank-trunc C498/C500 и
`Hagi.Contracts.TruncatedSVDTail.truncated_svd_error_eq_tail` —
ГОТОВАЯ форма ‖Δ − Δ_k‖² = Σ tail σ²; `mdl_rank_ce` — паттерн
kappaF-Lipschitz). Bench-инстанс: `--mode adapter-merge`
(точный rational rank + exact merge Δ = C·R при k = ρ; матрёшка
k < ρ — числовой power-iteration кандидат + ТОЧНЫЙ рациональный
per-point cert-bound, C489-принцип: числа не доверяем, доверяем
сертификату). -/
section Merge

open scoped Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Матричная композиция стека адаптеров: произведение
`Π (I + E_i)` по списку возмущений уровней (E_i = B_i·A_i — ранг
≤ r_i). Матричная форма fold-цепочки C533: уровень ℓ действует на
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
(C533/C535: L = 8, r = 1, d = 4): rank(Δ) ≤ 4 — merge даёт
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
функции стека (C533 `adapter_snap_bound`-паттерн: пошаговая
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

end Hagi.Theory.AdapterGrowth
