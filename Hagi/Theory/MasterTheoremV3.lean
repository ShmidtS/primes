/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 authors
-/

import Mathlib.Tactic
import Hagi.Theory.AdapterGrowth
import Hagi.Theory.MiniHagiLoop
import Hagi.Theory.NegativeTransfer
import Hagi.Theory.GrowSnap
import Hagi.Theory.CoverageReading
import Hagi.Theory.FunctionPreservingGrowth
import Hagi.Theory.HoldoutGateTwoWay
import Hagi.Step.AdamDirection

/-!
# MasterTheoremV3 — лестница метатеорем-спецификаций certified-машины v3

Один файл, пять namespace-блоков в порядке зависимости
(`Hagi.Theory.MasterTheoremV3` → `V31` → `V32` → `V33` → `V34`; FQN
стабильны). Новых глубоких фактов НЕТ ни на одной ступени: каждый
клоз — делегат к уже доказанной теореме, конъюнкция берёт её
hypotheses дословно (без ослабления).

## Карта клозов (все 14, делегаты rg-проверены)

| Клоз | Гарантия | Делегат |
|---|---|---|
| (1) | параметры ≤ 2·k·dd при любом n цикла | `self_compress_loop_sound` |
| (2) | забывание = 0 (изоляция per-task адаптеров) | `adapter_per_task_sound` |
| (3) | obj-цепь certified: телескоп ≤ o0 + Σ bounds | `self_compress_loop_sound` |
| (4) | покрытие монотонно вдоль append-only цикла | `iterative_loop_sound` |
| (5) | перенос управляем iff-границей 2⟪θ,t⟫ vs ‖θ‖² | `neg_transfer_char` |
| (6) | snap-грид k* минимален для ε-бюджета | `snap_k_eq_ceil` |
| (7) | вход прочитан побайтово (contiguous coverage) | `covStarts_covers` |
| (8) | smooth sufficient-граница переноса (равный бюджет) | `smooth_obj_transfer_bound` |
| (9) | schedule-оптимум: γ* = 1/L, max drop = G²/(2L) | `nl_drop_optimal` |
| (10) | иерархическое покрытие ЛЮБОГО n (peak ≤ m) | `hier_covers_any_n` |
| (11) | reading floor: total = ⌈n/w⌉ = floor любого покрытия | `hier_optimal` |
| (12) | growth: полезный первый шаг (strict CE-улучшение) | `first_step_strict_improves` |
| (13) | Adam: ⟨g, d⟩ > 0 на первом шаге | `adam_first_step_dot_pos` |
| (14) | holdout-гейт: принятый ⇒ pop-риск ≤ old + 2ε − margin | `holdout_gate_two_way_delta` |

## Дельты версий (каждая ступень = предыдущая + добор)

- `master_theorem_v3` — клозы (1)–(5): референсная
  метатеорема-сборка уровнем выше `v3_assembly_sound`.
- `hagi_master_v31` — += (6)–(8): клозы (1)–(5) проведены
  проекциями `hV3`. Клозы (5) + (8) = двухуровневый
  transfer-certified-контур: квадратичный iff (точный) + smooth
  sufficient (консервативный).
- `hagi_master_v32` — += (9)–(10): клозы (1)–(8) проведены
  одним делегатом `hagi_master_v31` (`have hV31`); (9)–(10)
  переиспользуют L/G/hL из гипотез v3.1.
- `hagi_master_v33` — += (11): клозы (1)–(10) проведены одним
  делегатом `hagi_master_v32` (`have hV32`); (11) переиспользует
  nB/B из hier-блока v3.2 и добавляет `hw : 0 < w`, `hdiv : w ∣ B`.
- `hagi_master_v34` — += (12)–(14): клозы (1)–(11) проведены одним
  делегатом `hagi_master_v33` (`have hV33`); (12)–(14) — три
  НОВЫХ гипотезных блока trailing (growth / Adam / holdout), между
  собой независимые. Внутри (12) клоз `exists_useful_eta` следует
  из тех же гипотез, поэтому в конъюнкцию не дублируется.

НЕ дублирует `MasterTheorem.lean` (центральная теорема A17
audit'а: certified-or-refuse дихотомия reference-machine noisy-PL
траекторий) — здесь машина v3 bench-контура (distill + self-compress
+ adapter bank), другой носитель и другие делегаты.
-/

--! v3
namespace Hagi.Theory.MasterTheoremV3

open scoped InnerProductSpace

open Hagi.Theory.AdapterGrowth Hagi.Theory.MiniHagiLoop
  Hagi.Theory.NegativeTransfer

/-- **(master_theorem_v3, — спецификация машины)**: для любого
прогона v3-машины на любом конечном корпусе ВСЕ пять гарантий
выполняются одновременно — existentially-quantified композиция
полных частей: (1) параметр-бюджет `params bs.length ≤ 2·k·dd` —
знание растёт, объём нет (`self_compress_loop_sound.2`); (2)
zero-forgetting — выход замороженной задачи неизменен ТОЧНО
(`adapter_per_task_sound`); (3) obj-цепь certified — телескоп
`step bs.length ≤ o0 + bs.sum` (`self_compress_loop_sound.1`);
(4) покрытие монотонно — каждая ранее покрытая позиция остаётся
покрытой (`iterative_loop_sound` при k = 0); (5) warm-перенос
управляем ТОЧНОЙ границей `2⟪θ,t⟫ vs ‖θ‖²` (`neg_transfer_char`).
Каждая конъюнкта — делегат к существующей теореме БЕЗ ослабления
гипотез; адапт-мосты не нужны (формулировки уже итоговые). -/
theorem master_theorem_v3
    {d : Type*} [Fintype d] [Nonempty d] {ι : Type}
    (k dd : ℕ) (_hcard : Fintype.card d = dd)
    (o0 : ℝ) (bs : List ℝ) (step params : ℕ → ℝ)
    (h0 : step 0 ≤ o0)
    (hstep : ∀ i, i < bs.length →
      step (i + 1) ≤ step i + bs.getD i 0)
    (hparams : ∀ i, i ≤ bs.length →
      params i = selfCompressParams k dd)
    {r : Type*} [Fintype r]
    (s : ℕ → ι → AdaptState r d) (a : ι)
    (hfroz : ∀ t', s (t' + 1) a = s t' a) (τ : ℕ)
    {Prog : Type} (CovP : Prog → ι → Prop) (n : ℕ)
    (st : ℕ → IterState Prog ι)
    (hAdd : ∀ k' < n, ∃ new, st (k' + 1) = iterStep (st k') new)
    (i : ι) (h0c : coversPrim CovP (st 0) i)
    {m : Type*} [Fintype m] (θ tB : EuclideanSpace ℝ m) :
    params bs.length ≤ 2 * k * dd ∧
      perTaskVec (s τ) a = perTaskVec (s 0) a ∧
      step bs.length ≤ o0 + bs.sum ∧
      coversPrim CovP (st n) i ∧
      (quadObj tB θ > quadObj tB 0 ↔ 2 * ⟪θ, tB⟫_ℝ < ‖θ‖ ^ 2) := by
  have hsc := self_compress_loop_sound k dd o0 bs step params h0
    hstep hparams
  exact ⟨hsc.2,
    adapter_per_task_sound s a hfroz τ,
    hsc.1,
    iterative_loop_sound CovP n st hAdd 0 (Nat.zero_le n) i h0c,
    neg_transfer_char θ tB⟩

#print axioms master_theorem_v3

end Hagi.Theory.MasterTheoremV3

--! v3.1
namespace Hagi.Theory.MasterTheoremV31

open scoped InnerProductSpace

open Hagi.Theory.AdapterGrowth Hagi.Theory.MiniHagiLoop
  Hagi.Theory.NegativeTransfer Hagi.Theory.GrowSnap
  Hagi.Theory.CoverageReading

/-- **(hagi_master_v31, — консолидация certified-машины v3.1)**:
для любого прогона v3-машины все ПЯТЬ гарантий v3 (параметр-бюджет,
zero-forgetting, certified obj-телескоп, монотонность покрытия,
точный iff-transfer) выполняются одновременно, И к ним три клоза
добора: (6) оптимальный snap-грид `snapK = ⌈log₂(L·d/ε)⌉ − 1`
минимален для ε-бюджета при `ε < L·d`; (7) каждый байт входа
`i < n` покрыт некоторым окном `[s, s + k)` решётки `covStarts`;
(8) для L-smooth objective с равным GD-бюджетом финал зажат
`f z − n•nlBudget ≤ f (nlRun n γ grad z) ≤ f z` (sufficient-уровень
двухуровневого transfer-контура рядом с точным iff (5)). Каждая
конъюнкта — делегат к существующей теореме БЕЗ ослабления гипотез. -/
theorem hagi_master_v31
    {d : Type*} [Fintype d] [Nonempty d] {ι : Type}
    (k dd : ℕ) (_hcard : Fintype.card d = dd)
    (o0 : ℝ) (bs : List ℝ) (step params : ℕ → ℝ)
    (h0 : step 0 ≤ o0)
    (hstep : ∀ i, i < bs.length →
      step (i + 1) ≤ step i + bs.getD i 0)
    (hparams : ∀ i, i ≤ bs.length →
      params i = selfCompressParams k dd)
    {r : Type*} [Fintype r]
    (s : ℕ → ι → AdaptState r d) (a : ι)
    (hfroz : ∀ t', s (t' + 1) a = s t' a) (τ : ℕ)
    {Prog : Type} (CovP : Prog → ι → Prop) (n : ℕ)
    (st : ℕ → IterState Prog ι)
    (hAdd : ∀ k' < n, ∃ new, st (k' + 1) = iterStep (st k') new)
    (i : ι) (h0c : coversPrim CovP (st 0) i)
    {m : Type} [Fintype m] (θ tB : EuclideanSpace ℝ m)
    (Lq dq εq : ℝ) (hεq : 0 < εq) (hLd0 : (0:ℝ) ≤ Lq * dq)
    (hLdq : εq < Lq * dq)
    (nc kc : ℕ) (hkc : 0 < kc)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (L γ G : ℝ)
    (hγ : 0 < γ) (hγL : γ ≤ 2 / L) (hL : 0 < L)
    (nE : ℕ) (z : E)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (hG : ∀ k', k' ≤ nE → ‖grad (nlRun k' γ grad z)‖ ≤ G) :
    params bs.length ≤ 2 * k * dd ∧
      perTaskVec (s τ) a = perTaskVec (s 0) a ∧
      step bs.length ≤ o0 + bs.sum ∧
      coversPrim CovP (st n) i ∧
      (quadObj tB θ > quadObj tB 0 ↔ 2 * ⟪θ, tB⟫_ℝ < ‖θ‖ ^ 2) ∧
      (snapK Lq dq εq hεq hLd0
        = Nat.ceil (Real.logb 2 (Lq * dq / εq)) - 1) ∧
      (∀ ib < nc, ∃ sw ∈ covStarts nc kc, sw ≤ ib ∧ ib < sw + kc) ∧
      (f z - nE * nlBudget γ L G ≤ f (nlRun nE γ grad z)
        ∧ f (nlRun nE γ grad z) ≤ f z) := by
  have hV3 := Hagi.Theory.MasterTheoremV3.master_theorem_v3 k dd _hcard o0 bs step params h0
    hstep hparams s a hfroz τ CovP n st hAdd i h0c θ tB
  exact ⟨hV3.1, hV3.2.1, hV3.2.2.1, hV3.2.2.2.1, hV3.2.2.2.2,
    snap_k_eq_ceil Lq dq εq hεq hLdq,
    covStarts_covers nc kc hkc,
    smooth_obj_transfer_bound f grad L γ G hγ hγL hL nE z hsm hG⟩

#print axioms hagi_master_v31

end Hagi.Theory.MasterTheoremV31

--! v3.2
namespace Hagi.Theory.MasterTheoremV32

open scoped InnerProductSpace

open Hagi.Theory.AdapterGrowth Hagi.Theory.MiniHagiLoop
  Hagi.Theory.NegativeTransfer Hagi.Theory.CoverageReading
  Hagi.Theory.GrowSnap

/-- **(hagi_master_v32, — консолидация certified-машины v3.2)**:
все 8 гарантий v3.1 (`hagi_master_v31`) выполняются
одновременно, И к ним (9) schedule-клоз: guaranteed per-step drop
при оптимальном шаге γ* = 1/L равен `G ^ 2 / (2 * L)`
(`nl_drop_optimal`); (10) hierarchical-coverage-клоз: без
верхней границы на n каждый байт `i < nB` входа покрыт окном
`[t, t + w)` решётки `hierStarts nB B w s'` при `0 < B`, `0 < s' ≤ w`
(`hier_covers_any_n`, peak ≤ m — streaming-чтение любого
объёма). Каждая конъюнкта — делегат БЕЗ ослабления гипотез;
клозы (9)–(10) переиспользуют L/G/hL из гипотез v3.1. -/
theorem hagi_master_v32
    {d : Type*} [Fintype d] [Nonempty d] {ι : Type}
    (k dd : ℕ) (_hcard : Fintype.card d = dd)
    (o0 : ℝ) (bs : List ℝ) (step params : ℕ → ℝ)
    (h0 : step 0 ≤ o0)
    (hstep : ∀ i, i < bs.length →
      step (i + 1) ≤ step i + bs.getD i 0)
    (hparams : ∀ i, i ≤ bs.length →
      params i = selfCompressParams k dd)
    {r : Type*} [Fintype r]
    (s : ℕ → ι → AdaptState r d) (a : ι)
    (hfroz : ∀ t', s (t' + 1) a = s t' a) (τ : ℕ)
    {Prog : Type} (CovP : Prog → ι → Prop) (n : ℕ)
    (st : ℕ → IterState Prog ι)
    (hAdd : ∀ k' < n, ∃ new, st (k' + 1) = iterStep (st k') new)
    (i : ι) (h0c : coversPrim CovP (st 0) i)
    {m : Type} [Fintype m] (θ tB : EuclideanSpace ℝ m)
    (Lq dq εq : ℝ) (hεq : 0 < εq) (hLd0 : (0:ℝ) ≤ Lq * dq)
    (hLdq : εq < Lq * dq)
    (nc kc : ℕ) (hkc : 0 < kc)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (L γ G : ℝ)
    (hγ : 0 < γ) (hγL : γ ≤ 2 / L) (hL : 0 < L)
    (nE : ℕ) (z : E)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (hG : ∀ k', k' ≤ nE → ‖grad (nlRun k' γ grad z)‖ ≤ G)
    (nB B w s' : ℕ) (hB : 0 < B) (hs : 0 < s') (hsw : s' ≤ w) :
    params bs.length ≤ 2 * k * dd ∧
      perTaskVec (s τ) a = perTaskVec (s 0) a ∧
      step bs.length ≤ o0 + bs.sum ∧
      coversPrim CovP (st n) i ∧
      (quadObj tB θ > quadObj tB 0 ↔ 2 * ⟪θ, tB⟫_ℝ < ‖θ‖ ^ 2) ∧
      (snapK Lq dq εq hεq hLd0
        = Nat.ceil (Real.logb 2 (Lq * dq / εq)) - 1) ∧
      (∀ ib < nc, ∃ sw ∈ covStarts nc kc, sw ≤ ib ∧ ib < sw + kc) ∧
      (f z - nE * nlBudget γ L G ≤ f (nlRun nE γ grad z)
        ∧ f (nlRun nE γ grad z) ≤ f z) ∧
      nlDrop (1 / L) L G = G ^ 2 / (2 * L) ∧
      ∀ ib < nB, ∃ t ∈ hierStarts nB B w s', t ≤ ib ∧ ib < t + w := by
  have hV31 := Hagi.Theory.MasterTheoremV31.hagi_master_v31 k dd
    _hcard o0 bs step params h0 hstep hparams s a hfroz τ CovP n st
    hAdd i h0c θ tB Lq dq εq hεq hLd0 hLdq nc kc hkc f grad L γ G
    hγ hγL hL nE z hsm hG
  exact ⟨hV31.1, hV31.2.1, hV31.2.2.1, hV31.2.2.2.1,
    hV31.2.2.2.2.1, hV31.2.2.2.2.2.1, hV31.2.2.2.2.2.2.1,
    hV31.2.2.2.2.2.2.2, nl_drop_optimal L G hL,
    hier_covers_any_n nB B w s' hB hs hsw⟩

#print axioms hagi_master_v32

end Hagi.Theory.MasterTheoremV32

--! v3.3
namespace Hagi.Theory.MasterTheoremV33

open scoped InnerProductSpace

open Hagi.Theory.AdapterGrowth Hagi.Theory.MiniHagiLoop
  Hagi.Theory.NegativeTransfer Hagi.Theory.CoverageReading
  Hagi.Theory.GrowSnap

/-- **(hagi_master_v33, — консолидация certified-машины v3.3)**:
все 10 гарантий v3.2 (`hagi_master_v32`) выполняются
одновременно, И к ним (11) reading-floor-клоз: при строчке `s = w`
(`hierStarts nB B w w`) и `w ∣ B` total окон равен
`(nB + w - 1) / w = ⌈nB/w⌉` — информационному минимуму — и НЕ
превышается никаким списком `L`, покрывающим `[0, nB)` окнами
длины `w` (`hier_optimal`). Каждая конъюнкта — делегат БЕЗ
ослабления гипотез; клоз (11) переиспользует nB/B из hier-блока
v3.2 и добавляет `hw : 0 < w`, `hdiv : w ∣ B`. -/
theorem hagi_master_v33
    {d : Type*} [Fintype d] [Nonempty d] {ι : Type}
    (k dd : ℕ) (_hcard : Fintype.card d = dd)
    (o0 : ℝ) (bs : List ℝ) (step params : ℕ → ℝ)
    (h0 : step 0 ≤ o0)
    (hstep : ∀ i, i < bs.length →
      step (i + 1) ≤ step i + bs.getD i 0)
    (hparams : ∀ i, i ≤ bs.length →
      params i = selfCompressParams k dd)
    {r : Type*} [Fintype r]
    (s : ℕ → ι → AdaptState r d) (a : ι)
    (hfroz : ∀ t', s (t' + 1) a = s t' a) (τ : ℕ)
    {Prog : Type} (CovP : Prog → ι → Prop) (n : ℕ)
    (st : ℕ → IterState Prog ι)
    (hAdd : ∀ k' < n, ∃ new, st (k' + 1) = iterStep (st k') new)
    (i : ι) (h0c : coversPrim CovP (st 0) i)
    {m : Type} [Fintype m] (θ tB : EuclideanSpace ℝ m)
    (Lq dq εq : ℝ) (hεq : 0 < εq) (hLd0 : (0 : ℝ) ≤ Lq * dq)
    (hLdq : εq < Lq * dq)
    (nc kc : ℕ) (hkc : 0 < kc)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (L γ G : ℝ)
    (hγ : 0 < γ) (hγL : γ ≤ 2 / L) (hL : 0 < L)
    (nE : ℕ) (z : E)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (hG : ∀ k', k' ≤ nE → ‖grad (nlRun k' γ grad z)‖ ≤ G)
    (nB B w s' : ℕ) (hB : 0 < B) (hs : 0 < s') (hsw : s' ≤ w)
    (hw : 0 < w) (hdiv : w ∣ B) :
    params bs.length ≤ 2 * k * dd ∧
      perTaskVec (s τ) a = perTaskVec (s 0) a ∧
      step bs.length ≤ o0 + bs.sum ∧
      coversPrim CovP (st n) i ∧
      (quadObj tB θ > quadObj tB 0 ↔ 2 * ⟪θ, tB⟫_ℝ < ‖θ‖ ^ 2) ∧
      (snapK Lq dq εq hεq hLd0
        = Nat.ceil (Real.logb 2 (Lq * dq / εq)) - 1) ∧
      (∀ ib < nc, ∃ sw ∈ covStarts nc kc, sw ≤ ib ∧ ib < sw + kc) ∧
      (f z - nE * nlBudget γ L G ≤ f (nlRun nE γ grad z)
        ∧ f (nlRun nE γ grad z) ≤ f z) ∧
      nlDrop (1 / L) L G = G ^ 2 / (2 * L) ∧
      (∀ ib < nB, ∃ t ∈ hierStarts nB B w s', t ≤ ib ∧ ib < t + w) ∧
      (hierStarts nB B w w).length = (nB + w - 1) / w ∧
      ∀ Ll : List ℕ, (∀ ib < nB, ∃ t ∈ Ll, t ≤ ib ∧ ib < t + w) →
        (nB + w - 1) / w ≤ Ll.length := by
  have hV32 := Hagi.Theory.MasterTheoremV32.hagi_master_v32 k dd
    _hcard o0 bs step params h0 hstep hparams s a hfroz τ CovP n st
    hAdd i h0c θ tB Lq dq εq hεq hLd0 hLdq nc kc hkc f grad L γ G
    hγ hγL hL nE z hsm hG nB B w s' hB hs hsw
  exact ⟨hV32.1, hV32.2.1, hV32.2.2.1, hV32.2.2.2.1,
    hV32.2.2.2.2.1, hV32.2.2.2.2.2.1, hV32.2.2.2.2.2.2.1,
    hV32.2.2.2.2.2.2.2.1, hV32.2.2.2.2.2.2.2.2.1,
    hV32.2.2.2.2.2.2.2.2.2, hier_optimal nB B w hw hB hdiv⟩

#print axioms hagi_master_v33

end Hagi.Theory.MasterTheoremV33

--! v3.4
namespace Hagi.Theory.MasterTheoremV34

open scoped InnerProductSpace

open Hagi.Theory.AdapterGrowth Hagi.Theory.MiniHagiLoop
  Hagi.Theory.NegativeTransfer Hagi.Theory.CoverageReading
  Hagi.Theory.GrowSnap Hagi.Theory.FunctionPreservingGrowth
  Hagi.Theory.HoldoutGateTwoWay Hagi.Theory.HoldoutRisk Hagi.Step
  Hagi.Probability

/-- **(hagi_master_v34, — консолидация certified-машины v3.4)**:
все 11 гарантий v3.3 (`hagi_master_v33`) выполняются одновременно, И
к ним три делегата growth-контура:
(12) при residual-сигнале `a < 0` и `stepEps < 2a²/R²` единственный
полезный первый шаг growth-блока даёт STRICT улучшение CE на
носителе `t` (`first_step_strict_improves`);
(13) первый шаг Adam — направление спуска: `⟨g, d⟩ > 0` при `g ≠ 0`
(`adam_first_step_dot_pos`);
(14) holdout-гейт two-way: при `|Θ| ≤ N`,
`log(2N/δ) ≤ 2k(ε/B)²` с вероятностью ≥ 1 − δ принятый кандидат
имеет популяционный риск ≤ old + 2ε − margin
(`holdout_gate_two_way_delta`).
Каждая конъюнкта — делегат БЕЗ ослабления гипотез. -/
theorem hagi_master_v34
    {d : Type*} [Fintype d] [Nonempty d] {ι : Type}
    (k dd : ℕ) (_hcard : Fintype.card d = dd)
    (o0 : ℝ) (bs : List ℝ) (step params : ℕ → ℝ)
    (h0 : step 0 ≤ o0)
    (hstep : ∀ i, i < bs.length →
      step (i + 1) ≤ step i + bs.getD i 0)
    (hparams : ∀ i, i ≤ bs.length →
      params i = selfCompressParams k dd)
    {r : Type*} [Fintype r]
    (s : ℕ → ι → AdaptState r d) (a : ι)
    (hfroz : ∀ t', s (t' + 1) a = s t' a) (τ : ℕ)
    {Prog : Type} (CovP : Prog → ι → Prop) (n : ℕ)
    (st : ℕ → IterState Prog ι)
    (hAdd : ∀ k' < n, ∃ new, st (k' + 1) = iterStep (st k') new)
    (i : ι) (h0c : coversPrim CovP (st 0) i)
    {m : Type} [Fintype m] (θ tB : EuclideanSpace ℝ m)
    (Lq dq εq : ℝ) (hεq : 0 < εq) (hLd0 : (0 : ℝ) ≤ Lq * dq)
    (hLdq : εq < Lq * dq)
    (nc kc : ℕ) (hkc : 0 < kc)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (L γ G : ℝ)
    (hγ : 0 < γ) (hγL : γ ≤ 2 / L) (hL : 0 < L)
    (nE : ℕ) (z : E)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (hG : ∀ k', k' ≤ nE → ‖grad (nlRun k' γ grad z)‖ ≤ G)
    (nB B w s' : ℕ) (hB : 0 < B) (hs : 0 < s') (hsw : s' ≤ w)
    (hw : 0 < w) (hdiv : w ∣ B)
    {K : Type} [Fintype K] [Nonempty K] {Bk : Type}
    (Lb : Bk → K → ℝ) (b : Bk) (bη : ℝ → Bk) (D : K → ℝ) (t : K)
    (ag R fOld : ℝ)
    (hlin : ∀ η u, Lb (bη η) u - Lb b u = η * D u)
    (hR : 0 < R) (hrange : ∀ u v, D u - D v ≤ R)
    (ha : ag = ∑ v, Hagi.Energy.smax (Lb b) v * D v - D t)
    (hdesc : ag < 0) (hmax : stepEps < 2 * ag ^ 2 / R ^ 2)
    (hce0 : Hagi.ceOneHot t (Lb b) = fOld)
    {ιA : Type*} [Fintype ιA] [Nonempty ιA]
    (g : ιA → ℝ) (hg : g ≠ 0) (epsA : ℝ) (hepsA : 0 < epsA)
    {Θ : Type} [Fintype Θ] {Ω : Type} [Fintype Ω] [Nonempty Ω]
    {kh : ℕ} (hkh : 0 < kh)
    (ℓ : Θ → Ω → ℝ) {Bh : ℝ} (hBh : 0 < Bh)
    (hℓ : ∀ θ ω, 0 ≤ ℓ θ ω ∧ ℓ θ ω ≤ Bh)
    (old : Θ) (cand : (Fin kh → Ω) → Θ) (margin epsH : ℝ)
    (hepsH : 0 < epsH) (N delta : ℝ) (hN : 0 < N) (hdelta : 0 < delta)
    (hcardΘ : (Fintype.card Θ : ℝ) ≤ N)
    (hbudget : Real.log (2 * N / delta) ≤ 2 * (kh : ℝ) * (epsH / Bh) ^ 2) :
    params bs.length ≤ 2 * k * dd ∧
      perTaskVec (s τ) a = perTaskVec (s 0) a ∧
      step bs.length ≤ o0 + bs.sum ∧
      coversPrim CovP (st n) i ∧
      (quadObj tB θ > quadObj tB 0 ↔ 2 * ⟪θ, tB⟫_ℝ < ‖θ‖ ^ 2) ∧
      (snapK Lq dq εq hεq hLd0
        = Nat.ceil (Real.logb 2 (Lq * dq / εq)) - 1) ∧
      (∀ ib < nc, ∃ sw ∈ covStarts nc kc, sw ≤ ib ∧ ib < sw + kc) ∧
      (f z - nE * nlBudget γ L G ≤ f (nlRun nE γ grad z)
        ∧ f (nlRun nE γ grad z) ≤ f z) ∧
      nlDrop (1 / L) L G = G ^ 2 / (2 * L) ∧
      (∀ ib < nB, ∃ t ∈ hierStarts nB B w s', t ≤ ib ∧ ib < t + w) ∧
      (hierStarts nB B w w).length = (nB + w - 1) / w ∧
      (∀ Ll : List ℕ, (∀ ib < nB, ∃ t ∈ Ll, t ≤ ib ∧ ib < t + w) →
        (nB + w - 1) / w ≤ Ll.length) ∧
      (∃ η : ℝ, 0 < η ∧ Hagi.ceOneHot t (Lb (bη η)) < fOld) ∧
      (0 < adamDot g (adamDir g (fun j => g j ^ 2) epsA)) ∧
      (1 - delta ≤
        prodPq (fun _ : Fin kh => popDens (Ω := Ω))
          (fun ωs => holdoutMean (ℓ (cand ωs)) ωs ≤
              holdoutMean (ℓ old) ωs - margin →
            popMean (ℓ (cand ωs)) ≤ popMean (ℓ old) + 2 * epsH - margin)) := by
  have hV33 := Hagi.Theory.MasterTheoremV33.hagi_master_v33 k dd
    _hcard o0 bs step params h0 hstep hparams s a hfroz τ CovP n st
    hAdd i h0c θ tB Lq dq εq hεq hLd0 hLdq nc kc hkc f grad L γ G
    hγ hγL hL nE z hsm hG nB B w s' hB hs hsw hw hdiv
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, h10, h11⟩ := hV33
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, h10, h11.1,
    fun Ll hLl => h11.2 Ll hLl,
    first_step_strict_improves Lb b bη D t ag R fOld hlin hR hrange ha
      hdesc hmax hce0,
    adam_first_step_dot_pos g hg hepsA,
    holdout_gate_two_way_delta hkh ℓ hBh hℓ old cand margin epsH hepsH
      N delta hN hdelta hcardΘ hbudget⟩

#print axioms hagi_master_v34

end Hagi.Theory.MasterTheoremV34
