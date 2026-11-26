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
import Hagi.Theory.MomentumAlign
import Hagi.Step.AdamDirection

/-!
# MasterTheoremV3 — лестница метатеорем-спецификаций certified-машины v3

Один файл, шесть namespace-блоков в порядке зависимости (`Hagi.Theory.MasterTheoremV3` →
`V31` → `V32` → `V33` → `V34` → `V35`; FQN стабильны). Новых глубоких фактов НЕТ
ни на одной ступени: каждый клоз — делегат к уже доказанной теореме, конъюнкция
берёт её hypotheses дословно (без ослабления).

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
- `hagi_master_v35` — += (O1)–(O6) optimizer-блок, единый контракт посылок `OptimizerPremises`.

НЕ дублирует `MasterTheorem.lean` (центральная теорема:
certified-or-refuse дихотомия reference-machine noisy-PL траекторий) — здесь машина
v3 bench-контура (distill + self-compress + adapter bank), другой носитель и делегаты.
-/

--! v3
namespace Hagi.Theory.MasterTheoremV3

open scoped InnerProductSpace

open Hagi.Theory.AdapterGrowth Hagi.Theory.MiniHagiLoop
  Hagi.Theory.NegativeTransfer

/-- **master_theorem_v3 — спецификация машины**: клозы (1)–(5)
карты выше выполняются одновременно для любого прогона v3-машины;
каждая конъюнкта — делегат к существующей теореме БЕЗ ослабления
гипотез. -/
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

/-- **hagi_master_v31 — certified-машина v3.1**:
клозы (1)–(8); (1)–(5) — проекции `master_theorem_v3`. -/
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

/-- **hagi_master_v32 — certified-машина v3.2**:
клозы (1)–(10); (1)–(8) — проекции `hagi_master_v31`. -/
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

/-- **hagi_master_v33 — certified-машина v3.3**:
клозы (1)–(11); (1)–(10) — проекции `hagi_master_v32`; (11) добавляет
`hw : 0 < w`, `hdiv : w ∣ B`. -/
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

/-- **hagi_master_v34 — certified-машина v3.4**:
клозы (1)–(14); (1)–(11) — проекции `hagi_master_v33`; (12)–(14) — три
независимых гипотезных блока (growth / Adam / holdout). -/
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

--! v3.5
namespace Hagi.Theory.MasterTheoremV35

open scoped InnerProductSpace

open Hagi.Theory.AdapterGrowth Hagi.Theory.MiniHagiLoop
  Hagi.Theory.NegativeTransfer Hagi.Theory.CoverageReading
  Hagi.Theory.GrowSnap Hagi.Theory.FunctionPreservingGrowth
  Hagi.Theory.HoldoutGateTwoWay Hagi.Theory.HoldoutRisk Hagi.Step
  Hagi.Probability Hagi.Theory.FirstLayerGrad Hagi.Theory.FirstLayerLip
  Hagi.Theory.FirstLayerLipBatch Hagi.Theory.MuonDescentW1Rect
  Hagi.Theory.MuonWide Hagi.Theory.MomentumAlign

/-- **`OptimizerPremises`** — единый контракт посылок оптимизаторного
блока v3.5: слой `W1 : ι → δ → ℝ`, батч `x`/`y`, метка `t`.
Поля — в точности посылки доказанных теорем (без ослабления):
`S_batch > 0`, равные ReLU-маски до/после шага `1/S_batch`, вне kink
на батче, батч-градиент ≠ 0; вне kink, `g ≠ 0` и `x ≠ 0` для
одиночного входа `xs`. -/
structure OptimizerPremises
    {ι δ K τ : Type} [Fintype ι] [Fintype δ] [Fintype K] [Nonempty K]
    [DecidableEq K] [Fintype τ] [Nonempty τ]
    (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ) (x : τ → δ → ℝ)
    (W1 : ι → δ → ℝ) (xs : δ → ℝ) (t : K) : Prop where
  hS : 0 < S_batch wo x
  hsame : ∀ t' i, reluMask (w1Pre (x t')
      (fun i j => W1 i j + (1 / S_batch wo x) * w1BatchDescentDir y b wo x W1 i j) i + b i)
      = reluMask (w1Pre (x t') W1 i + b i)
  hact : ∀ t' i, w1Pre (x t') W1 i + b i ≠ 0
  hG : w1BatchGradR x y b wo W1 ≠ 0
  hactS : ∀ i, w1Pre xs W1 i + b i ≠ 0
  hxS : xs ≠ 0
  hgS : Hagi.Theory.BatchRankOne.rowGrad xs b wo W1
    (Hagi.Energy.smax (w1L W1 b wo xs)) (Hagi.Theory.MuonDescentW1.onehot t) ≠ 0

/-- **hagi_master_v35 — optimizer-блок**: клозы
(1)–(14) карты v3.4 — проекции `hagi_master_v34`; оптимизаторный блок
= контракт (O7) ∧ (O1) ∧ … ∧ (O6), каждая конъюнкта —
делегат к доказанной теореме без ослабления посылок:
(O1) grad structure — `w1_grad_rank_one`, `batch_directional_derivative`;
(O2) smooth step — `w1BatchCE_optimal_step_drop` (γ* = 1/S_batch, сумма
CE по батчу; mean-форма кода — `w1MeanCE_optimal_step_drop`), `dir_drop_optimal`;
(O3) Muon optimality — `muon_step_optimal_in_isometry_group`, `wide_step_optimal'`;
(O4) NS approximation — `ns_sigma_min_three`, `muon_alignment_exact`, `wide_alignment_exact'`;
(O5) descent certificate — `muon_step_useful_w1_rect'`, `muon_step_useful_w1_rect_batch'`;
(O6) momentum — `momentum_align_cs`, `momentum_align_ge_grad`, `muon_momentum_bound`.
(O7) honest-closure — сам контракт `OptimizerPremises` (первая конъюнкта блока);
прочие посылки (`d ≠ 0`, `0 ≤ μ`, `⟪grad z, m_prev⟫ ≥ ‖grad z‖²`, `card m ≤ card n`,
`σ ∈ [1/2, 1]`, `m ≠ 0`) — в точности посылки делегатов. -/
theorem hagi_master_v35
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
    (hbudget : Real.log (2 * N / delta) ≤ 2 * (kh : ℝ) * (epsH / Bh) ^ 2)
    {ιO δO KO τO : Type} [Fintype ιO] [DecidableEq ιO] [Fintype δO] [DecidableEq δO]
    [Fintype KO] [Nonempty KO] [DecidableEq KO] [Fintype τO] [Nonempty τO]
    (yO : τO → KO) (bO : ιO → ℝ) (woO : ιO → KO → ℝ) (xO : τO → δO → ℝ)
    (W1O : ιO → δO → ℝ) (xsO : δO → ℝ) (tO : KO) (kO : ℕ)
    (hP : OptimizerPremises yO bO woO xO W1O xsO tO)
    (dO : E) (hdO : dO ≠ 0)
    (μ : ℝ) (mPrev : E) (hμ0 : 0 ≤ μ)
    (hagr : ‖grad z‖ ^ 2 ≤ ⟪grad z, mPrev⟫_ℝ)
    {nO : Type} [Fintype nO] [DecidableEq nO] (Gm : Matrix nO nO ℝ)
    {mO nW : Type} [Fintype mO] [DecidableEq mO] [Fintype nW] [DecidableEq nW]
    (Gw : Matrix mO nW ℝ) (hwO : Fintype.card mO ≤ Fintype.card nW)
    (σ : ℝ) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1)
    (Gp mm : Matrix ιO δO ℝ) (hmm : mm ≠ 0) :
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
            popMean (ℓ (cand ωs)) ≤ popMean (ℓ old) + 2 * epsH - margin)) ∧
      OptimizerPremises yO bO woO xO W1O xsO tO ∧
      ((∀ p q : KO → ℝ, ∀ jq : ιO × δO,
          Hagi.Theory.FunctionPreservingGrowth.chainGrad (w1Entry xsO bO woO W1O) p q jq
            = Hagi.Theory.FunctionPreservingGrowth.chainGrad
                (fun v i => reluMask (w1Pre xsO W1O i + bO i) * woO i v) p q jq.1 * xsO jq.2) ∧
        (∀ Δ : ιO → δO → ℝ, ∀ p q : τO → KO → ℝ,
          ∑ t', ∑ v, (p t' v - q t' v) * w1Jac (xO t') bO woO W1O Δ v
            = -∑ i, ∑ j, Hagi.Theory.BatchRankOne.batchGrad
                (fun t' => Hagi.Theory.BatchRankOne.rowGrad (xO t') bO woO W1O (p t') (q t'))
                xO i j * Δ i j)) ∧
      (w1BatchCE yO bO woO xO (fun i j => W1O i j
          + (1 / S_batch woO xO) * w1BatchDescentDir yO bO woO xO W1O i j)
          ≤ w1BatchCE yO bO woO xO W1O
            - parNorm (w1BatchDescentDir yO bO woO xO W1O) ^ 2 / (2 * S_batch woO xO) ∧
        f (z + (-⟪grad z, dO⟫_ℝ / (L * ‖dO‖ ^ 2)) • dO)
          ≤ f z - ⟪grad z, dO⟫_ℝ ^ 2 / (2 * L * ‖dO‖ ^ 2)) ∧
      (((∀ Δ : Matrix nO nO ℝ, Hagi.Theory.MuonIsometry.Isometry Δ →
           Hagi.Theory.MuonSpectral.fdot Gm Δ ≤ Hagi.Theory.MuonIsometry.ssum Gm) ∧
         ∃ Δ : Matrix nO nO ℝ, Hagi.Theory.MuonIsometry.Isometry Δ ∧
           Hagi.Theory.MuonSpectral.fdot Gm Δ = Hagi.Theory.MuonIsometry.ssum Gm) ∧
        ∃ (σw : mO → ℝ) (Pw : Matrix mO nW ℝ),
          (∀ i, 0 ≤ σw i) ∧ Pw * Pw.transpose = 1 ∧
          MuonWide.fdot_wide Gw Pw = ∑ i, σw i ∧
          ∀ Δ : Matrix mO nW ℝ, Δ * Δ.transpose = 1 → MuonWide.fdot_wide Gw Δ ≤ ∑ i, σw i) ∧
      (39 / 40 ≤ Hagi.Theory.NewtonSchulzSigma.ns_seq 3 σ ∧
        Hagi.Theory.MuonSpectral.fdot Gm (Hagi.Theory.MuonAlignment.ns_iter kO Gm)
          = ∑ i, Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues Gm i
              * Hagi.Theory.NewtonSchulzSigma.ns_seq kO
                (Hagi.External.Flywheel.Matrix.SVD.Real.realSingularValues Gm i) ∧
        ∃ σa : mO → ℝ, (∀ i, 0 ≤ σa i) ∧
          MuonWide.fdot_wide Gw (MuonWide.wide_iter kO Gw)
            = ∑ i, σa i * Hagi.Theory.NewtonSchulzSigma.ns_seq kO (σa i)) ∧
      ((∃ η : ℝ, 0 < η ∧ Hagi.ceOneHot tO
          (w1L (fun i j => W1O i j - η * w1StepR (w1GradR xsO bO woO W1O tO) kO i j) bO woO xsO)
          < Hagi.ceOneHot tO (w1L W1O bO woO xsO)) ∧
        ∃ η : ℝ, 0 < η ∧ w1BatchObjR xO yO bO woO (fun i j => W1O i j
            - η * w1StepR (w1BatchGradR xO yO bO woO W1O) kO i j)
          < w1BatchObjR xO yO bO woO W1O) ∧
      ((1 - μ) * ‖grad z‖ ^ 2 - |μ| * ‖grad z‖ * ‖mPrev‖ ≤ ⟪grad z, mom μ mPrev (grad z)⟫_ℝ ∧
        ‖grad z‖ ^ 2 ≤ ⟪grad z, mom μ mPrev (grad z)⟫_ℝ ∧
        Real.sqrt (Hagi.Theory.WideSVD.wfrobSq mm) - Real.sqrt (Hagi.Theory.WideSVD.wfrobSq (Gp - mm))
            * Real.sqrt (Hagi.Theory.WideSVD.wfrobSq (momStep mm kO))
          ≤ fdot_wide Gp (momStep mm kO)) := by
  have hV34 := Hagi.Theory.MasterTheoremV34.hagi_master_v34 k dd
    _hcard o0 bs step params h0 hstep hparams s a hfroz τ CovP n st
    hAdd i h0c θ tB Lq dq εq hεq hLd0 hLdq nc kc hkc f grad L γ G
    hγ hγL hL nE z hsm hG nB B w s' hB hs hsw hw hdiv
    Lb b bη D t ag R fOld hlin hR hrange ha hdesc hmax hce0
    g hg epsA hepsA hkh ℓ hBh hℓ old cand margin epsH hepsH
    N delta hN hdelta hcardΘ hbudget
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, h10, h11⟩ := hV34
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, h10, h11.1,
    fun Ll hLl => h11.2.1 Ll hLl,
    h11.2.2.1, h11.2.2.2.1, h11.2.2.2.2, hP,
    ⟨fun p q jq => w1_grad_rank_one xsO bO woO W1O p q jq,
      fun Δ p q =>
        Hagi.Theory.BatchRankOne.batch_directional_derivative xO bO woO W1O Δ p q⟩,
    ⟨w1BatchCE_optimal_step_drop yO bO woO xO W1O hP.hS hP.hsame,
      Hagi.Theory.MomentumAlign.dir_drop_optimal f grad L z dO hL hdO hsm⟩,
    ⟨Hagi.Theory.MuonIsometry.muon_step_optimal_in_isometry_group Gm,
      Hagi.Theory.WideSVD.wide_step_optimal' Gw hwO⟩,
    ⟨Hagi.Theory.NewtonSchulzSigma.ns_sigma_min_three hσ0 hσ1,
      Hagi.Theory.MuonAlignment.muon_alignment_exact Gm kO,
      Hagi.Theory.WideSVD.wide_alignment_exact' Gw hwO kO⟩,
    ⟨muon_step_useful_w1_rect' xsO bO woO W1O tO kO hP.hactS hP.hgS hP.hxS,
      muon_step_useful_w1_rect_batch' xO yO bO woO W1O kO hP.hact hP.hG⟩,
    ⟨Hagi.Theory.MomentumAlign.momentum_align_cs (grad z) mPrev μ,
      Hagi.Theory.MomentumAlign.momentum_align_ge_grad (grad z) mPrev μ hμ0 hagr,
      Hagi.Theory.MomentumAlign.muon_momentum_bound Gp mm hmm kO⟩⟩

#print axioms hagi_master_v35

end Hagi.Theory.MasterTheoremV35
