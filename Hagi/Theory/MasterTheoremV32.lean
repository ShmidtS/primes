/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 authors
-/

import Hagi.Theory.MasterTheoremV31
import Hagi.Theory.NegativeTransfer

/-!
# MasterTheoremV32 — консолидированная метатеорема машины v3.2 (C614)

Roadmap C612 top-3: расширение `hagi_master_v31` (C600, 8 клозов)
до v3.2 — добавлены два клоза: schedule-оптимум шага (C606) и
иерархическое покрытие любого n (C611). Как и в C600, каждая
конъюнкта — делегат к уже доказанной теореме, hypotheses
дословно, БЕЗ ослабления; новых глубоких фактов НЕТ — только
конъюнкция (KISS). Клозы (1)–(8) проводятся одним делегатом
`hagi_master_v31` (C600) через проекции `have hV31`.

## Карта клозов (все 10)

| Клоз | Гарантия | Делегат |
|---|---|---|
| (1)–(8) | машина v3.1 (параметр-бюджет, zero-forgetting, certified obj-телескоп, монотонность покрытия, iff-transfer, snap-грид, coverage-чтение, smooth transfer) | `hagi_master_v31` (C600) |
| (9) | schedule-оптимум: γ* = 1/L, max drop = G²/(2L) | `nl_drop_optimal` (C606) |
| (10) | иерархическое покрытие ЛЮБОГО n (peak ≤ m) | `hier_covers_any_n` (C611) |
-/

namespace Hagi.Theory.MasterTheoremV32

open scoped InnerProductSpace

open Hagi.Theory.AdapterGrowth Hagi.Theory.MiniHagiLoop
  Hagi.Theory.NegativeTransfer Hagi.Theory.CoverageReading
  Hagi.Theory.GrowSnap

/-- **(hagi_master_v32, C614 — консолидация certified-машины v3.2)**:
все 8 гарантий v3.1 (`hagi_master_v31`, C600) выполняются
одновременно, И к ним (9) schedule-клоз: guaranteed per-step drop
при оптимальном шаге γ* = 1/L равен `G ^ 2 / (2 * L)`
(`nl_drop_optimal`, C606); (10) hierarchical-coverage-клоз: без
верхней границы на n каждый байт `i < nB` входа покрыт окном
`[t, t + w)` решётки `hierStarts nB B w s'` при `0 < B`, `0 < s' ≤ w`
(`hier_covers_any_n`, C611; peak ≤ m — streaming-чтение любого
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
