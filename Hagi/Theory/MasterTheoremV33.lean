/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 authors
-/

import Hagi.Theory.MasterTheoremV32
import Hagi.Theory.CoverageReading

/-!
# MasterTheoremV33 — консолидированная метатеорема машины v3.3 (C622)

Roadmap C620 top-2: расширение `hagi_master_v32` (C614, 10 клозов)
до v3.3 — добавлен reading-floor-клоз: total иерархического
покрытия при `s = w` и `w ∣ B` равен `⌈n/w⌉` — информационному
floor ЛЮБОГО покрытия (`hier_optimal`, C618). Как и в C600/C614,
каждая конъюнкта — делегат к уже доказанной теореме, hypotheses
дословно, БЕЗ ослабления; новых глубоких фактов НЕТ — только
конъюнкция (KISS). Клозы (1)–(10) проводятся одним делегатом
`hagi_master_v32` (C614) через проекции `have hV32`.

## Карта клозов (все 11)

| Клоз | Гарантия | Делегат |
|---|---|---|
| (1)–(8) | машина v3.1 (параметр-бюджет, zero-forgetting,
certified obj-телескоп, монотонность покрытия, iff-transfer,
snap-грид, coverage-чтение, smooth transfer) |
  `hagi_master_v31` (C600), через `hagi_master_v32` |
| (9) | schedule-оптимум: γ* = 1/L, max drop = G²/(2L) |
  `nl_drop_optimal` (C606), через `hagi_master_v32` |
| (10) | иерархическое покрытие ЛЮБОГО n (peak ≤ m) |
  `hier_covers_any_n` (C611), через `hagi_master_v32` |
| (11) | reading floor: total = ⌈n/w⌉ = floor любого покрытия | `hier_optimal` (C618) |
-/

namespace Hagi.Theory.MasterTheoremV33

open scoped InnerProductSpace

open Hagi.Theory.AdapterGrowth Hagi.Theory.MiniHagiLoop
  Hagi.Theory.NegativeTransfer Hagi.Theory.CoverageReading
  Hagi.Theory.GrowSnap

/-- **(hagi_master_v33, C622 — консолидация certified-машины v3.3)**:
все 10 гарантий v3.2 (`hagi_master_v32`, C614) выполняются
одновременно, И к ним (11) reading-floor-клоз: при строчке `s = w`
(`hierStarts nB B w w`) и `w ∣ B` total окон равен
`(nB + w - 1) / w = ⌈nB/w⌉` — информационному минимуму — и НЕ
превышается никаким списком `L`, покрывающим `[0, nB)` окнами
длины `w` (`hier_optimal`, C618). Каждая конъюнкта — делегат БЕЗ
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
