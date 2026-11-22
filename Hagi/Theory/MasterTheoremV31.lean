/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 authors
-/

import Hagi.Theory.MasterTheoremV3
import Hagi.Theory.GrowSnap
import Hagi.Theory.CoverageReading

/-!
# MasterTheoremV31 — консолидированная метатеорема машины v3.1 (C600)

Roadmap C599 top-3 (юбилейный C600): сборка certified-машины v3.1
в ОДНОМ statement — все 5 клозов v3 (C576) плюс три клоза
добора: snap-грид оптимальность (C593), coverage-чтение (C598),
smooth sufficient-transfer (C592; v3 содержит только квадратичный
iff C572 — smooth-уровень добавлен здесь). Прецедент и паттерн —
`master_theorem_v3` (C576): каждый клоз — делегат к уже доказанной
теореме, hypotheses дословно, БЕЗ ослабления; новых глубоких
фактов НЕТ — только конъюнкция (KISS).

## Карта клозов (все 8, делегаты rg-проверены)

| Клоз | Гарантия | Делегат |
|---|---|---|
| (1) | параметры ≤ 2·k·dd при любом n цикла | `master_theorem_v3.1` (C576/C555) |
| (2) | забывание = 0 (изоляция per-task адаптеров) | `master_theorem_v3.2` (C576/C544) |
| (3) | obj-цепь certified: телескоп ≤ o0 + Σ bounds | `master_theorem_v3.3` (C576/C555) |
| (4) | покрытие монотонно вдоль append-only цикла | `master_theorem_v3.4` (C576/C549) |
| (5) | перенос управляем iff-границей 2⟪θ,t⟫ vs ‖θ‖² | `master_theorem_v3.5` (C576/C572) |
| (6) | snap-грид k* минимален для ε-бюджета | `snap_k_eq_ceil` (C593) |
| (7) | вход прочитан побайтово (contiguous coverage) | `covStarts_covers` (C598) |
| (8) | smooth sufficient-граница переноса (равный бюджет) | `smooth_obj_transfer_bound` (C592) |

Клоз (5) + (8) = двухуровневый transfer-certified-контур:
квадратичный iff (точный) + smooth sufficient (консервативный).
-/

namespace Hagi.Theory.MasterTheoremV31

open scoped InnerProductSpace

open Hagi.Theory.AdapterGrowth Hagi.Theory.MiniHagiLoop
  Hagi.Theory.NegativeTransfer Hagi.Theory.GrowSnap
  Hagi.Theory.CoverageReading

/-- **(hagi_master_v31, C600 — консолидация certified-машины v3.1)**:
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
