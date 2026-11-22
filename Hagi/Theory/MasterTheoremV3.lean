/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 authors
-/

import Mathlib.Tactic
import Hagi.Theory.AdapterGrowth
import Hagi.Theory.MiniHagiLoop
import Hagi.Theory.NegativeTransfer

/-!
# MasterTheoremV3 — метатеорема-спецификация машины v3 (C576)

Roadmap C575 top-2: композиция ВСЕХ характеристик certified-машины
mini-HAGI v3 (C547–C572) в ОДНОМ statement. Новых глубоких фактов
НЕТ — это референсная метатеорема-сборка уровнем выше
`v3_assembly_sound` (C558): каждый клоз — делегат к уже доказанной
теореме, конъюнкция берёт их hypotheses дословно (без ослабления).

## Карта клозов (все 5, делегаты rg-проверены)

| Клоз | Гарантия | Делегат |
|---|---|---|
| (1) | параметры ≤ 2·k·dd при любом n цикла | `self_compress_loop_sound` (C555) |
| (2) | забывание = 0 (изоляция per-task адаптеров) | `adapter_per_task_sound` (C544) |
| (3) | obj-цепь certified: телескоп ≤ o0 + Σ bounds | `self_compress_loop_sound` (C555) |
| (4) | покрытие монотонно вдоль append-only цикла | `iterative_loop_sound` (C549) |
| (5) | перенос управляем границей 2⟪θ,t⟫ vs ‖θ‖² | `neg_transfer_char` (C572) |

НЕ дублирует `MasterTheorem.lean` (C392, центральная теорема A17
audit'а: certified-or-refuse дихотомия reference-machine noisy-PL
траекторий) — здесь машина v3 bench-контура (distill + self-compress
+ adapter bank), полностью другой носитель и другие делегаты.
-/

namespace Hagi.Theory.MasterTheoremV3

open scoped InnerProductSpace

open Hagi.Theory.AdapterGrowth Hagi.Theory.MiniHagiLoop
  Hagi.Theory.NegativeTransfer

/-- **(master_theorem_v3, C576 — спецификация машины)**: для любого
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
