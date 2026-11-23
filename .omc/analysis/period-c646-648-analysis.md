# Phase analysis: C646–C648 — эра «рост + вероятность» (2026-11-24)

Series HEAD eaee5ea2 (C648; `git log`: e84eac25 C646 → 2a554dc7 C647 →
eaee5ea2 C648; tree clean). Виток C649 — docs-виток (прецедент C645):
READ-ONLY, один docs-commit. Серия закрывает roadmap C645 top-1
(`certified_step_block`) и top-2 (телескоп batch → global) — top-2 только
как УСЛОВНАЯ вероятность над моделью iid-батча.

## Commit one-liners (C646–C648)

- C646 e84eac25 `feat: certified step on block params via logit range
  lemma` — `Hagi/Theory/FunctionPreservingGrowth.lean` (+95):
  `certified_step_block_of_range`, `block_step_certified_of_range_bound`,
  `block_step_commit_of_range_bound`, негатив
  `block_range_bound_violated_not_certified`. Freeze 8887 → 8891 (+4 thm).
- C647 2a554dc7 `feat: batch to global drop telescoping` —
  `Hagi/Contracts/BatchGlobalTelescope.lean` (+225, новый модуль):
  `batch_telescope_fixed`, `fixedBatch_telescope`, `batch_drop_generalizes`,
  `certified_batch_drop_global`. Freeze 8891 → 8899 (+6 thm, +2 def).
- C648 eaee5ea2 `feat: certified rounds union bound` — там же (+186,
  уровень (C)): `rounds_union`, `rounds_telescope`, `roundGood`,
  `certified_rounds_union`. Freeze 8899 → 8907 (+5 thm, +3 def).

## (а) Рост + вероятность: certified-цепочка до global-obj

1. **Identity-старт (h0).** Wo = 0 ⇒ obj (θ 0) = fOld (код дословно).
2. **Certified-шаг на блоке (C646).** Range-лемма CE — на логитах
   (`lse_shift_upper`), носитель параметров не важен ⇒
   `certified_step_block_of_range` переносит сертификат с trunk на блок.
3. **Warm-up h1.** `block_step_commit_of_range_bound` ⇒
   `CertifiedFiniteStep` ⇒ `warmup_h1_of_certified_steps` ⇒ obj ≤ fOld.
4. **Batch → global (C647).** (A) batch = датасет — certified; (B)
   фиксированный batch телескопирует в batch-objective
   (`batch_telescope_fixed`), global — через
   `empirical_bernstein_mean_bound` (`batch_drop_generalizes`).
5. **Union bound (C648).** `rounds_union` + `rounds_telescope` ⇒
   `certified_rounds_union`: P ≥ 1−α все раунды хорошие ⇒
   obj k ≤ obj 0 − Σ dropB + k·ebGap(α/k).
6. **Итог.** Слабое место сдвинулось с «шаг не сертифицирован» на
   «модель батча/раунда — гипотеза».

Модели-гипотезы, которые код должен подтвердить (не код-факты):
- **iid из q.** Код: `rng.choice(replace=False)` — WOR, не iid.
- **Независимость раундов.** Код: θ меняется между раундами ⇒ зависимы;
  bound верен лишь внутри модели `roundP`.
- **b/sig для EB.** Код не считает диапазон/дисперсию per-sample
  приращений loss; `ebGap` не вычисляется.
- **Block-only JVP.** range(Δz) по блоку при замороженном trunk —
  реализация кода, не теорема.
- **k и α/k.** Код: 8 раундов, α не делит.

## (б) Метрики серии

| Метрика | C646 | C647 | C648 |
|---|---|---|---|
| Freeze | 8887 → **8891** | **8899** | **8907** |
| Δ freeze | +4 (4 thm) | +8 (6 thm, 2 def) | +8 (5 thm, 3 def) |
| Тип | feat (Lean) | feat (Lean, модуль) | feat (Lean) |

- Freeze 8907 = 8887 + 20 (5 def, 15 thm) за 3 бита; 0 lost/changed.
- Мосты кода: 8 = 5 (C638–C644) + шаг на блоке + batch → global +
  union bound ↔ lm.py:978-1008 @ca52eb4.

## (в) Honest-открытые пункты (цена формализации)

- **Независимость раундов** (высокая): martingale/Azuma-чтение
  условное по θ либо contract-level gate.
- **WOR-консервативность** (высокая): FCP (N−n)/(N−1) ≤ 1 — интуиция,
  Mathlib-леммы нет; цена — order-statistics/FCP-лемма.
- **b/sig в коде** (средняя): instrumentation + тест; иначе slack
  k·ebGap неизвестен.
- **Warm-up ≠ certified** (средняя): код — голый Adam
  (unified.py:423-433), h1 условна; закрывается external push.
- **Adam EMA:** ⟨g, m̂/√v̂⟩ ≥ 0 покомпонентно лишь при знаке m̂ = знаку g;
  для EMA не факт. `adam_inner_nonneg` не доказана (STATUS.md:2357).
- **Block-only JVP** — реализация; **holdout-гейт** — измеряется.

## (г) HAGI_v2 recheck — без чтения dirty-дерева

HEAD ca52eb4 (wave 255, тот же); дерево НЕ чистое: ` M hagi/lm.py`,
` M hagi/unified.py`, ` M scripts/neuro_symbolic_cycle.py`,
` M tests/test_live_adapter.py`. Содержимое не читалось. Влияние на
freeze 8907: none. Риск: правка lm.py/unified.py устарит строки 978-1008
карточек C647/C648 и warm-up-строки C642/C644.

## (д) Roadmap ≥5

1. **Paper v0.9** (docs, med): code-bridge era — 8 мостов C638–C648,
   proposition-предложения; цепочка identity → block → batch → global
   (вероятностно) одним разделом.
2. **Adam EMA-лемма покомпонентно** (Lean, med): honest-проверка на
   снапшоте (доля знакосогласия m̂ и g); при < 100% — негатив в Lean.
3. **Bench certified-warmup-sim** (code, med-high): режим симуляции
   C642–C648 с certified-шагом; показать obj ≤ fOld на снапшоте.
4. **WOR-консервативность** (high): гипергоеметрия (цена высокая) или
   обход — stratified/fixed batch в коде (уровень (B), Proposal).
5. **External push user** (high): `PROPOSAL-certified-warmup.md` +
   paper v0.9; без него h1 — условие, не код-факт.
6. **Recheck dirty-дерева HAGI_v2** после коммита (docs, low).

Top-3: (1) paper v0.9; (2) Adam EMA honest-проверка; (3)
certified-warmup-sim.

## Honest limits (процедурные)

- READ-ONLY: lake build не запускался; freeze и гейты — по
  `.tmp/C646–C648/receipt.md`, STATUS.md и коммитам. Код HAGI_v2 не
  перечитывался (dirty-дерево); строки — из карточек.
- «8 мостов» — сумма по карточкам C638–C648, не machine-checked.
- Имена сверены `rg` по текущему дереву Lean.
