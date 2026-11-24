# Phase analysis: C662–C664 — эра «v3.4 + wave258b» (2026-11-24)

Series HEAD 0ce30c0d → C664 (C663 0ce30c0d ← C662 4fd95e00 ← C661
6f9837d3 docs). Закрыты roadmap C661 top-1 (v3.4), top-2
(PROPOSAL-holdout-size), top-3 (chain rule, линейный носитель).

## (а) Эра: консолидация 14 клозов и порядок окон

1. **C662 `hagi_master_v34` (+1 theorem).** v3.4 = v3.3 + (12) strict
   first growth step (`first_step_strict_improves`, +1 theorem в
   FunctionPreservingGrowth.lean), (13) Adam-first descent
   (`adam_first_step_dot_pos`, C655), (14) holdout two-way
   (`holdout_gate_two_way_delta`, C660); клозы (1)–(11) одним делегатом
   `hagi_master_v33`. PROPOSAL-holdout-size: k ≥ log(2N/δ)/(2(ε/B)²).
2. **C663 chain rule (+1 def, +2 theorem).** `chainGrad J p y i =
   Σ_v J v i·(y v − p v)`; `chain_linear` (чистая алгебра),
   `useful_of_adam_first` — a = −⟪g, d⟫ < 0 из Adam-first ⇒
   `first_step_useful_certified`. Pin C657 (1) закрыт для ЛИНЕЙНОГО
   носителя (Wo-блок при фиксированных h).
3. **C664 wave258b-мост (+1 def, +3 theorem).** bab8aff чинил три
   потребителя oldest-first trunk: `_read_all_windows` (ctx[j:i][::-1] →
   левый паддинг), holdout train_guarded (idx[p+k−1..p] → idx[p..p+k−1]),
   `generate` (WAVE 258c). Мост: holdout = `slot`/`slot_last` (существующие),
   generation = `padSlot` + `padSlot_tail/_last/_full` (новая конструкция).
4. **Паспорт чтения:** порядок слотов внутри окна — EXACT (C651 для
   `_windows`, C664 для generation/holdout); решётка начал окон —
   `covStarts_covers` / hier (bench-twin). Инварианты разные, оба держатся.

## (б) Метрики: freeze 8959 → 8967 (+8, 0 lost/changed)

- 8959 → 8960 (C662: +1 theorem); 8960 → 8963 (C663: +1 def, +2 theorem);
  identity (C661: docs); 8963 → 8967 (C664: +1 def, +3 theorem).
  AllAxioms PASS (C663, C664), CI PASS (C664, .tmp/C664/gates.log).
- Paper v1.0 → v1.1: 74 якоря перепинены (54 repin.py + 20 repin2.py),
  сдвиг +11 / +11 строк (C663 FPG / C662 MasterTheoremV3), не +17.

## (в) Honest-открытые

- **U2** (высокая): reachable drop ≥ δ на non-convex ландшафте — открыто.
- **Нелинейный chain rule** (высокая): b1/W1 через relu — нужен
  HasFDerivAt; C663 закрыл только линейный носитель.
- **unified.py:1010** (средняя): neural-фолбэк ещё читает `[::-1]` с
  `logits(x)[0]` — тот же класс бага, что wave258b; прогоном не проверял.
- **Holdout** (высокая): iid — модель; k = 512 вакуумно (ε ≈ 0.065B);
  PROPOSAL-holdout-size ждёт решения owner кода.
- **Range-coder round-trip** (средняя): только карточка и тесты.

## (г) HAGI_v2 recheck — HEAD 134f81b (wave 259), worktree dirty

`git log bab8aff..HEAD` = 134f81b (wave 259): тесты перезаписали
production-чекпоинт (770 доменов) — пути следуют CKPT_DIR, save()
под guard, sandbox-тест. Worktree dirty (archiver.py, trunk_ops.py,
unified.py, +92/−22) — чтение только через git show. wave258b
(bab8aff) и residual `[::-1]` в unified.py:1010 — см. (в). Freeze 8967
не затронут.

## (д) Roadmap

1. **unified.py:1010 → push** (docs → user-push, high): окно neural-фолбэка
   развёрнуто относительно trained trunk (`[::-1]` + `logits(x)[0]`);
   замер CE до/после — owner кода HAGI_v2.
2. **Нелинейный chain rule** (Lean, high): HasFDerivAt-вариант
   `chain_linear` на relu-блоке (b1/W1); закрывает honest C663.
3. **U2** (statement-кандидат, med-high): finite-grid UAT — «для любой
   функции на конечном множестве ∃ блок класса F с CE < ε».
4. **Holdout size** (код, med-high): решение по k ≥ 1199 (ε = 0.05B,
   δ = 0.05, N = 10) — PROPOSAL-holdout-size ждёт owner.
5. **Paper v1.2** (docs, med): аудит shorthand-якорей §3.9–§3.18 после
   C664-перепина; `iterStep`/`hier_*` таблицы — сверить с HEAD.
6. **Wave 259 follow-up** (код, med): восстановление production-чекпоинта
   после инцидента тестов (770 доменов, 283 адаптера) — owner HAGI_v2.

Top-3: (1) unified.py:1010 push; (2) нелинейный chain rule; (3) U2.

Honest limits: READ-ONLY — числа wave258b из commit msg (не перемеряно);
HAGI_v2 — только git show; freeze/gates — по .tmp/C664/gates.log.
