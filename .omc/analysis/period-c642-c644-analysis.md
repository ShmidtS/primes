# Phase analysis: C642–C644 — эра «сертификация роста» (2026-11-24)

Series HEAD 8de578e3 (C644; `git log`: eb399530 C642 → ad36e5bb C643 →
8de578e3 C644; tree clean). Виток C645 — docs-виток анализа (прецедент
C641): READ-ONLY, один docs-commit. Серия закрывает roadmap C641 top-1
и top-2: разрыв C640 «после шага 0 Wo ≠ 0 функция не сертифицирована»
стал теоремой — условной; условие (h1) закрыто только с нашей стороны.

## Commit one-liners (C642–C644)

- C642 eb399530 `feat: post warmup growth certificate` — WarmUp в
  `Hagi/Theory/FunctionPreservingGrowth.lean` (+117): `warmup_telescope`,
  `warmup_safe`, `warmup_strict`, `post_warmup_growth_safe(_of_certified)`,
  негатив `uncertified_step_can_worsen`. Freeze 8869 → 8875 (+6 thm).
- C643 ad36e5bb `feat: armijo backtracking bridge from hagi v2 wave 254`
  — `RollbackGate.lean` (+58): `btScale`, `backtrackAccept`,
  `backtrack_accept_drop`, `backtrack_scale_halves`, `backtrack_trials_bounded`.
  Freeze 8875 → 8880 (+5: 2 def, 3 thm).
- C644 8de578e3 `feat: certified warmup composition and proposal` —
  `stepEps`, `CertifiedFiniteStep`, `warmup_h1_of_certified_steps`,
  `warmup_safe_of_certified_steps`, `post_warmup_growth_safe_of_certified_steps`,
  негативы `uncertified_step_not_certified`, `batch_drop_not_global`;
  `docs/PROPOSAL-certified-warmup.md` (+204). Freeze 8880 → 8887 (+7).

## (а) Рост ёмкости: цепочка сертификации

1. **Identity-старт (h0).** Wo = 0 ⇒ функция модели не меняется ⇒
   obj (θ 0) = fOld. Единственное звено, где код и теорема совпадают
   дословно (lm.py:589-601 @ca52eb4).
2. **Warm-up h1.** C642: h1 посылка; C644: контракт `CertifiedFiniteStep`
   (COMMIT drop > 1e-12 ∨ HOLD) ⇒ h1 ⇒ `warmup_safe`.
3. **Rollback-гейт.** При ЛЮБОМ вердикте holdout-гейта obj ≤ fOld
   (REJECT = точный `rollback_state_params`).
4. **Итог.** Цепочка identity → warm-up → гейт → obj ≤ fOld доказана
   для любого числа шагов. Сертифицируется train-objective, не функция.
5. **Единственный разрыв — реализационный.** Warm-up в коде
   (unified.py:423-433) — голый Adam, НЕ вызывает `_certified_finite_step`
   (lm.py:826); тот пишет в trunk, не в блок; сертифицирует batch-CE,
   а `batch_drop_not_global` фиксирует: batch-drop не телескопирует
   в global. Код траектории «по контракту на одном obj» не строит.

## (б) Метрики серии

| Метрика | C642 | C643 | C644 |
|---|---|---|---|
| Freeze | 8869 → **8875** | **8880** | **8887** |
| Δ freeze | +6 (6 thm) | +5 (2 def, 3 thm) | +7 (2 def, 5 thm) |
| Тип | feat (Lean) | feat (Lean) | feat (Lean + proposal) |
| Гейты | 17 PASS | 17 PASS | 17 PASS |

- Freeze 8887 = 8869 + 18 (4 def, 14 theorem); 0 lost/changed.
- Мосты кода: 5 (3 из C638–C640 + backtrack wave254 + контракт ↔ lm.py:826).
- Witness rc=0 (lean 4.36.0); аксиомы: propext, Classical.choice, Quot.sound.

## (в) Honest-разрывы

- **Warm-up ≠ certified (главный).** Код: Adam 2 эпохи; h1 условна;
  закрывается только предложением (user-push).
- **Adam EMA.** ⟨g, d⟩ ≤ 0 — не код-факт (EMA m̂/√v̂ по направлению
  MGDA); `adam_inner_nonneg` не доказана и не включена.
- **Range + JVP.** Сертификат — о logits-сдвиге (range(d)²/8), мост — о
  точном CE, код — о JVP-ширине r2 (fallback 1.0); вне окна занижен.
- **Backtrack — не Armijo (C643).** Предикат: worst ≤ порог регрессии
  ∧ wb − wa > total_bound; β = 1/2, 9 проб, σ·γ·⟪g,d⟫ нет; зовётся только
  из self-test (selfmodel.py:201-222).
- **MGDA-нормировка, FW-скорость (C639).** Код g/‖g‖, канон сырой; ε > 0
  ⇒ 2ε; FW не формализована.
- **Batch vs global.** Негатив формализован, положительного телескопа нет.
- **Holdout-гейт** — измеряется, не доказывается (train ≠ holdout).

## (г) HAGI_v2 recheck — волны 256+

HEAD ca52eb4 (wave 255, тот же, что в C641); волн 256+ нет. Дерево НЕ
чистое: ` M hagi/lm.py`, ` M hagi/unified.py`,
` M scripts/neuro_symbolic_cycle.py`, ` M tests/test_live_adapter.py`;
содержимое не читалось (READ-ONLY). Влияние на freeze 8887: none.
Риск: dirty-правка unified.py устарит строки 423-433 карточек C642/C644.

## (д) Roadmap ≥5

1. **`certified_step_block`** (Lean, high). Шаг по параметрам блока при
   замороженном trunk. Если range-лемма CE (`ce_direction_range`) не
   зависит от носителя параметров (только logits-сдвиг), сертификат
   переносится бесплатно; склеить с `warmup_h1_of_certified_steps`.
   Риск: нужны functional-логиты блока (JVP по блоку) — в коде их нет.
2. **Телескоп batch → global** (Lean, high). Honest: без вероятностной
   модели batch ≠ global. Кандидат — FixedBatch/CertifiedLoop statement,
   где batch фиксирован и objective один на всех шагах: применим
   `warmup_telescope`, obj честно названа fixed-batch CE.
3. **Adam EMA descent-лемма** (Lean, med). m̂/√v̂ сохраняет знак g только
   покомпонентно; для d = MGDA это не даёт ⟨g, d⟩ ≤ 0. Формализовать
   покомпонентный факт + негатив на скалярное произведение.
4. **Paper v0.9** (docs, med; external push user): 5 мостов кода,
   условный сертификат роста, proposal.
5. **External push PROPOSAL-certified-warmup** (user, high): без него
   h1 — условие, не код-факт.
6. **Recheck dirty-дерева HAGI_v2** после его коммита (docs, low).

Top-3: (1) `certified_step_block`; (2) телескоп через FixedBatch;
(3) Adam EMA-лемма.

## Honest limits (процедурные)

- READ-ONLY: lake не запускался; freeze 8887, 17 гейтов и witness — по
  `.tmp/C642–C644/receipt.md`, STATUS.md и коммитам. Код HAGI_v2 в этой
  сессии не перечитывался (dirty-дерево); строки — из карточек.
- `ce_direction_range` — по `rg` в нашем Lean; независимость от
  носителя параметров не проверялась.
