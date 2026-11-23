# Phase analysis: C650–C651 — эра «repair + archiver» (2026-11-24)

Series HEAD b32a9003 (C651 ← 8fb0f1fa C650; tree clean). Виток C652 —
docs-виток (прецедент C649): READ-ONLY, один docs-commit. Закрыт roadmap
C649 top-1 (paper v0.9); top-2 (Adam EMA) и top-3 (warmup-sim) не начаты.

## (а) Эра: что закрыто, что остаётся claim'ом кода

1. **Code-bridge эра задокументирована** (paper v0.9 §3.20/§4.8): 8
   мостов C638–C648 (сумма по карточкам, не machine-checked). Дрейф
   якорей зафиксирован (paper-draft.md:1485): lm.py:826 → :831 и др.
2. **Repair-forgetting — мост потока управления, EXACT.** Код
   (unified.py:408-455 @e9a96fc): пока gate post > pre — snapshot →
   шаг на старых байтах → нет улучшения ⇒ точный rollback, СТОП.
   Lean: `RepairRun` (done/retrain/rollback) ⇒ `repair_sound`:
   z ≤ v − tol·a ∧ z ≤ v ∧ a ≤ r. Граница ЛИНЕЙНАЯ: код принимает
   любое улучшение > 1e-4, ρ не фиксирован ⇒ (1 − ρ)^k не следует;
   верхней границы забывания нет. Клоз (2) `master_theorem_v3` кодом
   не инстанцируется: repair пишет в общий trunk.
3. **Archiver — claim кода без формализации.** `hagi/archiver.py
   @b3740e0`: 32-бит range coder, 16-бит CDF (`probs_to_cdf` :33-39:
   freq ≥ 1, остаток 65536 в argmax), stored-fallback (:188).
   Docstring :2-3: «size within o(1) of −log₂ P(data), ratio IS the
   model's CE» — в primes не доказано. `trit_roundtrip` — позиционная упаковка,
   не интервальный кодер.
4. **WindowOrder — инвариант порядка, не цели**: `slot`/`slotRev`,
   `slot_mono`, `slot_last`, `slotRev_first`; смежность цели (target =
   idx[p]) Lean-утверждением не является.

**Archiver-вердикт: entropy-модуля в Mathlib НЕТ.** `rg -l -i
"ArithmeticCoding|RangeCoder|entropy|Huffman|Kraft"` по
`C:/Users/shmid/mathlib4/Mathlib` (dir из lake-manifest, HEAD fc4f59e5):

- Есть: `InformationTheory/` = Hamming, Coding/{Kraft, KraftMcMillan, PrefixFree,
  UniquelyDecodable}, KullbackLeibler/{Basic, ChainRule, DataProcessing, KLFun};
  отдельно `Analysis/SpecialFunctions/BinaryEntropy`.
- Нет: arithmetic/range/Huffman-кодера, Shannon source-coding theorem,
  связи «энтропия = длина кода».
- У primes есть: CE − H = KL (`klDef_eq_ceDef_sub_of_support`,
  `Hagi/Probability/FiniteLogScore.lean:97`), `ceDef q q = entDef q` (Prelude,
  STATUS.md:451). Связи CE с ДЛИНОЙ КОДА нет нигде.
- Цена моста: (i) модель интервального кодера + инвариант непустого
  интервала; (ii) round-trip encoder/decoder; (iii) codelength ≈
  −Σ log₂ p (Kraft — о prefix-free, range coder не покрывает).
  Три куска, ≥ 3 циклов; начинать с (iii) как statement-кандидата.

## (б) Метрики: freeze 8907 (C650 docs identity) → 8921 (C651 Lean, +14)

- C650 8fb0f1fa: только `docs/paper-draft.md` (+356/−9). C651 b32a9003:
  `RepairForgetting.lean` (новый), WindowOrder в `CoverageReading.lean`.
- Δ состава: +9 thm, +4 def, +1 inductive; 0 lost/changed (receipt
  C651, `.tmp/C651/logs/ci.log:30`).
- Мосты кода: 8 (C638–C648) + repair + WindowOrder = 10; archiver — 0
  (сумма по карточкам, не machine-checked).

## (в) Honest-пункты (цена формализации)

- **Archiver lossless = тесты** (высокая): 6 тестов @b3740e0 (round-trip,
  stored-fallback, привязка к модели, порча отвергается). Хеша
  чекпоинта в контейнере нет: «only the SAME model decodes» — docstring.
- **(1 − ρ)^k не существует** (средняя): нужна ρ-пороговая политика приёма
  в коде; сейчас честна только линейная граница. **Gate ≠ забывание**
  (средняя): gate = CE на ≤ 8 доменах × 256 позиций; +0.553 → +0.036 —
  из commit msg, не перемеряны.
- **Target-смежность `_windows`** (высокая, находка C651): контекст idx[p−n..p),
  цель idx[pos+k] ⇒ gate CE 0.181 → 7.307 на probe (`.tmp/C651/logs/`
  windows_probe.log). HAGI_v2 read-only — не чинилось.
- **Adam EMA** (средняя): `adam_inner_nonneg` не доказана; warm-up —
  голый Adam ⇒ h1 условна. **WOR / b/sig / α/k** — код не считает, (C).

## (г) HAGI_v2 recheck — HEAD b3740e0 (wave 258) = карточечный, tree clean

Волн 259+ нет (`git log b3740e0..HEAD` пуст); freeze 8921 не затронут;

## (д) Roadmap

1. **Archiver, шаг 1 — statement-кандидат** (Lean, high): «на конечном
   блоке codelength ≈ −Σ log₂ p; при p = q (CE = H) — H». Опора:
   `klDef_eq_ceDef_sub_of_support`, `ceDef_self = entDef`. Затем (ii)
   round-trip лемма, затем (i) кодер.
2. **Adam EMA honest-проверка** (Lean+code, med): доля знакосогласия
   m̂ и g на снапшоте; 100% ⇒ лемма, иначе негатив в Lean.
3. **Bench certified-warmup-sim** (code, med-high; C649 top-3): режим
   симуляции C642–C648 с certified-шагом; показать obj ≤ fOld.
4. **Era-index C634–C637** (docs, low): секции refactor-эры
   отсутствуют. Решение: одна строка-ссылка на `refactor-master-plan-v7.md`
   (Chesterton: пропуск в индексе, не правило). В C652 не добавлена.
5. **Target-смежность `_windows` в Lean** (Lean, med): негатив «порядок
   есть, цель не та» + инвариант `target = idx[p]`; баг — owner HAGI_v2.
6. **External push user** (high): paper v0.9 + `PROPOSAL-certified-warmup.md`
   + 14 cards; h1 — условие, не код-факт.

Top-3: (1) archiver statement-кандидат; (2) Adam EMA honest-проверка;
(3) certified-warmup-sim.

## Honest limits (процедурные)

- READ-ONLY: lake build не запускался; freeze/гейты C651 — по receipt и
  ci.log; HAGI_v2 — только `git show b3740e0:<path>`. Mathlib-вердикт —
  `rg` по clone @fc4f59e5 (path из lake-manifest, без pinned rev).
