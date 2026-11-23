# Phase analysis: C638–C640 — эра «код HAGI_v2 → Lean-мосты» (2026-11-23)

Series HEAD 38e0892b7525204335c44aca171723f824ec6fa6 (C640; `git log`
проверен: 8999bdc8 C638 → 9fbca579 C639 → 38e0892b C640; tree clean).
Виток C641 — docs-виток фазового анализа (прецедент C631/C634/C637):
READ-ONLY, один docs-commit. Серия C638–C640 = смена направления
потока: до неё primes поставлял теорию, HAGI_v2 её читал; теперь
код HAGI_v2 сверяется с Lean-каноном и primes отвечает Lean-мостами
на конкретные строки кода. Все три витка — посадки, freeze
8849 → 8869.

## Commit one-liners (C638–C640)

- C638 8999bdc8 `feat: adaptive step certificate bridge from hagi v2
  waves 252-254` — `AdaptiveMajorizer.lean` (+352): канон на точном
  диапазоне (`ceDispRange`, `ce_direction_range`), `kappaClamp`
  (окно (1e-5, 50]), `ce_adaptive_code_drop`, `ce_range_code_drop`,
  `adaptive_claim_scaled(_bounds)` (defect 2: 39/400 ≈ 400/39 раз).
  Freeze 8849 → 8861 (+12: 4 def, 8 theorem).
- C639 9fbca579 `feat: mgda code correspondence bridge from hagi v2`
  — `Hagi/Model/BatchCEDescentMgdaCode.lean` (+157):
  `mgdaCodeDirection`, `MgdaStationary`,
  `mgda_norm_sq_le_of_stationary` (2ε, Young), `mgda_eq_of_stationary`
  (ε = 0 точен), `batchGradientMinimizer_eq_mgdaCodeDirection_of_stationary`.
  Freeze 8861 → 8869 (+8: 3 def, 5 theorem).
- C640 38e0892b `docs: function preserving growth bridge card from hagi
  v2 wave 255` — только STATUS.md (+72), класс (a): statement кода ⊂
  канон. Freeze 8869 identity. Witness rc=0 (4 позитива, 1 негатив).

## (а) Эра: цикл «теория → код» замкнулся двунаправленно

1. **HAGI_v2 сам сверяется с Lean.** Коммит 4c70f7a (wave 252) в C:/HAGI_v2
   озаглавлен «three certificate defects, found by checking it against Lean»;
   волна 254 (1ae924e) переносит MGDA на нормированные градиенты, волна 255
   (ca52eb4) гейтит рост по сигналу GrowthGate `128·‖G‖²/(2L)` против c_add. В
   repo HAGI_v2 0 `.lean`-файлов: сверка идёт по канону primes, файлы живут только
   здесь.
2. **Происхождение Lean-файлов роста.** Оба файла — исконные для primes, из эры
   merge-islands (bench `--mode grow`), а не перенос из HAGI_v2:
   `Hagi/Theory/FunctionPreservingGrowth.lean` добавлен 2f21bf7a (2026-11-19,
   `feat: function preserving growth bridge from merge islands`),
   `Hagi/Theory/GrowTrunkBlock.lean` — db9c9f63 (2026-11-21, `feat: grow trunk
   block identity bench`); повторное касание 48070b1b (2026-11-21) и
   docstring-правка 0f2798cc (2026-11-23). В HAGI_v2 имя
   `FunctionPreservingGrowth.lean` — только в заголовке коммита и комментариях
   (lm.py:565, :583) как ссылка на bench-прецедент. Хронология: Lean 19.11 → код
   23.11.
3. **Итог эры.** Поток стал двусторонним: primes → теория → HAGI_v2 (код, дефекты,
   коммит-сообщения ссылаются на Lean) → primes (Lean-мосты на конкретные строки
   кода). Класс вердиктов (a) «statement кода ⊂ канон» — новый тип посадки: 0
   новых теорем, единица — карточка соответствия с честными границами.

## (б) Метрики серии

| Метрика | C638 | C639 | C640 |
|---|---|---|---|
| Freeze | 8849 → **8861** | **8869** | 8869 (identity) |
| Δ freeze | +12 | +8 | 0 |
| Тип | feat (Lean) | feat (Lean) | docs (card) |
| Гейты | 17 PASS | 17 PASS | 17 PASS |

- Freeze 8869 = 8849 + 20 (7 def, 13 theorem); 0 lost/changed.
- Мосты кода: 3 (шаг adaptive/range, MGDA, рост) на 3 волны
  HAGI_v2 (252/254, 254, 255). Аксиомы новых теорем: propext,
  Classical.choice, Quot.sound.

## (в) Honest-разрывы

- **Post-warm-up (C640, главный).** После шага 0 Wo ≠ 0: keep-iff
  holdout CE + rollback — эмпирика; клоз zero-forgetting
  `master_theorem_v3` требует замороженной per-task ветви, рост trunk
  под него не подпадает. «Forgetting 4x lower» — A/B на 6 чанках.
- **Range + JVP (C638).** Реальный сертификат — `ce_range_code_drop`;
  мост о точном CE, код — о JVP (rollback 2/5 в нелинейной LM); вне
  окна C кода занижен, claim не сертифицирован.
- **FW-скорость (C639).** Не формализована; в 6 кейсах FW стоп на
  итерации 0 — нетривиальная траектория не наблюдалась.
- **Нормировка MGDA (C639).** Код: g/‖g‖, канон: сырые градиенты;
  дословный мост только при равных нормах; ε > 0 ⇒ 2ε.

## (г) HAGI_v2 recheck — волны 255+

Прямой аудит C:/HAGI_v2 на момент C641: HEAD ca52eb4 (wave 255, тот
же, что в C640), волн 256+ нет. Дерево НЕ чистое: ` M hagi/unified.py`
— незакоммиченная правка в файле с `_maybe_grow` (содержимое не
читалось, READ-ONLY). Влияние на freeze 8869: none. Кандидат на
следующий виток: diff этой правки после коммита в HAGI_v2.

## (д) Roadmap ≥5 к цели «max качество, min объём, min вычисления»

1. **Post-warm-up сертификат роста** (Lean, high; выгода: закрывает
   главный разрыв C640; риск: теоремы нет без гипотез о L и шаге).
   Warm-up с замороженным trunk: obj(новая) ≤ obj(старая) − certified
   drop (через `nl_drop_optimal`) + keep-iff holdout ⇒ «рост безопасен
   после warm-up». Кандидат-теорема, не обещание.
2. **Adam backtracking → Armijo-мост** (Lean, high; риск: в коде нет L
   и Armijo-условия — гейт validation loss; нужен мост «validation ⇒
   Armijo»).
3. **Range-ветка с нелинейной моделью** (Lean+bench, med; выгода:
   2/5 rollback-отказов; риск: оценка остатка JVP может быть vacuous).
4. **Per-task gate wave254 ↔ transfer-гейт C601** (docs, med; дёшево).
5. **External push (user): paper v0.9** с тремя мостами (hold; без
   п.1 остаётся «рост не сертифицирован»).

Top-3: (1) post-warm-up сертификат; (2) Armijo-мост; (3) карточка
per-task gate ↔ C601.

## Honest limits (процедурные)

- READ-ONLY виток: lake не запускался; freeze 8869, 17 гейтов и
  witness-прогоны C638–C640 — по receipt'ам `.tmp/C638–C640`,
  коммит-сообщениям и STATUS.md.
- HAGI_v2 аудит (§а, §г) — по `git log`/`git status`/`fd`;
  код lm.py/unified.py/selfmodel.py в этой сессии не перечитывался,
  цитаты строк — из карточек C638–C640.
- Era-индекс до C641 заканчивался на C633 (секции C634–C637 нет;
  разборы — `git show b3e7c6ab^:.omc/analysis/`).
