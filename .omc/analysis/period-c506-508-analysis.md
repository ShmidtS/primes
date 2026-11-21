# Phase analysis: C506–C508 — repeated grow, upstream SVD, A-GEM vs rank-trunc (2026-11-21)

Series HEAD 9ae7a3d8e89b899d11e34408c59951e64f9a6076 (C508;
`git log` проверен: 48070b1 C506 feat → 09a76c0 C507 feat →
9ae7a3d C508 feat). Виток закрыл roadmap C505 №1 (повторяемый
grow-цикл), №5 (A-GEM vs rank-trunc bench) и подготовил №3
(upstream-SVD standalone-патч, PR-ready). Главный сдвиг: grow-эра
завершена — машина роста повторяема вглубь (2→5) с измеренным
пределом бюджета, continual-инструментарий стал ПОЛНЫМ
(zero/full/rank-trunc/A-GEM — все с теоремами и bench), внешний
контур (upstream-патч) готов к отправке.

## Commit one-liners (C506–C508)

- C506 48070b1 `feat:` repeated grow cycle depth budget —
  `--mode mini-hagi5`: 3 identity-grow события в ОДНОМ прогоне,
  trunk глубина 2→5, 16 certified шагов, exact obj-инвариант на
  каждом grow; знаменатели признаков ×~3.2/grow (280→840→2520
  цифр, измерено ×3), предел бюджета спроецирован (~8000 цифр
  /~150 s на глубину 6) — honest limit в телеметрии. Lean
  GrowTrunkBlock +2: `grow_blocks_repeat_sound`,
  `grow_blocks_obj_invariant_repeat`.
- C507 09a76c0 `feat:` svd upstream standalone patch —
  `upstream/svd/SVDDecomposition.lean` (607 строк, 42 decls,
  27 theorems) + README с PR-чек-листом. Байт-в-байт от
  `Hagi/External/Flywheel/SVDCore.lean` кроме header/namespace
  (minimal diff, защита от statement drift); exit 0 против
  Mathlib fc4f59e; вне lake-таргетов.
- C508 9ae7a3d `feat:` agem vs rank trunc continual comparison —
  `--mode agem-vs-ranktrunc`: оба механизма C498 на ОДНОМ
  сценарии C485 (общие данные/бюджет/eta/сетка). A-GEM:
  B-прогресс 0.2667, forgetA −0.140, 18 конфликтов/24, все с
  interference РОВНО 0; rank-trunc: B-прогресс 0.0499, forgetA
  −0.0013, 24 проекций/24, per-point bound (delta·x)² ≤
  ‖delta‖²·sigmaTail². Witness живой: `agem_step_nonneg_interf`
  + `rank_trunc_forgetting_bound`.

## (а) Grow-эра: итог

- **Рост повторяем по двум осям.** Fiber-ширина (C494) и
  block-глубина (C504) объединены в repeat-машину: C506 —
  3 grow-события подряд в одном прогоне, exact-инвариант на
  каждом, certified-обучение нового блока после каждого.
  Паттерн «нейтральная вставка → certified-обучение» — уже
  не событие, а цикл.
- **Предел ИЗМЕРЕН, не постулирован.** ×3.2/grow на знаменатели
  — экспонента бюджета; глубина 6 ~8000 цифр/~150 s за
  фиксированной границей. Дальнейший рост глубины на exact
  Fractions бесперспективен (Sunk-Cost сигнал) — нужна либо
  аппроксимация, либо рост в ширину.
- **Continual-инструментарий полный.** zero-GPM, full-GPM
  (C494-тупик при исчерпании span), rank-trunc (per-point
  bound), A-GEM (дешёвые свободные шаги) — все четыре имеют
  теоремы + живые bench-инстансы. Матрица выбора закрыта
  эмпирически (см. decision-таблицу б).
- **Внешний вклад готов.** upstream/svd — standalone,
  компилируется против Mathlib, PR-чек-лист в README;
  отправка — внешний шаг user.

## (б) Decision-таблица: выбор continual-механизма per-step

Измеренное состояние → механизм (эмпирическая база C485/C494/C508):

| Измеренное состояние | Механизм | Почему | Число |
|---|---|---|---|
| ⟨g, g_old⟩ ≥ 0 (нет конфликта) | A-GEM free step | полный градиент, нулевая цена | free шаги в C508 |
| Конфликт РЕДКИЙ у старта задачи | A-GEM | одна GS-итерация дешевле постоянной проекции | B-прогресс 0.267 vs 0.050 |
| Конфликт — норма (18/24), но g⊥-проекция сохраняет прогресс | A-GEM | interference ровно 0, прогресс удержан | 18/18 interference = 0 |
| Требуется per-point bound забывания | rank-trunc | (delta·x)² ≤ ‖delta‖²·sigmaTail² | forgetA −0.0013 vs −0.140 |
| Span(A) исчерпан (тупик full-GPM, C494) | rank-trunc | единственный выход из тупика | C494→C500-механика |
| Строгий ноль влияния на СТАРУЮ задачу | full-GPM | точная проекция, дорогая | C494/C498 |
| Нулевой шаг допустим (задача не конфликтует) | zero-GPM | дёшево, без гарантий прогресса | C498 |

Правило: conflict-rate и span-полнота — ИЗМЕРЯЕМЫЕ per-step
сигналы; выбор механизма по таблице автоматизируем (см.
roadmap №1 hybrid).

## (в) Метрики витка (замер C509, READ-ONLY)

- **Freeze verify (HEAD 9ae7a3d, C508-гейты)**: PASS,
  `TestFreeze.py` 22/22 OK, **8591** declarations, 0 aliased,
  ничего не потеряно/не изменено (C504: 8589; +2 — C506
  GrowTrunkBlock, certify-then-commit).
- **Index regen**: дрейф C506 обнаружен и закрыт в этом бите:
  theorems 12765→**12767** (GrowTrunkBlock 7→9 decls), modules
  576, Proven 495 — без изменений. C507/C508 новых Hagi.*
  деклараций не дали (upstream вне lake; A-GEM — bench).
- **Streak посадок**: 47 (C504) + C505–C508 = **51**; freeze
  PASS на каждом; посадка C509 → 52 подряд.

## (г) Roadmap следующего витка (ранжировано к цели)

1. **Hybrid-mechanism bench** — авто-выбор continual-механизма
   per-step по измеренному состоянию (conflict-rate,
   span-полнота) внутри одного прогона, по decision-таблице
   (б). Rank 1: превращает таблицу из анализа в самонастройку;
   все четыре механизма уже в bench_bridge.
2. **Selfloop recheck** (внешний) — сверка логов selfloop-обучения
   с certified-предсказаниями. Rank 2: внешний цикл валидации.
3. **Paper-обновление + upstream-отправка SVD** (внешний шаг
   user) — вставить числа C506–C508 (grow-кривая, ×3.2/grow,
   A-GEM ×5.3 прогресс) в docs/paper-draft.md; upstream/svd
   PR-ready, отправка по чек-листу README. Rank 3.
4. **Imports-финал** — deriv-safe механикой до нуля. Rank 4:
   гигиена, компаунд-ускорение.
5. **Мини-HAGI как LIBRARY** — выделить bench-конвейер
   (grow + continual-механизмы + admission/rollback) в
   переиспользуемый python-модуль `hagi_bench.py` для
   HAGI_v2-агента. Rank 5: превращает витки C485–C508 в
   библиотеку.
6. **Паломар-карточки** — зафиксировать «известное unknown»
   (regime-переходы, saturation-глубина) карточками. Rank 6.

Top-3 на следующий виток: (1) hybrid-mechanism bench (авто-выбор
по таблице б), (2) selfloop recheck (внешний), (3) paper-числа
C506–C508 + SVD-отправка (внешний шаг user).

## Honest limits (процедурные)

- A-GEM ×5.3 прогресс — один сценарий C485 (fixed seed, ранг
  span 2 из dim 4); переносимость не сертифицирована.
  A-GEM даёт только first-order 0 interference, не per-point
  bound — сравнение механизмов НЕ иерархично, они ортогональны
  по гарантиям.
- Предел глубины 5 — предел exact-Fraction конвейера, не
  архитектуры; аппроксимационный путь не начинался.
- Префикс-шапка witness C506 (3 шага вместо полного) — полные
  дроби depth-5 ~10^5 знаков непереносимы в Lean; честно
  задокументировано в STATUS.
- Прее-существующее: `--mode continual` падает на живом корпусе
  (нет smoke_gpu.bin в rd_load_dataset; воспроизведено на HEAD
  C507 до коммита) — вне скоупа витка.
- Streak-счёт вручную по посадкам; receipts до C483
  фрагментарны (после C499 фиксируются анализами).
