# Phase analysis: C499–C500 — ЮБИЛЕЙНЫЙ рубеж C500 + виток C500 (rank-trunc escape) (2026-11-21)

Series HEAD b105f23d304239406d6332f10238d270e40354de (C500;
`git log` проверен: 35f2508 docs C499 → b105f23 C500 feat). Виток
C499–C500 закрил roadmap-пункты C497–C498 №1 (bench-включение
GPM-relaxed = mini-hagi3) и закрыл единственный пробел C498-теории
живым прогоном: gpm2-фаза, в которой full-GPM честно HOLD-ит (4
HOLD, 0 шагов, delta == 0 на сетке), ЭСКРАПИРОВАНА rank-trunc
relaxed-проекцией — 4 committed-шага с certified-забыванием ≤
‖delta‖² · sigmaTail² (bound asserts per-step). Это юбилейный
виток: конвейер перешагнул C500.

## Commit one-liners (C499–C500)

- C499 35f2508 `docs:` phase analysis c497-c498 — этот документ
  (анализ + index-regen, закоммиченный в C500-диффе).
- C500 b105f23 `feat:` mini hagi three rank trunc escape —
  `scripts/bench_bridge.py --mode mini-hagi3` (+669 строк):
  mini-HAGI3 = mini-hagi2 структура (2-block trunk, 3 задачи,
  holdout, канонический obj) с фазой E-gpm2relax: arm FULL (точная
  C494-реплика: 0 committed, first_delta_exactly_zero=true,
  телеметрия) против arm RANK-TRUNC (relaxed GPM: минимальный k с
  max sigmaTail² ≤ eps², eps = 1/10 PIN; 4 committed шага, k=1),
  каждый шаг assert-ом проверяет forgetting_bound
  (rank_trunc_forgetting_bound, C498) и certified-монотонность obj.
  Итог прогона (живой, этот виток): 15 certified шагов всего,
  задача 3 прогрессирует (mse-дроп > 0), gpm2 full 0 vs relaxed 4.

## (а) ЮБИЛЕЙ-ОБЗОР: эпохи C213 → C500 (кратко)

Инвентарь на C500 (theorem-index, реген в этом бите): **574
modules / 12731 theorems / 4704 defs / 493 Proven**; Freeze
verify **8574** declarations (PASS, см. (в)); streak посадок
**43**; всего 2102 коммита (362 feat / 144 docs).

| Эпоха | Коммиты (≈) | Ядро | Ключевая вершина |
|---|---|---|---|
| C213–C260 audit-эра (A15–A19) | ~240 audit-битов | source-first аудит, якоря,(statement audit) | A15–A19: fail-closed statement-аудиты, зависимостные графы |
| C260–C380 конвейер-эра | ~150 | certify-then-commit гейты, Freeze.py | Freeze-механизм, theorem-index реген, landing-дисциплина |
| C380–C450 реальные-данные эра | ~90 | unified_ledger, HAGI_v2 корпуса | certified-прогноз на измеренных holdout-метках |
| C450–C494 мини-HAGI эра | ~60 | mini-hagi1/2, sandwich-CE | sandwich-монотонность, C494 all-HOLD феномен |
| C494–C500 forecast+relaxed эра | ~12 | TrainerBenchmark, GPMRelaxed, mini-hagi3 | certified forecast 4/6, rank-trunc escape (C500) |

(Счётчики по subject-ключам `git log`; границы эпох — плавные,
таблица — юбилейная сводка, не точная периодизация.)

## (б) мини-HAGI3 итог: тупик C494 замкнут

- **Тупик замкнут**: gpm2-фаза, где full-GPM даёт delta == 0 на
  сетке 1/10000 (4 честных HOLD, 0 шагов — точная реплика C494),
  выходит через rank-trunc: k=1 (минимальный k с tail²-бюджетом
  ≤ eps²), 4 committed шага, задача 3 прогрессирует. Теория
  C498 (`gpm_tradeoff`, `gpm_hold_when_covered`) получила живое
  bench-свидетельство — единственный пробел прошлого витка закрыт.
- **15 certified шагов** в полном прогоне (A-trunk2 → C-gpm1 →
  E-gpm2relax → F-quant → G-stop); certified obj-цепь монотонна,
  каждый relaxed-шаг bound-asserted (forget ≤ ‖delta‖·sigmaTail).
- **ε-pin честен**: eps = 1/10 зафиксирован как PIN; eps = 1/100
  невозможен (tail²-бюджет не выполняется ни при каком k < rank —
  см. tail2max_by_k в телеметрии) — компромисс забывание/прогресс
  не «настроен», а измерен.

## (в) Метрики витка (замер C501, READ-ONLY)

- **Freeze verify (HEAD b105f23, C500-гейты)**: PASS,
  `TestFreeze.py` 22/22 OK, **8574** declarations, 0 aliased,
  ничего не потеряно/не изменено (C498: 8574; C500 — код-дифф
  только bench_bridge.py, Lean-поверхность не тронута).
- **Index**: регенерирован в C500 (закрыл дрейф C497–C498:
  572→574 modules, 12713→12731 theorems, 491→493 Proven). В этом
  бите C501 дрейфа нет (HEAD совпадает с закоммиченным индексом).
- **mini-hagi3 прогон** (живой, этот виток): 15 шагов, gpm2 full
  0 vs relaxed 4, k=1, eps=1/10, forgetting ≤ bound — все assert
  зелёные (exit 0).
- **Streak посадок**: 41 (C498) + C499 + C500 = **43**; freeze
  PASS на каждом; посадка C501 → 44 подряд.

## (г) Roadmap следующего витка (ранжировано к цели)

1. **Сужение sandwich-полос** — адаптивные n, m > 10,
   Bernoulli-монотонность по n, m: точность certified-прогноза
   4/6 → выше. Rank 1: прямое усиление полезности C497-прогноза;
   полосы — единственный узкий вход.
2. **Upstream Mathlib SVD-пакет + паломар-карточки** —
   continual-эру машину как Mathlib PR; карточки ключевых
   результатов (GPMRelaxed, sandwich, trainer-benchmark). Rank 2:
   внешний цикл, признание теории.
3. **Paper-черновик certify-then-commit HAGI** —
   docs/paper-draft.md: mini-HAGI + sandwich-CE +
   certified-prediction + trainer-benchmark + rank-trunc escape
   как связная история (C491–C500 — законченная дуга, материал
   созрел полностью). Rank 3: внешний артефакт.
4. **mini-hagi: grow через блоки trunk** — certifiedBlock-добавление
   C450 в bench: рост не только fiber-признаками, но и trunk
   (grow1/grow2 фазы mini-hagi3 уже дают каркас). Rank 4:
   масштабная ось машины.
5. **Imports-финал / КРЕДО-остатки** — bare imports и
   производные хвосты. Rank 5: гигиена, компаунд-ускорение.
6. **A-GEM bench-сравнение vs rank-trunc** —
   `agem_step_nonneg_interf` (C498) в прогоне против relaxed-GPM:
   количественное сравнение компромиссов. Rank 6: завершает
   теоретическую ветку C498.

Top-3 на следующий виток: (1) сужение sandwich-полос (точность
прогноза), (2) upstream Mathlib SVD + паломар-карточки,
(3) paper-черновик certify-then-commit.

## Honest limits

- mini-hagi3 — один живой прогон (единый корпус, fixed seed
  разбиение); переносимость на другие корпуса не сертифицирована.
- eps = 1/10 — PIN конкретного прогона, не универсальный
  параметр; при eps = 1/100 бюджет не выполняется (зафиксировано
  честно), оптимальный eps-выбор не формализован.
- rank-trunc «эскапирует» тупик на ЭТОЙ фазе; гарантия, что
  relaxed-GPM не упрётся в свой тупик при росте ранга прошлого,
  не формализована (открытый вопрос к следующей эпохе).
- Юбилейная таблица эпох (а) — сводка по subject-ключам git log,
  не формальная периодизация; Freeze 8574 — C500-гейты
  (Lean-поверхность HEAD, bench-дифф C500 её не менял).
