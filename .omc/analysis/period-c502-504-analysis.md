# Phase analysis: C502–C504 — Bernoulli+band tightening, paper/upstream, grow-in-depth (2026-11-21)

Series HEAD db9c9f6369e686811ad29dd8026035ddb05b048f (C504;
`git log` проверен: 8640fb5 C502 feat → 8f57839 C503 docs →
db9c9f6 C504 feat). Виток закрыл roadmap-пункты C499–C500 №1
(сужение sandwich-полос — Bernoulli-монотонность + адаптивный
предикат), №2 (upstream SVD-паспорт) и №3 (paper-черновик), а
также №4 (grow через блоки trunk). Главный сдвиг: машина роста
стала ДВУХОСЕВОЙ — fiber-ширина (C494-линия) и block-глубина
(C504), обе certified с точной нейтральностью при добавлении и
measured-прогрессом после обучения нового блока.

## Commit one-liners (C502–C504)

- C502 8640fb5 `feat:` adaptive sandwich band tightening —
  `Hagi/Theory/BandTightening.lean` (+431): `bernoulliLower_mono`
  (MVT-путь, монотонность Bernoulli-нижней границы по n, m) и
  `cert_pred_adaptive` (адаптивный certified-предикат с полосой,
  сужающейся по фактическим n, m); bench_bridge адаптирован.
  Прогнозная точность 4/6 — предел модели, а не полос (см. honest).
- C503 8f57839 `docs:` paper draft + SVD upstream prep —
  `docs/paper-draft.md` (7 блоков, 19 якорей),
  `docs/UPSTREAM-SVD.md` (паспорт топ-3 кандидатов для Mathlib
  upstream), STATUS-обновление. Внешний артефакт-виток: код не
  менялся, Lean-поверхность нетронута.
- C504 db9c9f6 `feat:` grow trunk block identity bench —
  `Hagi/Theory/GrowTrunkBlock.lean` (+155): residual-zero
  identity-добавление 3-го trunk-блока с ТОЧНОЙ obj-инвариантностью
  (равенство, не неравенство) при вставке; bench_bridge +479:
  grow-фаза глубина 2→3, 3-й блок certified-обучен, 4 шага
  measured-прогресса после нейтральной вставки.

## (а) Значение витка

- **Второе измерение роста.** C494 дал fiber-шишину как
  certified-ось роста; C504 добавил block-глубину: вставка
  residual-zero identity-блока строго нейтральна (obj-инвариант
  — равенство), а последующее обучение нового блока даёт
  measured-прогресс (4 шага). Обе оси — добавление с точной
  нейтральностью + certified-обучение — единый паттерн.
- **Bernoulli-пин закрыт.** `bernoulliLower_mono` (MVT) +
  `cert_pred_adaptive` завершают sandwich-фреймворк
  математически: полоса теперь функция измеренных n, m, и
  сужение легально certified. Точность прогноза осталась 4/6 —
  это предел МОДЕЛИ (regime-разбиение), а не ширины полос.
- **Внешние артефакты готовы.** paper-draft (7 блоков / 19
  якорей на proven-результаты) и SVD-upstream паспорт — оба
  certified-then-commit: каждое утверждение черновика
  trac'ается до theorem-index. Виток C503 — первый чисто
  внешний (нет кода), конвейер выдержал смену модальности.

## (б) Honest limits

- 4/6 точность прогноза после band tightening — сужение полос
  НЕ улучшило попадание: промахи уходят в модельный шум
  (regime-переходы), а не в полосу. Дальнейшее сужение —
  бесперспективно (Sunk-Cost сигнал).
- obj-инвариант при identity-grow сам по себе бесполезен —
  нейтральность это разрешение на рост, пользу даёт только
  certified-обучение нового блока (4 шага прогресса). Кривая
  «глубина vs прогресс» на одном прогоне не измерена.
- paper/upstream — черновики, не поданные материалы; upstream
  требует фактической отправки (внешний шаг, вне READ-ONLY
  машины).

## (в) Метрики витка (замер C505, READ-ONLY)

- **Freeze verify (HEAD db9c9f6, C504-гейты)**: PASS,
  `TestFreeze.py` 22/22 OK, **8589** declarations, 0 aliased,
  ничего не потеряно/не изменено (C500: 8574; +15 — C502
  BandTightening + C504 GrowTrunkBlock, всё через
  certify-then-commit).
- **Index**: дрейф C504 обнаружен и закрыт регеном в этом бите:
  575→**576** modules, 12758→**12765** theorems, 494→**495**
  Proven (db9c9f6 не включил theorem-index — GrowTrunkBlock
  отсутствовал в закоммиченном индексе).
- **Streak посадок**: 43 (C500) + C501–C504 = **47**; freeze
  PASS на каждом; посадка C505 → 48 подряд.

## (г) Roadmap следующего витка (ранжировано к цели)

1. **Повторяемый grow-цикл** — несколько grow-событий в одном
   прогоне: глубина 3→4→5 до предела вычислительного бюджета;
   измерить кривую «глубина vs certified-прогресс». Rank 1:
   превращает C504-паттерн из события в машину (главный вопрос:
  где насыщение).
2. **Selfloop-лог recheck** (внешний) — сверка логов
   selfloop-обучения с certified-предсказаниями. Rank 2:
   внешний цикл валидации.
3. **Upstream-SVD фактическая отправка** (внешний) — подготовить
   branch/patch-файл из docs/UPSTREAM-SVD.md (top-3 паспорт уже
   есть). Rank 3: внешний цикл, признание.
4. **Paper-полировка** — вставить числа из mini-HAGI-прогонов в
   docs/paper-draft.md, закрыть holes якорями на новые C502/C504
   результаты. Rank 4.
5. **A-GEM vs rank-trunc bench** — `agem_step_nonneg_interf` в
   прогоне против relaxed-GPM. Rank 5: завершает ветку C498.
6. **Imports-финал** — 63→0 deriv-safe механикой. Rank 6:
   гигиена, компаунд-ускорение.

Top-3 на следующий виток: (1) повторяемый grow-цикл (глубина
3→5), (2) selfloop-лог recheck, (3) upstream-SVD patch-файл.

## Honest limits (процедурные)

- C502/C504 — по одному живому прогону каждый (fixed seed);
  переносимость на другие корпуса не сертифицирована.
- BandTightening MVT-путь проверен Freeze-гейтами, но
  независимого statement-аудита нового модуля в этом витке не
  было (аудит-эра процедуры — по запросу перед upstream).
- Streak-счёт ведётся вручную по посадкам; receipts до C483
  фрагментарны в .tmp (после C499 фиксируются анализами).
