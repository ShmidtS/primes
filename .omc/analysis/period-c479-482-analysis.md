# Phase analysis: C479–C482 — конвейерная эра HAGI-bench (2026-11-20)

Series HEAD 99d17096 (chore: stmdup allowlist поверх a7c14ec3 = C482;
`git log -2` проверен). Виток C479–C482 закрыл дорожную карту C478
top-3 ЦЕЛИКОМ: (1) сквозной bench-цикл — C479, (2) HAGI_v2 порт-пакет —
C480, (3) trunk-обучение — C481; плюс транш-3 гигиены импортов — C482.
HAGI-bench после этого витка — ПОЛНАЯ certified-модель целевого
цикла, не набор изолированных режимов.

## Commit one-liners (C479–C482)

- C479 9544bd48 `feat:` unified full pipeline certified bench —
  Hagi/Theory/FullPipeline.lean (211 строк) + bench `--mode
  full-pipeline`: ОДНА задача проходит ШЕСТЬ фаз подряд (TRAIN →
  EF21 → HADAMARD-TERN → GROW → MERGE → STOP) как один CertStepData
  трейс. Всё — composition GLUE поверх существующих теорем
  (C462/C474/C477/C443/C444/C476/C446 через certify_then_commit_sound
  C463, T=6). Лосс 46/3 → ~0.0677, holdout-stop сработал.
- C480 7f658697 `docs:` hagi port proposal package — 4 новых
  PROPOSAL-документа (tight-kappa C471, fisher-quant C472,
  joint-step C475, merge-meas C476) + PROPOSAL-index.md (5 записей,
  adaptive-majorizer C466 помечен SUPERSEDED). Каждый: Lean-якоря,
  freeze-пин (8462), минимальный Python-diff, sanity-числа,
  критерий валидации. Sanity-скрипты: .tmp/C480/.
- C481 4723fa02 `feat:` certified trunk training bench —
  Hagi/Theory/TrunkTrain.lean + bench `--mode trunk-train`:
  НЕЛИНЕЙНЫЙ ствол (рациональный RMSNorm-суррогат x/(|x|+ε),
  docstring-пин, W1-ReLU-W2), обучаемый JOINTLY с головой.
  Live-гарантия — measured descent в точных Fraction с
  guarded rollback (hold-семантика C443/C474); A/R/dd — телеметрия.
- C482 a7c14ec3 `refactor:` import tranche three + heartbeats —
  13 файлов сужены с bare `import Mathlib` на адресные импорты
  (76 → 63), честный итог: компаунд-ускорение НЕ наступило —
  транзитивные цепочки всё ещё содержат bare-модули; выигрыш
  только в цепочках, суженных ПОЛНОСТЬЮ (SphericalAngle: 7339 vs
  18261 jobs до отката). Транш-4 (63) — где ляжет компаунд.
- (тех.) 99d17096 `chore:` stmdup allowlist — TrunkTrain.
  trunk_traj_drop_pos задокументирован как намеренный близнец
  FullPipeline.full_traj_drop_pos (паттерн C479-glue, прецедент
  C476/C481).

## (a) Конвейерная эра: bench как модель целевого цикла

До C479 bench тренировал режимы ПО ОТДЕЛЬНОСТИ (cert-ce, ef21-step,
hadamard-tern, grow, grow-stop). После C479–C481 bench моделирует
весь жизненный цикл HAGI_v2: обучение → сжатие (EF21 in-step) →
квантование (когерентностный гейт + ternary jump) → рост (admission
margin) → слияние (measured-δ) → останов (Ville anytime), и ствол
обучается нелинейно и совместно с головой, с certified-шагами.

Что отличает bench от «реальной» модели (honest list):

1. **Масштаб данных** — bench-задачи крошечные (считать лосс можно
   в точных Fraction); реальные датасеты HAGI_v2 на порядки больше.
2. **Настоящий softmax** — CE считается на рациональном
   суррогате/точной арифметике, не на float-softmax с
   log-sum-exp; RMSNorm — рациональный суррогат x/(|x|+ε).
3. **Параллельность** — bench последователен; реальный цикл —
   конкурентные ветки/эксперты.
4. **Live-гарантия vs теория**: bench коммитит по measured drop > 0
   (execute-grounded); теоретические критерии (2A²/R², гейты) —
   advisory/теги. Это осознанный дизайн (honesty-пины в обоих
   модулях), но означает: bench проверяет МЕХАНИКУ контура, а не
   численную силу мажорант.

Всё же каждый шаг certified (MachineDiffTest C482: 2000 конфигураций,
1923 certified) и freeze непрерывен.

## (б) Порт-пакет: механизм доставки — ФИКСИРУЮ

5 предложений готовы агенту HAGI_v2 (4 Proposed + 1 SUPERSEDED).
Механизм доставки (прецедент C466, единственный работавший путь):

1. **Переносчик — пользователь**: docs/PROPOSAL-*.md подаются в
   контекст агента HAGI_v2 (это отдельный проект/сессия; общего
   канала нет, кросс-репо автоматики не существует).
2. **Возврат статуса — лог + STATUS.md**: после порта HAGI_v2-агент
   (или пользователь) меняет статус в docs/PROPOSAL-index.md
   Proposed → Ported и добавляет запись в STATUS.md с номером
   валидации loop-5 (`real ≥ certified` на каждом шаге — критерий
   прописан в каждом документе). Sanity-эталоны для сверки:
   .tmp/C480/sanity-{tight-kappa,fisher-quant,joint-step,
   merge-meas}.py.
3. **Происхождение — Lean-якоря**: каждый документ цитирует
   freeze-пиннутые якоря primes (Freeze 8462) — обратная
   прослеживаемость после порта сохраняется через git-историю primes.

## (в) Метрики витка (замер C483, READ-ONLY)

- **Freeze verify (HEAD 99d17096): PASS, 8468 declarations,
  0 aliased, nothing lost/changed** (.tmp/C483/freeze-verify.log;
  8453 на C478 → +15 за виток: FullPipeline 14 thm/22 defs +
  TrunkTrain, частично сокращено траншем C482).
- **Index regen (C483)**: exit 0, пойман дрейф — закоммиченный
  индекс был 562/12509/4637/481-Proven; фактический **564 modules /
  12527 theorems / 4677 defs / 1192 noncomputable, Proven 483**
  (+FullPipeline, +TrunkTrain). Закоммичен в этом бите (прецедент
  C478). Axiom-профиль: propext / Classical.choice / Quot.sound,
  без дрейфа (AllAxiomCheck PASS в C482-гейтах).
- **Streak посадок**: 22 (C456–C478) + C479/C480/C481/C482 = **26
  подряд** (27 коммитов с техническим stmdup-chore), freeze PASS
  на каждом.
- **Bare imports**: 76 → **63** файлов (`rg -l --crlf
  '^import Mathlib$' Hagi/`, ground truth; без --crlf rg видит
  только 31 — CRLF-ловушка, зафиксирована ещё в C482-research).
  Компаунд-эффект по job-graph только при ПОЛНОМ сужении цепочки.

## (г) Roadmap ≥6, ранжировано к цели (certified-цикл ≈ реальный)

1. **Масштаб данных в trunk-bench** — подключить реальный датасет
   из HAGI_v2 corpus (read-only чтение данных извне primes —
   разрешено; запись нет). 100+ точек, holdout-статистика, лосс в
   float с certified-границей. Это главный remaining-разрыв (а)-1:
   без масштаба bench остаётся механической моделью. Rank 1 —
   бьёт в самый большой honest-гэп.
2. **Без-возвратный holdout (C435-пин хвост)** — зафиксировать
   holdout до цикла так, чтобы никакой шаг (включая гейты) не мог
   его перечитать; замкнуть хвост C435. Rank 2 — дешёвый,
   закрывает методологическую дыру в статистике стопа.
3. **Continual/parallel-фронт** — несколько задач ПОСЛЕДОВАТЕЛЬНО
   на одном стволе, GPM-нулевое забывание как bench-метрика
   (certified non-interference). Rank 3 — прямой шаг от одного
   certified-цикла к certified-последовательностям (продолжение
   C478-roadmap №6).
4. **Selfloop-лог (внешний recheck)** — 149-раундовый selfloop
   нельзя проверить внутри репо; внешний запуск + лог-файл как
   intake. Rank 4 — ценен, но блокер внешний (как в C478).
5. **Imports финальный транш (транш-4, 63 bare)** — полный заход
   с deriv-pin механикой (deriv-risk family): только после него
   компаунд-ускорение job-graph (7339-vs-18261 эффект) станет
   массовым. Rank 5 — гигиена, эффект отложенный, но измеримый.
6. **Curriculum-теория в bench** — CurriculumCert → порядок данных
   как certified-параметр цикла (порядок задач с сертификатом).
   Rank 6 — ново и конгруэнтно контуру, но зависит от (1) и (3):
   curriculum без масштаба данных и последовательностей не
   тестируем.

Top-3 на следующий виток: (1) масштаб данных в trunk-bench,
(2) без-возвратный holdout, (3) continual-фронт (GPM-нулевое
забывание).

## Honest limits

- C482 «13/76» честно БЕЗ warm speedup — не скрывать: компаунд
  только при полном сужении цепочки (SphericalAngle — единственный
  полный пример, потом откат).
- C479/C481 — glue-теоремы: НОВОЕ только композиция, маршруты и
  witness-мост; компонентная математика не переутверждается
  (route map — TAG, не клейм ре-вывода).
- Bench-линейная голова C479 против нелинейного ствола C481 —
  ствол НЕ проходит через softmax-голову реального класса; это
  суррогатная цепочка (honesty-пин в TrunkTrain).
- Freeze в (в) измерен на HEAD 99d17096 (stmdup-chore поверх C482);
  сам chore-коммит деклараций не менял.
- Index-дрейф 562→564: закоммиченный индекс C481/C482-битов не был
  регенерирован — это второй раз подряд (C478: 556→562); правило
  «regen в каждом аналитическом бите» соблюдено теперь, но
  нарушение в C479–C482 фиксируем.
