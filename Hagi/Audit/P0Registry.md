# P0 Registry — фактическое состояние доказанной теории (этап 0 плана рефакторинга)

Дата: 2026-10-18. Все проверки выполнены на текущем HEAD рабочей копии.

## 1. Объём

- Lean-модулей в `Hagi/`: 267; импортов в `Hagi.lean`: 266.
- Деклараций (Freeze lock, CI-гейт): 2766; DupLint: 0 дубликатов.
- `h_emp_*`-посылок: 118 в 34 файлах (assumptions.lock, CI-гейт AssumptionScan);
  17 инфо-примитивов.
- CI: LINT / MATHLIBPIN (56a00585) / DUPLINT / NSLINT / DOCLINT / LAYERLINT /
  FREEZE / ASSUMPTIONSCAN / STATUSLINT — все PASS; полная сборка `lake build`
  успешна (LAKE_JOBS=16).

## 2. Транзитивные аксиомы ключевых capstone-теорем

Все перечисленные зависят только от [propext, Classical.choice, Quot.sound] —
стандартный трио Mathlib; `sorryAx` отсутствует:

- `Hagi.Unified.MasterHAGI`, `MasterHAGI_trunc`, `masterhagi_growth_witness`,
  `frontier_cone_trunc`, `sustained_takeoff_trunc`
- `Hagi.Unified.hagi_synthesis`, `grand_synthesis`, `grand_synthesis_weak`
- `Hagi.Energy.temperature_corridor`, `landauer_cooling_floor`
- (исторические spot-check'и: Sidon-мост, SphericalDamping, InexactContraction,
  DirectionPacking/Welch, Cooling — тот же трио.)

## 3. Скан `sorry` / `axiom`

`rg "sorry|axiom "` по `Hagi/` даёт совпадения ТОЛЬКО в комментариях/докстрингах
(CoherenceCharacterization.lean:1789, FreedmanTwoSided.lean:13/198/772 —
заявления «0 sorry» в документации). Объявлений `sorry`/`axiom` в коде нет.

## 4. Классификация (карта для этапов 1–7)

- **Доказанные математические законы** (без модельных посылок): Уэлч-граница и
  её следствия; Нернст-оценки, E=F+T·S, максимум энтропии, thermal_blur/
  reveal/corridor/pair; неточное сжатие (bound/floor/halt); AA-gain;
  Slerp-геометрия; геометрические суммы/расписания; Sidon; концентрация
  (Hoeffding/Azuma/Freedman...); спектральные (Flywheel).
- **Условные теоремы** (с `h_emp_*`-посылками — реестр в assumptions.lock):
  Landauer-мосты, cone_step/takeoff-семейство, MasterHAGI-цепочки. По плану
  (этап 5B) физические посылки подлежат отдельному обоснованию.
- **Определения/модели**: GrowthState/StageSemantics (две семантики —
  конфликт №1 этапа 1), Potential Φ1/Φ2 (конфликт №2), StageEffects-бюджет
  (конфликт №3), CorePremises (включает S'.gen = S.gen — критический пункт
  этапа 4, требует решения: неизменяемая архитектура или обучаемый компонент).
- **Открытые задачи**: Layer 4 перколяции (p_c → takeoff), P0-переносимая
  сборка (отсутствие elan — внешний блокер), сложность AdaptiveSafeQP
  (сетка направлений может расти экспоненциально).

## 5. Блокеры P0

- «Воспроизводимое окружение» в строгом смысле (elan-менеджер) недоступно в
  сессии; используем pinned toolchain + MathlibPIN-гейт — фиксация ревизии
  есть, управление toolchain — внешняя задача.

**Вывод:** каркас теории целостен (0 sorry, аксиомы стандартные, гейты зелёные);
переход к этапу 1 (единая семантика перехода, единый потенциал, ресурсный
контракт) обоснован.
