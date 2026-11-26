# HAGI_v2

Формализация на Lean 4 / Mathlib математической основы HAGI_v2 —
предполагаемой архитектуры тернарной RD-канальной причинной
языковой модели, развиваемой из небольших доменных экспертов.
Цель — качество обучения при ограниченном бюджете модели, памяти и
вычислений. Репозиторий даёт формальную основу этой цели, а не
сообщение о её достижении для реальной системы.

## Общая идея

Центральный объект — не изолированный алгоритм, а контур адаптивного обучения: состояние модели
связывается с энергией или целевым функционалом, измеренными эффектами, оценками качества,
памятью, стоимостью перехода и правилами accept/hold. Отдельные компоненты отвечают за
подготовку данных, выбор батча, шаг оптимизации, объединение экспертов, квантование,
консолидацию памяти и анализ траекторий. Контур позволяет формулировать точные вопросы: что
сохраняется при переходе, какие ресурсы расходуются, какие свойства доказаны на заданном
носителе. Схема — объект математического исследования, а не описание обученной полноразмерной
сети.

## Три уровня результата

1. **Математическая база.** Конечные алгебраические, вероятностные,
   информационные и энергетические утверждения без экспериментальных
   предпосылок.
2. **Условные сертификаты.** Свойства шага или конечной траектории,
   выводимые из явно перечисленных входных условий. Если свойство
   реального обучения задано как посылка, теорема его использует, но
   не доказывает.
3. **Мосты между ними.** Связи отдельных условий с конкретными моделями
   и доказанными механизмами; своя область применимости, посылки
   произвольной модели не устраняются.

`Hagi.Unified.CertifiedLoop.certified_loop` — верхнеуровневая теорема о конечной цепочке
сертифицированных переходов с общей целью, ограничениями качества и учётом бюджета (при своих
посылках). Частный мост: конечная log-linear one-hot CE, residual-направление и явно измеренные
old/new CE дают одношаговую оценку joint potential; обе CE-идентификации остаются предпосылками,
нулевое направление допускается. Условия и формула — [ALGORITHMS
§3.4](ALGORITHMS.md#34-конечная-log-linear-ce-и-joint-potential), главный результат — [карточка
DerivAlong](STATUS.md#hagiunified).

Не доказывается: достижение AGI, оптимальность архитектуры, качество обучения, глобальная
гладкость, сходимость, обобщение, преимущество по времени и объёму вычислений. Утверждения о
held-out данных относятся к отдельным моделям и не следуют из сертификата одного шага. Точные
формулировки, носители и предпосылки — в исходниках `Hagi/**/*.lean`; README их не заменяет.

## Рецепт одного цикла

Порядок и граница результата — [ALGORITHMS §10](ALGORITHMS.md#10-сборка-рецепта-и-граница-результата).

1. Задать experts/core/residual, проверить parameter и routing budgets — [§1](ALGORITHMS.md#1-архитектура-общее-ядро-и-маршрутизируемые-остатки).
2. Выбрать initial HNet ratio и разрядность только в их declared models — [§6](ALGORITHMS.md#6-квантование-и-распределение-памятибитов), [§7](ALGORITHMS.md#7-hnet-стартовый-ratio-из-continuous-cost-модели).
3. Вычислить residual-градиенты и supported propensity — [§3](ALGORITHMS.md#3-направление-и-сертифицированный-размер-шага), [§4](ALGORITHMS.md#4-выбор-примеров-supported-inverse-propensity-mse).
4. Взять общий `D̄`, вычислить `Ā,Q̄,eta_b`; иначе certified `D` или явный min-norm — [§3.2](ALGORITHMS.md#32-общее-направление-для-arithmetic-mean-batch), [§3.3](ALGORITHMS.md#33-min-normmgda-и-safeqp).
5. Выбрать оптимизатор по доказанному контракту — [§5](ALGORITHMS.md#5-оптимизатор-выбирать-по-доказанному-контракту), [§13](ALGORITHMS.md#13-средне-скоростной-optimizer-стек-ef21-muon).
6. Сформировать proposed successor, измерить каждую sample CE, риск и цену; guards, router и охлаждение — [§9](ALGORITHMS.md#9-исполнение-guards-router-и-охлаждение).
7. Принять только guarded/resource-certified successor, иначе hold; ядро — [§11](ALGORITHMS.md#11-каноническое-ядро-сертификации-hagicertcorelean).
8. Упаковать принятое представление, сложить все error terms — [§6](ALGORITHMS.md#6-квантование-и-распределение-памятибитов).
9. Оценивать выбор на новых данных fixed codebook, не на том же CE-чеке — [§8](ALGORITHMS.md#8-конечный-выбор-архитектуры-и-качества-оценки).

Минимизируются отдельно: supplied-batch CE, selected-estimator MSE,
quantization/certification error, declared resources, HNet cost.

## Структура репозитория

`Hagi.lean` — корневой модуль и общая точка импорта. Три
lake-библиотеки (`lakefile.toml`): `Hagi`, `Hagi.Benchmarks`,
`Hagi.Research`; цели по умолчанию — `Hagi` и `Hagi.Benchmarks`.

| Домен | Каталоги | Содержание |
| --- | --- | --- |
| База | [`Hagi/Math`](Hagi/Math), [`Hagi/Core`](Hagi/Core), [`Hagi/Numerics`](Hagi/Numerics), [`Hagi/Geometry`](Hagi/Geometry), [`Hagi/Spectral`](Hagi/Spectral), [`Hagi/StatMech`](Hagi/StatMech) | Общие определения, конечные носители, алгебраические и геометрические результаты |
| Архитектура | [`Hagi/Architecture`](Hagi/Architecture), [`Hagi/Ensemble`](Hagi/Ensemble), [`Hagi/Sparsity`](Hagi/Sparsity) | Композиция компонентов, объединение экспертов, структурные ограничения |
| Энергия и ресурсы | [`Hagi/Energy`](Hagi/Energy), [`Hagi/Budget`](Hagi/Budget), [`Hagi/Runtime`](Hagi/Runtime) | Квантование, энергия, ресурсный учёт, точные представления исполнения |
| Данные и обучение | [`Hagi/Data`](Hagi/Data), [`Hagi/Information`](Hagi/Information), [`Hagi/Probability`](Hagi/Probability), [`Hagi/Learning`](Hagi/Learning), [`Hagi/Optimization`](Hagi/Optimization), [`Hagi/Model`](Hagi/Model), [`Hagi/Generalization`](Hagi/Generalization) | Модели данных, выборки и потерь, оценки, оптимизация, вопросы обобщения |
| Переходы обучения | [`Hagi/Step`](Hagi/Step), [`Hagi/Pretraining`](Hagi/Pretraining), [`Hagi/Planning`](Hagi/Planning), [`Hagi/Contracts`](Hagi/Contracts) | Шаги, контроллеры, контракты переходов, конечные траектории |
| Рост и динамика | [`Hagi/Growth`](Hagi/Growth), [`Hagi/Dynamics`](Hagi/Dynamics), [`Hagi/State`](Hagi/State) | Состояния роста, устойчивость, бюджеты, динамические законы |
| Теория | [`Hagi/Theory`](Hagi/Theory) | Канон-модули, мосты HAGI_v2, growth-семья, bench-мосты; карта — [ALGORITHMS §27](ALGORITHMS.md#27-каноны-theory) |
| Интеграция | [`Hagi/System`](Hagi/System), [`Hagi/Unified`](Hagi/Unified) | Связанные состояния, измеренные эффекты, мосты, условные сертификаты |
| Дополнительные направления | [`Hagi/Autonomy`](Hagi/Autonomy) | Маршрутизация и смежные автономные модели |
| Примеры и сопровождение | [`Hagi/Challenge`](Hagi/Challenge), [`Hagi/Audit`](Hagi/Audit), [`Hagi/External`](Hagi/External) | Сравнительные формулировки, аудит, внешние математические связи |
| Сертификация и карантин | [`Hagi/Cert`](Hagi/Cert), [`Hagi/Benchmarks`](Hagi/Benchmarks), [`Hagi/Research`](Hagi/Research) | Ядро сертификации (`Hagi/Cert`); демонстрационные свидетели (`Benchmarks`), исследовательские модели Omni/Percolation/Schelling/Discovery и архив Legacy (`Hagi/Research/Legacy`) — вне корневого замыкания `Hagi.lean` |

Что нужно знать контрибьютору:

- `Hagi/External/` и `upstream/` — зеркала внешних источников; не редактировать
  (правка воспроизводится при sync).
- `Hagi/Research` (с `Legacy`) и `Hagi/Benchmarks` — карантин; `Research` вне
  `lake build` по умолчанию (`lake build Hagi.Research`), `Benchmarks` входит в цели
  по умолчанию.
- Формулировки (statements) заморожены `scripts/Freeze.py`.

## Документация

- [ALGORITHMS.md](ALGORITHMS.md) — архитектура и алгоритмы обучения, связь рецептов
  с формальными результатами и их посылками.
- [STATUS.md](STATUS.md) — главные доказанные результаты по каждому Lean-файлу Root
  с существенными условиями.
- [RELATED.md](RELATED.md) — соответствие внешним Lean-проектам.
- [docs/PROPOSAL-index.md](docs/PROPOSAL-index.md) — пакеты «теория → реализация»;
  [docs/PREMISES-STATUS.md](docs/PREMISES-STATUS.md) — открытые посылки;
  [docs/DERIVED-CONFIG.md](docs/DERIVED-CONFIG.md) — какие параметры обучения выводимы.
- [Hagi.lean](Hagi.lean) — карта импортов; `scripts/` — средства сопровождения.

## Сборка и CI

```bash
lake build                   # цели по умолчанию: Hagi, Hagi.Benchmarks
lake build Hagi.Research     # карантинная библиотека
bash scripts/ci.sh           # сборка + полная батарея проверок
python scripts/StatusLint.py # идентификаторы в документах существуют
```

### Воспроизводимость

- Lean закреплён в `lean-toolchain`; Mathlib — в `scripts/mathlib-rev.txt` (строка 1 —
  rev, строка 2 — коммит компилятора без суффикса сборки).
- В `lakefile.toml` зависимость `mathlib` указана локальным путём к предсобранной Mathlib.
  Для чистого клона замените require-блок на канонический git+rev-конфиг из комментария
  в `lakefile.toml` и запустите `lake build`.
