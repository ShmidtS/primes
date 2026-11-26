# UPSTREAM-SVD — Flywheel SVD Mathlib-вклад подготовка

Паспорт подготовки пакета `Hagi/External/Flywheel/` к предложению
в Mathlib. Проверка отсутствия выполнена rg по локальному
чекбауту Mathlib rev fc4f59e577feb1a4956671bc04ac18aaaf8cd842
(= scripts/mathlib-rev.txt, 2026-11); перед подачей PR перепроверить
на свежем master.

Лицензия: файл LICENSE репо — Apache 2.0; заголовки Flywheel:
«Copyright (c) 2025 FLYWHEEL … Released under Apache 2.0 …
Authors: Aleksandar Markovski». Совместимо с Mathlib (Apache 2.0);
при upstream сохранять авторство + стандартный Mathlib-header.

## 1. Инвентарь (22 SVD-модуля, Hagi/External/Flywheel/)

| # | Модуль | Роль / главный decl |
|---|---|---|
| 1 | SVD.lean | hub: реэкспорт SVD-семейства |
| 2 | SVDCore.lean | `svd_decomposition` :565 (ℂ, n×n, существование A = U Σ V*) |
| 3 | SVDReal.lean | `svd_decomposition` :352 (ℝ-вариант) |
| 4 | SVDDiagonal.lean | структура диагонального ядра Σ |
| 5 | SVDEigenvalues.lean | сингулярные числа через спектр A*A |
| 6 | SVDRectangular.lean | hub прямоугольного семейства |
| 7 | SVDRectangularDecomposition.lean | `svd_decomposition_rectangular` :541 (m×n) |
| 8 | SVDRectangularOrdering.lean | убывание сингулярных чисел |
| 9 | SVDRectangularNorms.lean | нормы через σ |
| 10 | SVDRectangularCoherence.lean | coherence-инварианты |
| 11 | SVDTruncated.lean | rank-k усечение |
| 12 | TruncatedSVDRank1.lean | rank-1 хвост |
| 13 | EckartYoungLower.lean | `eckart_young_lower_bound` :45 |
| 14 | CourantFischer.lean | `courantFischer_maxMin_bounds` :950, `courantFischer_minMax_bounds` :1090 |
| 15 | WeylInequality.lean | `weyl_eigenvalue_bounds` :374, `weyl_singularValue_perturbation` :774 |
| 16 | SpectralNormGap.lean | щели спектральной нормы |
| 17 | CoherenceCharacterization.lean | характеризация coherence |
| 18 | FrobeniusNorm.lean | Frobenius-норма, связь с σ |
| 19 | MatrixNormRelations.lean | соотношения матричных норм |
| 20 | MDLRank.lean | MDL-ранговые оценки |
| 21 | NormSupport.lean | support-леммы о нормах |
| 22 | NegDiagRank.lean | ранг с отрицательной диагональю (сервисный) |

## 2. Зависимость-карта

- **Внутри Flywheel**: только `import Mathlib.*` +
  intra-Flywheel импорты (rg "^import" — проверено). Ни одного
  импорта `Hagi.*`-внутренностей → каталог самодостаточен,
  upstream-извлечение = вырезание каталога с правкой импорт-путей.
- **Обратные потребители в Hagi** (rg -l "Hagi.External.Flywheel"
  вне External/, проверено): `Hagi/Contracts/TruncatedSVDTail.lean`,
  `Hagi/Contracts/GradientBottleneck.lean`,
  `Hagi/Contracts/GradientBottleneckIdentification.lean`,
  `Hagi/Contracts/SparseInferenceCert.lean`,
  `Hagi/Pretraining/ProbeError.lean`. Связи рвутся при извлечении,
  заменить на Mathlib-импорт после лендинга. Справочно:
  `Hagi/Step/Muon.lean` / `NewtonSchulzMatrix.lean` / `GPMRelaxed`
  упоминают SVD идейно, без импорта Flywheel.
- **Внутренние слои пакета**: NormSupport → SVDCore →
  SVDEigenvalues/SVDDiagonal → SVDReal → SVDRectangular* →
  SVDTruncated/TruncatedSVDRank1; CourantFischer →
  WeylInequality → FrobeniusNorm → EckartYoungLower.

## 3. README-паспорта кандидатов (8)

Формат: statement; Mathlib-совместимость; лицензия-заметка.

1. **svd_decomposition (SVDCore :565, ℂ / SVDReal :352, ℝ)** —
   существование SVD для квадратной матрицы. Совместимость:
   Mathlib API линейно-отображенческий
   (`LinearMap.singularValues`, Analysis/InnerProductSpace/
   SingularValues.lean); нужен мост `Matrix ↔ LinearMap.toMatrix`
   или переформулировка statement в Matrix-терминах. Лицензия:
   Apache 2.0, Markovski — ок.
2. **svd_decomposition_rectangular (SVDRectangularDecomposition
   :541)** — m×n вариант; та же совместимость-заметка.
3. **eckart_young_lower_bound (EckartYoungLower :45)** —
   оптимальность rank-k усечения в Frobenius-норме; зависит от
   FrobeniusNorm + SVDCore. Требует полный Frobenius (не
   спектральную норму) — комментарий в источнике (:1125).
4. **courantFischer_maxMin/minMax_bounds (:950/:1090)** —
   вариационная характеризация эрмитовых собственных чисел.
5. **weyl_eigenvalue_bounds (:374)** — устойчивость спектра
   эрмитовых матриц.
6. **weyl_singularValue_perturbation (:774)** — устойчивость
   сингулярных чисел.
7. **SVDRectangularOrdering** — antitone-порядок σ (в Mathlib
   есть antitone для LinearMap-версии — сверить дублирование!).
8. **FrobeniusNorm / MatrixNormRelations** — norm-слой; кандидат
   на слияние с Mathlib.Analysis.Matrix.Normed.

## 4. Приоритет-ранг (топ-3 + обоснование отсутствия)

Проверка на rev fc4f59e: в Mathlib ЕСТЬ только
`Analysis/InnerProductSpace/SingularValues.lean` — def
`singularValues` (LinearMap → ℕ→₀ℝ) + базовые свойства
(nonneg/antitone/support/zero-iff). rg -ni "Eckart" по Mathlib/ —
0 файлов; "courant|minmax" в Matrix/Spectral.lean и InnerProductSpace/
Spectrum.lean — 0; "weyl"-хиты только RootSystem/Cartan (группы
Вейля, не матричное неравенство Вейля).

1. **svd_decomposition (ℝ+ℂ)** — в Mathlib НЕТ теоремы
   существования SVD-разложения (ни матричной, ни LinearMap):
   def singularValues есть, разложения нет. Естественное
   достраивание к существующему API. Наибольшая ценность,
   наибольший объём (тянет SVDCore/SVDEigenvalues/SVDDiagonal).
2. **eckart_young_lower_bound** — каноничный результат, в Mathlib
   отсутствует целиком; малый дифф поверх (1); пакуется одним PR
   с FrobeniusNorm.
3. **weyl_singularValue_perturbation** — устойчивость SVD,
   отсутствует; самодостаточен после CourantFischer (кандидат 4,
   следующий эшелон).

## 5. Чек-лист дальнейших шагов

1. Перепроверить отсутствие на свежем Mathlib master
   (`rg -ni "singular value|Eckart|CourantFischer|Weyl"`).
2. Переписать statements в LinearMap-API (или мост Matrix↔LinMap).
3. Mathlib style-проход (naming, docstrings).
4. Разбить на PR-серию: NormSupport → SVDCore → rectangular →
   CourantFischer → Weyl → EckartYoung.
5. Заменить внутренние Hagi-импорты Flywheel на Mathlib после
   лендинга (строки §2).
