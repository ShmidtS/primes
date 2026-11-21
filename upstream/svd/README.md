# upstream/svd — Mathlib-кандидат `svd_decomposition` (топ-1 из C503)

Standalone-патч: существование SVD квадратной комплексной матрицы
`A = U * Σ * Vᴴ` (`Matrix.SVD.svd_decomposition`) для предложения
в mathlib4 (см. `docs/UPSTREAM-SVD.md`, топ-3 паспорт C503).

## Компиляция (вне lake-таргетов)

```
lake env lean upstream/svd/SVDDecomposition.lean
```

Статус: exit 0, 0 ошибок (против Mathlib rev fc4f59e, см.
`scripts/mathlib-rev.txt`). Единственный вывод — 5 deprecation-warnings
(`dif_pos` → `dite_eq_left`, `push_neg` → `push Not`) — актуальны для
нового Mathlib-master; устраняются на PR-этапе (см. чек-лист).
Файл НЕ входит в `lake build`: все `lean_lib` в `lakefile.toml` имеют
globs `Hagi.*` / `Hagi.Benchmarks` и т.п.; каталог `upstream/` ни одним
glob не покрыт, в `defaultTargets` отсутствует.

## Diff против оригинала (`Hagi/External/Flywheel/SVDCore.lean`)

1. **Header**: добавлен Mathlib copyright-header (Markovski, Apache 2.0 —
   из заголовков Flywheel, лицензия репо совместима) + модульный
   docstring upstream-candidate (назначение/происхождение/статус).
2. **Namespace**: удалён внешний `namespace Hagi.External.Flywheel` …
   `end Hagi.External.Flywheel`; остался `namespace Matrix.SVD`
   (Mathlib-стиль: результирующие FQN `Matrix.SVD.*`).
3. Всё остальное (импорты, `open`, переменные, все 27 decls и
   доказательства) — байт-в-байт. Никаких переименований decl-имён и
   правок доказательств (minimal diff, защита от statement drift).
   Hagi-специфика в файле отсутствовала: импорты только `Mathlib.*`
   (проверено rg '^import').

## Чек-лист для PR в mathlib4

- [ ] Перепроверить на свежем master: `Matrix.singularValues` /
      коллизии имён (Mathlib имеет `LinearMap.singularValues` — def без
      теоремы существования; рассмотреть мост или переименование при
      ревью).
- [ ] Deprecated-вызовы: `dif_pos` → `dite_eq_left` (3×),
      `push_neg` → `push Not` (1×) — новые имена на master.
- [ ] Место в дереве: кандидат `Mathlib/LinearAlgebra/Matrix/SVD.lean`
      (или `Mathlib/Analysis/Matrix/SVD.lean`); обновить module
      docstring-заголовок (убрать UPSTREAM CANDIDATE-блок).
- [ ] Стиль: `lake lint`/CI mathlib — стиль docstring'ов, длина строк
      (100), `set_option maxHeartbeats` обосновать (2× 400000) или
      уменьшить; lint `unusedSectionVars`-варнинги просмотреть.
- [ ] Header: сохранить авторство Markovski + Apache 2.0 (уже в файле).
- [ ] CI: `run_lake.sh`-билд, `style-check`, `check-powered-by` —
      стандартный mathlib CI.
- [ ] Прочитать CONTRIBUTING mathlib4: PR-описание, Zulip-обсуждение
      (обсуждение API `unitaryGroup` vs `Matrix.Unitary` — вероятное
      ревью-замечание).
