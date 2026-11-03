# Воспроизводимая сборка HAGI (audit P0)

Фиксация окружения, относительно которого доказаны все теоремы:

| Компонент | Версия |
|-----------|--------|
| Lean toolchain | leanprover/lean4:v4.35.0 |
| Mathlib | commit 56a005855ea17e0b0958f73ec801ae140b0a1679 (chore: bump toolchain to v4.35.0 #44806) |

Файлы-свидетели: lean-toolchain, scripts/mathlib-rev.txt,
lake-manifest.json (транзитивные deps с rev-ами).

## На машине разработчика (Windows, локальная сборка Mathlib)

lakefile.toml указывает path = C:/Users/shmid/mathlib4 —
готовая скомпилированная Mathlib нужного коммита (быстрая сборка,
без загрузки). Ничего делать не нужно: lake build && bash scripts/ci.sh.

## На чистой машине (переносимая конфигурация)

1. Установить elan и toolchain v4.35.0 (elan toolchain install
   leanprover/lean4:v4.35.0; elan default — та же версия).
2. В lakefile.toml закомментировать локальный [[require]]
   (name/scope/path) и раскомментировать git-вариант с
   rev = 56a0058... (блок уже подготовлен в комментарии).
3. lake update (скачает Mathlib и транзитивные deps по
   манифесту), lake build (первая сборка Mathlib: ~1-2 часа,
   32+ ГБ RAM или swap; дальнейшие сборки инкрементальны).
4. Проверка доказательной базы: bash scripts/ci.sh —
   16 гейтов, включая ALLAXIOMS (только
   [propext, Classical.choice, Quot.sound]), FREEZE
   (3917 деклараций), 0 sorry.

## Быстрая альтернатива без пересборки Mathlib

Склонировать Mathlib нужного коммита отдельно (git checkout
56a0058...), собрать один раз (lake build в клоне), затем указать
path на клон в lakefile.toml (тот же блок) — и lake update в primes.
