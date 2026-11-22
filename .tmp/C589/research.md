# C589 research — README canon-map под v6-реальность

Base: 009b6fad (C588), tree clean. Freeze base 8775. Docs-only транш V5.

## Что дрейфнуло в README.md (v5-карта vs v6-реальность)

1. Заголовок «Канон-карта (после рефакторинга v5, транши W1–W8)» —
   v6 (V1–V5) завершается этим траншем; LayerLint-таблица слоёв
   НЕ менялась (V1–V4 не трогали каталоги) — слой-карта остаётся.
2. Строка «Теория и канон-модули»: «31 файл: 10 канон-модулей…» —
   реально 47 файлов (ls Hagi/Theory | wc -l): 10 старых канонов +
   MasterTheoremV3 (канон v3-машины, C576), AdapterGrowth (канон
   механики роста адаптеров, 4 секции с маркировкой C587/C588-era),
   growth-семья (GrowSnap, GrowTrunkBlock, FunctionPreservingGrowth,
   AdapterBank), bridges-семья C530+ (RollbackGate, WeightDecayLeak,
   OEComplete, ExactBypass, FactLedger, RangeWrap, AdaptiveContext,
   NegativeTransfer, AutoTransferGate, TritCodec, MiniHagiLoop,
   KnowledgeConsolidation и др.), bench-семья (MiniHagi, MiniHagi2,
   MiniHagiLoop, TrainerBenchmark, CertCEHoldout, CertSandwichBench).
3. Таблица «Канон-файлы»: НЕТ строк про bridges-семью C530+
   (канон = таблица §27a ALGORITHMS, C588), AdapterGrowth-секции
   (V3 — маркировка секций вместо нарезки), Probability
   EmpiricalBernstein (канон EB-радиуса поверх Freedman, C539),
   Theory MasterTheoremV3 (канон 5 гарантий v3, C576).
4. Honest-границы: НЕТ записи про V2Bridges-слияние отложено
   (default (c) из v6-плана: до стабилизации HAGI_v2 cadence +
   опроса внешнего sync-агента FQN-vs-module-import); НЕТ записи
   про перманентность 22 bare-import deriv-pins (C571 терминальное
   состояние, STATUS.md:1884).
5. README ссылается на ALGORITHMS §3.4/DerivAlong, но НЕ ссылается
   на §27a (канон мостов C588) — добавить ссылку в канон-карту.

## rg-проверка путей (все пути в README-дельте реальны)

- Hagi/Theory/{AdapterGrowth,AdapterBank,MasterTheoremV3,GrowSnap,
  RollbackGate,WeightDecayLeak,OEComplete,ExactBypass,FactLedger,
  RangeWrap,AdaptiveContext,NegativeTransfer,AutoTransferGate,
  TritCodec,MiniHagiLoop,KnowledgeConsolidation,MiniHagi,MiniHagi2,
  TrainerBenchmark,CertCEHoldout,CertSandwichBench}.lean — ls ✓.
- Hagi/Probability/EmpiricalBernstein.lean — ls ✓.
- ALGORITHMS.md#27a — секция существует (строка 3382, C588).

## Гейты (docs-only, прецедент C588)

- StatusLint (backticked пути/идентификаторы в README не сканируются?
  — проверим: скрипт сканирует STATUS/ALGORITHMS; README-пути
  проверим rg вручную), DocLint (pre-existing паритет байт-в-байт),
  lake build (rc=0), Freeze identity 8775.
- README не входит в decl-набор Freeze и в StatusLint-цели
  (уточнить флаги; при включении README — PASS ожидаем).
