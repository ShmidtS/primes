# C585 notes — survey новых Theory-модулей с v5 (C522)

Base: 64aae9ae (C583). C584 (KnowledgeConsolidation) in flight — НЕ читан,
в планах помечен отдельной строкой.

## Инвентарь: 14 новых файлов в Hagi/Theory/ (31 → 46 с v5, minus C584)

Все — source-anchored мосты к HAGI_v2 (upstream файл:строка в докстринге),
все в собственных namespace `Hagi.Theory.<Name>` (FQN стабилен).

| Файл | строк | C-бит | import Hagi | тема |
|---|---|---|---|---|
| FactLedger | 71 | C579 | MasterTheoremV3 | append-only факт-леджер |
| RangeWrap | 63 | C581 | FactLedger | piecewise range-affine mod |
| AdaptiveContext | 114 | C582 | RangeWrap | Occam-выбор окна контекста |
| OEComplete | 120 | C540 | — | Levin+OE дедупликация поиска |
| ExactBypass | 129 | C541 | InfoCore | PROVEN_EXACT symbolic bypass |
| TritCodec | 137 | C574 | — | 5-trit/byte codec |
| MasterTheoremV3 | 89 | C576 | AG+MHL+NT | метатеорема-спецификация v3 |
| AutoTransferGate | 164 | C577 | NT+AdapterBank | warm/cold transfer-гейт |
| WeightDecayLeak | 166 | C538 | Continual | GPM memory under decay |
| MiniHagiLoop | 203 | C547 | EB+AG+OE | full self-improving loop bench |
| NegativeTransfer | 213 | C572 | — | точная граница негативного переноса |
| RollbackGate | 239 | C530 | — | exact pre-step rollback |
| AdapterBank | 231 | C567 | AdapterGrowth | bank доменных адаптеров |
| GrowSnap | 166 | C521 | GrowTrunkBlock | snap-политика grow (пограничный,
| | | | | в v5-дереве отсутствовал, создан после) |

## Ключевые находки

1. **Serial spine smell**: MasterTheoremV3 → FactLedger → RangeWrap →
   AdaptiveContext — линейная цепочка, каждый следующий импортирует
   предыдущего. У RangeWrap/AdaptiveContext нет содержательной
   зависимости от предшественника — это cadence-артефакт (каждый новый
   мост ставился «поверх» предыдущего). Candidate: слить хвост спайна
   + одиночные микс-мосты в Hagi/Theory/V2Bridges.lean.
2. **Все namespace раздельные** → merge_module.py сохраняет FQN
   деклараций. РИСК: внешние sync-агенты импортируют модули по
   `import Hagi.Theory.X` — слияние ломает module path. Митигируется
   re-export shell'ами (3 строки) или отказом от слияния до
   стабилизации HAGI_v2 cadence. Материал ГОРЯЧИЙ (C530+ биты активны).
3. **AdapterGrowth 908 строк, 4 секции** (C532 базис + C555
   self-compressing + C556 cluster distillation + C558 mini-v3
   reference) — нарезка по секциям без переноса деклараций (прецедент
   W7-опций v5).
4. **Header/docstring drift**: 6 из 9 свежих файлов ставят
   `set_option linter.style.header false` и используют `##` вместо
   канонического `#`; RollbackGate/MasterTheoremV3 — канонические.
   Нужен единый канон-заголовок в V-транше доков.
5. **bench_bridge.py ссылается на 24 вхождения новых модулей** —
   мосты живые, монолит-вердикт v5 (W5) подтверждён.
6. Freeze.py сейчас падает (stale olean, incompatible header) — на
   docs-only бите build не запускался; identity-гейт фиксируется на
   исполнение траншей (нужен свежий `lake build` перед Freeze).

## Дрейф старых каталогов (быстрые rg-проверки, не re-read)

- Hagi.lean: добавлены импорты новых Theory-модулей — ожидаемо (root hub).
- STATUS.md: ссылается на новые мосты — продолжение роста (v5-W6
  свёртка до ~1500 НЕ выполнена → перенос в v6 V4).
- scripts/bench_bridge.py: +24 ссылки на новые модули, режимы
  mini-hagi-loop / adapter-transfer-auto / trit-codec и т.д.
- docs/: PALOMAR-CARDS.md, paper-draft.md ссылаются на новые мосты —
  docs-словарь продолжать с учётом bridges-терминологии.
- Вне Theory/: новых import новых модулей нет — дрейфа потребителей
  нет, LayerLint DAG не менялся.

## PolarExpressCert

Живёт в Hagi/Optimization/PolarExpressCert.lean (не Theory) — вне
инвентаря Theory, учтён в V-транше доков Optimization.
