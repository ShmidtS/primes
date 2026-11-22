# C589 plan — v6 t5: README canon-map под v6, honest-границы

Base: 009b6fad (C588). ONE atomic commit
`refactor: v6 t5 readme canon map`. Freeze base 8775.

## Шаги

1. README.md, секция «Канон-карта»: заголовок →
   «после рефакторингов v5 (W1–W8) и v6 (V1–V5)»; слой-таблица
   LayerLint без изменений (DAG не менялся V1–V4).
2. Строка «Теория и канон-модули» в таблице структуры: 47 файлов;
   перечислить семьи: 10 канонов v5 + MasterTheoremV3; growth-семья
   (AdapterGrowth [4 секции — маркировка v6-V3], AdapterBank,
   GrowSnap, GrowTrunkBlock, FunctionPreservingGrowth);
   bridges-семья C530+ (канон — §27a ALGORITHMS); bench-семья.
3. Таблица «Канон-файлы»: + строки:
   - Theory MasterTheoremV3 — канон 5 гарантий машины v3 (C576);
   - Theory AdapterGrowth — канон механики роста адаптеров, секции
     промаркированы (v6-V3), нарезка не делалась;
   - Probability EmpiricalBernstein — канон EB-радиуса поверх
     Freedman (C539);
   - Theory bridges C530+ — канон-носитель описаний = ALGORITHMS
     §27a (C588), одно описание одного моста ровно один раз.
4. Honest-границы: + V2Bridges-слияние микс-мостов отложено до
   стабилизации HAGI_v2 cadence и опроса внешнего sync-агента
   (FQN vs module import); + 22 bare-import deriv-pins
   перманентны (C571 терминальное состояние, сужение запрещено
   deriv-риском).
5. Гейты (.tmp/C589/logs/): StatusLint (PASS), DocLint
   (pre-existing байт-паритет), lake build rc=0, Freeze identity
   8775. README не трогает decl-набор и docstring — DocLint-профиль
   байт-в-байт с HEAD.
6. Receipt .tmp/C589/receipt.md, маркер последней строкой, sha256
   предпоследней строкой. .tmp/C589/* add -f (прецедент C585/C588).

## Риски

- StatusLint сканирует README: только новые реальные пути — rg
  проверено (research.md).
- Никаких Lean/docco правок → build/DocLint паритет ожидаем.
