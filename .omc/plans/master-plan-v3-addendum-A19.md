# Addendum A19 — четвёртый внешний аудит: certify-then-commit + план слоистой переработки

Источник: user-provided audit (2026-11-19), HEAD ~C447 (50358a5).

## Вердикт (принят)

- Сильное: вероятность (freedmanD, Ville/e-process, holdout), оптимизаторы,
  квантование-кодеки, DerivedState/CertChecker/RiskChannel/StageDropCertificate.
- Главные слабости (по убыванию):
  N1 нет теорем о многослойной нелинейной сети (trunk = интерфейс: hLip/hCausal — поля);
  N2 капстоуны — тавтологии учёта (спад — поле структуры; инстансы — игрушки);
  N3 автомат записывает, а не вычисляет (energy из StageEffects; Adam-моменты не EMA);
  N4 takeoff = решение рекуррентности при 49 h_emp_* допущениях;
  N5 слияние точно только для линейного по параметрам;
  N6 границы неприменимы в масштабе (quant-мост √(V·n); CE-мажоранта по размаху, не Var_p);
  N7 Describes/hcost/hfl — гипотезы доверия измерению;
  N8 структура: 44% модулей никто не импортирует; 14 островов Core/Architecture;
  цикл 7 директорий; lse/softmaxP в Core/Concat; Flywheel обслуживает один кластер;
  20 модулей >1000 строк; 25 maxHeartbeats до 16M; 73 bare import Mathlib.

## Программа A19 (фазы аудита, адаптировано)

1. A19.1 Чистка: Legacy → git-тег (Benchmarks-witness перенести); 6 висячих Growth —
   подключить или Research; убрать TelescopeInstances/Ctv2Telescope; lse/ceOneHot/softmaxP
   из Core/Concat в канонический Info-модуль. Критерий: Archive/Research никем не импортируются.
2. A19.2 Журнал+состояние: StepRecord + AdditiveLedger; 23 cert-структуры → toRecord;
   один TrainState; StageEffects — выход, не вход.
3. A19.3 Вероятность/информация: одна PMF-подложка; мосты один раз; свернуть
   prodE/pmfMean/densD; дубли имён 69 → 0.
4. A19.4 Спуск/квантование: SmoothMajorizer база; 46 CE-модулей → 8-10; scale/padding/
   codebook-CE → Quant/Codebook (выбор масштаба из кодбука + union bound); одна
   «дефект+PL»-лемма. Deprecated-алиасы для старых имён.
5. A19.5 Острова: одна теорема «функция-сохраняющее расширение»: BlockDiag/OrthoFiber →
   CertifiedBlock + growLM; иначе — Research. У каждого Model/Merge — импортёр.
6. A19.6 Нарезка: швы в модулях >1000 строк; микромодули слить; import Mathlib → точечные;
   maxHeartbeats ≤ 400k; циклов между директориями нет.

## Алгоритмический план (предложения аудита, в репо их нет)

P1 адаптивная CE-мажоранта: Var_p(Δz)·(e^{ηR}−1−ηR)/R² вместо range²/8;
P2 штраф квантования по Fisher (кривизна), не lip·ε_q; weightedExpAllocation_optimal;
P3 квантование внутри шага (EF21 contractive), не пост-фактум;
P4 рост только функция-сохраняющим блоком + откат;
P5 Hadamard-поворот под проверяемым условием некогерентности.

## Целевой certify-then-commit цикл (SSOT)

PROPOSE (SGD/Muon/sign/Dust, η≤η_safe) → CERTIFY (drop_lb = α²/4c − 2·lip·ε_Q;
e-process LCB(gain)) → ADMIT (LCB−λM·Δmem−λR·Δrisk−ε>0; Парето) → COMMIT/HOLD/ROLLBACK
(δ-бюджет Σw≤1) → LOG (CertStepData ℚ → checkTrajectory). Пробелы G1-G6: вывод lip/causal
для реальных блоков; ствол-мажоранта; Fisher-мост; адаптивная CE-мажоранта; слияние вне
линейного; сквозная теорема цикла. Метрика практики: логировать «граница/измеренное» в
CertStepData; неподтверждённая h_emp_* → стоп роста (взлёт как наблюдаемое условие).

Правила: freeze-identity на переносы; deprecated-алиасы; каждый бит = probe → plan/review
→ gates → атомарный коммит → receipt. Приоритет: честность > полнота; разрядка > новые
капстоуны.
