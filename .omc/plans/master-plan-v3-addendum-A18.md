# Addendum A18 — третий внешний аудит: трёхъярусная верификация + план разрядки

Источник: user-provided deep audit (2026-11-18), HEAD на момент аудита ~C421.

## Вердикт аудита (принят)

- Ярус A (настоящая математика): SVD/Eckart-Young, CE-анализ с явными
  константами и безусловной ridge-GD сходимостью, heavy-ball, NS/Muon,
  EF21 с честными препятствиями, Freedman/Ville/e-process, regret/halving,
  верифицированные кодеки/KV-кэш. ~20-25% корпуса.
- Ярус B: certificate-алгебра (54 структуры, 27 адаптеров) — корректно,
  но элементарно; телескопы пере-доказаны ≥6 раз.
- Ярус C: 91 теорема с h_emp_* посылками; кластер takeoff/RSI (11 файлов
  Growth) вне корневого замыкания Hagi.lean — карантин де-факто.

## Принятые слабости (работаем)

W1 состояние=телеметрия (energy не функция весов); W2 нет LM как функции;
W3 обобщение не статистическое; W4 инфляция имён / UNFOLD_ECHO;
W5 две вероятностные башни без моста; W6 дубли (2 softmax, 6 телескопов,
momentum×3, EF×4, SafeQP×5) и мегафайлы; W7 нет исполнимости (noncomputable ℝ).

## Целевая архитектура (директива)

Math/ (LinearAlgebra, Analysis, Probability, Information, Online, Numerics)
→ Model/ (Head/ — ОДИН softmax, Blocks, Quant, Memory, Ensemble)
→ Step/ (Direction, Size, Compress, Safe) → Cert/ (ядро: один телескоп
через AdditiveLedger typeclass; 54→~6 структур) → State/ (одно каноническое,
evaluate ВЫВОДИТСЯ из Model.Head; effects — типизированная телеметрия)
→ Loop/ (Kernel + Controller-разрез ParetoExecution + Monitor)
→ Growth/ (выводимые effects; takeoff → rename geometric_growth_of_assumed_dynamics)
→ Examples/; Archive/ отдельным пакетом вне defaultTargets.

## Программа A18 (биты, приоритет по отдаче)

1. A18.1 softmax-унификация: Energy.smax → softDef, теорема-мост,
   CEDescent на softDef.
2. A18.2 UNFOLD_ECHO-линт: расширение TrivialLint (заключение =
   развёрнутая посылка) → baseline, только сжатие.
3. A18.3 Cert-ядро: один телескоп (AdditiveLedger), слияние
   CertifiedLoop/Kernel/HonestTransition/StepContract/TransitionCert/
   CommitGate → ядро+адаптеры.
4. A18.4 разрядка h_emp_smooth/lip через DerivAlong-мост для блоков
   (fderiv-границы RoPE/attention-композиций).
5. A18.5 confinement для safe-step динамики (монотонность loss ⇒ шар)
   + margin_pl_ball ⇒ глобальный PL-режим. Разрядка PL.
6. A18.6 State-унификация: energy/effects как функции весов
   (coherentGrowth — инвариант конструкции, не теорема-заплатка).
7. A18.7 вероятностный мост finite-PMF ↔ MeasureTheory; Freedman для
   адаптированных дисперсий.
8. A18.8 исполнимый сертификат-чекер (Kernel-леджеры + BitVec-кодеки)
   как внешний валидатор тренера; заменa синтетических Nonvacuity.
9. A18.9 карантин: Legacy/Research отдельным пакетом; переименование
   инфляционных имён (muon_pl_rate и др.).
10. A18.10 точные импорты вместо `import Mathlib` (97 файлов).

Правила: freeze-identity на переносы; каждый бит = probe → plan/review →
gates → атомарный коммит → receipt. Приоритет конфликтов: честность
над полнотой; разрядка посылок > новые мастер-теоремы.
