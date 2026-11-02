# RELATED — соответствие HAGI внешним Lean-проектам (обзор 2026-10)

Топ-5 приоритетов исследования + соответствие файлов HAGI.

| Проект | Фокус | Соответствие в HAGI | Действие |
|---|---|---|---|
| FormalSLT | time-uniform PAC-Bayes, confidence seq, e-processes | Unified/AnytimeMartingale (Ville, e-process), Unified/AnytimePACBayes (time-uniform Catoni — №71) | заимствовать stitching-технику при расширении |
| TorchLean | spec→exec→verify, CROWN/IBP | Model/CertifiedTransition (execution cert), Energy/Quantizer | принцип: связать вычисление с сертификатом |
| LeanAgent | continual learning, forgetting | Unified/MemoryCycle, Growth/GrowthDynamics | идеи консолидации памяти |
| ArtificialTheorems | SGD conv., Robbins-Siegmund, spec/proof split | Optimization/RobbinsMonro, Examples/QuadraticEndToEnd | паттерн разделения спецификации |
| Qwenputer (divagr18) | exact CPU in weights, GDN RAM, frozen non-learned layers | Model/RVCore, Model/RVCoreBignum (carry brick), Model/GDNRAM, Step/CPUFreeze, Unified/NCTheorem, Unified/NCStepCert (NC inside certified_loop) | заимствовать бignum-композицию, инварианты GDN-адресации |
| Cartesia From-Tokens-to-Bytes I/II | byte-level H-Nets, multi-stage dynamic chunking, compression product | Model/HNet, Model/HNet2 (two-stage product + beats-dense), Data/BytePatch, Model/AdaptiveChunking | формализовать packing-инварианты и in-context tokenization |
| LeanForControl | Lyapunov, устойчивость | Foundations/PerronCone, Growth/*, Unified/StepContract | сопоставление конусов Ляпунова |
| lean4-mlir (brettkoonce) | Lean-spec → MLIR/StableHLO → GPU; backward = Jacobian-transpose по ℝ, 0 проектных аксиом; TRUST.md-модель доверия | Model/ReferenceMachine + Model/MachineBridge (n-мерный end-to-end мост машина↔состояние); AssumptionScan | будущий нижайзер эталонной машины: ReferenceMachine как spec, их верифицированный путь как исполнение с доверенным ℝ→Float32 барьером |

## Рабочие мосты (theorem-level, `Hagi/Unified/LinkedProjects.lean`)

Package-level интеграция невозможна
(тулчейны 4.27/4.32 vs наш 4.35 + локальный
Mathlib-pin); связь — на уровне теорем:

- **ArtificialTheorems RL/ValueIterationComplete** →
  `value_iteration_via_contraction`: точная и
  приближённая value iteration — частный
  случай единого ядра
  `inexact_contraction_bound` (‖V_k − V*‖ ≤ γ^k·‖V_0 − V*‖ +
  ε(1−γ^k)/(1−γ)); их SGD/Robbins–Siegmund соседствует с
  Optimization/RobbinsMonro и Unified/RateTheory.
- **FormalSLT** anytime-PAC-Bayes master e-processes: наш
  слой сегодня — один master
  (AnytimeMartingale/AnytimePACBayes/Freedman*); их countable
  master над каталогом стратегий — кандидат в
  расширение (stitching-техника).
- **TorchLean** spec→exec→verify: наш аналог исполнительного
  слоя — ReferenceMachine/MachineBridge; принцип
  «одно определение и учится, и
  доказывается» — целевой формат для
  StageSemantics (исполняемые эффекты стадий).

Полный обзор: см. такт №228 STATUS.md; уникальность HAGI —
объединённая теория сертифицированного адаптивного обучения.
