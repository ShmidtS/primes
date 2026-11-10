# RELATED — соответствие HAGI внешним Lean-проектам (обзор 2026-10; проверка ссылок C200)

Топ-5 приоритетов исследования + соответствие файлов HAGI.

| Проект | Фокус | Соответствие в HAGI | Действие |
|---|---|---|---|
| [FormalSLT](https://github.com/Robby955/FormalSLT) ([Reservoir](https://reservoir.lean-lang.org/@Robby955/formal-slt)) | finite-sample learning theory, confidence sequences, e-processes | Unified/AnytimeMartingale (Ville, e-process), Unified/AnytimePACBayes (time-uniform Catoni — №71) | заимствовать stitching-технику при расширении, без подмены monitoring-risk гарантией остановки |
| [TorchLean](https://github.com/lean-dojo/TorchLean) | spec→exec→verify, FloatLib/ATen trust boundaries, CROWN/IBP | Model/CertifiedTransition (execution cert), Energy/Quantizer | принцип: связать вычисление с сертификатом; внешнее GPU-исполнение не считать Lean-доказательством |
| LeanAgent | continual learning, forgetting | Unified/MemoryCycle, Foundations/GrowthDynamics | идеи консолидации памяти |
| ArtificialTheorems | SGD conv., Robbins-Siegmund, spec/proof split | Optimization/RobbinsMonro, Examples/QuadraticEndToEnd | паттерн разделения спецификации |
| [Qwenputer](https://github.com/divagr18/Qwenputer) | exact CPU in weights, GDN state as memory, frozen computed layers | Model/RVCore, Model/GDNBridge, Model/NeuralComputer, Step/CPUFreeze, Unified/NCStepCert (NC inside certified_loop) | заимствовать bignum-композицию и инварианты GDN-адресации; не приписывать HAGI внешние benchmark-результаты |
| Cartesia From-Tokens-to-Bytes I/II | byte-level H-Nets, multi-stage dynamic chunking, compression product | Model/HNet, Model/HNet2 (two-stage product + beats-dense), Data/BytePatch, Model/AdaptiveChunking | формализовать packing-инварианты и in-context tokenization |
| LeanForControl | Lyapunov, устойчивость | Foundations/PerronCone, Growth/ConeDynamics, Unified/StepContract | сопоставление конусов Ляпунова |
| lean4-mlir (brettkoonce) | Lean-spec → MLIR/StableHLO → GPU; backward = Jacobian-transpose по ℝ, 0 проектных аксиом; TRUST.md-модель доверия | Model/ReferenceMachine + Model/MachineBridge (n-мерный end-to-end мост машина↔состояние); AssumptionScan | будущий нижайзер эталонной машины: ReferenceMachine как spec, их верифицированный путь как исполнение с доверенным ℝ→Float32 барьером |

## Рабочие мосты (theorem-level, `Hagi/Unified/LinkedProjects.lean`)

Package-level интеграция в эти доказательства не добавлена
(у внешних проектов другие toolchain/pin; FormalSLT, например,
указывает Lean 4.32.2, а HAGI — Lean 4.35.0 и локальный
Mathlib-pin); связь — только на уровне теорем и локальных
адаптеров, не executive-compatibility claim:

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
  Внешний LibTorch/CUDA backend остаётся trust boundary по
  документации самого TorchLean.

Ссылки по текущему изменению документации проверены через Reservoir/GitHub API:
`Robby955/FormalSLT`, `lean-dojo/TorchLean`, `divagr18/Qwenputer`.
Полный обзор: см. такт №228 STATUS.md. Позиционирование HAGI —
объединённая теория сертифицированного адаптивного обучения с явными
trust boundaries; это не заявка на доказанную уникальность или
универсальную оптимальность модели.
