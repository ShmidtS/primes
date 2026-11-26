# RELATED — соответствие HAGI внешним Lean-проектам (обзор 2026-10)

Топ приоритетов исследования + соответствие файлов HAGI.

| Проект | Фокус | Соответствие в HAGI | Действие |
|---|---|---|---|
| [FormalSLT](https://github.com/Robby955/FormalSLT) ([Reservoir](https://reservoir.lean-lang.org/@Robby955/formal-slt)) | finite-sample learning theory, confidence sequences, e-processes | Unified/AnytimeMartingale (Ville, e-process), Unified/StitchingEProcess (конечное сшивание master e-processes), Theory/Statistics (time-uniform Catoni `anytime_catoni`) | сшивание доказано; заимствовать счётную технику при необходимости, без подмены monitoring-risk гарантией остановки |
| [TorchLean](https://github.com/lean-dojo/TorchLean) | spec→exec→verify, FloatLib/ATen trust boundaries, CROWN/IBP | Model/CertifiedTransition (execution cert), Energy/Quantizer | связать вычисление с сертификатом; внешнее GPU-исполнение не считать Lean-доказательством |
| LeanAgent | continual learning, forgetting | State/MemoryCycle | идеи консолидации памяти |
| ArtificialTheorems | SGD conv., Robbins-Siegmund, spec/proof split | Optimization/RobbinsMonro, Benchmarks/QuadraticEndToEnd | паттерн разделения спецификации |
| [Qwenputer](https://github.com/divagr18/Qwenputer) | exact CPU in weights, GDN state as memory, frozen computed layers | Model/RVCore, Model/GDNBridge, Model/NeuralComputer, Step/CPUFreeze, Unified/NCStepCert (NC внутри certified_loop) | заимствовать bignum-композицию и инварианты GDN-адресации; не приписывать HAGI внешние benchmark-результаты |
| Cartesia From-Tokens-to-Bytes I/II | byte-level H-Nets, multi-stage dynamic chunking, compression product | Model/HNet, Model/HNet2 (two-stage product + beats-dense), Data/BytePatch, Model/AdaptiveChunking | формализовать packing-инварианты и in-context tokenization |
| LeanForControl | Lyapunov, устойчивость | Growth/LinearCone (PerronCone, ConeDynamics, GrowthDynamics), Unified/StepContract | сопоставление конусов Ляпунова |
| lean4-mlir (brettkoonce) | Lean-spec → MLIR/StableHLO → GPU; backward = Jacobian-transpose по ℝ, 0 проектных аксиом; TRUST.md-модель доверия | Model/ReferenceMachine + Model/MachineBridge (n-мерный end-to-end мост машина↔состояние); AssumptionScan | будущий нижайзер эталонной машины: ReferenceMachine как spec, их верифицированный путь как исполнение с доверенным ℝ→Float32 барьером |

## Рабочие мосты (theorem-level, `Hagi/Unified/LinkedProjects.lean`)

Package-level интеграция в эти доказательства не добавлена: у внешних
проектов другие toolchain/pin (FormalSLT, например, указывает Lean
4.32.2, HAGI — Lean 4.36.0 и локальный Mathlib-pin). Связь — только на
уровне теорем и локальных адаптеров, не executive-compatibility claim.

- **ArtificialTheorems RL/ValueIterationComplete** →
  `value_iteration_via_contraction`: точная и приближённая value
  iteration — частный случай единого ядра
  `inexact_contraction_bound` (‖V_k − V*‖ ≤ γ^k·‖V_0 − V*‖ +
  ε(1−γ^k)/(1−γ)); их SGD/Robbins–Siegmund соседствует с
  Optimization/RobbinsMonro и Unified/RateTheory.
- **FormalSLT** anytime-PAC-Bayes master e-processes: конечное
  сшивание доказано (Unified/StitchingEProcess: master
  Σ wᵏ•Eᵏ над конечным семейством с priors Σ ≤ 1 — Ville
  time-uniform контроль). Остающийся gap: счётный master над
  каталогом стратегий (tsum-замыкание) и конструкции per-strategy
  e-processes.
- **TorchLean** spec→exec→verify: аналог исполнительного слоя —
  ReferenceMachine/MachineBridge; принцип «одно определение и
  учится, и доказывается» — целевой формат для StageSemantics
  (исполняемые эффекты стадий). Внешний LibTorch/CUDA backend
  остаётся trust boundary по документации самого TorchLean.

Ссылки FormalSLT, TorchLean, Qwenputer проверены через
Reservoir/GitHub API. Позиционирование HAGI — объединённая теория
сертифицированного адаптивного обучения с явными trust boundaries;
это не заявка на доказанную уникальность или универсальную
оптимальность модели.
