# RELATED — соответствие HAGI внешним Lean-проектам (обзор 2026-10)

Топ-5 приоритетов исследования + соответствие файлов HAGI.

| Проект | Фокус | Соответствие в HAGI | Действие |
|---|---|---|---|
| FormalSLT | time-uniform PAC-Bayes, confidence seq, e-processes | Unified/AnytimeMartingale (Ville, e-process), Unified/AnytimePACBayes (time-uniform Catoni — №71) | заимствовать stitching-технику при расширении |
| TorchLean | spec→exec→verify, CROWN/IBP | Model/CertifiedTransition (execution cert), Energy/Quantizer | принцип: связать вычисление с сертификатом |
| LeanAgent | continual learning, forgetting | Unified/MemoryCycle, Growth/GrowthDynamics | идеи консолидации памяти |
| ArtificialTheorems | SGD conv., Robbins-Siegmund, spec/proof split | Optimization/RobbinsMonro, Examples/QuadraticEndToEnd | паттерн разделения спецификации |
| LeanForControl | Lyapunov, устойчивость | Foundations/PerronCone, Growth/*, Unified/StepContract | сопоставление конусов Ляпунова |

Полный обзор: см. такт №228 STATUS.md; уникальность HAGI —
объединённая теория сертифицированного адаптивного обучения.
