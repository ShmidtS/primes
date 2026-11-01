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

Полный обзор: см. такт №228 STATUS.md; уникальность HAGI —
объединённая теория сертифицированного адаптивного обучения.
