# C537 — Карта внешнего плана оптимизации HAGI_v2 → primes

Дата: 2026-11-21. HEAD 53bc284 (C536). Только анализ, без реализации.
Все статусы проверены `rg` по кодовой базе (не по памяти).

## Сводная таблица

| Пункт | primes-статус (теорема/файл) | Новый формализуемый объект | Сложность | Ранг |
|---|---|---|---|---|
| P1 EB-bound (Freedman/Empirical-Bernstein) | Частично: Freedman-канон есть — `Hagi/Probability/Freedman.lean` (`freedman_tail_low`, `freedman_confidence`, `finite_freedman`, `adaptive_success_freedman`); EB упомянут только как план в `Hagi/Unified/LinkedProjects.lean` (стр. 29) — теоремы EB НЕТ | `empirical_bernstein_bound`: ε_EB = √(2σ̂²ln(3/α)/n) + 3R·ln(3/α)/(n−1); переиспользует `freedman_mgf` + `cond_var_le_second` | med | 2 |
| P2 SVD-INT8+AWQ+FWHT+Lloyd-Max | Частично: `Hagi/Core/Hadamard.lean` (Sylvester/FWHT ортогональность: `sylvester_mul_transpose`, `hadamardReal_mul_transpose`), `Hagi/Theory/MergeQuant.lean` (`fisher_quant_loss_bound`, `quad_fisher_quant_bound`, `fisher_beats_lipschitz`), SVD-ядро `Hagi/External/Flywheel/SVD*.lean` | Lloyd-Max оптимальность скалярного квантователя при g=64 (stationarity + MSE-оптимальность в классе) | med-high | 5 |
| P3 Polar-Express Minimax Newton-Schulz | Нет NS-итерации (rg `newton|schulz` в Optimization — пусто); полярная декомпозиция упоминается только структурно в `Hagi/External/Flywheel/SVDCore.lean` (P=√(AᴴA)) | Interval-сертификат 3-шаговых minimax-коэффициентов: если коэф. ∈ боксов и ‖X‖≤c, то ‖X₊−U‖ ≤ bound (по индукции + Lipschitz полинома) | med | 6 |
| P4 GPM + weight-decay LEAK | Сильно покрыто: `Hagi/Theory/Continual.lean` (`gpm_multi_step_invariant`, `gpm_multi_zero_forgetting`, `gpm_hold_when_covered`, `proj_compl_orth`, `gpm_tradeoff`, `rank_trunc_forgetting_bound`), `Hagi/Learning/ContinualForgetting.lean` (`continual_forgetting_bound`), EF21: `Hagi/Optimization/EF21Quantizer.lean` (`ef21_pl_linear_rate`, `ef21_inexact_descent`). WD-проекция НЕ формализована (rg `weightDecay|wd_leak` — пусто) | **wd_leak_theorem**: непроецируемый wd (шаг −λW имеет компоненту в защищённом подпространстве P‖ ≠ 0 ⇒ leak растёт), проецируемый (P⊥-проекция шага) ⇒ сохранение `gpm_multi_zero_forgetting`; склейка с `ef21_update_norm_le` для wd+EF21 в P⊥ | med | 1 |
| P5 Coherence 3-Leaf TIES | Частично: `Hagi/Theory/Statistics.lean`, `Hagi/Theory/BlockAdmission.lean`, `Hagi/Ensemble/MergePrice.lean`; нелинейный merge: `Hagi/Theory/MergeQuant.lean` (`nonlinear_merge_bound`, `quad_merge_exact`) | Row-Norm Disjoint TIES: sign-majority + row-norm веса — сохранение консенсуса при disjoint-поддержках; U-кривая по H_leaf — только на дискретной модели | med | 7 |
| P6 Anytime VOI scheduler | Частично: `Hagi/Theory/FullPipeline.lean` (`full_pipeline_sound`, `full_pipeline_stop_never_commits`), `Hagi/Theory/SelfEdit.lean` (adopt-gates: `adopt_chain_terminates`, `noop_not_adopted`), `Hagi/Theory/AnytimeHoldoutStop.lean`. Hash-consing/OE-полноты НЕТ (rg `hash.?cons|optimistic` — пусто) | **OE-completeness**: hash-consing + optimistic exploration не теряют решения — дискретная теорема о покрытии графа поиска (инъективность хеша на канонических формах ⇒ дедупликация сохраняет достижимость) | med | 3 |
| P7 Энтропийный байтовый патчинг | Сильно покрыто: `Hagi/Data/BytePatch.lean` (`patch_cover`, `patch_le_raw`, `patch_attn_saving`, `patchSeq_total_length`); multi-scale causal exp-каналов НЕТ (rg пусто) | exp-каналы O(T·K·D): разложение каузальной экспоненциальной памяти в K каналов — telescoping-тождество сложности | med | 8 |
| P8 Символьный bypass PROVEN_EXACT | Частично: `Hagi/Unified/DerivAlong.lean` (лог-линейная производная), `Hagi/Model/CECoupledShortcut.lean` (CE-шорткаты). Прямой «CE=0 на покрытых позициях» НЕТ | **zero_ce_on_exact**: детерминированное покрытие (модель = символическая формула на множестве позиций) ⇒ CE=0 на покрытии; мост к вероятностной семантике (P=1 ⇒ −ln P = 0) | low-med | 4 |

## Топ-4 по ценности/стоимости (цель: max качество, min объём, min вычисления)

1. **P4 wd_leak_theorem** — наибольшая ценность: закрывает единственный
   пробел в единственной полностью формализованной семье (Continual);
   переиспользует `gpm_multi_zero_forgetting` + `proj_compl_orth`;
   внешний план подтверждает экспериментально (leak 5.68e-15 vs 1.945),
   т.е. теорема имеет однозначную эмпирическую калибровку.
2. **P1 empirical_bernstein_bound** — дополнение к Freedman-канону
   (C525); замечание о EB уже в `LinkedProjects.lean` как признанный
   пробел. 27–48× экономия валидации = сильный bridge-аргумент.
3. **P6 OE-completeness (hash-consing)** — чисто дискретная теорема,
   низкий риск, новый класс результатов (поисковая полнота) в primes.
4. **P8 zero_ce_on_exact** — самый дешёвый (low-med); прямая опора на
   `DerivAlong`/`CECoupledShortcut`; формализует «бесплатный» −33% FLOP
   как корректность (log-loss=0 на покрытии).

Не вошли: P3 (med, ценность ниже — сертификат коэффициентов без
методологической новизны для primes), P2/P5/P7 (в основном эмпирики
архитектуры; формализуемые осколки — Lloyd-Max, TIES-сохранение,
exp-каналы — дороже и слабее связаны с каноном).

## Honest «не формализуемо осмысленно»

- P2 численные dB-результаты (15.13 vs 13.95 dB), AWQ-RMS калибровка,
  выбор r=8/g=64 — архитектурные эмпирики; формализуется только
  структурная часть (уже есть Hadamard/Fisher/SVD).
- P3 −40% FLOP и CosSim 0.99339 — измерения; коэффициенты Newton-Schulz
  найдены численной минимизацией (сертификат возможен, но это
  interval-arithmetic работа, не анализ).
- P5 U-кривая H_leaf*=8 — эмпирика конкретных моделей.
- P6 80/86 vs 25 — бенчмарк-числа.

## Port-proposal мосты (прецедент C466, docs/PROPOSAL-*.md)

- P1 → `PROPOSAL-empirical-bernstein.md` (дополнение Freedman-канона;
  внешнему агенту нужен: формулировка ε_EB + план через `freedman_mgf`).
- P4 → `PROPOSAL-wd-leak.md` (наивысший приоритет; формулировки leak/
  projected-wd поверх существующих Continual типов).
- P6 → `PROPOSAL-oe-completeness.md` (новый модуль, дискретный).
- P8 → `PROPOSAL-zero-ce-exact.md` (мост P=1, расширяет
  CECoupledShortcut).

P2/P3/P5/P7 port-proposals не рекомендуются (эмпирики / interval-работа
вне ядра канона).
