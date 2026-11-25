# DERIVED-CONFIG v2 — выводимая конфигурация обучения (C683–C687)

PROPOSAL-уровень: код HAGI_v2 не менялся. Факты кода — `hagi/` @ca52eb4
(только чтение). Lean-сборка — `Hagi/Theory/DerivedConfig.lean`
(`TrainingConfig`, `optimalConfig`, `optimalConfig_spec`).
Расчёт — `python scripts/derive_config.py` (stdlib, детерминированный;
вывод ниже без правки). C684: константы `L` для relu-блока по `W1` —
`Hagi/Theory/FirstLayerLip.lean` (Lipschitz `Lfun`, гладкость `S`). C685:
батч-версия `Hagi/Theory/FirstLayerLipBatch.lean` (`S_batch`, mean-форма кода).
v2 (C687): derived from `hagi_master_v35`
(Hagi/Theory/MasterTheoremV3.lean:458) — единая теорема = клозы (1)–(14)
машины + оптимизаторный блок (O7) ∧ (O1)–(O6), где (O7) — сам контракт
посылок `OptimizerPremises` (Hagi/Theory/MasterTheoremV3.lean:428).
Кредо: число появляется только если оно
(a) доказано в Lean, (b) вывод скрипта из констант кода @sha,
(c) receipt бенча; иначе — `HONEST-GAP` с причиной.

## 1. Дерево вывода

Статусы: **DERIVED** — формула из теоремы + число на входах кода;
**BOUNDED** — теорема даёт интервал/неравенство, код внутри или
число — из receipt; **HONEST-GAP** — не выводится (указано, чего не хватает).

| Группа | Параметр | Теорема (FQN, якорь) | Статус |
|---|---|---|---|
| Шаг | γ* = 1/L, drop = G²/(2L) | `Hagi.Theory.NegativeTransfer.nl_drop_optimal`, NegativeTransfer.lean:481; максимум — `nlDrop_le_optimal`, NegativeTransfer.lean:467 | DERIVED (γ_auto = 1/(2·trH̄), receipt C609); Adam lr — HONEST-GAP-число: для relu-блока по `W1` гладкость `S = ‖wo‖_F²·‖x‖₂²` ДОКАЗАНА (C684, `w1CE_descent_lemma`), но код не логирует `‖wo‖_F`, `‖x‖₂` и Adam-шаг нормирован (не `1/S·∇`) |
| Шаг (W1) | S = ‖wo‖_F²·‖x‖₂²; Lfun = 2·‖wo‖_F·‖x‖₂ | `Hagi.Theory.FirstLayerLip.w1CE_descent_lemma`, FirstLayerLip.lean:258; `w1CE_optimal_step_drop`, FirstLayerLip.lean:392; `w1CE_lipschitz_param`, FirstLayerLip.lean:182 | DERIVED-формула (witness 35, 1/35) / HONEST-GAP-число кода (‖wo‖, ‖x‖ не логируются) |
| Шаг (W1, батч) | S_batch = ‖wo‖_F²·Σ_t‖x t‖₂²; mean: S_batch/B | `Hagi.Theory.FirstLayerLipBatch.w1BatchCE_descent_lemma`, FirstLayerLipBatch.lean:113; `w1BatchCE_optimal_step_drop`, FirstLayerLipBatch.lean:218; `w1MeanCE_optimal_step_drop`, FirstLayerLipBatch.lean:247 | DERIVED-формула (witness 49, 1/49; mean 2/49) / HONEST-GAP-число до телеметрии PROPOSAL #11 |
| Направление / момент (Muon) | вдоль любого `d`: γ* = a/(L‖d‖²), drop a²/(2L‖d‖²), `a = ⟨G,d⟩`; момент: `⟨G,m1⟩ = 0.15‖G‖² + 0.85⟨G,m1_prev⟩`; Muon с моментом: `⟨G,X₃⟩ ≥ ‖m1‖_F − ‖G−m1‖_F‖X₃‖_F` | `Hagi.Theory.MomentumAlign.dir_drop_optimal`, MomentumAlign.lean:112; `w1BatchCE_dir_optimal_step_drop`, MomentumAlign.lean:261; `momentum_align`, MomentumAlign.lean:140; `muon_momentum_bound`, MomentumAlign.lean:419 | BOUNDED (формулы; числа — из телеметрии PROPOSAL-muon-guards (e)); значение 0.85 — HONEST-GAP |
| Шаг (certified) | L_dir = denom (кривизна направления) | `Hagi.Theory.AdaptiveMajorizer.ce_range_code_drop`, AdaptiveMajorizer.lean:1497; `ce_adaptive_code_drop`, AdaptiveMajorizer.lean:1473 | DERIVED: `denom = Q' + 4·curv_reg` (core.py:1314-1319) — код ИЗМЕРЯет L_dir, majorizer `η·A − η²·R²/8` |
| Шаг | η* = −4a/R², drop = 2a²/R² | `Hagi.Theory.FunctionPreservingGrowth.useful_first_step`, FunctionPreservingGrowth.lean:584 | DERIVED: код `eta = 4A/denom`, `cert_drop = 2A²/denom` (core.py:1320-1321, lm.py:861) — та же формула при d = −ḡ (a = −A, R² = denom) |
| Warm-up | COMMIT iff drop > 0 | `warmup_h1_of_certified_steps`, FunctionPreservingGrowth.lean:410 | BOUNDED: теорема требует drop > stepEps > 0; порог 1e-12 (core.py:1333) — любое положительное |
| Snap | k* = ⌈log₂(L·d/ε)⌉ − 1 | `Hagi.Theory.GrowSnap.snap_k_eq_ceil`, GrowSnap.lean:342; минимальность — `snap_k_min`, GrowSnap.lean:301 | DERIVED (числа — receipt C597; в коде @sha snap-грида нет) |
| Окно | w* = √(a/c), cost ≥ 2√(a·c) | `Hagi.Theory.WindowTradeoff.mixedCost_relax_min_eq`, CoverageReading.lean:648; `mixedCost_relax_min`, CoverageReading.lean:628; total ≥ 2n√(a·c) — `mixedCost_lower`, CoverageReading.lean:675 | DERIVED-формула / HONEST-GAP-число (a, c в коде не измеряются). Fixed-cost: бери w_max — `windowCost_fixed_mono`, CoverageReading.lean:575 |
| Growth | stay ⟺ bound ≤ c_add | `Hagi.Theory.GrowthGate.growth_gate_stay_char`, NegativeTransfer.lean:576 | DERIVED: c_add кода совпадает с формой теоремы; n и L — HONEST-GAP |
| Holdout | k ≥ ln(2N/δ)/(2(ε/B)²) | `holdout_gate_two_way_delta`, HoldoutGateTwoWay.lean:109 | BOUNDED: таблица 877/1199 не доказана в Lean (PROPOSAL 8) |
| LCB | P[ложный GROW] ≤ 2·exp(−2k(r/2B)²) | `paired_lcb_false_grow_bound`, NadyaOptimal.lean:270 | BOUNDED: r детерминированный в теореме, z·σ̂/√n в коде — случайная |
| Muon | σ₃ ≥ 39/40 при σ₀ ≥ 1/2 | `ns_sigma_min_three`, NewtonSchulzSigma.lean:126 | DERIVED (iters = 3, core.py:1755) |
| Cosine | 3/20 ≤ sched ≤ 1 | `cosine_sched_bounds`, NadyaOptimal.lean:143 | BOUNDED (описание, не оптимум): относится к schedule «Надя» (floor 0.15·lr₀); `train_minibatch` использует PyTorch-косинус с eta_min = 0 (lm.py:404) — другой schedule, floor не выводится |
| Batch | B² = Bn·t0/c | `amgm_equality`, Audit.lean:651 | HONEST-GAP-число: Bn, t0, c не измерены |
| Decay | (1−ηλ)-leak | `naive_decay_leak`, WeightDecayLeak.lean:126 | HONEST-GAP: значение λ не выводится |
| **v3.5 (O1)** | grad structure: `∇_{W1} CE = g ⊗ x` (rank one); батч: `D CE[Δ] = −⟨Σ_t g_t ⊗ x_t, Δ⟩` | `w1_grad_rank_one`, FirstLayerGrad.lean:123; `batch_directional_derivative`, BatchRankOne.lean:65 (оба в `hagi_master_v35`, MasterTheoremV3.lean:458) | DERIVED-формула (без посылок; код не логирует `g`, `x` по отдельности) |
| **v3.5 (O2)** | smooth step: γ* = 1/S_batch (сумма CE по батчу; mean — `B/S_batch`), drop = ‖D‖²/(2·S_batch); вдоль любого `d`: γ* = a/(L‖d‖²), drop a²/(2L‖d‖²) | `w1BatchCE_optimal_step_drop`, FirstLayerLipBatch.lean:218; `w1MeanCE_optimal_step_drop`, FirstLayerLipBatch.lean:247; `dir_drop_optimal`, MomentumAlign.lean:112 | DERIVED-формула / HONEST-GAP-число (посылки `S_batch > 0`, равные маски; код шага `1/S_batch` не делает) |
| **v3.5 (O3)** | Muon optimality: `⟨G, Δ⟩ ≤ Σσ` на изометриях (`ΔᵀΔ = 1`, `ΔΔᵀ = 1`), максимум достигается | `muon_step_optimal_in_isometry_group`, MuonIsometry.lean:175; `wide_step_optimal'`, WideSVD.lean:317 | DERIVED (теорема-факт шага кода `ns₃(Ĝ)`; не значение параметра) |
| **v3.5 (O4)** | NS approximation: σ₃ ≥ 39/40 при σ₀ ∈ [1/2, 1]; `⟨G, ns_k G⟩ = Σ σ i·ns_seq k (σ i)` | `ns_sigma_min_three`, NewtonSchulzSigma.lean:126; `muon_alignment_exact`, MuonAlignment.lean:104; `wide_alignment_exact'`, WideSVD.lean:306 | DERIVED (iters = 3, core.py:1755) |
| **v3.5 (O5)** | descent certificate: `∃ η > 0`, CE строго убывает после `W1 − η·ns_k(Ĝ)`, слой любой формы (батч и один вход) | `muon_step_useful_w1_rect_batch'`, MuonDescentW1Rect.lean:369; `muon_step_useful_w1_rect'`, MuonDescentW1Rect.lean:348 | BOUNDED (только `∃η`; величина `η` и `cos_lr·0.7` не связаны; посылки — вне kink, `G ≠ 0`) |
| **v3.5 (O6)** | momentum: `⟨G,m⟩ ≥ (1−μ)‖G‖² − μ‖G‖‖m_prev‖` всегда; `≥ ‖G‖²` при `⟨G,m_prev⟩ ≥ ‖G‖²`; Muon с моментом: `⟨G,Xₖ⟩ ≥ ‖m‖_F − ‖G−m‖_F‖Xₖ‖_F` | `momentum_align_cs`, MomentumAlign.lean:149; `momentum_align_ge_grad`, MomentumAlign.lean:179; `muon_momentum_bound`, MomentumAlign.lean:419 | BOUNDED (числа — телеметрия PROPOSAL-muon-guards (e)); μ = 0.85 — HONEST-GAP) |

Сборка: `Hagi.Theory.DerivedConfig.optimalConfig_spec` — γ, η, k*, w*
подставлены в теоремы выше без переформулировки (Freeze identity:
9218 → 9221, +3 декларации, аксиом ≤3). Holdout/LCB/cosine/Muon
в структуру не вошли: их теоремы не являются «значение-оптимум»
интервала/вероятности — подстановка потребовала бы новых statements.

Вторая сборка (v2, C687): `hagi_master_v35` (MasterTheoremV3.lean:458) —
(1)–(14) машины + (O7) ∧ (O1)–(O6) ОДНОЙ конъюнкцией ((O7) — контракт
`OptimizerPremises` как первая конъюнкта блока); посылки слоя — контрактом
`OptimizerPremises` (MasterTheoremV3.lean:428: `S_batch > 0`, равные
маски, вне kink, `G ≠ 0`), прочие — в точности посылки делегатов
(`d ≠ 0`, `0 ≤ μ`, `⟨grad z, m_prev⟩ ≥ ‖grad z‖²`, `card m ≤ card n`,
`σ ∈ [1/2, 1]`, `m ≠ 0`). Ноль новых доказательств, аксиом 3.

## 2. Рассчитанная таблица (вывод `scripts/derive_config.py`)

Обозначения кода: `ATA/TGC` — три машины receipt C609; `A = ‖ḡ‖²`,
`denom` — кривизна направления (core.py:1314-1319). Строки `witness`
(C684) — числа на входах `.tmp/C684/traj.lean` (x = (1,2),
wo = [[1,0],[0,2],[1,1]]), НЕ на коде: код не логирует `‖wo‖_F`, `‖x‖₂`.
Строки `batch` (C685) — два входа x₁ = (1,2), x₂ = (1,1), `B = 2`
(`.tmp/C685/traj.lean`): S_batch = 7·(5+2) = 49, γ*_batch = 1/49,
γ*_mean = 2/49.

|---|---|---|---|---|---|
| γ (guarded Adam lr) | 0.003 | γ* = 1/S_batch (mean: B/S_batch), S_batch = ‖wo‖_F²·Σ_t‖x t‖₂² — FirstLayerLipBatch; DERIVED-формула; число — HONEST-GAP до телеметрии PROPOSAL #11 | — | HONEST-GAP | w1BatchCE_optimal_step_drop FirstLayerLipBatch.lean:218; nl_drop_optimal NegativeTransfer.lean:481 |
| S (W1 smoothness) witness | — | 7·5 = 35 | — | BOUNDED | w1CE_descent_lemma FirstLayerLip.lean:258 (witness, не код) |
| γ* = 1/S witness (W1, plain GD) | — | 1/35 = 0.0286 | — | BOUNDED | w1CE_optimal_step_drop :392 (witness, не код) |
| γ (guarded Adam lr), batch form | 0.003 | γ* = 1/S_batch (mean: B/S_batch) = 0.0204 (mean 0.0408); witness, не код | — | HONEST-GAP | w1MeanCE_optimal_step_drop FirstLayerLipBatch.lean:247; PROPOSAL-smoothness-logging (#11) |
| S_batch (W1 smoothness, batch) witness | — | 7·(5+2) = 49 ≤ B·7·max = 70 | — | BOUNDED | w1BatchCE_descent_lemma FirstLayerLipBatch.lean:113; S_batch_le_max :86 (witness) |
| γ*_batch / γ*_mean witness | — | 1/49 = 0.0204; B/S_batch = 0.0408 | — | BOUNDED | w1BatchCE_optimal_step_drop :218; w1MeanCE_optimal_step_drop :247 (witness) |
| Lfun (W1 Lipschitz) witness | — | 2·√7·√5 = 11.8322 | — | BOUNDED | w1CE_lipschitz_param :182 (функция, не градиент; witness) |
| L_dir certified step (denom) | Q' + 4·curv_reg | R² = denom: код ИЗМЕРЯЕТ (core.py:1314-1319) | — | DERIVED | ce_range_code_drop AdaptiveMajorizer.lean:1497; useful_first_step :584 |
| γ_auto ATA (ATA/TGC) | 0.4775 | 1/(2·trH̄)=5000000/10470759 | — | DERIVED | auto-LR 1/(2·trace H̄), receipt C609 |
| γ_auto TGC (ATA/TGC) | 0.5203 | 1/(2·trH̄)=13500000/25944901 | — | DERIVED | auto-LR 1/(2·trace H̄), receipt C609 |
| γ_auto TGC' (ATA/TGC) | 0.6671 | 1/(2·trH̄)=156250/234227 | — | DERIVED | auto-LR 1/(2·trace H̄), receipt C609 |
| L implied by γ_auto | — | 4.188/3.844/2.998 | — | DERIVED | L = 2·trH̄ = 1/γ_auto |
| η certified step | 4A/denom | −4a/R² = 4A/denom | 1 | DERIVED | useful_first_step FunctionPreservingGrowth.lean:584 |
| drop certified step | 2A²/denom | 2a²/R² | 1 | DERIVED | useful_first_step :584 (R² = denom) |
| witness R=2, a=−1/2: η* | — | 1.0 | — | DERIVED | useful_first_step (R=2) |
| COMMIT threshold | 1e-12 | >0 (строго) | — | BOUNDED | warmup_h1_of_certified_steps FunctionPreservingGrowth.lean:410 |
| backtrack β / probes | 0.5 / 13 | β, probes: не формализованы | — | HONEST-GAP | — |
| snap k* | нет snap-грида | ⌈log₂(L·d/ε)⌉−1 | — | DERIVED | snap_k_eq_ceil GrowSnap.lean:342 |
| snap k* bench (C597): код legacy / auto | 40 | 18/19/20 | — | DERIVED | receipt C597 (paper-draft.md:1332) |
|   k* при L·d/ε = 2^5 | — | 4.0 | — | DERIVED | snap_k_eq_ceil |
|   k* при L·d/ε = 2^9 | — | 8.0 | — | DERIVED | snap_k_eq_ceil |
|   k* при L·d/ε = 2^17 | — | 16.0 | — | DERIVED | snap_k_eq_ceil |
|   k* при L·d/ε = 2^21 | — | 20.0 | — | DERIVED | snap_k_eq_ceil |
| bits saved vs legacy (33 snaps) | — | 2788 | — | DERIVED | receipt C597 |
| coverage w | max 16 (tol 0.01) | √(a/c); a, c в коде не измеряются | — | HONEST-GAP | mixedCost_relax_min_eq CoverageReading.lean:648 |
| w bench (n=100000, fixed cost) | 16 | 256 → 391 reads | 0.0625 | BOUNDED | windowCost_fixed_mono CoverageReading.lean:575; receipt C623 |
|   reads(16)/reads(256) | 6250 | 391 | 15.98 | DERIVED | receipt C623 |
| growth c_add | 10·(d·h+h²)/N | 2.1357 (N=115072, no blocks) | — | DERIVED | growth_gate_stay_char NegativeTransfer.lean:576 |
| growth probe n | 128 | n·G²/(2L): n не формализовано | — | HONEST-GAP | growth_gate_stay_char :576 |
| growth L | CE loss (unified.py:400) | Lipschitz-константа majorizer | — | HONEST-GAP | nl_drop_optimal :481 |
| holdout k (N=2, δ=0.05, ε=0.05B) | max(256, 2%·n) | 877 | — | BOUNDED | holdout_gate_two_way_delta HoldoutGateTwoWay.lean:109; таблица не доказана (PROPOSAL 8) |
| holdout k (N=10, δ=0.05, ε=0.05B) | max(256, 2%·n) | 1199 | — | BOUNDED | holdout_gate_two_way_delta HoldoutGateTwoWay.lean:109; таблица не доказана (PROPOSAL 8) |
|   n windows needed for k≥1199 @2% | — | 59950 | — | DERIVED | 1199/0.02 |
| P[false GROW] bound, z=1.5, σ̂=B/2, n=256 | n=256 | ≤1.5097 (vacuous: >1) | — | BOUNDED | paired_lcb_false_grow_bound NadyaOptimal.lean:270 |
| P[false GROW] bound, z=2.4, σ̂=B/2, n=256 | n=256 | ≤0.9735 (vacuous: >1) | — | BOUNDED | paired_lcb_false_grow_bound NadyaOptimal.lean:270 |
| P[false GROW] bound, z=2.4, σ̂=0.05B, n=256 | n=256 | ≤0.3166 | — | BOUNDED | paired_lcb_false_grow_bound NadyaOptimal.lean:270 |
| LCB n for P≤0.05 (z=2.4, σ̂=0.05B) | 256 | 513 | 0.499 | DERIVED | paired_lcb_false_grow_bound :270 |
| σ₃(σ₀) table | iters=3 | 0.1:0.3284, 0.3:0.8045, 0.5:0.9753, 0.7:0.9993, 0.9:1.0000, 1.0:1.0000 | — | DERIVED | ns_sigma_min_three NewtonSchulzSigma.lean:126 (σ₀≥½ ⇒ ≥39/40) |
| σ₃(1) bound | — | 0.9750 ≤ 1.0000 | — | DERIVED | ns_sigma_min_three :126 |
| Muon effective step (t=1) | 0.04·sched·0.7 | 0.02800 | — | DERIVED | step = cos_lr·0.7·X₃ (core.py:1755) |
| Muon momentum alignment | m1 = 0.85·m1 + 0.15·gW1 | ⟨G,m1⟩ = 0.15·‖G‖² + 0.85·⟨G,m1_prev⟩ ≥ 0.15·‖G‖² (если ⟨G,m1_prev⟩ ≥ 0) | — | BOUNDED | momentum_align, momentum_align_ge MomentumAlign.lean:140/:169 |
| Muon momentum half-residual | ‖G−m1‖_F·‖X₃‖_F | ≤ ‖m1‖_F/2 ⇒ ⟨G,X₃⟩ ≥ ‖G‖_F/3 (X₃ = ns₃(m1/‖m1‖_F)) | — | BOUNDED | muon_momentum_bound :419; muon_momentum_third :442 |
| Muon momentum | 0.85/0.15 | значение 0.85 не выводится | — | HONEST-GAP | momentum_align_cs MomentumAlign.lean:149 (⟨G,m⟩ ≥ (1−μ)‖G‖² − μ‖G‖‖m_prev‖) |
| sched(T) hybrid | 0.0 (eta_min=0) | 3/20 = 0.15 | — | BOUNDED | cosine_sched_bounds NadyaOptimal.lean:143 |
| sched(1)/sched(0) hybrid | 0.999969 | ≤1 | — | BOUNDED | cosine_sched_bounds :143 |
| sched(T) minibatch | 0.0 (eta_min=0) | 3/20 = 0.15 | — | BOUNDED | cosine_sched_bounds NadyaOptimal.lean:143 |
| sched(1)/sched(0) minibatch | 1.000000 | ≤1 | — | BOUNDED | cosine_sched_bounds :143 |
| Adam β₁/β₂/eps | 0.9/0.999/1e-08 | — | — | HONEST-GAP | теоремы нет |
| weight decay λ | 0.0002 | B²=Bn·t0/c → значение λ не выводится | — | HONEST-GAP | WeightDecayLeak.lean:126 (механизм, не значение) |
| batch B | 512 | B*=√(Bn·t0/c); Bn,t0,c не измерены | — | HONEST-GAP | amgm_equality Audit.lean:651 |
| steps / epochs | 3000/30 | — | — | HONEST-GAP | теоремы нет |
| k_ctx, dim, hidden, seed | 8/64/128/7 | — | — | HONEST-GAP | теоремы нет |
| init scale | 0.08 | — | — | HONEST-GAP | теоремы нет |
| LCB z | 2.4 | — | — | HONEST-GAP | z не выводится (r свободный параметр) |
| adapter min gain | 0.005 | — | — | HONEST-GAP | теоремы нет |
| ternary grid | 3 levels, row scale mean|W| | — | — | HONEST-GAP | теоремы оптимальности нет |

STATUS COUNTS: BOUNDED=18 DERIVED=22 HONEST-GAP=16


## 3. Расхождения кода с выведенным (top)

1. **Cosine floor.** Код: `cos_lr = lr0·½(1+cos(πt/T))` (core.py:1741),
   `CosineAnnealingLR` с `eta_min = 0` (lm.py:404) ⇒ sched(T) = 0;
   доказанный коридор — [3/20, 1] (`cosine_sched_bounds`). Код выходит
   ниже доказанного минимума; шаги в конце цикла не покрыты теоремой.
2. **Growth L.** Код подставляет значение CE-функции потерь в роль L
   (unified.py:400-405); теорема требует Lipschitz-константу majorizer
   (`nl_drop_optimal`). Пока L ≠ Lipschitz, `signal ≤ c_add` — не
   certified-stay. Квантификация: сигнал = n·G²/(2L) обратно пропорционален
   L; γ_auto-receipts дают L = 2.998–4.188 (1/γ_auto), код — L = CE.
   Знак вердикта при такой замене не выводится (HONEST-GAP).
   Уточнение C684: для relu-блока по `W1` липшицева константа функции
   `Lfun = 2·‖wo‖_F·‖x‖₂` и гладкость градиента `S = ‖wo‖_F²·‖x‖₂²` —
   доказанные формулы (`w1CE_lipschitz_param`, `w1CE_descent_lemma`),
   но код не логирует `‖wo‖_F`, `‖x‖₂`, а growth-гейт подставляет значение
   CE — другая величина; в роль `L` гейта годится `S`, не `Lfun`:
   `n·G²/(2L)` — из `nl_drop_optimal`, где `L` — гладкость.
3. **Holdout и LCB-размер пробы.** Код: `max(256, 2%·n)` окон (lm.py:391),
   growth-проба 128, old-domains 256. Выведено: holdout ≥ 1199 (N = 10)
   ⇒ нужно n ≥ 59950 окон при 2%, либо доля ≥ 1199/n; LCB-проба ≥ 513
   при σ̂ = 0.05B, z = 2.4 для P ≤ 0.05. Код в ≥ 2 раза ниже обеих границ.

Дополнительно (без доказанного «должно быть», только факт):
- Adam lr 3e-3 / 1e-3 против γ_auto 0.477–0.667 — разные объекты
  (Adam-шаг нормирован, γ — линейный); сравнение ratio не определено.
- Coverage: w-choices до 16 при бенче 256 (fixed-cost режим — бери w_max).

## 4. Honest: что НЕ выводится и почему

| Параметр | Причина |
|---|---|
| Adam lr (число) | γ* = 1/S_batch (mean: B/S_batch) доказана (C684–C685, v3.5 O2), но: Adam-шаг нормирован (`m̂/√v̂`), теорема — про `γ·∇`; код не логирует ‖wo‖_F², Σ_t‖x t‖₂² — до телеметрии PROPOSAL #11 |
| Adam β₁, β₂, eps | нет теоремы об оптимальности моментов/дисперсии в репозитории |
| Muon μ = 0.85 | выравнивание и граница drop доказаны (C686, MomentumAlign.lean); оптимальности значения μ нет, код не логирует ⟨G,m1⟩, ‖G−m1‖_F |
| weight decay λ | `naive_decay_leak` описывает механизм leak, не оптимальное λ |
| batch B | формула `amgm_equality` есть, входов Bn, t0, c в коде нет |
| steps / epochs, T_max | нет теоремы о длине цикла |
| k_ctx, dim, hidden, seed, init scale | нет теоремы о ёмкости/ширины |
| backtrack β, число проб | нет теоремы |
| Muon momentum 0.85 (значение), scale 0.7 | значения не выводятся; доказаны (v3.5 O4/O6): σ₃ ≥ 39/40, выравнивание ⟨G,m1⟩ (C686), граница через невязку; шаг кода `cos_lr·0.7` не связан с `∃η` теоремы O5 |
| LCB z | r — свободный параметр теоремы; z не выводится |
| adapter min gain, ternary grid | нет теоремы оптимальности |
| holdout k, LCB | таблица чисел не доказана (BOUNDED) |

### Что блокирует оставшиеся HONEST-GAP (v3.5)

| Параметр | Чего не хватает |
|---|---|
| Adam lr (число) | то и другое: теорема для нормированного Adam-шага (`m̂/√v̂`) + измерение в коде (`‖wo‖_F²`, `Σ_t‖x t‖₂²`, PROPOSAL #11) |
| cos_lr·0.7 ↔ γ* | то и другое: теорема (величина `η` в O5 — только `∃η`; связь с `1/S_batch` для шага Muon не доказана) + измерение (телеметрия `S_batch`, PROPOSAL-muon-guards (e)) |
| Muon μ = 0.85 | то и другое: теорема об оптимальности `μ` + измерение (`⟨G,m1⟩`, `‖G−m1‖_F` в коде) |
| Adam β₁, β₂, eps | теорема (оптимальность моментов/дисперсии) |
| Adam-направление (⟨g, d⟩ > 0 только на первом шаге, клоз (13)) | теорема (спуск после первого шага) |
| фон Нейман (максимум `⟨G, Δ⟩` по шару `‖Δ‖₂ ≤ 1`) | теорема (доказан максимум только на изометриях, O3) |
| kink (relu) | то и другое: теорема о шаге через kink + измерение (доля входов на kink) |
| малые σ (< 1/2) | теорема (после 3 итераций нет нижней границы; зависимость от `iters`) |
| weight decay λ | теорема (оптимальное `λ`) |
| batch B | то и другое: теорема (`amgm_equality` есть) + измерение (`Bn`, `t0`, `c`) |
| steps / epochs, T_max | теорема (длина цикла) |
| k_ctx, dim, hidden, seed, init scale | теорема (ёмкость/ширина) |
| backtrack β, число проб | теорема |
| LCB z | теорема (вывод `z`) |
| adapter min gain, ternary grid | теорема оптимальности |
| growth probe n | теорема (формализация `n`) |
| growth L (гейт) | измерение (в роли `L` гейта — `S`, не значение CE; `S` не логируется) + теорема-certified-stay при такой замене |
| coverage w | измерение (`a`, `c` в коде не измеряются) |

## 5. Ссылки

- STATUS.md: NegativeTransfer, GrowSnap, CoverageReading, NadyaOptimal,
  MuonDescentW1Rect (C668–C682), NewtonSchulzSigma, FirstLayerLipBatch (C685), MomentumAlign (C686: шаг вдоль направления, момент `m1`, Muon с моментом), MasterTheoremV3 (C687: `hagi_master_v35`, клозы O1–O6), FirstLayerLip (C684:
  `w1CE_lipschitz_param`, `w1CE_descent_lemma`, `w1CE_optimal_step_drop`).
- docs/paper-draft.md: таблица «доказано vs код» (receipts C597, C609, C623).
- docs/PROPOSAL-holdout-size.md (#8), docs/PROPOSAL-certified-warmup.md (#7),
  docs/PROPOSAL-muon-guards.md (#9), docs/PROPOSAL-smoothness-logging.md (#11).
