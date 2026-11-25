# Era index — C591–C670 (2026-11-22/25)

Навигация по эрам: период | главные коммиты | доказанные
результаты | фронтир на конец эры. Per-beat-файлы
(`period-c*-analysis.md`, C244–C664) не tracked: история — `git log` /
`git show <sha>`; живой носитель — этот индекс и карточки STATUS. Имена —
по состоянию на HEAD (модули v7-слияний: `GrowthGate`,
`WindowTradeoff`, лестница `MasterTheoremV31..V33` →
`Hagi/Theory/{NegativeTransfer,CoverageReading,MasterTheoremV3}.lean`).
Числа freeze — рост только на новые Lean-декларации; docs-витки
— identity. Планы рефакторинга: `refactor-master-plan-v8.md` (этот
каталог); v7, v7-cycle2, cycle3-survey — `archive/`.

<a id="c591-c593"></a>
## C591–C593 — фронтир: certified-оптимумы параметров (freeze 8775→8803)

- Коммиты: 9d29c12e (integrity post-cleanup, bench dedup −57),
  8ee33d9e, 0e8c65e0.
- Доказано: `smooth_obj_transfer_bound` / `sufficient_negative_transfer`
  (L-smooth transfer — sufficient, не iff); `snap_k_eq_ceil`,
  `snap_k_min`, `snap_optimal_k`: k* = ⌈log₂(Ld/ε)⌉−1 —
  доказанный минимум бит-бюджета снапа.
- Фронтир: авто-k* в bench; certified-порог wave232-гейта
  (вместо proxy ce ≤ 0.5); метатеория-2.

<a id="c594-c598"></a>
## C594–C598 — техдолг + применение теории (freeze 8803→8807)

- Коммиты: a58554ec, 06b52134 (docs/PREMISES-STATUS.md), 8ff8787b
  (bench sweep: 13 PASS / 22 honest-ABORT / 0 traceback), 272a5593
  (auto snapK, −2788 бит / 33 snap), 1646cd02.
- Доказано: `covStarts_covers` (полный список стартов покрывает
  каждый байт); негатив `covStarts_trunc_uncovered_zero`
  (tail-усечение окон теряет байт 0).
- Фронтир: метатеория v3.1; certified transfer-гейт; span окон
  (код-импликация негатива).

<a id="c599-c602"></a>
## C599–C602 — консолидация: v3.1 + гейты + adaptive span (freeze 8807→8813)

- Коммиты: c26c0510, b6ca19e9 (`hagi_master_v31`, 8 клозов-
  делегатов, без новых доказательств), 5a1caff3 (двухуровневый
  transfer-гейт: quad-iff + smooth-sufficient), fa5ba08d.
- Доказано: `covStartsStep_covers` — покрытие ⇔ 0 < s ≤ w (iff);
  `covStartsStep_len_le`; `covStartsStep_adaptive_covers`.
- Фронтир: иерархия окон за границей n ≤ 4032 (INFEASIBLE);
  paper v0.6; h_emp-разрядки.

<a id="c606-c611"></a>
## C606–C611 — formula-driven: γ*, corpus-политика, иерархия (freeze 8814→8822)

- Коммиты: 9ac23393, 0da35ab7, d71a06bb (snapshot default),
  c60f69bf (auto_lr = 1/(2·tr H̄)), 76354a17 (трёхуровневый
  fallback), dd0e1ea2.
- Доказано: `nl_drop_bound`, `nl_drop_optimal`
  — γ* = 1/L, max drop G²/(2L) (полный квадрат); `hier_covers_any_n`
  — покрытие любого n без верхней границы; `hier_peak_window_budget`
  (peak ≠ total).
- Фронтир: применение иерархии в bench; метатеория v3.2; Card 9–11.

<a id="c612-c615"></a>
## C612–C615 — v3.2-канон (freeze 8822→8823)

- Коммиты: d1bea6a2, 819ae31f (`--mode generate-hier`, сверка с
  Lean #eval: n=8128 → [63,63,1]), 609726d1 (`hagi_master_v32`,
  10 клозов: v3.1 + γ* + hier), dff31052 (Card 9–11).
- Доказано: нового нет — только конъюнкция делегатов, аксиомы = 3.
- Фронтир: paper v0.7; оптимальность B; PARTIAL-разрядки.

<a id="c616-c619"></a>
## C616–C619 — зрелость: paper v0.7, floor, разрядки-раунд 2 (freeze 8823→8835)

- Коммиты: 5254f6e8, db2d3d2a (paper v0.7 §3.18/§4.6), 8ff07bd8,
  feb74d6b.
- Доказано: `hier_optimal` — total = ⌈n/w⌉, floor любого покрытия,
  константность по B (гипотеза B* = √(nw) опровергнута: 1563 при
  B ∈ {64,2048,4032,4096}); `lse_weighted_le`, `ensemble_ce_le_weighted`,
  `merge_energy_bridgeW` (точное равенство CE(mixture); ныне
  `Hagi/Research/Legacy/Nonvacuity.lean`).
- Фронтир: Card 12; адаптивный w; v3.3 клоз 11.

<a id="c620-c623"></a>
## C620–C623 — теория чтения: Card 12, v3.3, w-trade-off (freeze 8835→8841)

- Коммиты: 50319384, 0caca593 (Card 12), b127b605
  (`hagi_master_v33`, 11 клозов), 30e9a6ec.
- Доказано: `windowCost_linear_near_const` — при линейной цене
  окна total ≈ не зависит от w (зазор < c·w); fixed ⇒ w_max.
- Фронтир: Card 13; bench cost-regime; mixed w* (не-теорема).

<a id="c624-c626"></a>
## C624–C626 — чтение-эра закрыта внутренне (freeze 8841 identity)

- Коммиты: d3e0da84, c8715f3b (Card 13), 7d7ff186 (`--cost-regime
  {fixed,linear,mixed}`, python-двойник с fail-closed asserts).
- Доказано: нового нет (bench-виток без Lean-дерева).
- Фронтир: paper v0.8; mixed-w* в Lean; rank/adapter-ёмкость.

<a id="c627-c630"></a>
## C627–C630 — чтение-эра закрыта внешне (freeze 8841→8844)

- Коммиты: ef57c959, dd4102cf (mixed w* = (a/(c·(α−1)))^(1/α)),
  912f16c4 (paper v0.8), 83d80193 (Palomar recheck: 1298 results,
  0 пересечений по 13 карточкам).
- Доказано: `mixedCost_relax_min_eq`, `mixedCost_lower` (AM-GM);
  последний не-теоремный элемент серии стал certified.
- Фронтир: certified rank/adapter-ёмкость; memory-consolidation;
  publication gate (user).

<a id="c631-c633"></a>
## C631–C633 — открытие capacity-эры: growth-gate (freeze 8844→8849)

- Коммиты: 0286bfcd, 5cfdb759 (`GrowthGate.lean` +189), 1341c611
  (гейт перед каждым добавлением блока/адаптера в bench).
- Доказано: `growthGate`, `growth_gate_stay_char` (iff порога),
  `nl_drop_step_eq`/`nl_drop_total`, `growth_gate_sound` —
  certified-STAY: при n·G²/(2L) ≤ c_add рост не окупается.
  Honest pins: квадратичный класс; grow = разрешение, не обещание.
- Фронтир: негатив-контроль stay-ветки; калибровка c_add (λ);
  Card 14 — закрыты fbcaa5e0 / 606e899f.

<a id="c638-c640"></a>
## C638–C640 — эра «код HAGI_v2 → Lean-мосты» (freeze 8849→8869)

- Коммиты: 8999bdc8 (`AdaptiveMajorizer.lean` +352), 9fbca579
  (`BatchCEDescentMgdaCode.lean` +157), 38e0892b (карточка роста).
- Мосты кода: `ce_range_code_drop` (реальный сертификат шага;
  adaptive-ветка не берётся), `mgda_eq_of_stationary` (ε=0 точен,
  иначе 2ε), рост wave255 ⊂ `benchResidualBlock` / `identityBlock`.
- Фронтир: post-warm-up сертификат роста; Armijo-мост Adam
  backtracking; JVP-остаток range-ветки; per-task gate ↔ C601.

<a id="c642-c644"></a>
## C642–C644 — эра «сертификация роста» (freeze 8869→8887)

- Коммиты: eb399530 (C642 `FunctionPreservingGrowth.lean` +117), ad36e5bb
  (C643 `RollbackGate.lean` +58), 8de578e3 (C644 + `PROPOSAL-certified-warmup.md`).
- Доказано: `warmup_safe` (identity-старт + certified-шаги ⇒ obj ≤ fOld),
  `post_warmup_growth_safe` (любой вердикт rollback-гейта),
  `backtrack_accept_drop` (реальный предикат wave254, не Armijo),
  `CertifiedFiniteStep` ⇒ `warmup_h1_of_certified_steps`.
- Негативы: `uncertified_step_can_worsen`, `uncertified_step_not_certified`,
  `batch_drop_not_global`.
- Honest: в коде warm-up — голый Adam (h1 условна); certified-шаг пишет в
  trunk по batch-CE, не в блок; batch-drop не телескопирует в global.
- Фронтир: `certified_step_block`, телескоп batch→global, Adam EMA-лемма,
  paper v0.9, external push proposal.

<a id="c645-c646"></a>
## C645–C646 — certified-шаг на параметрах блока (freeze 8887→8891)

- Коммиты: 46a28709 (C645 разбор), C646 `FunctionPreservingGrowth.lean` (+4).
- Вердикт: range-лемма CE — на ЛОГИТАХ (`lse_shift_upper`), от θ-носителя
  не зависит ⇒ certified-шаг переносится на блок бесплатно.
- Доказано: `certified_step_block_of_range`, `block_step_certified_of_range_bound`,
  `block_step_commit_of_range_bound` ⇒ `warmup_h1_of_certified_steps` на блоке.
- Негатив: `block_range_bound_violated_not_certified`.
- Honest: range(Δz) через block-only JVP — реализация кода, не теорема.

<a id="c647"></a>
## C647 — телескоп batch→global (freeze 8891→8899)

- Коммит: C647 `Contracts/BatchGlobalTelescope.lean` (+6 theorem, +2 def).
- Вердикт: per-batch certified drop телескопирует только в batch-objective
  (`batch_telescope_fixed`/`fixedBatch_telescope`); глобальный objective
  контролируется вероятностно (`batch_drop_generalizes` через EB,
  `certified_batch_drop_global`) при iid-модели батча.
- Код (lm.py:978-1008 @ca52eb4): выборка без возвращения, 8 раундов
  перестановок по 32, любой d > 0 принимается — уровень (C), не (A)/(B).
- Honest: iid — идеализация; b/sig для EB код не считает; union bound по
  шагам не собран.

<a id="c648"></a>
## C648 — union bound по раундам (freeze 8899→8907)

- Коммит: C648 `Contracts/BatchGlobalTelescope.lean` (+5 theorem, +3 def).
- Вердикт: в модели независимых раундов (`roundP`) union bound
  (`rounds_union`, через `prodPq_union_finset`) + телескоп
  (`rounds_telescope`) ⇒ `certified_rounds_union`: P ≥ 1−α все раунды
  хорошие ⇒ obj k ≤ obj 0 − Σ dropB + k·ebGap(α/k).
- Honest: независимость раундов — гипотеза-модель (код зависим через θ);
  WOR-консервативность не формализована (Mathlib леммы нет); код не
  считает b/sig и не делит α по раундам.

<a id="c650-c651"></a>
## C650–C651 — paper v0.9; repair + archiver (freeze 8907→8921)

- Коммиты: 8fb0f1fa (C650 paper v0.9: 8 мостов (ныне §3.19), §4.8 таблица,
  pins 22–29, дрейф якорей lm.py:826→:831), b32a9003 (C651
  `RepairForgetting.lean` +114, WindowOrder +40).
- Доказано: `repair_sound` (z ≤ v − tol·a ∧ z ≤ v ∧ a ≤ r — линейно, ρ в
  коде нет); `slot_mono`, `slot_last`, `slotRev_first` (порядок, не
  цель). Не доказано: archiver (range coder в Lean нет, lossless = тесты);
  h1 warm-up; WOR; Adam EMA.
- Фронтир: archiver statement-кандидат (codelength ↔ CE/H; entropy-модуля
  в Mathlib нет); Adam EMA; certified-warmup-sim; target-смежность
  `_windows` (баг b3740e0).

<a id="c653-c655"></a>
## C653–C655 — эра «компрессия + Adam-вердикт» (freeze 8921→8948)

- Коммиты: 08405376 (C653 `Theory/ArchiverCodeLength.lean`), 0ccaa34f
  (C654 `scripts/bench_bridge.py` certified-warmup-sim, freeze identity),
  fbc8cfcd (C655 `Step/AdamDirection.lean`).
- Доказано: ideal coder — E_p[len] ≤ CE+1, CE = H+KL/log₂, p̂=p ⇒ H ≤
  E[len] ≤ H+1 (Kraft/McMillan); Adam first-step ⟨g,d⟩>0, sign-flip на
  шаге 2 (β=0.9) ⇒ не descent, `backtrackAccept` обязателен.
- Симуляция: 600 COMMIT/0 HOLD, obj 3.76→2.78, identity бит-в-бит; plain
  Adam тоже ↓ без сертификата.
- Honest: range-coder round-trip (≥400 строк), WOR, независимость
  раундов, block-only JVP, holdout-гейт, существование полезного блока.
- Фронтир: paper v1.0 candidate; Card 15–16 + PALOMAR recheck; полезный
  блок; holdout ↔ PAC-Bayes (носитель в primes есть); external push.

<a id="c657-c660"></a>
## C657–C660 — эра «release v1.0»: useful-first-step, holdout two-way (freeze 8948→8959)

- Коммиты: 65d9f11e (C657 useful first warmup step, U2 honest),
  4e4ef126 (C658 Cards 15–17, niche 1331/0), 85c7c670 (C659 paper
  v1.0: §0 23 моста / 7 слоёв, 173 якоря), 4408912f (C660
  `HoldoutGateTwoWay.lean` +3 theorem).
- Доказано: `useful_first_step` — drop(η*) = 2a²/R² при η* = 4|a|/R²,
  `exists_useful_eta`, `first_step_useful_certified`,
  `first_step_strict_improves`; негатив `no_signal_no_drop` (a = 0 ⇒
  COMMIT невозможен); `holdout_gate_two_way(_delta)` — union bound по Θ
  покрывает peeking, принятый гейт ⇒ pop_new ≤ pop_old + 2ε − margin.
- Honest: U2 открыт; a < 0 и линейность по η — гипотезы (chain rule к
  `adam_first_step_dot_pos` не формализован); iid-holdout — модель;
  при k = 512 сертификат почти вакуумный (2ε ≈ 0.25B).
- Фронтир: метатеория v3.4 (+3 клоза); PROPOSAL-holdout-size (k ≥ 1199
  для ε = 0.05B, δ = 0.05, |Θ| = 10); paper §0 без строки C660.

<a id="c662-c664"></a>
## C662–C664 — эра «v3.4 + wave258b»: 14 клозов, chain rule, порядок окон (freeze 8959→8967)

- Коммиты: 6f9837d3 (C661 разбор c657–c660), 4fd95e00 (C662
  `hagi_master_v34` + PROPOSAL-holdout-size), 0ce30c0d (C663 chain
  rule Adam-first ⇒ useful warm-up), C664 (wave258b `padSlot` + разбор).
- Доказано: v3.4 = v3.3 + (12) strict first step, (13) Adam-first
  descent, (14) holdout two-way; `chain_linear`, `useful_of_adam_first`
  (a < 0 выведен для линейного носителя); `padSlot_tail/_last/_full` —
  generation-окно (левый паддинг) и holdout-окно — один порядок, query в
  последнем слоте.
- Honest: нелинейный chain rule (relu-блок) открыт; U2 открыт; iid-holdout
  — модель, k = 512 вакуумно; hagi/unified.py:1010 @bab8aff ещё `[::-1]`.
- HAGI_v2: HEAD 134f81b (wave 259: потеря production-чекпоинта тестами),
  worktree dirty — чтение только через git show.
- Фронтир: unified.py:1010 → push; HasFDerivAt chain rule; U2; решение по
  k ≥ 1199.

<a id="c665-c667"></a>
## C665–C667 — эра «нелинейный носитель + Надя + width-рост» (freeze 8967→9043)

- Коммиты: 32a61ee5 (C665 `useful_of_adam_first_fderiv/_relu` —
  b1-блок, строгое убывание для малого η), 5c99e460 (C666 — носители
  10 идей «Надя.txt»: BitAlloc/Schedules/LCB/Bypass),
  3ba95ac3 (C667 `grow_width` function-preserving, nh = 1, T1–T3).
- Honest: certified-величина drop для нелинейного носителя и
  производная по W1 открыты; нечётная ширина и nh > 1 не формализованы;
  hagi/unified.py:1010 @bab8aff ещё `[::-1]`; U2 открыт.

<a id="c668"></a>
## C668 — производная по первому слою W1 (freeze 9043→9054)

- Коммит: `feat: first layer gradient rank one and useful w1 step`
  (sha — в receipt `.tmp/C668/receipt.md`).
- Исследование: F3 = «производная по W1 не формализована»; код —
  `_block_add` lm.py:586 @ca52eb4 (`relu(a @ W1 + b1) @ Wo`), `W1` —
  lm.py:594 @ca52eb4. Внешние источники не использованы: реестр Palomar
  (1351 entries, API) не содержит fderiv/chain rule/backprop;
  sciencemadereadable даёт статьи о low-rank-градиентах (Sonthalia et al.
  2025), не формализации.
- Результат: `Hagi/Theory/FirstLayerGrad.lean` — `hasFDerivAt_w1L`
  (chain rule: линейная `W1 ↦ W1ᵀx` + `hasFDerivAt_reluL`),
  `w1_grad_rank_one` (`g (i,j) = g i · x j`),
  `w1_directional_derivative`, `useful_of_adam_first_w1` (T5, строгое
  убывание), `w1_rank_one_step_eq_bias`.
- Honest: certified drop по W1 не выведен; один вход (батч = Σ_t g_t ⊗ a_t
  не формализован); оптимум по норме Фробениуса не формализован;
  U2 открыт.

<a id="c669"></a>
## C669 — батч-градиент по W1 и оптимальность шага (freeze 9054→9070)

- Коммит: `feat: batch gradient frobenius optimal step and rank one
  optimality` (sha — в receipt `.tmp/C669/receipt.md`).
- Исследование: пин C668 «батч = Σ_t g_t ⊗ a_t; оптимум по норме
  Фробениуса не формализован». Код: `W1 -= (cos_lr * 0.7) *
  newton_schulz_orthogonalize(m1, iters=3)` core.py:1755 @ca52eb4 (Muon-шаг
  по `W1`), `newton_schulz_orthogonalize` core.py:1350 @ca52eb4; лосс —
  `cross_entropy` по батчу lm.py:688 @ca52eb4. Источники: Chen, Li, Liu
  «Muon Optimizes Under Spectral Norm Constraints» (arXiv 2506.15054),
  Li–Hong «A Note on the Convergence of Muon» (arXiv 2502.02900) — через
  ask.sciencemadereadable.com; формулировки T1–T3 взяты из них, доказательства
  элементарные. Реестр Palomar: `/api/cards?q=` отдаёт 404, готовой карты
  по spectral-norm дуальности не найдено.
- Результат: `Hagi/Theory/BatchRankOne.lean` — `batch_directional_derivative`
  (T1), `frob_step_le` + `sgd_step_attains` (T2: SGD-направление оптимально
  в шаре Фробениуса, Коши–Шварц), `rank_one_inner` + `rank_one_le` +
  `rank_one_best_v` (T3'': оптимум внутри rank-one-семейства при фикс. `u`).
- Honest (down-scope): спектральный аналог (max ⟨G,Δ⟩ при ‖Δ‖₂ ≤ 1 = σ_max,
  шаг `U Vᵀ`) не доказан — нужна дуальность спектральной/ядерной нормы
  (hbridge); сравнение с Adam-sign не формализовано; Muon-шаг кода
  (core.py:1755) относится к другой `W1`, чем слой `_block_add` (lm.py:586).

<a id="c670"></a>
## C670 — rank-one спектральный шаг Muon и σ_max (freeze 9070→9084)

- Коммит: `feat: rank one spectral step optimal via courant fischer muon core`
  (sha — в receipt `.tmp/C670/receipt.md`).
- Исследование: пин C669 «спектральный аналог T2 (max ⟨G,Δ⟩ при ‖Δ‖₂ ≤ 1
  равен σ_max, шаг `U Vᵀ`) не доказан». Код: newton_schulz_orthogonalize
  core.py:1350 @ca52eb4, вызов core.py:1755 @ca52eb4 (quirk `iters=3` ⇒
  приближённая изометрия). Инвентаризация Flywheel: вещественный SVD
  (svd_decomposition, realAV_eq_constructedU_real_mul_sigma в SVDReal.lean),
  Courant–Fischer (rayleigh_le_eigenvalue_max), Eckart–Young,
  spectral_norm_eq_max_singularValue (комплексный), `‖A‖_F² = Σσ²`. В
  Mathlib v4.36 pin: LinearMap.singularValues (sNum0, antitone) без
  равенства операторной норме; дуальности спектральной/ядерной норм и
  неравенства фон Неймана нет. Реестр Palomar недоступен (C669 — 404).
- Результат: `Hagi/Theory/MuonSpectral.lean` — `rank_one_norm_bound`
  (Courant–Fischer в форме SVD), `rank_one_inner_le` (T1),
  `rank_one_spectral_norm` (T2: `‖u ⊗ v‖₂ = 1`), `rank_one_attains` (T3:
  топ-пара достигает σ_max), `rank_one_spectral_step_optimal` (T4).
- Honest (down-scope): только rank-one срез; полный шаг Muon `U Vᵀ` (von
  Neumann / спектрально-ядерная дуальность) не доказан; `smax = ‖G‖₂` для
  вещественных матриц не выведен; прямоугольный слой не формализован.
