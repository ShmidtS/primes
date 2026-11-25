# Era index — C591–C681 (2026-11-22/25)

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

<a id="c668-c676"></a>
## C668–C676 — эра «Muon chain»: шаг Muon слоя W1 как доказанный спуск (freeze 9043→9149)

Сводка эры (секции C668..C676 ниже — носители, не удалять):
- Коммиты: c85d35bf (C668), 3c1fb372 (C669), a3f7c669 (C670), ff584ffb
  (C671), f7972b11 (C672), ecacde41 (docs), 42db5e61 (C673), c34f4e43
  (C674), 9efa9dc1 (C675), 57483f97 (C676); C677 — docs-консолидация
  (paper v1.2, Cards 18–19, PROPOSAL-muon-guards), freeze identity;
  C678 — прямоугольный шаг (sha — в receipt `.tmp/C678/receipt.md`);
  C679 — вещественный прямоугольный SVD (pad-to-square), гипотеза
  MuonWide снята (sha — в receipt `.tmp/C679/receipt.md`);
  C680 — wide Muon безусловно: нормировка, транспонирование, сертификат
  (sha — в receipt `.tmp/C680/receipt.md`);
  C681 — прямоугольный слой `W1 : dim × hidden` → широкий Muon-шаг, мост
  к слою (sha — в receipt `.tmp/C681/receipt.md`).
- Цепочка: градиент W1 = g ⊗ x вне излома (C668) → батч, F-оптимальный
  SGD (C669) → rank-one оптимум σ_max (C670/671) → оптимум на
  изометриях без фон Неймана (C672) → NS-схема σ ↦ σ(3−σ²)/2, σ₃ ≥ 39/40
  (C673) → общие сингулярные векторы (C674) → нормировка, сертификат
  спуска (C675) → инстанцирование на слое W1 (C676).
- Результат: для квадратного W1, G ≠ 0, вне излома `CE(W1 − η·ns_k(Ĝ))
  < CE(W1)` для малого η; first-order drop ≥ ‖G‖_F.
- C678: строка кода core.py:1363 = `ns_step` для `m×n`; итерации
  сохраняют сингулярные базисы; оптимум на строчных изометриях `Σ σ i`.
- C679: `exists_wide_svd` — широкий SVD существует; T1', T2, T5
  без гипотезы разложения.
- C680: для широкой `G ≠ 0` `σ i(Ĝ) ≤ 1` (`‖G‖_F² = Σ σ i²`) ⇒ T3 и
  сертификат спуска без единой посылки о структуре `G`; для любой формы
  (в т.ч. высокой) код-выход = `wide_iter k G` (`ns_step_transpose`).
- C681: мост к слою — `muon_step_useful_w1_rect(_batch)`: для
  прямоугольного слоя `ι → δ → ℝ`, вне излома, `G ≠ 0`, `card ι ≤ card δ`
  шаг `W1 − η·wide_iter k Ĝ` строго убывает CE (один вход / батч).
- Honest: слой `dim × hidden` покрыт при `dim ≤ hidden` (высокий слой
  не сведён; сертификат C676 — квадрат; сертификат C680 — координатный
  носитель `m → n → ℝ`, мост к слою — C681),
  фон Нейман, η только существует (`cos_lr·0.7`, momentum `m1`), малые σ,
  mean-лосс.
- Следующий шаг: мост «слой `W1 : dim × hidden` → широкий `G`» и
  сертификат спуска C676 на нём; липшицева оценка; momentum.

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

<a id="c671"></a>
## C671 — вещественный мост `σ_max = ‖G‖₂` и spectral ball (freeze 9084→9090)

- Коммит: `feat: real spectral norm equals top singular value muon ball corollaries`
  (sha — в receipt `.tmp/C671/receipt.md`).
- Исследование: пин C670 «`smax = ‖G‖₂` для вещественных матриц не выведен».
  Flywheel: `spectral_norm_eq_max_singularValue` (комплексный, MatrixNormRelations:328,
  через `l2_opNorm_hermitian_eq_sup_abs_eigenvalues`). Mathlib v4.36 pin:
  `Matrix.l2_opNorm_diagonal`, `l2_opNorm_conjTranspose`,
  `l2_opNorm_conjTranspose_mul_self`, `l2_opNorm_mulVec`; вещественного
  `l2_opNorm_le_frobenius_norm` в pin нет (во Flywheel — только комплексный).
- Результат: `Hagi/Theory/MuonSpectral.lean` — `smax_eq_opNorm` (T1, путь (b):
  SVD + инвариантность), `smax_le_frobenius` (T2), `opNorm_mulVec_le` (T3);
  несущие `l2_opNorm_mul_orth`, `l2_opNorm_diagonal_abs`, `l2_opNorm_diagonal_nonneg`.
- Источники: ask.sciencemadereadable.com — релевантных работ по запросу нет
  (неполезно); Palomar `?view=cards` — JS-страница, карту найти не удалось.
- Honest (down-scope): `‖u ⊗ v‖₂ = ‖u‖₂·‖v‖₂` для неединичных векторов
  не доказан — отброшен по Sunk Cost; полный шаг Muon (von Neumann) по-прежнему открыт.

<a id="c672"></a>
## C672 — полный шаг Muon оптимален на группе изометрий (freeze 9090→9102)

- Коммит: `feat: muon step optimal over isometries without von neumann`
  (sha — в receipt `.tmp/C672/receipt.md`).
- Исследование: пин C671 «полный шаг Muon (von Neumann) открыт». Путь (P1)
  фон Нейман — мажоризация/Birkhoff, тяжёл и в пине Mathlib отсутствует.
  Путь (P2): для изометрии `ΔᵀΔ = 1` (то, что выдаёт идеальный
  Newton–Schulz, core.py:1363 @ca52eb4) достаточно `⟨G, Δ⟩ = Σ σ i·Q i i`,
  `Q = UᵀΔV` — изометрия ⇒ `Q i i ≤ 1`. Выбран P2 (без внешних теорем).
- Код-якорь (READ-ONLY, `git show ca52eb4:hagi/core.py`): нормировка —
  Frobenius `np.linalg.norm` (core.py:1353), итерация core.py:1363, вызов
  `iters=3` core.py:1755.
- Результат: новый `Hagi/Theory/MuonIsometry.lean` — `isometry_diag_le_one`
  (T1), `isometry_inner_le_ssum` (T2), `uv_transpose_attains_ssum` (T3),
  `muon_step_optimal_in_isometry_group` (T4); носители `fdot_eq_trace`,
  `inner_eq_sigma_weighted_diag`, `isometry_conj`. Down-scope не потребовался.
- Источники: ask.sciencemadereadable.com — релевантных работ нет (выдача
  про aligning мюонных камер CERN и trace ratio; неполезно); Palomar —
  реестр недоступен (как в C669–C671), не повторялось.
- Honest (границы): максимум доказан на группе изометрий, не на всём шаре
  `‖Δ‖₂ ≤ 1`; приближённость `iters = 3` (оценка σ_min), прямоугольный `G`,
  сходимость итерации к `U Vᵀ` и мост к обновлению `W1` (lm.py:586) не
  формализованы. Следующий шаг: нижняя граница `σ_min` после k итераций
  (полином `p_k(t) = (3t − t³)/2` для `t = σ²`) — кандидат на формализацию.

<a id="c673"></a>
## C673 — скалярная динамика Ньютона–Шульца и граница σ_min после k итераций (freeze →9115)

- Коммит: `feat: newton schulz quadratic defect contraction explicit sigma bound`
  (sha — в receipt `.tmp/C673/receipt.md`).
- Исследование: пин C672 «σ_min после 3 итераций не формализована». Код
  (READ-ONLY, `git show ca52eb4:hagi/core.py`): КВАДРАТИЧНАЯ схема
  `X = 0.5 * (3.0 * I_m - X @ X.T) @ X` core.py:1363 (a = 3/2, b = −1/2,
  кубичного члена нет), нормировка Frobenius core.py:1353, `iters=3`
  core.py:1755. Путь: скалярная динамика `σ ← σ(3 − σ²)/2` через собственное
  число `YᵀY` (T5'), дефект `d = 1 − σ` сжимается квадратично.
- Результат: новый `Hagi/Theory/NewtonSchulzSigma.lean` (11 деклараций) —
  `ns_quadratic_invariant` (T1), `ns_seq_bounds` (T1'), `ns_defect_contraction`
  (T2), `ns_defect_bound` (T3), `ns_sigma_min_three` (T4: σ₀ ≥ 1/2 ⇒ σ₃ ≥ 39/40),
  `ns_step_eigenvalue` / `ns_step_eigenvalue_sigma` (T5/T5'); носители `ns_p`,
  `ns_seq`, `ns_step`, `ns_p_mono`, `ns_seq_mono`, `ns_shift_mulVec`.
- Источники: ask.sciencemadereadable.com — полезно: Shulgin et al., arXiv
  2610.30280 (малые сингулярные числа NS-итерации Muon не поднимают —
  подтверждает гипотезу σ₀ ≥ 1/2); de Oliveira et al., arXiv 2609.30546
  (гарантии сходимости Muon).
- Honest (границы): σ₀ ≥ 1/2 — гипотеза (код даёт лишь σ₀ ≤ 1); T5 — через
  собственный вектор XᵀX (спектр YᵀY из SVD-носителя не собран); мост
  «σ_min(Δ_k) ≥ 1 − ε ⇒ ⟨G, Δ_k⟩ ≥ (1 − ε)·ssum G» не доказан (нужна
  диагональ Q = UᵀΔ_kV); прямоугольный X, сходимость к U Vᵀ, кубичная схема
  (в коде отсутствует) — не формализованы.
- Следующий шаг: лемма о диагонали приближённой изометрии — если
  `ΔᵀΔ = I + E`, `‖E‖ ≤ 2ε − ε²` (т.е. `σ_min ≥ 1 − ε`), то `Q i i ≥ 1 − ε`
  для `Q = UᵀΔV`; тогда `⟨G, Δ_k⟩ ≥ (1 − ε)·ssum G` с `ε = 39/40`-дефектом.

<a id="c674"></a>
## C674 — Newton–Schulz делит сингулярные векторы с градиентом: точное выравнивание (freeze →9122)

- Коммит: `feat: newton schulz shares singular vectors with gradient exact muon alignment`
  (sha — в receipt `.tmp/C674/receipt.md`).
- Исследование: пин C673 «нужна лемма о диагонали Q = UᵀΔ_kV». Проверка математики:
  утверждение `tr(B·Q) ≥ σ_min(Q)·tr(B)` для несимметричной `Q` ЛОЖНО (Q —
  поворот на 90°, B = I: tr Q = 0). Для шага кода оно и не нужно: итерация
  core.py:1363 — правое умножение на симметричный множитель, поэтому
  `X_k = U·diag(ns_seq k∘σ)·Vᵀ` и `Q` диагональна. Источник
  ask.sciencemadereadable.com — НЕ полезно (выдал muon g-2); palomar — пусто.
- Результат: новый `Hagi/Theory/MuonAlignment.lean` (7 деклараций) —
  `ns_step_svd` (T1), `ns_iter_svd` (T1'), `muon_alignment_exact` (T2:
  `⟨G, X_k⟩ = Σ σ i·ns_seq k (σ i)`), `muon_near_optimal` (T3: `σ ≤ 1 ⇒
  `⟨G, X₃⟩ ≥ (39/40)·Σ_{σ≥1/2} σ i`), `muon_alignment_ge_gradient` (T4:
  `⟨G, G⟩ ≤ ⟨G, X_k⟩`); носители `ns_iter`, `kept`.
- Honest: `σ i ≤ 1` нормированного градиента — гипотеза (формализовано лишь
  `smax ≤ ‖G‖_F`); малые `σ < 1/2` без нижней границы; прямоугольный `G`,
  `η = cos_lr·0.7`, обновление `W1` — не формализованы.
- Следующий шаг: главный разрыв теории оптимизатора — мост «шаг → обновление
  слоя» (core.py:1755 ↔ lm.py:586): доказать, что `W ← W − η·X₃` с
  `⟨∇_W L, X₃⟩ ≥ 0` даёт спуск (first-order, липшицева константа); и
  `realSingularValues (c•G) = |c|·σ`, чтобы снять гипотезу `σ ≤ 1`.

<a id="c675"></a>
## C675 — Нормировка градиента и сертификат спуска Muon-шага: итог цепочки C668–C675 (freeze →9139)

- Коммит: `feat: muon step descent certificate and normalized gradient scaling`
  (sha — в receipt `.tmp/C675/receipt.md`).
- Исследование: носитель `Matrix` не имеет `Inner`-инстанта с `fdot`; мост
  «функциональный носитель C669 ↔ Matrix» дороже 150 строк ⇒ сертификат
  сформулирован абстрактно (`useful_of_neg_fderiv`, перенос
  `useful_step_of_fderiv` C642) со связью дифференциала как гипотезой.
  Проверка знака: C669 даёт `f'(W)[Δ] = −⟨batchGrad, Δ⟩`, шаг кода
  `W − η·X₃` ⇒ убывание ⟺ `g = −batchGrad` (обычный градиент).
  Источник ask.sciencemadereadable.com: релевантно — Roy & Chakraborty
  arXiv 2610.03306 (finite-step NS сохраняет выравнивание с momentum при
  ограниченной спектральной норме), Wang et al. 2609.33152, Shulgin et al.
  2610.30280.
- Результат: новый `Hagi/Theory/MuonDescent.lean` (223 строки, 17 деклараций,
  8 теорем) — S1 `smax_smul`, `sigma_le_smax`, `normed_sigma_le_one`,
  `muon_step_inner_ge_frob`, `normed_near_optimal`; S2 `useful_of_neg_fderiv`,
  `muon_step_useful`; S3 `muon_vs_sign_first_order`. Гипотеза `σ ≤ 1`
  нормированного градиента снята.
- Honest: `φ Δ = ⟨g, Δ⟩` на носителе `Matrix` — гипотеза (C668/C669 —
  функциональный носитель); `η` только существует; momentum, `cos_lr·0.7`,
  липшицева лемма спуска, сходимость — вне теории; сравнение «на единицу
  нормы шага» не доказано (только witness-числа); квадратный `G`.
- Следующий шаг: (1) мост «функциональный носитель → Matrix» и явный
  дифференциал слоя `lm.py:586` (снять гипотезу `muon_step_useful`);
  (2) липшицева лемма `L(W − ηX) ≤ L(W) − η⟨g,X⟩ + η²L/2·‖X‖_F²` — оценка
  шага; (3) `‖ns_iter k Ĝ‖_F` через SVD для сравнения Muon/sign на единицу
  нормы; (4) прямоугольный `G`.

<a id="c679"></a>
## C679 — Вещественный прямоугольный SVD из квадратного (pad-to-square): гипотеза MuonWide снята (freeze →9179)

- Коммит: `feat: real rectangular svd exists from square decomposition wide alignment unconditional`
  (sha — в receipt `.tmp/C679/receipt.md`).
- Исследование: квадратный `svd_decomposition` (SVDReal.lean:352) даёт
  `U V : n×n`, `σ = realSingularValues` без обещания порядка; но
  `eigenvalues₀` антонатонен по нумерации `equivOfCardEq` — при переносе
  на неё (`enum`) «нулевые — последние» доказуемо через ранг:
  #ненулевых = `rank (GᵀG) = rank G ≤ card m`. Прямоугольного SVD в
  Mathlib 4.36 нет (`LinearMap.singularValues` без равенства `A = UΣVᵀ`).
- Путь A (pad-to-square), с поворотом: подматрица `U[range, range]` не
  ортогональна при `rank G < card m`, поэтому `G = K·V₀ᵀ` (`V₀` — первые
  столбцы `V`, `K := G·V₀ : m×m`) и ВТОРОЙ квадратный SVD для `K`:
  `G = U·diag σ·(V₀W)ᵀ`. Пути B (Gram + дополнение базиса) и C (подматрицы
  `U`) отброшены: дороже / неверны.
- Результат: новый `Hagi/Theory/WideSVD.lean` (315 строк, 16 деклараций,
  4 теоремы): `exists_wide_svd`; следствия без гипотезы
  `wide_iter_svd'`, `wide_alignment_exact'`, `wide_step_optimal'`;
  носители `padSquare`, `enum`, `leadingEmbedding`, `zeros_outside_leading`,
  `sum_leading`, `antitone_real_sqrt_nonneg`.
- Источники: ask.sciencemadereadable.com — НЕ полезно (10 работ:
  учебники/приложения SVD, формализации нет); palomar — не искал
  (Cards 18–19 квадратные, C678). Ссылок не добавлено.
- Honest: порядок `σ` не утверждается; только `card m ≤ card n`;
  T3 остаётся с посылками `σ ≤ 1` и разложения; высокий случай
  (транспонирование core.py:1358) без теоремы.
- Следующий шаг: (1) `normed_sigma_le_one` в широком случае ⇒ T3 без
  гипотезы; (2) мост «слой `W1 : ι → δ → ℝ` → широкий `G`» и сертификат
  спуска C676 на нём; (3) транспонирование (высокий случай).

<a id="c681"></a>
## C681 — Прямоугольный слой W1 → широкий Muon-шаг: мост в кодовой размерности (freeze →9207)

- Коммит: `feat: rectangular w1 layer muon descent in code dimension`
  (sha — в receipt `.tmp/C681/receipt.md`).
- Исследование: носитель `muon_step_useful_wide` (WideSVD:446) — `W, G :
  Matrix m n ℝ`, `f : (m → n → ℝ) → ℝ`, `φ` — CLM на Pi-типе; квадратность
  C676 сидит только в `muonStep`/`fdot`. `w1_fderiv_apply` и
  `w1Batch_fderiv_apply` переносятся заменой `Matrix n n ℝ` → `Matrix ι δ ℝ`,
  `fdot` → `fdot_wide`; спуск — `useful_of_neg_fderiv` (generic по `E`)
  на носителе `ι → δ → ℝ`; sup vs ℓ² не возникает — лемма одномерна вдоль
  луча. Down-scope не потребовался (ветка B5 не сработала).
- Результат: новый `Hagi/Theory/MuonDescentW1Rect.lean` (12 деклараций):
  `w1GradR`, `fdot_wide_neg_of`, `w1_fderiv_apply_R`, `w1GradR_ne`,
  `w1StepR`, `fdot_wide_w1StepR_pos`, `muon_step_rect_of_fderiv`,
  `muon_step_useful_w1_rect`, `w1BatchObjR`, `w1BatchGradR`,
  `w1Batch_fderiv_apply_R`, `muon_step_useful_w1_rect_batch`.
  Freeze 9195 → 9207 (+12, identity).
- Witness `.tmp/C681/traj.lean`, rc = 0: слой 3×4 вне излома,
  `w1GradR = −(g ⊗ x)`; Float-реплика: `‖G‖_F² = 3.5`,
  `⟨G, wide_iter 3 Ĝ⟩ = ‖G‖_F = 1.870829`. Аксиомы 7 теорем ≤ 3.
- Источники: ask.sciencemadereadable.com — 403; palomar (ddg) — 0
  результатов. Ссылок не добавлено.
- Honest: `card ι ≤ card δ` (посылка, высокий слой не сведён); `G ≠ 0`
  в батче — посылка; η; momentum; mean; фон Нейман.
- Следующий шаг: высокий слой (`card ι > card δ`) через
  `wide_iter_transpose`; липшицева оценка для `η`; momentum `m1`.

<a id="c680"></a>
## C680 — Wide Muon безусловно: нормировка (S1), транспонирование (S2), сертификат спуска (S3) (freeze →9195)

- Коммит: `feat: wide muon normalized spectrum transpose and descent unconditional`
  (sha — в receipt `.tmp/C680/receipt.md`).
- Исследование: план `wsmax G := smax (pad G)` + `padSquare_mulVec` +
  `opNorm_mulVec_le` отброшен как избыточный — для цели `σ i(Ĝ) ≤ 1`
  достаточно тождества `‖G‖_F² = tr(GᵀG) = tr(diag σ²·VᵀV) = Σ σ i²`
  (`wfrobSq_eq_sum_sigma_sq`): `σ i² ≤ Σ σ² = ‖Ĝ‖_F² = 1`. Для высокого
  случая: `ns_step` определён для любых `m×n` (C678), и
  `(3I − XXᵀ)X = X(3I − XᵀX)` симметрично ⇒ `ns_step Xᵀ = (ns_step X)ᵀ`,
  кодовое транспонирование core.py:1358–1361 — эффективность. Для S3:
  `Matrix m n ℝ` при `m ≠ n` не является `NormedAddCommGroup` в репо
  (норма есть только для квадратных) ⇒ носитель `m → n → ℝ`;
  `useful_of_neg_fderiv` generic по `E` — переиспользован, декларация
  не менялась.
- Результат: MuonWide +`ns_step_transpose`, `wide_iter_transpose`,
  `code_ns`, `code_ns_eq_wide_iter`; WideSVD +`wfrobSq`, `wnormed`,
  `wfrobSq_eq_sum_sigma_sq`, `wnormed_sigma_le_one`,
  `wnormed_inner_eq_one`, `wide_alignment_ge_gradient'`,
  `muon_step_useful_wide` (+ носители). Freeze 9179 → 9195 (+16).
- Witness `.tmp/C680/traj.lean`, rc = 0: `G = diag(3,4)` (2×3),
  `‖G‖_F² = 25`, `σ(Ĝ) = (3/5, 4/5)`, T3 при `k = 3`, `code_ns 3 Gᵀ =
  wide_iter 3 Gᵀ`. Аксиомы 7 теорем ≤ 3.
- Источники: ask.sciencemadereadable.com — не полезно (список
  учебников/приложений SVD); palomar — одна попытка не требовалась
  (Cards 18–19 квадратные). Ссылок не добавлено.
- Honest: T3'/сертификат — только широкая форма; сертификат на
  координатном носителе, мост к слою `W1` (C676) не формализован;
  η только существует; фон Нейман; momentum.
- Следующий шаг: мост «`W1 : dim × hidden` → широкий `G`» + сертификат
  спуска C676 на нём; липшицева оценка; momentum.

<a id="c678"></a>
## C678 — Прямоугольный Muon-шаг: широкая форма, сингулярные базисы, оптимум (freeze →9163)

- Коммит: `feat: rectangular muon iteration keeps singular bases wide isometry optimum`
  (sha — в receipt `.tmp/C678/receipt.md`).
- Исследование: код (core.py:1349 @ca52eb4) транспонирует к `m ≤ n` и
  итерирует `(1/2)(3I_m − XXᵀ)X`; алгебраически это правая форма
  `X(3I_n − XᵀX)/2`, для которой `NewtonSchulzSigma.ns_step` уже объявлен
  для `Matrix m n`. Прямоугольный SVD не нужен как ТЕОРЕМА: достаточно
  гипотезы-структуры `G = U·diag σ·Vᵀ` (`U : m×m`, `V : n×m`), т.к.
  `XᵀX = V·diag σ²·Vᵀ` требует только `VᵀV = 1`. Вещественного
  прямоугольного SVD в репо нет — карточка «pad-to-square».
- Результат: новый `Hagi/Theory/MuonWide.lean` (257 строк, 14 деклараций,
  8 теорем): K `code_step_eq_ns_step`; T1 `ns_step_wide_svd`; T1'
  `ns_iter_wide_svd`; T2 `wide_alignment_exact`; T3
  `wide_alignment_ge_gradient`; T4 `wide_row_isometry`; T5
  `wide_inner_le_sigma_sum`, `wide_step_optimal`; носители `code_step`,
  `wide_iter`, `fdot_wide`, `fdot_wide_eq_trace`,
  `wide_inner_eq_sigma_weighted_diag`, `col_sq_eq_one`.
- Источники: ask.sciencemadereadable.com — НЕ полезно (10 работ о
  полуортогональных матрицах без связи с NS; релевантных 0); palomar
  (одна попытка) — Cards 18–19 есть, широкого шага нет. Ссылок не
  добавлено.
- Honest: разложение `G` — гипотеза всех T1–T5; guard core.py:1355 и
  `iters` 4/3 — факт кода, не теорема; оптимум — на строчных
  изометриях; `σ ≤ 1` для широкого `Ĝ` не доказано.
- Следующий шаг: (1) pad-to-square — существование широкого SVD из
  квадратного; (2) мост «слой `W1 : ι → δ → ℝ` → широкий `G`» и
  сертификат спуска C676 на нём; (3) `normed_sigma_le_one` в широком
  случае.

<a id="c676"></a>
## C676 — Мост «слой W1 → Muon-шаг»: гипотеза `φ` теоремы `muon_step_useful` снята (freeze →9149)

- Коммит: `feat: w1 layer muon step descent without carrier hypothesis`
  (sha — в receipt `.tmp/C676/receipt.md`).
- Исследование: носители C668/C669 — функциональные (`ι → δ → ℝ`), Muon-цепочка
  C674/C675 — `Matrix n n ℝ` (scoped-норма `Matrix.Norms.L2Operator`; инстанса
  `NormedAddCommGroup (Matrix n n ℝ)` по умолчанию нет). Мост «Matrix →
  функциональный носитель» через CLM доказуем, но шумный; дешевле (KISS)
  инстанцировать сертификат в функциональном носителе:
  `useful_of_neg_fderiv` + `muonStep`/`muon_step_inner_ge_frob` применяются к
  `Matrix.of` без изменения носителя `W1`.
- Результат: новый `Hagi/Theory/MuonDescentW1.lean` (234 строки, 10 деклараций,
  6 теорем): `fdot_neg_of`, `w1_fderiv_apply`, `w1Grad_ne`,
  `muon_step_useful_w1`, `w1Batch_fderiv_apply`, `muon_step_useful_w1_batch`;
  носители `onehot`, `w1Grad`, `w1BatchObj`, `w1BatchGrad`.
  Источник ask.sciencemadereadable.com: Fu–Chi–Liang (ISIT 2019) — только
  к следующему шагу (локальная гладкость CE), в Lean не использован.
- Honest: слой квадратный (`ι = δ = n`), в коде `dim × hidden`; в батче
  `G ≠ 0` — посылка; mean-лосс не выписан отдельно; `η` только существует.
- Следующий шаг: (1) прямоугольный слой (`Matrix m n`, NS с `UᵀU = I`,
  `VᵀV = I`) — кодовый размер `W1`; (2) липшицева оценка шага
  `L(W − ηX) ≤ L(W) − η⟨G,X⟩ + η²L/2·‖X‖²`; (3) momentum-буфер `m1`
  (в коде NS применяется к `m1`, не к `G`).

