# Era index — C591–C640 (2026-11-22/23)

Навигация по эрам: период | главные коммиты | доказанные
результаты | фронтир на конец эры. Per-beat разбор удалённых
`period-*-analysis.md` — `git log` / `git show <sha>`. Имена —
по состоянию на HEAD (модули v7-слияний: `GrowthGate`,
`WindowTradeoff`, лестница `MasterTheoremV31..V33` →
`Hagi/Theory/{NegativeTransfer,CoverageReading,MasterTheoremV3}.lean`).
Числа freeze — рост только на новые Lean-декларации; docs-витки
— identity. Планы рефакторинга: `refactor-master-plan-v7.md`,
`refactor-master-plan-v7-cycle2.md` (этот каталог).

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
- Полный разбор: `period-c638-c640-analysis.md`.

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
  paper v0.9, external push proposal. Разбор: `period-c642-c644-analysis.md`.

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

<a id="c646-c648"></a>
## C646–C648 — эра «рост + вероятность» (freeze 8887→8907)

- Коммиты: e84eac25 (C646 certified-шаг на блоке), 2a554dc7 (C647
  `Contracts/BatchGlobalTelescope.lean`, уровни A/B/C), eaee5ea2 (C648).
- Доказано: `certified_step_block_of_range` (range-лемма на логитах
  носитель-независима), `batch_drop_generalizes` (через EB),
  `certified_rounds_union` (k раундов, slack k·ebGap(α/k)).
- Honest: iid/независимость раундов — модель, не код; код не считает
  b/sig; WOR-консервативность не формализована; JVP — реализация.
- Фронтир: paper v0.9 (8 мостов C638–C648); Adam EMA-лемма;
  bench certified-warmup-sim; WOR; external push proposal.
  Разбор: `period-c646-648-analysis.md`.
