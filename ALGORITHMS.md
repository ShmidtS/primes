# ALGORITHMS.md — оптимальные алгоритмы HAGI, выведенные из доказанных теорем

Каждый алгоритм — прямое следствие машинно-верифицированной
теоремы. Ссылки: `Hagi/<модуль>.lean`.

## 0. Главный цикл контроллера (certified growth loop)

```
while True:
    1. ИЗМЕРИТЬ      twoGap, d*, G, κ, s, inj, ξ        [GapLaw, SafeQP]
    2. СЕРТИФИЦИРОВАТЬ  Γ_i/K_i для каждого действия i    [R86]
    3. ВЫБРАТЬ        argmax Γ_i/K_i (бюджет B)          [R86]
    4. ИСПОЛНИТЬ      merge/joint/internalize/prune      [R71–R82]
    5. ПРОВЕРИТЬ     证书: E снизилось, старое не тронуто  [R72, R81]
    6. STOP если      консенсус И inj ≤ ξ                [R80]
```

Теорема-основание: `liveness_two_axis` (R80) — цикл не
замерзает, пока жива любая ось; заморозка = честный стоп.

## 1. Выбор действия: argmax Γ/K (оптимально доказано)

- Теорема: `ratio_dominance` + `budget_allocation_dominance`
  (R86): концентрация бюджета на argmax Γ_certified/K
  доминирует ЛЮБУЮ разбивку бюджета.
- Алгоритм:

```
ACTIONS = {merge, joint, internalize(TL;DR), prune,
           grow_leaf, distill, TTT-refresh}
for i in ACTIONS:
    Γ_i = предсказанный сертифицированный прирост:
        merge:        G = twoGap            [GapLaw]
        joint:        η‖d*‖²/2              [SafeQP_descent]
        internalize:  G_insight (KL-gap)    [insight_kl_descent]
        prune:        экономия − δ²/4       [prune_certificate]
        grow:         G_new − стоимость     [liveness_merge]
    K_i = замеренный wall-clock/FLOPs
choose argmax Γ_i/K_i
```

- Запрет: НЕ выбирать по standalone CE кандидата —
  `selection_hurts` (контрпример доказан).

## 2. Безопасный шаг: SafeQP-проекция (LR устранён)

- Теоремы: `safeQP_exists_unique`, `safeQP_descent`,
  `safeqp_inactive` (R84), `optimal_step_unconstrained` (R54).
- Алгоритм:

```
d* = proj_C(g0),  C = {d : ⟨g_i, d⟩ ≥ −ε_i}
η* = ⟨g0,d*⟩ / (L·‖d*‖²)         # аналитический, не гиперпараметр
если g0 ∈ C: шаг не активен (d* = g0)   [safeqp_inactive]
```

- Гарантия: ‖d*‖² ≤ ⟨g₀,d*⟩; спуск E ≤ E − η‖d*‖²/2;
  ε_i-бюджет на каждый старый домен.

## 3. Гейт слияния: реальный CE-зазор

- Теоремы: `twoGap_ce_identity`, `ce_gap_bounded` (R67):
  зазор слияния = ТОЧНО (CE₁+CE₂)/2 − CE_merge, ≤ M²/4.
- Алгоритм:

```
MERGE если twoGap > κ√n·s/2 + ε      # прирост > цена сжатия
PRUNE  если ‖z_i − z_j‖_∞ ≤ δ        # certificate δ²/4 [R72]
SKIP-гейт: η·gap ≤ M²/4              [R59]
```

- Дерево = сиб-на-домен, НЕ сиб-на-сид: доменная
  ортогональность гарантирует twoGap > 0
  (`domain_disagreement_floor` R66); сид-сибы коллапсируют.

## 4. Ось данных: фронтир-инъекция

- Теоремы: `diversity_floor_strict_pos`, `liveness_data_axis`
  (R80): inj > ξ ⟹ D_T > 0 на каждом поколении.
- Алгоритм:

```
при консенсусе (G → 0):
    инъекция свежих независимых данных/доменов
    (self-play генератор / новые корпусы)
    до восстановления twoGap > ε
стоп всей системы ⟺ консенсус И inj ≤ ξ  [liveness_two_axis]
```

## 5. Интернализация инсайтов (RLTL;DR-канал)

- Теоремы: `insight_kl_descent` (валюта), `tldr_drift_null`
  (нулевой дрейф вне носителя), `insight_consolidation_safe`
  (SafeQP-фильтр), `tldr_two_tier_safety` (R79/R81).
- Алгоритм:

```
провал → insight (TL;DR) → retry с insight
интернализация: LoRA-адаптер ΔW = A·B, ker B = вне-носитель
    вне носителя: дрейф ТОЧНО 0      [tldr_drift_null]
    в носителе:   SafeQP + Fisher-шар [R72+R79]
```

## 6. Роутер: Hedge + tail-budget

- Теоремы: `gating_tail_bound` (ошибка top-k = точно хвост),
  `router_regret_bound` (R(T) ≤ 2√(T ln K)).
- Алгоритм:

```
routing: top-k по |c_i| с бюджетом ошибки:
    min k : Σ_{i>k} c_i² ≤ ε_route        [tail identity]
веса: Hedge, η = √(ln K / T)              [regret bound]
```

## 7. Бюджеты: waterfilling

- Теоремы: KVWater (b_i − b_j = (ln c_i − ln c_j)/κ),
  `amgm_batch_bound` (B* = 2√(c·B_n·t₀)), ErrorProp.
- Алгоритм:

```
биты KV/весов:  b_i ~ ln(чувствительность_i)
батч:           B* по AM-GM
сжатие:         тернарное, цена κ√n·s/2 в общем сертификате
```

## 8. Мета-закон роста

- Теоремы: `capability_gain_transfer` (R82) →
  `growth_efficiency_div` (R83) →
  `capability_takeoff_counted/floor` (R85).
- Закон:

```
каждый успешный цикл: C ← C·(1+α), неудача: C не трогаем
итог: C_T ≥ C₀(1+α)^{N_успехов}           [R85]
условие взлёта: N ≥ ⌊pT⌋ (измеренная скорость открытий)
```

## Честные границы (что НЕ выведено)

- Вероятностная концентрация N ~ pT (DiscoveryProbability)
  — h_emp_, вероятностный слой открыт.
- ImplementationRefinement (Lean ↔ PyTorch/BF16) — открыт.
- NS-сходимость, Эккарт–Янг, нелинейная step-0
  инвариантность — открыты (STATUS.md).
