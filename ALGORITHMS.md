# ALGORITHMS.md — алгоритмы HAGI, выведенные из доказанных теорем

Каждый алгоритм — прямое следствие машинно-верифицированной
теоремы Lean 4 / Mathlib (Hagi/, 2909 theorem/lemma, 0 sorry,
аксиомы только propext/Classical.choice/Quot.sound).
Ссылки: `Hagi/<Каталог>/<Модуль>.lean`. Измеряемые посылки
помечены `h_emp_` и никогда не скрыты.

---

## 0. Главный цикл: certified loop (Gen-3, канонический)

Единый сертифицированный цикл обучения. Плоские капстоуны
поколения Gen-1 (`MasterHAGI*`, `grand_synthesis`)
`@[deprecated]`; Gen-1-семантика копируемых эффектов
доказуемо противоречива на T = 2

```
loop t = 0..n:
  1. ИЗМЕРИТЬ        obj (энергия), M.evaluate (качество),
                     spend (стоимость) из состояния
  2. СЕРТИФИЦИРОВАТЬ StepCert на переходе s→s':
        trans   : HonestTransition — спуск зависим от
                  исполнения: obj s' ≤ obj s − drop, drop > 0
        quality : FloorKept M s' floor — покомпонентный
                  пол качества (НЕ скалярный Qgen:
                  `qgen_hides` — контрпример)
        budget  : b' ≤ b − spend, 0 ≤ spend
  3. COMMIT/HOLD     без сертификата — hold
                     (`gate_never_increases`: энергия
                     не растёт НИКОГДА)
  4. СТОП            бюджет исчерпан / floor достигнут
```

- Итог горизонта (`certified_loop`, Unified/CertifiedLoop):
  Σdrops ≤ obj₀ − objₙ ∧ FloorKept ∧ 0 ≤ bₙ ≤ b₀ − Σspends.
- Строгость (`certified_loop_strict`): при n ≥ 1 спуск
  строгий, objₙ < obj₀.
- Весь горизонт (`certified_loop_all`): floor держится на
  КАЖДОМ промежуточном состоянии.
- Не-вакуозность (`quad_loop_horizon`): исполняемая
  машина (квадратичная, полушаг η = 1/2 — энергия × 1/4
  за шаг) инстанцирует сертификаты на любом горизонте
  (`quad_witness_T3`, `quad_witness_T10`).
- Закрепление: `master_hagi_challenge_v3` — comparator-гейт
  CI (пин типа StepCert, аксиомы чистые).
- Операциональные ядра `CertStep` (цикл 46):
  `logitStepCertExactCore` (scalar large-step CE),
  `ncMinimalStepCert` (энергия = gain нейрокомпьютера),
  `trainStepMinimalCert` (точный drop TrainState).
  Цикл 47 добавляет `GrowthComputedCert.stepCert` и
  `mergeStrictCertStep` (не нулевой Jensen gap).
  Исполнение даёт drop и actual без `h_emp_*`; полы, риск
  и бюджет подключаются как расширения, не подмена ядра.

## 1. Выбор действия: argmax Γ/K

- Теоремы: `ratio_dominance`, `budget_allocation_dominance`,
  `argmax_pair_certified` (Budget/CertifiedArgmax).
- Алгоритм:

```
for i in ACTIONS:                     # merge/joint/grow/
                                       # internalize/prune
    Γ_i = сертифицированный прирост:
        merge:   G = JensenGap ≥ 0    # MergeBridge
        joint:   η‖d*‖²/2             # safeQP_descent
        grow:    growGain (h_emp_)
        prune:   экономия − δ²/4
    K_i = измеренная стоимость
choose argmax Γ_i/K_i                  # доминирует любую разбивку
```

- Контрпример-предостережение: `tie_ambiguity` — при малых
  зазорах argmax противоречив; порог задаётся certified-полем.
- Запрет: не выбирать по standalone CE — `selection_hurts`.

## 2. Безопасный шаг: SafeQP (без learning rate)

- Теоремы: `safeQP_exists_unique`, `safeQP_descent`,
  `safeqp_inactive`, `safeqpEtaMax` (Step/ProjectionDescent,
  Step/MetricSafeQP).

```
d* = proj_C(g₀),  C = {d : ⟨g_i, d⟩ ≥ −ε_i}   # старые домены
η* ≤ safeqpEtaMax = min(1/L, ...)              # аналитический
если g₀ ∈ C:  шаг неактивен (d* = g₀)
```

- Гарантия спуска (joint_stage):
  E′ ≤ E − η⟨g₀,d*⟩ + Lη²‖d*‖²/2 ≤ E − η‖d*‖²/2
  при η ≤ 1/L и ‖d*‖² ≤ ⟨g₀,d*⟩.
- Оптимальный η (R347, StageCalculus):
  `quadratic_bound_max` — безусловный потолок модельного
  спуска inner²/(2L·dnorm²) при η* = inner/(L·dnorm²);
  `eta_star_exceeds_cap` — при certified descent η* > 1/L,
  кап активен; `joint_stage_cap_optimal` — на допустимом
  интервале оптимален η = 1/L, спуск dnorm²/(2L);
  `cap_cost_factor` — цена капа = фактор inner/dnorm² > 1.
  Правило: η = 1/L всегда (не настраивать); усилие — не в
  η-тюнинге, а в росте dnorm² (quality of direction).
- LR↔batch эквивалентность (`lr_batch_equivalence`,
  StochasticSafeQP; Smith et al. 1711.00489): шумовой бюджет
  шага η·noiseEps ∝ ησ/√m инвариантен при (η, m) → (kη, k²m).
  Правило планировщика: вместо снижения LR в k раз —
  увеличение batch в k² раз; сертификаты
  `stochastic_safeQP_feasibility` сохраняются на том же δ,
  а последовательных обновлений на ту же кривую — в k раз
  меньше (больше параллелизма). 

## 2b. Сжатые шаги: sign/Lion/SAM (Unified/SignDescent)

Компрессия шага с сертификатом чистого спуска. Ключевой
факт: НЕмасштабированный sign-шаг НЕ выровнен (норма
знакового вектора = число ненулевых координат, может
превышать ℓ₁-норму градиента) — масштаб обязателен.

```
s = ‖g‖₁ / n                            # signScale
шаг = x − η·s·sign(g)                   # η ≤ 1/L
```

- SignSGD: `sign_scaled_aligned` — выровненность
  (nrm2 ≤ inprod при s = ‖g‖₁/n); `sign_descent` — чистое
  убывание η(1−Lη/2)·s²·nnz (Bernstein 1802.04434: связь
  signSGD с нормализованным SGD).
- Lion (момент m): `scaled_sign_aligned_of_coherence` при
  согласованности момента с градиентом
  (‖m‖₁/n·nnz(m) ≤ ⟨g, sign(m)⟩); `lion_descent` — чистое
  убывание (Chen 2302.06675).
- Оптимальность знака: `sign_is_pointwise_max` — знак
  максимизирует ⟨g, v⟩ на всём ℓ∞-кубе |v i| ≤ 1 (векторное
  ядро спектральной оптимальности Muon;
  `muon_alignment_optimal` — матричная форма).
- SAM: `sam_descent_bridge` — спуск δ по worst-neighbor
  цели переносится на истинный лосс как δ − sharp (острота
  samW − L); плоский случай `sam_descent_flat` — чистый
  спуск (Foret 2010.01412). Правило: SAM-спуск честен
  ровно настолько, насколько найденный минимум плоский.
- Правило для сжатых машин: сначала SafeQP-направление
  (η = 1/L), затем компрессия шага до знаков с масштабом
  s = ‖g‖₁/n — сертификат спуска сохраняется формально.

## 2c. Точный large-step сертификат scalar logit CE

- `logitCE_strictAnti`: функция `log(1+exp(−w))` строго
  убывает на всём ℝ; `descent_step_strict`: при любом η > 0
  шаг `w′ = w + η/(1+exp(w))` строго уменьшает CE.
- Алгоритм (`logitStepCertExact`, `logitStepCertExact'`):
  вычислить новый вес и положить сертифицированный drop равным
  ТОЧНОМУ `logitCE w − logitCE w′ > 0`; бюджет требует
  η ≤ budget, полы следуют из `logitCE_nonneg`. Кап η ≤ 2
  не нужен для положительности точного drop в этой scalar
  one-example модели; на исходном диапазоне 0 < η ≤ 2
  точный спуск не меньше старой оценки
  (`logit_exact_drop_dominates`).
- Граница применимости: это не теорема о large-step GD для
  общей логистической регрессии; там возможны осцилляции и
  циклы (Wu et al., DOI `10.48550/arxiv.2402.15926`;
  Meng et al., DOI `10.48550/arxiv.2406.05033`). Расширение
  на несколько примеров/параметров требует нового доказательства,
  агрессивные шаги вне scalar-модели — только через measured
  commit/hold, не через эту теорему.

## 3. Гейт слияния: реальный CE-зазор

- Теорема (Unified/MergeBridge): CE(t, mid) = mean CE −
  jensenGap(z₁,z₂), jensenGap ≥ 0 — выводится из Core-lse
  теории, не постулируется.
- Правило: сливать пару, если jensenGap ≥ порога; экономия
  экспертов без роста CE гарантирована теоремой.
- Строгость (R356, `jensenGap_pos_witness`): при реальном
  несогласии экспертов (z₁=(0,0) vs z₂=(a,−a), a≠0) зазор
  строго положителен: ½log(cosh a) > log(cosh(a/2)) —
  слияние расходящихся экспертов строго лучше среднего,
  не-idle свидетель.

## 4. Квантование: тернарная сетка + мост потери

- Тернарное округление: |w − qTern| ≤ s/2 (Energy/Ternary).
- Мост в потерю (QuantBridge):
  - `quant_loss_bridge`: ‖(Ŵ−W)x‖ ≤ D·√(d_in·d_out)·‖x‖;
  - `quant_frob_loss`: ΔE ≤ κ_F·D·√(d_in·d_out);
  - `compress_chain_cost`: |ℓ(W)−ℓ(W″)| ≤ κ_F·(δ₁+δ₂);
  - `frob_minkowski`: норма-Минковского + Коши–Буняковский.
- Compress-стадия (compress_stage): E′ − E ≤ κ·s·qerr при
  qerr ≤ 1/2 — из этих канонов.

## 5. Спектральный отбор (Flywheel-порт)

- `eckart_young_frobenius`: усечение SVD оптимально по
  Фробениусу; Weyl-стабильность; `mdlJ_first_order`,
  `mdl_rank_ce` — MDL-ранг первого порядка.
- Правило: ранг k выбирать по MDL-критерию; потеря
  контролируется сертификатом Эккарта–Юнга.

## 6. Бюджет битов: water-filling

- `transfer_exact`: маржинальный обмен битами точен;
  `two_layer_equalize`: балансировка = water-filling;
  фактор-2 жадного инварианта (`stable_factor_two`).
- Сертификат поколения (distill_quant_composite):
  S_n + n·g ≤ E₀ + δ_n + totalError.

## 7. Концентрация и anytime-валидность

- Хёфдинг (MGF), Азума: P[ΣX ≤ −Δ] ≤ exp(−Δ²/2n).
- Freedman (`freedman_tail_low`):
  P[ΣX ≤ −Δ] ≤ exp(−Δ²/(2(V+bΔ/3))) — адаптивно к
  дисперсии; при V ≪ n сильнее Азумы.
- Мартингальные успехи: `adaptive_success_freedman`,
  anytime-формы (AnytimeValid) — доверительные границы
  валидны при произвольной остановке.

## 7b. Grokking-расписание (R366, Recurrence)

- `grokking_threshold_time`: остаточная динамика
  r(t+1) = r(t) − ηλ·r(t) достигает порога ε к моменту
  T = ln(r₀/ε)/(η·λ) — время генерализации управляется
  ПРОИЗВЕДЕНИЕМ learning rate × weight decay (формальное
  ядро спектральной теории grokking, arXiv:2609.26679).
- Правило планировщика: для целевого времени генерализации T*
  выбирать η·λ ≥ ln(r₀/ε)/T*; при фиксированном η (кап 1/L,
  R347) это задаёт weight decay λ — ещё один гиперпараметр
  выведен, а не настроен. Фазовая геометрия: слишком большое
  λ (ηλ > 1) — расходимость (условие ηλ ≤ 1 в теореме).

## 7c. Heavy Ball: точная критическая траектория (цикл 43)

- `hb_pair_second_order`: старая пара `(e,v)` имеет свободный
  коэффициент `β + η·(1−β)`, а не `β`; характеристический
  многочлен canonical second-order модели нельзя неявно
  применять к этой паре.
- Для canonical критической рекурренты при `ρ ≠ 0`
  алгоритм вычисляет `C = e₀`, `D = e₁/ρ − e₀`; тогда
  `e_n = (C+D·n)·ρ^n` (`hb_repeated_root_closed_form`,
  обратный witness — `hb_repeated_root_form_solves`).
  Сама оценка `hb_critical_trajectory_bound` верна при
  `ρ > 0`; для затухания дополнительно требуется `ρ < 1`.
- Сертифицированный runtime-stop при `0 < ρ < 1`:
  принимать шаг n только при вычисленном `(|e₀|+|D|·n)·ρ^n ≤ ε`; тогда
  `|e_n| ≤ ε` следует из `hb_critical_trajectory_bound`.
  Чистая оценка `Cρ^n` запрещена: кратный корень даёт
  Jordan-фактор n. Внутренние моды с различными корнями —
  следующий алгоритмический frontier, не эта теорема.

## 7d. Heavy Ball: различные корни и двухкорневой темп

- `hb_two_root_closed_form`: если λ₁,λ₂ — корни одного
  характеристического многочлена и начальные данные
  разложены как `e₀=A+B`, `e₁=Aλ₁+Bλ₂`, алгоритм
  ошибки вычисляется как `e_n=Aλ₁^n+Bλ₂^n`; обратный
  witness — `hb_two_root_form_solves`.
- При `λ₁≠λ₂` (`hb_distinct_root_init`,
  `hb_distinct_root_explicit`):
  `A=(e₁−λ₂e₀)/(λ₁−λ₂)`,
  `B=(λ₁e₀−e₁)/(λ₁−λ₂)`.
  Знаменатель проверяется только разностью корней;
  нулевой корень допустим.
- Темп вычисления (`hb_two_root_norm_bound`,
  `hb_two_root_spectral_norm_bound`): для β>0 и
  `t²−4β ≤ 0`, `‖e_n‖ ≤ (‖A‖+‖B‖)·(√β)^n`.
  Это замыкает внутреннюю scalar-моду без Jordan-фактора;
  кратный корень обслуживается отдельно по 7c.
- Runtime: принимать n, если вычисленный RHS не превышает ε.
  Полный спектр по ортонормированным модам и коэффициент,
  зависящий от обусловленности, — следующий шаг, не
  содержание этих скалярных теорем.

## 7e. Аналитическое закрытие предпосылок

- `pl_stop_certificate_quadratic`: для квадратичной цели
  `E(w)=μ(w−a)²/2` с `L*=0` PL-форма выполняется точно;
  stop certificate вызывается без `h_emp_pl`.
- `audit/assumption_closure.md` фиксирует все 45 файлов lock:
  существующие smooth/lip/dist/grow/merge выводы и настоящие
  trust boundaries (independence, physics, telemetry).
- `forgetting_kl_quadratic_unit_fisher` и
  `tldr_two_tier_safety_unit_fisher`: скалярная модель задаёт
  KL как dW²/2, единичная F и её inner-product равенство
  доказываются, а h_emp_second здесь не нужен. Это не универсальная
  вероятностная KL-формула для всех распределений.
- `mopd_kl_scaling_warning_fivefold`: в явной fivefold-модели
  coэффициент политики равен пяти по построению, поэтому достаточный
  ε-budget выводится без h_emp_scaling. Произвольный λ отдельно
  измеряется/моделируется и этой теорией не закрывается.
- `projected_gradient_lipschitz` и
  `cut_signal_attention_quant_projection`: для scaled projected
  gradient достаточно нормы ортопроектора ≤1, поэтому здесь
  `h_emp_attsmooth` вывести можно. Выбирать retained subspace,
  измерять clamp/probe radii и передать границу в Cut-треугольник.
  Это строго явная модель общего P для двух карт, не доказательство
  адаптивного softmax attention и не оптимальность выбора маски.
- `fd_probe_error_quadratic` (цикл 57): для выбранного
  `probeQuadraticEnergy` вычислять forward-difference ошибку как
  (L/2)σ‖v‖² из самой энергии, без отдельной hmodel-матрицы.
- `probeQuadraticGrad_lipschitz`: общий для двух карты quadratic
  поле сохраняет Lipschitz по L с общим центром; это источник
  h_emp_attsmooth для Cut-инстанса, но не всего нелинейного attention.
- `computedGenStep` и `generalization_safe_step_computed` (цикл 56):
  для canonical energy=growthQuad weights вычислить веса и energy
  одним шагом. Probe/risk поля остаются неизменными именно этой
  hold-моделью, поэтому fit/G/risk доказаны без эмпирических wrappers;
  возможные новые оценки probe отдельно исследуются, не предполагаются
  неизменными автоматически или устанавливаются в фиктивную константу.
- `scripts/AssumptionScan.py` после цикла 55 исключает comments из
  premise-registry: действительный legacy count 137 содержал 24
  комментарных вхождения, реальный список locks 113. Классы закрывают
  только proofs; само сокращение реестра не считается новой теоремой.
- Общие conditional lemmas сохраняются только как интерфейс
  классов функций. Запрещено выдавать `EmpiricalPremises.holds`
  за доказательство гладкости: `premises_give_smooth` требует
  явной smoothness-модели; документация исправлена соответственно.

## 7h. Heavy Ball: вещественные корни и доминирующий темп

- `hb_two_root_norm_cap`: по отдельности полученные границы
  модулей λ₁ и λ₂ дают одну экспоненциальную оценку без
  требования одинаковых модулей. Нулевой и отрицательный
  корни допустимы.
- `hb_real_root_pm`: при D=t²−4β≥0 использовать
  явные корни `(t±√D)/2`; `hb_real_root_pm_norm`
  оценивает их общим знаменателем `r=(|t|+√D)/2`.
- `hb_real_two_root_norm_bound`: полная двухкорневая
  траектория удовлетворяет `‖e_n‖≤(‖A‖+‖B‖)r^n`.
  Это честная triangle-верхняя оценка, не обещающая точный
  max modulus. При D≤0 сохранять более точную оценку
  `r=√β` из 7d, при кратном корне — Jordan-форму 7c.
- Runtime: вычислить r, затем принимать n, если коэффициент
  начальных данных умноженный на r^n не превышает допуск.
  Векторный оператор пока оценивать только после разложения
  по модам; следствие о κ вне доказанного скалярного API.

## 7i. Heavy Ball: L²-сборка ортонормированных мод

- `hb_two_root_l2_bound`: координатно заданные корни и стартовые
  коэффициенты дают общую оценку векторной ошибки
  `‖e_n‖ ≤ sqrt(sum((‖A_i‖+‖B_i‖)^2))·ρ^n`.
  Используется Euclidean L²-норма, не сумма модальных амплитуд.
- `hb_two_root_orthonormal_bound`: тот же результат в исходном
  векторном пространстве через изометрию ортонормированного базиса.
  Алгоритм считает модальные коэффициенты и общий допуск ρ,
  затем использует глобальный L²-бюджет для runtime-stop.
- Вещественные корни берутся из 7h, комплексные — из 7d;
  кратные корни отдельно обслуживаются Jordan-формой 7c.
- Это НЕ автоматическая теорема спектрального существования и
  НЕ универсальный rate для stochastic/nonconvex HB. Цель —
  далее ограничить коэффициент через root separation и κ.
  Контекст по ограничениям SHB: Dang et al., 2401.06738.

## 7j. Heavy Ball: точный взвешенный L²-stop

- `hb_two_root_l2_weighted_bound`: каждая мода имеет свой тип
  затухания ρ_i; вычисляемая оценка векторной ошибки —
  `sqrt(sum(((‖A_i‖+‖B_i‖)·ρ_i^n)^2))`.
- `hb_two_root_orthonormal_weighted_bound`: та же сумма переносится
  через базисную изометрию в исходное векторное пространство.
  Общая оценка из 7i остаётся дешёвым uniform-вариантом, не заменой
  точной взвешенной формулы.
- Runtime: накапливать квадраты C_i²·ρ_i^(2n), взять sqrt
  и остановиться, когда полученная сумма не превышает допуск ε.
  Равенство и оптимальность именно этой upper-bound не утверждаются.
  Следующий вычислительный шаг — direct bound C_i через root gap
  и параметры состояния/κ, а не только через данные A_i/B_i.

## 7k. Heavy Ball: модальный префактор от начальных ошибок

- `hb_distinct_root_coefficient_sum_bound` выводит оценку
  `‖A‖+‖B‖ ≤ 2(‖e₁‖+ρ‖e₀‖)/gap`, где gap — нижняя граница
  модуля разности корней. Нулевой знаменатель исключён положительным
  gap, а не отдельным необъяснённым признаком различности.
- `hb_two_root_l2_initial_gap_bound` восстанавливает модальные A/B
  из e₀,e₁ и включает соответствующую вычислимую оценку в
  точную взвешенную L²-сумму из 7j.
- Runtime: вычислить gap_i и квадратичную сумму префакторов;
  малый gap автоматически увеличивает допуск, поэтому правило не
  скрывает численную чувствительность Vandermonde-разложения.
- Это консервативная начальная norm-bound, НЕ доказанная оптимальная
  κ-формула. Осталось связать gap с curvature/pair параметрами
  исходной HB-динамики и завершить базисный переход этой версии.

## 7l. Heavy Ball: исходная пара и runtime-certification

- `hb_pair_second_order_complex` исключает velocity из реальной
  пары, установленной прежним scalar proof: получается
  `t=1+β−η`, `c=β+η(1−β)` для λ²−tλ+c.
- `hb_pair_l2_initial_gap_bound` строит взвешенный L²-bound с
  префактором от начальных ошибок/root gap непосредственно от
  первопорядкового состояния. Это НЕ замена c на коэффициент β
  canonical-квадратики.
- `hb_pair_orthonormal_initial_gap_bound`: в произвольном полном
  ортонормированном базисе использовать компонентные velocity/error
  измерения, корни/tolerance и базисную изометрию; A/B заполняются
  алгоритмически из e₀,e₁ и не вводятся как свободные данные.
- Runtime-stop обязан явно проверять root norm и positive gap;
  если модальные темпы <1, возникает вычислимый допуск затухания,
  а если ≥1 — только растущая верхняя оценка. Probe из этого
  цикла относится ко второму случаю и не моделирует training success.
  Оптимальная κ-конфигурация и глобальная сходимость доказаны
  этими тремя мостами НЕ будут; это точная модельная связь.

## 8. Мета-закон роста: конус и насыщение

- Конус (frontier_cone_inductive):
  F(t+1) ≥ ρF(t) + γC(t) ⟹ C₀(1+γk)^T ≤ C_T.
- Насыщение (pl_gap_lower_trunc):
  C_T ≤ C* − (1−σ)^T·(C*−C₀).
- Совместимость (`cert_horizon_bound`): логарифмический
  горизонт — взлёт и потолок совместимы только если
  (1+γk)^(T−1) ≤ σC*/((γk+σ)C₀); явная форма (R349,
  `cert_horizon_log_bound`): T ≤ 1 + [ln(σC*) −
  ln((γk+σ)C₀)]/ln(1+γk) — чем сильнее конус, тем короче
  совместимый горизонт.
- На состоянии: `StateBinding` — C(t) = (S t).capability,
  G(t) = growGain; конус на реальной траектории состояний.
- Каскад: `sustained_takeoff_trunc`, `growth_dichotomy`,
  `elasticity_chain`, `saturation_limit`.

## 9. Капстоун: HAGI-синтез на семействе доменов

- `HAGICert` (ArchitectureTheorem, Fin I — произвольное
  семейство доменов):

```
взлёт:   C₀(1+γk)^T ≤ C_T
потолок: C_T ≤ C* − (1−σ)^T(C*−C₀)
риск:    ∀ домен i:
         Σₜ risk(t,i) ≤ T·best(i) + R + ε₀/(1−ρₑ)
```

  (`hagi_synthesis`; риск-часть — `universality_longhorizon`.)
- Свидетели не-вакуозности: `trunc_nonvacuous`,
  `certifiedHAGI_nonvacuous`, `coupledHAGI_nonvacuous`,
  `masterhagi_growth_witness`, `cert_horizon_witness` —
  все структуры предпосылок населены конкретными
  траекториями.

## 10. Интернализация инсайтов и инсайт-канал

- `ce_gap_kl_identity`: KL-зазор как сертифицированный
  прирост; `forgetting_kl_bound` — забывание ограничено.
- `liveness_two_axis`: цикл не замерзает, пока жива любая
  ось (консенсус/новизна); заморозка = честный стоп.

## 11. Контроллерные гейты (Runtime/ControllerGates)

- Variance gate: logitRange(f) масштабируется линейно при
  делении температуры; R²/8-граница контрактуется
  квадратично; перелёт R ≥ R̄ чинится точно τ = R/R̄
  (`variance_gate_contract`, `variance_gate_normalize`).
- Trust region: шаг (R/‖x‖)•x имеет норму ровно R и
  ближайший к x в шаре (`trust_region_proj_norm`,
  `trust_region_nearest`).
- Динамический роутинг: инжекция 1/√(2L) на ветвь даёт
  суммарную дисперсию v/2 независимо от глубины пути.

## 12. Направляющие константы (вместо гиперпараметров)

- η: аналитический `safeqpEtaMax` (не гиперпараметр);
- порог слияния: jensenGap-гейт (измеренный, не настроечный);
- ранг: MDL-критерий первого порядка;
- τ variance gate: R/R̄ (точный ремонт перелёта);
- горизонт: `cert_horizon_bound` (логарифмическая стыковка
  γk-взлёта и σ-насыщения);
- бюджет битов: water-filling `two_layer_equalize`.

## 13. Термостатный контроллер (Growth/Thermostat,
Probability/GibbsConcentration)

Отжиг T_t = T₀·α^t (0 < α < 1) как управляющий контур
селектора; все величины сходятся к пределам без настройки
гиперпараметров.

- Монотонность: `thermostat_monotone` — T_{t+1} ≤ T_t;
  `thermostat_tendsto_zero` — T_t → 0.
- Полярный Ньютон: `newton_step_descent` — итерация
  x ↦ (x+2)/3(x) монотонно спускается при x ≥ 1 и зажата
  1 ≤ newtonIter x₀ ≤ x₀ (`newton_iter_bracket`).
- Сертификат состояния: `hagi_certified_state` —
  ∃N ∀t≥N: stop ∧ gate ∧ концентрация ∧ ∃ε-репрезен-
  тативная точка (R412+R413).
- ЧЕТЫРЕ ЧИСТОТЫ вдоль отжига:
  - метрика: `certified_state_tv_tendsto` — TV → 0;
  - энергия: `certified_state_energy_tendsto` —
    ⟨E⟩_t → E*;
  - свободная энергия: `certified_state_free_energy_-
    tendsto` — F_t → E*;
  - энтропия (Нернст): `certified_state_entropy_tendsto` —
    S_t → 0;
  - избыток: `certified_state_excess_tendsto` —
    ⟨E⟩−F → 0.
- Lp-вертикаль (R498–R508, Probability/ExpChord): кирпичи `exp_chord`/`log_chord` (двухточечные хорды e^{rx} и ln), `amgm_weighted`, `young_two`, `hoelder_finite`/`hoelder_weighted`, `minkowski_finite`/`minkowski_weighted`, `lp_one_le_card`, `lp_mean_le_rms`. Моментная вертикаль R492–497 (Popoviciu/Chebyshev/Cantelli/Bhatia–Davis, Probability/MomentBounds): хвостовые критерии ранней остановки охлаждения (Var_{p_T}(E) ≤ ε_var ⟹ стоп-гейт термостата); Lp-нормы — сертифицированные границы для merge/регуляризации.

- Термостатный контракт (R510–512, GibbsFluctuations): гейт Var_{p_T}(E) ≤ ε Certified при T ≤ δ/ln(Δ²(n−1)/ε); сходимость Var→0 вдоль T_n=δ/(n+1); явное число шагов n+1 ≥ ln(Δ²(n−1)/ε) — охлаждение останавливается не раньше сертификата и не позже необходимого.
- Калориметрия: `certified_state_excess` —
  ⟨E⟩−F ≤ (Δ+T₀)·C·θ.
- Admission-гейт памяти: `admission_margin_sound` —
  ε_cert-запас = сертификат soundness: истинный выигрыш
  покрывает стоимость + риск.

## 14. Hedge-селектор и regret (Probability/MWU)

Мультипликативные веса как универсальный селектор;
температура = обратный learning rate (η = 1/T).

- Одношаговое зажатие потенциала: `mwu_potential_squeeze`
  — ηℓ_min ≤ −ln Z′ ≤ 2η⟨ℓ⟩ (hedge-ядро без рядов:
  (1+2x)(1−x) ≥ 1 ⟹ e^{−2x} ≤ 1−x).
- Телескоп: `mwu_uniform_squeeze` — потенциал кумулятивных
  потерь зажат с двух сторон при uniform-старте.
- √-балансировка: `mwu_sqrt_bound` — −ln W ≤
  2√(η⟨L⟩·ln n) при η⟨L⟩ ≤ ln n (равновесное геометри-
  ческое среднее R443-пары; классическая regret-структура).
- Гиббс = hedge: `gibbs_hedge_squeeze` — при η = 1/T
  (1/T)E_min ≤ −ln((1/n)Σe^{−E/T}) ≤ 2(1/T)⟨E⟩.
- Репрезентативность: `mwu_representative` — выборка из
  hedge-распределения e^{−ηL} репрезентативна (мост
  Хёфдинг ↔ MWU; полный граф мостов: 4 вертикали,
  все 6 пар).

## 15. PAC-Bayes мост (Probability/GibbsConcentration)

Тождество Катони замыкает термодинамику и PAC-Bayes.

- Log-декомпозиция веса: `gibbs_weight_log_decomp` —
  ln(ρ_v·n) = ln n − ln Z − E_v/T (вес = сложение
  случайности, нормировки и энергии).
- KL-тождество Катони: `gibbs_katoni_kl` —
  KL(ρ‖unif) = −ln Z − ⟨E⟩/T + ln n; вместе с
  R422 (KL = ln n − S) даёт F = ⟨E⟩ − T·S — гиббсовская
  свободная энергия выведена из PAC-Bayes.

## 16. Ядро теории информации
(Probability/GibbsConcentration)

- Второй закон в общем виде: `finite_kl_nonneg` —
  KL(ρ‖γ) ≥ 0 для любых распределений (ln u ≤ u−1
  почленно с u := γ/ρ).
- Log-sum: `log_sum_ineq` (+ `_on` на подмножествах) —
  A·ln(A/B) ≤ Σa·ln(a/b) (нормализация + R447).
- Обработка данных: `kl_data_processing` —
  KL(Tρ‖Tγ) ≤ KL(ρ‖γ) для любого сжатия T
  (fiber-разложение + log-sum по слоям).
- Выпуклость: дуга R454–R457 — вогнутость ln →
  выпуклость x·ln x → скалярная x·ln(x/y) →
  KL по первому аргументу.
- Арифметика совместных: `kl_product_additive`
  (KL аддитивен на произведении), `entropy_subadditive`
  (S(joint) ≤ S₁+S₂), `entropy_chain` (цепное правило
  Шеннона), `joint_entropy_ge_marginal` (условная
  энтропия ≥ 0), `mutual_info_nonneg` (I ≥ 0).
- Равновесие: `gibbs_free_energy_identity` —
  F = ⟨E⟩ − T·S на Гиббс-мере.

## 17. Active-Inference вертикаль
(RAG arXiv 2607.13612)

- Прокси-дихотомия: `proxy_cert_preserved` /
  `proxy_cert_lost` — нижняя оценка энтропии
  сохраняет surprise-сертификат по построению,
  верхняя строго теряет; `gibbs_cert_bridge` — мост
  к Гиббс-равновесию (R462).
- Зазор суррогат/истина: `gap_decomposition` +
  `gapII_nonpos` + `gap_graceful` — три источника
  (miscalibration/bias/slack), смещение ≤ 0 для
  нижних прокси, линейная деградация.
- Компаундинг: `compounding_bound` / `compounding_sq`
  — e_H ≤ L^H·e₀ и e_H² ≤ (L²)^H·e₀²; MPC
  horizon-one обнуляет.
- EFE-потолок: `efe_ceiling` — G = P − I ≤ P;
  state-epistemic gap = взаимная информация.
- Амортизированная политика:
  `amortized_policy_bound` — суррогатный argmin при
  равномерном зазоре c исполняет в 2c от оптимума.

## 18. Pinsker-семейство и TV-дуальность
(Probability/GibbsConcentration)

- Капстоун MWU: `mwu_regret_regimes` —
  −ln((1/n)Σe^{−ηℓ}) ≤ max(2√(η⟨ℓ⟩·lnn), 2η⟨ℓ⟩);
  η = √(lnn/⟨ℓ⟩) даёт классический 2√(⟨ℓ⟩·lnn).
- Верхнее TV: `tv_le_pos_part_kl` — TV ≤ Σ_{q<p}
  p·ln(p/q). МАТАН-ЛОВЛЯ: линейное KL ≥ TV неверно
  (контрпример 0.368 < 0.4 — Пинскер требует √).
- Бхаттачарья: `bhattacharyya_cauchy` — BC ≤ 1
  (Коши-сумм); `one_minus_bc_le_half_kl` —
  1−BC ≤ KL/2 (per-v t−1 ≤ t·ln t).
- Пинскер: `pinsker_sqrt_kl` — TV ≤ √(KL)
  (тождество |p−q| = |√p−√q|(√p+√q) + Коши);
  `neg_log_bc_le_half_kl` — BC ≥ e^{−KL/2};
  `tv_le_sqrt_one_minus_exp` — Бретаньоль–Юбер
  TV ≤ √(1−e^{−KL}) (точнее при большом KL).
- Дуальность: `tv_dual_abs` — |E_p f − E_q f| ≤ TV
  для любой 0 ≤ f ≤ 1 (расщепление + f → 1−f).
- Совместная выпуклость: `kl_joint_convex` —
  классическое замыкание ядра инфо-теории.

## 19. Дониер-Варадхан и Cramér-вертикаль
(Probability/GibbsConcentration)

- ДВ-нижняя грань: `kl_variational_lower` —
  KL ≥ E_p f − ln E_q e^{f} (софтмакс-наклон
  r = q·e^f/Z + R447); точность:
  `kl_dv_attained` (f := ln(p/q), Z = 1);
  наклон-констант: `kl_chernoff_tilt`.
- Cramér-вертикаль (2401.01148, NeurIPS 2024):
  `cramer_tilt_kl` (пороговая форма),
  `cramer_sup_le_kl` (sup-форма через csSup_le),
  `cramer_cgf` (CGF-форма с центрированием),
  `subgauss_dev_kl` (λ*-подстановка, (E−μ)²/2σ² ≤
  KL — без дифф-исчисления).
- События и масштаб: `markov_finite` (t·p({g≥t}) ≤
  E_p g), `chernoff_event` (p({g≥t}) ≤ e^{−λt}·
  E_p e^{λg}), `exp_tilt_interpol` (интерполяция
  через R454 — 3 случая), `mean_shift_tv`
  (|E_p g − E_q g| ≤ (b−a)·TV через R473),
  Hellinger: `hellinger_sq_eq_one_minus_bc`,
  `hellinger_le_half_kl`.

## Честные границы (что НЕ выведено)

- `h_emp_grow`, `h_emp_smooth`, `h_emp_lip` — измеряемые
  посылки stage-теорем; их вывод из Core-слоя открыт
  (merge и compress закрыты мостами).
- γ-дефицит mixer.gain→0 — не закрыт (контрпримерная зона).
- Плоские капстоуны (`MasterHAGI*`, `grand_synthesis`)
  депрекнуты и НЕ заменены выводом — их содержание
  поглощается условным `certified_loop`; полный вывод
  всех посылок из физики — открытый фронт.
- Closure gap: 286 library-листьев (оптимизаторы,
  attention-экономия, alignment) доказаны автономно, но
  не инстанцируют StepCert/DescentCore.Objective — их
  интеграция в certified loop открыта.
- Сертификатный веер: 8 представлений перехода не сведены
  к канонической цепочке Execution → Measurement →
  StepCert → CertifiedLoop.
- Полная Fannes-граница; anytime-Freedman (M∧V-форма).
- Lean↔Runtime property-тесты — требуют torch-рантайма.
