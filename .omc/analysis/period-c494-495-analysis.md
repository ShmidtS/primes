# Phase analysis: C494–C495 — масштабирование мини-HAGI + certified-prediction (2026-11-21)

Series HEAD 0605de04e08b2fa2c902ed4f3c32f43dc4adb0f1 (C495;
`git log` проверен: 737cda3a C492 → 8525db4 C494 → 0605de04 C495).
Виток C494–C495 закрыл roadmap-пункты C493 №1 (масштабирование
мини-HAGI) и №3-половину (монотонность sandwich-границ): мини-HAGI
укрупнён до 2-блочного trunk / 3 continual-задач / 2 grow-событий,
а certified-конвейер впервые выдаёт доказанные ПРЕДСКАЗАНИЯ (argmax),
не только certified-спуск.

## Commit one-liners (C494–C495)

- C494 8525db4 `feat:` scaled mini hagi deeper trunk three
  tasks — Hagi/Theory/MiniHagi2.lean (miniHagi2Canonical — среднее
  MSE трёх живых задач; mini_hagi2_canonical_drop — контракт
  допуска: не-рост по всем задачам + строгий спуск хотя бы по
  одной ⇒ строгий canonical-спуск; mini_hagi2_gpm_descent —
  accumulated-GPM мост: шаг, ортогональный input-span ОБЕИХ прошлых
  задач, оставляет их bench-лоссы точно инвариантными (C485-мост),
  так что спуск текущей задачи = canonical-спуск с certified zero
  forgetting); bench `--mode mini-hagi2`: 2 последовательных
  блока (L1-rms → W1 → ReLU → W2, joint finite-difference
  обучение через ОБА блока в фазе A), 3 continual-задачи (C488
  split family), 2 fiber grow (C444 margin, оба ADMIT — dim 4→6),
  accumulated GPM, тернарная квантизация (C443), Ville stop
  (C446) — ОДНИМ прогоном на живом корпусе, каждый шаг
  certify-then-commit. MSE 0.014–0.032 по фазам.
- C495 0605de04 `feat:` sandwich monotonicity and certified
  prediction — Hagi/Theory/SandwichMonotone.lean: (1) границы
  C489-sandwich монотонны по своему логиту — expLower_mono /
  expUpper_mono / exp_le_expUpper_inv (pow_le_pow_left₀);
  (2) certified_pred: разъединение sandwich-интервалов двух
  классов `hi a / ∑ lo < lo b / ∑ hi` даёт истинный порядок
  softDef через sandwich_gap_cert, а суррогат-мидпоинт
  sandwichMid точен до полуширины интервала (sandwich_mid_acc) —
  certified_argmax_strict (CertifiedArgmax) восстанавливает
  ДОКАЗАННЫЙ argmax; (3) sandwich_disjoint_example: C489-sanity
  z = (0,1,2), n = m = 10 — оба разделения точны рационально,
  предсказание (класс 2) сертифицировано.

## (а) Итог витка: масштаб держит, конвейер предсказывает

1. **Масштабирование подтверждено** — C494: архитектура выросла
   количественно (trunk 2 блока, 44 параметра, dim 4→6 через ДВА
   grow-события, 3 continual-задачи с GPM-нулём на обеих прошлых),
  и качественно canonical-цепь выдержала: admission-контракт
   (не-рост по всем + строгий спуск хотя бы одной) доказан для
   T = 3 и прокручен на живых данных — certify-then-commit
   масштабируется по задачам и по глубине trunk, а не только на
   13 шагах mini-HAGI (C492).
2. **Joint trunk-обучение в certified-цикле** — фаза A учит ОБА
   блока конечными разностями (C481-форма) и затем замораживает;
   честный пин: GPM/grow — linear-readout-утверждения над
   замороженными trunk-фичами (docstring-pinned).
3. **Certified-prediction — новая вершина семантики** — C495:
   до сих пор конвейер сертифицировал СПУСК (обучение); теперь
   разъединение рациональных sandwich-интервалов сертифицирует
   АРГМАКС (предсказание) с точным рациональным примером.
   Certify-then-commit распространён с обучения на инференс.

## (б) Честные остатки (pins)

- **gpm2-фаза все HOLD** — проекция выжала доступное пространство
  признаков: дальнейший continual-спуск в span-ортогональном
  подпространстве невозможен; честный телеметрический исход, но
  демонстрация «GPM растёт дальше» требует больше задач/ширины.
- **Суммарная p̂-монотонность не пин** — C495 монотонность границ
  по логиту ≠ монотонность нормализованной оценки lo v / ∑ hi
  по своему z v (числитель и знаменатель растут вместе —
  честная негативная фиксация sandwich_lower_anti_mono);
  Bernoulli-монотонность по n, m (точность растёт с n, m) —
  остаётся открытой как и на C489.
- **MSE-достижения 0.014–0.032 — прогонные числа живого
  корпуса** (средозависимого, прунинг между сессиями);
  переносимость не сертифицирована.
- **Certified-prediction пока на 3-классовом sanity-примере** —
  мост к реальному argmax над корпусом (связка с cert-sandwich
  C491-бенчем) — следующий шаг.

## (в) Метрики витка (замер C496, READ-ONLY)

- **Freeze verify (HEAD 0605de04, C495-гейты)**: PASS,
  **8555** declarations, 0 aliased, nothing lost/changed
  (8541 → +14: MiniHagi2 ×3 + SandwichMonotone ×11).
- **Index regen (этот бит C496)**: exit 0, дрейф пойман и
  закоммичен: закоммиченный индекс (C493) 570 modules / 12699
  theorems / 4692 defs / 1202 noncomputable / 489 Proven;
  фактический **572 / 12713 / 4697 / 1204 / Proven 491**
  (+MiniHagi2 C494: 3/1/Proven, +SandwichMonotone C495:
  11/4/Proven). Паттерн дрейфа в feat-битах — 6-й раз подряд
  (C478, C479–482, C484–485, C487–489, C491–492, теперь
  C494–C495).
- **Streak посадок**: 37 (по C493) + C494 + C495 = **39**,
  freeze PASS на каждом; с посадкой C496 → 40 подряд.

## (г) Roadmap следующего витка (ранжировано к цели)

1. **Мини-HAGI против реального тренера HAGI_v2** —
  selfloop-телеметрия как задача/бенчмарк для canonical-цепи:
   прямое сравнение certified-предсказания (C495 argmax) с
   фактическим исходом эксперимента. Rank 1: единственный способ
   узнать, certify-then-commit реально предсказывает мир, а не
   только sanity-примеры; закрывает пин selfloop-intake (C486 №3).
2. **GPM-расширение при исчерпании** — gpm2-фаза все HOLD:
   проекция выжала пространство. Relaxed-projection /
   регуляризация (допуск малого контролируемого забывания с
   сертификатом на его границу) — теория нового класса.
   Rank 2: следующий содержательный барьер масштабирования.
3. **Upstream Mathlib SVD-пакет** — continual-эру машину
   (Gram-Schmidt rank/SVD) как Mathlib PR. Rank 3: внешний
   цикл; зависит от стабильности API.
4. **Imports финал + Ф6-хвост** — bare imports и производные
   хвосты. Rank 4: гигиена, компаунд-ускорение.
5. **Паломар-registry карточки ключевых результатов** —
   мини-HAGI + certified-prediction как внешний вклад.
   Rank 5: внешний цикл, репутационный.
6. **Paper-черновик certify-then-commit** — форма научной
   публикации (mini-HAGI + sandwich-CE + certified-prediction
   как связная история). Rank 6: зреет, но после №1.

Top-3 на следующий виток: (1) мини-HAGI vs HAGI_v2-телеметрия,
(2) GPM relaxed-projection, (3) upstream SVD-пакет.

## Honest limits

- Масштаб C494 — по-прежнему miniature: 44 параметра, живой
  корпрус ~26–31 точка, линейный readout над замороженным trunk;
  перенос на реальный масштаб не автоматический.
- Certified-prediction C495 — точный рациональный пример, не
  бенч на корпусе; связка с cert-sandwich-бенчем не построена.
- Все HOLD/не-срабатывания (gpm2-стоп, quant, Ville) — честные
  исходы, но «позитивные» ветки (реальный reject-then-recover,
  анти-деградация) в этом витке не демонстрировались.
- Freeze 8555 — из C495-гейтов (тот же HEAD); index regen
  выполнен в этом бите C496 (READ-ONLY для кода, индекс +
  анализ — единственный дифф).
