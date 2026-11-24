# Phase analysis: C657–C660 — эра «release v1.0» (2026-11-24)

Series HEAD 4408912f (C660 ← C659 85c7c670 ← C658 4e4ef126 ← C657
65d9f11e; tree clean). C661 — docs: READ-ONLY, один docs-commit, freeze
identity 8959. Закрыты roadmap C656 top-1 (paper v1.0), top-2 (Card
15–16 + PALOMAR), top-3 (U1; U2 открыт), (4) holdout-гейт (C660).

## (а) Эра: certified-паспорт release v1.0

1. **C657 useful first step (+1 def, +7 theorem).** Носитель: шаги
   `bη` с линейным смещением логитов `η·D`, `R` — range-константа,
   `a = ⟨softmax (L b) − onehot, D⟩`; `linDrop a R η = −(η·a + η²·R²/8)`.
   Доказано: `useful_first_step` (drop(η*) = 2a²/R², η* = 4|a|/R²),
   `useful_eta_le` (максимум единственный), `exists_useful_eta`
   (stepEps < 2a²/R²), `first_step_useful_certified`,
   `first_step_strict_improves`; негатив `no_signal_no_drop`.
   Смысл (главный результат эры): рост не только безопасен (obj ≤
   fOld, C642–C646), но выгоден с ПЕРВОГО шага ⟺ residual-сигнал
   a < 0 и 2a²/R² > stepEps.
2. **C658 Cards 15–17 + niche** (1331 results, 0 пересечений);
   теорем нет.
3. **C659 paper v1.0.** §0 — карта 23 мостов по 7 слоям (growth,
   step, reading, transfer, compression, probability, rollback);
   173 якоря, сверены `.tmp/C659/audit.py` @4e4ef126, freeze 8956.
   Статусы exact / conditional / honest gap — в таблице.
4. **C660 HoldoutGateTwoWay (+3 theorem).** Код-гейт: GROW iff
   holdoutMean(new) < holdoutMean(old) − 1e-4, одна выборка ≤ 512
   окон, peeking (лучшее состояние блока выбирается по holdout).
   `holdout_gate_two_way`: P ≥ 1 − |Θ|·2·exp(−2k(ε/B)²) [гейт принял
   ⇒ pop_new ≤ pop_old + 2ε − margin]; `_delta`: |Θ| ≤ N,
   log(2N/δ) ≤ 2k(ε/B)² ⇒ P ≥ 1 − δ. Union bound покрывает peeking;
   peeking; `anytime_catoni` неприменим (супермартингал по шагу
   выборки, а код заглядывает в одну выборку).
5. **Паспорт, 7 слоёв (теорема ↔ код):** рост — identity-гейт exact,
   growthGate honest gap; шаг — range-ветка exact, certified-шаг и
   useful-first-step conditional (h1, a < 0); чтение — порядок окон
   exact, floor/иерархия — bench-twin; перенос — iff + γ*
   conditional (quad-модель); компрессия — ideal coder conditional,
   range coder honest gap; вероятность — EB/union conditional (iid,
   независимость раундов); rollback — backtracking/repair exact как
   предикаты, post-warmup conditional (h1). C660 holdout — conditional
   (iid-модель); строки в paper §0 ещё НЕТ.
6. **Рекомендация коду (из C660).** ε/B = √(log(2N/δ)/(2k)). При
   k = 512, δ = 0.05: N = 2 ⇒ ε = 0.065B (2ε = 0.13B); N = 10 ⇒
   ε = 0.076B (2ε = 0.153B); witness C660 (ε = B/8) ⇒ 2ε = 0.25B —
   почти вакуумный. Для ε = 0.05B, δ = 0.05, |Θ| = 10:
   k ≥ ln(2·10/0.05)/(2·0.05²) = 5.991/0.005 ⇒ **k ≥ 1199 окон**
   (N = 2 ⇒ 877); код режет holdout до 512 ⇒ нетривиальный ε
   недостижим на текущем срезе.

## (б) Метрики: freeze 8948 → 8959 (+11, 0 lost/changed)

- 8948 → 8956 (C657: +7 theorem, +1 def); identity (C658, C659:
  docs); 8956 → 8959 (C660: +3 theorem). Карточки 17; paper v1.0 —
  23 моста, 173 якоря. AllAxioms PASS (C657, C660), CI PASS (C660).

## (в) Honest-открытые

- **U2** (высокая): «блок expressive ⇒ reachable drop ≥ δ» — нужна
  гарантия на non-convex ландшафте многих шагов + UAT на конечной
  сетке; в primes ни того, ни другого. Код: W1 random ⇒ a ≠ 0 п.н.
  — вероятностный факт кода, не теорема.
- **Chain rule a < 0** (высокая): ⟨g, d⟩ > 0 (C655) ⇒ a < 0 — НЕ
  формализовано; a < 0 и линейность по η (JVP при Wo = 0) — гипотезы.
- **Holdout** (высокая): iid — модель (код — детерминированный
  связный срез, окна перекрываются); CE ∉ [0,B] без нормировки;
  N = 2 + число checkpoint-оценок — число из кода; связь с
  CommitGate.gen ≥ 2ε не формализована; k = 512 ⇒ вакуумность.
- **WOR / iid / независимость раундов** (средняя): код сэмплит без
  возвращения и обновляет θ между раундами.
- **Range-coder round-trip** (высокая): только карточка и тесты.
- **Warm-up h1** (средняя): код греет голым Adam.

## (г) HAGI_v2 recheck — HEAD b3740e0 (wave 258) = карточечный

`git log b3740e0..HEAD` пуст, волн 259+ нет; код читался через
`git show` в C657/C660 (lm.py:581-601 @ca52eb4, unified.py:504-581
@b3740e0). Freeze 8959 не затронут.

## (д) Roadmap

1. **Метатеория v3.4** (Lean, high): `hagi_master_v34` = v3.3 +
   (12) useful-first-step + (13) holdout-two-way + (14)
   Adam-first-step; конъюнкция делегатов. Потребитель есть (paper §0
   → канон), не YAGNI; v3.3 не трогать.
2. **PROPOSAL-holdout-size** (docs → user-push, high): k ≥
   log(2N/δ)/(2(ε/B)²); k ≥ 1199 (ε = 0.05B, δ = 0.05, N = 10), 877
   (N = 2); код держит 512. Решение по срезу — owner кода.
3. **Chain rule a < 0** (Lean, med-high): гипотеза-лемма
   Jᵀ-согласованности на нашем носителе (⟨g, d⟩ > 0 ⇒ a < 0) —
   связка Adam-first-step ↔ useful-first-step; закрывает honest (1)
   C657. Сначала statement-кандидат, потом proof.
4. **U2** (statement-кандидат, med): finite-grid UAT — «для любой
   функции на конечном множестве ∃ блок класса F с CE < ε»; честно:
   только существование параметров, не достижимость.
5. **Paper v1.1** (docs, med): строка C660 в §0 (24 моста), v3.4 в
Top-3: (1) v3.4; (2) PROPOSAL-holdout-size; (3) chain rule a < 0.

Honest limits: READ-ONLY — lake build не запускался; факты по STATUS.md,
Lean-файлам HEAD и gates.log; HAGI_v2 — только `git show`.
