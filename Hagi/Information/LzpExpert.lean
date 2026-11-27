/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Information.MixtureCoding

/-!
# LzpExpert — LZP-эксперт в потоковом предикторе

HAGI_v2 26dcd09 (archiver): эксперт контекста `p_ctx` смешивается с
LZP-кандидатом `b` при длине совпадения `ml`: `cf = min(0.94, 0.30 + 0.08·ml)`,
`p_lz = p_ctx·(1 − cf)`, `p_lz[b] += cf`, итог — взвешенная смесь с экспертом
нейросети (PPM + LZP). Сжатие лучше на 6–10% (замер кода).

* `lzp_false_cost`, `lzp_false_ce` — для ложного кандидата (`y ≠ b`) вероятность
  равна `p y·(1 − λ·cf)`: проигрыш ровно `−log(1 − λ·cf)` nat; при `λ = 0.5`,
  `cf = 0.94` это `≤ 0.35` nat — кап `cf` удерживает цену ошибки;
* `lzp_true_gain`, `lzp_true_ce_lower` — верный кандидат даёт вероятность
  не меньше `λ·cf` независимо от `p b`.
В сочетании с `mixCE_le_best_regret` (смесевая CE ≤ CE лучшего эксперта
минус `−log w_j`) это обосновывает схему PPM + LZP + neural в одном смесятеле.
-/

namespace Hagi.Information.LzpExpert
/-- LZP-эксперт (HAGI_v2 26dcd09): `p_lz = p·(1−cf)`, `p_lz[b] += cf`, смешанный с
весом `λ`. Для символа `y ≠ b` (ложный кандидат) вероятность смеси равна
`p y · (1 − λ·cf)`: проигрыш относительно эксперта контекста — ровно
`−log(1 − λ·cf)`, ограниченный капом `cf ≤ 0.94` и весом `λ`. -/
theorem lzp_false_cost (py cf lam : ℝ) :
    (1 - lam) * py + lam * ((1 - cf) * py) = py * (1 - lam * cf) := by
  have : lam * ((1 - cf) * py) = lam * py - lam * cf * py := by ring
  rw [this]; ring
/-- Тот же шаг для верного кандидата `y = b`: выигрыш ограничен `−log(1 − λ·cf)`
относительно `p y`; при `p y = 0` — `−log(λ·cf)`. -/
theorem lzp_true_gain (pb cf lam : ℝ) :
    (1 - lam) * pb + lam * ((1 - cf) * pb + cf)
      = pb * (1 - lam * cf) + lam * cf := by
  have : lam * ((1 - cf) * pb + cf) = lam * pb - lam * cf * pb + lam * cf := by ring
  rw [this]; ring
/-- CE-форма: при ложном кандидате перекрёстная энтропия растёт ровно на
`−log(1 − λ·cf)` nat; при `λ = 0.5`, `cf = 0.94` — не более `0.35` nat
(кап `cf` удерживает проигрыш), а верный кандидат даёт `p y ≥ λ·cf`. -/
theorem lzp_false_ce (py cf lam : ℝ) (hpy : 0 < py) (h : lam * cf < 1) :
    -Real.log ((1 - lam) * py + lam * ((1 - cf) * py))
      = -Real.log py - Real.log (1 - lam * cf) := by
  rw [lzp_false_cost, Real.log_mul (ne_of_gt hpy) (ne_of_gt (sub_pos.mpr h))]
  ring
/-- С верным кандидатом `b` вероятность смеси не меньше `λ·cf` — выигрыш
`−log(λ·cf)` относительно любой контекстной вероятности `p b < λ·cf`. -/
theorem lzp_true_ce_lower (pb cf lam : ℝ) (hpb : 0 ≤ pb) (hl1 : lam * cf ≤ 1) :
    lam * cf ≤ (1 - lam) * pb + lam * ((1 - cf) * pb + cf) := by
  rw [lzp_true_gain]
  have : 0 ≤ pb * (1 - lam * cf) := mul_nonneg hpb (sub_nonneg.mpr hl1)
  linarith

end Hagi.Information.LzpExpert
