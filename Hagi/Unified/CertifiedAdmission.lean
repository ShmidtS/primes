/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.PairedGain
import Hagi.Data.ValWindows
import Hagi.Data.HoldoutPurity

/-!
# CertifiedAdmission — три посылки сертификата приёма и их статус в коде

Сертификат приёма блока (admit_false_le, PairedGain) опирается на три посылки; каждая
проверяется своим модулем:

1. holdout — суффикс чистого хвоста нового домена (Hagi/Data/HoldoutPurity.lean) —
   выполнено после de61271;
2. окна независимы: `step ≥ k` (indep_threshold (Hagi/Data/ValWindows.lean)) — нарушено
   для доменов короче `256·k` байт (`k = 64`: 16384) — proposal 17;
3. гейт — EB-радиус (PairedGain) — выполнено (paired_margin_eb в trunk_ops).

* `admission_premises_iff` — посылки (1)+(2) в явном виде;
* `short_domain_breaks` — при `k > 1` и `n < 256·k` посылка (2) ложна.
-/

namespace Hagi.Unified.CertifiedAdmission

/-- Посылки сертифицированного приёма (unified.py _old_domains_ce_vec +
paired_margin_eb): holdout — суффикс чистого хвоста (Hagi/Data/HoldoutPurity.lean),
окна не перекрываются (indep_threshold (Hagi/Data/ValWindows.lean)), EB-гейт
(admit_false_le (Hagi/Probability/PairedGain.lean)). -/
theorem admission_premises_iff (n k h tailLen : ℕ) :
    (h ≤ tailLen ∧ k ≤ max 1 (n / 256)) ↔ h ≤ tailLen ∧ (k ≤ 1 ∨ 256 * k ≤ n) := by
  rw [Hagi.Data.ValWindows.indep_threshold]
/-- Состояние кода: (1) выполнено после de61271; (2) нарушено при `n < 256·k`
с `k > 1` (k = 64: домены короче 16384 байт — proposal 17); (3) выполнено. -/
theorem short_domain_breaks (n k : ℕ) (hk : 1 < k) (hn : n < 256 * k) :
    ¬ (k ≤ 1 ∨ 256 * k ≤ n) := by
  rintro (h | h)
  · omega
  · omega

end Hagi.Unified.CertifiedAdmission
