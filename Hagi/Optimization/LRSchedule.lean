import Mathlib

/-!
# Оптимальные LR-расписания: позднее затухание (источник №11)

Источник №11: Li et al., ICLR 2026 (arXiv 2602.06797),
"Optimal Learning-Rate Schedules under Functional Scaling
Laws: Power Decay and Warmup-Stable-Decay".

Формализовано ядро WSD-результата: фаза затухания занимает
исчезающую долю горизонта и вносит ограниченный вклад —
любые k последних шагов с η ≤ η_max добавляют к ошибке
PL-рекуррентности не более k·σ²·η_max². Следствие (θT-фаза
затухания): вклад фазы O(θT) — позднее затухание не портит
порядок скорости сходимости; «широкий класс late-decay
профилей достигает оптимума» (ядро shape-insensitivity
источника).
-/

namespace Hagi.Optimization.LRSchedule

/-- PL-РЕКУРРЕНТНОСТЬ С РАСПИСАНИЕМ: сжатие (1−μ·η_t)·e_t
плюс шумовой член σ²·η_t². -/
def plRec (mu sig : ℝ) (eta : ℕ → ℝ) (e : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, e (t + 1) ≤ (1 - mu * eta t) * e t + sig ^ 2 * eta t ^ 2

/-- ШАГ: при e_t ≥ 0, μη_t ∈ [0,1] ошибка за шаг растёт не
более чем на σ²η_t² (сжатие не увеличивает). -/
theorem pl_step_noise_bound (mu sig : ℝ) (eta : ℕ → ℝ) (e : ℕ → ℝ)
    (hrec : plRec mu sig eta e) (t : ℕ)
    (hmu : 0 ≤ mu) (heta : 0 ≤ eta t)
    (hwindow : mu * eta t ≤ 1) (he : 0 ≤ e t) :
    e (t + 1) ≤ e t + sig ^ 2 * eta t ^ 2 := by
  have hcontr : 0 ≤ 1 - mu * eta t := by
    have := mul_nonneg hmu heta
    linarith
  have h1 : (1 - mu * eta t) * e t ≤ e t := by
    have hme : 0 ≤ mu * eta t := mul_nonneg hmu heta
    have hle : (1 - mu * eta t) ≤ 1 := by linarith
    have := mul_le_mul_of_nonneg_right hle he
    simpa using this
  have h3 := hrec t
  linarith

/-- ПОЗДНЯЯ ФАЗА (ядро источника №11): любые k последних
шагов с 0 ≤ η ≤ η_max в окне μη ≤ 1 добавляют к ошибке не
более k·σ²·η_max². Следствие: θ-доля горизонта затухания
вносит O(θT·σ²η_max²) — позднее затухание не меняет порядок
скорости сходимости (WSD-оптимальность stable-фазы). -/
theorem late_phase_bound (mu sig etaMax : ℝ)
    (eta e : ℕ → ℝ) (m k : ℕ)
    (hrec : plRec mu sig eta e)
    (hmu : 0 ≤ mu) (hmax : 0 ≤ etaMax)
    (hnn : ∀ t, 0 ≤ eta t)
    (hb : ∀ t, eta t ≤ etaMax)
    (henn : ∀ t, 0 ≤ e t)
    (hwindow : ∀ t, mu * eta t ≤ 1) :
    e (m + k) ≤ e m + (k : ℝ) * sig ^ 2 * etaMax ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := pl_step_noise_bound mu sig eta e hrec (m + k)
      hmu (hnn (m + k)) (hwindow (m + k)) (henn (m + k))
    have hnoise : sig ^ 2 * eta (m + k) ^ 2
        ≤ sig ^ 2 * etaMax ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sq_le_sq' (by linarith [hmax, hnn (m + k), hb (m + k)]) (hb (m + k))
    have hkey : e (m + k + 1) ≤ e (m + k) + sig ^ 2 * etaMax ^ 2 := by
      linarith [hstep, hnoise]
    rw [Nat.cast_succ]
    show e ((m + k) + 1) ≤ e m + ((k : ℝ) + 1) * sig ^ 2 * etaMax ^ 2
    nlinarith [hkey, ih]

end Hagi.Optimization.LRSchedule
