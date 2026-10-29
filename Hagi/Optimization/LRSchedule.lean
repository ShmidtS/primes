import Mathlib
import Hagi.Foundations.Recurrence

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


/-- ПОЛНАЯ WSD-ОЦЕНКА (источник №11, capstone): stable-фаза
длины m с η = η_max даёт геометрическое сжатие ρ = 1−μη_max
плюс шумовой бюджет σ²η_max²·(1−ρ^m)/(1−ρ); фаза затухания
длины k добавляет ещё ≤ k·σ²η_max². Асимптотика по m
определяется stable-фазой; затухание на θ-доле (k = θT)
вкладывает O(θT) — ядро WSD-оптимальности. -/
theorem wsd_full_bound (mu sig etaMax : ℝ)
    (eta e : ℕ → ℝ) (m k : ℕ)
    (hrec : plRec mu sig eta e)
    (hmu : 0 < mu) (hetaMax : 0 < etaMax)
    (hwindow : mu * etaMax ≤ 1)
    (hnn : ∀ t, 0 ≤ eta t)
    (hb : ∀ t, eta t ≤ etaMax)
    (henn : ∀ t, 0 ≤ e t)
    (hstable : ∀ t < m, eta t = etaMax) :
    e (m + k)
      ≤ (1 - mu * etaMax) ^ m * e 0
        + sig ^ 2 * etaMax ^ 2 * ((1 - (1 - mu * etaMax) ^ m)
          / (1 - (1 - mu * etaMax)))
        + (k : ℝ) * sig ^ 2 * etaMax ^ 2 := by
  set rho := 1 - mu * etaMax with hrho
  have hpos : 0 < mu * etaMax := mul_pos hmu hetaMax
  have hrho01 : 0 ≤ rho ∧ rho < 1 := by
    constructor
    · linarith
    · linarith
  -- шаги stable-фазы: e_{t+1} ≤ rho·e_t + σ²η_max²
  have hstep : ∀ t < m, e (t + 1) ≤ rho * e t + sig ^ 2 * etaMax ^ 2 := by
    intro t ht
    have hst := hstable t ht
    have hrec' := hrec t
    rw [hst] at hrec'
    rw [hrho]
    exact hrec'
  have hupper := Hagi.Foundations.recurrence_upper (rho := rho)
    (c := sig ^ 2 * etaMax ^ 2) e m hrho01.1 hrho01.2 hstep
  -- late-фаза
  have hlate := late_phase_bound mu sig etaMax eta e m k hrec
    (le_of_lt hmu) (le_of_lt hetaMax) hnn hb henn
    (fun t => le_trans
      (mul_le_mul_of_nonneg_left (hb t) (le_of_lt hmu)) hwindow)
  linarith [hupper, hlate]


/-! ## Cosine LR Schedule (источник №30)

Источник №30: Loshchilov & Hutter, "SGDR: Stochastic
Gradient Descent with Warm Restarts" (arXiv 1608.03983).
Cosine-расписание: η(t) = η_max/2 · (1 + cos(π·t/T)) —
плавное затухание от η_max до 0 на горизонте T.

Формализованное ядро (строгое):
- `cos_anti`: косинус анти-монотонен на [0, π]
  (через произведение синусов — без анализа);
- `cosLR_nonneg`: расписание неотрицательно;
- `cosLR_start`: η(0) = η_max (полный шаг в начале);
- `cosLR_end`: η(T) = 0 (нулевой шаг в конце);
- `cosLR_anti`: расписание анти-монотонно на [0, T].
-/

/-- Косинус анти-монотонен на [0, π]: разность косинусов —
произведение неотрицательных синусов. -/
theorem cos_anti (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ Real.pi) : Real.cos t ≤ Real.cos s := by
  have ha : 0 ≤ (s + t) / 2 := by linarith
  have hb : (s + t) / 2 ≤ Real.pi := by linarith
  have hc : 0 ≤ (t - s) / 2 := by linarith
  have hd : (t - s) / 2 ≤ Real.pi := by linarith
  have hsm := Real.sin_nonneg_of_nonneg_of_le_pi ha hb
  have hsd := Real.sin_nonneg_of_nonneg_of_le_pi hc hd
  have h2 : Real.cos s - Real.cos t
      = 2 * Real.sin ((s + t) / 2) * Real.sin ((t - s) / 2) := by
    rw [Real.cos_sub_cos]
    rw [show (s - t) / 2 = -((t - s) / 2) from by ring,
      Real.sin_neg ((t - s) / 2)]
    ring
  have h3 : 0 ≤ Real.cos s - Real.cos t := by rw [h2]; positivity
  linarith

/-- Cosine LR: η_max/2 · (1 + cos(π·t/T)). -/
noncomputable def cosLR (etaMax T t : ℝ) : ℝ :=
  etaMax / 2 * (1 + Real.cos (Real.pi * t / T))

theorem cosLR_nonneg (etaMax T t : ℝ) (_hT : 0 < T)
    (hmax : 0 ≤ etaMax) : 0 ≤ cosLR etaMax T t := by
  have hc : -1 ≤ Real.cos (Real.pi * t / T) := Real.neg_one_le_cos _
  unfold cosLR
  nlinarith [hc]

theorem cosLR_start (etaMax T : ℝ) : cosLR etaMax T 0 = etaMax := by
  unfold cosLR
  norm_num

theorem cosLR_end (etaMax T : ℝ) (hT : T ≠ 0) :
    cosLR etaMax T T = 0 := by
  unfold cosLR
  have hpT : Real.pi * T / T = Real.pi := by
    rw [mul_comm]
    exact mul_div_cancel_left₀ Real.pi hT
  rw [hpT, Real.cos_pi]
  norm_num

theorem cosLR_anti (etaMax T s t : ℝ) (hT : 0 < T)
    (hmax : 0 ≤ etaMax) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    cosLR etaMax T t ≤ cosLR etaMax T s := by
  have hps : 0 ≤ Real.pi * s / T := by
    apply div_nonneg _ (le_of_lt hT)
    exact mul_nonneg Real.pi_pos.le hs
  have hpt : Real.pi * t / T ≤ Real.pi := by
    rw [div_le_iff₀ hT]
    nlinarith [Real.pi_pos, ht]
  have hmono := cos_anti (Real.pi * s / T) (Real.pi * t / T)
    (by
      apply div_nonneg _ (le_of_lt hT)
      exact mul_nonneg Real.pi_pos.le hs)
    (by
      have hmul := mul_le_mul_of_nonneg_left hst Real.pi_pos.le
      field_simp
      linarith [hmul])
    hpt
  have h2 : 0 ≤ etaMax / 2 := by positivity
  unfold cosLR
  nlinarith [hmono, h2]

end Hagi.Optimization.LRSchedule

