import Mathlib.Tactic
import Hagi.State.CanonicalTrainState

/-!
# TrainTrajectory — траекторная теорема на CanonicalTrainState
(user audit 5.3, A15 Step 5.3 = rank #2)

Финальная траекторная теорема, учитывающая численную погрешность
(BF16/ternary) реального бэкенда, делающая носитель
`CanonicalTrainState` load-bearing:

* `obj_telescope_err` — общий телескоп с аддитивной ошибкой на шаг:
  ЛИНЕЙНОЕ накопление (треугольник по значению цели, без
  квадратичного раздувания через расстояния состояний);
* `Trajectory T` — карта траектории: T сертифицированных
  Progress-шагов, каждый несёт `FullStepCert` на ПОЛНОМ
  состоянии (веса + Adam-буферы);
* `trajectory_descent` — телескоп: `fullObjective(θ_T) ≤
  fullObjective(θ_0) − ∑ drop_j`, ЯВНАЯ константа c(T) = ∑ drops
  (индукция той же формы, что ядерная `kernel_core` само ядро
  лежит в Unified layer 6 и не импортируемо со слоя State = 3);
* `RoundedFullStepCert` / `RoundedTrajectory` — исполненный шаг
  реального бэкенда: спуск полной цели минус drop ПЛЮС аддитивная
  ошибка исполнения `execErr` (округление BF16/ternary), плюс ошибка
  считывания `rho` между измеренной и истинной целью;
* `rounded_trajectory_bound` — ТРАЕКТОРНАЯ ТЕОРЕМА:
  `f_true(θ_T) ≤ f_true(θ_0) − ∑ drop_j + ∑ execErr_j + 2ρ`;
* `rounded_trajectory_uniform` — замкнутая форма c(T):
  `f_true(θ_T) ≤ f_true(θ_0) − T·δ + T·ε + 2ρ`;
* `coord_err_bound` — пин численной погрешности (binder-форма):
  координатная ошибка ≤ s/2 (concrete instantiation —
  `Hagi.Runtime.qTern_error_in`, qTern in-range; кросс-папочный
  импорт Runtime→State запрещён LayerLint, см. TernaryExact) +
  L-липшицевость цели дают ошибку шага ≤ L·m·s/2;
* `with_holds_bound` — форма с Hold: Hold — тождество
  (`hold_rollback_total`), вклад 0; суммы по всем шагам, где
  hold-шаги вносят нулевые d/e — эффективных шагов T' ≤ T.

Честные пины (premise-form): `execErr` per backend — binder;
координатная ошибка s/2 — binder с конкретной instantiation в
`Hagi.Runtime.TernaryExact.qTern_error_in` (точная, без посылок,
кроме in-range); липшицева константа L для `fullObjective` —
binder (в TrainState нет леммы Липшица для energy); `rho` —
binder.
-/

set_option relaxedAutoImplicit false

namespace Hagi.State

variable {n a e q r c k : ℕ}

/-! ## Общий телескоп с аддитивной ошибкой (линейное накопление) -/

/-- ТЕЛЕСКОП С ОШИБКОЙ: цепочка неравенств `g(j+1) ≤ g(j) − d_j +
e_j` даёт `g(T) ≤ g(0) − ∑ d + ∑ e`. Накопление ошибки ЛИНЕЙНОЕ:
каждая `e_j` входит один раз (треугольник по значению, не через
норму состояния — нет квадратичного раздувания). -/
theorem obj_telescope_err (T : ℕ) (g d e : ℕ → ℝ)
    (h : ∀ j < T, g (j + 1) ≤ g j - d j + e j) :
    g T ≤ g 0 - ∑ j ∈ Finset.range T, d j + ∑ j ∈ Finset.range T, e j := by
  revert h
  induction T with
  | zero => intro _; simp
  | succ T ih =>
    intro h
    have hT := h T (Nat.lt_succ_self T)
    have hrest := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

/-! ## Progress-only траектория и телескоп -/

/-- Карта траектории : T сертифицированных Progress-шагов
на каноническом состоянии — каждый шаг несёт `FullStepCert` на
ПОЛНОМ состоянии (веса + Adam-буферы). -/
structure Trajectory (T : ℕ) where
  /-- Состояния траектории: `states j` — после j шагов. -/
  states : ℕ → CanonicalTrainState n a e q r c k
  /-- Сертификат каждого шага. -/
  certs : ∀ j < T, FullStepCert (states j) (states (j + 1))

/-- Drop шага j как полная функция (kernel-паттерн суммы по
`ℕ → ℝ`, доказательство равенства отдельно). -/
noncomputable def Trajectory.stepDrop (T : ℕ)
    (tr : Trajectory (n := n) (a := a) (e := e) (q := q) (r := r)
      (c := c) (k := k) T) (j : ℕ) : ℝ :=
  if h : j < T then (tr.certs j h).drop else 0

theorem Trajectory.stepDrop_eq (T : ℕ)
    (tr : Trajectory (n := n) (a := a) (e := e) (q := q) (r := r)
      (c := c) (k := k) T) {j : ℕ} (hj : j < T) :
    tr.stepDrop T j = (tr.certs j hj).drop :=
  by simp [stepDrop, hj]

/-- ТЕЛЕСКОП (progress-only run): после T сертифицированных шагов
полная цель не выше начальной минус сумма заявленных drop'ов. ЯВНАЯ
константа c(T) = ∑_{j<T} drop_j. -/
theorem trajectory_descent (T : ℕ)
    (tr : Trajectory (n := n) (a := a) (e := e) (q := q) (r := r)
      (c := c) (k := k) T) :
    fullObjective (tr.states T) ≤ fullObjective (tr.states 0)
      - ∑ j ∈ Finset.range T, tr.stepDrop T j := by
  have key : ∀ j < T, fullObjective (tr.states (j + 1))
      ≤ fullObjective (tr.states j) - tr.stepDrop T j + (0 : ℝ) :=
    fun j hj => by
      have hd := (tr.certs j hj).descent
      rw [tr.stepDrop_eq T hj]
      linarith
  have h := obj_telescope_err T (fun j => fullObjective (tr.states j))
    (tr.stepDrop T) (fun _ => (0 : ℝ)) key
  simpa using h

/-! ## Исполненный шаг с численной погрешностью -/

/-- Сертификат ИСПОЛНЕННОГО шага реального бэкенда (BF16/ternary):
спуск полной цели минус drop плюс АДДИТИВНАЯ ошибка исполнения
`execErr` (округление). `FullStepCert` — идеализированный
частный случай (execErr = 0). -/
structure RoundedFullStepCert (s s' : CanonicalTrainState n a e q r c k) where
  /-- Заявленный спуск полной цели. -/
  drop : ℝ
  /-- Спуск положителен. -/
  drop_pos : 0 < drop
  /-- Ошибка исполнения (округление бэкенда). -/
  execErr : ℝ
  /-- Ошибка неотрицательна. -/
  execErr_nonneg : 0 ≤ execErr
  /-- Спуск НА ПОЛНОМ состоянии с учётом округления. -/
  execDescent : fullObjective s' ≤ fullObjective s - drop + execErr

/-- Траектория исполненных шагов + канал считывания: измеренная
`fullObjective` отличается от истинной цели (интерпретированный
objective точного real-state бэкенда) не более чем на `rho` в каждой
точке 0..T. -/
structure RoundedTrajectory (T : ℕ) where
  /-- Состояния траектории. -/
  states : ℕ → CanonicalTrainState n a e q r c k
  /-- Истинная цель точного бэкенда, индексирована шагом. -/
  trueObjective : ℕ → ℝ
  /-- Сертификат каждого исполненного шага. -/
  certs : ∀ j < T, RoundedFullStepCert (states j) (states (j + 1))
  /-- Ошибка считывания (measured vs true). -/
  rho : ℝ
  /-- Неотрицательность ошибки считывания. -/
  rho_nonneg : 0 ≤ rho
  /-- Канал считывания в каждой точке 0..T. -/
  readout : ∀ j ≤ T, |fullObjective (states j) - trueObjective j| ≤ rho

/-- Drop исполненного шага j как полная функция. -/
noncomputable def RoundedTrajectory.stepDrop (T : ℕ)
    (tr : RoundedTrajectory (n := n) (a := a) (e := e) (q := q) (r := r)
      (c := c) (k := k) T) (j : ℕ) : ℝ :=
  if h : j < T then (tr.certs j h).drop else 0

/-- Ошибка исполнения шага j как полная функция. -/
noncomputable def RoundedTrajectory.stepExecErr (T : ℕ)
    (tr : RoundedTrajectory (n := n) (a := a) (e := e) (q := q) (r := r)
      (c := c) (k := k) T) (j : ℕ) : ℝ :=
  if h : j < T then (tr.certs j h).execErr else 0

theorem RoundedTrajectory.stepDrop_eq (T : ℕ)
    (tr : RoundedTrajectory (n := n) (a := a) (e := e) (q := q) (r := r)
      (c := c) (k := k) T) {j : ℕ} (hj : j < T) :
    tr.stepDrop T j = (tr.certs j hj).drop :=
  by simp [stepDrop, hj]

theorem RoundedTrajectory.stepExecErr_eq (T : ℕ)
    (tr : RoundedTrajectory (n := n) (a := a) (e := e) (q := q) (r := r)
      (c := c) (k := k) T) {j : ℕ} (hj : j < T) :
    tr.stepExecErr T j = (tr.certs j hj).execErr :=
  by simp [stepExecErr, hj]

/-- ТРАЕКТОРНАЯ ТЕОРЕМА : после T исполненных
сертифицированных шагов ИСТИННАЯ цель ограничена начальной минус
сумма drop'ов ПЛЮС ЛИНЕЙНАЯ сумма ошибок исполнения ПЛЮС удвоенная
ошибка считывания (треугольник на обоих концах). Явная константа:
истинное значение ≤ идеализированное + (∑ execErr_j + 2·rho). -/
theorem rounded_trajectory_bound (T : ℕ)
    (tr : RoundedTrajectory (n := n) (a := a) (e := e) (q := q) (r := r)
      (c := c) (k := k) T) :
    tr.trueObjective T ≤ tr.trueObjective 0
      - ∑ j ∈ Finset.range T, tr.stepDrop T j
      + ∑ j ∈ Finset.range T, tr.stepExecErr T j
      + 2 * tr.rho := by
  have key : ∀ j < T, fullObjective (tr.states (j + 1))
      ≤ fullObjective (tr.states j) - tr.stepDrop T j
        + tr.stepExecErr T j :=
    fun j hj => by
      have hd := (tr.certs j hj).execDescent
      rw [tr.stepDrop_eq T hj, tr.stepExecErr_eq T hj]
      exact hd
  have hmeas := obj_telescope_err T
    (fun j => fullObjective (tr.states j)) (tr.stepDrop T)
    (tr.stepExecErr T) key
  have h0 := abs_le.mp (tr.readout 0 (Nat.zero_le T))
  have hT := abs_le.mp (tr.readout T (Nat.le_refl T))
  linarith

/-- Замкнутая форма c(T): равномерные drop ≥ δ и execErr ≤ ε дают
`f_true(θ_T) ≤ f_true(θ_0) - T*δ + T*ε + 2*rho` — константа
зависит только от T, δ, ε, rho. -/
theorem rounded_trajectory_uniform (T : ℕ)
    (tr : RoundedTrajectory (n := n) (a := a) (e := e) (q := q) (r := r)
      (c := c) (k := k) T) (delta eps : ℝ)
    (hdelta : ∀ j < T, delta ≤ tr.stepDrop T j)
    (heps : ∀ j < T, tr.stepExecErr T j ≤ eps) :
    tr.trueObjective T ≤ tr.trueObjective 0 - T * delta + T * eps
      + 2 * tr.rho := by
  have hmain := rounded_trajectory_bound T tr
  have hsumd : T * delta ≤ ∑ j ∈ Finset.range T, tr.stepDrop T j := by
    have hmem : ∀ j ∈ Finset.range T, delta ≤ tr.stepDrop T j :=
      fun j hj => hdelta j (Finset.mem_range.mp hj)
    have hcard : ∑ j ∈ Finset.range T, delta = T * delta := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc T * delta = ∑ j ∈ Finset.range T, delta := hcard.symm
      _ ≤ ∑ j ∈ Finset.range T, tr.stepDrop T j := Finset.sum_le_sum hmem
  have hsume : ∑ j ∈ Finset.range T, tr.stepExecErr T j ≤ T * eps := by
    have hmem : ∀ j ∈ Finset.range T, tr.stepExecErr T j ≤ eps :=
      fun j hj => heps j (Finset.mem_range.mp hj)
    have hcard : ∑ j ∈ Finset.range T, eps = T * eps := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ∑ j ∈ Finset.range T, tr.stepExecErr T j
        ≤ ∑ j ∈ Finset.range T, eps := Finset.sum_le_sum hmem
      _ = T * eps := hcard
  linarith

/-! ## Пин: координатная ошибка округления (binder-форма) -/

/-- КООРДИНАТНАЯ ОШИБКА ОКРУГЛЕНИЯ (binder-форма, слой State):
если каждый обновляемый координат отклоняется не более чем на
половину шага сетки s (конкретную instantiation даёт
`Hagi.Runtime.qTern_error_in` — qTern in-range, ошибка ≤ s/2,
Runtime-слой 3, кросс-папочный импорт запрещён LayerLint) и цель
`F : (Fin m → ℝ) → ℝ` L-липшицева по сумме координатных
отклонений, то ошибка цели ≤ L·(m·s/2). L — premise-binder (в
TrainState нет леммы Липшица для energy — честный пин). -/
theorem coord_err_bound {m : ℕ} (w w' : Fin m → ℝ) (s L : ℝ)
    (F : (Fin m → ℝ) → ℝ)
    (hcoord : ∀ i, |w' i - w i| ≤ s / 2)
    (hL : 0 ≤ L)
    (hLip : |F w' - F w| ≤ L * ∑ i, |w' i - w i|) :
    |F w' - F w| ≤ L * m * s / 2 := by
  calc |F w' - F w| ≤ L * ∑ i, |w' i - w i| := hLip
    _ ≤ L * ∑ i, (s / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ => hcoord i)) hL
    _ = L * m * s / 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-! ## Форма с Hold (эффективных шагов T' ≤ T) -/

/-- ФОРМА С HOLD: в смешанном прогоне длины T каждый шаг — либо
Progress с сертифицированным (округлённым) спуском, либо Hold,
который по `hold_rollback_total` — тождество на состоянии и
вкладывает НУЛЕВЫЕ d/e в суммы. Заключение — тот же телескоп по
всем T шагам; ненулевые drop'ы встречаются только на progress-шагах,
т.е. эффективных шагов T' ≤ T. -/
theorem with_holds_bound {S : Type*} (f : S → ℝ) (T : ℕ)
    (run : ℕ → S) (outs : ℕ → Outcome S) (d e : ℕ → ℝ)
    (hcert : ∀ j < T, outs j ≠ Outcome.hold →
      f (run (j + 1)) ≤ f (run j) - d j + e j)
    (hhold : ∀ j < T, outs j = Outcome.hold →
      run (j + 1) = run j ∧ d j = 0 ∧ e j = 0) :
    f (run T) ≤ f (run 0) - ∑ j ∈ Finset.range T, d j
      + ∑ j ∈ Finset.range T, e j := by
  have key : ∀ j < T, f (run (j + 1)) ≤ f (run j) - d j + e j := by
    intro j hj
    rcases eq_or_ne (outs j) Outcome.hold with hh | hh
    · obtain ⟨hrun, hd, he⟩ := hhold j hj hh
      simp [hrun, hd, he]
    · exact hcert j hj hh
  exact obj_telescope_err T (fun j => f (run j)) d e key

end Hagi.State
