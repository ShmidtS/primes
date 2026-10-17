/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic

set_option linter.style.header false

open Finset Real

open Finset in
/-- **Нижняя грань энергии (R420)**: E* ≤ ⟨E⟩_T
почленно (E* · w_v ≤ E_v · w_v). Вместе с R393
полный сэндвич:
E* ≤ ⟨E⟩_T ≤ E* + Δ·(n−1)·e^{−δ/T} —
энергия Гиббса зажата между
основным состоянием и хвостом. -/
theorem gibbs_expected_energy_lower {V : Type*} [Fintype V]
    [Nonempty V] (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (vstar : V) (hmin : ∀ v, E vstar ≤ E v) :
    E vstar ≤ (∑ v, E v * Real.exp (-(E v)/T))
        / (∑ v, Real.exp (-(E v)/T)) := by
  set Z : ℝ := ∑ v, Real.exp (-(E v)/T) with hZ
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  -- E* = (sum E* * e) / Z  <=  (sum E * e) / Z
  have hnum : (∑ v, E vstar * Real.exp (-(E v)/T))
      ≤ ∑ v, E v * Real.exp (-(E v)/T) := by
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_right (hmin v) (le_of_lt (exp_pos _))
  -- rewrite numerator: sum E* * e = E* * Z
  have hsplit : ∑ v, E vstar * Real.exp (-(E v)/T)
      = E vstar * Z := by
    rw [hZ, Finset.mul_sum]
  rw [hsplit] at hnum
  rwa [le_div_iff₀ hZpos]

open Finset in
/-- **Верхняя грань свободной энергии (R421)**:
F(T) = −T·ln Z ≤ E* поточено (Z ≥ w*,
логарифм монотонен, −T < 0). Вместе с R398
полный сэндвич свободной энергии:
E* − T·ln(1+(n−1)e^{−δ/T}) ≤ F(T) ≤ E* —
сжимается к E* при охлаждении. -/
theorem free_energy_upper {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) (vstar : V) :
    -T * Real.log (∑ v, Real.exp (-(E v)/T)) ≤ E vstar := by
  have hZpos : (0:ℝ) < ∑ v, Real.exp (-(E v)/T) :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  -- Z >= w* : single_le_sum
  have hw : Real.exp (-(E vstar)/T)
      ≤ ∑ v, Real.exp (-(E v)/T) :=
    single_le_sum (f := fun v => Real.exp (-(E v)/T))
      (fun v _ => le_of_lt (exp_pos _)) (Finset.mem_univ vstar)
  -- log mono
  have hlog : Real.log (Real.exp (-(E vstar)/T))
      ≤ Real.log (∑ v, Real.exp (-(E v)/T)) :=
    Real.log_le_log (exp_pos _) hw
  rw [Real.log_exp] at hlog
  -- -T * log Z <= -T * (-(E vstar)/T) = E vstar
  have hmul : -T * Real.log (∑ v, Real.exp (-(E v)/T))
      ≤ -T * (-(E vstar)/T) :=
    mul_le_mul_of_nonpos_left hlog (by linarith : (-T:ℝ) ≤ 0)
  have : -T * (-(E vstar)/T) = E vstar := by
    field_simp
  linarith

open Finset in
/-- **Разложение перекрёстной энтропии (R422)**:
∑ w·ln(w·n) = ∑ w·ln w + ln n — тождество
энтропия/KL: KL(pḟ‖u) =
−S + ln n. Вместе с R418 (S ≥ 0) даёт
KL(pḟ‖u) ≤ ln n; мост к Пинскеру на
Гиббс-парах: охлаждение убивает энтропию
→ KL к равномерному растёт до ln n (порядок
максимальной энтропии обращается). -/
theorem gibbs_kl_uniform_split {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) :
    ∑ v, (Real.exp (-(E v)/T)
        / ∑ v, Real.exp (-(E v)/T))
      * Real.log ((Real.exp (-(E v)/T)
        / ∑ v, Real.exp (-(E v)/T))
        * (Fintype.card V : ℝ))
    = ∑ v, (Real.exp (-(E v)/T)
        / ∑ v, Real.exp (-(E v)/T))
      * Real.log (Real.exp (-(E v)/T)
        / ∑ v, Real.exp (-(E v)/T))
      + Real.log (Fintype.card V : ℝ) := by
  set Z : ℝ := ∑ v, Real.exp (-(E v)/T) with hZ
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set w : V → ℝ := fun v => Real.exp (-(E v)/T) / Z with hw
  have hwpos : ∀ v, 0 < w v := fun v => div_pos (exp_pos _) hZpos
  have hw1 : ∑ v, w v = 1 := by
    rw [hw]
    simp only
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  have hcard : (0:ℝ) < (Fintype.card V : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr
      ⟨Classical.arbitrary V⟩)
  -- per-term: log (w * n) = log w + log n
  have hterm : ∀ v ∈ Finset.univ,
      w v * Real.log (w v * (Fintype.card V : ℝ))
        = w v * Real.log (w v)
          + w v * Real.log (Fintype.card V : ℝ) := by
    intro v _
    have hsplit : Real.log (w v * (Fintype.card V : ℝ))
        = Real.log (w v) + Real.log (Fintype.card V : ℝ) :=
      (Real.log_mul (ne_of_gt (hwpos v)) (ne_of_gt hcard))
    rw [hsplit, mul_add]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hsecond : ∑ v, w v * Real.log (Fintype.card V : ℝ)
      = Real.log (Fintype.card V : ℝ) := by
    have hcomm : ∑ v, w v * Real.log (Fintype.card V : ℝ)
        = ∑ v, Real.log (Fintype.card V : ℝ) * w v :=
      Finset.sum_congr rfl (fun v _ => by rw [mul_comm])
    rw [hcomm, ← Finset.mul_sum, hw1, mul_one]
  rw [hsecond]

open Finset in
/-- **Элементарный зазор Гиббса (R432)** —
первый кирпич моста к multiplicative
weights (RAG-опора: arXiv 2608.09389,
EW-regret ≤ M√(2 ln A·T)):
⟨E⟩_T ≤ E_min + T·n для ЛЮБЫх E
(без гэп-предположений!).
Доказательство:
x + T ≤ T·e^{x/T} почленно +
свёртка w·e^{(E−Emin)/T} = e^{−Emin/T}
тожденственно. При температуре
η = T/шаг это без-regret зона
экспоненциальных весов. -/
theorem gibbs_energy_gap_crude {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) :
    ∃ vmin : V, (∑ v, E v * Real.exp (-(E v)/T))
        / (∑ v, Real.exp (-(E v)/T)) - E vmin
      ≤ T * (Fintype.card V : ℝ) := by
  obtain ⟨vmin, hvmin⟩ : ∃ vmin : V, ∀ v : V, E vmin ≤ E v := by
    obtain ⟨a, _, ha⟩ := Finset.exists_min_image (Finset.univ : Finset V) E
      Finset.univ_nonempty
    exact ⟨a, fun v => ha v (Finset.mem_univ v)⟩
  refine ⟨vmin, ?_⟩
  have hZpos : (0:ℝ) < ∑ v, Real.exp (-(E v)/T) :=
    Finset.sum_pos (fun v _ => exp_pos _) ⟨vmin, Finset.mem_univ _⟩
  -- numerator identity
  have hterm : ∀ v : V, Real.exp (-(E v)/T) * (E v - E vmin)
      = E v * Real.exp (-(E v)/T)
        - Real.exp (-(E v)/T) * E vmin := fun v => by ring
  have hnum : (∑ v, E v * Real.exp (-(E v)/T))
      / (∑ v, Real.exp (-(E v)/T)) - E vmin
      = (∑ v, Real.exp (-(E v)/T) * (E v - E vmin))
        / (∑ v, Real.exp (-(E v)/T)) := by
    have hsumEq : ∑ v, Real.exp (-(E v)/T) * (E v - E vmin)
        = ∑ v, E v * Real.exp (-(E v)/T)
          - E vmin * ∑ v, Real.exp (-(E v)/T) := by
      rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_sub_distrib,
        Finset.sum_congr rfl (fun v _ => mul_comm (Real.exp (-(E v)/T)) (E vmin)),
        ← Finset.mul_sum]
    rw [hsumEq, sub_div, mul_div_cancel_right₀ (E vmin) (ne_of_gt hZpos)]
  rw [hnum]
  -- per-point exponential identity (folded form)
  have hident : ∀ v : V, Real.exp (-(E v)/T)
      * Real.exp ((E v - E vmin)/T) = Real.exp (-(E vmin)/T) := by
    intro v
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  -- per-point bound: x <= T*exp(x/T) - T... via add_one_le_exp
  have hpt : ∀ v : V, Real.exp (-(E v)/T) * (E v - E vmin)
      ≤ Real.exp (-(E v)/T) * (T * Real.exp ((E v - E vmin)/T)) := by
    intro v
    have hnn : (0:ℝ) ≤ E v - E vmin := sub_nonneg.mpr (hvmin v)
    have hmult := mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp ((E v - E vmin)/T)) (le_of_lt hT)
    have hrew : T * ((E v - E vmin)/T + 1)
        = (E v - E vmin) + T := by
      rw [mul_add]
      have hd : T * ((E v - E vmin)/T) = E v - E vmin := by
        field_simp
      rw [hd, mul_one]
    have hkey2 : E v - E vmin
        ≤ T * Real.exp ((E v - E vmin)/T) := by linarith [hmult, hrew]
    exact mul_le_mul_of_nonneg_left hkey2 (exp_pos _).le
  -- sum bound
  have h1 : (∑ v : V, Real.exp (-(E v)/T) * (E v - E vmin))
      ≤ ∑ v : V, Real.exp (-(E v)/T)
        * (T * Real.exp ((E v - E vmin)/T)) :=
    Finset.sum_le_sum (fun v _ => hpt v)
  have hterm2 : ∀ v : V, Real.exp (-(E v)/T)
      * (T * Real.exp ((E v - E vmin)/T))
      = T * Real.exp (-(E vmin)/T) := by
    intro v
    calc Real.exp (-(E v)/T) * (T * Real.exp ((E v - E vmin)/T))
        = T * (Real.exp (-(E v)/T)
          * Real.exp ((E v - E vmin)/T)) := by ring
      _ = T * Real.exp (-(E vmin)/T) := by rw [hident v]
  have h2 : ∑ v : V, Real.exp (-(E v)/T)
        * (T * Real.exp ((E v - E vmin)/T))
      = T * (Fintype.card V : ℝ) * Real.exp (-(E vmin)/T) := by
    rw [Finset.sum_congr rfl (fun v _ => hterm2 v), Finset.sum_const]
    norm_num
    ring
  have hsum : (∑ v : V, Real.exp (-(E v)/T) * (E v - E vmin))
      ≤ T * (Fintype.card V : ℝ) * Real.exp (-(E vmin)/T) :=
    h1.trans_eq h2
  have hC : Real.exp (-(E vmin)/T)
      ≤ ∑ v, Real.exp (-(E v)/T) :=
    single_le_sum (f := fun v => Real.exp (-(E v)/T))
      (fun v _ => le_of_lt (exp_pos _)) (Finset.mem_univ vmin)
  rw [div_le_iff₀ hZpos]
  have hn : (0:ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hC (mul_nonneg (le_of_lt hT) hn)
  linarith [hsum, hmul]

open Finset in
/-- **Log-декомпозиция Гиббс-веса
(R445)** (PAC-Bayes/Катони, RAG arXiv
2609.12891): ln(ρ_v·n) = ln n − ln Z −
E_v/T — вес = сложение
случайности,
нормировки и
энергии. Кирпич
KL-тождества Катони
(λ⟨r⟩ + KL = −ln Z_π):
суммирование по
v даёт тождество
в целом. -/
theorem gibbs_weight_log_decomp {V : Type*} [Fintype V]
    [Nonempty V] (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (v : V) :
    Real.log ((Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T))
        * (Fintype.card V : ℝ))
    = Real.log (Fintype.card V : ℝ)
      - Real.log (∑ v : V, Real.exp (-(E v)/T))
      - (E v)/T := by
  set Z : ℝ := ∑ v : V, Real.exp (-(E v)/T) with hZdef
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hnn : (0:ℝ) < n :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
  have hsplit : (Real.exp (-(E v)/T) / Z) * n
      = n * Real.exp (-(E v)/T) / Z := by
    field_simp
  have hexpne : Real.exp (-(E v)/T) ≠ 0 := by positivity
  rw [hsplit, Real.log_div (by positivity) hZpos.ne',
    Real.log_mul hnn.ne' hexpne, Real.log_exp]
  ring

open Finset in
/-- **KL-тождество Катони (R446)**:
KL(ρḟ‖unif) = −ln Z − ⟨E⟩/T + ln n —
суммарование
log-декомпозиции
R445: λ⟨r⟩ + KL(ρḟ‖π) =
−ln Z_π в uniform-случае.
Связь с известным:
вместе с R422 (KL = ln n − S)
даёт F = ⟨E⟩ − T·S — гибсовская
свободная энергия из
PAC-Bayes-тожества. Мост
термодинамика ↔
PAC-Bayes формально замкнут. -/
theorem gibbs_katoni_kl {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) :
    (∑ v : V, (Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T))
      * Real.log ((Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T))
        * (Fintype.card V : ℝ)))
    = Real.log (Fintype.card V : ℝ)
      - Real.log (∑ v : V, Real.exp (-(E v)/T))
      - (1/T) * (∑ v : V, (Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T)) * E v) := by
  set Z : ℝ := ∑ v : V, Real.exp (-(E v)/T) with hZdef
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set ρ : V → ℝ := fun v => Real.exp (-(E v)/T) / Z with hρ
  have hρsum : ∑ v : V, ρ v = 1 := by
    rw [hρ]
    simp only
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  -- per-term split
  have hterm : ∀ v : V, ρ v * Real.log (ρ v * n)
      = ρ v * (Real.log n - Real.log Z)
        - (ρ v * E v)/T := by
    intro v
    rw [gibbs_weight_log_decomp E T hT v, mul_sub, mul_div_assoc]
  rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_sub_distrib]
  -- part 1: sum(rho * c) = c
  rw [Finset.sum_congr rfl (fun v _ => mul_comm (ρ v)
      (Real.log n - Real.log Z)), ← Finset.mul_sum, hρsum, mul_one]
  -- part 2: sum (rho E / T) = (sum rho E)/T
  rw [← Finset.sum_div]
  ring

open Finset in
/-- **Общий второй закон (R447)**:
KL(ρḟ‖γ) ≥ 0 для любых
двух распределений
на конечном носителе:
ln u ≤ u−1 почленно с
u := γ/ρ даёт ρ·ln(ρ/γ) ≥ ρ−γ;
телескоп даёт 0.
Обобщение R418 (Гибс-случай)
на произвольные пары;
основа для вариационного
принципа Гиббса. -/
theorem finite_kl_nonneg {V : Type*} [Fintype V] [Nonempty V]
    (ρ γ : V → ℝ)
    (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v : V, ρ v = 1)
    (hγ : ∀ v, 0 < γ v) (hγ1 : ∑ v : V, γ v = 1) :
    (0:ℝ) ≤ ∑ v : V, ρ v * Real.log (ρ v / γ v) := by
  -- per-v: ln(gamma/rho) <= gamma/rho - 1
  have hln : ∀ v : V, Real.log (γ v / ρ v) ≤ γ v / ρ v - 1 :=
    fun v => Real.log_le_sub_one_of_pos (div_pos (hγ v) (hρ v))
  -- negate: rho * log(rho/gamma) >= rho - gamma
  have hterm : ∀ v : V, ρ v - γ v
      ≤ ρ v * Real.log (ρ v / γ v) := by
    intro v
    have hneg : Real.log (ρ v / γ v) = -(Real.log (γ v / ρ v)) := by
      rw [Real.log_div (hρ v).ne' (hγ v).ne',
        Real.log_div (hγ v).ne' (hρ v).ne']
      ring
    rw [hneg]
    have hc : ρ v * (γ v / ρ v) = γ v := by
      field_simp [(hρ v).ne']
    -- -rho*log(gamma/rho) >= rho - gamma
    nlinarith [hln v, hρ v, hc]
  -- sum telescope
  have hsum : ∑ x : V, (ρ x - γ x) = 0 := by
    rw [Finset.sum_sub_distrib, hρ1, hγ1, sub_self]
  calc (0:ℝ)
      = ∑ v : V, (ρ v - γ v) := by rw [hsum]
    _ ≤ ∑ v : V, ρ v * Real.log (ρ v / γ v) :=
      Finset.sum_le_sum (fun v _ => hterm v)

open Finset in
/-- **Вариационный
принцип Гиббса (R448)**:
для любого распределения ρ:
⟨E⟩_ρ + T·Σρ ln ρ ≥ −T·ln Z —
свободная энергия
любого ρ (⟨E⟩ − T·S
с S = −Σρ ln ρ) не меньше
гиббсовой F = −T ln Z.
Вывод: R447 (KL ≥ 0) на
Гиббс-мере γ с
разворачиванием
T·KL почленно
(T·KL = T·Σρ ln ρ + ⟨E⟩ + T ln Z).
Равенство на Гиббсе —
R446. Минимум свободной
энергии достигается
равновесным
распределением. -/
theorem gibbs_variational {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v : V, ρ v = 1) :
    -T * Real.log (∑ v : V, Real.exp (-(E v)/T))
      ≤ (∑ v : V, ρ v * E v)
        + T * (∑ v : V, ρ v * Real.log (ρ v)) := by
  set Z : ℝ := ∑ v : V, Real.exp (-(E v)/T) with hZdef
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set γ : V → ℝ := fun v => Real.exp (-(E v)/T) / Z with hγ
  have hγpos : ∀ v, 0 < γ v := fun v => by
    rw [hγ]; positivity
  have hγ1 : ∑ v : V, γ v = 1 := by
    rw [hγ]
    simp only
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  have hKL := finite_kl_nonneg ρ γ hρ hρ1 hγpos hγ1
  have hlogγ : ∀ v : V, Real.log (γ v)
      = -(E v)/T - Real.log Z := by
    intro v
    rw [hγ, Real.log_div (exp_pos _).ne' hZpos.ne', Real.log_exp]
  -- T * KL = T*S-form + <E> + T log Z
  have hTKL : T * (∑ v : V, ρ v * Real.log (ρ v / γ v))
      = T * (∑ v : V, ρ v * Real.log (ρ v))
        + (∑ v : V, ρ v * E v) + T * Real.log Z := by
    have hsplit : ∀ v : V,
        T * (ρ v * Real.log (ρ v / γ v))
        = ρ v * (T * Real.log (ρ v)) + ρ v * E v
          + ρ v * (T * Real.log Z) := by
      intro v
      rw [Real.log_div (hρ v).ne' (hγpos v).ne', hlogγ v]
      field_simp
      ring
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun v _ => hsplit v)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun v _ =>
      mul_left_comm (ρ v) T (Real.log (ρ v)))]
    rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun v _ => mul_comm (ρ v) (T * Real.log Z))]
    rw [← Finset.mul_sum, hρ1, mul_one]
  have hKL' : (0:ℝ) ≤ T * (∑ v : V, ρ v * Real.log (ρ v / γ v)) :=
    mul_nonneg (le_of_lt hT) hKL
  rw [hTKL] at hKL'
  linarith

open Finset in
/-- **Нижняя грань свободной энергии (R449)**:
E_min − T·ln n ≤ F = −T·ln Z.
Вместе с R421 (F ≤ E*) — сэндвич свободной энергии:
E_min − T·ln n ≤ F ≤ E_min.
Классическая термодинамика: свободная энергия
зажата между основанием с энтропийным
запасом T·ln n и насыщением E_min.
Метод: Z ≤ n·e^{−E_min/T} почленно + монотонность ln
+ умножение на −T < 0. -/
theorem gibbs_free_energy_lower {V : Type*} [Fintype V]
    [Nonempty V] (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (vmin : V) (hmin : ∀ v : V, E vmin ≤ E v) :
    (E vmin) - T * Real.log ((Fintype.card V : ℝ))
      ≤ -T * Real.log (∑ v : V, Real.exp (-(E v)/T)) := by
  have hZ : ∑ v : V, Real.exp (-(E v)/T)
      ≤ (Fintype.card V : ℝ) * Real.exp (-(E vmin)/T) := by
    have hexp : ∀ v : V, Real.exp (-(E v)/T)
        ≤ Real.exp (-(E vmin)/T) := by
      intro v
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div]
      exact neg_le_neg ((div_le_div_iff_of_pos_right hT).mpr (hmin v))
    calc ∑ v : V, Real.exp (-(E v)/T)
        ≤ ∑ v : V, Real.exp (-(E vmin)/T) :=
          Finset.sum_le_sum (fun v _ => hexp v)
      _ = (Fintype.card V : ℝ) * Real.exp (-(E vmin)/T) := by
          simp [Finset.sum_const]
  have hn : (0:ℝ) < Fintype.card V :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
  have hexpmin : (0:ℝ) < Real.exp (-(E vmin)/T) := exp_pos _
  have hlog : Real.log (∑ v : V, Real.exp (-(E v)/T))
      ≤ Real.log ((Fintype.card V : ℝ)) - (E vmin)/T := by
    have h1 := Real.log_le_log (Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩) hZ
    rw [Real.log_mul hn.ne' hexpmin.ne', Real.log_exp, neg_div] at h1
    exact h1
  have h3 : -T * (Real.log ((Fintype.card V : ℝ)) - (E vmin)/T)
      = (E vmin) - T * Real.log ((Fintype.card V : ℝ)) := by
    field_simp
    ring
  have h4 := mul_le_mul_of_nonpos_left hlog (by linarith : (-T:ℝ) ≤ 0)
  rw [h3] at h4
  exact h4

open Finset in
/-- **Максимальная энтропия (R450)**:
S(ρ) = −Σρ ln ρ ≤ ln n для любого
распределения на n-точечном
носителе — равновесие
(uniform) максимизирует энтропию.
Вывод: R447 с γ = uniform:
KL(ρḟ‖unif) ≥ 0 ⇔ S ≤ ln n.
Вместе с R418 (S ≥ 0) и R429 (Нернст
на термостате) — полный
энтропийный контур любого
распределения: 0 ≤ S ≤ ln n. -/
theorem finite_max_entropy {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (ρ : V → ℝ)
    (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v : V, ρ v = 1) :
    -(∑ v : V, ρ v * Real.log (ρ v))
      ≤ Real.log ((Fintype.card V : ℝ)) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hnne : n ≠ 0 := by positivity
  set γ : V → ℝ := fun _ => 1/n with hγ
  have hγpos : ∀ v, 0 < γ v := by
    intro v; rw [hγ]; positivity
  have hγ1 : ∑ v : V, γ v = 1 := by
    rw [hγ]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, one_div]
    rw [← hn]
    exact mul_inv_cancel₀ hnne
  have hKL := finite_kl_nonneg ρ γ hρ hρ1 hγpos hγ1
  -- expand KL: sum rho (log rho + log n)
  have hexp : ∑ v : V, ρ v * Real.log (ρ v / γ v)
      = (∑ v : V, ρ v * Real.log (ρ v))
        + Real.log n := by
    have hsplit : ∀ v : V, ρ v * Real.log (ρ v / γ v)
        = ρ v * Real.log (ρ v) + ρ v * Real.log n := by
      intro v
      rw [hγ, one_div, div_inv_eq_mul,
        Real.log_mul (hρ v).ne' hnne]
      ring
    rw [Finset.sum_congr rfl (fun v _ => hsplit v),
      Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun v _ => mul_comm (ρ v) (Real.log n))]
    rw [← Finset.mul_sum, hρ1, mul_one]
  rw [hexp] at hKL
  linarith

