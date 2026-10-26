import Hagi.Energy.Cooling

/-!
# ComputeScaling — compute-optimal нижняя граница потерь

Формализация следствия инфо-теор. scaling laws
(Jeon–Van Roy, arXiv 2407.01456): при потерях a/m + b/n и
линейной стоимости C = m+n — L ≥ (√a+√b)²/C для любой
аллокации бюджета между моделью и данными.
-/

namespace Hagi.Optimization

/-- COMPUTE-OPTIMAL НИЖНЯЯ ГРАНИЦА (инфо-теор. scaling laws,
Jeon–Van Roy arXiv 2407.01456): при потерях L(m,n) = a/m + b/n
(модель m, данные n) и линейной стоимости вычислений
C = m+n — для ЛЮБОЙ аллокации
L ≥ (√a + √b)² / C:
суммарный бюджет ограничивает потери снизу; равенство
достигается только при n·√a = m·√b (линейная
data/model-пропорция — вывод Jeon–Van Roy). -/
theorem compute_scaling_lower_bound (a b m n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hn : 0 < n) :
    (Real.sqrt a + Real.sqrt b) ^ 2 / (m + n) ≤ a / m + b / n := by
  set X := Real.sqrt a with hX
  set Y := Real.sqrt b with hY
  have e1 : X * X = a := by rw [hX]; exact Real.mul_self_sqrt (le_of_lt ha)
  have e2 : Y * Y = b := by rw [hY]; exact Real.mul_self_sqrt (le_of_lt hb)
  have hmn : (0:ℝ) < m + n := by linarith
  have key : (n * X - m * Y) ^ 2 ≥ 0 := sq_nonneg _
  rw [div_add_div _ _ hm.ne' hn.ne',
    div_le_div_iff₀ hmn (by positivity : (0:ℝ) < m * n)]
  have hex : (a * n + m * b) * (m + n)
      = (X + Y) ^ 2 * (m * n) + (n * X - m * Y) ^ 2 := by
    rw [← e1, ← e2]
    ring
  linarith [hex, key]

/-- ДОСТИЖИМОСТЬ ГРАНИЦЫ (Jeon–Van Roy): аллокация
m = √a·s, n = √b·s (линейная data/model-пропорция m/n = √a/√b)
ДОСТИГАЕТ нижней границы compute_scaling_lower_bound:
L = (√a+√b)²/(m+n) — граница точная, оптимум вычислений. -/
theorem compute_scaling_bound_attained (a b s : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    (Real.sqrt a + Real.sqrt b) ^ 2
      / (Real.sqrt a * s + Real.sqrt b * s)
      = a / (Real.sqrt a * s) + b / (Real.sqrt b * s) := by
  set X := Real.sqrt a with hX
  set Y := Real.sqrt b with hY
  have e1 : X * X = a := by rw [hX]; exact Real.mul_self_sqrt (le_of_lt ha)
  have e2 : Y * Y = b := by rw [hY]; exact Real.mul_self_sqrt (le_of_lt hb)
  have hXs : (0:ℝ) < X * s := by
    have : (0:ℝ) < X := Real.sqrt_pos.mpr ha
    positivity
  have hYs : (0:ℝ) < Y * s := by
    have : (0:ℝ) < Y := Real.sqrt_pos.mpr hb
    positivity
  have hXY : (0:ℝ) < X + Y := by
    have : (0:ℝ) < X := Real.sqrt_pos.mpr ha
    have : (0:ℝ) < Y := Real.sqrt_pos.mpr hb
    linarith
  have keyL : (X + Y) ^ 2 / (X * s + Y * s) = (X + Y) / s := by
    have hfac : X * s + Y * s = (X + Y) * s := by ring
    rw [hfac]
    field_simp
  have keyR : a / (X * s) + b / (Y * s) = (X + Y) / s := by
    rw [← e1, ← e2]
    have h1 : X * X / (X * s) = X / s := by field_simp
    have h2 : Y * Y / (Y * s) = Y / s := by field_simp
    rw [h1, h2]
    ring
  rw [keyL, keyR]

/-- K-РЕСУРСНАЯ COMPUTE-ГРАНИЦА: для любого конечного набора
ресурсов с потерями Σ aᵢ/mᵢ и линейной стоимостью C = Σ mᵢ:
Σ aᵢ/mᵢ ≥ (Σ √aᵢ)² / C — обобщение Jeon–Van Roy на
многоресурсную аллокацию вычислений (индукция по 2-ресурсной
базе compute_scaling_lower_bound). -/
theorem compute_scaling_multi {ι : Type} (S : Finset ι)
    (a m : ι → ℝ) (ha : ∀ i ∈ S, 0 < a i)
    (hm : ∀ i ∈ S, 0 < m i) :
    (∑ i ∈ S, Real.sqrt (a i)) ^ 2 / (∑ i ∈ S, m i)
      ≤ ∑ i ∈ S, a i / m i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have haj : 0 < a j := ha j (Finset.mem_insert_self j s)
    have hmj : 0 < m j := hm j (Finset.mem_insert_self j s)
    have has : ∀ i ∈ s, 0 < a i :=
      fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hms : ∀ i ∈ s, 0 < m i :=
      fun i hi => hm i (Finset.mem_insert_of_mem hi)
    have hih := ih has hms
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    rcases Finset.eq_empty_or_nonempty s with hs0 | hsne
    · rw [hs0, Finset.sum_empty, Finset.sum_empty,
        Finset.sum_insert (by simp : ¬ (j : ι) ∈ (∅ : Finset ι)), Finset.sum_empty]
      rw [add_zero, add_zero]
      have h2 : (Real.sqrt (a j)) ^ 2 = a j :=
        Real.sq_sqrt (le_of_lt haj)
      rw [h2]
      simp
    · rw [Finset.sum_insert hj,
        add_comm (Real.sqrt (a j)) (∑ i ∈ s, Real.sqrt (a i)),
        add_comm (m j) (∑ i ∈ s, m i)]
      have hsne' := hsne
      obtain ⟨i0, hi0mem⟩ := hsne
      have hXpos : (0:ℝ) < ∑ i ∈ s, Real.sqrt (a i) :=
        lt_of_lt_of_le (Real.sqrt_pos.mpr (has i0 hi0mem))
          (Finset.single_le_sum (fun i _ => Real.sqrt_nonneg _)
            hi0mem)
      have hMs : (0:ℝ) < ∑ i ∈ s, m i :=
        Finset.sum_pos hms hsne'
      have hX2 : Real.sqrt ((∑ i ∈ s, Real.sqrt (a i)) ^ 2)
          = ∑ i ∈ s, Real.sqrt (a i) :=
        Real.sqrt_sq (Finset.sum_nonneg
          (fun i _ => Real.sqrt_nonneg _))
      have hbase := compute_scaling_lower_bound
        ((∑ i ∈ s, Real.sqrt (a i)) ^ 2) (a j)
        (∑ i ∈ s, m i) (m j)
        (by nlinarith [hXpos]) haj hMs hmj
      rw [hX2] at hbase
      calc (∑ i ∈ s, Real.sqrt (a i) + Real.sqrt (a j)) ^ 2
            / (∑ i ∈ s, m i + m j)
          ≤ (∑ i ∈ s, Real.sqrt (a i)) ^ 2 / (∑ i ∈ s, m i)
              + a j / m j := hbase
        _ ≤ a j / m j + ∑ i ∈ s, a i / m i := by
              linarith [hbase, hih]

/-- ДОСТИЖИМОСТЬ K-РЕСУРСНОЙ ГРАНИЦЫ (Jeon–Van Roy,
многоресурсный оптимум): пропорциональная аллокация
mᵢ = √aᵢ·s ДОСТИГАЕТ нижней границы
Σ aᵢ/mᵢ = (Σ √aᵢ)² / Σ mᵢ — граница точная для любого
конечного набора ресурсов; оптимальная аллокация вычислений
пропорциональна корням вкладов. -/
theorem compute_scaling_multi_attained {ι : Type} (S : Finset ι)
    (a : ι → ℝ) (s : ℝ) (hne : S.Nonempty)
    (ha : ∀ i ∈ S, 0 < a i) (hs : 0 < s) :
    (∑ i ∈ S, Real.sqrt (a i)) ^ 2 / (∑ i ∈ S, Real.sqrt (a i) * s)
      = ∑ i ∈ S, a i / (Real.sqrt (a i) * s) := by
  have hsqrt : ∀ i ∈ S, (Real.sqrt (a i)) * Real.sqrt (a i)
      = a i := fun i hi => Real.mul_self_sqrt (le_of_lt (ha i hi))
  have hpos : ∀ i ∈ S, (0:ℝ) < Real.sqrt (a i) :=
    fun i hi => Real.sqrt_pos.mpr (ha i hi)
  have hterm : ∀ i ∈ S,
      a i / (Real.sqrt (a i) * s) = Real.sqrt (a i) / s := by
    intro i hi
    have hx := hpos i hi
    calc a i / (Real.sqrt (a i) * s)
        = (Real.sqrt (a i) * Real.sqrt (a i)) / (Real.sqrt (a i) * s) := by
          rw [hsqrt i hi]
      _ = Real.sqrt (a i) / s := by
          field_simp
  rw [Finset.sum_congr rfl (fun i hi => hterm i hi)]
  have hden : ∑ i ∈ S, Real.sqrt (a i) * s
      = s * ∑ i ∈ S, Real.sqrt (a i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  obtain ⟨i0, h0m⟩ := hne
  have hsumpos : (0:ℝ) < ∑ i ∈ S, Real.sqrt (a i) :=
    Finset.sum_pos' (fun i _ => Real.sqrt_nonneg _)
      ⟨i0, h0m, hpos i0 h0m⟩
  rw [hden, ← Finset.sum_div]
  have hne0 : s * ∑ i ∈ S, Real.sqrt (a i) ≠ 0 :=
    mul_ne_zero (ne_of_gt hs) (ne_of_gt hsumpos)
  field_simp

end Hagi.Optimization
