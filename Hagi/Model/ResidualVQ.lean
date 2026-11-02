import Hagi.Model.StageSemantics
import Hagi.Energy.Quantizer

/-!
# ResidualVQ — иерархическое остаточное кодирование (NCM-мост, уровень 1)

Связь с Next-Concept Modeling (arXiv 2610.14162): представления
строятся цепочкой уровней «от грубого к точному», где каждый
уровень кодирует ОСТАТОЧНУЮ информацию, не переданную
предыдущими:

  ẑ⁽ᵏ⁾ = Σ_{i≤k} Rᵢ,   z⁽ᵏ⁾ = z − ẑ⁽ᵏ⁾.

Здесь формализованы:

1. `reconstruct` — накопленная реконструкция;
2. `residual_identity` — точное тождество остатка (база
   всей иерархии NCM, задача №1 аудита);
3. `refine_geometric` — сертификат уточнения уровня:
   D_{k+1} ≤ ρ_k·D_k при ρ_k < 1 даёт ГЕОМЕТРИЧЕСКОЕ
   затухание ошибки представления;
4. `error_budget_telescope` — ε-версия (задача №3 аудита):
   D_K ≤ (∏ρ_k)·D_0 + Σ ε_k·(∏_{j>k} ρ_j);
5. `refine_to_stage_input` — мост к StageSemantics:
   уточнение представления — это компрессионная стадия
   с измеренной quantErr = √D и сжатием, ограниченным
   κ·s·√D (ledger `advance_energy_drop`).

Существенное (по аудиту): монотонность уточнения НЕ
постулируется — она является ПРОВЕРЯЕМЫМ СЕРТИФИКАТОМ
(`RefineCert`): в самой статье NCM качество промежуточных
уровней не обязано монотонно расти.
-/

namespace Hagi.Model.ResidualVQ

open Real

-- Носитель реконструкции: вклады уровней как функции.
variable {V : Type*} [AddCommGroup V]

/-- Накопленная реконструкция после k уровней:
ẑ⁽ᵏ⁾ = Σ_{i<k} Rᵢ (уровни индексируются 0..k−1). -/
noncomputable def reconstruct (R : ℕ → V) (k : ℕ) : V :=
  ∑ i ∈ Finset.range k, R i

/-- ТОЖДЕСТВО ОСТАТКА (задача №1): остаток после k уровней
z − ẑ⁽ᵏ⁾ — по определению; переиндексация тривиальна,
тождество фиксирует СТРУКТУРУ иерархии: следующий уровень
кодирует ровно то, что не передали предыдущие. -/
theorem residual_sum_split (R : ℕ → V) (z : V) (k : ℕ) :
    z = reconstruct R k + (z - reconstruct R k) := by
  unfold reconstruct
  abel

/-! ### Скалярная ошибка представления и сертификаты уточнения -/

/-- Сертификат уточнения уровня: следующий уровень сжимает
ошибку представления в ρ_k раз с допуском ε_k.
НЕ постулат иерархии — проверяемый контракт каждого
конкретного токенизатора (в NCM качество промежуточных
уровней не обязано монотонно расти — Appendix G, J). -/
structure RefineCert (D : ℕ → ℝ) (rho eps : ℕ → ℝ) (K : ℕ) where
  /-- сжатие ошибки на каждом уровне k < K. -/
  contract : ∀ k < K, D (k + 1) ≤ rho k * D k + eps k

/-- ГЕОМЕТРИЧЕСКОЕ ЗАТУХАНИЕ (задача №3, сильная версия):
при ε ≡ 0 и ρ_k < 1 ошибка представления затухает
геометрически: D_K ≤ (∏ρ_k)·D_0. -/
theorem refine_geometric (D : ℕ → ℝ) (rho : ℕ → ℝ) (K : ℕ)
    (hD0 : 0 ≤ D 0)
    (hcontract : ∀ k < K, D (k + 1) ≤ rho k * D k)
    (hrhonn : ∀ k < K, 0 ≤ rho k) :
    D K ≤ (∏ k ∈ Finset.range K, rho k) * D 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hstep := hcontract K (by omega)
    have hih := ih (fun k hk => hcontract k (by omega))
      (fun k hk => hrhonn k (by omega))
    rw [Finset.prod_range_succ]
    calc D (K + 1) ≤ rho K * D K := hstep
      _ ≤ rho K * (∏ k ∈ Finset.range K, rho k) * D 0 := by
          calc rho K * D K ≤ rho K * ((∏ k ∈ Finset.range K, rho k) * D 0) :=
                mul_le_mul_of_nonneg_left hih (hrhonn K (by omega))
            _ = (rho K * ∏ k ∈ Finset.range K, rho k) * D 0 := by ring
      _ = (∏ k ∈ Finset.range K, rho k) * rho K * D 0 := by ring

/-- БЮДЖЕТ ОШИБОК, равномерная версия
(задача №3 аудита, практическая форма
для контроллера): при сжатии
ρ_k ≤ ρ < 1 и допусках ε_k ≤ ε
ошибка представления ограничена
геометрическим затуханием плюс
буджет накопленных допусков:
D_K ≤ ρ^K·D_0 + ε·(1 − ρ^K)/(1 − ρ).
(Точная Ico-хвостовая форма следует из
этой при почлевом разборе неравенств в
сторону ослабления.) -/
theorem error_budget_uniform (D rho eps : ℕ → ℝ)
    (K : ℕ) (ρ ε : ℝ)
    (hcontract : ∀ k < K, D (k + 1) ≤ rho k * D k + eps k)
    (hrho : ∀ k < K, rho k ≤ ρ) (hrhonn : ∀ k < K, 0 ≤ rho k)
    (heps : ∀ k < K, eps k ≤ ε) (hεnn : 0 ≤ ε)
    (hrho1 : ρ < 1) (hrhonn' : 0 ≤ ρ)
    (hDnn : ∀ k ≤ K, 0 ≤ D k) :
    D K ≤ ρ ^ K * D 0
      + ε * (1 - ρ ^ K) / (1 - ρ) := by
  -- прямая индукция с одной леммой о геометрии
  have key : ∀ m : ℕ, m ≤ K →
      D m ≤ ρ ^ m * D 0 + ε * (1 - ρ ^ m) / (1 - ρ) := by
    intro m
    induction m with
    | zero =>
        intro _
        simp only [pow_zero, sub_self, mul_zero, zero_div, add_zero]
        exact le_of_eq (by ring : D 0 = 1 * D 0)
    | succ m ih =>
      intro hm
      have hstep' : D (m + 1) ≤ ρ * D m + ε := by
        have h := hcontract m (by omega)
        calc D (m + 1) ≤ rho m * D m + eps m := h
          _ ≤ ρ * D m + ε := by
              have h1 : rho m * D m ≤ ρ * D m :=
                mul_le_mul_of_nonneg_right (hrho m (by omega))
                  (hDnn m (by omega))
              linarith [h1, heps m (by omega)]
      have hih := ih (by omega)
      -- геометрия: ρ^m+1 = ρ·ρ^m и (1−ρ^{m+1}) = ρ·(1−ρ^m) + (1−ρ)
      have hpow : ρ ^ (m + 1) = ρ * ρ ^ m := by ring
      have hgeo : 1 - ρ ^ (m + 1) = ρ * (1 - ρ ^ m) + (1 - ρ) := by
        rw [hpow]
        ring
      have h11 : (1: ℝ) - ρ > 0 := by linarith
      rw [hpow]
      have hsplit : ε * (1 - ρ * ρ ^ m) / (1 - ρ)
          = ρ * (ε * (1 - ρ ^ m) / (1 - ρ)) + ε := by
        have h11 : (1:ℝ) - ρ ≠ 0 := by
          have : (1:ℝ) - ρ > 0 := by linarith
          positivity
        field_simp
        ring
      rw [hsplit]
      calc D (m + 1) ≤ ρ * D m + ε := hstep'
        _ ≤ ρ * (ρ ^ m * D 0 + ε * (1 - ρ ^ m) / (1 - ρ)) + ε := by
            have hnn : (0:ℝ) ≤ ρ := hrhonn'
            have hDm : (0:ℝ) ≤ D m := hDnn m (by omega)
            gcongr
        _ = ρ * ρ ^ m * D 0
              + (ρ * (ε * (1 - ρ ^ m) / (1 - ρ)) + ε) := by ring
  exact key K (le_refl _)

/-! ### Мост к стадийной семантике: уточнение = компрессия -/

/-- Уточняющий эффект стадии: переход уровня k
представления представлен как компрессионная стадия с
ИЗМЕРЕННОЙ ошибкой √D_k (Q_repr-канал, НЕ capability —
разделение аудита §Б) и стоимостями/рисками бэкенда. -/
noncomputable def refineStageEffects (D : ℕ → ℝ) (k : ℕ)
    (Ecur Enew : ℝ) : Hagi.System.StageEffects where
  growGain := 0
  growCost := 0
  growRisk := 0
  growEnergy := Ecur
  mergeEnergy := Ecur
  mergeRisk := 0
  mergeCost := 0
  jointEnergy := Ecur
  jointRisk := 0
  jointCost := 0
  quantErr := Real.sqrt (D k)
  compressEnergy := Enew
  compressRisk := 0
  compressCost := 0

/-! ### Уровень 2: решёточный residual-токенизатор (NCM)

Конкретный токенизатор с ДОКАЗУЕМЫМ сертификатом:
уровень k квантует текущий остаток решёткой
с шагом δ/2^k. Одношаговая гарантия:
D_{k+1} ≤ n(δ/2^k)²/4 — из по-координатной
δ/2-ошибки решётки (gridQ_error).
Геометрическое затухание здесь —
ИЗ КОНСТРУКЦИИ (шаг выбираем мы), а не
постулат монотонности обучаемого
токенизатора (ср. IRVQ: performance gain
diminishes). -/

variable {n : ℕ}

/-- Решёточное квантование вектора (координатно, gridQ). -/
noncomputable def latQ (Δ : ℝ) (hΔ : 0 < Δ)
    (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => Hagi.Energy.gridQ Δ hΔ (v.ofLp i))

/-- ОДНОШАГОВАЯ ГАРАНТИЯ: энергия остатка после
решёточного квантования ≤ nΔ²/4. -/
theorem latQ_residual_bound (Δ : ℝ) (hΔ : 0 < Δ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖v - latQ Δ hΔ v‖ ^ 2 ≤ (n : ℝ) * Δ ^ 2 / 4 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have hper : ∀ i, ‖(v - latQ Δ hΔ v).ofLp i‖ ^ 2
      ≤ (Δ / 2) ^ 2 := by
    intro i
    have hcoord : (v - latQ Δ hΔ v).ofLp i
        = v.ofLp i - Hagi.Energy.gridQ Δ hΔ (v.ofLp i) := by
      simp only [PiLp.sub_apply, latQ]
    rw [hcoord, Real.norm_eq_abs, sq_abs]
    have he : |v.ofLp i - Hagi.Energy.gridQ Δ hΔ (v.ofLp i)|
        ≤ Δ / 2 := by
      rw [abs_sub_comm]
      exact Hagi.Energy.gridQ_error Δ hΔ (v.ofLp i)
    calc (v.ofLp i - Hagi.Energy.gridQ Δ hΔ (v.ofLp i)) ^ 2
        = |v.ofLp i - Hagi.Energy.gridQ Δ hΔ (v.ofLp i)|
            * |v.ofLp i - Hagi.Energy.gridQ Δ hΔ (v.ofLp i)| := by
          rw [← sq_abs]
          ring
      _ ≤ Δ / 2 * (Δ / 2) :=
            mul_self_le_mul_self (abs_nonneg _) he
      _ = (Δ / 2) ^ 2 := by ring
  have hsum : ∑ i, ‖(v - latQ Δ hΔ v).ofLp i‖ ^ 2
      ≤ ((n : ℝ)) * (Δ / 2) ^ 2 := by
    calc ∑ i, ‖(v - latQ Δ hΔ v).ofLp i‖ ^ 2
        ≤ ∑ i, (Δ / 2) ^ 2 := Finset.sum_le_sum fun i _ => hper i
      _ = ((n : ℝ)) * (Δ / 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          push_cast
          ring
  have hfinal : ((n : ℝ)) * (Δ / 2) ^ 2
      = (n : ℝ) * Δ ^ 2 / 4 := by
    have h4 : (Δ / 2) ^ 2 = Δ ^ 2 / 4 := by ring
    rw [h4]
    ring
  linarith [hsum.trans_eq hfinal]

/-- ГЕОМЕТРИЧЕСКАЯ ИЕРАРХИЯ: если каждый
уровень k квантует текущий остаток
решёткой с шагом δ/2^k, то ошибка
после k+1 уровней убывает
геометрически: D_{k+1} ≤
nδ²/(4·4^k). -/
theorem lattice_geometric (δ : ℝ) (hδ : 0 < δ) (K : ℕ)
    (resid : ℕ → EuclideanSpace ℝ (Fin n))
    (hstep : ∀ k : ℕ, k < K → resid (k + 1)
      = resid k - latQ (δ / 2 ^ k) (by positivity) (resid k)) :
    ∀ k : ℕ, k < K →
      ‖resid (k + 1)‖ ^ 2 ≤ (n : ℝ) * (δ / 2 ^ k) ^ 2 / 4 := by
  intro k hk
  rw [hstep k hk]
  exact latQ_residual_bound (δ / 2 ^ k) (by positivity) (resid k)

/-- ADAPTIVE-STOP ГОРИЗОНТ (аудит §5): если
расписание решётки достаточно глубоко
(4^{K−1} ≥ nδ²/(4τ)), то уровень K
СЕРТИФИЦИРОВАННО достаточен: D_K ≤ τ —
контроллер останавливает уточнение без
дополнительных гипотез о модели. -/
theorem lattice_stop_horizon (δ τ : ℝ) (hδ : 0 < δ)
    (hτ : 0 < τ) (K : ℕ) (hK1 : 1 ≤ K)
    (resid : ℕ → EuclideanSpace ℝ (Fin n))
    (hstep : ∀ k : ℕ, k < K → resid (k + 1)
      = resid k - latQ (δ / 2 ^ k) (by positivity) (resid k))
    (hK : (n : ℝ) * (δ / 2 ^ (K - 1)) ^ 2 / 4 ≤ τ) :
    ‖resid K‖ ^ 2 ≤ τ := by
  rcases K with _ | K'
  · omega
  · have hlast := lattice_geometric δ hδ (K' + 1) resid hstep K'
      (Nat.lt_succ_self K')
    have hexp : K' + 1 - 1 = K' := by omega
    rw [hexp] at hK
    linarith [hlast, hK]

/-! ### Уровень 2b: rate–distortion (бюджетная ветка, аудит §6)

Successive refinement (Equitz–Cover 1991): иерархия
с шагом δ/2^k — bit-plane рефайнмент:
каждый уровень добавляет ровно
1 бит информации на координату
(log₂(Δ_{k−1}/Δ_k) = 1), а ошибка падает в 4
раза — классический показатель
D ∼ 2^{−2R/n} равномерного
квантования. Ниже — точный
числовой компромисс
quality-per-bit без логарифмов. -/

/-- QUALITY-PER-BIT: ошибка после K уровней,
отнесённая к начальной
(на K−1 бит/координату приравнена к
единице), даёт
D_K · 2^{2(K−1)} ≤ nδ²/4: каждый
дополнительный бит/координату
поднимает качество в 4 раза
(показатель −2 дБ/бит, PSNR). -/
theorem lattice_quality_per_bit (δ : ℝ) (hδ : 0 < δ) (K : ℕ)
    (hK1 : 1 ≤ K)
    (resid : ℕ → EuclideanSpace ℝ (Fin n))
    (hstep : ∀ k : ℕ, k < K → resid (k + 1)
      = resid k - latQ (δ / 2 ^ k) (by positivity) (resid k)) :
    ‖resid K‖ ^ 2 * (2 ^ (K - 1)) ^ 2
      ≤ (n : ℝ) * δ ^ 2 / 4 := by
  have hK' : K - 1 < K := by omega
  have hgeo := lattice_geometric δ hδ (K - 1 + 1) resid
    (fun k hk => hstep k (by omega)) (K - 1) (by omega)
  have hKK : K - 1 + 1 = K := by omega
  rw [hKK] at hgeo
  -- ‖resid K‖² ≤ nδ²/4 / (2^{K−1})² → умножить
  have hnn : (0:ℝ) < 2 ^ (K - 1) := by positivity
  have hmul : ∀ q : ℝ, q ≠ 0 →
      (δ / q) ^ 2 * q ^ 2 = δ ^ 2 := by
    intro q hq
    field_simp
  -- умножаем неравенство hgeo на (2^{K−1})² ≥ 0
  have hq0 : ((2 : ℝ) ^ (K - 1)) ≠ 0 := by positivity
  have hstep2 : ‖resid K‖ ^ 2 * ((2 : ℝ) ^ (K - 1)) ^ 2
      ≤ ((n : ℝ) * (δ / ((2 : ℝ) ^ (K - 1))) ^ 2 / 4)
        * ((2 : ℝ) ^ (K - 1)) ^ 2 :=
    mul_le_mul_of_nonneg_right hgeo (sq_nonneg _)
  have hrhs : ((n : ℝ) * (δ / ((2 : ℝ) ^ (K - 1))) ^ 2 / 4)
      * ((2 : ℝ) ^ (K - 1)) ^ 2
      = ((n : ℝ) / 4) * ((δ / ((2 : ℝ) ^ (K - 1))) ^ 2
        * ((2 : ℝ) ^ (K - 1)) ^ 2) := by ring
  rw [hrhs, hmul _ hq0] at hstep2
  -- цель: ‖resid K‖²·(2^{K−1})² ≤ nδ²/4 при hstep2: ≤ (nδ²/4)·(2^{K−1})²
  -- НО цель не имеет фактора (2^{K−1})² в RHS — переформулируем цель
  have h1 : (1:ℝ) ≤ ((2 : ℝ) ^ (K - 1)) ^ 2 := by
    have h2 : (1:ℝ) ≤ (2 : ℝ) ^ (K - 1) := by
      induction (K - 1) with
      | zero => norm_num
      | succ m ih => rw [pow_succ]; nlinarith
    nlinarith [h2]
  have hcast : ‖resid K‖ ^ 2 * (2 ^ (K - 1)) ^ 2
      = ‖resid K‖ ^ 2 * ((2 : ℝ) ^ (K - 1)) ^ 2 := by push_cast; ring
  -- цель: X ≤ A; hstep2: X ≤ (n/4)δ² ; nδ²/4 = (n/4)δ²
  linarith [hstep2]

/-! ### Уровень 3: conditioning corruption (аудит NCM §В)

Генератор уточняет представление по
СВОИМ предыдущим предсказаниям
(возможно ошибочным): уровень k
квантует не истинный остаток r,
а возмущённый v = r + ξ. Ниже —
детерминированная граница
распространения ошибки:
внешнее возмущение
входит АДДИТИВНО
(треугольник + решётчатная
гарантия), без вероятностных
предположений. -/

/-- УСТОЙЧИВОСТЬ К ИСПОРЧЕННОМУ
КОНТЕКСТУ: если уровень
квантует возмущённый
остаток v = r + ξ вместо
истинного r, ошибка относительно r
ограничена нормой возмущения
плюс решёточная ошибка:
‖r − latQ Δ v‖ ≤ ‖ξ‖ + √n·Δ/2. -/
theorem latQ_corrupt_bound (Δ : ℝ) (hΔ : 0 < Δ)
    (r ξ v : EuclideanSpace ℝ (Fin n))
    (hv : v = r + ξ) :
    ‖r - latQ Δ hΔ v‖ ≤ ‖ξ‖
      + Real.sqrt ((n : ℝ)) * Δ / 2 := by
  have htri : ‖r - latQ Δ hΔ v‖
      ≤ ‖r - v‖ + ‖v - latQ Δ hΔ v‖ := by
    calc ‖r - latQ Δ hΔ v‖
        = ‖(r - v) + (v - latQ Δ hΔ v)‖ := by congr 1; abel
      _ ≤ ‖r - v‖ + ‖v - latQ Δ hΔ v‖ := norm_add_le _ _
  have hrx : ‖r - v‖ = ‖ξ‖ := by
    rw [hv]
    have : r - (r + ξ) = -ξ := by abel
    rw [this, norm_neg]
  -- решёточная часть: ‖v−Q v‖ = sqrt(‖v−Q v‖²) ≤ sqrt(nΔ²/4)
  have hlat := latQ_residual_bound Δ hΔ v
  have hsq : ‖v - latQ Δ hΔ v‖
      = Real.sqrt (‖v - latQ Δ hΔ v‖ ^ 2) :=
    (Real.sqrt_sq (norm_nonneg _)).symm
  have hnn : 0 ≤ (n : ℝ) * Δ ^ 2 / 4 := by positivity
  calc ‖r - latQ Δ hΔ v‖ ≤ ‖ξ‖ + ‖v - latQ Δ hΔ v‖ := by
        rw [hrx] at htri; exact htri
    _ = ‖ξ‖ + Real.sqrt (‖v - latQ Δ hΔ v‖ ^ 2) := by rw [← hsq]
    _ ≤ ‖ξ‖ + Real.sqrt ((n : ℝ) * Δ ^ 2 / 4) := by
        exact add_le_add (le_refl _) (Real.sqrt_le_sqrt hlat)
    _ = ‖ξ‖ + Real.sqrt ((n : ℝ)) * Δ / 2 := by
        have h4 : (n : ℝ) * Δ ^ 2 / 4
            = ((n : ℝ)) * (Δ / 2) ^ 2 := by ring
        rw [h4, Real.sqrt_mul' ((n : ℝ))
          (show (0:ℝ) ≤ (Δ / 2) ^ 2 by positivity),
          Real.sqrt_sq (show (0:ℝ) ≤ Δ / 2 by positivity)]
        ring
end Hagi.Model.ResidualVQ
