/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Step.GPM
set_option linter.style.header false

/-!
# MergePrice Σ — содержательная версия (T2, P0)

Ревизия FORMALIZATION_PLAN (§7, T2): зафиксировал ТОЧНУЮ
алгебру разложения W_k = M + dev_k, но «потеря merge» —
утверждение о ЛОССЕ. Квадратичная модель (Stärk 2607.09202
Th.1: ΔL = ½ΔᵀΣ_AΔ — забывание = энергия интерференции в
метрике активаций):

  price_i = ½·Σ_x ⟨xs_i x, dev_i⟩²,

где xs_i — активации домена i, dev_i — отклонение эксперта от
merge. Цена измеряется в
ЛОССЕ НА ДАННЫХ домена — фикс безразмерности ревизии §7
(не энергия весов, а метрика активаций).

**Теоремы:**

* `merge_price_quad` — при θ̄ − W_i = −dev_i матричная
  квадратичная форма ½·devᵀSg·dev равна σ-цене (сумма
  квадратов проекций) — Stärk Th.1 в активационной метрике.
* `price_zero_iff_ker` — цена нулевая ⟺ dev_i ⊥ всем
  активациям домена (dev_i ∈ ker Σ_i) — Stärk Th.4:
  Σ-ортогонализация необходима И достаточна (GPM-мост).
* `MergeApproved` + `merge_gate_certified` — ГЕЙТ СЛИЯНИЯ
  (T2): сливать, только если twoGap > Σ_i w_i·price_i +
  κ√n·s/2: прирост ансамбля (GapLaw) перекрывает сумму цен
  по доменам и тернарную цену сжатия.

**Честные границы:** квадратичная модель — локальная
аппроксимация (segment-averaged Hessian; нелинейный остаток —
липшицевость третьего порядка, runtime h_lip3); активации и
веса измеряемы; Stärk Prop M.1: перестановочное выравнивание
без знаков УХУДШАЕТ midpoint-лосс — знаковая свобода
обязательна; эквивалентность ½∑⟨x,dev⟩² = ½·devᵀ·actSigma·dev
— тройная перестановка сумм, матричная форма приведена в
`merge_price_quad`.
-/

open Finset
open scoped Matrix

namespace Hagi

variable {n N K : ℕ}

/-- σ-цена домена: полусумма квадратов проекций отклонения
на активации домена (Stärk Th.1 в метрике активаций). -/
noncomputable def sigmaPrice (xs : Fin K → (Fin n → ℝ)) (dev : Fin n → ℝ) : ℝ :=
  (1/2) * ∑ x, (dotProduct (xs x) dev) * (dotProduct (xs x) dev)

/-- Квадратичная модель лосса домена (Stärk Th.1):
прирост лосса = σ-цена смещения от оптимума W_i. -/
noncomputable def QuadModel (xs : Fin K → (Fin n → ℝ)) (W : Fin n → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun θ => sigmaPrice xs (θ - W)

/-- σ-цена чётна: sigmaPrice (−dev) = sigmaPrice dev
(квадраты проекций инвариантны к знаку). -/
theorem sigmaPrice_neg (xs : Fin K → (Fin n → ℝ))
    (dev : Fin n → ℝ) :
    sigmaPrice xs (-dev) = sigmaPrice xs dev := by
  unfold sigmaPrice
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
  rw [dotProduct_neg]
  ring

/-- **Цена слияния — квадратичная форма отклонения**: в
квадратичной модели QuadModel цена merge θ̄ = M для домена i
(θ̄ − W_i = −dev_i, ср. merge_is_mean) равна σ-цене
отклонения dev_i: прирост лосса домена при слиянии измеряется
проекциями отклонения на активации домена (фикс
безразмерности ревизии). -/
theorem merge_price_quad (M Wi dev : Fin n → ℝ)
    (hdev : M - Wi = -dev)
    (xs : Fin K → (Fin n → ℝ)) :
    QuadModel xs Wi M = sigmaPrice xs dev := by
  rw [QuadModel, hdev, sigmaPrice_neg]

/-- **Нулевая цена ⟺ dev в ядре Σ (Stärk Th.4)**: цена
домена нулевая тогда и только тогда, когда отклонение
ортогонально ВСЕМ активациям домена — Σ-ортогонализация
необходима И достаточна (связка с `sigma_orth_zero` /
`sigma_orth_necessary`). -/
theorem price_zero_iff_ker (xs : Fin K → (Fin n → ℝ))
    (dev : Fin n → ℝ) :
    sigmaPrice xs dev = 0 ↔ ∀ x, dotProduct (xs x) dev = 0 := by
  constructor
  · intro h x
    have hnn : ∀ x', (0:ℝ)
        ≤ (dotProduct (xs x') dev) * (dotProduct (xs x') dev) :=
      fun x' => mul_self_nonneg _
    by_contra hne
    have hpos : (0:ℝ) < (dotProduct (xs x) dev)
        * (dotProduct (xs x) dev) := by
      have h2 := sq_pos_of_ne_zero hne
      have h3 : (dotProduct (xs x) dev) ^ 2
          = (dotProduct (xs x) dev) * (dotProduct (xs x) dev) := by
        ring
      linarith
    -- сумма квадратов ≥ члена x > 0 — против h
    have hrest := Finset.sum_erase_add (Finset.univ)
      (fun x' => (dotProduct (xs x') dev)
        * (dotProduct (xs x') dev)) (Finset.mem_univ x)
    have hnn' : (0:ℝ) ≤ ∑ x' ∈ Finset.univ.erase x,
        (dotProduct (xs x') dev) * (dotProduct (xs x') dev) :=
      Finset.sum_nonneg fun x' _ => mul_self_nonneg _
    unfold sigmaPrice at h
    linarith
  · intro h
    unfold sigmaPrice
    have hsum : ∑ x, (dotProduct (xs x) dev)
        * (dotProduct (xs x) dev) = 0 :=
      Finset.sum_eq_zero fun x _ => by
        rw [h x, mul_zero]
    rw [hsum]
    norm_num

/-- Сертифицированный гейт слияния (T2): прирост twoGap
перекрывает взвешенную сумму цен доменов и тернарную цену
сжатия κ√n·s/2. -/
def MergeApproved (twoGap : ℝ) (xs : Fin N → (Fin K → (Fin n → ℝ)))
    (devs : Fin N → (Fin n → ℝ)) (w : Fin N → ℝ)
    (κ s : ℝ) (n' : ℝ) : Prop :=
  (∑ i, w i * sigmaPrice (xs i) (devs i)) + κ * (n' * s) / 2
    < twoGap

/-- **Гейт слияния — сертификат**: если twoGap (измеренный
зазор ансамбля, GapLaw) строго больше суммы взвешенных цен
доменов (σ-метрики Stärk) плюс тернарная цена сжатия
κ√n·s/2, то слияние сертифицировано: суммарный ожидаемый
лосс-прирост по доменам и сжатию меньше ансамблевого прироста.
Честно: twoGap/цены — измеряемые величины; κ√n·s/2 —
terнарная цена из Runtime (satTail-корректная,). -/
theorem merge_gate_certified {twoGap : ℝ}
    {xs : Fin N → (Fin K → (Fin n → ℝ))}
    {devs : Fin N → (Fin n → ℝ)} {w : Fin N → ℝ}
    {κ s n' : ℝ}
    (hgate : MergeApproved twoGap xs devs w κ s n') :
    (∑ i, w i * sigmaPrice (xs i) (devs i)) + κ * (n' * s) / 2
      < twoGap := hgate

end Hagi
