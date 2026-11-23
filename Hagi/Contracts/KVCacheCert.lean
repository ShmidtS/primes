/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Cert.StepGen
import Mathlib.Tactic

set_option linter.style.header false

/-!
# KV-cache inference: cached attention IS exact recompute

The sequence-inference extension of the compute-certification line
(`SparseInferenceCert` `ComputeToQuality`): the KV-cache
certificate — cached attention (each new token attends over stored
keys/values through a running summary) has per-token work `t + 1`
while the recompute-from-scratch regime RE-ATTENDS every past
token at every step, and the cached output is EXACTLY the full
recomputation. Only the PACKAGING is new; every ingredient is at
the honest List level:

* the exactness object is route (b) of the analysis: softmax
  attention does NOT decompose additively in its WEIGHTS (the
  normalizer is global), but the (den, num) accumulator pair does:
  den = Σ e^{q·k}, num = Σ e^{q·k}·v are PLAIN SUMS over the token
  list, so the incremental update (den + e^s, num + e^s·v) is
  exactly one appended term — `kv_cache_exact`. The running
  logsumexp is the log-image of the additive den:
  `lseCombine a b = log(eᵃ + eᵇ)` is associative
  (`lse_combine_assoc`, proved exactly) and combines the
  normalizers (`lse_cache_step`); route (a) (linear/GDN-style
  additive summaries, the `Hagi.External.MemT.GDN2` lag-1
  recurrent contrast) decomposes even more trivially and is cited
  as the contrast, not formalized here;
* the work model is the discipline (`localField_dense_
  work`, `denseMatVecWork` style): ℕ definitions, theorems only
  ABOUT the products, division-free product identities —
  `2·cachedTotalWork n = n(n+1)` (quadratic) against
  `6·recomputeTotalWork n = n(n+1)(n+2)` (cubic), exact ratio
  `(n+2)/3` (`kv_work_ratio`), strict cached < recompute for
  n ≥ 2 (`kv_total_work_lt`);
* the certified transition is the packaging pattern
  (`sparse_step_certified` over the kernel
  `Hagi.Cert.CertStepGen`): `kv_step_certified` spends
  `cachedTokenWork` in the budget channel and ZERO in the risk
  channel — exactness (`kv_cache_exact`) makes the error spend
  zero; that is the certificate.

Honest scope:

* SINGLE head, SCALAR carrier: score = q·k on ℝ, value ∈ ℝ; the
  token list carries (key, value) pairs (no `List.zip` truncation
  hazard); streaming incremental form only.
* NO memory-layout claims (no paged/blocked cache, no capacity
  eviction); NO d² projection accounting — projections are
  excluded from BOTH regimes, the certificate is the
  attention-pass count contrast alone; no multi-head, no
  numerical-stability claim (the lse form is GIVEN as the stable
  image, not proven superior).
* Work measured in the entry-read model; no asymptotics in
  statements; numbers live in the numeric `Anchor` lemmas only.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.KVCacheCert

open scoped BigOperators

/-! ## The carrier: score, cache state, full recompute -/

/-- Score of key `k` against query `q` (single head, scalar). -/
def score (q k : ℝ) : ℝ := q * k

/-- The KV-cache state: the stored normalizer (Σ e^{q·k}) and the
stored weighted-value sum (Σ e^{q·k}·v) — the running summary. -/
structure KVCache where
  /-- Stored normalizer `Σ e^{score}`. -/
  den : ℝ
  /-- Stored weighted-value sum `Σ e^{score}·v`. -/
  num : ℝ

/-- The empty cache (empty prefix: den = num = 0). -/
def kvEmpty : KVCache := ⟨0, 0⟩

/-- One incremental cache update: the token `(k, v)` is appended;
the summary gains exactly the new term. -/
noncomputable def kvStep (q : ℝ) (c : KVCache) (k v : ℝ) : KVCache :=
  ⟨c.den + Real.exp (score q k), c.num + Real.exp (score q k) * v⟩

/-- Full-recompute denominator over a token list: `Σ e^{score}`. -/
noncomputable def tokDen (q : ℝ) (toks : List (ℝ × ℝ)) : ℝ :=
  (toks.map fun t => Real.exp (score q t.1)).sum

/-- Full-recompute numerator over a token list:
`Σ e^{score}·v` (the weighted value sum). -/
noncomputable def tokNum (q : ℝ) (toks : List (ℝ × ℝ)) : ℝ :=
  (toks.map fun t => Real.exp (score q t.1) * t.2).sum

/-- Full softmax attention output: weighted value sum over the
global normalizer — the recompute-from-scratch reference. -/
noncomputable def tokFull (q : ℝ) (toks : List (ℝ × ℝ)) : ℝ :=
  tokNum q toks / tokDen q toks

/-- The cache built from a prefix by incremental updates
(foldl over the token list — the streaming build). -/
noncomputable def tokKV (q : ℝ) (toks : List (ℝ × ℝ)) : KVCache :=
  toks.foldl (fun c t => kvStep q c t.1 t.2) kvEmpty

/-- Cached attention output for a new token, computed from the
stored summary only: `(num + e^s·v) / (den + e^s)`. -/
noncomputable def cachedAttn (c : KVCache) (s v : ℝ) : ℝ :=
  (c.num + Real.exp s * v) / (c.den + Real.exp s)

/-! ## The exactness engine (foldl accumulator = map-sum) -/

/-- **Engine (den)**: the streaming foldl accumulator's den is the
initial den plus the map-sum of exponentials — induction over the
token list. -/
theorem foldl_den_eq (q : ℝ) (toks : List (ℝ × ℝ)) (c : KVCache) :
    (toks.foldl (fun c t => kvStep q c t.1 t.2) c).den
      = c.den + tokDen q toks := by
  induction toks generalizing c with
  | nil => simp [tokDen]
  | cons t ts ih =>
    rw [List.foldl_cons, ih]
    simp only [tokDen, List.map_cons, List.sum_cons, kvStep]
    ring

/-- **Engine (num)**: the streaming foldl accumulator's num is the
initial num plus the map-sum of weighted values. -/
theorem foldl_num_eq (q : ℝ) (toks : List (ℝ × ℝ)) (c : KVCache) :
    (toks.foldl (fun c t => kvStep q c t.1 t.2) c).num
      = c.num + tokNum q toks := by
  induction toks generalizing c with
  | nil => simp [tokNum]
  | cons t ts ih =>
    rw [List.foldl_cons, ih]
    simp only [tokNum, List.map_cons, List.sum_cons, kvStep]
    ring

/-- **Append (den)**: appending one token adds exactly its
exponential to the denominator. -/
theorem tokDen_append (q k v : ℝ) (toks : List (ℝ × ℝ)) :
    tokDen q (toks ++ [(k, v)])
      = tokDen q toks + Real.exp (score q k) := by
  simp [tokDen, List.map_append, List.sum_append]

/-- **Append (num)**: appending one token adds exactly its
weighted value to the numerator. -/
theorem tokNum_append (q k v : ℝ) (toks : List (ℝ × ℝ)) :
    tokNum q (toks ++ [(k, v)])
      = tokNum q toks + Real.exp (score q k) * v := by
  simp [tokNum, List.map_append, List.sum_append]

/-- **MAIN 1 — the KV-cache correctness**: the cached incremental
output (from the stored summary alone) EQUALS the full
recomputation over the extended token list — `cached = exact
recompute`, at the List carrier level. Near-definitional BY DESIGN:
the honest object is the (den, num) pair of plain sums (softmax
weights themselves do NOT decompose; the normalizer is carried
along — route (b) of the analysis). -/
theorem kv_cache_exact (q k v : ℝ) (toks : List (ℝ × ℝ)) :
    cachedAttn (tokKV q toks) (score q k) v
      = tokFull q (toks ++ [(k, v)]) := by
  have hden : (tokKV q toks).den = tokDen q toks := by
    have h := foldl_den_eq q toks kvEmpty
    simpa [tokKV, kvEmpty] using h
  have hnum : (tokKV q toks).num = tokNum q toks := by
    have h := foldl_num_eq q toks kvEmpty
    simpa [tokKV, kvEmpty] using h
  unfold cachedAttn tokFull
  rw [hnum, hden, tokDen_append, tokNum_append]

/-! ## The running logsumexp layer -/

/-- Log-sum-exp combine: the associative log-image of the additive
denominator update. -/
noncomputable def lseCombine (a b : ℝ) : ℝ :=
  Real.log (Real.exp a + Real.exp b)

/-- The denominator of a nonempty token list is positive (every
exponential is positive; `List.sum_pos`). -/
theorem den_pos (q : ℝ) (toks : List (ℝ × ℝ)) (hne : toks ≠ []) :
    0 < tokDen q toks := by
  induction toks with
  | nil => exact absurd rfl hne
  | cons t ts ih =>
    simp only [tokDen]
    exact List.sum_pos _ (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨t', _, hx'⟩ := hx
      rw [← hx']
      exact Real.exp_pos _) (by simp)

/-- **lse combine is associative** — proved EXACTLY (no numerics):
`log(e^{log(eᵃ+eᵇ)} + e^c) = log(eᵃ + e^{log(eᵇ+e^c)})` by
`Real.exp_log` on positive sums and plain `add_assoc`. The
running-normalizer update can be applied in any grouping. -/
theorem lse_combine_assoc (a b c : ℝ) :
    lseCombine (lseCombine a b) c = lseCombine a (lseCombine b c) := by
  have h1 : 0 < Real.exp a + Real.exp b := by
    have := Real.exp_pos a; have := Real.exp_pos b; linarith
  have h2 : 0 < Real.exp b + Real.exp c := by
    have := Real.exp_pos b; have := Real.exp_pos c; linarith
  unfold lseCombine
  rw [Real.exp_log h1, Real.exp_log h2]
  congr 1
  ring

/-- **Running logsumexp**: the log-denominator of the extended
list is the lse-combine of the stored log-denominator and the new
score — the stable-image form of `tokDen_append` (needs a nonempty
prefix: the log of the empty den 0 is undefined). -/
theorem lse_cache_step (q k v : ℝ) (toks : List (ℝ × ℝ))
    (hne : toks ≠ []) :
    Real.log (tokDen q (toks ++ [(k, v)]))
      = lseCombine (Real.log (tokDen q toks)) (score q k) := by
  have hpos := den_pos q toks hne
  unfold lseCombine
  rw [tokDen_append, Real.exp_log hpos]

/-! ## The work model (discipline, division-free) -/

/-- Cached per-token work at prefix length `t`: the new query's
ONE pass over the `t` stored keys plus itself — `t + 1`
entry-reads. (Projections excluded from BOTH regimes: the
certificate is the attention-pass contrast.) -/
def cachedTokenWork (t : ℕ) : ℕ := t + 1

/-- Recompute-regime per-token work at prefix length `t`:
regenerating from scratch re-attends EVERY past token — token `s`
(of the `t + 1` in the prefix) attends `s + 1` keys, summed. -/
def recomputeTokenWork (t : ℕ) : ℕ := ∑ s ∈ Finset.range (t + 1), (s + 1)

/-- Cached total work over an `n`-token stream: the sum of the
per-token passes — the QUADRATIC regime. -/
def cachedTotalWork (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range n, cachedTokenWork t

/-- Recompute total work over an `n`-token stream: every step
re-runs the whole prefix — the CUBIC regime. -/
def recomputeTotalWork (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range n, recomputeTokenWork t

/-- **Per-token cached bound**: with constant `C ≥ 1`, the cached
per-token work is at most `C·(t + 1)` — the honest O(n) per-token
statement (constant 1 already achieves it: the pass is exactly
`t + 1` reads). -/
theorem cached_step_work_le (t C : ℕ) (hC : 1 ≤ C) :
    cachedTokenWork t ≤ C * (t + 1) := by
  unfold cachedTokenWork
  nlinarith

/-- **The honest split**: the recompute-regime step work is the
cached step work PLUS the re-attended past (the inner sum over
`s < t`) — the recomputation of previous tokens is the entire
difference between the regimes. -/
theorem recompute_step_split (t : ℕ) :
    recomputeTokenWork t
      = cachedTokenWork t + ∑ s ∈ Finset.range t, (s + 1) := by
  unfold recomputeTokenWork cachedTokenWork
  rw [Finset.sum_range_succ]
  omega

theorem cachedTotalWork_succ (n : ℕ) :
    cachedTotalWork (n + 1)
      = cachedTotalWork n + cachedTokenWork n := by
  unfold cachedTotalWork
  rw [Finset.sum_range_succ]

theorem recomputeTokenWork_succ (t : ℕ) :
    recomputeTokenWork (t + 1)
      = recomputeTokenWork t + (t + 2) := by
  unfold recomputeTokenWork
  rw [Finset.sum_range_succ]

/-- **Cached step closed form** (division-free): twice the
recompute step work is `(t+1)(t+2)` — the triangular number
identity `∑_{s ≤ t} (s+1) = (t+1)(t+2)/2` without ℕ division. -/
theorem recompute_step_work_eq (t : ℕ) :
    2 * recomputeTokenWork t = (t + 1) * (t + 2) := by
  induction t with
  | zero => simp [recomputeTokenWork]
  | succ t ih =>
    rw [recomputeTokenWork_succ]
    have h : (t + 1) * (t + 2) + 2 * (t + 2)
        = (t + 2) * (t + 3) := by ring
    nlinarith [ih, h]

/-- **MAIN 2 (cached total, quadratic)**: the cached total work
identity — `2·cachedTotalWork n = n(n+1)` (division-free form of
the triangular sum; induction, no ℕ division). -/
theorem cached_total_work_eq (n : ℕ) :
    2 * cachedTotalWork n = n * (n + 1) := by
  induction n with
  | zero => simp [cachedTotalWork]
  | succ n ih =>
    rw [cachedTotalWork_succ]
    have h : n * (n + 1) + 2 * (n + 1) = (n + 1) * (n + 2) := by ring
    unfold cachedTokenWork
    nlinarith [ih, h]

/-- **MAIN 2 (recompute total, cubic)**: the recompute total work
identity — `6·recomputeTotalWork n = n(n+1)(n+2)` (division-free
tetrahedral identity; induction over the step recursion with the
step closed form `recompute_step_work_eq`). -/
theorem recompute_total_work_eq (n : ℕ) :
    6 * recomputeTotalWork n = n * (n + 1) * (n + 2) := by
  induction n with
  | zero => simp [recomputeTotalWork]
  | succ n ih =>
    have hstep := recompute_step_work_eq n
    have hrec : recomputeTotalWork (n + 1)
        = recomputeTotalWork n + recomputeTokenWork n := by
      unfold recomputeTotalWork
      rw [Finset.sum_range_succ]
    rw [hrec]
    have h : n * (n + 1) * (n + 2) + 3 * ((n + 1) * (n + 2))
        = (n + 1) * (n + 2) * (n + 3) := by ring
    nlinarith [ih, hstep, h]

/-- **MAIN 2 — the exact compute ratio**: the recompute total is
EXACTLY `(n+2)/3` times the cached total — the cubic-vs-quadratic
KV-cache account in one identity (`3·recompute = (n+2)·cached`),
cancellation of the factor 2 from the two product identities. -/
theorem kv_work_ratio (n : ℕ) :
    3 * recomputeTotalWork n = (n + 2) * cachedTotalWork n := by
  have h6 : 6 * recomputeTotalWork n = (n + 2) * (2 * cachedTotalWork n) := by
    have hA := recompute_total_work_eq n
    have hB := cached_total_work_eq n
    nlinarith [hA, hB]
  have h2 : 2 * (3 * recomputeTotalWork n)
      = 2 * ((n + 2) * cachedTotalWork n) := by
    calc 2 * (3 * recomputeTotalWork n)
        = 6 * recomputeTotalWork n := by ring
      _ = (n + 2) * (2 * cachedTotalWork n) := h6
      _ = 2 * ((n + 2) * cachedTotalWork n) := by ring
  exact Nat.mul_left_cancel (by norm_num) h2

/-- **MAIN 3 — strict total-work advantage**: from the second
token on, the cached total work is STRICTLY below the recompute
total (the t = 1 step already pays one re-attended past token).
The premise is necessary: at n ≤ 1 the regimes coincide. -/
theorem kv_total_work_lt (n : ℕ) (hn : 2 ≤ n) :
    cachedTotalWork n < recomputeTotalWork n := by
  have hsplit : recomputeTotalWork n
      = cachedTotalWork n
        + ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range t, (s + 1) := by
    unfold recomputeTotalWork cachedTotalWork
    rw [Finset.sum_congr rfl (fun t _ => recompute_step_split t)]
    simp [Finset.sum_add_distrib]
  have hterm : (∑ s ∈ Finset.range (1 : ℕ), (s + 1))
      ≤ ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range t, (s + 1) :=
    Finset.single_le_sum
      (f := fun t => ∑ s ∈ Finset.range t, (s + 1))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn)
  have h1 : (∑ s ∈ Finset.range (1 : ℕ), (s + 1)) = 1 := by simp
  omega

/-! ## The certified transition (packaging over the kernel) -/

/-- **The KV-cache step IS a certified transition**: the cached
attention step packaged as a `Hagi.Cert.CertStepGen` (
`sparse_step_certified` pattern): the budget channel spends the
cached per-token work `workSpend` (instantiate at
`cachedTokenWork t`; the compute accounting), the risk channel
spends ZERO error — exactness (`kv_cache_exact`) makes the error
spend zero with the full prior risk as the explicit nonnegative
remainder (the no-zero-pinning lesson) — that is the
certificate: correctness + the cost statement in one object. -/
noncomputable def kv_step_certified {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ)
    (workSpend : ℝ) (s s' : S)
    (drop : ℝ) (hdrop : 0 < drop)
    (hdesc : M.objective s' ≤ M.objective s - drop)
    (hbud : M.budget s' = M.budget s - workSpend)
    (hbudnn : 0 ≤ M.budget s')
    (riskRem : ℝ)
    (hrisk : M.risk s = 0 + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (delta : ℝ)
    (hdelta : deltaLevel s' = deltaLevel s - delta)
    (hdeltaNN : 0 ≤ deltaLevel s')
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    Hagi.Cert.CertStepGen M obl deltaLevel s s' where
  drop := drop
  drop_pos := hdrop
  descent := hdesc
  budgetSpend := workSpend
  budget_next := hbud
  budget_nonneg := hbudnn
  riskSpend := 0
  riskRem := riskRem
  risk_next := hrisk'
  risk_split := hrisk
  risk_nonneg := hrem
  delta := delta
  delta_next := hdelta
  delta_nonneg := hdeltaNN
  floorsKept := hfloors

/-- The risk spend of the packaged KV-cache step is exactly zero —
the exactness half of the certificate, structurally. -/
theorem kv_step_certified_zeroError {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ)
    (workSpend : ℝ) {s s' : S}
    (drop : ℝ) (hdrop : 0 < drop)
    (hdesc : M.objective s' ≤ M.objective s - drop)
    (hbud : M.budget s' = M.budget s - workSpend)
    (hbudnn : 0 ≤ M.budget s')
    (riskRem : ℝ)
    (hrisk : M.risk s = 0 + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (delta : ℝ)
    (hdelta : deltaLevel s' = deltaLevel s - delta)
    (hdeltaNN : 0 ≤ deltaLevel s')
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    (kv_step_certified M obl deltaLevel workSpend s s' drop hdrop
      hdesc hbud hbudnn riskRem hrisk hrisk' hrem delta hdelta hdeltaNN
      hfloors).riskSpend = 0 := rfl

/-- The compute spend of the packaged KV-cache step is the work
argument (instantiate at `cachedTokenWork t`). -/
theorem kv_step_certified_budgetSpend {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ)
    (workSpend : ℝ) {s s' : S}
    (drop : ℝ) (hdrop : 0 < drop)
    (hdesc : M.objective s' ≤ M.objective s - drop)
    (hbud : M.budget s' = M.budget s - workSpend)
    (hbudnn : 0 ≤ M.budget s')
    (riskRem : ℝ)
    (hrisk : M.risk s = 0 + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (delta : ℝ)
    (hdelta : deltaLevel s' = deltaLevel s - delta)
    (hdeltaNN : 0 ≤ deltaLevel s')
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    (kv_step_certified M obl deltaLevel workSpend s s' drop hdrop
      hdesc hbud hbudnn riskRem hrisk hrisk' hrem delta hdelta hdeltaNN
      hfloors).budgetSpend = workSpend := rfl

/-! ## Numeric anchors: the 3-token sequence -/

namespace Anchor

/-- The anchor prefix: two tokens, scores `1·0 = 0`, values 1, 2. -/
private def pre : List (ℝ × ℝ) := [(0, 1), (0, 2)]

/-- The full 3-token anchor: scores 0, 0, 0; values 1, 2, 3. -/
private def toks3 : List (ℝ × ℝ) := [(0, 1), (0, 2), (0, 3)]

/-- **Full-recompute anchor**: uniform weights (all e⁰ = 1) give
attention output `(1+2+3)/3 = 2`. -/
private theorem anchor_full : tokFull 1 toks3 = 2 := by
  simp only [tokFull, tokNum, tokDen, score, toks3, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

/-- **Cached-incremental anchor**: the third token computed from
the two-token cache — THROUGH `kv_cache_exact` (not a bare
computation): the cached step equals the full recompute = 2. -/
theorem anchor_cached :
    cachedAttn (tokKV 1 pre) (score 1 0) 3 = 2 := by
  rw [kv_cache_exact 1 0 3 pre]
  have : pre ++ [(0, 3)] = toks3 := by
    simp [pre, toks3]
  rw [this, anchor_full]

/-- **lse-combine anchor**: the running normalizer in log space —
`lseCombine (log 2) 0 = log 3` (denominators 2 → 3). -/
theorem anchor_lse : lseCombine (Real.log 2) 0 = Real.log 3 := by
  unfold lseCombine
  rw [Real.exp_log (by norm_num), Real.exp_zero]
  norm_num

/-- **Work anchors**: the 3-token stream costs `cachedTotalWork 3
= 1+2+3 = 6` cached reads against `recomputeTotalWork 3 =
1+3+6 = 10` recompute reads — the exact ratio
`(3+2)/3 = 10/6` of `kv_work_ratio`. -/
theorem anchor_work :
    cachedTotalWork 3 = 6 ∧ recomputeTotalWork 3 = 10 := by
  constructor
  · norm_num [cachedTotalWork, cachedTokenWork,
      Finset.sum_range_succ]
  · norm_num [recomputeTotalWork, recomputeTokenWork,
      Finset.sum_range_succ]

end Anchor

end Hagi.Contracts.KVCacheCert
