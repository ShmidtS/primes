# Open Erdos Prize Problems — Complete List with Lean Project Relevance

Source: https://www.erdosproblems.com/ (YAML from https://github.com/teorth/erdosproblems)
Total problems in database: 1217
Open problems with monetary prize: 55
Fetched: 2026-07-02

---

## Tier 1: HIGHLY RELEVANT to this Lean project

These problems map directly to infrastructure already formalized in the project.

### Problem 687 — Prize: $1000 — Status: Open
- **URL**: https://www.erdosproblems.com/687
- **Tags**: number theory
- **OEIS**: A048670, A058989
- **Formalized in Lean (DeepMind)**: No
- **Statement**: Let Y(x) be the maximal y such that there exists a choice of congruence classes a_p for all primes p<=x such that every integer in [1,y] is congruent to at least one of the a_p mod p. Give good estimates for Y(x). In particular, can one prove that Y(x)=o(x^2) or even Y(x)<<x^{1+o(1)}?
- **Notes**: Jacobsthal function. Closely related to prime gaps (see Problem 4). Best upper bound Y(x)<<x^2 (Iwaniec). Best lower bound Y(x)>>x*log(x)*logloglog(x)/loglog(x) (Ford-Green-Konyagin-Maynard-Tao). Maier-Pomerance conjecture: Y(x)<<x*(log x)^{2+o(1)}.
- **Lean relevance**: **VERY HIGH**. The project has:
  - `coprimeResidues` (Wheel.lean) — residue class enumeration
  - `endpointForbiddenResidueCount` (GapFrequency.lean) — counting forbidden residues
  - `wheelCandidates`, `wheelGaps` (Wheel.lean) — covering via residue classes
  - `PrimeFreeInterval` (PrimeFree.lean) — intervals without primes
  - `primorial` bounds (PrimeFree.lean) — direct connection to Jacobsthal
  - The problem is essentially about covering intervals with residue classes mod primes, which is what the wheel/sieve infrastructure models.

### Problem 143 — Prize: $500 — Status: Open
- **URL**: https://www.erdosproblems.com/143
- **Tags**: primitive sets
- **OEIS**: N/A
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Let A subset (1,infinity) be a countably infinite set such that for all x!=y in A and integers k>=1 we have |kx-y|>=1. Does this imply that A is sparse? In particular, does this imply that sum_{x in A} 1/(x log x) < infinity or sum_{x<n, x in A} 1/x = o(log n)?
- **Notes**: If A is a set of integers then the condition implies A is a primitive set (no element divides another). Convergence of sum 1/(n log n) for primitive sets was proved by Erdos [Er35]. Partially resolved by Koukoulopoulos-Lamzouri-Lichtman [KLL25] who proved sum 1/x = o(log n).
- **Lean relevance**: **VERY HIGH**. The project has:
  - `IsPrimitiveSet` (VonMangoldtChain.lean:43) — exact definition of primitive sets
  - `erdosWeight` = 1/(n log n) (VonMangoldtChain.lean:47) — the weight in the conjecture
  - `erdosSum` (VonMangoldtChain.lean:50) — the sum over a primitive set
  - `erdos_primitive_set_bound_finite` (VonMangoldtChain.lean:85) — finite version of Erdos's bound
  - `DivisibilityChain` structure (VonMangoldtChain.lean:58)
  - `mertens_chain_bound` (VonMangoldtChain.lean:99)
  - This is the MOST directly attackable problem with existing infrastructure.

### Problem 470 — Prize: $10 — Status: Open
- **URL**: https://www.erdosproblems.com/470
- **Tags**: number theory, divisors
- **OEIS**: A006037, A002975
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Call n weird if sigma(n)>=2n and n is not pseudoperfect (not the sum of any set of its divisors). Are there any odd weird numbers? Are there infinitely many primitive weird numbers (no proper divisor of n is weird)?
- **Notes**: Smallest weird number is 70. Melfi proved infinitely many primitive weird numbers conditional on prime gap bound p_{n+1}-p_n < (1/10)*p_n^{1/2}. No odd weird numbers below 10^21. Odd weird number must have >= 6 prime divisors.
- **Lean relevance**: **HIGH**. The project has:
  - `divisorCorrectionProduct` (SingularSeries.lean:41) — divisor product structure
  - `IsPrimitiveSet` (VonMangoldtChain.lean:43) — "primitive" weird numbers = primitive set condition
  - `primorial` (Wheel.lean:16) — relevant to constructing weird numbers
  - Prime gap infrastructure relevant to Melfi's conditional result

### Problem 710 — Prize: ₹2000 (~$38) — Status: Open
- **URL**: https://www.erdosproblems.com/710
- **Tags**: number theory
- **OEIS**: A390246
- **Formalized in Lean (DeepMind)**: No
- **Statement**: Let f(n) be minimal such that in (n, n+f(n)) there exist distinct integers a_1,...,a_n such that k | a_k for all 1<=k<=n. Obtain an asymptotic formula for f(n).
- **Notes**: Erdos-Pomerance proved (2/sqrt(e)+o(1))*n*(log n / loglog n)^{1/2} <= f(n) <= (1.7398+o(1))*n*(log n)^{1/2}.
- **Lean relevance**: **HIGH**. The project has:
  - `ConsecutivePrimeStart` (GapFrequency.lean:20) — divisibility positioning
  - `divisorCorrectionProduct` (SingularSeries.lean:41) — divisor structure
  - `primorial` and prime-free intervals (PrimeFree.lean) — interval construction
  - The problem is about placing multiples in intervals, which connects to the wheel/sieve framework.

### Problem 711 — Prize: ₹1000 (~$19) — Status: Open
- **URL**: https://www.erdosproblems.com/711
- **Tags**: number theory
- **OEIS**: possible
- **Formalized in Lean (DeepMind)**: No
- **Statement**: Let f(n,m) be minimal such that in (m, m+f(n,m)) there exist distinct integers a_1,...,a_n such that k | a_k for all 1<=k<=n. Prove that max_m f(n,m) <= n^{1+o(1)} and that max_m (f(n,m)-f(n,n)) -> infinity.
- **Notes**: Second question answered affirmatively by van Doorn [vD26]. Erdos-Pomerance proved max_m f(n,m) << n^{3/2}.
- **Lean relevance**: **HIGH**. Same infrastructure as Problem 710, plus:
  - `PrimeFreeInterval` (PrimeFree.lean:21) — interval length bounds
  - `exists_prime_gap_ge_primorial_bound` (PrimeFree.lean:124) — gap existence

### Problem 126 — Prize: $250 — Status: Open
- **URL**: https://www.erdosproblems.com/126
- **Tags**: number theory
- **OEIS**: possible
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Let f(n) be maximal such that if A subseteq N has |A|=n then prod_{a!=b in A}(a+b) has at least f(n) distinct prime factors. Is it true that f(n)/log n -> infinity?
- **Notes**: Erdos-Turan proved log n << f(n) << n/log n. f(n)=o(n/log n) has never been proved.
- **Lean relevance**: **MEDIUM-HIGH**. The project has:
  - `primePairCount` (HardyLittlewood.lean:23) — counting prime pairs
  - `AdmissibleSet` (HardyLittlewood.lean:41) — sets with congruence conditions
  - `tupleSingularSeriesPartial` (HardyLittlewood.lean:50) — singular series for tuples
  - `singularSeriesFactor` (SingularSeries.lean:46) — prime factor structure

### Problem 708 — Prize: $100 — Status: Open
- **URL**: https://www.erdosproblems.com/708
- **Tags**: number theory
- **OEIS**: possible
- **Formalized in Lean (DeepMind)**: No
- **Statement**: Let g(n) be minimal such that for any A subseteq [2,infinity) cap N with |A|=n and any set I of max(A) consecutive integers there exists some B subseteq I with |B|=g(n) such that prod_{a in A} a | prod_{b in B} b. Is it true that g(n) <= (2+o(1))n? Or perhaps even g(n) <= 2n?
- **Notes**: Erdos-Suranyi proved g(n) >= (2-o(1))n and g(3)=4. Erdos offered '100 dollars or 1000 rupees' in [Er92c].
- **Lean relevance**: **MEDIUM-HIGH**. The project has:
  - `primorial` (Wheel.lean:16) — product of primes dividing
  - `coprimeResidues` (Wheel.lean:99) — residue coverage
  - `divisorCorrectionProduct` (SingularSeries.lean:41) — divisor products
  - `PrimeFreeInterval` (PrimeFree.lean:21) — interval constructions

---

## Tier 2: MODERATELY RELEVANT (number theory infrastructure applicable)

### Problem 3 — Prize: $5000 — Status: Open
- **URL**: https://www.erdosproblems.com/3
- **Tags**: number theory, additive combinatorics, arithmetic progressions
- **OEIS**: A003002, A003003, A003004, A003005
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: If A subseteq N has sum_{n in A} 1/n = infinity then must A contain arbitrarily long arithmetic progressions?
- **Notes**: Essentially asking for good bounds on r_k(N). Bloom-Sisask proved k=3 case. Kelley-Meka gave better r_3(N) bounds. Erdos thought this was the 'only way to approach' the Green-Tao theorem on APs of primes.
- **Lean relevance**: **MEDIUM**. Prime distribution infrastructure (primesUpTo, gap distributions) provides context but the problem is about general sets, not specifically primes.

### Problem 142 — Prize: $10000 — Status: Open
- **URL**: https://www.erdosproblems.com/142
- **Tags**: additive combinatorics, arithmetic progressions
- **OEIS**: A003002, A003003, A003004, A003005
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Let r_k(N) be the largest possible size of a subset of {1,...,N} that does not contain any non-trivial k-term arithmetic progression. Prove an asymptotic formula for r_k(N).
- **Notes**: Erdos called this 'probably unattackable at present' and 'probably enormously difficult'. Best bounds: Kelley-Meka for k=3, Green-Tao for k=4, Leng-Sah-Sawhney for k>=5.
- **Lean relevance**: **LOW-MEDIUM**. General combinatorics, not directly using prime gap infrastructure.

### Problem 1052 — Prize: $10 — Status: Open
- **URL**: https://www.erdosproblems.com/1052
- **Tags**: number theory
- **OEIS**: A002827
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: A unitary divisor of n is d|n such that (d, n/d)=1. A number n>=1 is a unitary perfect number if it is the sum of its unitary divisors (aside from n itself). Are there only finitely many unitary perfect numbers?
- **Notes**: Carlitz-Erdos-Subbarao offer $10. Five known unitary perfect numbers: 6, 60, 90, 87360, 146361946186458562560000. No odd unitary perfect numbers.
- **Lean relevance**: **MEDIUM**. The project has:
  - `divisorCorrectionProduct` (SingularSeries.lean:41) — related to coprime divisor products
  - `coprimeResidues` (Wheel.lean:99) — coprimality conditions
  - `IsPrimitiveSet` (VonMangoldtChain.lean:43) — divisibility antichains

### Problem 123 — Prize: $250 — Status: Open
- **URL**: https://www.erdosproblems.com/123
- **Tags**: number theory
- **OEIS**: N/A
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Let a,b,c>=1 be three integers which are pairwise coprime. Is every large integer the sum of distinct integers of the form a^k * b^l * c^m (k,l,m>=0), none of which divide any other?
- **Notes**: d-completeness conjecture of Erdos-Lewin. Proven for several specific triples. Stronger conjecture for a=2, b=3, c=5: all large n are sum of distinct 2^k*3^l*5^m with ratio < 1+epsilon.
- **Lean relevance**: **MEDIUM**. The project has:
  - `IsPrimitiveSet` (VonMangoldtChain.lean:43) — "none of which divide any other"
  - `coprimeResidues` (Wheel.lean:99) — coprimality
  - `primorial` (Wheel.lean:16) — products of prime powers

### Problem 50 — Prize: $250 — Status: Open
- **URL**: https://www.erdosproblems.com/50
- **Tags**: number theory
- **OEIS**: N/A
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Schoenberg proved that for every c in [0,1] the density of {n in N : phi(n) < cn} exists. Let this density be denoted by f(c). Is it true that there are no x such that f'(x) exists and is positive?
- **Notes**: Erdos could prove the distribution function is purely singular.
- **Lean relevance**: **LOW-MEDIUM**. Related to Euler totient distribution. The project has `totient_primorial_explicit` (Wheel.lean:409) and `primorialWheelMeanGap_eq_euler_product` (Wheel.lean:428) which connect to totient asymptotics.

### Problem 1135 — Prize: $500 — Status: Open (Collatz conjecture)
- **URL**: https://www.erdosproblems.com/1135
- **Tags**: number theory
- **OEIS**: A006370, A008908
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Define f:N->N by f(n)=n/2 if n is even and f(n)=(3n+1)/2 if n is odd. Given any integer m>=1 does there exist k>=1 such that f^(k)(m)=1?
- **Notes**: Not originally an Erdos problem (devised by Collatz before 1952). Erdos called it 'hopeless' and said 'Mathematics may not be ready for such problems'. The $500 prize value is from Erdos's estimate, not a formal offer.
- **Lean relevance**: **LOW**. No direct connection to prime gap infrastructure.

---

## Tier 3: LESS RELEVANT but in number theory / additive combinatorics

### Problem 1 — Prize: $500 — Status: Open
- **URL**: https://www.erdosproblems.com/1
- **Tags**: number theory, additive combinatorics
- **OEIS**: A276661
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: If A subseteq {1,...,N} with |A|=n is such that the subset sums sum_{a in S} a are distinct for all S subseteq A then N >> 2^n.
- **Notes**: Erdos called this 'perhaps my first serious problem' (dated 1931). Best upper bound N <= 0.22002*2^n (Bohman). Best lower bound N >= binom(n, floor(n/2)) (Dubroff-Fox-Xu, proving Elkies-Gleason bound).
- **Lean relevance**: **LOW**. Additive combinatorics, not prime-related.

### Problem 28 — Prize: $500 — Status: Open
- **URL**: https://www.erdosproblems.com/28
- **Tags**: number theory, additive basis
- **OEIS**: N/A
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: If A subseteq N is such that A+A contains all but finitely many integers then limsup 1_A * 1_A(n) = infinity. (Erdos-Turan conjecture)
- **Notes**: Stronger conjecture: limsup 1_A*1_A(n)/log n > 0. Even stronger: |A cap [1,N]| >> N^{1/2} suffices.
- **Lean relevance**: **LOW**. Additive number theory, not directly prime-related.

### Problem 30 — Prize: $1000 — Status: Open
- **URL**: https://www.erdosproblems.com/30
- **Tags**: number theory, sidon sets, additive combinatorics
- **OEIS**: A143824, A227590, A003022
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Let h(N) be the maximum size of a Sidon set in {1,...,N}. Is it true that, for every epsilon>0, h(N) = N^{1/2} + O_epsilon(N^epsilon)?
- **Notes**: Erdos-Turan problem. Best upper bound: h(N) <= N^{1/2} + 0.98183*N^{1/4} + O(1) (Carter-Hunter-O'Bryant). Singer showed h(N) >= (1-o(1))*N^{1/2}.
- **Lean relevance**: **LOW**. Sidon sets, not prime-related.

### Problem 39 — Prize: $500 — Status: Open
- **URL**: https://www.erdosproblems.com/39
- **Tags**: number theory, sidon sets, additive combinatorics
- **OEIS**: N/A
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Is there an infinite Sidon set A subset N such that |A cap {1,...,N}| >>_epsilon N^{1/2-epsilon} for all epsilon>0?
- **Notes**: Best construction: >> N^{sqrt(2)-1+o(1)} (Ruzsa). Erdos proved liminf |A cap {1,...,N}| / N^{1/2} = 0 for every infinite Sidon set.
- **Lean relevance**: **LOW**. Sidon sets.

### Problem 40 — Prize: $500 — Status: Open
- **URL**: https://www.erdosproblems.com/40
- **Tags**: number theory, additive basis
- **OEIS**: N/A
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: For what functions g(N)->infinity is it true that |A cap {1,...,N}| >> N^{1/2}/g(N) implies limsup 1_A*1_A(n) = infinity?
- **Notes**: Stronger form of Erdos-Turan conjecture [28].
- **Lean relevance**: **LOW**. Additive number theory.

### Problem 41 — Prize: $500 — Status: Open
- **URL**: https://www.erdosproblems.com/41
- **Tags**: number theory, sidon sets, additive combinatorics
- **OEIS**: N/A
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Let A subset N be an infinite set such that the triple sums a+b+c are all distinct for a,b,c in A (aside from trivial coincidences). Is it true that liminf |A cap {1,...,N}| / N^{1/3} = 0?
- **Notes**: General problem for h>= 2: liminf |A cap {1,...,N}| / N^{1/h} = 0. Proved for h=4 (Nash) and all even h (Chen).
- **Lean relevance**: **LOW**. Sidon/B_h sets.

### Problem 66 — Prize: $500 — Status: Open
- **URL**: https://www.erdosproblems.com/66
- **Tags**: number theory, additive basis
- **OEIS**: N/A
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Is there A subseteq N such that lim_{n->infinity} 1_A*1_A(n)/log n exists and is != 0?
- **Notes**: Erdos believed the answer should be no. Erdos-Sarkozy proved |1_A*1_A(n) - log n|/sqrt(log n) -> 0 is impossible.
- **Lean relevance**: **LOW**. Additive number theory.

### Problem 52 — Prize: $250 — Status: Open (sum-product problem)
- **URL**: https://www.erdosproblems.com/52
- **Tags**: number theory, additive combinatorics
- **OEIS**: A263996
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Let A be a finite set of integers. Is it true that for every epsilon>0, max(|A+A|, |A*A|) >>_epsilon |A|^{2-epsilon}?
- **Notes**: Erdos-Szemeredi proved lower bound |A|^{1+c}. Current record: |A|^{1962/1469-o(1)} (Cushman). Conjecture is FALSE for sets of reals (Bloom-Sawin-Schildkraut-Zhelezov).
- **Lean relevance**: **LOW**. Additive combinatorics.

### Problem 1191 — Prize: $1000 — Status: Open
- **URL**: https://www.erdosproblems.com/1191
- **Tags**: additive combinatorics, sidon sets
- **OEIS**: possible
- **Formalized in Lean (DeepMind)**: No
- **Statement**: Let A subset N be an infinite Sidon set. Is it true that liminf_{x->infinity} |A cap [1,x]| / x^{1/2} * (log x)^{1/2} = 0? Does there exist an infinite Sidon set A such that liminf |A cap [1,x]| / x^{1/2} * (log x)^c > 0 for some c>0?
- **Notes**: Second question is stronger form of [39]. Erdos offered $1000 'for clearing up the problems'.
- **Lean relevance**: **LOW**. Sidon sets.

### Problem 138 — Prize: $500 — Status: Open
- **URL**: https://www.erdosproblems.com/138
- **Tags**: additive combinatorics
- **OEIS**: A005346
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Let the van der Waerden number W(k) be such that whenever N>=W(k) and {1,...,N} is 2-coloured there must exist a monochromatic k-term arithmetic progression. Improve the bounds for W(k) - for example, prove that W(k)^{1/k} -> infinity.
- **Notes**: Berlekamp: W(p+1) >= p*2^p for prime p. Gowers: W(k) <= 2^{2^{2^{2^{2^{k+9}}}}}. Best lower bound: W(k) >> 2^k (Kozik-Shabanov).
- **Lean relevance**: **LOW**. Ramsey theory / van der Waerden numbers.

### Problem 241 — Prize: $100 — Status: Open
- **URL**: https://www.erdosproblems.com/241
- **Tags**: additive combinatorics, sidon sets
- **OEIS**: A387704
- **Formalized in Lean (DeepMind)**: Yes
- **Statement**: Let f(N) be the maximum size of A subseteq {1,...,N} such that the sums a+b+c with a,b,c in A are all distinct (aside from trivial coincidences). Is it true that f(N) ~ N^{1/3}?
- **Notes**: Bose-Chowla construction: (1+o(1))*N^{1/3} <= f(N). Best upper bound: (7/2)^{1/3}*N^{1/3} (Green). General Bose-Chowla conjecture for r-fold sums: |A| ~ N^{1/r}, known only for r=2 (see [30]).
- **Lean relevance**: **LOW**. Sidon/B_h sets.

---

## Tier 4: NOT RELEVANT to this Lean project (other domains)

### Combinatorics / Graph Theory / Geometry / Set Theory / Analysis

| # | Prize | Tags | Statement (brief) |
|---|-------|------|-------------------|
| 20 | $1000 | combinatorics | Sunflower conjecture |
| 592 | $1000 | set theory, ramsey theory | Set-theoretic Ramsey problem |
| 625 | $1000 | graph theory, chromatic number | Chromatic number problem |
| 74 | $500 | graph theory, chromatic number, cycles | Cycle chromatic number |
| 146 | $500 | graph theory, turan number | Turan number problem |
| 161 | $500 | combinatorics, ramsey theory, discrepancy | Discrepancy theory |
| 500 | $500 | graph theory, hypergraphs, turan number | Hypergraph Turan number |
| 564 | $500 | graph theory, ramsey theory, hypergraphs | Hypergraph Ramsey |
| 593 | $500 | set theory, graph theory, hypergraphs, chromatic number | Hypergraph chromatic number |
| 601 | $500 | graph theory, set theory | Graph/set theory problem |
| 604 | $500 | geometry, distances | Pinned distance problem |
| 712 | $500 | graph theory, turan number, hypergraphs | Hypergraph Turan |
| 713 | $500 | graph theory, turan number | Turan number |
| 77 | $250 | graph theory, ramsey theory | Ramsey theory |
| 165 | $250 | graph theory, ramsey theory | Ramsey theory |
| 183 | $250 | graph theory, ramsey theory | Ramsey theory |
| 595 | $250 | graph theory, set theory | Graph/set problem |
| 671 | $250 | analysis | Analysis problem |
| 78 | $100 | graph theory, ramsey theory | Ramsey theory |
| 86 | $100 | graph theory | Graph theory |
| 99 | $100 | geometry, distances | Erdos distance problem |
| 101 | $100 | geometry | Geometry problem |
| 104 | $100 | geometry | Geometry problem |
| 119 | $100 | analysis, polynomials | Polynomial problem |
| 120 | $100 | combinatorics | Erdos similarity problem |
| 132 | $100 | distances | Distance problem |
| 588 | $100 | geometry | Geometry problem |
| 1029 | $100 | graph theory, ramsey theory | Ramsey theory |
| 661 | $50 | geometry, distances | Distance problem |
| 634 | $25 | geometry | Geometry problem |

---

## Summary: Most Attackable Problems with Current Lean Infrastructure

| Rank | Problem | Prize | Key Lean Infrastructure Connection |
|------|---------|-------|-----------------------------------|
| 1 | **#143** | $500 | `IsPrimitiveSet`, `erdosWeight`, `erdosSum`, `erdos_primitive_set_bound_finite` — direct match |
| 2 | **#687** | $1000 | `coprimeResidues`, `endpointForbiddenResidueCount`, `wheelGaps`, `PrimeFreeInterval`, `primorial` — Jacobsthal/sieve |
| 3 | **#470** | $10 | `divisorCorrectionProduct`, `IsPrimitiveSet`, `primorial` — weird numbers |
| 4 | **#710** | ₹2000 | `ConsecutivePrimeStart`, `divisorCorrectionProduct`, `PrimeFreeInterval` — divisibility placement |
| 5 | **#711** | ₹1000 | Same as #710, plus `PrimeFreeInterval` bounds |
| 6 | **#708** | $100 | `primorial`, `coprimeResidues`, `divisorCorrectionProduct` — divisibility covering |
| 7 | **#126** | $250 | `primePairCount`, `AdmissibleSet`, `singularSeriesFactor` — prime factors of products |
| 8 | **#123** | $250 | `IsPrimitiveSet`, `coprimeResidues`, `primorial` — d-completeness |
| 9 | **#1052** | $10 | `divisorCorrectionProduct`, `coprimeResidues` — unitary divisors |
| 10 | **#50** | $250 | `totient_primorial_explicit`, `primorialWheelMeanGap_eq_euler_product` — totient distribution |

### Key observations:

1. **Problem #143** is the single most directly attackable problem. The Lean project already defines `IsPrimitiveSet`, `erdosWeight = 1/(n log n)`, `erdosSum`, and proves `erdos_primitive_set_bound_finite`. The conjecture is that sum_{x in A} 1/(x log x) < infinity for sets satisfying the divisibility condition. The partial result by Koukoulopoulos-Lamzouri-Lichtman (sum 1/x = o(log n)) could potentially be formalized.

2. **Problem #687** (Jacobsthal function) connects to the wheel/sieve infrastructure: `coprimeResidues`, `wheelGaps`, `endpointForbiddenResidueCount`, and `PrimeFreeInterval` all model the problem of covering intervals with residue classes mod primes. The conjecture Y(x) << x*(log x)^{2+o(1)} of Maier-Pomerance could potentially be approached with the singular series framework.

3. **Problems #710 and #711** (Erdos-Pomerance) are about placing multiples of 1,...,n in short intervals. The `ConsecutivePrimeStart` definition and `PrimeFreeInterval` constructions are directly relevant.

4. **Problem #470** (weird numbers) connects through `divisorCorrectionProduct` (coprime divisor products) and `IsPrimitiveSet` (primitive weird numbers). The conditional result on prime gaps (Melfi) connects to the prime gap infrastructure.

5. **Problem #708** (Erdos-Suranyi) is about divisibility covering in intervals, connecting to `primorial`, `coprimeResidues`, and `divisorCorrectionProduct`.
