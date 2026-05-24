"""
Модуль для работы с распределением промежутков между простыми числами.

Математическая модель:
- Точки на прямой: P_n = {0, 1} ∪ {простые ≤ n}
- Промежутки: g_i = точка_{i+1} - точка_i
- Функция частот: F(g) = |{i : g_i = g}|
- k-е простое число: p_k = Σ_{i=0}^{k} g_i = 1 + Σ_{g} g · F_k(g)

где F_k(g) — количество промежутков размера g среди первых k+1 промежутков.
"""

from __future__ import annotations

import math
import time
from collections.abc import Iterator

_WHEEL_MODULUS = 210
_SMALL_WHEEL_PRIMES = (2, 3, 5, 7)
_WHEEL210_CANDIDATES = tuple(r for r in range(1, _WHEEL_MODULUS) if math.gcd(r, _WHEEL_MODULUS) == 1)
_WHEEL210_INDEX = [-1] * _WHEEL_MODULUS
for _wheel_index, _wheel_residue in enumerate(_WHEEL210_CANDIDATES):
    _WHEEL210_INDEX[_wheel_residue] = _wheel_index
_WHEEL210_DELTAS = tuple(
    _WHEEL210_CANDIDATES[i + 1] - _WHEEL210_CANDIDATES[i]
    for i in range(len(_WHEEL210_CANDIDATES) - 1)
) + (_WHEEL_MODULUS + _WHEEL210_CANDIDATES[0] - _WHEEL210_CANDIDATES[-1],)
_WHEEL210_NEXT = []
for _residue in range(_WHEEL_MODULUS):
    for _index, _candidate in enumerate(_WHEEL210_CANDIDATES):
        if _candidate >= _residue:
            _WHEEL210_NEXT.append((_candidate - _residue, _index))
            break
    else:
        _WHEEL210_NEXT.append((_WHEEL_MODULUS + _WHEEL210_CANDIDATES[0] - _residue, 0))


def _wheel210_candidates() -> list[int]:
    """Все числа 0 < r < 210, взаимно простые с 210."""
    return list(_WHEEL210_CANDIDATES)


def _wheel210_deltas() -> list[int]:
    """Разности между последовательными кандидатами wheel 210, включая wrap-around."""
    return list(_WHEEL210_DELTAS)


def _sieve(limit: int) -> list[int]:
    """Решето Эратосфена. Возвращает все простые числа до limit включительно."""
    if limit < 2:
        return []
    if limit == 2:
        return [2]

    # Храним только нечётные числа: индекс i соответствует 2*i + 3.
    size = (limit - 1) // 2
    sieve = bytearray(b"\x01") * size
    cross_limit = (math.isqrt(limit) - 3) // 2 + 1
    for i in range(cross_limit):
        if sieve[i]:
            p = 2 * i + 3
            start = (p * p - 3) // 2
            sieve[start::p] = b"\x00" * (((size - 1 - start) // p) + 1)
    return [2] + [2 * i + 3 for i, is_prime in enumerate(sieve) if is_prime]


def _naive_sieve_gaps(x: int) -> dict[int, int]:
    """Эталонный подсчёт gaps обычным решетом для проверки и сравнения скорости."""
    primes = _sieve(x)
    gaps: dict[int, int] = {}
    previous: int | None = None
    for prime in primes:
        if previous is not None:
            gap = prime - previous
            gaps[gap] = gaps.get(gap, 0) + 1
        previous = prime
    return gaps


class GapSieve:
    """Segmented wheel sieve modulo 210 для простых чисел, gaps и k-го простого."""

    def __init__(self, segment_bytes: int = 1 << 16) -> None:
        if segment_bytes <= 0:
            raise ValueError("segment_bytes must be positive")
        # Один байт на кандидата быстрее битового доступа в чистом Python.
        self.segment_bytes = segment_bytes
        self.candidates = _WHEEL210_CANDIDATES
        self.candidate_count = len(_WHEEL210_CANDIDATES)
        self.residue_to_index = _WHEEL210_INDEX
        self.blocks_per_segment = max(1, (segment_bytes + self.candidate_count - 1) // self.candidate_count)
        self.segment_span = self.blocks_per_segment * _WHEEL_MODULUS

    def iter_primes(self, x: int) -> Iterator[int]:
        """Генерирует все простые числа ≤ x через segmented wheel sieve modulo 210."""
        if x < 2:
            return
        for prime in _SMALL_WHEEL_PRIMES:
            if prime <= x:
                yield prime
        if x < 11:
            return

        base_primes = [p for p in _sieve(math.isqrt(x)) if p > 7]
        candidates = self.candidates
        candidate_count = self.candidate_count
        residue_to_index = self.residue_to_index
        wheel_deltas = _WHEEL210_DELTAS
        wheel_next = _WHEEL210_NEXT
        segment_span = self.segment_span
        modulus = _WHEEL_MODULUS

        for segment_low in range(0, x + 1, segment_span):
            segment_high = min(x, segment_low + segment_span - 1)
            block_count = (segment_high - segment_low) // modulus + 1
            mask = bytearray(b"\x01") * (block_count * candidate_count)
            view = memoryview(mask)

            for p in base_primes:
                p2 = p * p
                if p2 > segment_high:
                    break
                q_low = max(p, (segment_low + p - 1) // p)
                q_high = segment_high // p
                shift, delta_index = wheel_next[q_low % modulus]
                q = q_low + shift
                while q <= q_high:
                    multiple = p * q
                    residue_index = residue_to_index[multiple % modulus]
                    view[((multiple - segment_low) // modulus) * candidate_count + residue_index] = 0
                    q += wheel_deltas[delta_index]
                    delta_index += 1
                    if delta_index == candidate_count:
                        delta_index = 0

            for offset, is_prime in enumerate(view):
                if is_prime:
                    number = segment_low + (offset // candidate_count) * modulus + candidates[offset % candidate_count]
                    if 11 <= number <= segment_high:
                        yield number

    def gap_distribution(self, x: int) -> dict[int, int]:
        """Подсчитывает распределение промежутков между соседними простыми числами ≤ x."""
        gaps: dict[int, int] = {}
        previous: int | None = None
        for prime in self.iter_primes(x):
            if previous is not None:
                gap = prime - previous
                gaps[gap] = gaps.get(gap, 0) + 1
            previous = prime
        return gaps

    def nth_prime(self, k: int) -> int:
        """Находит k-е простое число в 0-индексации: 0 → 2, 1 → 3, 2 → 5."""
        if k < 0:
            raise ValueError("k must be non-negative")
        if k < len(_SMALL_WHEEL_PRIMES):
            return _SMALL_WHEEL_PRIMES[k]

        limit = self._nth_prime_upper_bound(k)
        while True:
            for index, prime in enumerate(self.iter_primes(limit)):
                if index == k:
                    return prime
            limit *= 2

    @staticmethod
    def _nth_prime_upper_bound(k: int) -> int:
        """Верхняя оценка для p_k при 0-индексации с запасом для малых k."""
        n = k + 1
        if n < 6:
            return 15
        log_n = math.log(n)
        return int(n * (log_n + math.log(log_n)) + 16)

    def benchmark(self, x: int) -> tuple[dict[int, int], float]:
        """Подсчитывает gaps и возвращает распределение вместе со временем."""
        start = time.perf_counter()
        gaps = self.gap_distribution(x)
        return gaps, time.perf_counter() - start

    def benchmark_against_naive(self, x: int) -> dict[str, tuple[dict[int, int], float]]:
        """Сравнивает segmented wheel sieve с обычным решетом на одном x."""
        wheel_gaps, wheel_time = self.benchmark(x)
        naive_start = time.perf_counter()
        naive_gaps = _naive_sieve_gaps(x)
        naive_time = time.perf_counter() - naive_start
        return {
            "segmented_wheel_210": (wheel_gaps, wheel_time),
            "naive_sieve": (naive_gaps, naive_time),
        }


def segmented_wheel_sieve_gaps(x: int) -> dict[int, int]:
    """
    Подсчёт всех промежутков между простыми числами ≤ x.
    Возвращает словарь {gap: count}. Использует segmented sieve с wheel 210.
    """
    return GapSieve().gap_distribution(x)


def benchmark_gap_distribution(x: int) -> tuple[dict[int, int], float]:
    """Подсчёт gaps через segmented wheel sieve modulo 210 и время выполнения."""
    return GapSieve().benchmark(x)


def benchmark_naive_gap_distribution(x: int) -> tuple[dict[int, int], float]:
    """Подсчёт gaps обычным решетом и время выполнения для сравнения скорости."""
    start = time.perf_counter()
    gaps = _naive_sieve_gaps(x)
    return gaps, time.perf_counter() - start


def prime_gap_distribution(n: int) -> list[list[int]]:
    """
    Распределение промежутков между точками {0, 1} ∪ {простые ≤ n}.
    По оси x — значение промежутка, по оси y — число промежутков этого значения.
    """
    if n < 2:
        return [[0, 0]]
    primes = _sieve(n)
    points = [0, 1] + primes
    gaps = [points[i + 1] - points[i] for i in range(len(points) - 1)]
    freq: dict[int, int] = {}
    for gap in gaps:
        freq[gap] = freq.get(gap, 0) + 1
    return [[0, 0]] + [[gap, freq[gap]] for gap in sorted(freq.keys())]


def prime_gap_distribution_by_count(k: int) -> list[list[int]]:
    """
    Распределение промежутков для первых k простых чисел.
    """
    if k <= 0:
        return [[0, 0]]
    if k < 6:
        limit = 15
    else:
        limit = int(k * (math.log(k) + math.log(math.log(k) + 1)) * 1.5) + 10
    primes = _sieve(limit)
    while len(primes) < k:
        limit *= 2
        primes = _sieve(limit)
    points = [0, 1] + primes[:k]
    gaps = [points[i + 1] - points[i] for i in range(len(points) - 1)]
    freq: dict[int, int] = {}
    for gap in gaps:
        freq[gap] = freq.get(gap, 0) + 1
    return [[0, 0]] + [[gap, freq[gap]] for gap in sorted(freq.keys())]


def _factorization(n: int) -> dict[int, int]:
    """Разложение натурального числа на простые множители."""
    factors: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def mangoldt(n: int) -> float:
    """Функция Мангольдта Λ(n): ln p, если n = p^k, иначе 0."""
    if n < 2:
        return 0.0
    factors = _factorization(n)
    if len(factors) == 1:
        return math.log(next(iter(factors)))
    return 0.0


def moebius(n: int) -> int:
    """Функция Мёбиуса μ(n)."""
    if n == 1:
        return 1
    if n < 1:
        return 0
    factors = _factorization(n)
    if any(power > 1 for power in factors.values()):
        return 0
    return -1 if len(factors) % 2 else 1


def prime_indicator_exact(n: int) -> float:
    """Точный индикатор простоты a(n) = μ(n)^2 · Λ(n) / ln n."""
    if n < 2:
        return 0.0
    mu = moebius(n)
    return (mu * mu) * mangoldt(n) / math.log(n)


def gap_frequency_exact(g: int, x: int) -> int:
    """Точная частота F(g, x) через сумму с индикатором простоты."""
    if g <= 0 or x < g + 2:
        return 0
    total = 0.0
    for n in range(2, x - g + 1):
        term = prime_indicator_exact(n) * prime_indicator_exact(n + g)
        for h in range(1, g):
            term *= 1.0 - prime_indicator_exact(n + h)
        total += term
    return round(total)


def _prime_indicator_sieve(n: int) -> int:
    """Индикатор простоты через включения-исключения по P(√n)."""
    if n < 2:
        return 0
    primes = [p for p in _sieve(math.isqrt(n)) if n % p == 0]
    total = 0
    for mask in range(1 << len(primes)):
        d = 1
        bits = 0
        for i, p in enumerate(primes):
            if mask & (1 << i):
                d *= p
                bits += 1
        if n % d == 0:
            total += -1 if bits % 2 else 1
    return total


def gap_frequency_sieve(g: int, x: int) -> int:
    """Точная частота F(g, x) через решето inclusion-exclusion."""
    if g <= 0 or x < g + 2:
        return 0
    total = 0
    for n in range(2, x - g + 1):
        term = _prime_indicator_sieve(n) * _prime_indicator_sieve(n + g)
        for h in range(1, g):
            term *= 1 - _prime_indicator_sieve(n + h)
        total += term
    return total


def prime_gap_frequency_reference(g: int, x: int) -> int:
    """Эталонная частота промежутка g из prime_gap_distribution."""
    for gap, count in prime_gap_distribution(x):
        if gap == g:
            return count
    return 0


_TWIN_PRIME_CONSTANT = 0.6601618158468696
_HYBRID_EXACT_LIMIT = 1_000_000


def _is_prime_trial(n: int) -> bool:
    """Проверка простоты trial division; используется только в черновых малых алгоритмах."""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def _prime_pair_count_exact_sieve(g: int, x: int) -> int:
    """
    Exact: считает π₂(g, x) решетом Эратосфена.

    Сложность: O((x+g) log log(x+g)) времени и O(x+g) памяти.
    """
    if g <= 0 or x < 2:
        return 0
    prime_set = set(_sieve(x + g))
    return sum(1 for p in prime_set if p <= x and p + g in prime_set)


def _forbidden_pair_residues(g: int, p: int) -> set[int]:
    """Остатки n mod p, запрещённые условиями p | n или p | n+g."""
    return {0, (-g) % p}


def _wheel_pair_survivors(g: int, x: int, y: int) -> tuple[list[int], int, int]:
    """
    Считает кандидаты, у которых n и n+g не делятся на простые ≤ y.

    Это φ₂(g, x, a) в wheel-форме для a = π(y), а не полноценная
    Meissel-Lehmer-декомпозиция. Возвращает allowed residues, modulus, φ₂.

    Сложность построения: O(M · π(y)), где M = ∏_{p≤y} p; поэтому y должен
    быть малым. Это главная причина, почему прямое обобщение не даёт
    практического sub-linear exact алгоритма.
    """
    base_primes = _sieve(y)
    modulus = 1
    for p in base_primes:
        modulus *= p
    if modulus == 1:
        return [0], 1, max(0, x - 1)

    allowed: list[int] = []
    for residue in range(modulus):
        if all(residue % p not in _forbidden_pair_residues(g, p) for p in base_primes):
            allowed.append(residue)

    full_cycles, tail = divmod(x, modulus)
    phi2 = full_cycles * len(allowed)
    phi2 += sum(1 for residue in allowed if 1 <= residue <= tail)
    if 1 in allowed:
        phi2 -= 1
    return allowed, modulus, phi2


def meissel_lehmer_pair_count(g: int, x: int, y: int | None = None) -> int:
    """
    Exact/draft: combinatorial pair counting для π₂(g, x) = #{p ≤ x: p и p+g простые}.

    Идея черновика:
    1. Построить φ₂(g, x, a): кандидаты n, где n и n+g не имеют простых
       делителей среди p₁..pₐ, через wheel по простым ≤ y.
    2. Вместо неизвестного компактного аналога P₂/P₃/... из Lehmer для пар
       проверить оставшихся кандидатов на простоту напрямую.

    Это точный алгоритм, но не доказанный sub-linear алгоритм. Его стоимость:
    O(M · π(y) + S(g, x, y) · √(x+g)), где M = ∏_{p≤y} p, а S — число
    survivors после малого решета. При y ≈ x^(1/3) wheel-модуль M слишком
    велик; при малом y остаётся слишком много survivors.
    """
    if g <= 0 or x < 2:
        return 0
    if g % 2 == 1:
        return 1 if 2 <= x and _is_prime_trial(2 + g) else 0
    if y is None:
        y = max(2, min(math.isqrt(x + g), int(round((x + g) ** (1 / 3)))))
    if y < 2:
        y = 1

    allowed, modulus, _phi2 = _wheel_pair_survivors(g, x, y)
    total = sum(1 for p in _sieve(min(x, y)) if _is_prime_trial(p + g))
    for start in range(0, x + 1, modulus):
        for residue in allowed:
            n = start + residue
            if y < n <= x and _is_prime_trial(n) and _is_prime_trial(n + g):
                total += 1
    return total


def _li2_pair_integral(x: int | float) -> float:
    """Аппроксимация ∫₂ˣ dt / log²(t) для Hardy-Littlewood."""
    if x <= 2:
        return 0.0
    if x >= 1_000_000:
        log_x = math.log(x)
        return x / (log_x * log_x) * (1.0 + 2.0 / log_x + 6.0 / (log_x * log_x))

    intervals = 2048
    if intervals % 2:
        intervals += 1
    a = 2.0
    b = float(x)
    h = (b - a) / intervals

    def f(t: float) -> float:
        return 1.0 / (math.log(t) ** 2)

    total = f(a) + f(b)
    for i in range(1, intervals):
        total += (4 if i % 2 else 2) * f(a + i * h)
    return total * h / 3.0


def hardy_littlewood_pair_estimate(g: int, x: int) -> float:
    """
    Approximate: Hardy-Littlewood estimate для prime pairs.

    Для нечётного g сингулярный ряд равен 0: кроме возможной пары (2, 2+g)
    асимптотически пар нет. Для чётного g используется
    2 C₂ ∏_{p|g, p>2} (p-1)/(p-2) · ∫₂ˣ dt/log²(t).

    Сложность: O(√g + 1) времени и O(1) памяти; результат не является exact.
    Известные эвристики дают ошибку порядка меньше главного члена в среднем,
    но эффективной доказанной границы, достаточной для exact count, нет.
    """
    if g <= 0 or x < 2:
        return 0.0
    if g % 2 == 1:
        return 1.0 if 2 <= x and _is_prime_trial(2 + g) else 0.0

    singular = 2.0 * _TWIN_PRIME_CONSTANT
    for p in _factorization(g):
        if p > 2:
            singular *= (p - 1) / (p - 2)
    return singular * _li2_pair_integral(x)


def hybrid_pair_count(g: int, x: int) -> int:
    """
    Hybrid: exact для малых x, approximate для больших x.

    При x ≤ 1e6 используется exact sieve. При больших x возвращается округлённая
    Hardy-Littlewood estimate, то есть это уже не доказанный точный count.
    Сложность exact-ветки: O((x+g) log log(x+g)); approximate-ветки: O(√g).
    """
    if x <= _HYBRID_EXACT_LIMIT:
        return _prime_pair_count_exact_sieve(g, x)
    return round(hardy_littlewood_pair_estimate(g, x))


def nth_prime_by_gaps(k: int) -> int:
    """
    Находит k-е простое число (0-индексация: 0 → 2, 1 → 3, 2 → 5, ...)
    через кумулятивную сумму промежутков.

    Формула: p_k = Σ_{i=0}^{k} g_i
    где g_0 = 1 (0→1), g_1 = 1 (1→2), g_2 = 1 (2→3),
    g_3 = 2 (3→5), g_4 = 2 (5→7), ...

    Эквивалентно: p_k = 1 + Σ_{g} g · F_k(g)
    где F_k(g) — количество промежутков размера g среди первых k+1 промежутков.
    """
    if k < 0:
        raise ValueError("k must be non-negative")
    if k < 6:
        limit = 15
    else:
        limit = int(k * (math.log(k) + math.log(math.log(k) + 1)) * 1.5) + 10
    primes = _sieve(limit)
    while len(primes) < k + 1:
        limit *= 2
        primes = _sieve(limit)
    points = [0, 1] + primes[:k + 1]
    gaps = [points[i + 1] - points[i] for i in range(len(points) - 1)]
    return sum(gaps)


def nth_prime_optimized(k: int) -> int:
    """
    Находит k-е простое число через решето с оценкой верхней границы.
    """
    if k < 0:
        raise ValueError("k must be non-negative")
    if k < 6:
        limit = 15
    else:
        limit = int(k * (math.log(k) + math.log(math.log(k) + 1)) * 1.5) + 10
    primes = _sieve(limit)
    while len(primes) < k + 1:
        limit *= 2
        primes = _sieve(limit)
    return primes[k]


def generate_gaps_optimized(k: int) -> list[int]:
    """Генерирует первые k+1 промежутков через решето."""
    if k < 0:
        raise ValueError("k must be non-negative")
    if k < 6:
        limit = 15
    else:
        limit = int(k * (math.log(k) + math.log(math.log(k) + 1)) * 1.5) + 10
    primes = _sieve(limit)
    while len(primes) < k + 1:
        limit *= 2
        primes = _sieve(limit)
    points = [0, 1] + primes[:k + 1]
    return [points[i + 1] - points[i] for i in range(len(points) - 1)]


def gap_distribution_from_gaps(gaps: list[int]) -> list[list[int]]:
    """Строит функцию частот по списку промежутков."""
    freq: dict[int, int] = {}
    for gap in gaps:
        freq[gap] = freq.get(gap, 0) + 1
    return [[0, 0]] + [[g, freq[g]] for g in sorted(freq.keys())]


if __name__ == "__main__":
    print("=== Точная формула F(g, x) ===")
    for x in [100, 1000, 10000]:
        for g in [2, 4, 6]:
            exact = gap_frequency_exact(g, x)
            ref = prime_gap_frequency_reference(g, x)
            print(f"g={g} x={x}: exact={exact} ref={ref} match={exact==ref}")
    print("\n=== k-е простое ===")
    for k in [0, 1, 2, 5, 10, 25, 100, 1000]:
        p1 = nth_prime_by_gaps(k)
        p2 = nth_prime_optimized(k)
        print(f"k={k}: by_gaps={p1} optimized={p2} match={p1==p2}")

