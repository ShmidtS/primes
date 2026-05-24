#!/usr/bin/env python3
"""Numerical verification tools for prime gap distribution theory.

The script is intentionally self-contained: it uses only the Python standard
library, numpy, matplotlib, and optionally mpmath when available for zeta zeros.
For full-scale runs at 10^8 or 10^9, prefer increasing --segment-size to match
available memory and CPU cache behavior.
"""

from __future__ import annotations

import argparse
import csv
import math
import os
from array import array
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

try:
    import mpmath as mp
except ImportError:  # mpmath is optional.
    mp = None

TWIN_PRIME_CONSTANT = 0.66016181584686957392781211001455577843262336028473
DEFAULT_LIMIT = 100_000_000
DEFAULT_X_VALUES = (10_000, 100_000, 1_000_000, 10_000_000, 100_000_000)
DEFAULT_SELECTED_GAPS = (2, 4, 6)
FIRST_100_ZETA_ZERO_GAMMAS = (
    14.134725141734693790457251983562470270784257115699,
    21.022039638771554992628479593896902777334340524903,
    25.010857580145688763213790992562821818659549672558,
    30.424876125859513210311897530584091320181560023715,
    32.935061587739189690662368964074903488812715603517,
    37.586178158825671257217763480705332821405597350831,
    40.918719012147495187398126914633254395726165962777,
    43.327073280914999519496122165406805782645668371837,
    48.005150881167159727942472749427516041686844001144,
    49.773832477672302181916784678563724057723178299676,
    52.970321477714460644147296608880990063825017888821,
    56.446247697063394804367759476706118876123671922767,
    59.347044002602353079653648674992219031098772806467,
    60.831778524609809844259901824524003802910090451219,
    65.112544048081606660875054253183705029348149295167,
    67.079810529494173714478828896522216770107144951746,
    69.546401711173979252926857526554738443012474209602,
    72.067157674481907582522107969826168390480906621457,
    75.704690699083933168326916762030345922811903530697,
    77.144840068874805372682664856304637015796032449234,
    79.337375020249367922763592877116228190613246743120,
    82.910380854086030183164837494770609497508880593782,
    84.735492980517050105735311206827741417106627934240,
    87.425274613125229406531667850919213252171886401269,
    88.809111207634465423682348079509378395444893409818,
    92.491899270558484296259725241810684878721794027730,
    94.651344040519886966597925815208053829945520331427,
    95.870634228245309758741029219246781695256461224987,
    98.831194218193692233324420138622327820658039063429,
    101.317851005731391228785447940292308906332866384300,
    103.725538040478339416398408108695280834481173069495,
    105.446623052326094493670832414111808997282753928282,
    107.168611184276407515123351963086191213476707881404,
    111.029535543169674524656450309944350415345968390073,
    111.874659176992637085612078716770594960311749873385,
    114.320220915452712765890937276191079809917657723829,
    116.226680320857554382160804312064755127329851232383,
    118.790782865976217322979139702699824347306210592809,
    121.370125002420645918945532970499922723001310631540,
    122.946829293552588200817460330770016496214389052211,
    124.256818554345767184732007966129924441573510864061,
    127.516683879596495124279323766906076268088309881018,
    129.578704199956050985768033906179973608640176067996,
    131.087688530932656723566372461501349059203547502975,
    133.497737202997586450130492042640607664974174943904,
    134.756509753373871331326064157169736178396230772350,
    138.116042054533443200191555190282447859835274624068,
    139.736208952121388950450046523382460846790052565889,
    141.123707404021123761940353818475355090300660879541,
    143.111845807620632739405123868913929966233102430354,
    146.000982486765518547402507596424682696891703932141,
    147.422765342559602049521185010431506168772775476375,
    150.053520420784880351432467236959370623037321262504,
    150.925257612241466761852524678305364809491217453483,
    153.024693811198896198256544255185446508885437305104,
    156.112909294237867569750189310169194746535308500942,
    157.597591817594059887530503158498765730723899519184,
    158.849988171420498724174994775540271414335642533400,
    161.188964137596027519437344129369554364915882975062,
    163.030709687181987243311039000687994896964954441323,
    165.537069187900418830038919354874797328367251935957,
    167.184439978174513440957756246210904578198629355167,
    169.094515415568821489505871181431834796667786788317,
    169.911976479411698966699843595821792288394437125364,
    173.411536519591552959846118649345595254156066757533,
    174.754191523365725813378762455866917514592905676819,
    176.441434297710418888892641057860933528118465532584,
    178.377407776099977285830935414184426183132361629734,
    179.916484020256996139340036612051237453687419641098,
    182.207078484366461915407037226987798690797457778239,
    184.874467848387508800960646617234258413085195579058,
    185.598783677707471466527704268392646612751425841888,
    187.228922583501851991641540586131243016150510111088,
    189.416158656016937084852289099845324491357839359964,
    192.026656360713786547283631425583430105527903471509,
    193.079726603845704047402205794376054252803720598555,
    195.265396679529235321463187814862272621315736848394,
    196.876481840958316948622263914696207735746230921412,
    198.015309676251912424919918702208867155062695980284,
    201.264751943703788733016133427548173222402863729902,
    202.493594514140534277686660637864315821020746937534,
    204.189671803104554330716438386313685097224040632086,
    205.394697202163286025212379390693090923180281497638,
    207.906258887806209861501967907753644147292760584386,
    209.576509716856259852835644289886752175983275593211,
    211.690862595365307563907486730719294253055783386697,
    213.347919359712666190639122021072608983751922637733,
    214.547044783491423222944201072590680268964919756203,
    216.169538508263700265869563354498028575339525077239,
    219.067596349021378985677256590437241245149182812669,
    220.714918839314003369115592633906339656761926800051,
    221.430705554693338732097475883784539747052759931859,
    224.007000254604335211728875528504895356085759918347,
    224.983324669582287503782523680528656491640967954014,
    227.421444279679291310461436160659234110244660725807,
    229.337413305525348107760083306756718738906773737896,
    231.250188700499164773806186770010527182203575103913,
    231.987235253180248603771668539197862205910698712385,
    233.693404178908300640704494732592202185568461824411,
    236.524229665816205802475507955662978689529495212189,
)


@dataclass(frozen=True)
class GapData:
    gaps: np.ndarray
    right_endpoints: np.ndarray
    frequencies: Counter[int]


def simple_sieve(limit: int) -> list[int]:
    """Return all primes <= limit using an odd-only in-memory sieve."""
    if limit < 2:
        return []
    if limit == 2:
        return [2]

    size = (limit - 1) // 2
    sieve = bytearray(b"\x01") * size
    cross_limit = (math.isqrt(limit) - 3) // 2 + 1
    for i in range(cross_limit):
        if sieve[i]:
            p = 2 * i + 3
            start = (p * p - 3) // 2
            sieve[start::p] = b"\x00" * (((size - 1 - start) // p) + 1)
    return [2] + [2 * i + 3 for i, is_prime in enumerate(sieve) if is_prime]


def segmented_sieve(limit: int, segment_size: int = 1 << 22) -> Iterable[int]:
    """Yield all primes <= limit with a numpy-backed segmented sieve."""
    if limit < 2:
        return
    yield 2
    if limit < 3:
        return

    root = math.isqrt(limit)
    base_primes = [p for p in simple_sieve(root) if p != 2]
    segment_size = max(segment_size | 1, 32_768)

    for low in range(3, limit + 1, segment_size):
        if low % 2 == 0:
            low += 1
        high = min(limit, low + segment_size - 1)
        if high % 2 == 0:
            high -= 1
        if high < low:
            continue

        segment_len = ((high - low) // 2) + 1
        is_prime = np.ones(segment_len, dtype=np.bool_)

        for p in base_primes:
            p2 = p * p
            if p2 > high:
                break
            start = max(p2, ((low + p - 1) // p) * p)
            if start % 2 == 0:
                start += p
            is_prime[(start - low) // 2 :: p] = False

        primes = low + 2 * np.nonzero(is_prime)[0]
        yield from primes.astype(np.int64).tolist()


def generate_primes(limit: int, segment_size: int = 1 << 22) -> list[int]:
    """Generate all primes <= limit as a Python list."""
    return list(segmented_sieve(limit, segment_size))


def collect_gap_data(limit: int, segment_size: int = 1 << 22) -> GapData:
    """Stream primes once and collect gaps, right endpoints, and frequencies."""
    gaps = array("I")
    right_endpoints = array("I")
    frequencies: Counter[int] = Counter()
    previous: int | None = None

    for prime in segmented_sieve(limit, segment_size):
        if previous is not None:
            gap = prime - previous
            gaps.append(gap)
            right_endpoints.append(prime)
            if gap % 2 == 0:
                frequencies[gap] += 1
        previous = prime

    return GapData(
        gaps=np.frombuffer(gaps, dtype=np.uint32).copy(),
        right_endpoints=np.frombuffer(right_endpoints, dtype=np.uint32).copy(),
        frequencies=frequencies,
    )


def distinct_prime_factors(n: int, primes: Sequence[int] | None = None) -> list[int]:
    """Return distinct prime factors of n."""
    factors: list[int] = []
    if n < 2:
        return factors
    if primes is None:
        primes = simple_sieve(math.isqrt(n))
    remainder = n
    for p in primes:
        if p * p > remainder:
            break
        if remainder % p == 0:
            factors.append(p)
            while remainder % p == 0:
                remainder //= p
    if remainder > 1:
        factors.append(remainder)
    return factors


def singular_series(gap: int, factor_primes: Sequence[int] | None = None) -> float:
    """Compute S(g) = 2*C2*prod_{p|k,p>2}(p-1)/(p-2), g=2k."""
    if gap <= 0 or gap % 2:
        return 0.0
    k = gap // 2
    product = 1.0
    for p in distinct_prime_factors(k, factor_primes):
        if p > 2:
            product *= (p - 1) / (p - 2)
    return 2.0 * TWIN_PRIME_CONSTANT * product


def li2(x: float, intervals: int = 20_000) -> float:
    """Numerically approximate integral_2^x dt/log(t)^2 by Simpson integration."""
    if x <= 2.0:
        return 0.0
    a = math.log(2.0)
    b = math.log(float(x))
    if b <= a:
        return 0.0
    n = max(2, intervals)
    if n % 2:
        n += 1
    u = np.linspace(a, b, n + 1, dtype=np.float64)
    values = np.exp(u) / (u * u)
    h = (b - a) / n
    return float((h / 3.0) * (values[0] + values[-1] + 4.0 * values[1:-1:2].sum() + 2.0 * values[2:-2:2].sum()))


def exact_gap_count(gaps: np.ndarray, right_endpoints: np.ndarray, gap: int, x: int) -> int:
    """Count gaps of a given size with right endpoint <= x."""
    stop = int(np.searchsorted(right_endpoints, x, side="right"))
    if stop <= 0:
        return 0
    return int(np.count_nonzero(gaps[:stop] == gap))


def build_hl_comparison(
    gap_data: GapData,
    x_values: Sequence[int],
    gap_sizes: Sequence[int],
    integration_intervals: int,
) -> list[dict[str, float | int]]:
    """Build exact-vs-Hardy-Littlewood rows for selected x and gap sizes."""
    max_gap = max(gap_sizes, default=2)
    factor_primes = simple_sieve(math.isqrt(max(2, max_gap // 2)) + 1)
    li2_cache = {x: li2(float(x), integration_intervals) for x in x_values}
    rows: list[dict[str, float | int]] = []

    for x in x_values:
        for gap in gap_sizes:
            exact = exact_gap_count(gap_data.gaps, gap_data.right_endpoints, gap, x)
            prediction = singular_series(gap, factor_primes) * li2_cache[x]
            error = exact - prediction
            relative_error = error / prediction if prediction else math.nan
            rows.append(
                {
                    "x": int(x),
                    "gap_size": int(gap),
                    "exact_count": int(exact),
                    "hl_prediction": float(prediction),
                    "error_term": float(error),
                    "relative_error": float(relative_error),
                }
            )
    return rows


def zeta_zero_gammas(count: int) -> list[float]:
    """Return zeta-zero ordinates, using mpmath when requested count exceeds the built-in table."""
    if count <= len(FIRST_100_ZETA_ZERO_GAMMAS) or mp is None:
        return [float(gamma) for gamma in FIRST_100_ZETA_ZERO_GAMMAS[:count]]
    zeros = [float(gamma) for gamma in FIRST_100_ZETA_ZERO_GAMMAS]
    for n in range(len(zeros) + 1, count + 1):
        zeros.append(float(mp.im(mp.zetazero(n))))
    return zeros


def oscillatory_approximation(x: float, gap: int, gammas: Sequence[float]) -> float:
    """Approximate 2*Re sum_gamma [((x+g)^rho - x^rho)/rho], rho=1/2+i*gamma."""
    if x <= 0.0 or not gammas:
        return 0.0
    total = 0.0 + 0.0j
    log_x = math.log(x)
    log_xg = math.log(x + gap)
    sqrt_x = math.sqrt(x)
    sqrt_xg = math.sqrt(x + gap)
    for gamma in gammas:
        rho = complex(0.5, gamma)
        numerator = sqrt_xg * complex(math.cos(gamma * log_xg), math.sin(gamma * log_xg))
        numerator -= sqrt_x * complex(math.cos(gamma * log_x), math.sin(gamma * log_x))
        total += numerator / rho
    return float(2.0 * total.real)


def build_zeta_rows(
    hl_rows: Sequence[dict[str, float | int]],
    zero_count: int,
) -> list[dict[str, float | int]]:
    """Attach approximate zeta-zero oscillation values to HL error rows."""
    gammas = zeta_zero_gammas(zero_count)
    rows: list[dict[str, float | int]] = []
    for row in hl_rows:
        x = int(row["x"])
        gap = int(row["gap_size"])
        rows.append(
            {
                "x": x,
                "gap_size": gap,
                "error_term": float(row["error_term"]),
                "oscillatory_approx": oscillatory_approximation(float(x), gap, gammas),
            }
        )
    return rows


def build_error_series(
    gap_data: GapData,
    gap: int,
    x_grid: np.ndarray,
    integration_intervals: int,
) -> np.ndarray:
    """Compute Delta(g,x) on a uniform x-grid for FFT and plotting."""
    series = np.empty(len(x_grid), dtype=np.float64)
    s_g = singular_series(gap)
    for index, x in enumerate(x_grid):
        exact = exact_gap_count(gap_data.gaps, gap_data.right_endpoints, gap, int(x))
        series[index] = exact - s_g * li2(float(x), integration_intervals)
    return series


def spectral_density(error_series: np.ndarray, spacing: float) -> tuple[np.ndarray, np.ndarray]:
    """Return one-sided FFT frequency and power arrays for an error series."""
    centered = error_series - np.mean(error_series)
    fft_values = np.fft.rfft(centered)
    frequencies = np.fft.rfftfreq(len(centered), d=spacing)
    power = np.abs(fft_values) ** 2
    return frequencies, power


def write_gap_frequencies(path: Path, frequencies: Counter[int]) -> None:
    with path.open("w", newline="", encoding="utf-8") as file:
        writer = csv.writer(file)
        writer.writerow(["gap_size", "frequency"])
        for gap, count in sorted(frequencies.items()):
            writer.writerow([gap, count])


def write_dict_rows(path: Path, rows: Sequence[dict[str, float | int]], fieldnames: Sequence[str]) -> None:
    with path.open("w", newline="", encoding="utf-8") as file:
        writer = csv.DictWriter(file, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def write_spectral_density(path: Path, frequencies: np.ndarray, power: np.ndarray) -> None:
    with path.open("w", newline="", encoding="utf-8") as file:
        writer = csv.writer(file)
        writer.writerow(["frequency", "power"])
        for frequency, value in zip(frequencies, power):
            writer.writerow([float(frequency), float(value)])


def plot_gap_distribution(path: Path, frequencies: Counter[int], limit: int) -> None:
    gaps = np.array(sorted(frequencies), dtype=np.float64)
    if len(gaps) == 0:
        return
    counts = np.array([frequencies[int(gap)] for gap in gaps], dtype=np.float64)
    factor_primes = simple_sieve(math.isqrt(max(2, int(gaps.max() // 2))) + 1)
    predicted = np.array([singular_series(int(gap), factor_primes) * li2(limit, 5_000) for gap in gaps], dtype=np.float64)

    plt.figure(figsize=(10, 6))
    plt.loglog(gaps, counts, "o", markersize=4, label="actual")
    plt.loglog(gaps, predicted, "-", linewidth=1.5, label="HL main term")
    plt.xlabel("gap size")
    plt.ylabel("frequency")
    plt.title(f"Prime gap distribution up to {limit:,}")
    plt.grid(True, which="both", alpha=0.3)
    plt.legend()
    plt.tight_layout()
    plt.savefig(path, dpi=150)
    plt.close()


def plot_error_terms(path: Path, hl_rows: Sequence[dict[str, float | int]], selected_gaps: Sequence[int]) -> None:
    plt.figure(figsize=(10, 6))
    for gap in selected_gaps:
        rows = [row for row in hl_rows if int(row["gap_size"]) == gap]
        if not rows:
            continue
        x_values = [int(row["x"]) for row in rows]
        errors = [float(row["error_term"]) for row in rows]
        plt.plot(x_values, errors, marker="o", label=f"g={gap}")
    plt.xscale("log")
    plt.xlabel("x")
    plt.ylabel("Delta(g, x)")
    plt.title("HL error term for selected prime gaps")
    plt.grid(True, which="both", alpha=0.3)
    plt.legend()
    plt.tight_layout()
    plt.savefig(path, dpi=150)
    plt.close()


def plot_spectral_density(path: Path, frequencies: np.ndarray, power: np.ndarray) -> None:
    plt.figure(figsize=(10, 6))
    if len(frequencies) > 1:
        plt.loglog(frequencies[1:], power[1:])
    else:
        plt.plot(frequencies, power)
    plt.xlabel("frequency")
    plt.ylabel("power")
    plt.title("Power spectrum of prime-gap error term")
    plt.grid(True, which="both", alpha=0.3)
    plt.tight_layout()
    plt.savefig(path, dpi=150)
    plt.close()


def parse_int_list(value: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in value.split(",") if part.strip())


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Numerically verify prime gap distribution theory.")
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT, help="Prime generation limit; default 100000000.")
    parser.add_argument("--segment-size", type=int, default=1 << 22, help="Odd-number span per sieve segment.")
    parser.add_argument("--x-values", type=parse_int_list, default=DEFAULT_X_VALUES, help="Comma-separated x values.")
    parser.add_argument("--gaps", type=parse_int_list, default=DEFAULT_SELECTED_GAPS, help="Comma-separated gaps for HL comparison.")
    parser.add_argument("--fft-gap", type=int, default=2, help="Gap size used for spectral density.")
    parser.add_argument("--fft-points", type=int, default=512, help="Number of uniform x-grid points for FFT.")
    parser.add_argument("--zeta-zeros", type=int, default=100, help="Number of zeta zeros for oscillatory approximation.")
    parser.add_argument("--integration-intervals", type=int, default=20_000, help="Simpson intervals for li2 integration.")
    parser.add_argument("--output-dir", type=Path, default=Path("."), help="Directory for CSV and PNG outputs.")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    limit = int(args.limit)
    output_dir = args.output_dir
    output_dir.mkdir(parents=True, exist_ok=True)

    x_values = tuple(sorted(x for x in args.x_values if 2 <= x <= limit))
    gap_sizes = tuple(gap for gap in args.gaps if gap > 0 and gap % 2 == 0)
    if not x_values:
        x_values = (limit,)
    if not gap_sizes:
        gap_sizes = DEFAULT_SELECTED_GAPS

    gap_data = collect_gap_data(limit, int(args.segment_size))
    write_gap_frequencies(output_dir / "gap_frequencies.csv", gap_data.frequencies)

    hl_rows = build_hl_comparison(gap_data, x_values, gap_sizes, int(args.integration_intervals))
    write_dict_rows(
        output_dir / "hl_comparison.csv",
        hl_rows,
        ["x", "gap_size", "exact_count", "hl_prediction", "error_term", "relative_error"],
    )

    zeta_rows = build_zeta_rows(hl_rows, int(args.zeta_zeros))
    write_dict_rows(
        output_dir / "zeta_oscillation.csv",
        zeta_rows,
        ["x", "gap_size", "error_term", "oscillatory_approx"],
    )

    start_x = max(3, min(x_values))
    fft_points = max(8, int(args.fft_points))
    x_grid = np.linspace(start_x, limit, fft_points, dtype=np.int64)
    error_series = build_error_series(gap_data, int(args.fft_gap), x_grid, max(200, int(args.integration_intervals) // 10))
    spacing = float(x_grid[1] - x_grid[0]) if len(x_grid) > 1 else 1.0
    frequencies, power = spectral_density(error_series, spacing)
    write_spectral_density(output_dir / "spectral_density.csv", frequencies, power)

    plot_gap_distribution(output_dir / "gap_distribution.png", gap_data.frequencies, limit)
    plot_error_terms(output_dir / "error_term.png", hl_rows, gap_sizes)
    plot_spectral_density(output_dir / "spectral_density.png", frequencies, power)

    dominant = np.argsort(power[1:])[-5:][::-1] + 1 if len(power) > 1 else np.array([], dtype=np.int64)
    print(f"Generated {len(gap_data.gaps):,} prime gaps up to {limit:,}.")
    print(f"Wrote outputs to {output_dir.resolve()}.")
    if len(dominant):
        peaks = ", ".join(f"{frequencies[i]:.6g}" for i in dominant)
        print(f"Dominant nonzero spectral frequencies: {peaks}")


if __name__ == "__main__":
    main()
