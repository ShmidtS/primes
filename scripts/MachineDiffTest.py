#!/usr/bin/env python3
"""Differential tests of the reference machine (audit v7, stage 6,
qwenputer fuzz.py pattern): Python port of ReferenceMachine
(Hagi/Model/ReferenceMachine.lean) on random configurations.

Checks the formally proven laws:
  1. jointStep_energy:        E(w') == (1-eta)^2 * E(w)
  2. jointStep_energy_decrease: 0<eta<2, w!=a => E(w') < E(w)
  3. machine_quant_err_bound: quantErr <= sqrt(n)*Delta/2
  4. machine_energy_bound:    E(machineStep) <= (sqrt(Sd)+sqrt(n)*Delta/2)^2/2
  5. machine_advance_certified (bridge): under the ledger premise
     (Em - Ep <= kappa*s*q) the certified drop holds:
     E0 - Em >= eta*|d|^2 - eta^2*|d|^2/2 - kappa*s*q

Numeric validation is NOT a substitute for the Lean proofs; it
catches implementation divergence from the formal model.
"""
import math
import random
import sys

TRIALS = 2000
TOL = 1e-9


def energy(a, w):
    return sum((wi - ai) ** 2 for ai, wi in zip(a, w)) / 2


def joint_step(a, w, eta):
    return [wi - eta * (wi - ai) for ai, wi in zip(a, w)]


def compress_q(delta, w):
    return [delta * round(wi / delta) for wi in w]


def quant_err(delta, w):
    return math.sqrt(sum((qi - wi) ** 2 for qi, wi in
                         zip(compress_q(delta, w), w)))


def run(seed):
    rng = random.Random(seed)
    n = rng.randint(1, 8)
    a = [rng.uniform(-3, 3) for _ in range(n)]
    w = [ai + rng.choice([-1, 1]) * rng.uniform(0.01, 2) for ai in a]
    eta = rng.uniform(0.01, 1.9)
    delta = rng.uniform(0.05, 1.0)
    kappa = rng.uniform(0.5, 3.0)
    s = rng.uniform(0.5, 2.0)

    E0 = energy(a, w)
    wp = joint_step(a, w, eta)
    Ep = energy(a, wp)
    wm = compress_q(delta, wp)
    Em = energy(a, wm)

    # 1. energy law
    assert abs(Ep - (1 - eta) ** 2 * E0) <= TOL * (1 + abs(E0)),         f"energy law: {Ep} != {(1-eta)**2 * E0}"
    # 2. strict decrease
    assert Ep < E0, "strict decrease failed"
    # 3. quant err bound
    q = quant_err(delta, wp)
    assert q <= math.sqrt(n) * delta / 2 + TOL,         f"quant err {q} > {math.sqrt(n)*delta/2}"
    # 4. full bound
    Sd = sum((x - ai) ** 2 for x, ai in zip(wp, a))
    rhs = (math.sqrt(Sd) + math.sqrt(n) * delta / 2) ** 2 / 2
    assert Em <= rhs + TOL, f"full bound: {Em} > {rhs}"
    # 5. certified drop (bridge): under the ledger premise
    d2 = sum((wi - ai) ** 2 for wi, ai in zip(w, a))
    drop = eta * d2 - eta ** 2 * d2 / 2 - kappa * s * q
    if Em - Ep <= kappa * s * q + TOL:
        assert E0 - Em >= drop - 1e-6 * (1 + E0),             f"certified drop: {E0 - Em} < {drop}"
        return ("cert", n)
    return ("skip", n)


def main():
    fails = 0
    certs = 0
    skips = 0
    for seed in range(TRIALS):
        try:
            kind, _ = run(seed)
            if kind == "cert":
                certs += 1
            else:
                skips += 1
        except AssertionError as e:
            print(f"FAIL seed={seed}: {e}")
            fails += 1
            if fails > 5:
                break
    if fails:
        print(f"MACHINEDIFF: FAIL ({fails} failures)")
        sys.exit(1)
    print(f"MACHINEDIFF: PASS ({TRIALS} configs; "
          f"{certs} certified, {skips} outside ledger premise)")


if __name__ == "__main__":
    main()
