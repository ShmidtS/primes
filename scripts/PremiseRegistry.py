#!/usr/bin/env python3
"""PremiseRegistry (C361, audit step 2.2): typed premise registry.

Validates scripts/premise_registry.toml against a FRESH
AssumptionScan scan (not the lock file), fail-closed both ways:

  * coverage: every scanned premise name (h_emp binders minus
    proven theorems, operational names, unprefixed per-file
    empirical premises) MUST be classified — unknown name FAILs;
  * staleness: every registry premise entry MUST still be found
    by the scan — stale entry FAILs;
  * enum: every `type` must be one of TYPES;
  * metadata: empirical entries require non-empty `measured`.

Marker: PREMISEREGISTRY: PASS (...) / FAIL, exit code 0/1.
"""
import sys
import tomllib
from pathlib import Path

import AssumptionScan

SCRIPTS = Path(__file__).resolve().parent
REGISTRY = SCRIPTS / "premise_registry.toml"

TYPES = ("mathematical", "model", "empirical",
         "operational", "approximation")

STATUS_ENUM = ("Proven", "Conditional", "Empirical",
               "Speculative", "Deprecated")


def load_registry(path=REGISTRY):
    """Load and structurally validate the toml registry."""
    with open(path, "rb") as fh:
        data = tomllib.load(fh)
    problems = []
    premises = data.get("premises", {})
    if not premises:
        problems.append("no [premises.*] entries")
    for name, entry in premises.items():
        if not isinstance(entry, dict):
            problems.append(f"{name}: entry is not a table")
            continue
        ptype = entry.get("type")
        if ptype not in TYPES:
            problems.append(f"{name}: invalid type {ptype!r} "
                            f"(not in {TYPES})")
        elif ptype == "empirical" and not entry.get("measured", "").strip():
            problems.append(f"{name}: empirical premise requires "
                            "non-empty `measured`")
    modules = data.get("modules", {})
    for key in ("quarantine", "research_prefixes", "deprecated_prefixes"):
        if key in modules and not isinstance(modules[key], list):
            problems.append(f"modules.{key}: expected a list")
    return data, problems


def required_names(hmap, proven, operational):
    """Premise names a fresh scan requires to be classified."""
    names = set()
    for per_file in hmap.values():
        names.update(per_file)
    names -= proven  # proven h_emp-named theorems are NOT premises
    unprefixed = set()
    for rel, counts in AssumptionScan.UNPREFIXED_EMPIRICAL.items():
        for n in counts:
            unprefixed.add(f"{rel}::{n}")
    return names, set(operational), unprefixed


def validate(scan_result=None, data=None):
    """Full validation; returns (problems, stats)."""
    if data is None:
        data, problems = load_registry()
    else:
        problems = []
    if scan_result is None:
        scan_result = AssumptionScan.scan()
    hmap, _prims, proven, operational = scan_result
    if problems:
        return problems, {}
    want_h, want_op, want_un = required_names(hmap, proven, operational)
    premises = data["premises"]
    have = {}
    for key, entry in premises.items():
        if "::" in key:
            have[key] = entry
    have_plain = {k: v for k, v in premises.items() if "::" not in k}
    # coverage
    for n in sorted(want_h):
        if n not in have_plain:
            problems.append(f"unclassified h_emp premise binder: {n}")
    for n in sorted(want_op):
        if n not in have_plain:
            problems.append(f"unclassified operational premise name: {n}")
    for n in sorted(want_un):
        if n not in have:
            problems.append(f"unclassified unprefixed empirical "
                            f"premise: {n}")
    # staleness
    for key in have_plain:
        if "::" in key:
            continue
        if key.startswith("h_emp_"):
            if key not in want_h and key not in proven:
                problems.append(f"stale registry entry (not scanned): "
                                f"{key}")
        elif key not in want_op:
            problems.append(f"stale registry entry (not scanned): {key}")
    for key in have:
        if key not in want_un:
            problems.append(f"stale registry entry (not scanned): {key}")
    stats = {}
    for entry in premises.values():
        stats[entry.get("type", "?")] = stats.get(entry.get("type", "?"), 0) + 1
    return problems, stats


def main():
    data, problems = load_registry()
    problems2, stats = validate(data=data)
    problems += problems2
    if problems:
        for p in problems:
            print(f"PREMISEREGISTRY: FAIL ({p})")
        return 1
    total = sum(stats.values())
    detail = ", ".join(f"{t}={stats[t]}" for t in TYPES if t in stats)
    print(f"PREMISEREGISTRY: PASS ({total} premises classified: {detail})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
