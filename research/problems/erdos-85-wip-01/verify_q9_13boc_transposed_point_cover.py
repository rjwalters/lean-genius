#!/usr/bin/env python3
"""Refute recovery of a coupling source from boundary point-cover slack."""

import glob
import json
from fractions import Fraction
from itertools import combinations
from pathlib import Path

from q9_symmetric_point_mass_obstruction import (
    N,
    contracted_collision_star_matching_cover,
    contracted_reverse_interval_point_cover,
    contracted_residual_rows,
    fixed_system,
    local_packing_family,
    local_packing_single_swap_certificate,
)


def local_summary(families, row):
    forced = set(families[row][0])
    possible = set()
    for packing in families[row]:
        forced &= set(packing)
        possible |= set(packing)
    return {
        "forced_neighbors": sorted(forced),
        "possible_neighbors": sorted(possible),
    }


def main():
    records = []
    for filename in sorted(glob.glob(
            "research/problems/erdos-85-wip-01/q9_branch4*.json")):
        with open(filename, encoding="utf-8") as stream:
            system = fixed_system(json.load(stream))
        families = {row: local_packing_family(system, row) for row in range(N)}
        if any(not families[row] for row in range(N)):
            continue
        local = {row: local_summary(families, row) for row in range(N)}
        obstructed = {}
        for target in range(N):
            forced = {
                row for row in range(N)
                if target in local[row]["forced_neighbors"]
            }
            impossible = {
                row for row in range(N)
                if target not in local[row]["possible_neighbors"]
            }
            compatible = any(
                forced <= packing and packing.isdisjoint(impossible)
                for packing in families[target]
            )
            forced_conflict = any(
                system["blocks"][u] & system["blocks"][v]
                for u, v in combinations(forced, 2)
            )
            if compatible or forced_conflict:
                continue
            residual = set(contracted_residual_rows(system, target, local))
            cover = contracted_collision_star_matching_cover(
                system, target, local
            )
            obstructed[target] = {
                "forced": forced,
                "impossible": impossible,
                "residual": residual,
                "score": (len(residual), -len(forced)),
                "fails": (
                    len(forced) + cover["cover_card"]
                    >= system["degree"][target]
                ),
            }
        for target, record in obstructed.items():
            if not record["fails"]:
                continue
            boundary = [
                z for z, other in obstructed.items()
                if other["score"] < record["score"]
                and z in record["forced"] | record["impossible"]
            ]
            score = min(obstructed[z]["score"] for z in boundary)
            for z in [z for z in boundary if obstructed[z]["score"] == score]:
                cover = contracted_reverse_interval_point_cover(system, z, local)
                assert cover is not None
                weights = dict(cover["weights"])
                scale = cover["scale"]
                loads = {
                    x: sum(weights.get(p, 0) for p in system["blocks"][x])
                    for x in record["residual"]
                }
                coupled = set()
                for x in record["residual"]:
                    joint = any(
                        target in packing and z in packing
                        for packing in families[x]
                    )
                    swap = local_packing_single_swap_certificate(
                        system, x, target, z
                    )
                    if joint or swap is not None:
                        coupled.add(x)
                assert coupled
                minimum = min(loads.values())
                maximum = max(loads.values())
                minimum_sources = {x for x, load in loads.items() if load == minimum}
                maximum_sources = {x for x, load in loads.items() if load == maximum}
                tight_sources = {x for x, load in loads.items() if load == scale}
                records.append({
                    "file": Path(filename).name,
                    "w": target,
                    "z": z,
                    "scale": scale,
                    "minimum": minimum,
                    "maximum": maximum,
                    "coupled": coupled,
                    "minimum_sources": minimum_sources,
                    "maximum_sources": maximum_sources,
                    "tight_sources": tight_sources,
                })

    print(f"canonical pairs: {len(records)}")
    assert len(records) == 19
    tests = {
        "some tight source couples": lambda r: bool(r["tight_sources"] & r["coupled"]),
        "some minimum-load source couples": lambda r: bool(r["minimum_sources"] & r["coupled"]),
        "every minimum-load source couples": lambda r: r["minimum_sources"] <= r["coupled"],
        "some maximum-load source couples": lambda r: bool(r["maximum_sources"] & r["coupled"]),
    }
    for label, test in tests.items():
        passed = sum(test(record) for record in records)
        print(f"{label}: {passed}/{len(records)}")
        if passed != len(records):
            bad = next(record for record in records if not test(record))
            print("first failure:", bad)
    assert sum(bool(r["tight_sources"] & r["coupled"]) for r in records) == 16
    assert sum(bool(r["minimum_sources"] & r["coupled"]) for r in records) == 14
    assert sum(r["minimum_sources"] <= r["coupled"] for r in records) == 0
    assert sum(bool(r["maximum_sources"] & r["coupled"]) for r in records) == 16
    print("tight-recovery failures:")
    for record in records:
        if not (record["tight_sources"] & record["coupled"]):
            print(record)


if __name__ == "__main__":
    main()
