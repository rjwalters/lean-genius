#!/usr/bin/env python3
"""Audit the 18 concurrent branch-3 local-packing triples exactly."""

from __future__ import annotations

import argparse
import hashlib
import json
from itertools import combinations
from pathlib import Path

from q9_symmetric_point_mass_obstruction import (
    fixed_system,
    random_outer,
)


def local_packings(system: dict, row: int) -> list[frozenset[int]]:
    neighbors = [
        v if u == row else u
        for u, v in system["edges"] if row in (u, v)
    ]
    return [
        frozenset(packing)
        for packing in combinations(neighbors, system["degree"][row])
        if all(
            system["blocks"][u].isdisjoint(system["blocks"][v])
            for u, v in combinations(packing, 2)
        )
    ]


def audit(system: dict) -> dict:
    if system["branch"] != 3:
        raise ValueError("concurrent packing audit requires branch 3")
    cache: dict[int, list[frozenset[int]]] = {}
    records = []
    for hole in (24, 25):
        for first, second in combinations(range(24), 2):
            common = sorted(
                system["blocks"][hole]
                & system["blocks"][first]
                & system["blocks"][second]
            )
            if not common:
                continue
            for row in (hole, first, second):
                if row not in cache:
                    cache[row] = local_packings(system, row)
            families = (cache[hole], cache[first], cache[second])
            pair_counts = [
                sum(X.isdisjoint(Y) for X in families[i]
                    for Y in families[j])
                for i, j in ((0, 1), (0, 2), (1, 2))
            ]
            triple_count = sum(
                X.isdisjoint(Y) and X.isdisjoint(Z) and Y.isdisjoint(Z)
                for X in families[0]
                for Y in families[1]
                for Z in families[2]
            )
            records.append({
                "hole": hole,
                "regular_rows": [first, second],
                "common_point": common[0],
                "packing_counts": [len(family) for family in families],
                "pairwise_disjoint_counts": pair_counts,
                "pairwise_disjoint_triple_count": triple_count,
                "obstructed": triple_count == 0,
                "genuinely_three_way": (
                    triple_count == 0 and all(count > 0 for count in pair_counts)
                ),
            })
    obstructed = [record for record in records if record["obstructed"]]
    return {
        "concurrent_shape_count": len(records),
        "obstructed_count": len(obstructed),
        "genuinely_three_way_count": sum(
            record["genuinely_three_way"] for record in records
        ),
        "obstructed": obstructed,
        "records": records,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("payload", type=Path, nargs="?")
    parser.add_argument("--random-seed", type=int)
    parser.add_argument("--timeout-seconds", type=int, default=30)
    args = parser.parse_args()
    if args.payload is None:
        if args.random_seed is None:
            parser.error("provide a payload or --random-seed")
        payload = random_outer(3, args.random_seed, args.timeout_seconds)
    else:
        payload = json.loads(args.payload.read_text())
    canonical = json.dumps(
        payload, sort_keys=True, separators=(",", ":")
    ).encode()
    result = audit(fixed_system(payload))
    result["payload_sha256"] = hashlib.sha256(canonical).hexdigest()
    print(json.dumps(result, separators=(",", ":")))


if __name__ == "__main__":
    main()
