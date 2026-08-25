#!/usr/bin/env python3
"""Test ABW essential point-pair transport to canonical B.3 boundary data."""

import glob
import json
from itertools import combinations

import numpy as np
from scipy.optimize import linprog

from q9_symmetric_point_mass_obstruction import (
    N, N_U1, contracted_collision_star_matching_cover,
    contracted_residual_rows, fixed_system, local_packing_family,
    local_packing_single_swap_certificate,
)


def fractional_matching(blocks, removed_points=frozenset(), removed_edge=None):
    kept = [
        i for i, block in enumerate(blocks)
        if i != removed_edge and not (block & removed_points)
    ]
    if not kept:
        return 0.0
    matrix = np.array([
        [int(point in blocks[i]) for i in kept] for point in range(N_U1)
    ], dtype=float)
    result = linprog(
        -np.ones(len(kept)), A_ub=matrix, b_ub=np.ones(N_U1),
        bounds=(0, 1), method="highs",
    )
    assert result.success
    return -float(result.fun)


def essential_deletions(blocks):
    baseline = fractional_matching(blocks)
    out = []
    for edge, block in enumerate(blocks):
        points = sorted(block)
        if len(points) == 3:
            choices = [(frozenset(set(points) - {v}), None) for v in points]
        else:
            # Pad a pair by one private dummy.  Keeping the dummy deletes the
            # two real points; deleting it removes only this edge in addition
            # to the one remaining real point.
            choices = [(frozenset(points), None)] + [
                (frozenset({v}), edge) for v in points
            ]
        for removed_points, removed_edge in choices:
            value = fractional_matching(blocks, removed_points, removed_edge)
            if value <= baseline - 1 + 1e-7:
                out.append((removed_points, removed_edge, value))
    assert out
    return baseline, out


def local_summary(families, row):
    forced = set(families[row][0])
    possible = set()
    for packing in families[row]:
        forced &= set(packing)
        possible |= set(packing)
    return {"forced_neighbors": forced, "possible_neighbors": possible}


def main():
    records = []
    for filename in sorted(glob.glob(
            "research/problems/erdos-85-wip-01/q9_branch4*.json")):
        with open(filename, encoding="utf-8") as stream:
            system = fixed_system(json.load(stream))
        families = {u: local_packing_family(system, u) for u in range(N)}
        if any(not families[u] for u in range(N)):
            continue
        local = {u: local_summary(families, u) for u in range(N)}
        obstructed = {}
        for w in range(N):
            forced = {u for u in range(N) if w in local[u]["forced_neighbors"]}
            impossible = {
                u for u in range(N) if w not in local[u]["possible_neighbors"]
            }
            compatible = any(
                forced <= packing and packing.isdisjoint(impossible)
                for packing in families[w]
            )
            conflict = any(
                system["blocks"][u] & system["blocks"][v]
                for u, v in combinations(forced, 2)
            )
            if compatible or conflict:
                continue
            residual = set(contracted_residual_rows(system, w, local))
            cover = contracted_collision_star_matching_cover(system, w, local)
            obstructed[w] = {
                "forced": forced, "impossible": impossible,
                "residual": residual,
                "score": (len(residual), -len(forced)),
                "fails": len(forced) + cover["cover_card"] >= system["degree"][w],
            }
        for w, record in obstructed.items():
            if not record["fails"]:
                continue
            boundary = [
                z for z, other in obstructed.items()
                if other["score"] < record["score"]
                and z in record["forced"] | record["impossible"]
            ]
            score = min(obstructed[z]["score"] for z in boundary)
            for z in [z for z in boundary if obstructed[z]["score"] == score]:
                coupled = {
                    x for x in record["residual"]
                    if any(w in p and z in p for p in families[x])
                    or local_packing_single_swap_certificate(system, x, w, z)
                    is not None
                }
                assert coupled
                rows = sorted(record["residual"])
                blocks = [system["blocks"][x] for x in rows]
                baseline, deletions = essential_deletions(blocks)
                touches_z = [
                    item for item in deletions
                    if item[0] & system["blocks"][z]
                ]
                transports = [
                    item for item in touches_z
                    if any(item[0] & system["blocks"][x] for x in coupled)
                    or (item[1] is not None and rows[item[1]] in coupled)
                ]
                records.append((filename, w, z, baseline, len(deletions),
                                len(touches_z), len(transports)))
    print(f"canonical pairs: {len(records)}")
    assert len(records) == 19
    print("essential deletion touches z:",
          f"{sum(record[5] > 0 for record in records)}/{len(records)}")
    print("essential deletion touches z and a coupling source:",
          f"{sum(record[6] > 0 for record in records)}/{len(records)}")
    assert sum(record[5] > 0 for record in records) == 11
    assert sum(record[6] > 0 for record in records) == 8
    for record in records:
        if record[6] == 0:
            print("first transport failure:", record)
            break


if __name__ == "__main__":
    main()
