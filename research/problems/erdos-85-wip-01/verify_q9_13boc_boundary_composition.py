#!/usr/bin/env python3
"""Probe the proposed boundary-composition deficit identity for B.3.

For every stored all-row-feasible strict terminal failure ``w``, compute the
exact maximum size of a partial local packing that contains every reverse-
forced row and avoids every reverse-impossible row.  Compare its deficit with
the number of reverse-obstructed rows on ``F_w union I_w``.  Equality is the
most literal executable form of the composition proposal from divergence #64.
"""

import glob
import json
from itertools import combinations

from q9_symmetric_point_mass_obstruction import (
    N,
    contracted_collision_star_matching_cover,
    contracted_residual_rows,
    fixed_system,
    local_packing_family,
)


def summaries(families):
    result = {}
    for row, family in families.items():
        forced = set(family[0])
        possible = set()
        for packing in family:
            forced &= set(packing)
            possible |= set(packing)
        result[row] = (forced, possible)
    return result


def interval_data(system, families, local, target):
    forced = {row for row in range(N) if target in local[row][0]}
    impossible = {row for row in range(N) if target not in local[row][1]}
    feasible = any(
        forced <= packing and packing.isdisjoint(impossible)
        for packing in families[target]
    )
    forced_conflict = any(
        system["blocks"][u] & system["blocks"][v]
        for u, v in combinations(forced, 2)
    )
    residual = set(contracted_residual_rows(
        system, target,
        {row: {
            "forced_neighbors": sorted(local[row][0]),
            "possible_neighbors": sorted(local[row][1]),
        } for row in range(N)},
    ))
    return forced, impossible, feasible, forced_conflict, residual


def matching_card(system, rows):
    blocks = system["blocks"]
    ordered = sorted(rows, key=lambda row: len(blocks[row]), reverse=True)
    best = 0

    def search(index, used, size):
        nonlocal best
        if size + len(ordered) - index <= best:
            return
        if index == len(ordered):
            best = max(best, size)
            return
        search(index + 1, used, size)
        row = ordered[index]
        if blocks[row].isdisjoint(used):
            search(index + 1, used | blocks[row], size + 1)

    search(0, set(), 0)
    return best


def main():
    records = []
    payload_count = 0
    for filename in sorted(glob.glob(
            "research/problems/erdos-85-wip-01/q9_branch4*.json")):
        with open(filename, encoding="utf-8") as stream:
            system = fixed_system(json.load(stream))
        families = {row: local_packing_family(system, row) for row in range(N)}
        if any(not families[row] for row in range(N)):
            continue
        payload_count += 1
        local = summaries(families)
        intervals = {
            row: interval_data(system, families, local, row)
            for row in range(N)
        }
        local_dict = {row: {
            "forced_neighbors": sorted(local[row][0]),
            "possible_neighbors": sorted(local[row][1]),
        } for row in range(N)}
        for target, (forced, impossible, feasible, forced_conflict,
                     residual) in intervals.items():
            if feasible or forced_conflict:
                continue
            cover = contracted_collision_star_matching_cover(
                system, target, local_dict
            )
            if len(forced) + cover["cover_card"] < system["degree"][target]:
                continue
            rank = len(forced) + matching_card(system, residual)
            deficit = system["degree"][target] - rank
            boundary = forced | impossible
            obstructed_boundary = {
                row for row in boundary if not intervals[row][2]
            }
            records.append((
                filename.rsplit("/", 1)[-1], target, deficit,
                len(obstructed_boundary), sorted(obstructed_boundary),
            ))

    assert payload_count == 10
    assert len(records) == 17
    equal = [record for record in records if record[2] == record[3]]
    assert all(record[2] == 1 for record in records)
    assert not equal
    print(f"verified: {payload_count} all-row-feasible stored payloads")
    print(f"verified: {len(records)} strict terminal failures")
    print(
        "composition identity deficit=obstructed-boundary-card: "
        f"{len(equal)}/{len(records)}"
    )
    for record in records:
        print(record)


if __name__ == "__main__":
    main()
