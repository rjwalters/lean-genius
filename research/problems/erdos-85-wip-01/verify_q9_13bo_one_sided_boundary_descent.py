#!/usr/bin/env python3
"""Verify the one-sided reverse-obstruction sharpening of (13bo)."""

import glob
import json
from itertools import combinations

from q9_symmetric_point_mass_obstruction import (
    N,
    contracted_collision_star_matching_cover,
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
    return forced, possible


def main():
    payload_count = 0
    failure_count = 0
    forced_deficit_count = 0
    impossible_deficit_count = 0
    overlap_count = 0
    pattern = "research/problems/erdos-85-wip-01/q9_branch4*.json"
    for filename in sorted(glob.glob(pattern)):
        with open(filename, encoding="utf-8") as stream:
            system = fixed_system(json.load(stream))
        families = {row: local_packing_family(system, row) for row in range(N)}
        if any(not families[row] for row in range(N)):
            continue
        payload_count += 1
        local = {row: local_summary(families, row) for row in range(N)}
        local_dict = {
            row: {
                "forced_neighbors": sorted(local[row][0]),
                "possible_neighbors": sorted(local[row][1]),
            }
            for row in range(N)
        }

        obstructed = {}
        for target in range(N):
            forced = {
                row for row in range(N) if target in local[row][0]
            }
            impossible = {
                row for row in range(N) if target not in local[row][1]
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
            residual = set(contracted_residual_rows(
                system, target, local_dict
            ))
            cover = contracted_collision_star_matching_cover(
                system, target, local_dict
            )
            obstructed[target] = {
                "forced": forced,
                "impossible": impossible,
                "residual": residual,
                "score": (len(residual), -len(forced)),
                "strict_terminal_fails": (
                    len(forced) + cover["cover_card"]
                    >= system["degree"][target]
                ),
                "forced_deficit": not any(
                    forced <= packing for packing in families[target]
                ),
                "impossible_deficit": not any(
                    packing.isdisjoint(impossible)
                    for packing in families[target]
                ),
            }

        for target, record in obstructed.items():
            if not record["strict_terminal_fails"]:
                continue
            failure_count += 1
            candidates = []
            for better, better_record in obstructed.items():
                if better_record["score"] >= record["score"]:
                    continue
                if better not in record["forced"] | record["impossible"]:
                    continue
                if not (
                    better_record["forced_deficit"]
                    or better_record["impossible_deficit"]
                ):
                    continue
                for source in sorted(record["residual"]):
                    joint = any(
                        target in packing and better in packing
                        for packing in families[source]
                    )
                    swap = local_packing_single_swap_certificate(
                        system, source, target, better
                    )
                    if joint or swap is not None:
                        candidates.append((better, source, better_record))
            assert candidates, (filename, target, record)
            _, _, selected = min(
                candidates, key=lambda item: (item[0], item[1])
            )
            if selected["forced_deficit"]:
                forced_deficit_count += 1
            if selected["impossible_deficit"]:
                impossible_deficit_count += 1
            if (
                selected["forced_deficit"]
                and selected["impossible_deficit"]
            ):
                overlap_count += 1

    assert payload_count == 10
    assert failure_count == 17
    assert forced_deficit_count == 14
    assert impossible_deficit_count == 9
    assert overlap_count == 6
    print(f"verified: {payload_count} all-row-feasible stored payloads")
    print(f"verified: {failure_count} strict dual-terminal failures")
    print("verified: every failure has a one-sided reverse-boundary descent")
    print(
        "selected one-sided deficits: "
        f"forced={forced_deficit_count}, "
        f"impossible={impossible_deficit_count}, overlap={overlap_count}"
    )


if __name__ == "__main__":
    main()
