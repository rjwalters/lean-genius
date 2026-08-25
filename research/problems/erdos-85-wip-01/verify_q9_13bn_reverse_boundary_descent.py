#!/usr/bin/env python3
"""Audit the reverse-boundary sharpening of the B.3 (13bn) descent."""

import glob
import json
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
        "packing_count": len(families[row]),
        "forced_neighbors": sorted(forced),
        "possible_neighbors": sorted(possible),
    }


def main():
    witnesses = []
    payload_count = 0
    canonical_better_count = 0
    canonical_point_cover_count = 0
    canonical_point_cover_deficits = []
    pattern = "research/problems/erdos-85-wip-01/q9_branch4*.json"
    for filename in sorted(glob.glob(pattern)):
        with open(filename, encoding="utf-8") as stream:
            system = fixed_system(json.load(stream))
        families = {row: local_packing_family(system, row) for row in range(N)}
        if any(not families[row] for row in range(N)):
            continue
        payload_count += 1
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
                "strict_terminal_fails": (
                    len(forced) + cover["cover_card"]
                    >= system["degree"][target]
                ),
            }

        for target, record in obstructed.items():
            if not record["strict_terminal_fails"]:
                continue
            boundary_better = [
                better for better, better_record in obstructed.items()
                if better_record["score"] < record["score"]
                and better in record["forced"] | record["impossible"]
            ]
            assert boundary_better, (filename, target, record)
            canonical_score = min(
                obstructed[better]["score"] for better in boundary_better
            )
            canonical_betters = [
                better for better in boundary_better
                if obstructed[better]["score"] == canonical_score
            ]
            canonical_better_count += len(canonical_betters)
            for better in canonical_betters:
                point_cover = contracted_reverse_interval_point_cover(
                    system, better, local
                )
                assert point_cover is not None, (
                    filename, target, better, obstructed[better]
                )
                canonical_point_cover_count += 1
                canonical_point_cover_deficits.append(
                    point_cover["scaled_demand_after_forced"]
                    - point_cover["scaled_total"]
                )
            candidates = []
            for better, better_record in obstructed.items():
                if better not in canonical_betters:
                    continue
                if better not in record["forced"] | record["impossible"]:
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
                        candidates.append({
                            "target": target,
                            "better": better,
                            "source": source,
                            "boundary": (
                                "forced" if better in record["forced"]
                                else "impossible"
                            ),
                            "joint": joint,
                            "single_swap": swap is not None,
                        })
            assert candidates, (filename, target, record)
            assert {item["better"] for item in candidates} == set(
                canonical_betters
            ), (filename, target, canonical_betters, candidates)
            witnesses.append((Path(filename).name, min(
                candidates,
                key=lambda item: (item["better"], item["source"]),
            )))

    assert payload_count == 10
    assert len(witnesses) == 17
    assert canonical_point_cover_count == canonical_better_count == 19
    forced_count = sum(item["boundary"] == "forced" for _, item in witnesses)
    impossible_count = len(witnesses) - forced_count
    print(f"verified: {payload_count} all-row-feasible stored payloads")
    print(f"verified: {len(witnesses)} strict dual-terminal failures")
    print("verified: every failure has a reverse-boundary lex descent")
    print(
        "verified: every minimum-score boundary row is exchange-coupled "
        f"({canonical_better_count} rows)"
    )
    print(
        "verified: every minimum-score boundary row has a strict "
        "fractional point-cover certificate "
        f"(scaled deficits {min(canonical_point_cover_deficits)}"
        f"..{max(canonical_point_cover_deficits)})"
    )
    print(f"selected boundary types: forced={forced_count}, impossible={impossible_count}")
    for filename, witness in witnesses:
        print(filename, witness)


if __name__ == "__main__":
    main()
