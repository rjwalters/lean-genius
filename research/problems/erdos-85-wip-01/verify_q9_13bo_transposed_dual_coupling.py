#!/usr/bin/env python3
"""Probe whether the strict point-cover dual locates a coupling source."""

import glob
import json
from itertools import combinations

from q9_symmetric_point_mass_obstruction import (
    N,
    contracted_collision_star_matching_cover,
    contracted_reverse_interval_point_cover,
    contracted_residual_rows,
    fixed_system,
    local_packing_family,
    local_packing_single_swap_certificate,
)


def summary(family):
    forced = set(family[0])
    possible = set()
    for packing in family:
        forced &= set(packing)
        possible |= set(packing)
    return {
        "forced_neighbors": sorted(forced),
        "possible_neighbors": sorted(possible),
    }


def main():
    total = 0
    located = 0
    full_certificate_located = 0
    certificate_pool_sizes = []
    certificate_noncoupling_sizes = []
    singleton_pool_count = 0
    clean_pool_count = 0
    minimum_block_selector_count = 0
    minimum_block_pool_sizes = []
    minimum_block_noncoupling_sizes = []
    dirty_pool_records = []
    counterexamples = []
    pattern = "research/problems/erdos-85-wip-01/q9_branch4*.json"
    for filename in sorted(glob.glob(pattern)):
        with open(filename, encoding="utf-8") as stream:
            system = fixed_system(json.load(stream))
        families = {row: local_packing_family(system, row) for row in range(N)}
        if any(not family for family in families.values()):
            continue
        local = {row: summary(families[row]) for row in range(N)}
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
                "strict": len(forced) + cover["cover_card"]
                >= system["degree"][target],
            }

        edges = set(system["edges"])
        for target, record in obstructed.items():
            if not record["strict"]:
                continue
            better_rows = [
                row for row, other in obstructed.items()
                if other["score"] < record["score"]
                and row in record["forced"] | record["impossible"]
            ]
            best_score = min(obstructed[row]["score"] for row in better_rows)
            for better in [
                row for row in better_rows
                if obstructed[row]["score"] == best_score
            ]:
                total += 1
                cover = contracted_reverse_interval_point_cover(
                    system, better, local
                )
                assert cover is not None
                weights = dict(cover["weights"])
                scale = cover["scale"]
                better_forced = set(cover["forced_incoming"])
                better_possible = {
                    row for row in range(N)
                    if better in local[row]["possible_neighbors"]
                }
                better_candidates = {
                    row for row in range(N)
                    if tuple(sorted((row, better))) in edges
                    and row in better_possible
                    and row not in better_forced
                    and all(not (system["blocks"][row] & system["blocks"][f])
                            for f in better_forced)
                }
                coupling_sources = set()
                for source in record["residual"]:
                    joint = any(
                        target in packing and better in packing
                        for packing in families[source]
                    )
                    swap = local_packing_single_swap_certificate(
                        system, source, target, better
                    )
                    if joint or swap is not None:
                        coupling_sources.add(source)
                tight = {
                    source for source in better_candidates
                    if sum(weights.get(point, 0)
                           for point in system["blocks"][source]) == scale
                }
                forced_star_atoms = {
                    source for source in range(N)
                    if tuple(sorted((source, better))) in edges
                    and source in better_possible
                    and source not in better_forced
                    and any(system["blocks"][source]
                            & system["blocks"][forced]
                            for forced in better_forced)
                }
                certificate_pool = record["residual"] & (
                    tight | forced_star_atoms
                )
                certificate_pool_sizes.append(len(certificate_pool))
                certificate_noncoupling_sizes.append(
                    len(certificate_pool - coupling_sources)
                )
                singleton_pool_count += len(certificate_pool) == 1
                clean_pool_count += certificate_pool <= coupling_sources
                minimum_block_size = min(
                    len(system["blocks"][source])
                    for source in certificate_pool
                )
                minimum_block_pool = {
                    source for source in certificate_pool
                    if len(system["blocks"][source]) == minimum_block_size
                }
                minimum_block_selector_count += bool(
                    coupling_sources & minimum_block_pool
                )
                minimum_block_pool_sizes.append(len(minimum_block_pool))
                minimum_block_noncoupling_sizes.append(
                    len(minimum_block_pool - coupling_sources)
                )
                if not certificate_pool <= coupling_sources:
                    dirty_pool_records.append({
                        "file": filename.rsplit("/", 1)[-1],
                        "target": target,
                        "better": better,
                        "atoms": [{
                            "row": source,
                            "couples": source in coupling_sources,
                            "tight": source in tight,
                            "forced_conflicts": sum(
                                bool(system["blocks"][source]
                                     & system["blocks"][forced])
                                for forced in better_forced
                            ),
                            "block_size": len(system["blocks"][source]),
                            "local_packing_count": len(families[source]),
                            "local_forced_card": len(
                                local[source]["forced_neighbors"]
                            ),
                        } for source in sorted(certificate_pool)],
                    })
                witnesses = coupling_sources & tight
                forced_star_sources = {
                    source for source in coupling_sources
                    if any(system["blocks"][source] & system["blocks"][forced]
                           for forced in better_forced)
                }
                if witnesses or forced_star_sources:
                    full_certificate_located += 1
                assert certificate_pool & coupling_sources
                if witnesses:
                    located += 1
                else:
                    source_diagnostics = {}
                    for source in sorted(coupling_sources):
                        source_diagnostics[source] = {
                            "candidate": source in better_candidates,
                            "edge": tuple(sorted((source, better))) in edges,
                            "possible": source in better_possible,
                            "forced": source in better_forced,
                            "conflicts_forced": sorted(
                                forced for forced in better_forced
                                if system["blocks"][source]
                                & system["blocks"][forced]
                            ),
                            "cover_weight": sum(
                                weights.get(point, 0)
                                for point in system["blocks"][source]
                            ),
                            "scale": scale,
                        }
                    counterexamples.append({
                        "file": filename.rsplit("/", 1)[-1],
                        "target": target,
                        "better": better,
                        "coupling_sources": sorted(coupling_sources),
                        "tight_candidates": sorted(tight),
                        "coupling_diagnostics": source_diagnostics,
                    })

    print(f"canonical boundary rows={total}")
    print(f"dual-located couplings={located}")
    print(f"full-certificate-located couplings={full_certificate_located}")
    print(
        "certificate-pool sizes="
        f"{min(certificate_pool_sizes)}..{max(certificate_pool_sizes)}; "
        "noncoupling atoms="
        f"{min(certificate_noncoupling_sizes)}.."
        f"{max(certificate_noncoupling_sizes)}"
    )
    print(
        f"singleton certificate pools={singleton_pool_count}; "
        f"all-atoms-couple pools={clean_pool_count}"
    )
    print(
        "minimum-block-size selector couples="
        f"{minimum_block_selector_count}/{total}; pool sizes="
        f"{min(minimum_block_pool_sizes)}..{max(minimum_block_pool_sizes)}; "
        "decoys="
        f"{min(minimum_block_noncoupling_sizes)}.."
        f"{max(minimum_block_noncoupling_sizes)}"
    )
    for record in dirty_pool_records:
        print("dirty-pool", record)
    assert full_certificate_located == total
    if counterexamples:
        print("transposed-dual tight-source conjecture: REFUTED")
        for item in counterexamples:
            print(item)
        raise SystemExit(1)
    print("transposed-dual tight-source conjecture: SURVIVES")


if __name__ == "__main__":
    main()
