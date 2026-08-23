#!/usr/bin/env python3
"""Audit the correctly scoped branch-3 certificate disjunction.

The two horns are:

* a strict bounded-denominator reduced full-fiber cover at a maximum-load
  exceptional-hole point; or
* an infeasible reciprocity-preserving partial primal on one exceptional and
  two regular triple rows.

The denominator bound is only a corpus-search parameter.  A pass is evidence
for the disjunction, not a proof that the chosen bound is universal.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from q9_bounded_denominator_full_fiber import scaled_cover
from q9_branch3_partial_primal_audit import first_infeasible_partial
from q9_symmetric_point_mass_obstruction import fixed_system, primal


def audit(payload: dict, max_denominator: int) -> dict:
    system = fixed_system(payload)
    if system["branch"] != 3:
        raise ValueError("certificate disjunction audit requires branch 3")

    hole_points = sorted(system["blocks"][24] | system["blocks"][25])
    loads = {
        point: sum(
            system["degree"][row]
            for row, block in enumerate(system["blocks"])
            if point in block
        )
        for point in hole_points
    }
    maximum_load = max(loads.values())
    maximum_points = [
        point for point in hole_points if loads[point] == maximum_load
    ]
    full_fiber_witness = None
    for denominator in range(1, max_denominator + 1):
        for point in maximum_points:
            witness = scaled_cover(system, point, denominator)
            if witness is not None:
                full_fiber_witness = witness
                break
        if full_fiber_witness is not None:
            break

    sparse_witness = first_infeasible_partial(system)
    globally_feasible = primal(system).success
    return {
        "global_primal_feasible": globally_feasible,
        "maximum_exceptional_hole_load": maximum_load,
        "maximum_load_points": maximum_points,
        "full_fiber_denominator_bound": max_denominator,
        "full_fiber_witness": full_fiber_witness,
        "sparse_partial_witness": sparse_witness,
        "certificate_disjunction_holds":
            full_fiber_witness is not None or sparse_witness is not None,
        "unclosed_infeasible_payload":
            not globally_feasible
            and full_fiber_witness is None
            and sparse_witness is None,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("payload", type=Path)
    parser.add_argument("--max-denominator", type=int, default=12)
    args = parser.parse_args()
    if args.max_denominator < 1:
        parser.error("--max-denominator must be positive")
    payload = json.loads(args.payload.read_text())
    canonical = json.dumps(
        payload, sort_keys=True, separators=(",", ":")
    ).encode()
    result = audit(payload, args.max_denominator)
    result["payload_sha256"] = hashlib.sha256(canonical).hexdigest()
    print(json.dumps(result, separators=(",", ":")))


if __name__ == "__main__":
    main()
