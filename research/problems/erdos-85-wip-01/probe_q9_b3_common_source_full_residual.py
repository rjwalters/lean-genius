#!/usr/bin/env python3
"""Probe a common-source alternating core while restoring residual clauses."""

import argparse
from z3 import And, Not, is_true, sat, unsat

from q9_b0_residual_defect_sat import N_U1, build, edge_key
from q9_symmetric_point_mass_obstruction import OUTER_ONLY_RELAX
from verify_q9_b3_common_source_qk_exchange_countermodel import (
    BLOCKS, K_EDGES,
)


CORE_BLOCKS = {
    8: [3, 12, 22],
    9: [2, 9, 19],
    10: [5, 8, 20],
    16: [5, 15, 19],
    17: [2, 8, 22],
    18: [3, 9, 20],
}
SOURCE = 26

RESTORE_GROUPS = {
    "outer": set(),
    "row": {"row-ledger", "marked-miss"},
    "residual-c4": {"residual-c4"},
    "b0-c4": {"b0-c4"},
    "dtb-common": {"dtb-common", "dtb-cap"},
    "dtb-zero": {"dtb-zero"},
    "dtb-ledger": {"dtb-rows", "dtb-columns", "marked-miss"},
    "full": set(OUTER_ONLY_RELAX),
}
for _name, _group in list(RESTORE_GROUPS.items()):
    if _name not in {"outer", "full"}:
        RESTORE_GROUPS[f"full-no-{_name}"] = set(OUTER_ONLY_RELAX) - _group


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=RESTORE_GROUPS)
    parser.add_argument(
        "--restore", action="append",
        choices=[
            "row", "residual-c4", "b0-c4", "dtb-common",
            "dtb-zero", "dtb-ledger",
        ],
        help="override mode and restore exactly these named groups",
    )
    parser.add_argument(
        "--restore-clause", action="append", choices=sorted(OUTER_ONLY_RELAX),
        help="add one exact relaxed clause family to the restored set",
    )
    parser.add_argument("--timeout-seconds", type=int, default=20)
    parser.add_argument("--pin-payload", action="store_true")
    parser.add_argument("--expect", choices=["sat", "unsat", "unknown"])
    args = parser.parse_args()
    restored = RESTORE_GROUPS[args.mode]
    if args.restore:
        restored = set().union(*(RESTORE_GROUPS[name] for name in args.restore))
    if args.restore_clause:
        restored = set(restored) | set(args.restore_clause)
    relax = OUTER_ONLY_RELAX - restored
    payload = None
    if args.pin_payload:
        payload = {"branch": 3, "blocks": BLOCKS, "k_edges": K_EDGES}
    solver, data = build(
        3, args.timeout_seconds * 1000, True,
        outer_seed=payload, relax=relax,
    )
    incidence = data["incidence"]
    k = data["k"]

    # Pin only the six rainbow blocks.  Their intersection graph is
    # K_{3,3}-wz with shores 8,9,10 and 16,17,18.
    for row, block in CORE_BLOCKS.items():
        support = set(block)
        for point in range(N_U1):
            solver.add(incidence[row, point] == (point in support))

    # Row 26 is a pair row in branch 3.  Require its K-zero-support
    # eligibility to contain every core row, but leave its two points free.
    for row in CORE_BLOCKS:
        for source_point in range(N_U1):
            for core_point in CORE_BLOCKS[row]:
                if source_point != core_point:
                    solver.add(Not(And(
                        incidence[SOURCE, source_point],
                        k[edge_key(source_point, core_point)],
                    )))

    result = solver.check()
    print(f"{args.mode}: {result}")
    if args.expect is not None:
        assert str(result) == args.expect
    if result == sat:
        model = solver.model()
        source = [
            point for point in range(N_U1)
            if is_true(model.eval(
                incidence[SOURCE, point], model_completion=True
            ))
        ]
        print(f"source {SOURCE} block: {source}")
    elif result == unsat:
        print("the selected restored clauses exclude this common-source model")
    else:
        print(f"reason_unknown: {solver.reason_unknown()}")


if __name__ == "__main__":
    main()
