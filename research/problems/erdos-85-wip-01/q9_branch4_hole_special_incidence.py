#!/usr/bin/env python3
"""Branch-4 hole points cannot all hit both punctured special classes.

The branch-4 normalized B0--U1 design has regular special-class row ranges
8..14 and 15..21 and exceptional hole rows 22..25.  This probe negates the
claim by requiring every point of every hole block to occur in a regular row
of both punctured classes.  The base design equations alone make that
negation UNSAT; all residual, DTB, row-ledger, and marked-miss families are
relaxed.

Consequently some hole point p has ``special(p) > 0``.  The projected column
law then gives full-fiber residual degree target ``D_p = 27 + special(p) >=
28``.  The script is a finite computational proof model, not yet a uniform
Lean derivation of the incidence lemma.
"""

from __future__ import annotations

import argparse
import time

from z3 import Implies, Or, sat, unknown

from q9_b0_residual_defect_sat import N_U1, build


RELAX = {
    "row-ledger", "residual-c4", "b0-c4", "dtb-common", "dtb-cap",
    "dtb-zero", "dtb-rows", "dtb-columns", "marked-miss",
}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout-seconds", type=int, default=60)
    args = parser.parse_args()

    solver, data = build(
        4, args.timeout_seconds * 1000, True, relax=RELAX
    )
    incidence = data["incidence"]
    regular_punctured_classes = (range(8, 15), range(15, 22))
    for hole in range(22, 26):
        for point in range(N_U1):
            for centers in regular_punctured_classes:
                solver.add(Implies(
                    incidence[hole, point],
                    Or([incidence[row, point] for row in centers]),
                ))

    started = time.monotonic()
    result = solver.check()
    print(f"result={result} elapsed={time.monotonic() - started:.3f}")
    if result == unknown:
        print("reason_unknown=" + solver.reason_unknown())
        return 2
    if result == sat:
        print("all_branch4_hole_points_special_zero=SAT_COUNTEREXAMPLE")
        return 1
    print("some_branch4_hole_point_special_positive=UNSAT_NEGATION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
