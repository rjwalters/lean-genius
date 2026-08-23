#!/usr/bin/env python3
"""Audit packing-choice incompatibility multiplicities for branch 4."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from q9_b0_residual_defect_sat import N
from q9_symmetric_point_mass_obstruction import fixed_system, local_packing_family


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("payload", type=Path)
    args = parser.parse_args()
    system = fixed_system(json.loads(args.payload.read_text()))
    families = {u: local_packing_family(system, u) for u in range(N)}
    worst = None
    for u in range(N):
        for v in range(N):
            if u == v or not families[u] or not families[v]:
                continue
            conflict = bool(system["blocks"][u] & system["blocks"][v])
            for choice, first in enumerate(families[u]):
                killed = 0
                for second in families[v]:
                    compatible = (
                        ((v in first) == (u in second))
                        and (not conflict or first.isdisjoint(second))
                    )
                    killed += int(not compatible)
                record = {
                    "fixed_row": u,
                    "target_row": v,
                    "fixed_choice": choice,
                    "target_packing_count": len(families[v]),
                    "blocks_conflict": conflict,
                    "killed_target_packings": killed,
                }
                if worst is None or killed > worst["killed_target_packings"]:
                    worst = record
    print(json.dumps({
        "maximum_kill": worst,
        "kill_at_most_one": (
            worst is None or worst["killed_target_packings"] <= 1
        ),
    }, separators=(",", ":")))


if __name__ == "__main__":
    main()
