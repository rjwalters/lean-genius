#!/usr/bin/env python3
"""Position of every hsb3 leaf in the generator's tree, from the pinned inputs only.

A leaf is (row of empty 7, row of empty 8, row of empty 9); the generator emits leaves in
lexicographic order of (canonical first row, canonical second row, canonical third row), each
level sorted by row_key. Row j has 7 - deg_E(7 + j) literals, so the cover line splits by the mask.

    tree(inputs_dir, cube) -> list of dicts per leaf: i1, i2, i3 (0-based index of the row among its
    siblings), n2 (second rows under this first row), n3 (third rows under this (first, second))
"""
from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import h7_common as hc  # noqa: E402

PAIRS = list(itertools.combinations(range(7), 2))


def row_sizes(mask: int) -> list[int]:
    deg = [0] * 7
    for idx, (l, r) in enumerate(PAIRS):
        if mask >> idx & 1:
            deg[l] += 1
            deg[r] += 1
    return [7 - deg[j] for j in range(hc.DEPTH)]


def tree(inputs: Path, name: str) -> list[dict]:
    meta = json.loads((inputs / "inputs.json").read_text())["cubes"][name]
    sizes = row_sizes(meta["mask"])
    assert sum(sizes) == meta["leaf_units"], (name, sizes, meta["leaf_units"])
    out, i1, i2, i3, prev = [], -1, -1, -1, (None, None)
    for line in (inputs / f"{name}.cover").read_bytes().splitlines():
        u = hc.units_of_cover_line(line)
        r1, r2 = tuple(u[:sizes[0]]), tuple(u[sizes[0]:sizes[0] + sizes[1]])
        if r1 != prev[0]:
            i1, i2, i3 = i1 + 1, 0, 0
        elif r2 != prev[1]:
            i2, i3 = i2 + 1, 0
        else:
            i3 += 1
        prev = (r1, r2)
        out.append({"i1": i1, "i2": i2, "i3": i3})
    n2, n3 = {}, {}
    for t in out:
        n2[t["i1"]] = max(n2.get(t["i1"], 0), t["i2"] + 1)
        n3[(t["i1"], t["i2"])] = max(n3.get((t["i1"], t["i2"]), 0), t["i3"] + 1)
    for t in out:
        t["n2"], t["n3"] = n2[t["i1"]], n3[(t["i1"], t["i2"])]
    return out


if __name__ == "__main__":
    inputs = Path(sys.argv[1])
    for name in hc.CUBES:
        t = tree(inputs, name)
        firsts = max(x["i1"] for x in t) + 1
        per_first = [sum(1 for x in t if x["i1"] == k) for k in range(firsts)]
        print(json.dumps({"cube": name, "leaves": len(t), "row_sizes": row_sizes(json.loads((inputs / "inputs.json").read_text())["cubes"][name]["mask"]),
                          "first_rows": firsts, "leaves_per_first_row": per_first[:12], "second_rows_under_first0": t[0]["n2"],
                          "third_rows_under_first0_second0": t[0]["n3"]}))
