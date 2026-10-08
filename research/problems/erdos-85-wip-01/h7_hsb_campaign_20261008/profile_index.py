#!/usr/bin/env python3
"""Solver time against leaf INDEX (head profile), exact campaign leaf format and binaries.

The cost sample drew 50 uniform leaves per cube; the canary showed that the lexicographically
first leaves are far harder than that sample suggests. This profiles geometric index strata:
for every k, the leaf at index 2^k (and index 0), plus one seeded random leaf of the stratum
[2^k, 2^(k+1)), per cube. Each leaf goes through cert_item.certify (CaDiCaL -> cake_lpr stream);
timeouts are recorded as data. Every receipt carries the leaf's position in the generator's
tree (leaf_tree.tree: first / second / third row index). Head leaves are scheduled first.

    profile_index.py --inputs DIR --out FILE --cubes cube_F7_t0,... --slots 14 --cap 7200
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import json
import random
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import cert_item  # noqa: E402
import h7_common as hc  # noqa: E402
import leaf_tree  # noqa: E402

SEED = 20261009


def plan(n: int, name: str) -> list[dict]:
    out = [{"leaf": 0, "stratum": [0, 1], "pick": "edge"}]
    k = 0
    while (1 << k) < n:
        lo, hi = 1 << k, min(n, 1 << (k + 1))
        out.append({"leaf": lo, "stratum": [lo, hi], "pick": "edge"})
        if hi - lo > 1:
            out.append({"leaf": random.Random(f"{SEED}:{name}:{k}").randrange(lo + 1, hi), "stratum": [lo, hi], "pick": "random"})
        k += 1
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inputs", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--cubes", required=True)
    ap.add_argument("--slots", type=int, default=14)
    ap.add_argument("--cap", type=int, default=7200)
    ap.add_argument("--heap-mb", type=int, default=2000)
    ap.add_argument("--work", type=Path, default=Path("/dev/shm/h7camp-profile"))
    ap.add_argument("--cadical", default="cadical")
    ap.add_argument("--cake-lpr", default="cake_lpr")
    ap.add_argument("--print-plan", action="store_true")
    a = ap.parse_args()
    meta = json.loads((a.inputs / "inputs.json").read_text())
    names = a.cubes.split(",")
    assert all(c in hc.CUBES for c in names)
    items = []
    for name in names:
        for p in plan(meta["cubes"][name]["leaves"], name):
            items.append(dict(p, cube=name))
    items.sort(key=lambda p: (p["leaf"], names.index(p["cube"])))  # head first, round-robin over cubes
    if a.print_plan:
        print(json.dumps({"items": len(items), "per_cube": {c: [p["leaf"] for p in items if p["cube"] == c] for c in names}}))
        return 0
    done = set()
    if a.out.exists():
        for line in a.out.read_text().splitlines():
            r = json.loads(line)
            done.add((r["cube"], r["leaf"]))
    items = [p for p in items if (p["cube"], p["leaf"]) not in done]
    bins = cert_item.tools(a.cadical, a.cake_lpr)
    cubes, trees, lock, out_lock = {}, {}, threading.Lock(), threading.Lock()
    print(f"profile: {len(items)} leaves, slots={a.slots}, cap={a.cap}s", flush=True)

    def run(p) -> None:
        name = p["cube"]
        with lock:
            if name not in cubes:
                cubes[name] = hc.Cube(a.inputs, name)
                trees[name] = leaf_tree.tree(a.inputs, name)
        rec = cert_item.certify(cubes[name], "leaf", p["leaf"], a.work, bins, a.cap, a.heap_mb)
        rec.update(stratum=p["stratum"], pick=p["pick"], tree=trees[name][p["leaf"]], seed=SEED)
        rec.pop("logs", None)
        with out_lock:
            with a.out.open("a") as f:
                f.write(json.dumps(rec, sort_keys=True) + "\n")
            s = rec.get("solver", {})
            print(f"{time.strftime('%H:%M:%S', time.gmtime())} {name} leaf {p['leaf']} {rec['status']} "
                  f"solve={s.get('cpu_seconds', 0):.0f}s conf={s.get('conflicts')} tree={rec['tree']}", flush=True)

    with cf.ThreadPoolExecutor(a.slots) as ex:
        list(ex.map(run, items))
    print("profile: finished", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
