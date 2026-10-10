#!/usr/bin/env python3
"""Measure the leaf split on the cloud builder (README section 9): generate the split of each named
leaf with split_leaf.py, then run the sub-cover and the sub-leaves through the campaign path
(cert_item: pinned CaDiCaL -> binary LRAT -> pinned cake_lpr; sub-leaves streamed, sub-covers retained),
one receipt line per item.

    split_measure.py --inputs ~/h7camp/inputs --leaf cube_F9_t0:1 --leaf cube_F8_t0:4 --depth 6 \\
        --slots 13 --cap 3600 --heap-mb 6000 --cadical ~/h7pilot/bin/cadical --cake-lpr ~/h7pilot/bin/cake_lpr \\
        --out ~/h7split/measure.jsonl --retain ~/h7split/retained [--deadline 25200] [--sample K]

Items are interleaved over the leaves (sub-cover of every leaf first, then sub-leaf 0 of every leaf,
sub-leaf 1, ...), so a run stopped by --deadline (no new item starts after it) is a balanced sample.
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import json
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import cert_item  # noqa: E402
import h7_common as hc  # noqa: E402
import split_leaf  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--inputs", type=Path, required=True)
    ap.add_argument("--leaf", action="append", required=True)
    ap.add_argument("--depth", type=int, default=6)
    ap.add_argument("--cubes", type=int, default=0, help="best-first split with this many cubes (0 = uniform depth)")
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--retain", type=Path, required=True)
    ap.add_argument("--cap", type=int, default=3600)
    ap.add_argument("--heap-mb", type=int, default=6000)
    ap.add_argument("--slots", type=int, default=13)
    ap.add_argument("--jobs", type=int, default=4, help="processes for the split generator")
    ap.add_argument("--deadline", type=int, default=0, help="seconds after start: no new item starts later")
    ap.add_argument("--sample", type=int, default=0, help="only every (subleaves/K)-th sub-leaf per leaf")
    ap.add_argument("--work", type=Path, default=Path("/dev/shm/h7split"))
    ap.add_argument("--cadical", default="cadical")
    ap.add_argument("--cake-lpr", default="cake_lpr")
    a = ap.parse_args()
    t_start = time.time()
    bins = cert_item.tools(a.cadical, a.cake_lpr)
    leaves = split_leaf.parse_leaves(argparse.Namespace(leaf=a.leaf, leaves_file=None))
    t0 = time.time()
    specs, rows = split_leaf.generate(a.inputs, leaves, a.depth, a.jobs, a.cubes)
    gen_s = time.time() - t0
    a.out.parent.mkdir(parents=True, exist_ok=True)
    specs_path = a.out.with_suffix(".specs.jsonl")
    specs_path.write_text("".join(json.dumps(s, sort_keys=True) + "\n" for s in specs))
    (a.out.with_suffix(".manifest.jsonl")).write_bytes(split_leaf.manifest_bytes(rows))
    print(json.dumps({"generated": len(specs), "rows": len(rows), "generator_seconds": round(gen_s, 1),
                      "subleaves": [s["subleaves"] for s in specs]}), flush=True)
    by_leaf: dict = {}
    for r in rows:
        by_leaf.setdefault((r["cube"], r["leaf"]), []).append(r)
    covers = [rs[0] for rs in by_leaf.values()]
    subs = [rs[1:] for rs in by_leaf.values()]
    if a.sample:
        subs = [[r for i, r in enumerate(rs) if i % max(1, len(rs) // a.sample) == 0][:a.sample] for rs in subs]
    order = covers + [rs[i] for i in range(max(len(rs) for rs in subs)) for rs in subs if i < len(rs)]
    cubes = {c: hc.Cube(a.inputs, c) for c in {r["cube"] for r in order}}
    lock = threading.Lock()

    def run(row: dict) -> None:
        if a.deadline and time.time() - t_start > a.deadline:
            return
        cube = cubes[row["cube"]]
        if row["kind"] == "subcover":
            rec = cert_item.certify_cover_retained(cube, a.retain, bins, a.cap, a.heap_mb, split=row)
        else:
            rec = cert_item.certify(cube, "subleaf", row["leaf"], a.work, bins, a.cap, a.heap_mb, split=row)
        rec["batch"] = row["id"]
        with lock, a.out.open("a") as f:
            f.write(json.dumps(rec, sort_keys=True) + "\n")
        print(row["id"], rec["status"], rec.get("solver", {}).get("cpu_seconds"), rec.get("checker", {}).get("cpu_seconds"),
              rec.get("proof", {}).get("bytes"), flush=True)

    with cf.ThreadPoolExecutor(a.slots) as ex:
        list(ex.map(run, order))
    print(json.dumps({"done": True, "wall_seconds": round(time.time() - t_start)}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
