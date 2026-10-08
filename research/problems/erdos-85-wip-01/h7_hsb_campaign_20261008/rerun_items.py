#!/usr/bin/env python3
"""Run named leaves through the campaign path with a chosen cap and heap (follow-up of capped
sample leaves; also usable for a handful of residual leaves on the builder).

    rerun_items.py --inputs DIR --out FILE --items cube_F7_t0:2061,cube_F7_t6:119 --cap 7200 --heap-mb 4000
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import cert_item  # noqa: E402
import h7_common as hc  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inputs", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--items", required=True)
    ap.add_argument("--cap", type=int, default=7200)
    ap.add_argument("--heap-mb", type=int, default=4000)
    ap.add_argument("--slots", type=int, default=2)
    ap.add_argument("--work", type=Path, default=Path("/dev/shm/h7camp-rerun"))
    ap.add_argument("--cadical", default="cadical")
    ap.add_argument("--cake-lpr", default="cake_lpr")
    a = ap.parse_args()
    bins = cert_item.tools(a.cadical, a.cake_lpr)
    items = [(c, int(n)) for c, n in (x.split(":") for x in a.items.split(","))]

    def run(item):
        name, leaf = item
        rec = cert_item.certify(hc.Cube(a.inputs, name), "leaf", leaf, a.work, bins, a.cap, a.heap_mb)
        with a.out.open("a") as f:
            f.write(json.dumps(rec, sort_keys=True) + "\n")
        print(name, leaf, rec["status"], rec.get("solver", {}).get("cpu_seconds"), rec.get("checker", {}).get("cpu_seconds"),
              rec.get("proof", {}).get("bytes"), flush=True)

    with cf.ThreadPoolExecutor(a.slots) as ex:
        list(ex.map(run, items))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
