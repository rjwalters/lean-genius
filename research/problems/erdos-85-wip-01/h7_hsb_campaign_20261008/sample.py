#!/usr/bin/env python3
"""Cost sample for the H7 t=0 hsb3 campaign: the 28 cover CNFs plus K random leaves per cube,
each run through the exact campaign path (cert_item.certify: positive-unit leaf CNF, CaDiCaL
binary LRAT streamed into cake_lpr). Fixed seed; leaves are scheduled round-robin over the cubes
so an early stop still leaves a balanced sample. Appends one receipt per line; resumable.

    sample.py --inputs DIR --out results.jsonl --per-cube 40 --slots 7 --cap 3600 \
              [--stop-launch-at EPOCH] [--no-covers]
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

SEED = 20261008


def picks(meta: dict, per_cube: int, seed: int = SEED) -> dict[str, list[int]]:
    out = {}
    for name in hc.CUBES:
        n = meta["cubes"][name]["leaves"]
        out[name] = random.Random(f"{seed}:{name}").sample(range(n), min(per_cube, n))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inputs", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--per-cube", type=int, default=40)
    ap.add_argument("--seed", type=int, default=SEED)
    ap.add_argument("--slots", type=int, default=7)
    ap.add_argument("--cap", type=int, default=3600)
    ap.add_argument("--heap-mb", type=int, default=2000)
    ap.add_argument("--work", type=Path, default=Path("/dev/shm/h7camp-sample"))
    ap.add_argument("--cadical", default="cadical")
    ap.add_argument("--cake-lpr", default="cake_lpr")
    ap.add_argument("--stop-launch-at", type=float, default=0, help="epoch seconds: start no new item after this")
    ap.add_argument("--no-covers", action="store_true")
    ap.add_argument("--cubes", default="", help="comma list (default all 28)")
    args = ap.parse_args()
    meta = json.loads((args.inputs / "inputs.json").read_text())
    bins = cert_item.tools(args.cadical, args.cake_lpr)
    names = [c for c in hc.CUBES if not args.cubes or c in args.cubes.split(",")]
    chosen = picks(meta, args.per_cube, args.seed)
    done = set()
    if args.out.exists():
        for line in args.out.read_text().splitlines():
            r = json.loads(line)
            done.add((r["cube"], r["kind"], r["leaf"]))
    items = [] if args.no_covers else [(c, "cover", None) for c in names]
    for j in range(args.per_cube):
        items += [(c, "leaf", chosen[c][j]) for c in names if j < len(chosen[c])]
    items = [it for it in items if it not in done]
    cubes: dict[str, hc.Cube] = {}
    load_lock, out_lock = threading.Lock(), threading.Lock()
    args.work.mkdir(parents=True, exist_ok=True)
    print(f"sample: {len(items)} items to run ({len(done)} already done), slots={args.slots} cap={args.cap}s "
          f"heap={args.heap_mb}MB seed={args.seed} bins={ {k: v['sha256'][:12] for k, v in bins.items()} }", flush=True)

    def run(item) -> None:
        name, kind, leaf = item
        if args.stop_launch_at and time.time() > args.stop_launch_at:
            return
        with load_lock:
            if name not in cubes:
                cubes[name] = hc.Cube(args.inputs, name)
        heap = args.heap_mb
        rec = cert_item.certify(cubes[name], kind, leaf, args.work, bins, args.cap, heap)
        if rec["status"] == "CHECK_HEAP_EXHAUSTED":
            first = {k: rec.get(k) for k in ("status", "solver", "checker", "proof")}
            rec = cert_item.certify(cubes[name], kind, leaf, args.work, bins, args.cap, heap * 4)
            rec["heap_retry_of"] = first
        rec["seed"], rec["sample_index"] = args.seed, (None if leaf is None else chosen[name].index(leaf))
        with out_lock:
            with args.out.open("a") as f:
                f.write(json.dumps(rec, sort_keys=True) + "\n")
            s, c, p = rec.get("solver", {}), rec.get("checker", {}), rec.get("proof", {})
            print(f"{time.strftime('%H:%M:%S', time.gmtime())} {name} {kind}{'' if leaf is None else leaf} "
                  f"{rec['status']} solve={s.get('cpu_seconds', 0):.1f}s conf={s.get('conflicts')} "
                  f"check={c.get('cpu_seconds', 0):.1f}s proof={p.get('bytes')}", flush=True)

    with cf.ThreadPoolExecutor(args.slots) as ex:
        list(ex.map(run, items))
    print("sample: finished", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
