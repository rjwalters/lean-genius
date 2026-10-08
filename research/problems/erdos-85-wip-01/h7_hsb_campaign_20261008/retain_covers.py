#!/usr/bin/env python3
"""Produce the retained cover artefacts for all 28 structural cubes (codex, room 53116): exact cover
CNF bytes, exact binary LRAT proof bytes, metadata. Same function the campaign worker uses for cover
rows (cert_item.certify_cover_retained). Seconds per cube; about 1.2 GB in total.

    retain_covers.py --inputs DIR --out DIR [--slots 4] [--sample receipts/sample_results.jsonl]

With --sample, each proof sha256 is compared with the streamed proof of the cost sample.
Writes <out>/covers-retained.json (index) and exits 0 only if all 28 are verified.
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
    ap.add_argument("--slots", type=int, default=4)
    ap.add_argument("--cap", type=int, default=900)
    ap.add_argument("--heap-mb", type=int, default=2000)
    ap.add_argument("--cadical", default="cadical")
    ap.add_argument("--cake-lpr", default="cake_lpr")
    ap.add_argument("--sample", type=Path)
    a = ap.parse_args()
    bins = cert_item.tools(a.cadical, a.cake_lpr)
    streamed = {}
    if a.sample:
        for line in a.sample.read_text().splitlines():
            r = json.loads(line)
            if r["kind"] == "cover":
                streamed[r["cube"]] = r["proof"]["sha256"]

    def run(name: str) -> dict:
        rec = cert_item.certify_cover_retained(hc.Cube(a.inputs, name), a.out, bins, a.cap, a.heap_mb)
        row = {"cube": name, "status": rec["status"], "cnf_sha256": rec.get("cnf_sha256"), "cnf_bytes": rec.get("cnf_bytes"),
               "proof_sha256": rec.get("proof", {}).get("sha256"), "proof_bytes": rec.get("proof", {}).get("bytes"),
               "same_proof_as_streamed_sample": (streamed.get(name) == rec.get("proof", {}).get("sha256")) if streamed else None}
        print(json.dumps(row), flush=True)
        return row

    with cf.ThreadPoolExecutor(a.slots) as ex:
        rows = list(ex.map(run, hc.CUBES))
    ok = all(r["status"] == "CERTIFIED" for r in rows)
    index = {"schema": "erdos85-h7-hsb-retained-covers-index-v1", "depth": hc.DEPTH, "count": len(rows), "all_verified": ok,
             "binaries": {k: v["sha256"] for k, v in bins.items()}, "inputs_json_sha256": hc.sha_file(a.inputs / "inputs.json"),
             "total_cnf_bytes": sum(r["cnf_bytes"] or 0 for r in rows), "total_proof_bytes": sum(r["proof_bytes"] or 0 for r in rows),
             "covers": rows}
    (a.out / "covers-retained.json").write_text(json.dumps(index, indent=1, sort_keys=True) + "\n")
    print("RETAINED_COVERS_ALL_VERIFIED" if ok else "RETAINED_COVERS_INCOMPLETE", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
