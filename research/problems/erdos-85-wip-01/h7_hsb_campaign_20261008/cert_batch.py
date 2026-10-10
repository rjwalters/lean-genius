#!/usr/bin/env python3
"""Certify one claim unit (a batch of leaves of one cube, one cover CNF, or one split sub-leaf / sub-cover). One process per
batch: the cube's pinned bytes (cube ++ hsb, ~10 MB) are loaded and verified once and reused for
every leaf, so the per-leaf cost is one file write + one solver parse + one checker parse.

Every leaf still gets its own CNF, its own LRAT proof and its own cake_lpr verdict: the Lean
evidence `SevenHighT0CanonicalHsbEvidence` wants one checked CNF per leaf.

Appends one receipt per item to --out (fsync after each). Items already CERTIFIED in --carry
(partial receipts of an interrupted earlier attempt) are re-validated against the pinned inputs
and copied, not re-run. A --stop-file is honoured between items.

The checker heap is fixed for the whole batch. CHECK_HEAP_EXHAUSTED is recorded like a solver
timeout (not an alarm, not retried here): the node's memory budget is slots x (heap + 1.5 GB), so an
in-batch heap escalation would overcommit it. Such items go to the residual pass, which runs with a
larger heap and correspondingly fewer slots. The proof is streamed and not kept, so a re-check
without re-solving is not possible; the leaf is never re-solved at the same heap inside a pass
(only CERTIFIED receipts are carried forward when a reclaimed batch is re-claimed).
Exit: 0 all items CERTIFIED, 3 alarm (CHECK_FAILED / SOLVER_SAT), 4 stopped, 1 otherwise.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import cert_item  # noqa: E402
import h7_common as hc  # noqa: E402

def items_of(row: dict) -> list:
    if row["kind"] == "cover":
        return [None]
    if row["kind"] in ("subleaf", "subcover"):  # one split item per row; the item key is the leaf index
        return [row["leaf"]]
    return list(row["leaves"]) if "leaves" in row else list(range(row["start"], row["end"]))


def expected_sha(cube: hc.Cube, row: dict, kind: str, leaf) -> str | None:
    """The CNF sha256 an item of this row must have, recomputed from the pinned inputs (None: invalid)."""
    try:
        if kind == "cover":
            return cube.meta["cover_cnf_sha256"]
        if not (isinstance(leaf, int) and 0 <= leaf < cube.n_leaves):
            return None
        if kind == "leaf":
            return cube.leaf_sha256(leaf)
        if kind == "subleaf":
            return cube.subleaf_sha256(leaf, row["clause"])
        if kind == "subcover":
            return cube.subcover_sha256(leaf, row["clauses"])
    except (KeyError, ValueError):
        return None
    return None


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--inputs", type=Path, required=True)
    p.add_argument("--batch", required=True, help="the manifest row as JSON")
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--work", type=Path, default=Path("/dev/shm/h7camp"))
    p.add_argument("--cap", type=int, default=7200)
    p.add_argument("--heap-mb", type=int, default=6000)
    p.add_argument("--cadical", default="cadical")
    p.add_argument("--cake-lpr", default="cake_lpr")
    p.add_argument("--carry", type=Path)
    p.add_argument("--stop-file", type=Path)
    p.add_argument("--retain-covers", type=Path, help="cover and subcover rows: keep exact CNF + LRAT proof bytes here (never used for leaves or subleaves)")
    p.add_argument("--allow-unpinned-binaries", action="store_true", help="tests only (fake checker)")
    a = p.parse_args()
    row = json.loads(a.batch)
    bins = cert_item.tools(a.cadical, a.cake_lpr, a.allow_unpinned_binaries)
    want_bins = {k: v["sha256"] for k, v in bins.items()}
    cube = hc.Cube(a.inputs, row["cube"])  # verifies every pinned hash of this cube
    kind = {"cover": "cover", "subleaf": "subleaf", "subcover": "subcover"}.get(row["kind"], "leaf")
    split = row if kind in ("subleaf", "subcover") else None
    carried = {}
    if a.carry and a.carry.is_file():
        for line in a.carry.read_text().splitlines():
            try:
                r = json.loads(line)
            except ValueError:
                continue  # a torn last line of a partial upload
            want = expected_sha(cube, row, kind, r.get("leaf"))
            if (r.get("status") == "CERTIFIED" and r.get("cube") == cube.name and r.get("kind") == kind
                    and want is not None and r.get("cnf_sha256") == want and r.get("binaries") == want_bins
                    and (split is None or r.get("split_sha256") == split["split_sha256"])
                    and r.get("checker", {}).get("verified_line") is True):
                carried[r["leaf"]] = r
    a.work.mkdir(parents=True, exist_ok=True)
    worst = 0
    with a.out.open("a") as out:
        for leaf in items_of(row):
            if a.stop_file and a.stop_file.exists():
                return 4
            retained = kind in ("cover", "subcover") and a.retain_covers
            if leaf in carried and not retained:  # a retained (sub-)cover is always re-run
                rec = dict(carried[leaf], carried=True)
            else:
                if retained:
                    rec = cert_item.certify_cover_retained(cube, a.retain_covers, bins, a.cap, a.heap_mb, split=split)
                elif kind == "subcover":
                    raise SystemExit("a subcover row needs --retain-covers")
                else:
                    extra = {"split": split} if split else {}  # leaf and cover calls are unchanged
                    rec = cert_item.certify(cube, kind, leaf, a.work, bins, a.cap, a.heap_mb, **extra)
            rec["batch"] = row["id"]
            out.write(json.dumps(rec, sort_keys=True) + "\n")
            out.flush()
            os.fsync(out.fileno())
            if rec["status"] in cert_item.ALARM:
                return 3
            if rec["status"] != "CERTIFIED":
                worst = 1
    return worst


if __name__ == "__main__":
    raise SystemExit(main())
