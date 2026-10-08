#!/usr/bin/env python3
"""Certify ONE campaign CNF (a leaf or a cover) of a structural H7/T0 cube, check-then-discard.

1. Write the CNF from the pinned in-memory cube (h7_common.Cube), hash the file that the solver
   and the checker will read, and require sha256 == the expected value.
2. CaDiCaL (binary LRAT) -> FIFO -> hashing relay -> FIFO -> cake_lpr; the proof is never stored.
   This step is the reviewed H1 code (../h1_cert_full_20261001/cert_row.py: solve_and_check),
   imported unchanged, including its waitid(WNOWAIT) watchdog.
3. CERTIFIED requires CaDiCaL exit 20 + `s UNSATISFIABLE` AND the cake_lpr stdout line
   `s VERIFIED UNSAT`. cake_lpr exits 0 even when a check fails; its exit code is ignored.

Statuses: CERTIFIED, CNF_MISMATCH, SOLVER_TIMEOUT (cap reached), SOLVER_SAT (alarm),
SOLVER_NOT_UNSAT, CHECK_HEAP_EXHAUSTED (retry with a larger heap), CHECK_FAILED (alarm), ERROR.
"""
from __future__ import annotations

import argparse
import os
import platform
import re
import shutil
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "h1_cert_full_20261001"))
import cert_row as h1  # noqa: E402  (reviewed H1 per-row certifier)
import h7_common as hc  # noqa: E402

ALARM = ("CHECK_FAILED", "SOLVER_SAT")
_STAT = re.compile(rb"^c (conflicts|decisions|propagations):\s+(\d+)", re.M)
_PARSE = re.compile(rb"^c\s+([0-9.]+)\s+[0-9.]+%\s+parse\s*$", re.M)
_TOTAL = re.compile(rb"^c total process time since initialization:\s+([0-9.]+)", re.M)


def tools(cadical: str, cake_lpr: str, allow_unpinned: bool = False) -> dict:
    """Resolve and hash the two binaries. Unless allow_unpinned (tests only), both must be the
    approved builds: a receipt made with any other solver or checker is worthless to the collector."""
    out = {}
    for k, v in (("cadical", cadical), ("cake_lpr", cake_lpr)):
        p = shutil.which(v) or v
        out[k] = {"path": str(p), "sha256": hc.sha_file(Path(p))}
        if not allow_unpinned and out[k]["sha256"] != hc.PINNED_BINARIES[k]:
            raise SystemExit(f"{k} at {p} has sha256 {out[k]['sha256']}, not the approved {hc.PINNED_BINARIES[k]}")
    return out


def certify(cube: hc.Cube, kind: str, leaf: int | None, work_root: Path, bins: dict, cap: int, heap_mb: int,
            keep_logs: bool = False) -> dict:
    """kind = 'leaf' (leaf index required) or 'cover'. Returns the receipt (never raises)."""
    ident = f"{cube.name}.{kind}{'' if leaf is None else leaf}"
    # Unique per attempt (H1 lesson: a duplicate claim must never touch a live attempt's directory).
    work = work_root / f"{ident}.{os.getpid()}.{time.time_ns()}"
    rec: dict = {"schema": "erdos85-h7-hsb-cert-v1", "cube": cube.name, "kind": kind, "leaf": leaf,
                 "depth": hc.DEPTH, "started_utc": h1.now(), "host": platform.node(), "cap_seconds": cap,
                 "binaries": {k: v["sha256"] for k, v in bins.items()}}
    try:
        work.mkdir(parents=True)
        cnf = work / "input.cnf"
        t0 = time.time()
        if kind == "leaf":
            rec["units"] = cube.units(leaf)
            rec["expected_cnf_sha256"] = cube.leaf_sha256(leaf)
            cube.write_leaf(leaf, cnf)
        elif kind == "cover":
            rec["expected_cnf_sha256"] = cube.meta["cover_cnf_sha256"]
            cube.write_cover(cnf)
        else:
            raise ValueError(kind)
        rec["cnf_sha256"] = hc.sha_file(cnf)
        rec["cnf_bytes"] = cnf.stat().st_size
        rec["write_seconds"] = round(time.time() - t0, 3)
        if rec["cnf_sha256"] != rec["expected_cnf_sha256"]:
            rec["status"] = "CNF_MISMATCH"
        else:
            a = argparse.Namespace(cadical=bins["cadical"]["path"], cake_lpr=bins["cake_lpr"]["path"], cap=cap,
                                   heap_mb=heap_mb)
            h1.solve_and_check(a, work, cnf, rec)
            slog = (work / "cadical.log").read_bytes()
            for m in _STAT.finditer(slog):
                rec["solver"][m.group(1).decode()] = int(m.group(2))
            for key, rx in (("parse_seconds", _PARSE), ("process_seconds", _TOTAL)):
                m = rx.search(slog)
                if m:
                    rec["solver"][key] = float(m.group(1))
            rec["solver"].pop("command", None)
            rc = rec["solver"]["returncode"]
            if rec["status"] == "SOLVER_NOT_UNSAT":
                rec["status"] = "SOLVER_SAT" if rc == 10 else "SOLVER_TIMEOUT" if rc == 0 else "SOLVER_NOT_UNSAT"
    except Exception as e:  # noqa: BLE001
        rec["status"], rec["error"] = "ERROR", f"{type(e).__name__}: {e}"
    rec["finished_utc"] = h1.now()
    if keep_logs or rec["status"] != "CERTIFIED":
        rec["logs"] = {}
        for name in ("cadical.log", "cake_lpr.log"):
            p = work / name
            if p.is_file():
                rec["logs"][name] = p.read_text(errors="replace")[-4000:]
    shutil.rmtree(work, ignore_errors=True)
    return rec
