#!/usr/bin/env python3
"""Bounded Kissat verdicts and CaDiCaL cross-checks; never request proofs.

Without --execute this validates inventory metadata and reports input availability.
Execution requires an unchanged, committed inventory and its not_before time.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import concurrent.futures
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import sys
import threading
import time

HEX = re.compile(r"[0-9a-f]{64}")
COMMIT = re.compile(r"[0-9a-f]{40}")
ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,159}")
LOG_LIMIT = 4 * 1024 * 1024
ABORT = threading.Event()


@contextmanager
def cancellation_handlers():
    ABORT.clear()
    old = {sig: signal.getsignal(sig) for sig in (signal.SIGINT, signal.SIGTERM)}
    try:
        for sig in old:
            signal.signal(sig, lambda _sig, _frame: ABORT.set())
        yield
    finally:
        for sig, handler in old.items():
            signal.signal(sig, handler)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def write_json(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def load_inventory(path: Path, raw: bytes | None = None) -> dict:
    data = json.loads(path.read_bytes() if raw is None else raw)
    if data.get("schema") != "erdos85-verdict-v1":
        raise ValueError("Expected erdos85-verdict-v1 inventory")
    start = dt.datetime.fromisoformat(data["not_before"].replace("Z", "+00:00"))
    if start.tzinfo is None:
        raise ValueError("not_before must include a timezone")
    seen = set()
    cases = data["cases"]
    if not cases:
        raise ValueError("Empty inventories cannot establish coverage")
    for case in cases:
        name = case["id"]
        if not ID.fullmatch(name) or name in seen:
            raise ValueError(f"Invalid or duplicate case id: {name}")
        seen.add(name)
        if case["sector"] not in {"H1", "H3", "H5", "H7"}:
            raise ValueError(f"Invalid sector: {name}")
        if not HEX.fullmatch(case["cnf_sha256"]):
            raise ValueError(f"Invalid CNF hash: {name}")
        if not COMMIT.fullmatch(case["generator_commit"]):
            raise ValueError(f"Invalid generator commit: {name}")
        if type(case["crosscheck"]) is not bool:
            raise ValueError(f"crosscheck must be Boolean: {name}")
        if case["sector"] != "H1" and not case["crosscheck"]:
            raise ValueError(f"Hard-sector UNSAT requires cross-check: {name}")
        for field in ("primary_cap_seconds", "crosscheck_cap_seconds"):
            if type(case[field]) is not int or not 1 <= case[field] <= 86400:
                raise ValueError(f"Invalid {field}: {name}")
        cnf = Path(case["cnf"])
        case["resolved_cnf"] = str((path.parent / cnf).resolve())
    return data


def require_banked_inventory(path: Path, commit: str, *, expected_bytes: bytes | None = None) -> None:
    expected = path.read_bytes() if expected_bytes is None else expected_bytes
    if not COMMIT.fullmatch(commit):
        raise ValueError("An exact 40-character inventory commit is required")
    root = Path(subprocess.check_output(
        ["git", "-C", str(path.parent), "rev-parse", "--show-toplevel"], text=True).strip())
    relative = path.resolve().relative_to(root.resolve()).as_posix()
    subprocess.run(["git", "-C", str(root), "merge-base", "--is-ancestor", commit, "HEAD"],
                   check=True, capture_output=True)
    subprocess.run(["git", "-C", str(root), "merge-base", "--is-ancestor", commit,
                    "refs/remotes/origin/erdos85/integration"], check=True, capture_output=True)
    banked = subprocess.check_output(["git", "-C", str(root), "show", f"{commit}:{relative}"])
    if banked != expected:
        raise ValueError("Working inventory differs from its committed bytes")
    if path.read_bytes() != expected:
        raise ValueError("Inventory changed after its snapshot was read")


def classify(returncode: int | None, log: bytes, stop_reason: str | None) -> str:
    if stop_reason:
        return "UNKNOWN"
    statuses = {line.strip() for line in log.splitlines() if line.startswith(b"s ")}
    if returncode == 20 and statuses == {b"s UNSATISFIABLE"}:
        return "UNSAT"
    if returncode == 10 and statuses == {b"s SATISFIABLE"}:
        return "SAT_CANDIDATE"
    if returncode == 0 and statuses <= {b"s UNKNOWN"}:
        return "UNKNOWN"
    return "ERROR"


def solver_identity(binary: Path) -> dict:
    version = subprocess.run([str(binary), "--version"], capture_output=True,
                             text=True, timeout=10, check=True)
    return {"path": str(binary), "sha256": sha256(binary),
            "version": version.stdout.strip()}


def run_solver(binary: Path, cnf: Path, cap: int, log_path: Path, *, kind: str | None = None) -> dict:
    # Native limits bound orphans even if the harness receives uncatchable SIGKILL.
    options = [f"--time={cap}"] if kind == "kissat" else ["-t", str(cap)] if kind == "cadical" else []
    command = [str(binary), *options, str(cnf)]  # One input; no proof filename.
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("CADICAL_", "KISSAT_"))}
    started = time.monotonic()
    binary_hash = sha256(binary)
    overflow = threading.Event()
    reader_errors = []
    with log_path.open("xb") as output:
        if ABORT.is_set():
            return {"command": command, "solver_sha256": binary_hash, "returncode": None,
                    "elapsed_seconds": 0, "stop_reason": "aborted", "verdict": "UNKNOWN",
                    "log_sha256": hashlib.sha256(b"").hexdigest(), "log_bytes": 0,
                    "proof_requested": False}
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   env=env, start_new_session=True)

        def drain() -> None:
            remaining = LOG_LIMIT
            assert process.stdout is not None
            try:
                for chunk in iter(lambda: process.stdout.read(65536), b""):
                    output.write(chunk[:remaining])
                    if len(chunk) > remaining:
                        overflow.set()
                    remaining = max(0, remaining - len(chunk))
            except Exception as error:
                reader_errors.append(str(error))
                overflow.set()
            finally:
                process.stdout.close()

        reader = threading.Thread(target=drain, daemon=True)
        reader.start()
        stop_reason = None
        try:
            while process.poll() is None:
                if ABORT.is_set():
                    stop_reason = "aborted"
                    break
                if overflow.is_set():
                    stop_reason = "log_limit"
                    break
                if time.monotonic() - started >= cap:
                    stop_reason = "wall_time_limit"
                    break
                time.sleep(0.05)
        finally:
            # Also terminate a spawned child holding stdout after its parent exits.
            if process.poll() is None or reader.is_alive():
                try:
                    os.killpg(process.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                reader.join(timeout=2)
                if reader.is_alive():
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    reader.join(timeout=2)
                if reader.is_alive():
                    raise RuntimeError("Solver descendants still hold output pipe")
        reader.join()
    if overflow.is_set():
        stop_reason = "log_limit"
    if reader_errors:
        stop_reason = "log_write_error"
    if sha256(binary) != binary_hash:
        stop_reason = "solver_binary_changed"
    log = log_path.read_bytes()
    return {"command": command, "solver_sha256": binary_hash, "returncode": process.returncode,
            "elapsed_seconds": time.monotonic() - started, "stop_reason": stop_reason,
            "verdict": classify(process.returncode, log, stop_reason),
            "log_sha256": sha256(log_path), "log_bytes": len(log), "proof_requested": False}


def run_case(case: dict, output: Path, kissat: Path, cadical: Path) -> dict:
    directory = output / case["id"]
    directory.mkdir()
    cnf = Path(case["resolved_cnf"])
    result = {"id": case["id"], "sector": case["sector"], "status": "ERROR",
              "cnf_sha256": case["cnf_sha256"], "generator_commit": case["generator_commit"]}
    try:
        if sha256(cnf) != case["cnf_sha256"]:
            raise ValueError("CNF hash mismatch before launch")
        primary = run_solver(kissat, cnf, case["primary_cap_seconds"], directory / "kissat.log", kind="kissat")
        result["primary"] = primary
        write_json(directory / "result.json", result)
        if sha256(cnf) != case["cnf_sha256"]:
            raise ValueError("CNF changed during primary solve")
        if primary["verdict"] == "UNSAT" and case["crosscheck"]:
            secondary = run_solver(cadical, cnf, case["crosscheck_cap_seconds"],
                                   directory / "cadical.log", kind="cadical")
            result["crosscheck"] = secondary
            result["status"] = {"UNSAT": "UNSAT_CROSSCHECKED", "UNKNOWN": "UNKNOWN",
                                "SAT_CANDIDATE": "DISAGREEMENT", "ERROR": "ERROR"}[secondary["verdict"]]
        else:
            result["status"] = "UNSAT_PRIMARY" if primary["verdict"] == "UNSAT" else primary["verdict"]
        if sha256(cnf) != case["cnf_sha256"]:
            raise ValueError("CNF changed during cross-check")
    except Exception as error:
        result.update(status="ERROR", error=f"{type(error).__name__}: {error}")
    write_json(directory / "result.json", result)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--inventory-commit")
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--case-id", action="append", help="Select an explicit pilot subset; repeat per ID")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--workers", type=int, choices=range(1, 5), default=4)
    parser.add_argument("--kissat", type=Path, default=Path("/opt/homebrew/bin/kissat"))
    parser.add_argument("--cadical", type=Path, default=Path("/opt/homebrew/bin/cadical"))
    args = parser.parse_args()
    inventory_path = args.inventory.resolve()
    inventory_raw = inventory_path.read_bytes()
    inventory = load_inventory(inventory_path, inventory_raw)
    cases = inventory["cases"]
    inventory_total = len(cases)
    if args.case_id:
        selected = set(args.case_id)
        if len(selected) != len(args.case_id) or not selected <= {c["id"] for c in cases}:
            parser.error("--case-id contains a duplicate or unknown case")
        cases = [c for c in cases if c["id"] in selected]
    if not args.execute:
        print(json.dumps({"mode": "dry_run", "cases": len(cases), "inventory_cases": inventory_total, "workers": args.workers,
                          "not_before": inventory["not_before"],
                          "missing_inputs": [c["id"] for c in cases if not Path(c["resolved_cnf"]).is_file()]}))
        return 0
    if not args.inventory_commit or not args.output_dir:
        parser.error("Execution requires --inventory-commit and --output-dir")
    require_banked_inventory(inventory_path, args.inventory_commit, expected_bytes=inventory_raw)
    start = dt.datetime.fromisoformat(inventory["not_before"].replace("Z", "+00:00"))
    if dt.datetime.now(dt.timezone.utc) < start:
        parser.error("Inventory execution window has not started")
    output = args.output_dir.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    # Reserve room for other agents. No solver run while the host is nearly full.
    if shutil.disk_usage(output.parent).free < 8 * 1024**3:
        parser.error("Fewer than 8 GiB free on output volume")
    output.mkdir()  # Every invocation is new; never silently rerun retained cases.
    (output / "inventory.snapshot.json").write_bytes(inventory_raw)
    identities = {"kissat": solver_identity(args.kissat.resolve()),
                  "cadical": solver_identity(args.cadical.resolve())}
    results = []
    stopped = False
    state = {"inventory_sha256": hashlib.sha256(inventory_raw).hexdigest(), "inventory_commit": args.inventory_commit,
             "solvers": identities, "workers": args.workers, "proof_logging": False,
             "inventory_cases": inventory_total, "selected_cases": [c["id"] for c in cases],
             "results": results, "status": "running", "pid": os.getpid()}
    write_json(output / "results.json", state)
    with cancellation_handlers(), concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        todo = iter(cases)
        pending = set()
        for _ in range(min(args.workers, len(cases))):
            pending.add(pool.submit(run_case, next(todo), output, args.kissat.resolve(), args.cadical.resolve()))
        while pending:
            done, pending = concurrent.futures.wait(pending, return_when=concurrent.futures.FIRST_COMPLETED)
            completed_batch = [future.result() for future in done]
            results.extend(completed_batch)
            stopped |= any(r["status"] in {"ERROR", "DISAGREEMENT", "SAT_CANDIDATE"}
                           for r in completed_batch)
            stopped |= ABORT.is_set()
            stopped |= shutil.disk_usage(output).free < 8 * 1024**3
            state["status"] = "draining" if stopped else "running"
            write_json(output / "results.json", state)
            if not stopped:
                for _ in completed_batch:
                    case = next(todo, None)
                    if case is not None:
                        pending.add(pool.submit(run_case, case, output, args.kissat.resolve(), args.cadical.resolve()))
    completed = {r["id"] for r in results}
    state["not_started"] = [c["id"] for c in cases if c["id"] not in completed]
    state["status"] = "aborted" if ABORT.is_set() else "stopped" if stopped else "complete"
    state["selected_all_unsat"] = not state["not_started"] and all(
        r["status"] in {"UNSAT_PRIMARY", "UNSAT_CROSSCHECKED"} for r in results)
    state["inventory_all_unsat"] = len(cases) == inventory_total and state["selected_all_unsat"]
    state["children_maxrss"] = {"value": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                                "units": "bytes" if sys.platform == "darwin" else "KiB",
                                "scope": "cumulative child high-water mark; not per-case or summed RSS"}
    write_json(output / "results.json", state)
    print(json.dumps({k: v for k, v in state.items() if k not in {"results", "solvers"}}))
    return 0 if state["selected_all_unsat"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
