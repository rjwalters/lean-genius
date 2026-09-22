#!/usr/bin/env python3
"""Cloud node supervisor for the H1 verdict-only census (board goal #44). SINGLE-SEAT.

One slot = one CPU. Each slot claims one case ID with an S3 conditional PUT, runs the
REVIEWED, UNCHANGED wrapper `sat49/dispatch_h1_residual_verdict_only.py --workers 1
--case-id ID` into a fresh run directory, uploads that whole run directory as one
tar.zst, writes a small ledger object, and repeats. This file never looks inside a CNF,
never classifies a solver log, and never requests a proof: every verdict is whatever the
reviewed runner wrote, and the reviewed summarizer re-derives it from the logs later.

Stop rules: `control/STOP` stops new claims everywhere. A SAT_CANDIDATE or DISAGREEMENT
writes `control/ALARM` and `control/STOP`. A slot stops after its own first ERROR; a node
stops claiming after MAX_NODE_ERRORS. When every slot has exited the node powers off,
which terminates it.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import shutil
import subprocess
import threading
import time

BUCKET = "2am-erdos85-certs"
BASE_PREFIX = "sat49/verdict-only-20260921"
PREFIX = BASE_PREFIX  # pass 1; `--pass-prefix NAME` appends /NAME (pass 2 and later)
CONFIG_COMMIT = "bf95b3937e894956d07f09b55401dc41ffa904a6"
QUEUE_SHA256 = "d9e4548ff356dfbd23db82b09d6a02d9a1d348f7c9aa4378e5dc6e8bc9e6fe87"
CONFIG = "research/problems/erdos-85-wip-01/phase_b_h1_verdict_20260916/config.draft.json"
CASE_TIMEOUT = 30000
AWS = "/usr/local/bin/aws"
RUNS = Path("/scratch/runs")
OUT = Path("/scratch/out")
MAX_NODE_ERRORS = 6
HERE = Path(__file__).resolve().parent

lock = threading.Lock()
node = {"errors": 0, "done": 0, "stop": False, "active": {}, "statuses": {}}


def log(message: str) -> None:
    line = f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())} {message}\n"
    with lock:
        with open("/var/log/e85-worker.log", "a") as out:
            out.write(line)


def aws(*args: str, timeout: int = 600) -> subprocess.CompletedProcess:
    return subprocess.run([AWS, *args], capture_output=True, text=True, timeout=timeout)


def exists(key: str) -> bool:
    """True/False only on a definite answer; anything else raises."""
    result = aws("s3api", "head-object", "--bucket", BUCKET, "--key", f"{PREFIX}/{key}")
    if result.returncode == 0:
        return True
    if "Not Found" in result.stderr or "(404)" in result.stderr or "NoSuchKey" in result.stderr:
        return False
    raise RuntimeError(f"head-object indeterminate: {result.stderr.strip()[:300]}")


def listing(sub: str) -> set[str]:
    result = aws("s3api", "list-objects-v2", "--bucket", BUCKET, "--prefix", f"{PREFIX}/{sub}/",
                 "--query", "Contents[].Key", "--output", "json")
    if result.returncode != 0:
        raise RuntimeError(f"list failed: {result.stderr.strip()[:300]}")
    keys = json.loads(result.stdout or "null") or []
    return {key.rsplit("/", 1)[1] for key in keys}


def put_new(key: str, body: Path) -> bool:
    """Atomic create. True = created, False = already existed; anything else raises."""
    result = aws("s3api", "put-object", "--bucket", BUCKET, "--key", f"{PREFIX}/{key}",
                 "--body", str(body), "--if-none-match", "*")
    if result.returncode == 0:
        return True
    if "PreconditionFailed" in result.stderr or "ConditionalRequestConflict" in result.stderr:
        return False
    raise RuntimeError(f"put-object failed: {result.stderr.strip()[:300]}")


def put_with_retry(key: str, body: Path) -> bool:
    for attempt in range(4):
        try:
            return put_new(key, body)
        except Exception as error:  # noqa: BLE001
            log(f"put retry {attempt} key={key} {error}")
            time.sleep(30)
    raise RuntimeError(f"upload failed after retries: {key}")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def run_case(args, slot: int, case_id: str) -> dict:
    run_dir = RUNS / case_id
    if run_dir.exists():
        shutil.rmtree(run_dir)
    sat49 = Path(args.repo) / "research/problems/erdos-85-wip-01/sat49"
    config = Path(args.repo) / CONFIG
    # Pass 1: the reviewed residual wrapper. Pass 2+: the reviewed base dispatcher with an
    # explicit case ID (the wrapper hard-codes the 14,400 s policy). Both are unchanged code.
    tool = "dispatch_verdict_only.py" if args.direct else "dispatch_h1_residual_verdict_only.py"
    command = ["python3.12", "-B", str(sat49 / tool),
               "--config", str(config), "--config-commit", CONFIG_COMMIT, "--execute",
               "--case-id", case_id, "--workers", "1", "--output-dir", str(run_dir),
               "--kissat", "/usr/local/bin/kissat", "--cadical", "/usr/local/bin/cadical"]
    started = time.time()
    # Generation cap + both solver caps + slack. The runner enforces the real caps.
    process = subprocess.run(command, capture_output=True, text=True, timeout=CASE_TIMEOUT, cwd=str(sat49))
    elapsed = time.time() - started
    record = {"id": case_id, "node": args.iid, "instance_type": args.itype, "slot": slot,
              "wrapper_returncode": process.returncode, "elapsed_seconds": round(elapsed, 1),
              "wrapper_stderr_tail": process.stderr[-1500:], "status": "ERROR",
              "config_commit": CONFIG_COMMIT, "config": CONFIG, "tool": tool, "pass_prefix": PREFIX,
              "checkout_head": subprocess.check_output(["git", "-C", args.repo, "rev-parse", "HEAD"], text=True).strip()}
    state_path = run_dir / "results.json"
    if state_path.is_file():
        state = json.loads(state_path.read_text())
        results = state.get("results", [])
        record["run_status"] = state.get("status")
        if len(results) == 1 and results[0].get("id") == case_id:
            record["status"] = results[0]["status"]
            solve = results[0].get("solve", {})
            for name in ("primary", "crosscheck"):
                if name in solve:
                    record[f"{name}_seconds"] = round(solve[name]["elapsed_seconds"], 1)
                    record[f"{name}_verdict"] = solve[name]["verdict"]
            if "error" in results[0]:
                record["error"] = results[0]["error"][:500]
    if run_dir.is_dir():
        OUT.mkdir(exist_ok=True)
        archive = OUT / f"{case_id}.tar.zst"
        tar = subprocess.Popen(["tar", "-C", str(RUNS), "-cf", "-", case_id], stdout=subprocess.PIPE)
        with archive.open("wb") as destination:
            zstd = subprocess.run(["zstd", "-q", "-6", "-c"], stdin=tar.stdout, stdout=destination)
        tar.stdout.close()
        if tar.wait() != 0 or zstd.returncode != 0:
            raise RuntimeError("archive failed")
        record["archive_sha256"] = sha256(archive)
        record["archive_bytes"] = archive.stat().st_size
        # Attempt-unique key: a retried case never overwrites earlier evidence.
        key = f"results/{case_id}.{args.iid}.{int(started)}.tar.zst"
        if not put_with_retry(key, archive):
            raise RuntimeError(f"result key already exists: {key}")
        record["archive_key"] = f"{PREFIX}/{key}"
        archive.unlink()
        shutil.rmtree(run_dir)
    ledger = OUT / f"{case_id}.ledger.json"
    ledger.write_text(json.dumps(record, indent=1) + "\n")
    if not put_with_retry(f"ledger/{case_id}.{args.iid}.{int(started)}.json", ledger):
        raise RuntimeError("ledger key already exists")
    ledger.unlink()
    return record


def slot_loop(args, slot: int, queue: list[str]) -> None:
    time.sleep(slot * 3)  # ramp: avoid 64 simultaneous container starts inside a 120 s generation cap
    order = queue[:]
    random.Random(f"{args.iid}:{slot}").shuffle(order)
    marker = Path(f"/scratch/freight/node")
    while True:
        with lock:
            if node["stop"]:
                break
        try:
            if exists("control/STOP"):
                log(f"slot={slot} STOP present")
                break
            taken = listing("claims")
            picked = None
            for case_id in order:
                if case_id in taken:
                    continue
                if put_new(f"claims/{case_id}", marker):
                    picked = case_id
                    break
            if picked is None:
                log(f"slot={slot} no work left")
                break
            with lock:
                node["active"][slot] = picked
            log(f"slot={slot} claimed {picked}")
            record = run_case(args, slot, picked)
            log(f"slot={slot} {picked} {record['status']} {record['elapsed_seconds']}s")
            with lock:
                node["active"].pop(slot, None)
                node["done"] += 1
                node["statuses"][record["status"]] = node["statuses"].get(record["status"], 0) + 1
            if record["status"] in ("SAT_CANDIDATE", "DISAGREEMENT"):
                note = OUT / f"alarm-{picked}.json"
                note.write_text(json.dumps(record, indent=1) + "\n")
                put_with_retry(f"control/ALARM-{picked}", note)
                put_with_retry("control/STOP", note)
                log(f"slot={slot} ALARM {picked} {record['status']}; STOP written")
                break
            if record["status"] == "ERROR":
                with lock:
                    node["errors"] += 1
                    if node["errors"] >= MAX_NODE_ERRORS:
                        node["stop"] = True
                log(f"slot={slot} stopping after ERROR on {picked}")
                break
        except Exception as error:  # noqa: BLE001
            log(f"slot={slot} infrastructure failure, slot stops: {type(error).__name__}: {error}")
            with lock:
                node["active"].pop(slot, None)
                node["errors"] += 1
                if node["errors"] >= MAX_NODE_ERRORS:
                    node["stop"] = True
            break


def heartbeat(args, threads: list[threading.Thread], final: bool = False) -> None:
    with lock:
        status = {"iid": args.iid, "instance_type": args.itype, "utc": time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                  "slots": args.slots, "alive_slots": sum(t.is_alive() for t in threads),
                  "done": node["done"], "errors": node["errors"], "statuses": dict(node["statuses"]),
                  "active": dict(node["active"]), "final": final,
                  "loadavg": os.getloadavg(), "scratch_free_gib": round(shutil.disk_usage("/scratch").free / 2**30, 1)}
    path = OUT / "status.json"
    OUT.mkdir(exist_ok=True)
    path.write_text(json.dumps(status, indent=1) + "\n")
    aws("s3", "cp", "--only-show-errors", str(path), f"s3://{BUCKET}/{PREFIX}/nodes/{args.iid}/status.json")
    aws("s3", "cp", "--only-show-errors", "/var/log/e85-worker.log", f"s3://{BUCKET}/{PREFIX}/nodes/{args.iid}/worker.log")


def main() -> int:
    global PREFIX, CONFIG, CONFIG_COMMIT, CASE_TIMEOUT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True)
    parser.add_argument("--iid", required=True)
    parser.add_argument("--itype", required=True)
    parser.add_argument("--slots", type=int, required=True)
    parser.add_argument("--no-poweroff", action="store_true")
    parser.add_argument("--pass-prefix", default="", help="pass 2+: S3 sub-prefix for claims/results/ledger/nodes/control")
    parser.add_argument("--queue", default="queue-1137.ids", help="ID file in this directory")
    parser.add_argument("--queue-sha256", default=QUEUE_SHA256)
    parser.add_argument("--config", default=CONFIG, help="repo-relative dispatch config")
    parser.add_argument("--config-commit", default=CONFIG_COMMIT)
    parser.add_argument("--direct", action="store_true", help="use dispatch_verdict_only.py instead of the residual wrapper")
    args = parser.parse_args()
    if args.pass_prefix:
        PREFIX = f"{BASE_PREFIX}/{args.pass_prefix}"
    CONFIG, CONFIG_COMMIT = args.config, args.config_commit
    policy = json.loads((Path(args.repo) / CONFIG).read_text())
    CASE_TIMEOUT = (policy["generation_cap_seconds"] + policy["policies"]["H1"]["primary_cap_seconds"]
                    + policy["policies"]["H1"]["crosscheck_cap_seconds"] + 1200)
    raw = (HERE / args.queue).read_bytes()
    if hashlib.sha256(raw).hexdigest() != args.queue_sha256:
        raise SystemExit("queue identity mismatch")
    queue = raw.decode().split()
    if not queue or len(set(queue)) != len(queue):
        raise SystemExit("queue empty or has duplicates")
    RUNS.mkdir(parents=True, exist_ok=True)
    log(f"node start iid={args.iid} type={args.itype} slots={args.slots} prefix={PREFIX} queue={args.queue} n={len(queue)} config={CONFIG}@{CONFIG_COMMIT[:10]} direct={args.direct} case_timeout={CASE_TIMEOUT}")
    threads = [threading.Thread(target=slot_loop, args=(args, slot, queue), daemon=True)
               for slot in range(args.slots)]
    for thread in threads:
        thread.start()
    while any(thread.is_alive() for thread in threads):
        heartbeat(args, threads)
        time.sleep(300)
    log("all slots exited")
    heartbeat(args, threads, final=True)
    if not args.no_poweroff:
        subprocess.run(["/usr/sbin/poweroff"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
