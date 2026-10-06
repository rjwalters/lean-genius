#!/usr/bin/env python3
"""Cloud node supervisor for the H1 certificate-BANK re-validation (2026-10-06): stream each 2026-08
bank proof from S3 into cake_lpr against the pinned-emitter CNF. Derived from ../h1_cert_full_20261001/cert_worker.py.

(Original docstring of the cert worker follows; "cert_row.py" below means bank_check_row.py here.)

Same claim/ledger/STOP discipline as ../phase_b_h1_verdict_cloud_20260921/node_worker.py (claim =
S3 PutObject If-None-Match on claims/<ID>; attempt-unique result keys; control/STOP; ALARM), but each
slot runs cert_row.py: emit the CNF with the pinned v2cnf, solve with proof-logging CaDiCaL, stream
the proof through a hashing relay into cake_lpr, and keep only the receipt (no proof is stored).

Scheduling: rows are claimed in manifest order (longest census CaDiCaL time first) so the long rows
start early. A node-wide memory budget (MEM_BUDGET_GB) is reserved per row as heap + SOLVER_GB, so
slots never overcommit RAM; a CHECK_HEAP_EXHAUSTED row is retried on the same slot with the heap
doubled (up to MAX_HEAP_MB). A row is not claimed unless its expected time (census seconds x 1.5 +
1 h) fits in the node's remaining lifetime.

Alarms (write control/ALARM-<ID> and control/STOP): CHECK_FAILED (the verified checker rejected a
proof) or a SAT answer from the solver. CNF_MISMATCH / ERROR stop the slot; MAX_NODE_ERRORS stops the
node. When every slot has exited the node powers off.
"""
from __future__ import annotations

import argparse, hashlib, json, os, shutil, subprocess, sys, threading, time
from pathlib import Path

BUCKET = "2am-erdos85-certs"
PREFIX = "sat49/bankcheck-20261006"
AWS = "/usr/local/bin/aws"
WORK = Path("/scratch/cert")
OUT = Path("/scratch/out")
MAX_NODE_ERRORS = 6
SOLVER_GB = 2
MAX_HEAP_MB = 64000
HERE = Path(__file__).resolve().parent

lock = threading.Lock()
mem_cv = threading.Condition(lock)
node = {"errors": 0, "done": 0, "stop": False, "active": {}, "statuses": {}, "mem_free_gb": 0.0}
STARTED = time.time()


def log(message: str) -> None:
    line = f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())} {message}\n"
    with open("/var/log/e85-cert.log", "a") as out:
        out.write(line)


def aws(*args: str, timeout: int = 600) -> subprocess.CompletedProcess:
    return subprocess.run([AWS, *args], capture_output=True, text=True, timeout=timeout)


def exists(key: str) -> bool:
    r = aws("s3api", "head-object", "--bucket", BUCKET, "--key", f"{PREFIX}/{key}")
    if r.returncode == 0:
        return True
    if "Not Found" in r.stderr or "(404)" in r.stderr or "NoSuchKey" in r.stderr:
        return False
    raise RuntimeError(f"head-object indeterminate: {r.stderr.strip()[:300]}")


def listing(sub: str) -> set[str]:
    keys, token = [], None
    while True:
        cmd = ["s3api", "list-objects-v2", "--bucket", BUCKET, "--prefix", f"{PREFIX}/{sub}/", "--output", "json"]
        if token:
            cmd += ["--continuation-token", token]
        r = aws(*cmd)
        if r.returncode != 0:
            raise RuntimeError(f"list failed: {r.stderr.strip()[:300]}")
        page = json.loads(r.stdout or "{}")
        keys += [c["Key"] for c in page.get("Contents", [])]
        token = page.get("NextContinuationToken")
        if not token:
            return {k.rsplit("/", 1)[1] for k in keys}


def put_new(key: str, body: Path) -> bool:
    r = aws("s3api", "put-object", "--bucket", BUCKET, "--key", f"{PREFIX}/{key}", "--body", str(body), "--if-none-match", "*")
    if r.returncode == 0:
        return True
    if "PreconditionFailed" in r.stderr or "ConditionalRequestConflict" in r.stderr:
        return False
    raise RuntimeError(f"put-object failed: {r.stderr.strip()[:300]}")


def put_with_retry(key: str, body: Path) -> bool:
    for attempt in range(4):
        try:
            return put_new(key, body)
        except Exception as e:  # noqa: BLE001
            log(f"put retry {attempt} key={key} {e}")
            time.sleep(30)
    raise RuntimeError(f"upload failed after retries: {key}")


def reserve(gb: float) -> None:
    with mem_cv:
        while node["mem_free_gb"] < gb:
            mem_cv.wait(30)
        node["mem_free_gb"] -= gb


def release(gb: float) -> None:
    with mem_cv:
        node["mem_free_gb"] += gb
        mem_cv.notify_all()


def run_row(args, slot: int, row: dict) -> dict:
    heap = args.heap_mb
    attempts = []
    while True:
        # Unique per attempt: a duplicate claim of the same row on this node must never touch a
        # live attempt's directory (2026-10-05: rmtree of a running attempt lost two UNSAT receipts).
        out = WORK / f"{row['id']}.h{heap}.{int(time.time())}.s{slot}"
        need = heap / 1000 + SOLVER_GB
        reserve(need)
        try:
            out.mkdir(parents=True)
            cand = out / "candidates.json"
            cand.write_text(json.dumps(row["candidates"]))
            cmd = [sys.executable, "-B", str(HERE / "bank_check_row.py"), row["id"], "--out", str(out),
                   "--heap-mb", str(heap), "--candidates", str(cand) if row["candidates"] else "none",
                   "--inventory", args.inventory, "--v2cnf", args.v2cnf, "--cake-lpr", args.cake_lpr,
                   "--aws", AWS, "--profile", ""]
            subprocess.run(cmd, capture_output=True, text=True)
        finally:
            release(need)
        rp = out / row["id"] / "receipt.json"
        receipt = json.loads(rp.read_text()) if rp.is_file() else {"status": "ERROR", "error": "no receipt"}
        attempts.append(out)
        if receipt["status"] == "CHECK_HEAP_EXHAUSTED" and heap * 2 <= MAX_HEAP_MB:
            log(f"slot={slot} {row['id']} heap {heap} MB exhausted; retrying at {heap * 2}")
            heap *= 2
            continue
        break
    # Archive every attempt's small artefacts (receipts + logs; there is no proof file to archive).
    OUT.mkdir(exist_ok=True)
    stamp = int(time.time())
    archive = OUT / f"{row['id']}.tar.zst"
    tar = subprocess.Popen(["tar", "-C", str(WORK), "-cf", "-", *[a.name for a in attempts]], stdout=subprocess.PIPE)
    with archive.open("wb") as dst:
        z = subprocess.run(["zstd", "-q", "-6", "-c"], stdin=tar.stdout, stdout=dst)
    tar.stdout.close()
    if tar.wait() != 0 or z.returncode != 0:
        raise RuntimeError("archive failed")
    key = f"results/{row['id']}.{args.iid}.{stamp}.tar.zst"
    if not put_with_retry(key, archive):
        raise RuntimeError(f"result key exists: {key}")
    ledger = {"id": row["id"], "node": args.iid, "instance_type": args.itype, "slot": slot, "status": receipt["status"],
              "heap_mb": heap, "attempts": len(attempts), "archive_key": f"{PREFIX}/{key}",
              "archive_sha256": hashlib.sha256(archive.read_bytes()).hexdigest(),
              "cnf_sha256": receipt.get("cnf_sha256"), "gz_sha256": receipt.get("gz_sha256"), "lrat_sha256": receipt.get("lrat_sha256"),
              "gz_bytes": receipt.get("gz_bytes"), "lrat_bytes": receipt.get("lrat_bytes"), "wall_seconds": receipt.get("wall_seconds"),
              "cnf_match": receipt.get("cnf_match"), "gz_match": receipt.get("gz_match"), "lrat_match": receipt.get("lrat_match"),
              "no_producer_ledger": receipt.get("no_producer_ledger"), "failure": receipt.get("failure"),
              "solver_returncode": None, "error": receipt.get("error"),
              "checkout_head": subprocess.check_output(["git", "-C", args.repo, "rev-parse", "HEAD"], text=True).strip()}
    lp = OUT / f"{row['id']}.ledger.json"
    lp.write_text(json.dumps(ledger, indent=1) + "\n")
    if not put_with_retry(f"ledger/{row['id']}.{args.iid}.{stamp}.json", lp):
        raise RuntimeError("ledger key exists")
    archive.unlink(); lp.unlink()
    for a in attempts:
        shutil.rmtree(a, ignore_errors=True)
    return ledger


def slot_loop(args, slot: int, rows: list[dict]) -> None:
    time.sleep(slot * 3)
    # Claim body = instance ID, so the controller can release claims held by dead (e.g. spot-reclaimed) nodes.
    marker = OUT / "claim-owner"
    OUT.mkdir(exist_ok=True)
    marker.write_text(args.iid)
    while True:
        with lock:
            if node["stop"]:
                return
        try:
            picked = None
            for attempt in range(3):
                try:
                    if exists("control/STOP"):
                        log(f"slot={slot} STOP present")
                        return
                    taken = listing("claims")
                    left = STARTED + args.lifetime - time.time()
                    for row in rows:
                        if row["id"] in taken or row["lrat_bytes_max"] / 10e6 * 2 + 3600 > left:
                            continue
                        if put_new(f"claims/{row['id']}", marker):
                            picked = row
                            break
                    break
                except Exception as e:  # noqa: BLE001
                    log(f"slot={slot} claim attempt {attempt} failed: {type(e).__name__}: {e}")
                    if attempt == 2:
                        raise
                    time.sleep(60 + 10 * slot % 30)
            if picked is None:
                log(f"slot={slot} nothing claimable (done, taken, or does not fit the remaining lifetime)")
                return
            with lock:
                node["active"][slot] = picked["id"]
            log(f"slot={slot} claimed {picked['id']} ({picked['lrat_bytes_max'] / 1e9:.1f} GB LRAT)")
            ledger = run_row(args, slot, picked)
            log(f"slot={slot} {picked['id']} {ledger['status']} heap={ledger['heap_mb']} lrat={ledger['lrat_bytes']}")
            with lock:
                node["active"].pop(slot, None)
                node["done"] += 1
                node["statuses"][ledger["status"]] = node["statuses"].get(ledger["status"], 0) + 1
            alarm = ledger["status"] == "CHECK_FAILED"  # cake_lpr rejected a bank proof against the pinned CNF
            if alarm:
                note = OUT / f"alarm-{picked['id']}.json"
                note.write_text(json.dumps(ledger, indent=1) + "\n")
                put_with_retry(f"control/ALARM-{picked['id']}", note)
                put_with_retry("control/STOP", note)
                log(f"slot={slot} ALARM {picked['id']} {ledger['status']}; STOP written")
                return
            if ledger["status"] in ("CNF_MISMATCH", "HASH_MISMATCH", "ERROR", "CHECK_HEAP_EXHAUSTED"):
                with lock:
                    node["errors"] += 1
                    if node["errors"] >= MAX_NODE_ERRORS:
                        node["stop"] = True
                log(f"slot={slot} stopping after {ledger['status']} on {picked['id']}")
                return
        except Exception as e:  # noqa: BLE001
            log(f"slot={slot} infrastructure failure, slot stops: {type(e).__name__}: {e}")
            with lock:
                node["active"].pop(slot, None)
                node["errors"] += 1
                if node["errors"] >= MAX_NODE_ERRORS:
                    node["stop"] = True
            return


def heartbeat(args, threads, final=False) -> None:
    with lock:
        status = {"iid": args.iid, "instance_type": args.itype, "utc": time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                  "slots": args.slots, "alive_slots": sum(t.is_alive() for t in threads), "done": node["done"],
                  "errors": node["errors"], "statuses": dict(node["statuses"]), "active": dict(node["active"]),
                  "mem_free_gb": round(node["mem_free_gb"], 1), "final": final, "loadavg": os.getloadavg(),
                  "scratch_free_gib": round(shutil.disk_usage("/scratch").free / 2**30, 1)}
    OUT.mkdir(exist_ok=True)
    p = OUT / "status.json"
    p.write_text(json.dumps(status, indent=1) + "\n")
    for src, name in ((str(p), "status.json"), ("/var/log/e85-cert.log", "worker.log")):
        r = aws("s3", "cp", "--only-show-errors", src, f"s3://{BUCKET}/{PREFIX}/nodes/{args.iid}/{name}")
        if r.returncode != 0:
            log(f"heartbeat upload of {name} failed rc={r.returncode}: {r.stderr.strip()[:300]}")


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", required=True)
    p.add_argument("--freight", required=True, help="dir with manifest.jsonl and tables/")
    p.add_argument("--manifest-sha256", required=True)
    p.add_argument("--iid", required=True)
    p.add_argument("--itype", required=True)
    p.add_argument("--slots", type=int, required=True)
    p.add_argument("--mem-budget-gb", type=float, required=True)
    p.add_argument("--heap-mb", type=int, default=4000)
    p.add_argument("--inventory", required=True)
    p.add_argument("--lifetime", type=int, default=108000)
    p.add_argument("--v2cnf", required=True)
    p.add_argument("--cake-lpr", default="/usr/local/bin/cake_lpr")
    p.add_argument("--docker", default="docker")
    p.add_argument("--only", default="", help="comma-separated IDs (canary)")
    p.add_argument("--no-poweroff", action="store_true")
    args = p.parse_args()
    raw = (Path(args.freight) / "manifest.jsonl").read_bytes()
    if hashlib.sha256(raw).hexdigest() != args.manifest_sha256:
        raise SystemExit("manifest identity mismatch")
    rows = [json.loads(l) for l in raw.decode().splitlines() if l.strip()]
    for r in rows:
        r["id"] = r["tag"]
    if args.only:
        keep = set(args.only.split(","))
        rows = [r for r in rows if r["id"] in keep]
    node["mem_free_gb"] = args.mem_budget_gb
    WORK.mkdir(parents=True, exist_ok=True)
    log(f"node start iid={args.iid} type={args.itype} slots={args.slots} mem_budget={args.mem_budget_gb}GB heap={args.heap_mb}MB rows={len(rows)} prefix={PREFIX}")
    threads = [threading.Thread(target=slot_loop, args=(args, s, rows), daemon=True) for s in range(args.slots)]
    for t in threads:
        t.start()
    while any(t.is_alive() for t in threads):
        heartbeat(args, threads)
        time.sleep(300)
    log("all slots exited")
    heartbeat(args, threads, final=True)
    if not args.no_poweroff:
        subprocess.run(["/usr/sbin/poweroff"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
