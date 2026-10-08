#!/usr/bin/env python3
"""Node supervisor for the H7 t=0 hsb3 certificate campaign (check-then-discard).

Modelled on ../h1_cert_full_20261001/cert_worker.py, with the same discipline:
claim = conditional put (If-None-Match) of claims/<batch id>, body = this node's instance id, so
the controller can release claims of dead nodes; attempt-unique result keys; control/STOP;
control/ALARM-<id> on CHECK_FAILED or SAT; node error budget; unique work directory per attempt.

Differences from H1: the claim unit is a BATCH (64 leaves of one cube, or one cover CNF) run by
one cert_batch.py process; per-leaf receipts are uploaded as one results/<id>.<iid>.<t>.jsonl.zst;
progress of a running batch is uploaded to partial/<id>.<iid>.jsonl every PARTIAL_SECONDS, and a
node that later claims a released batch carries the CERTIFIED receipts forward instead of
re-solving them (bounds what a spot reclaim can cost).

Stores: S3 (campaign), or --local-store DIR (same semantics on a directory; used for the
end-to-end test on the builder and for --plan).   --plan prints what would be claimed and exits.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import h7_common as hc  # noqa: E402

BUCKET = "2am-erdos85-certs"
PREFIX = "sat49/h7hsb-20261008"
AWS = "/usr/local/bin/aws"
MAX_NODE_ERRORS = 6
PARTIAL_SECONDS = 600
SLOT_GB = 1.5  # CaDiCaL + CNF file on tmpfs, on top of the checker heap

lock = threading.Lock()
node = {"errors": 0, "done": 0, "items": 0, "stop": False, "active": {}, "statuses": {}}
STARTED = time.time()
LOG = Path("/var/log/e85-h7hsb.log")


def log(message: str) -> None:
    line = f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())} {message}\n"
    with open(LOG, "a") as out:
        out.write(line)


class S3Store:
    def aws(self, *args: str, timeout: int = 600) -> subprocess.CompletedProcess:
        return subprocess.run([AWS, *args], capture_output=True, text=True, timeout=timeout)

    def exists(self, key: str) -> bool:
        r = self.aws("s3api", "head-object", "--bucket", BUCKET, "--key", f"{PREFIX}/{key}")
        if r.returncode == 0:
            return True
        if "Not Found" in r.stderr or "(404)" in r.stderr or "NoSuchKey" in r.stderr:
            return False
        raise RuntimeError(f"head-object indeterminate: {r.stderr.strip()[:300]}")

    def listing(self, sub: str) -> set[str]:
        keys, token = [], None
        while True:
            cmd = ["s3api", "list-objects-v2", "--bucket", BUCKET, "--prefix", f"{PREFIX}/{sub}", "--output", "json"]
            if token:
                cmd += ["--continuation-token", token]
            r = self.aws(*cmd)
            if r.returncode != 0:
                raise RuntimeError(f"list failed: {r.stderr.strip()[:300]}")
            page = json.loads(r.stdout or "{}")
            keys += [c["Key"] for c in page.get("Contents", [])]
            token = page.get("NextContinuationToken")
            if not token:
                return {k.rsplit("/", 1)[1] for k in keys}

    def put_new(self, key: str, body: Path) -> bool:
        r = self.aws("s3api", "put-object", "--bucket", BUCKET, "--key", f"{PREFIX}/{key}", "--body", str(body),
                     "--if-none-match", "*")
        if r.returncode == 0:
            return True
        if "PreconditionFailed" in r.stderr or "ConditionalRequestConflict" in r.stderr:
            return False
        raise RuntimeError(f"put-object failed: {r.stderr.strip()[:300]}")

    def put(self, key: str, body: Path) -> None:
        r = self.aws("s3", "cp", "--only-show-errors", str(body), f"s3://{BUCKET}/{PREFIX}/{key}")
        if r.returncode != 0:
            raise RuntimeError(f"cp failed: {r.stderr.strip()[:300]}")

    def get(self, key: str, dest: Path) -> bool:
        return self.aws("s3", "cp", "--only-show-errors", f"s3://{BUCKET}/{PREFIX}/{key}", str(dest)).returncode == 0


class LocalStore:
    """Directory with the same primitives; put_new is exclusive (O_EXCL), like If-None-Match."""

    def __init__(self, root: Path):
        self.root = root
        root.mkdir(parents=True, exist_ok=True)

    def exists(self, key: str) -> bool:
        return (self.root / key).exists()

    def listing(self, sub: str) -> set[str]:
        d, _, pre = sub.rpartition("/")
        base = self.root / d
        return {p.name for p in base.iterdir() if p.name.startswith(pre)} if base.is_dir() else set()

    def put_new(self, key: str, body: Path) -> bool:
        dst = self.root / key
        dst.parent.mkdir(parents=True, exist_ok=True)
        try:
            fd = os.open(dst, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
        except FileExistsError:
            return False
        with os.fdopen(fd, "wb") as f:
            f.write(body.read_bytes())
        return True

    def put(self, key: str, body: Path) -> None:
        dst = self.root / key
        dst.parent.mkdir(parents=True, exist_ok=True)
        tmp = dst.with_name(dst.name + f".tmp{os.getpid()}.{threading.get_ident()}")
        shutil.copyfile(body, tmp)
        os.replace(tmp, dst)

    def get(self, key: str, dest: Path) -> bool:
        src = self.root / key
        if not src.is_file():
            return False
        shutil.copyfile(src, dest)
        return True


def put_with_retry(store, key: str, body: Path) -> bool:
    for attempt in range(4):
        try:
            return store.put_new(key, body)
        except Exception as e:  # noqa: BLE001
            log(f"put retry {attempt} key={key} {e}")
            time.sleep(30)
    raise RuntimeError(f"upload failed after retries: {key}")


def run_batch(args, store, slot: int, row: dict) -> dict:
    bid = row["id"]
    # Unique per attempt: a duplicate claim on this node must never touch a live attempt's files.
    out_dir = args.out / f"{bid}.{int(time.time())}.s{slot}"
    out_dir.mkdir(parents=True)
    receipts, carry, stop_file = out_dir / "receipts.jsonl", out_dir / "carry.jsonl", out_dir / "STOP"
    # Carry forward CERTIFIED receipts of interrupted attempts (cert_batch re-validates each one).
    with carry.open("wb") as dst:
        for name in sorted(store.listing(f"partial/{bid}.")):
            tmp = out_dir / "partial.tmp"
            if store.get(f"partial/{name}", tmp):
                data = tmp.read_bytes()
                dst.write(data if data.endswith(b"\n") or not data else data + b"\n")
    cmd = [sys.executable, "-B", str(HERE / "cert_batch.py"), "--inputs", str(args.inputs), "--batch", json.dumps(row),
           "--out", str(receipts), "--work", str(args.work), "--cap", str(args.cap), "--heap-mb", str(args.heap_mb),
           "--cadical", args.cadical, "--cake-lpr", args.cake_lpr, "--carry", str(carry), "--stop-file", str(stop_file)]
    if args.allow_unpinned_binaries:
        cmd.append("--allow-unpinned-binaries")
    proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=open(out_dir / "batch.err", "wb"))
    last = time.time()
    while True:
        try:
            rc = proc.wait(timeout=30)
            break
        except subprocess.TimeoutExpired:
            pass
        if time.time() - last > args.partial_seconds:
            last = time.time()
            try:
                if receipts.is_file() and receipts.stat().st_size:
                    store.put(f"partial/{bid}.{args.iid}.jsonl", receipts)
                if store.exists("control/STOP"):
                    stop_file.write_text("stop\n")
            except Exception as e:  # noqa: BLE001
                log(f"slot={slot} {bid} partial upload/STOP check failed: {type(e).__name__}: {e}")
    recs = [json.loads(l) for l in receipts.read_text().splitlines()] if receipts.is_file() else []
    if rc == 4:  # stopped between items: keep the partial, write no ledger, leave the claim for the controller
        if recs:
            store.put(f"partial/{bid}.{args.iid}.jsonl", receipts)
        return {"id": bid, "status": "STOPPED", "items": len(recs)}
    statuses: dict[str, int] = {}
    for r in recs:
        statuses[r["status"]] = statuses.get(r["status"], 0) + 1
    expected = 1 if row["kind"] == "cover" else (len(row["leaves"]) if "leaves" in row else row["end"] - row["start"])
    certified = statuses.get("CERTIFIED", 0)
    if rc == 3 or any(s in statuses for s in ("CHECK_FAILED", "SOLVER_SAT")):
        status = "ALARM"
    elif rc == 0 and certified == expected == len(recs):
        status = "CERTIFIED"
    elif len(recs) == expected and all(s in ("CERTIFIED", "SOLVER_TIMEOUT", "CHECK_HEAP_EXHAUSTED") for s in statuses):
        status = "INCOMPLETE"  # every item ran; timeouts and heap-exhausted checks go to the residual pass
    else:
        status = "ERROR"
    stamp = int(time.time())
    packed = out_dir / "receipts.jsonl.zst"
    with packed.open("wb") as dst:
        z = subprocess.run(["zstd", "-q", "-9", "-c", str(receipts)], stdout=dst) if receipts.is_file() else None
    if z is None or z.returncode != 0:
        packed.write_bytes(b"")
    key = f"results/{bid}.{args.iid}.{stamp}.jsonl.zst"
    if not put_with_retry(store, key, packed):
        raise RuntimeError(f"result key exists: {key}")
    err = (out_dir / "batch.err").read_text(errors="replace")[-2000:]
    ledger = {"id": bid, "cube": row["cube"], "kind": row["kind"], "node": args.iid, "instance_type": args.itype,
              "slot": slot, "status": status, "items": expected, "ran": len(recs), "certified": certified,
              "carried": sum(1 for r in recs if r.get("carried")), "statuses": statuses, "batch_returncode": rc,
              "not_certified": [{"leaf": r["leaf"], "status": r["status"]} for r in recs if r["status"] != "CERTIFIED"],
              "results_key": f"{PREFIX}/{key}", "results_sha256": hashlib.sha256(packed.read_bytes()).hexdigest(),
              "receipts_sha256": hashlib.sha256(receipts.read_bytes()).hexdigest() if receipts.is_file() else None,
              "proof_bytes": sum(r.get("proof", {}).get("bytes") or 0 for r in recs),
              "solver_cpu_seconds": sum(r.get("solver", {}).get("cpu_seconds") or 0 for r in recs),
              "checker_cpu_seconds": sum(r.get("checker", {}).get("cpu_seconds") or 0 for r in recs),
              "max_solver_cpu_seconds": max([r.get("solver", {}).get("cpu_seconds") or 0 for r in recs] or [0]),
              "inputs_json_sha256": args.inputs_sha256, "manifest_sha256": args.manifest_sha256,
              "checkout_head": args.head, "stderr_tail": err if status == "ERROR" else None}
    lp = out_dir / "ledger.json"
    lp.write_text(json.dumps(ledger, indent=1) + "\n")
    if not put_with_retry(store, f"ledger/{bid}.{args.iid}.{stamp}.json", lp):
        raise RuntimeError("ledger key exists")
    shutil.rmtree(out_dir, ignore_errors=True)
    return ledger


def slot_loop(args, store, slot: int, rows: list[dict]) -> None:
    time.sleep(slot * 0.5 if args.local_store else slot * 3)
    marker = args.out / "claim-owner"  # claim body = instance id (controller releases dead nodes' claims)
    while True:
        with lock:
            if node["stop"] or (args.max_batches and node["done"] + len(node["active"]) >= args.max_batches):
                return
        try:
            picked = None
            for attempt in range(3):
                try:
                    if store.exists("control/STOP"):
                        log(f"slot={slot} STOP present")
                        return
                    left = STARTED + args.lifetime - time.time()
                    if left < args.min_left:
                        log(f"slot={slot} {left:.0f}s of node lifetime left (< {args.min_left}); not claiming")
                        return
                    taken = store.listing("claims/")
                    for row in rows:
                        if row["id"] in taken:
                            continue
                        if store.put_new(f"claims/{row['id']}", marker):
                            picked = row
                            break
                    break
                except Exception as e:  # noqa: BLE001
                    log(f"slot={slot} claim attempt {attempt} failed: {type(e).__name__}: {e}")
                    if attempt == 2:
                        raise
                    time.sleep(60 + 10 * slot % 30)
            if picked is None:
                log(f"slot={slot} nothing claimable")
                return
            with lock:
                node["active"][slot] = picked["id"]
            log(f"slot={slot} claimed {picked['id']}")
            ledger = run_batch(args, store, slot, picked)
            log(f"slot={slot} {picked['id']} {ledger['status']} certified={ledger.get('certified')}/{ledger.get('items')} "
                f"proof={ledger.get('proof_bytes')} solver_cpu={ledger.get('solver_cpu_seconds', 0):.0f}s")
            with lock:
                node["active"].pop(slot, None)
                node["done"] += 1
                node["items"] += ledger.get("ran", 0)
                node["statuses"][ledger["status"]] = node["statuses"].get(ledger["status"], 0) + 1
            if ledger["status"] == "STOPPED":
                return
            if ledger["status"] == "ALARM":
                note = args.out / f"alarm-{picked['id']}.json"
                note.write_text(json.dumps(ledger, indent=1) + "\n")
                put_with_retry(store, f"control/ALARM-{picked['id']}", note)
                put_with_retry(store, "control/STOP", note)
                log(f"slot={slot} ALARM {picked['id']}; STOP written")
                return
            if ledger["status"] == "ERROR":
                with lock:
                    node["errors"] += 1
                    if node["errors"] >= MAX_NODE_ERRORS:
                        node["stop"] = True
                log(f"slot={slot} stopping after ERROR on {picked['id']}")
                return
        except Exception as e:  # noqa: BLE001
            log(f"slot={slot} infrastructure failure, slot stops: {type(e).__name__}: {e}")
            with lock:
                node["active"].pop(slot, None)
                node["errors"] += 1
                if node["errors"] >= MAX_NODE_ERRORS:
                    node["stop"] = True
            return


def heartbeat(args, store, threads, final=False) -> None:
    with lock:
        status = {"iid": args.iid, "instance_type": args.itype, "utc": time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                  "slots": args.slots, "alive_slots": sum(t.is_alive() for t in threads), "batches_done": node["done"],
                  "items_done": node["items"], "errors": node["errors"], "statuses": dict(node["statuses"]),
                  "active": dict(node["active"]), "final": final, "loadavg": os.getloadavg(),
                  "work_free_gib": round(shutil.disk_usage(args.work).free / 2**30, 1)}
    p = args.out / "status.json"
    p.write_text(json.dumps(status, indent=1) + "\n")
    for src, name in ((p, "status.json"), (LOG, "worker.log")):
        try:
            store.put(f"nodes/{args.iid}/{name}", Path(src))
        except Exception as e:  # noqa: BLE001
            log(f"heartbeat upload of {name} failed: {e}")


def main() -> int:
    global LOG
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--inputs", type=Path, required=True, help="dir with inputs.json, canonical.body, <cube>.*")
    p.add_argument("--inputs-sha256", required=True, help="sha256 of inputs.json")
    p.add_argument("--manifest", type=Path, help="batch manifest (default: regenerated from inputs.json)")
    p.add_argument("--manifest-sha256", required=True)
    p.add_argument("--iid", required=True)
    p.add_argument("--itype", default="unknown")
    p.add_argument("--head", default="unknown")
    p.add_argument("--slots", type=int, required=True)
    p.add_argument("--mem-gb", type=float, required=True,
                   help="node memory budget: slots * (heap + 1.5 GB) must fit (the heap never grows inside a batch)")
    p.add_argument("--allow-unpinned-binaries", action="store_true", help="tests only (fake checker)")
    p.add_argument("--heap-mb", type=int, default=2000)
    p.add_argument("--cap", type=int, default=3600)
    p.add_argument("--lifetime", type=int, default=129600)
    p.add_argument("--min-left", type=int, default=3 * 3600, help="do not claim with less node lifetime left")
    p.add_argument("--partial-seconds", type=int, default=PARTIAL_SECONDS)
    p.add_argument("--cadical", default="/usr/local/bin/cadical")
    p.add_argument("--cake-lpr", default="/usr/local/bin/cake_lpr")
    p.add_argument("--work", type=Path, default=Path("/dev/shm/h7camp"))
    p.add_argument("--out", type=Path, default=Path("/scratch/out"))
    p.add_argument("--log", type=Path, default=LOG)
    p.add_argument("--only", default="", help="comma-separated batch ids (canary)")
    p.add_argument("--max-batches", type=int, default=0, help="stop after this many batches (canary / test)")
    p.add_argument("--local-store", type=Path, help="use a directory instead of S3 (test / dry run)")
    p.add_argument("--plan", action="store_true", help="dry run: print what would be claimed, touch nothing")
    p.add_argument("--no-poweroff", action="store_true")
    args = p.parse_args()
    LOG = args.log
    if hc.sha_file(args.inputs / "inputs.json") != args.inputs_sha256:
        raise SystemExit("inputs.json identity mismatch")
    meta = json.loads((args.inputs / "inputs.json").read_text())
    raw = args.manifest.read_bytes() if args.manifest else hc.manifest_bytes(meta)
    if hashlib.sha256(raw).hexdigest() != args.manifest_sha256:
        raise SystemExit("manifest identity mismatch")
    rows = [json.loads(l) for l in raw.decode().splitlines() if l.strip()]
    if args.only:
        keep = set(args.only.split(","))
        rows = [r for r in rows if r["id"] in keep]
    if args.slots * (args.heap_mb / 1000 + SLOT_GB) > args.mem_gb:
        raise SystemExit(f"{args.slots} slots x ({args.heap_mb} MB heap + {SLOT_GB} GB) exceeds {args.mem_gb} GB")
    if not args.allow_unpinned_binaries and not args.plan:  # fail before claiming anything
        for k, path in (("cadical", args.cadical), ("cake_lpr", args.cake_lpr)):
            if hc.sha_file(Path(path)) != hc.PINNED_BINARIES[k]:
                raise SystemExit(f"{k} at {path} is not the approved build")
    store = LocalStore(args.local_store) if args.local_store else S3Store()
    if args.plan:
        taken = store.listing("claims/") if (args.local_store or os.path.exists(AWS)) else set()
        free = [r for r in rows if r["id"] not in taken]
        items = sum(1 if r["kind"] == "cover" else (len(r["leaves"]) if "leaves" in r else r["end"] - r["start"]) for r in free)
        print(json.dumps({"plan": True, "manifest_rows": len(rows), "claimed": len(rows) - len(free), "claimable": len(free),
                          "claimable_items": items, "slots": args.slots, "heap_mb": args.heap_mb, "cap": args.cap,
                          "first": [r["id"] for r in free[:args.slots]], "store": str(args.local_store or f"s3://{BUCKET}/{PREFIX}")}))
        return 0
    args.out.mkdir(parents=True, exist_ok=True)
    args.work.mkdir(parents=True, exist_ok=True)
    (args.out / "claim-owner").write_text(args.iid)
    log(f"node start iid={args.iid} type={args.itype} slots={args.slots} heap={args.heap_mb}MB cap={args.cap}s "
        f"rows={len(rows)} store={args.local_store or PREFIX} head={args.head}")
    threads = [threading.Thread(target=slot_loop, args=(args, store, s, rows), daemon=True) for s in range(args.slots)]
    for t in threads:
        t.start()
    beat = 0.0
    while any(t.is_alive() for t in threads):
        if time.time() - beat > 300:
            beat = time.time()
            heartbeat(args, store, threads)
        time.sleep(5)
    log("all slots exited")
    heartbeat(args, store, threads, final=True)
    if not args.no_poweroff:
        subprocess.run(["/usr/sbin/poweroff"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
