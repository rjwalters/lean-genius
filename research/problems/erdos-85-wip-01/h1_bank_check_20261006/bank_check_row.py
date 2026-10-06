#!/usr/bin/env python3
"""Re-validate ONE 2026-08 H1 certificate-bank row with cake_lpr (no solving, no drat-trim).

1. Find the row's producer ledger line (cnf_sha256, compact_lrat_sha256, compact_gz_sha256) under
   s3://2am-erdos85-certs/sat49/campaign-20260825/{h1-fleet,h1-fleet-v2,h1-fleet-v3}/ledger/<tag>.line
2. Rebuild the orbit table from proofs/Proofs/Certificates/h1_orbit_inventory.compact (tag = sha1 of the
   sorted nonzero table, as in phase_b_h1_h3/freeze.py), emit the CNF with the pinned v2cnf inside the
   pinned image, run `v2cnf check`, and require sha256 == the ledger's cnf_sha256.
3. Stream s3://…/h1/<tag>.compact.lrat.gz → sha256 (gz) → gunzip → sha256 (LRAT) → FIFO → cake_lpr.
   VERIFIED only if cake_lpr prints "s VERIFIED UNSAT" AND both stream hashes equal the matching ledger
   candidate's. A row with NO producer ledger is still VERIFIED by the emitter CNF + cake_lpr alone and
   is marked no_producer_ledger (the ledger match is provenance, not the correctness argument).
   Nothing but the CNF and logs touches disk.
"""
from __future__ import annotations
import argparse, hashlib, json, os, platform, shutil, subprocess, threading, time
from pathlib import Path

BUCKET = "s3://2am-erdos85-certs/sat49/campaign-20260825"
IMAGE = "sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"
PAIRS = [(c, j) for c in range(8) for j in range(c + 1, 8) if j != (c ^ 1)]


def sha(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""):
            h.update(b)
    return h.hexdigest()


def awsbase():
    return [args_.aws] + (["--profile", args_.profile] if args_.profile else []) + ["--region", "us-east-1"]


def payer():
    return ["--request-payer", "requester"] if args_.request_payer else []


def aws(args, **kw):
    return subprocess.run(awsbase() + list(args), **kw)


def ledger_line(tag: str) -> dict:
    for fleet in ("h1-fleet-v3", "h1-fleet-v2", "h1-fleet"):
        r = aws(["s3", "cp", *payer(), f"{BUCKET}/{fleet}/ledger/{tag}.line", "-"], capture_output=True, text=True)
        if r.returncode == 0 and r.stdout.strip():
            for line in r.stdout.strip().splitlines()[::-1]:
                f = line.split()
                kv = dict(x.split("=", 1) for x in f[2:] if "=" in x)
                if f[1] == tag and kv.get("compact") == "ok" and kv.get("trim") == "VERIFIED":
                    kv["fleet"], kv["raw"] = fleet, line
                    return kv
    raise SystemExit(f"no usable ledger line for {tag}")


def table_for(tag: str):
    for line in open(args_.inventory):
        vals = list(map(int, line.split()))
        table = {p: v for p, v in zip(PAIRS, vals[1:], strict=True) if v}
        if hashlib.sha1(json.dumps(sorted(table.items())).encode()).hexdigest()[:16] == tag:
            return vals[0], table
    raise SystemExit(f"tag {tag} not in inventory")


def docker_v2cnf(argv, inputs: Path, out):
    cmd = ["docker", "run", "--rm", "--read-only", "--network", "none", "--memory", "8g", "--cpus", "1",
           "--mount", f"type=bind,src={args_.v2cnf},dst=/v2cnf,readonly", "--mount", f"type=bind,src={inputs},dst=/inputs,readonly",
           IMAGE, "/usr/bin/timeout", "--signal=TERM", "--kill-after=5s", "300s", "/v2cnf", *argv]
    return subprocess.run(cmd, stdout=out, stderr=subprocess.STDOUT).returncode


def main():
    global args_
    p = argparse.ArgumentParser()
    p.add_argument("tag"); p.add_argument("--out", type=Path, required=True)
    p.add_argument("--heap-mb", type=int, default=8000)
    p.add_argument("--inventory", default="/Volumes/Stripe/lean-genius/erdos85-certpilot/proofs/Proofs/Certificates/h1_orbit_inventory.compact")
    p.add_argument("--v2cnf", default="/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/campaign-20260825.noindex/h1fleet/v3freight-rebuild-20260905/stage/freight/v2cnf")
    p.add_argument("--cake-lpr", default="/Volumes/Stripe/lean-genius/cake_lpr-src/cake_lpr")
    p.add_argument("--aws", default=shutil.which("aws") or "aws"); p.add_argument("--profile", default="2am-admin", help="'' on cloud nodes (instance role)")
    p.add_argument("--request-payer", action="store_true", help="add --request-payer requester (third parties reading the Requester Pays bucket)")
    p.add_argument("--candidates", default="", help="JSON file of producer-ledger candidates from the manifest, or 'none' (no producer ledger); default: look up S3 ledgers")
    args_ = p.parse_args()
    d = args_.out.resolve() / args_.tag; d.mkdir(parents=True, exist_ok=False)
    rec = {"schema": "erdos85-h1-bank-check-v2", "tag": args_.tag, "host": platform.node(), "started": time.time(),
           "cake_lpr_sha256": sha(Path(args_.cake_lpr)), "v2cnf_sha256": sha(Path(args_.v2cnf)), "image": IMAGE}
    if args_.candidates:
        cands = json.loads(Path(args_.candidates).read_text()) if args_.candidates != "none" else []
    else:
        cands = [ledger_line(args_.tag)]
    rec["candidates"] = cands; rec["no_producer_ledger"] = not cands
    prof, table = table_for(args_.tag); rec["profile"] = prof
    assert all(str(prof) == c.get("p") for c in cands), (prof, [c.get("p") for c in cands])
    inp = d / "input"; inp.mkdir()
    (inp / "table.json").write_text(json.dumps([[list(k), v] for k, v in sorted(table.items())]))
    with open(inp / "input.cnf", "wb") as f:
        rc = docker_v2cnf(["emit", str(prof), "/inputs/table.json"], inp, f)
    with open(d / "v2cnf-check.log", "wb") as f:
        crc = docker_v2cnf(["check", str(prof), "/inputs/table.json", "/inputs/input.cnf"], inp, f)
    rec["cnf_sha256"] = sha(inp / "input.cnf")
    rec["emit_ok"] = rc == 0 and crc == 0
    led = next((c for c in cands if c["cnf_sha256"] == rec["cnf_sha256"]), None)
    rec["cnf_match"] = rec["emit_ok"] and (led is not None or not cands)
    if not rec["cnf_match"]:
        rec["status"] = "CNF_MISMATCH"
    else:
        fifo = d / "lrat.fifo"; os.mkfifo(fifo)
        clog = open(d / "cake_lpr.log", "wb")
        t0 = time.time()
        cake = subprocess.Popen([args_.cake_lpr, str(inp / "input.cnf"), str(fifo), f"--CML_HEAP_SIZE={args_.heap_mb}", "--CML_STACK_SIZE=1000"],
                                stdout=clog, stderr=subprocess.STDOUT)
        dl = subprocess.Popen(awsbase() + ["s3", "cp", *payer(), f"{BUCKET}/h1/{args_.tag}.compact.lrat.gz", "-"],
                              stdout=subprocess.PIPE, stderr=open(d / "download.err", "wb"))
        gz = subprocess.Popen(["gzip", "-dc"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        hg, hl, n = hashlib.sha256(), hashlib.sha256(), {"gz": 0, "lrat": 0}

        def feed():
            for b in iter(lambda: dl.stdout.read(1 << 20), b""):
                hg.update(b); n["gz"] += len(b)
                gz.stdin.write(b)
            gz.stdin.close()

        def drain():
            with open(fifo, "wb") as out:
                for b in iter(lambda: gz.stdout.read(1 << 20), b""):
                    hl.update(b); n["lrat"] += len(b)
                    try:
                        out.write(b)
                    except BrokenPipeError:
                        rec["checker_closed_early"] = True
                        for _ in iter(lambda: gz.stdout.read(1 << 20), b""):
                            pass
                        break
        tf, td = threading.Thread(target=feed), threading.Thread(target=drain)
        tf.start(); td.start(); tf.join(); td.join()
        rec["download_rc"], rec["gunzip_rc"] = dl.wait(), gz.wait()
        rec["cake_rc"] = cake.wait(); clog.close(); fifo.unlink()
        log = (d / "cake_lpr.log").read_text(errors="replace")
        rec.update(wall_seconds=time.time() - t0, gz_bytes=n["gz"], lrat_bytes=n["lrat"],
                   gz_sha256=hg.hexdigest(), lrat_sha256=hl.hexdigest(),
                   gz_match=(led is None) or hg.hexdigest() == led["compact_gz_sha256"],
                   lrat_match=(led is None) or hl.hexdigest() == led["compact_lrat_sha256"],
                   verified_line="s VERIFIED UNSAT" in log, heap_exhausted="heap space exhausted" in log,
                   failure=next((l for l in log.splitlines() if l.startswith("c Checking failed")), None))
        ok = rec["verified_line"] and rec["gz_match"] and rec["lrat_match"] and rec["download_rc"] == 0 and rec["gunzip_rc"] == 0 and not rec.get("checker_closed_early")
        rec["status"] = "VERIFIED" if ok else ("CHECK_HEAP_EXHAUSTED" if rec["heap_exhausted"] else ("HASH_MISMATCH" if rec["verified_line"] else "CHECK_FAILED"))
    (inp / "input.cnf").unlink(missing_ok=True)
    rec["finished"] = time.time()
    (d / "receipt.json").write_text(json.dumps(rec, indent=1) + "\n")
    print(json.dumps({k: rec.get(k) for k in ("tag", "status", "wall_seconds", "gz_bytes", "lrat_bytes")}))


if __name__ == "__main__":
    main()
