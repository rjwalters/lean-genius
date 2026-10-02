#!/usr/bin/env python3
"""Goal #48: zero-spend replay of the 96 historical H1 certificates on the Mac.

Per row: check canonical CNF sha256 -> gunzip archived DRAT -> drat-trim -L (LRAT) ->
lratreplay (Std LRAT.check, pinned image a5ca6c4e, Linux build sha 37aad1d5...) in Docker.
Intermediates are deleted after each row; receipts.jsonl keeps sizes, timings, hashes.
"""
import concurrent.futures as cf, gzip, hashlib, json, os, shutil, subprocess, sys, time
from pathlib import Path
HERE = Path(__file__).resolve().parent
W = HERE.parent
OUT = Path(sys.argv[1]); OUT.mkdir(parents=True, exist_ok=True)
WORKERS = int(os.environ.get("WORKERS", "4"))
DRAT_TRIM = "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/v2-tier1-work/bin/drat-trim"
TOOLS = "/Volumes/Stripe/lean-genius/artifacts/erdos85-conflict-v6-bootstrap-sol1-20260909.noindex/materialization-check/tools"
IMAGE = "sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"
# CHECKER=lean (Std LRAT.check via lratreplay, in-memory ~10x proof bytes) or cake (cake_lpr, streaming,
# bounded heap). Rows killed for memory (rc 137) are LRAT_CHECK_OOM, not failures, and are retried.
CHECKER = os.environ.get("CHECKER", "lean")
CAKE = os.environ.get("CAKE_LPR", "/Volumes/Stripe/lean-genius/cake_lpr-src/cake_lpr")

def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""): h.update(b)
    return h.hexdigest()

rows = json.load(open(W / "phase_b_historical_overlay/historical-95.json"))["rows"]
rows.append(json.load(open(W / "phase_b_historical_overlay_96/historical-96.json"))["extra_case"])
assert len(rows) == 96
rec_path = OUT / "receipts.jsonl"
done = set()
if rec_path.exists():
    done = {j["tag"] for j in map(json.loads, filter(str.strip, rec_path.read_text().splitlines()))
            if j.get("status") != "LRAT_CHECK_OOM"}

def timed(cmd, log, **kw):
    t0 = time.time()
    with open(log, "wb") as f:
        p = subprocess.Popen(cmd, stdout=f, stderr=subprocess.STDOUT, **kw)
        _, st, ru = os.wait4(p.pid, 0)
    return os.waitstatus_to_exitcode(st), time.time() - t0, ru.ru_utime + ru.ru_stime

def run(r):
    tag = r["tag"]; d = OUT / tag; d.mkdir(exist_ok=True)
    rec = {"tag": tag, "profile": r["profile"], "cnf_sha256_expected": r["cnf_sha256"]}
    cnf = proof = None
    for e in r["evidence"]:
        base = e["cnf_path"][:-4]
        for suf in (".drat.gz", ".drat"):
            if Path(base + suf).exists(): cnf, proof = Path(e["cnf_path"]), Path(base + suf); break
        if cnf: break
    rec["cnf_path"], rec["drat_path"] = str(cnf), str(proof)
    if sha(cnf) != r["cnf_sha256"]:
        rec["status"] = "CNF_SHA_MISMATCH"; return rec
    work = d / "work"; work.mkdir(exist_ok=True)
    shutil.copyfile(cnf, work / "f.cnf")
    drat = work / "p.drat"
    if proof.suffix == ".gz":
        with gzip.open(proof, "rb") as s, open(drat, "wb") as t: shutil.copyfileobj(s, t, 1 << 22)
    else:
        shutil.copyfile(proof, drat)
    rec["drat_bytes"] = drat.stat().st_size
    rc, wall, cpu = timed([DRAT_TRIM, str(work / "f.cnf"), str(drat), "-L", str(work / "p.lrat"), "-t", "200000"], d / "drat-trim.log")
    rec.update(drat_trim_rc=rc, drat_trim_wall=wall, drat_trim_cpu=cpu)
    drat.unlink()
    lrat = work / "p.lrat"
    if not lrat.exists() or b"s VERIFIED" not in (d / "drat-trim.log").read_bytes():
        rec["status"] = "DRAT_TRIM_FAILED"; shutil.rmtree(work); return rec
    rec["lrat_bytes"] = lrat.stat().st_size; rec["lrat_sha256"] = sha(lrat)
    if CHECKER == "cake":
        rc, wall, cpu = timed([CAKE, str(work / "f.cnf"), str(lrat), "--CML_HEAP_SIZE=4000", "--CML_STACK_SIZE=1000"], d / "cake_lpr.log")
        log = (d / "cake_lpr.log").read_text(errors="replace")
        rec.update(checker="cake_lpr", checker_sha256=sha(CAKE), cake_lpr_rc=rc, cake_lpr_wall=wall)
        rec["status"] = "CAKE_LPR_VERIFIED" if rc == 0 and "s VERIFIED UNSAT" in log else "CAKE_LPR_FAILED"
    else:
        rc, wall, cpu = timed(["docker", "run", "--rm", "--network", "none", "--memory", "24g",
                               "-v", f"{TOOLS}:/tools:ro", "-v", f"{work}:/w:ro", IMAGE,
                               "/tools/bin/lratreplay", "/w/f.cnf", "/w/p.lrat"], d / "lratreplay.log")
        log = (d / "lratreplay.log").read_text(errors="replace")
        rec.update(checker="lratreplay", lratreplay_rc=rc, lratreplay_wall=wall)
        rec["status"] = ("LRAT_CHECK_ACCEPTED" if rc == 0 and "LRAT accepted: true" in log
                         else "LRAT_CHECK_OOM" if rc == 137 else "LRAT_CHECK_FAILED")
    shutil.rmtree(work)
    rec["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    return rec

todo = [r for r in rows if r["tag"] not in done]
print(f"{len(todo)} rows, {WORKERS} workers", flush=True)
with cf.ThreadPoolExecutor(WORKERS) as ex, open(rec_path, "a") as out:
    # as_completed: a receipt lands when its row finishes, not behind slower rows (#48 crash lesson)
    for fut in cf.as_completed([ex.submit(run, r) for r in todo]):
        rec = fut.result()
        out.write(json.dumps(rec) + "\n"); out.flush()
        print(rec["tag"], rec["status"], round(rec.get("drat_trim_wall", 0)), round(rec.get("lratreplay_wall", rec.get("cake_lpr_wall", 0))), flush=True)
