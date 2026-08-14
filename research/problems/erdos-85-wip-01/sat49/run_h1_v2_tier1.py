#!/usr/bin/env python3
"""Tier-1 exact-v2 LRAT ingestion pipeline for durable DRAT shards.

Configuration is via ``H1_TIER1_*`` environment variables.  In particular,
``H1_TIER1_JOBS`` selects a shard without replacing the active ``jobs.tsv``.
Pass ``--dry-run`` to validate and count the selected jobs without starting
any conversion or replay process.

Per orbit (compact-replay flow, squad 3533/3536/3537):
  1. CNF: use sweep source CNF when present (state MATCH via `v2cnf check`),
     else emit the Lean-exact CNF via `v2cnf emit` (state LEAN-EXACT).
  2. drat-trim <cnf> <drat> -L <lrat>   -> requires "s VERIFIED"
  3. lrat-check <cnf> <lrat>            -> requires "VERIFIED" (not NOT)
  4. streaming compact (compact_h1_v2_lrat.py) -> the form Lean's checker
     consumes; then lratreplay <cnf> <COMPACT> in docker -> requires
     "LRAT accepted: true".  Raw lratreplay acceptance does NOT transfer
     to parseOrderFortyNineLratProof + LRAT.check (squad 3533).
  5. all-green: bank <orbit>.v2.compact.lrat + manifest into v2-lrat/.
     Raw LRAT is hashed for provenance then DROPPED (source DRAT(.gz) + CNF
     hashes preserve provenance; never delete source DRAT — squad 3537).

Replay concurrency: ONE 32g replay host-wide, enforced both by an in-process
semaphore and the cross-process mkdir lock at v2-tier1-work/replay.lock
(PID+timestamp owner metadata, stale-owner liveness reclaim).  Every tool
that runs `lratreplay` must honor the same lock (squad 3537).

Resumable: orbits already LEAN_ACCEPTED in results.tsv are skipped.
"""
import concurrent.futures as cf
import hashlib, os, re, subprocess, sys, threading, time
from contextlib import contextmanager

BASE = "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49"
WORK = BASE + "/v2-tier1-work"
LRAT_DIR = BASE + "/v2-lrat"
DT = WORK + "/bin/drat-trim"
LC = WORK + "/bin/lrat-check"
COMPACTOR = WORK + "/compact_h1_v2_lrat.py"
IMAGE = "lean4-arm64:v4.31.0"
JOBS = os.environ.get("H1_TIER1_JOBS", WORK + "/jobs.tsv")
RESULTS = os.environ.get("H1_TIER1_RESULTS", WORK + "/results.tsv")
WORKERS = int(os.environ.get("H1_TIER1_WORKERS", "4"))
if WORKERS < 1:
    raise ValueError("H1_TIER1_WORKERS must be positive")
lock = threading.Lock()
# Replays are the memory-heavy stage. The Docker VM is 48 GiB total, so run
# ONE replay at a time at 32g (leaves VM headroom for the v2cnf containers
# and host drat-trim pressure); raise only from measured peak (codex, 3515).
REPLAY_MEM = "32g"
replay_slots = threading.Semaphore(1)
REPLAY_LOCK = WORK + "/replay.lock"

@contextmanager
def replay_lock():
    """Cross-process replay mutex (squad 3537): mkdir lock with PID owner
    metadata; a lock whose owner PID is dead is reclaimed."""
    while True:
        try:
            os.mkdir(REPLAY_LOCK)
            with open(REPLAY_LOCK + "/owner", "w") as f:
                f.write(f"{os.getpid()} {time.time():.0f}\n")
            break
        except FileExistsError:
            try:
                pid = int(open(REPLAY_LOCK + "/owner").read().split()[0])
                os.kill(pid, 0)  # raises if owner is dead
            except FileNotFoundError:
                # The owner creates the directory before its metadata file.
                # Do not steal a lock during that small publication window.
                try:
                    age = time.time() - os.stat(REPLAY_LOCK).st_mtime
                except FileNotFoundError:
                    continue
                if age < 60:
                    time.sleep(1)
                    continue
                try:
                    os.rmdir(REPLAY_LOCK)
                except OSError:
                    pass
                continue
            except (OSError, ValueError):
                try:
                    os.remove(REPLAY_LOCK + "/owner")
                except FileNotFoundError:
                    pass
                try:
                    os.rmdir(REPLAY_LOCK)
                except OSError:
                    pass
                continue
            time.sleep(15)
    try:
        yield
    finally:
        try:
            os.remove(REPLAY_LOCK + "/owner")
        except FileNotFoundError:
            pass
        try:
            os.rmdir(REPLAY_LOCK)
        except OSError:
            pass

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

def cnf_clause_count(path):
    """Original clause count from the DIMACS header (p cnf <vars> <clauses>)."""
    with open(path) as f:
        for line in f:
            if line.startswith("p cnf"):
                return int(line.split()[3])
    raise ValueError(f"no DIMACS header in {path}")

def docker(args, timeout, memory="12g"):
    cmd = ["docker", "run", "--rm", "--memory=" + memory, "--cpus=2",
           "-v", "lean-mathlib-cache:/cache", "-v", BASE + ":/data"] + [IMAGE] + args
    return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)

def to_data(path):
    assert path.startswith(BASE + "/")
    return "/data/" + path[len(BASE) + 1:]

def record(orbit, state, detail=""):
    with lock:
        with open(RESULTS, "a") as f:
            f.write(f"{orbit}\t{state}\t{detail}\n")
    print(f"{orbit}\t{state}\t{detail}", flush=True)

def process(job):
    orbit, profile, family, mode, tpath, cpath, dpath = job
    tmp = WORK + "/tmp/" + orbit
    lrat = tmp + ".lrat"
    drat = tmp + ".drat"
    compact = tmp + ".compact.lrat"
    try:
        # 1. CNF
        if cpath:
            cnf = cpath
            r = docker(["/cache/bin/v2cnf", "check", profile, to_data(tpath), to_data(cnf)], 900)
            if "MATCH" not in r.stdout:
                record(orbit, "FAIL-MATCH", (r.stdout + r.stderr).strip().replace("\n", " | ")[:300])
                return
            cnf_state = "MATCH"
        else:
            cnf = tmp + ".lean.cnf"
            r = docker(["/bin/bash", "-c",
                        f"/cache/bin/v2cnf emit {profile} {to_data(tpath)} > {to_data(cnf)}"], 900)
            if r.returncode != 0 or os.path.getsize(cnf) == 0:
                record(orbit, "FAIL-EMIT", r.stderr.strip()[:300])
                return
            cnf_state = "LEAN-EXACT"
        # 2. gunzip (or plain copy) + drat-trim
        # Some fleet proofs are stored uncompressed while jobs.tsv names the
        # .gz path (45 tags archive-wide); use the plain .drat when the .gz
        # is absent instead of failing — never compress on this volume.
        if dpath.endswith(".gz") and not os.path.exists(dpath) and os.path.exists(dpath[:-3]):
            dpath = dpath[:-3]
        if dpath.endswith(".gz"):
            with open(drat, "wb") as f:
                subprocess.run(["gunzip", "-c", dpath], stdout=f, check=True, timeout=3600)
        else:
            drat = dpath
        r = subprocess.run([DT, cnf, drat, "-L", lrat], capture_output=True, text=True, timeout=7200)
        if "s VERIFIED" not in r.stdout:
            tail = [l for l in r.stdout.splitlines() if not l.startswith("c WARNING")][-3:]
            record(orbit, "FAIL-DRAT-TRIM", " | ".join(tail)[:300])
            return
        # 3. lrat-check (raw)
        r = subprocess.run([LC, cnf, lrat], capture_output=True, text=True, timeout=3600)
        verdict = [l for l in r.stdout.splitlines() if "VERIFIED" in l]
        if not verdict or "NOT VERIFIED" in verdict[-1]:
            record(orbit, "FAIL-LRAT-CHECK", " | ".join(verdict)[:300])
            return
        # 4. streaming compact, then Lean replay of the COMPACT payload
        num_orig = cnf_clause_count(cnf)
        r = subprocess.run([sys.executable, COMPACTOR, lrat, str(num_orig), compact],
                           capture_output=True, text=True, timeout=3600)
        if r.returncode != 0 or not os.path.exists(compact):
            record(orbit, "FAIL-COMPACT", (r.stdout + r.stderr).strip().replace("\n", " | ")[:300])
            return
        with replay_slots, replay_lock():
            r = docker(["/cache/bin/lratreplay", to_data(cnf), to_data(compact)],
                       3600, memory=REPLAY_MEM)
        if "LRAT accepted: true" not in r.stdout:
            detail = (r.stdout + r.stderr).strip().replace("\n", " | ")[:250]
            state = "FAIL-INFRA-OOM" if r.returncode == 137 else "FAIL-LEAN-REPLAY"
            record(orbit, state, f"rc={r.returncode} {detail}")
            return
        m = re.search(r"CNF clauses: (\d+); LRAT actions: (\d+)", r.stdout)
        clauses, actions = m.groups() if m else ("?", "?")
        # 5. bank COMPACT only; hash raw for provenance, then drop it
        raw_sha = sha256(lrat)
        final = LRAT_DIR + "/" + orbit + ".v2.compact.lrat"
        os.replace(compact, final)
        csha, ksha = sha256(cnf), sha256(final)
        kbytes = os.path.getsize(final)
        table = open(tpath).read().strip()
        with open(LRAT_DIR + "/" + orbit + ".manifest.txt", "w") as f:
            f.write(f"orbit {orbit}\nprofile {family}\nmode {mode}\n"
                    f"cnf_state {cnf_state}\nsource_cnf_sha256 {csha}\n"
                    f"raw_lrat_sha256 {raw_sha}\n"
                    f"compact_lrat_sha256 {ksha}\ncompact_bytes {kbytes}\n"
                    f"source_cnf_clauses {clauses}\nlrat_actions {actions}\n"
                    f"drat_trim_result s VERIFIED\nlrat_check_result c VERIFIED\n"
                    f"lean_replay_compact LRAT accepted: true\ntable {table}\n")
        record(orbit, "LEAN_ACCEPTED",
               f"{cnf_state} clauses={clauses} actions={actions} compact_sha={ksha[:16]} compact_bytes={kbytes}")
    except Exception as e:
        record(orbit, "FAIL-EXC", str(e)[:300])
    finally:
        for p in (drat, tmp + ".lean.cnf", lrat, compact):
            if p != dpath and p.startswith(WORK) and os.path.exists(p):
                os.remove(p)

def main():
    done = set()
    if os.path.exists(RESULTS):
        for line in open(RESULTS):
            f = line.split("\t")
            if len(f) >= 2 and f[1].strip() == "LEAN_ACCEPTED":
                done.add(f[0])
    jobs = []
    for line in open(JOBS):
        j = line.rstrip("\n").split("\t")
        if len(j) != 7:
            raise ValueError(f"malformed job row in {JOBS}: expected 7 fields")
        if j[0] not in done:
            jobs.append(j)
    print(f"jobs={JOBS} pending {len(jobs)} / accepted-ledger {len(done)}",
          flush=True)
    if "--dry-run" in sys.argv:
        return
    with cf.ThreadPoolExecutor(max_workers=WORKERS) as ex:
        list(ex.map(process, jobs))
    print("PIPELINE COMPLETE", flush=True)

if __name__ == "__main__":
    main()
