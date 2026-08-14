#!/usr/bin/env python3
"""Tier-1 exact-v2 LRAT ingestion pipeline for durable DRAT shards.

Configuration is via ``H1_TIER1_*`` environment variables.  In particular,
``H1_TIER1_JOBS`` selects a shard without replacing the active ``jobs.tsv``.
Pass ``--dry-run`` to validate and count the selected jobs without starting
any conversion or replay process.

Per orbit:
  1. CNF: use sweep source CNF when present (state MATCH via `v2cnf check`),
     else emit the Lean-exact CNF via `v2cnf emit` (state LEAN-EXACT).
  2. drat-trim <cnf> <drat> -L <lrat>   -> requires "s VERIFIED"
  3. lrat-check <cnf> <lrat>            -> requires "VERIFIED" (not NOT)
  4. lratreplay <cnf> <lrat> (Lean, in docker) -> requires "LRAT accepted: true"
  5. all-green: bank <orbit>.v2.lrat + manifest into v2-lrat/, record row.

Resumable: orbits already in results.tsv are skipped.
"""
import concurrent.futures as cf
import hashlib, os, re, subprocess, sys, threading

BASE = "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49"
WORK = BASE + "/v2-tier1-work"
LRAT_DIR = BASE + "/v2-lrat"
DT = WORK + "/bin/drat-trim"
LC = WORK + "/bin/lrat-check"
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

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

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
        # 3. lrat-check
        r = subprocess.run([LC, cnf, lrat], capture_output=True, text=True, timeout=3600)
        verdict = [l for l in r.stdout.splitlines() if "VERIFIED" in l]
        if not verdict or "NOT VERIFIED" in verdict[-1]:
            record(orbit, "FAIL-LRAT-CHECK", " | ".join(verdict)[:300])
            return
        # 4. Lean replay (memory-heavy: one slot at REPLAY_MEM;
        # 12g caused invisible exit-137 OOM kills with empty output)
        with replay_slots:
            r = docker(["/cache/bin/lratreplay", to_data(cnf), to_data(lrat)],
                       3600, memory=REPLAY_MEM)
        if "LRAT accepted: true" not in r.stdout:
            detail = (r.stdout + r.stderr).strip().replace("\n", " | ")[:250]
            state = "FAIL-INFRA-OOM" if r.returncode == 137 else "FAIL-LEAN-REPLAY"
            record(orbit, state, f"rc={r.returncode} {detail}")
            return
        m = re.search(r"CNF clauses: (\d+); LRAT actions: (\d+)", r.stdout)
        clauses, actions = m.groups() if m else ("?", "?")
        # 5. bank
        final = LRAT_DIR + "/" + orbit + ".v2.lrat"
        os.replace(lrat, final)
        csha, lsha = sha256(cnf), sha256(final)
        table = open(tpath).read().strip()
        with open(LRAT_DIR + "/" + orbit + ".manifest.txt", "w") as f:
            f.write(f"orbit {orbit}\nprofile {family}\nmode {mode}\n"
                    f"cnf_state {cnf_state}\nsource_cnf_sha256 {csha}\n"
                    f"lrat_sha256 {lsha}\nsource_cnf_clauses {clauses}\n"
                    f"lrat_actions {actions}\n"
                    f"drat_trim_result s VERIFIED\nlrat_check_result c VERIFIED\n"
                    f"lean_replay LRAT accepted: true\ntable {table}\n")
        record(orbit, "LEAN_ACCEPTED", f"{cnf_state} clauses={clauses} actions={actions} lrat_sha={lsha[:16]}")
    except Exception as e:
        record(orbit, "FAIL-EXC", str(e)[:300])
    finally:
        for p in (drat, tmp + ".lean.cnf", lrat):
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
