#!/usr/bin/env python3
"""H3/H5 cube-and-conquer feasibility pilot, node side (one spot instance, verdict timing + 1-2 certs).

Phase A: Knuth random walks (sample_walks.py, one process per walk) on each cell listed in plan.json.
Phase B: for every (cell, walk, depth) in the plan, build the cube CNF (base + sorted unit clauses
         inserted after the header = cube_verdict.cube_bytes layout, the one the Lean CubeTree
         composition consumes) and time CaDiCaL 3.0.1 on it under the cap (no proof). One job per core.
Phase C: certificate path: the solved cubes with the smallest wall time >= 5 s (at most plan.cert_n)
         are re-solved with binary LRAT streamed into cake_lpr (h1_cert_full_20261001/cert_row.py).
Results are appended to out/results.jsonl and pushed with presigned PUT URLs (no IAM role on the node).
"""
import concurrent.futures as cf, hashlib, json, os, subprocess, sys, time, types, threading
from pathlib import Path

W = Path(sys.argv[1])  # work dir with bases/<cell>.cnf, plan.json, urls.json
plan = json.loads((W / "plan.json").read_text())
urls = json.loads((W / "urls.json").read_text())
OUT = W / "out"; OUT.mkdir(exist_ok=True)
CODE = Path(__file__).resolve().parent  # repo layout: research/problems/erdos-85-wip-01/<dir>/
sys.path.insert(0, str(CODE.parent / "phase_b_h1_verdict_cloud_20260921"))
sys.path.insert(0, str(CODE.parent / "h1_cert_full_20261001"))
import cube_verdict  # noqa: E402
from cert_row import solve_and_check  # noqa: E402
lock = threading.Lock()
SCRATCH = Path(os.environ.get("E85_SCRATCH", "/scratch"))
SLOTS = plan.get("slots", os.cpu_count())


def emit(rec):
    with lock:
        with open(OUT / "results.jsonl", "a") as f:
            f.write(json.dumps(rec) + "\n")


def push():
    for name in ("results.jsonl", "node.log"):
        p = OUT / name
        if p.exists() and name in urls:
            subprocess.run(["curl", "-s", "-f", "-X", "PUT", "-T", str(p), urls[name]], capture_output=True)


def pusher():
    while True:
        push(); time.sleep(60)


def log(msg):
    with lock:
        with open(OUT / "node.log", "a") as f:
            f.write(time.strftime("%H:%M:%S ") + msg + "\n")


threading.Thread(target=pusher, daemon=True).start()
log(f"start slots={SLOTS} cells={[c['cell'] for c in plan['cells']]}")

# Phase A: walks
walks = {}
procs = []
for c in plan["cells"]:
    for w in range(c["walks"]):
        o = OUT / f"walk_{c['cell']}_{w:02d}.json"
        procs.append((c["cell"], w, o, subprocess.Popen(
            [sys.executable, str(CODE / "sample_walks.py"), str(W / "bases" / f"{c['cell']}.cnf"), "--walks", "1",
             "--first-walk", str(w), "--depth", str(c["walk_depth"]), "--out", str(o)],
            stdout=subprocess.DEVNULL, stderr=open(OUT / f"walk_{c['cell']}_{w:02d}.err", "w"))))
for cell, w, o, p in procs:
    p.wait()
    walks[(cell, w)] = json.loads(o.read_text())["walks"][0]
log(f"phase A done: {len(walks)} walks")
emit({"phase": "A", "walks": {f"{k[0]}/{k[1]}": {"cube": v["cube"], "W": v["W"]} for k, v in walks.items()}})
push()

# Phase B: timing
jobs = []
for c in plan["cells"]:
    for depth in c["depths"]:
        for w in range(c.get("walks_per_depth", {}).get(str(depth), c["walks"])):
            wk = walks[(c["cell"], w)]
            if len(wk["cube"]) < depth:
                continue
            jobs.append({"cell": c["cell"], "walk": w, "depth": depth, "cube": wk["cube"][:depth], "W": wk["W"][depth - 1]})
bases = {}


def base(cell):
    with lock:
        if cell not in bases:
            bases[cell] = cube_verdict.read_cnf(W / "bases" / f"{cell}.cnf")
        return bases[cell]


def run(job):
    raw, hi, nv, nc = base(job["cell"])
    d = OUT / f"{job['cell']}_w{job['walk']:02d}_d{job['depth']:02d}"; d.mkdir(exist_ok=True)
    cnf = SCRATCH / f"{d.name}.cnf"
    cnf.write_bytes(cube_verdict.cube_bytes(raw, hi, nv, nc, {abs(l): int(l > 0) for l in job["cube"]}))
    t0 = time.time()
    p = subprocess.Popen(["cadical", "-t", str(plan["cap"]), str(cnf)], stdout=open(d / "cadical.log", "wb"), stderr=subprocess.STDOUT)
    _, st, ru = os.wait4(p.pid, 0)
    wall = time.time() - t0
    slog = (d / "cadical.log").read_text(errors="replace")
    res = "UNSAT" if "s UNSATISFIABLE" in slog else "SAT" if "s SATISFIABLE" in slog else "UNKNOWN"
    conf = next((l.split()[2] for l in slog.splitlines() if l.startswith("c conflicts:")), None)
    rec = dict(job, phase="B", result=res, rc=os.waitstatus_to_exitcode(st), wall_s=round(wall, 1),
               cpu_s=round(ru.ru_utime + ru.ru_stime, 1), maxrss_kb=ru.ru_maxrss, conflicts=conf, cube_cnf=cnf.name)
    cnf.unlink()
    emit(rec); log(f"{d.name} {res} {wall:.0f}s")
    return rec


with cf.ThreadPoolExecutor(SLOTS) as ex:
    results = list(ex.map(run, jobs))
log("phase B done"); push()

# Phase C: certificate path on the fastest solved cubes
solved = sorted((r for r in results if r["result"] == "UNSAT" and r["wall_s"] >= 5), key=lambda r: r["wall_s"])


def cert(r):
    raw, hi, nv, nc = base(r["cell"])
    d = OUT / f"cert_{r['cell']}_w{r['walk']:02d}_d{r['depth']:02d}"; d.mkdir(exist_ok=True)
    cnf = SCRATCH / f"{d.name}.cnf"
    cnf.write_bytes(cube_verdict.cube_bytes(raw, hi, nv, nc, {abs(l): int(l > 0) for l in r["cube"]}))
    a = types.SimpleNamespace(cadical="cadical", cake_lpr="cake_lpr", heap_mb=plan.get("heap_mb", 32000),
                              cap=int(min(plan["cap"], max(600, 4 * r["wall_s"]))))
    rec = {"phase": "C", "cell": r["cell"], "walk": r["walk"], "depth": r["depth"], "cube": r["cube"],
           "verdict_wall_s": r["wall_s"], "cnf_sha256": hashlib.sha256(cnf.read_bytes()).hexdigest()}
    log(f"cert {d.name} start")
    try:
        solve_and_check(a, d, cnf, rec)
    except Exception as e:  # noqa: BLE001
        rec["status"] = "ERROR"; rec["error"] = repr(e)
    cnf.unlink()
    emit(rec); log(f"cert {d.name} {rec.get('status')}"); push()


with cf.ThreadPoolExecutor(2) as ex:
    list(ex.map(cert, solved[:plan.get("cert_n", 2)]))
log("all done"); push()
