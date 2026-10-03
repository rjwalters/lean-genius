#!/usr/bin/env python3
"""Goal #48 full run: certify ONE H1 census row, check-then-discard (operator decision 2026-10-01).

1. Emit the row's CNF from its banked table.json with the pinned emitter `v2cnf emit <profile>`
   inside the pinned image, run `v2cnf check`, and require sha256 == the census cnf_sha256.
2. Solve with CaDiCaL (binary LRAT proof logging). The proof is never written to disk:
   CaDiCaL -> FIFO A -> relay (sha256 + byte count) -> FIFO B -> cake_lpr (CakeML-verified checker).
3. Write receipt.json. Success requires CaDiCaL exit 20 + "s UNSATISFIABLE" AND cake_lpr stdout
   "s VERIFIED UNSAT" (cake_lpr exits 0 even when a check FAILS, so the exit code proves nothing).

The proof sha256 lets a third party who re-runs the same solver binary on the same CNF confirm
they regenerated the identical proof. Statuses: CERTIFIED, CNF_MISMATCH, SOLVER_NOT_UNSAT,
CHECK_HEAP_EXHAUSTED (resource limit; retry with a larger --heap-mb), CHECK_FAILED, ERROR.
"""
from __future__ import annotations

import argparse, hashlib, json, os, platform, shutil, subprocess, threading, time
from pathlib import Path

CHUNK = 1 << 20


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""):
            h.update(b)
    return h.hexdigest()


def now() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def docker_v2cnf(args, inputs: Path, v2cnf: Path, image: str, stdout) -> int:
    cmd = [args.docker, "run", "--rm", "--read-only", "--network", "none", "--memory", "8g", "--cpus", "1",
           "--pids-limit", "64", "--mount", f"type=bind,src={v2cnf},dst=/v2cnf,readonly",
           "--mount", f"type=bind,src={inputs},dst=/inputs,readonly", image,
           "/usr/bin/timeout", "--signal=TERM", "--kill-after=5s", "300s", "/v2cnf", *args.v2cnf_args]
    return subprocess.run(cmd, stdout=stdout, stderr=subprocess.STDOUT).returncode


def emit_cnf(a, work: Path, rec: dict) -> Path | None:
    inputs = work / "input"
    inputs.mkdir(parents=True, exist_ok=True)
    (inputs / "table.json").write_bytes(a.table.read_bytes())
    rec["table_sha256"] = sha(inputs / "table.json")
    cnf = inputs / "input.cnf"
    t0 = time.time()
    with open(cnf, "wb") as out:
        a.v2cnf_args = ["emit", str(a.profile), "/inputs/table.json"]
        rc = docker_v2cnf(a, inputs, a.v2cnf, a.image, out)
    rec["emit"] = {"returncode": rc, "seconds": time.time() - t0}
    if rc != 0:
        return None
    with open(work / "v2cnf-check.log", "wb") as log:
        a.v2cnf_args = ["check", str(a.profile), "/inputs/table.json", "/inputs/input.cnf"]
        rec["emit"]["check_returncode"] = docker_v2cnf(a, inputs, a.v2cnf, a.image, log)
    rec["cnf_sha256"] = sha(cnf)
    rec["cnf_bytes"] = cnf.stat().st_size
    ok = rec["emit"]["check_returncode"] == 0 and rec["cnf_sha256"] == a.cnf_sha256
    return cnf if ok else None


def relay(src: Path, dst: Path, state: dict, solver: subprocess.Popen) -> None:
    """Copy FIFO A -> FIFO B, hashing every byte. If the checker goes away, keep draining and
    hashing (so the solver can finish and the proof hash is still complete), and record it."""
    h, n = hashlib.sha256(), 0
    with open(src, "rb") as fin:
        state["src_open"] = True
        fout = open(dst, "wb")
        state["dst_open"] = True
        while True:
            b = fin.read(CHUNK)
            if not b:
                break
            h.update(b)
            n += len(b)
            if fout is not None:
                try:
                    fout.write(b)
                except BrokenPipeError:
                    state["checker_closed_early"] = True
                    fout = None
        state["dst_closing"] = True  # from here on the checker may legitimately finish
        if fout is not None:
            try:
                fout.close()
            except BrokenPipeError:
                state["checker_closed_early"] = True
    state["proof_sha256"], state["proof_bytes"] = h.hexdigest(), n


def solve_and_check(a, work: Path, cnf: Path, rec: dict) -> None:
    fa, fb = work / "proof-a.fifo", work / "proof-b.fifo"
    for f in (fa, fb):
        if f.exists():
            f.unlink()
        os.mkfifo(f)
    t0 = time.time()
    cake_out = open(work / "cake_lpr.log", "wb")
    checker = subprocess.Popen([a.cake_lpr, str(cnf), str(fb), f"--CML_HEAP_SIZE={a.heap_mb}", "--CML_STACK_SIZE=1000"],
                               stdout=cake_out, stderr=subprocess.STDOUT)
    solver_cmd = [a.cadical, "-t", str(a.cap), "--lrat=true", "--binary=true", str(cnf), str(fa)]
    solver = subprocess.Popen(solver_cmd, stdout=open(work / "cadical.log", "wb"), stderr=subprocess.STDOUT)
    state: dict = {}
    t = threading.Thread(target=relay, args=(fa, fb, state, solver), daemon=True)
    t.start()

    def exited(p: subprocess.Popen) -> bool:
        # Peek without reaping (WNOWAIT): Popen.poll() would reap the child and make the main
        # thread's os.wait4 fail with ECHILD (2026-10-03 full-run bug: 5 rows lost as ERROR).
        try:
            return os.waitid(os.P_PID, p.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT) is not None
        except ChildProcessError:
            return True

    def watchdog() -> None:
        # Never deadlock on a FIFO: if the checker dies, drain FIFO B; if the solver dies before
        # opening FIFO A, open-and-close A so the relay sees EOF.
        drained = False
        while t.is_alive():
            if exited(checker) and not drained and not state.get("dst_closing"):
                drained = True
                state["checker_exited_early"] = True
                threading.Thread(target=lambda: open(fb, "rb").read(), daemon=True).start()
            if exited(solver) and not state.get("src_open"):
                try:
                    os.close(os.open(fa, os.O_WRONLY | os.O_NONBLOCK))
                except OSError:
                    pass
            time.sleep(1)

    threading.Thread(target=watchdog, daemon=True).start()
    _, sst, sru = os.wait4(solver.pid, 0)
    solver_wall = time.time() - t0
    t.join()
    _, cst, cru = os.wait4(checker.pid, 0)
    cake_out.close()
    for f in (fa, fb):
        f.unlink()
    slog = (work / "cadical.log").read_text(errors="replace")
    clog = (work / "cake_lpr.log").read_text(errors="replace")
    rec["solver"] = {"command": solver_cmd, "returncode": os.waitstatus_to_exitcode(sst), "wall_seconds": solver_wall,
                     "cpu_seconds": sru.ru_utime + sru.ru_stime, "maxrss": sru.ru_maxrss,
                     "unsat_line": "s UNSATISFIABLE" in slog}
    rec["checker"] = {"returncode": os.waitstatus_to_exitcode(cst), "wall_seconds": time.time() - t0,
                      "cpu_seconds": cru.ru_utime + cru.ru_stime, "maxrss": cru.ru_maxrss, "heap_mb": a.heap_mb,
                      "verified_line": "s VERIFIED UNSAT" in clog,
                      "failure": next((l for l in clog.splitlines() if l.startswith("c Checking failed")), None)}
    rec["proof"] = {"sha256": state.get("proof_sha256"), "bytes": state.get("proof_bytes"), "format": "cadical binary LRAT",
                    "stored": False, "checker_closed_early": state.get("checker_closed_early", False) or state.get("checker_exited_early", False)}
    if not (rec["solver"]["returncode"] == 20 and rec["solver"]["unsat_line"]):
        rec["status"] = "SOLVER_NOT_UNSAT"
    elif rec["checker"]["verified_line"] and not rec["proof"]["checker_closed_early"]:
        rec["status"] = "CERTIFIED"
    elif "heap space exhausted" in clog:
        rec["status"] = "CHECK_HEAP_EXHAUSTED"  # resource limit, not a rejection: retry with a larger heap
    else:
        rec["status"] = "CHECK_FAILED"


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--case-id", required=True)
    p.add_argument("--table", type=Path, required=True)
    p.add_argument("--profile", type=int, required=True)
    p.add_argument("--cnf-sha256", required=True)
    p.add_argument("--out", type=Path, required=True, help="new per-row work/receipt directory")
    p.add_argument("--cap", type=int, default=86400)
    p.add_argument("--heap-mb", type=int, default=4000)
    p.add_argument("--v2cnf", type=Path, required=True)
    p.add_argument("--image", default="sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6")
    p.add_argument("--docker", default="docker")
    p.add_argument("--cadical", default="cadical")
    p.add_argument("--cake-lpr", default="cake_lpr")
    a = p.parse_args()
    for k in ("docker", "cadical", "cake_lpr"):
        setattr(a, k, shutil.which(getattr(a, k)) or getattr(a, k))
    work = a.out.resolve()
    work.mkdir(parents=True)
    rec = {"schema": "erdos85-h1-cert-row-v1", "case_id": a.case_id, "profile": a.profile,
           "expected_cnf_sha256": a.cnf_sha256, "started_utc": now(), "host": platform.node(),
           "machine": platform.machine(), "tool_sha256": sha(Path(__file__)),
           "binaries": {k: {"path": str(v), "sha256": sha(Path(v))} for k, v in
                        (("cadical", a.cadical), ("cake_lpr", a.cake_lpr), ("v2cnf", a.v2cnf))}, "image": a.image}
    try:
        cnf = emit_cnf(a, work, rec)
        if cnf is None:
            rec["status"] = "CNF_MISMATCH"
        else:
            solve_and_check(a, work, cnf, rec)
            cnf.unlink()
    except Exception as e:  # noqa: BLE001
        rec["status"], rec["error"] = "ERROR", f"{type(e).__name__}: {e}"
    rec["finished_utc"] = now()
    (work / "receipt.json").write_text(json.dumps(rec, indent=1) + "\n")
    print(json.dumps({k: rec.get(k) for k in ("case_id", "status")} | {"proof_bytes": rec.get("proof", {}).get("bytes")}))
    return 0 if rec["status"] == "CERTIFIED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
