"""Cloud-only cold project build. Default: validate inputs without compiling."""
import argparse
import concurrent.futures
import json
import os
import re
import signal
import subprocess
import threading
import time
from pathlib import Path

from prepare import ROOT, closure, sha

RUNTIME = "Erdos85H3TripleCompletionRuntime"
# Exported by `lean -c` without a Lake package (attempt 1 copied the Lake-built
# spelling `initialize_proofs_...` and failed to load the plugin).
INIT = "initialize_Proofs_Erdos85H3TripleCompletionRuntime"
SMOKE = "Erdos85H3TripleCompletionPart000"


def save(path, data):
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(data, indent=2) + "\n")
    tmp.replace(path)


def validate_inputs(plan, root):
    if closure(root) != plan["sources"]:
        raise ValueError("Source/dependency drift")
    for rel, digest in plan["config_sha256"].items():
        if sha(root / "proofs" / rel) != digest:
            raise ValueError("Toolchain/config drift: " + rel)
    for rel, digest in plan["runner_sha256"].items():
        if sha(Path(__file__).parent / rel) != digest:
            raise ValueError("Runner drift: " + rel)
    accepted = root / "research/problems/erdos-85-wip-01/order49_h3_closed_capstone_20261008/PLAN.json"
    if sha(accepted) != plan["accepted_axiom_plan_sha256"] or json.loads(accepted.read_text())["exports"] != plan["expected_exports"]:
        raise ValueError("Accepted axiom evidence drift")
    for row in plan["artifacts"]:
        path = root / row["path"]
        if path.stat().st_size != row["bytes"] or sha(path) != row["sha256"]:
            raise ValueError("Certificate drift: " + row["path"])


def exports(text):
    result = []
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        names = [s.strip() for s in raw.split(",") if s.strip()]
        if len(set(names)) != len(names) or "sorryAx" in names:
            raise ValueError("Invalid axiom set: " + name)
        result.append({"theorem": name, "axioms": sorted(names)})
    return result


def package_revisions(root):
    manifest = json.loads((root / "proofs/lake-manifest.json").read_text())
    result = {}
    for package in manifest["packages"]:
        path = root / "proofs" / manifest["packagesDir"] / package["name"]
        actual = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        if actual != package["rev"]:
            raise ValueError("External package revision mismatch: " + package["name"])
        result[package["name"]] = actual
    return result


def kill_group(child):
    """SIGKILL the child's session. A group that is already exiting is not an
    error: Linux reports ESRCH, macOS reports EPERM once only zombies remain."""
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    except PermissionError:
        if child.poll() is None:
            # Still running after EPERM: wait for the exit already under way,
            # and re-raise only if it never comes.
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                raise


def command_run(command, log, env, deadline, stop):
    started = time.monotonic()
    started_unix = time.time()
    reason = None
    killed = False
    with log.open("xb") as stream:
        child = subprocess.Popen(command, env=env, stdout=stream, stderr=subprocess.STDOUT,
                                 start_new_session=True)
        try:
            while child.poll() is None:
                if stop.is_set() or time.monotonic() >= deadline:
                    reason = "STOP" if stop.is_set() else "TIMEOUT"
                    kill_group(child)
                    killed = True
                    break
                try:
                    child.wait(timeout=0.2)
                except subprocess.TimeoutExpired:
                    pass
        finally:
            # A second signal after SIGKILL only races the exit (EPERM on macOS).
            if not killed and child.poll() is None:
                kill_group(child)
            child.wait()
    row = {"command": command, "returncode": child.returncode, "stop_reason": reason,
           "elapsed_seconds": time.monotonic() - started, "log_sha256": sha(log),
           "started_unix": started_unix, "finished_unix": time.time()}
    save(log.with_suffix(".json"), row)
    if child.returncode or reason:
        raise RuntimeError("Failed process: " + str(log))
    return row


# Rough per-module wall-time estimates in seconds (attempt 1 receipts and the
# Oct 7/8 builder log). They only order ready work; they never gate it.
ESTIMATES = [
    (r"Erdos85OrderFortyNineSevenHighT1Rep0Certificate", 8149),
    (r"Erdos85OrderFortyNineSevenHighT[2-7]Rep\d+Certificate", 3000),
    (r"Erdos85H5T\dPart\d+", 2000),
    (r"Erdos85H3PairPart\d+", 1300),
    (r"Erdos85OrderFortyNineSevenHighCnf", 1011),
    (r"Erdos85SignedSRGSAT", 843),
    (r"Erdos85OrderFortyNineCanonicalMaskFibers", 609),
    (r"Erdos85H3TripleCompletionPart\d{3}", 20),
]


def estimate(name):
    for pattern, seconds in ESTIMATES:
        if re.fullmatch(pattern, name):
            return seconds
    return 30


def priorities(sources):
    """Longest estimated path from each module to the endpoint; the smoke part
    and its ancestors come first so a plugin failure surfaces within the first hour.
    Attempt 1 scheduled alphabetically and left the H7 certificate chain idle
    behind 35-minute searches for four hours."""
    users = {name: [] for name in sources}
    for name, row in sources.items():
        for dep in row["dependencies"]:
            users[dep].append(name)
    tail = {}

    def path(name):
        if name not in tail:
            tail[name] = estimate(name) + max([path(u) for u in users[name]] or [0])
        return tail[name]

    smoke, stack = {SMOKE} if SMOKE in sources else set(), [SMOKE] if SMOKE in sources else []
    while stack:
        for dep in sources[stack.pop()]["dependencies"]:
            if dep not in smoke:
                smoke.add(dep)
                stack.append(dep)
    return {name: (name in smoke, path(name)) for name in sources}


def build(plan, out, execution_commit=None):
    out.mkdir(exist_ok=False)
    fresh = out / "lean"
    (fresh / "Proofs").mkdir(parents=True)
    (out / "logs").mkdir()
    # Lean resolves the Proofs package root as a whole. A missing module in this
    # first empty root must fail; it cannot fall back to a seeded Proofs root.
    env = dict(os.environ)
    env["LEAN_PATH"] = str(fresh) + os.pathsep + env.get("LEAN_PATH", "")
    stop = threading.Event()
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, lambda *_: stop.set())
    started = time.monotonic()
    deadline = started + plan["limits"]["wall_seconds"]
    report = {"status": "RUNNING", "scope": plan["scope"], "sources": plan["sources"],
              "initial_project_objects": [], "lean_path": env["LEAN_PATH"],
              "lean_version": subprocess.check_output(["lean", "--version"], text=True).strip(),
              "completed": {}, "started_unix": time.time(), "output_root": str(out),
              "execution_commit_declared": execution_commit,
              "external_package_revisions": package_revisions(ROOT),
              "cgroup_memory_bytes": int(Path("/sys/fs/cgroup/memory.max").read_text()),
              "cgroup_cpu_max": Path("/sys/fs/cgroup/cpu.max").read_text().strip()}
    if "version 4.31.0" not in report["lean_version"] or "aarch64" not in report["lean_version"]:
        raise ValueError("Unexpected Lean toolchain: " + report["lean_version"])
    save(out / "plan.json", plan)
    library = out / "libH3TripleRuntime.so"

    def compile_one(name):
        source = Path("Proofs") / (name.replace(".", "/") + ".lean")
        obj = fresh / source.with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        if obj.exists() or sha(source) != plan["sources"][name]["sha256"]:
            raise ValueError("Source drift or preexisting object: " + name)
        command = ["lean", "-j1"]
        if re.fullmatch(r"Erdos85H3TripleCompletionPart\d{3}", name):
            if not library.exists():
                raise ValueError("Fresh native runtime plugin missing")
            command += ["--plugin=" + str(library) + "=" + INIT]
        command += [str(source), "-o", str(obj)]
        cfile = out / "H3TripleRuntime.c"
        if name == RUNTIME:
            command += ["-c", str(cfile)]
        log = out / "logs" / (name + ".log")
        row = command_run(command, log, env, deadline, stop)
        text = log.read_text(errors="replace")
        if re.search(r"\bsorry\b|\bsorryAx\b|\berror:", text):
            raise ValueError("Lean diagnostic: " + name)
        if not obj.is_file() or obj.is_symlink() or obj.stat().st_size == 0:
            raise ValueError("Missing fresh output: " + name)
        row.update({"source_sha256": sha(source), "object_sha256": sha(obj),
                    "object_bytes": obj.stat().st_size, "exports": exports(text),
                    "warning_count": len(re.findall(r"\bwarning:", text))})
        if name == RUNTIME:
            plugin_command = ["leanc", "-O3", "-DLEAN_EXPORTING", "-shared", "-fPIC",
                              str(cfile), "-o", str(library)]
            row["plugin_build"] = command_run(plugin_command, out / "logs/plugin.log", env,
                                               min(deadline, time.monotonic() + 120), stop)
            if INIT not in cfile.read_text(errors="replace"):
                raise ValueError("Runtime C does not define plugin initializer " + INIT)
            row["runtime_c_sha256"] = sha(cfile)
            row["plugin_sha256"] = sha(library)
        if name == plan["endpoint"] and row["exports"] != plan["expected_exports"]:
            raise ValueError("Endpoint axiom set differs from accepted evidence")
        return row

    pending = set(plan["sources"])
    rank = priorities(plan["sources"])
    active = {}
    pool = concurrent.futures.ThreadPoolExecutor(max_workers=plan["limits"]["workers"])
    try:
        probe = out / "ColdIsolationProbe.lean"
        probe.write_text("import Proofs." + plan["endpoint"] + "\n")
        probe_log = out / "logs/isolation-probe.log"
        try:
            command_run(["lean", "-j1", str(probe)], probe_log, env,
                        min(deadline, time.monotonic() + 30), stop)
        except RuntimeError:
            receipt = json.loads(probe_log.with_suffix(".json").read_text())
            text = probe_log.read_text(errors="replace")
            missing = fresh / "Proofs" / (plan["endpoint"] + ".olean")
            if receipt["stop_reason"] or str(missing) not in text or "does not exist" not in text:
                raise ValueError("Isolation probe failed for an unexpected reason")
            report["isolation_probe"] = {"status": "PASS_EXPECTED_MISSING_FRESH_OBJECT", **receipt}
        else:
            raise ValueError("Cold isolation failed: endpoint imported before any compilation")
        save(out / "RUN.json", report)
        while pending or active:
            if (out / "STOP").exists() or stop.is_set() or time.monotonic() >= deadline:
                raise RuntimeError("STOP or overall time limit")
            for future in list(active):
                if future.done():
                    name = active.pop(future)
                    report["completed"][name] = future.result()
                    save(out / "RUN.json", report)
                    print(json.dumps({"compiled": name, "complete": len(report["completed"])}), flush=True)
            # No memory reservations: the Oct 7/8 builder compiled all 13 H7
            # certificates concurrently at a ~20 GB peak; the 110 GiB cgroup is the bound.
            for name in sorted(pending, key=lambda n: (rank[n], n), reverse=True):
                if len(active) >= plan["limits"]["workers"]:
                    break
                if not set(plan["sources"][name]["dependencies"]) <= report["completed"].keys():
                    continue
                active[pool.submit(compile_one, name)] = name
                pending.remove(name)
            if pending and not active:
                raise ValueError("Unresolvable build dependency graph")
            if active:
                concurrent.futures.wait(active, timeout=1, return_when=concurrent.futures.FIRST_COMPLETED)
        validate_inputs(plan, ROOT)
        if package_revisions(ROOT) != report["external_package_revisions"]:
            raise ValueError("External package revisions changed during build")
        for name, row in report["completed"].items():
            obj = fresh / "Proofs" / (name.replace(".", "/") + ".olean")
            if sha(obj) != row["object_sha256"]:
                raise ValueError("Object drift: " + name)
        if len(report["completed"]) != 893:
            raise ValueError("Incomplete project closure")
        report["status"] = "COLD_PROJECT_BUILD_COMPLETE_PENDING_AUDIT"
    except BaseException as exc:
        stop.set()
        report["status"] = "FAILED"
        report["error"] = repr(exc)
        raise
    finally:
        stop.set()
        pool.shutdown(wait=True, cancel_futures=True)
        report["elapsed_seconds"] = time.monotonic() - started
        report["finished_unix"] = time.time()
        report["unfinished"] = sorted(set(plan["sources"]) - report["completed"].keys())
        save(out / "RUN.json", report)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--execution-commit", required=True,
                        help="Full host job commit; terminal auditor binds this to retained host job.sha")
    parser.add_argument("--execute-plan", help="Exact SHA256 of reviewed plan; not itself spending authorization")
    args = parser.parse_args()
    plan = json.loads(args.plan.read_text())
    if not re.fullmatch(r"[0-9a-f]{40}", args.execution_commit):
        raise ValueError("Full execution commit required")
    # /workspace is a linked worktree: its .git pointer refers to host-only
    # /opt/lean-genius metadata. Bind source/code bytes here, and bind the host
    # execution identity to its retained job.sha in the terminal audit.
    if not Path("/.dockerenv").exists() or Path.cwd() != Path("/workspace/proofs"):
        raise RuntimeError("Cloud container /workspace/proofs required; local Lean execution prohibited")
    limits = plan["limits"]
    if limits != {"workers": 12, "memory_gib": 110, "cpus": 16, "wall_seconds": 35400}:
        raise ValueError("Unreviewed resource limits")
    memory = int(Path("/sys/fs/cgroup/memory.max").read_text())
    quota, period = map(int, Path("/sys/fs/cgroup/cpu.max").read_text().split())
    if memory != 110 * 1024 ** 3 or quota != 16 * period:
        raise ValueError("Unexpected cgroup resource limits")
    validate_inputs(plan, ROOT)
    if args.output.exists():
        raise ValueError("Refusing existing output directory")
    if args.execute_plan is None:
        print(json.dumps({"status": "READ_ONLY_PREFLIGHT_PASS", "sources": len(plan["sources"]),
                          "plan_sha256": sha(args.plan), "scope": "No compilation or launch authorization"}))
        return
    if args.execute_plan != sha(args.plan):
        raise ValueError("Plan identity mismatch")
    build(plan, args.output.resolve(), args.execution_commit)


if __name__ == "__main__":
    main()
