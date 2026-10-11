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
INIT = "initialize_proofs_Proofs_Erdos85H3TripleCompletionRuntime"


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


def command_run(command, log, env, deadline, stop):
    started = time.monotonic()
    started_unix = time.time()
    reason = None
    with log.open("xb") as stream:
        child = subprocess.Popen(command, env=env, stdout=stream, stderr=subprocess.STDOUT,
                                 start_new_session=True)
        try:
            while child.poll() is None:
                if stop.is_set() or time.monotonic() >= deadline:
                    reason = "STOP" if stop.is_set() else "TIMEOUT"
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    break
                try:
                    child.wait(timeout=0.2)
                except subprocess.TimeoutExpired:
                    pass
        finally:
            if child.poll() is None:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            child.wait()
    row = {"command": command, "returncode": child.returncode, "stop_reason": reason,
           "elapsed_seconds": time.monotonic() - started, "log_sha256": sha(log),
           "started_unix": started_unix, "finished_unix": time.time()}
    save(log.with_suffix(".json"), row)
    if child.returncode or reason:
        raise RuntimeError("Failed process: " + str(log))
    return row


def weight(name):
    # Keep large packed-certificate compilation from overlapping another large
    # certificate. The cgroup is the hard limit; these are scheduler reservations.
    return 64 if re.fullmatch(r"Erdos85OrderFortyNineSevenHighT[1-7]Rep[0-2]Certificate", name) else 16


def build(plan, out):
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
                    "object_bytes": obj.stat().st_size, "exports": exports(text)})
        if name == RUNTIME:
            plugin_command = ["leanc", "-O3", "-DLEAN_EXPORTING", "-shared", "-fPIC",
                              str(cfile), "-o", str(library)]
            row["plugin_build"] = command_run(plugin_command, out / "logs/plugin.log", env,
                                               min(deadline, time.monotonic() + 120), stop)
            row["runtime_c_sha256"] = sha(cfile)
            row["plugin_sha256"] = sha(library)
        if name == plan["endpoint"] and row["exports"] != plan["expected_exports"]:
            raise ValueError("Endpoint axiom set differs from accepted evidence")
        return row

    pending = set(plan["sources"])
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
            reserved = sum(weight(n) for n in active.values())
            for name in sorted(pending):
                if len(active) >= plan["limits"]["workers"]:
                    break
                if reserved + weight(name) > 96:
                    continue
                if not set(plan["sources"][name]["dependencies"]) <= report["completed"].keys():
                    continue
                active[pool.submit(compile_one, name)] = name
                pending.remove(name)
                reserved += weight(name)
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
    parser.add_argument("--execute-plan", help="Exact SHA256 of reviewed plan; not itself spending authorization")
    args = parser.parse_args()
    plan = json.loads(args.plan.read_text())
    actual_commit = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
    if actual_commit != plan["source_commit"]:
        # The reviewed plan may be committed on top of its frozen source commit;
        # validate_inputs still requires exact source, config and artifact bytes.
        subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                        plan["source_commit"], actual_commit], check=True)
    if not Path("/.dockerenv").exists() or Path.cwd() != Path("/workspace/proofs"):
        raise RuntimeError("Cloud container /workspace/proofs required; local Lean execution prohibited")
    limits = plan["limits"]
    if limits != {"workers": 6, "memory_gib": 110, "cpus": 16, "wall_seconds": 35400}:
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
    build(plan, args.output.resolve())


if __name__ == "__main__":
    main()
