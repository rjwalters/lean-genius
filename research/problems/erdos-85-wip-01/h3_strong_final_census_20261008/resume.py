"""Continue a stopped Full261 check without discarding verified prefix work.

First capture a terminal record on the cloud host. Only after that, run inside
cloud Docker with --base-build, --output (the original path), --snapshot (new),
and --terminal-record. The prior output is copied and checked before mutation.
No running job is stopped, no timeout is extended, and no job is submitted here.
"""

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
PACKAGE = Path(__file__).resolve().parent
RESEARCH = PACKAGE.parent
REPOSITORY = RESEARCH.parents[2]
JOBS = Path("/opt/e85/jobs")
HOST_REPOSITORY = Path("/opt/e85/wt/erdos85__h3-census-20261008")
CONTAINER_REPOSITORY = Path("/workspace")


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


audit = load("final_audit", PACKAGE / "audit.py")
checker = load("final_check", PACKAGE / "check.py")
require, digest, read_json = audit.require, audit.digest, audit.read_json


def capture_terminal(job, output, record):
    require(not Path("/.dockerenv").exists(), "Capture terminal state on the cloud host")
    require(re.fullmatch(r"\d{8}T\d{6}-erdos85__h3-census-20261008-\d+", job),
            "Unexpected census job ID")
    directory = JOBS / job
    exit_path = directory / "exit"
    require(exit_path.is_file(), "Job has no authoritative terminal exit record")
    code = int(exit_path.read_text().strip())
    require(code != 0, "Do not resume a successful job")
    pid = int((directory / "pid").read_text().strip())
    require(not Path(f"/proc/{pid}").exists(), "Original job process is still present")
    log = (directory / "log").read_text()
    commit = re.search(r"^\[e85\] commit ([0-9a-f]{40}) ", log, re.M)
    require(commit is not None, "No execution commit in job log")
    command_match = re.search(r"^Command: (.+)$", log, re.M)
    require(command_match is not None, "No command in terminal job log")
    command = shlex.split(command_match[1])
    require(command[:3] == ["lake", "env", "python3"] and len(command) > 3,
            "Terminal job was not a final census check")
    script = Path(os.path.normpath(CONTAINER_REPOSITORY / "proofs" / command[3]))
    scripts = {CONTAINER_REPOSITORY / "research/problems/erdos-85-wip-01" /
               "h3_strong_final_census_20261008" / name for name in ["check.py", "resume.py"]}
    require(script in scripts, "Unexpected terminal job script")
    require(command.count("--output") == 1, "No unique terminal output argument")
    index = command.index("--output")
    require(index + 1 < len(command), "Missing terminal output path")
    recorded_output = Path(os.path.normpath(
        CONTAINER_REPOSITORY / "proofs" / command[index + 1]))
    require(recorded_output.is_relative_to(CONTAINER_REPOSITORY), "Output outside repository")
    expected_output = HOST_REPOSITORY / recorded_output.relative_to(CONTAINER_REPOSITORY)
    require(output == expected_output, "Terminal job output does not match requested output")
    require(output.is_dir(), "Missing census output")
    record.parent.mkdir(parents=True, exist_ok=True)
    with record.open("x") as handle:
        json.dump({"status": "TERMINAL", "job": job, "exit_code": code,
                   "execution_commit": commit[1], "job_pid_absent": pid,
                   "recorded_output": str(recorded_output),
                   "job_log_sha256": digest(directory / "log"),
                   "job_exit_sha256": digest(exit_path),
                   "build_receipt_sha256": digest(output / "RUN.json")}, handle, indent=2)
        handle.write("\n")
    print(json.dumps(read_json(record)), flush=True)


def library_unchanged(commit, library):
    paths, pending = set(), list(library)
    while pending:
        module = pending.pop()
        if not module.startswith("Proofs."):
            continue
        path = Path("proofs") / (module.replace(".", "/") + ".lean")
        if str(path) in paths:
            continue
        paths.add(str(path))
        source = REPOSITORY / path
        require(source.is_file(), f"Missing library source: {path}")
        pending.extend(checker.census.imports(source))
    paths.update({"proofs/lean-toolchain", "proofs/lake-manifest.json",
                  "proofs/lakefile.lean", "proofs/lakefile.toml"})
    changed = subprocess.check_output(
        ["git", "diff", "--name-only", commit, "--", "proofs"],
        cwd=REPOSITORY, text=True).splitlines()
    require(not set(changed) & paths,
            f"Library/toolchain inputs changed: {sorted(set(changed) & paths)}")
    return len(paths)


def validate_prefix(output, sources, library, recorded_output=None):
    recorded_output = recorded_output or output
    receipt_hash = digest(output / "RUN.json")
    receipt = read_json(output / "RUN.json")
    require(receipt["status"] in {"RUNNING", "MODULE_FAILURE"},
            "Only an interrupted or failed module check can be continued")
    require(receipt["lean_threads"] == 1, "Unexpected compiler thread setting")
    expected_inputs = {n: {"source": str(p.relative_to(RESEARCH)), "sha256": digest(p)}
                       for n, p in sources}
    require(receipt["inputs"] == expected_inputs, "Planned source inventory changed")
    require(receipt["dependency_build"] == {
        "command": ["lake", "build", *library], "exit_code": 0,
        "log_sha256": digest(output / "dependencies.log")}, "Dependency evidence mismatch")
    entries = receipt["results"]
    require(len(entries) <= len(sources), "Too many recorded results")
    require([r["module"] for r in entries] == [n for n, _ in sources[:len(entries)]],
            "Recorded results are not the exact dependency prefix")
    passed = []
    for index, entry in enumerate(entries):
        name, source = sources[index]
        if entry["status"] != "PASS":
            require(index == len(entries) - 1 and receipt["status"] == "MODULE_FAILURE",
                    "Failure is not the final recorded module")
            require(entry["status"] == "FAIL", "Unknown failed-module status")
            break
        require(entry["exit_code"] == 0, f"Nonzero prefix exit: {name}")
        require(read_json(output / (name + ".run.json")) == entry,
                f"Individual receipt mismatch: {name}")
        require(entry["source"] == expected_inputs[name]["source"], f"Wrong source: {name}")
        require(entry["source_sha256"] == expected_inputs[name]["sha256"], f"Changed source: {name}")
        for suffix, key in [(".lean", "source_sha256"), (".log", "log_sha256"),
                            (".olean", "olean_sha256")]:
            require(digest(output / (name + suffix)) == entry[key], f"Changed {name}{suffix}")
        target = recorded_output / (name + ".lean")
        require(entry["command"] == ["lean", "-R", str(recorded_output), "-o",
                str(target.with_suffix(".olean")), str(target)], f"Wrong command: {name}")
        text = (output / (name + ".log")).read_text()
        require("sorry" not in text.lower(), f"Sorry in log: {name}")
        reports = [{"theorem": m[1], "axioms": [a.strip() for a in (m[2] or "").split(",")
                    if a.strip()]} for m in audit.REPORT.finditer(text)]
        require(reports == entry["axiom_exports"], f"Axiom records differ: {name}")
        expected = re.findall(r"^#print axioms (\S+)\s*$", source.read_text(), re.M)
        require(len(reports) == len(expected), f"Missing axiom report: {name}")
        for actual, wanted in zip(reports, expected):
            require(actual["theorem"] == wanted or actual["theorem"].endswith("." + wanted),
                    f"Wrong axiom export: {name}")
            require(set(actual["axioms"]) <= audit.STANDARD, f"Nonstandard axiom: {name}")
        passed.append(entry)
    require(len(passed) < len(sources), "All modules already passed; audit instead")
    require(digest(output / "RUN.json") == receipt_hash, "Receipt changed during validation")
    return receipt, passed, receipt_hash


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture-terminal", metavar="JOB")
    parser.add_argument("--terminal-record", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--base-build", type=Path)
    parser.add_argument("--snapshot", type=Path)
    args = parser.parse_args()
    output, terminal_path = args.output.resolve(), args.terminal_record.resolve()
    if args.capture_terminal:
        capture_terminal(args.capture_terminal, output, terminal_path)
        return 0
    require(Path("/.dockerenv").exists() and Path("Proofs").is_dir(),
            "Resume only inside cloud Docker from proofs")
    require(args.base_build is not None and args.snapshot is not None,
            "--base-build and --snapshot are required")
    base_build, snapshot = args.base_build.resolve(), args.snapshot.resolve()
    require(not snapshot.exists() and snapshot != output and output not in snapshot.parents
            and snapshot not in output.parents, "Snapshot must be a fresh, separate directory")
    terminal = read_json(terminal_path)
    require(terminal["status"] == "TERMINAL" and terminal["exit_code"] != 0,
            "Missing failed/timeout terminal-job record")
    require(terminal["recorded_output"] == str(output), "Terminal record is for another output")
    require(digest(output / "RUN.json") == terminal["build_receipt_sha256"],
            "Build changed after terminal capture")
    base, sources, library = checker.plan()
    library_files = library_unchanged(terminal["execution_commit"], library)
    _, _, base_library = checker.census.plan("full")
    base_receipt = read_json(base_build / "RUN.json")
    require(base_receipt["branch"] == "full" and base_receipt["shard_count"] == 100,
            "Wrong prerequisite branch/shard count")
    base_audit = audit.audit_build(base_build, base, base_library, RESEARCH, base_build)
    receipt, prefix, prior_sha = validate_prefix(output, sources, library)
    require(receipt["base_build"] == str(base_build)
            and receipt["base_receipt_sha256"] == base_audit["receipt_sha256"],
            "Prerequisite census mismatch")
    shutil.copytree(output, snapshot)
    _, copied_prefix, copied_sha = validate_prefix(snapshot, sources, library, output)
    require(copied_sha == prior_sha and copied_prefix == prefix, "Snapshot failed validation")
    receipt["results"] = prefix
    receipt["status"] = "RUNNING"
    receipt.setdefault("continuations", []).append({
        "terminal": terminal, "snapshot": str(snapshot), "prior_receipt_sha256": prior_sha,
        "reused_modules": len(prefix), "unchanged_library_inputs": library_files})

    def save():
        tmp = output / "RUN.json.tmp"
        tmp.write_text(json.dumps(receipt, indent=2) + "\n")
        tmp.replace(output / "RUN.json")

    save()
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["LEAN_PATH"] = os.pathsep.join((str(output), str(base_build), env.get("LEAN_PATH", "")))
    for name, source in sources[len(prefix):]:
        entry = checker.compile_one(name, source, output, env)
        receipt["results"].append(entry)
        if entry["status"] != "PASS":
            receipt["status"] = "MODULE_FAILURE"
        save()
        print(json.dumps({"module": name, "status": entry["status"]}), flush=True)
        if entry["status"] != "PASS":
            return 1
    checker.verify_base(base_build, base)
    receipt["status"] = "PASS"
    save()
    final = audit.audit_build(output, sources, library, RESEARCH, output)
    require(digest(base_build / "RUN.json") == base_audit["receipt_sha256"],
            "Prerequisite changed during continuation")
    print(json.dumps({"status": "PASS", "base": base_audit, "final": final}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
