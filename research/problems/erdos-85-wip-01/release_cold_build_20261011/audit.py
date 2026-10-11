"""Read-only check of a terminal cold-build bundle; does not run Lean."""
import argparse
import json
import re
from pathlib import Path

from prepare import ROOT, sha
from run import INIT, RUNTIME, exports, validate_inputs


def audit(plan, out):
    report = json.loads((out / "RUN.json").read_text())
    if report["status"] != "COLD_PROJECT_BUILD_COMPLETE_PENDING_AUDIT":
        raise ValueError("Run is not complete")
    if json.loads((out / "plan.json").read_text()) != plan or report["sources"] != plan["sources"]:
        raise ValueError("Run/plan identity mismatch")
    validate_inputs(plan, ROOT)
    completed = report["completed"]
    original = Path(report["output_root"])
    quota, period = map(int, report["cgroup_cpu_max"].split())
    if report["cgroup_memory_bytes"] != 110 * 1024 ** 3 or quota != 16 * period:
        raise ValueError("Resource receipt mismatch")
    packages = json.loads((ROOT / "proofs/lake-manifest.json").read_text())["packages"]
    if report["external_package_revisions"] != {p["name"]: p["rev"] for p in packages}:
        raise ValueError("External package receipt mismatch")
    if len(completed) != 893 or set(completed) != set(plan["sources"]) or report["unfinished"]:
        raise ValueError("Incomplete source coverage")
    if report["initial_project_objects"] or report["elapsed_seconds"] > plan["limits"]["wall_seconds"] + 30:
        raise ValueError("Initial objects or elapsed-time violation")
    probe = report["isolation_probe"]
    if probe["status"] != "PASS_EXPECTED_MISSING_FRESH_OBJECT" or not probe["returncode"] or probe["stop_reason"]:
        raise ValueError("Isolation probe not accepted")
    if sha(out / "logs/isolation-probe.log") != probe["log_sha256"]:
        raise ValueError("Isolation log drift")
    for name, row in completed.items():
        obj = out / "lean/Proofs" / (name.replace(".", "/") + ".olean")
        log = out / "logs" / (name + ".log")
        if obj.is_symlink() or sha(obj) != row["object_sha256"] or obj.stat().st_size != row["object_bytes"]:
            raise ValueError("Object drift: " + name)
        if sha(log) != row["log_sha256"] or row["returncode"] or row["stop_reason"]:
            raise ValueError("Compile/log failure: " + name)
        if not report["started_unix"] <= row["started_unix"] <= row["finished_unix"] <= report["finished_unix"]:
            raise ValueError("Invalid compile timestamps: " + name)
        if row["source_sha256"] != plan["sources"][name]["sha256"]:
            raise ValueError("Source hash mismatch: " + name)
        for dep in plan["sources"][name]["dependencies"]:
            if completed[dep]["finished_unix"] > row["started_unix"]:
                raise ValueError("Dependency compiled too late: " + name)
        command = row["command"]
        expected = ["lean", "-j1"]
        if re.fullmatch(r"Erdos85H3TripleCompletionPart\d{3}", name):
            expected += ["--plugin=" + str(original / "libH3TripleRuntime.so") + "=" + INIT]
            if completed[RUNTIME]["plugin_build"]["finished_unix"] > row["started_unix"]:
                raise ValueError("Runtime plugin not fresh before part")
        remote_obj = original / "lean/Proofs" / (name.replace(".", "/") + ".olean")
        expected += ["Proofs/" + name.replace(".", "/") + ".lean", "-o", str(remote_obj)]
        if name == RUNTIME:
            expected += ["-c", str(original / "H3TripleRuntime.c")]
        if command != expected:
            raise ValueError("Unexpected build command: " + name)
        text = log.read_text(errors="replace")
        if re.search(r"\bsorry\b|\bsorryAx\b|\berror:", text) or exports(text) != row["exports"]:
            raise ValueError("Lean log/axiom mismatch: " + name)
    runtime = completed[RUNTIME]
    if sha(out / "H3TripleRuntime.c") != runtime["runtime_c_sha256"] or sha(out / "libH3TripleRuntime.so") != runtime["plugin_sha256"]:
        raise ValueError("Runtime C/plugin drift")
    plugin = runtime["plugin_build"]
    if plugin["returncode"] or plugin["stop_reason"] or sha(out / "logs/plugin.log") != plugin["log_sha256"]:
        raise ValueError("Runtime plugin compilation failed")
    if completed[plan["endpoint"]]["exports"] != plan["expected_exports"]:
        raise ValueError("Headline axioms differ from accepted evidence")
    return {"status": "COLD_PROJECT_BUILD_AUDIT_PASS", "source_count": len(completed),
            "axiom_counts": [len(x["axioms"]) for x in completed[plan["endpoint"]]["exports"]],
            "run_sha256": sha(out / "RUN.json"), "scope": plan["scope"],
            "elapsed_seconds": report["elapsed_seconds"]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    print(json.dumps(audit(json.loads(args.plan.read_text()), args.output.resolve()), indent=2))
