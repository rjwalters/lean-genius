"""Run one preflight-verified varied H3 pair on the cloud, without retries."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

PACKAGE = Path(__file__).resolve().parent
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def reports(text):
    return [{"theorem": n, "axioms": [x.strip() for x in (ax or "").split(",") if x.strip()]}
            for n, ax in re.findall(
                r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", text)]


def preflight(case_name, evidence):
    plan = json.loads((PACKAGE / "PLAN.json").read_text())
    case, = [c for c in plan["cases"] if c["namespace"].split(".")[-1] == case_name]
    receipt = json.loads((evidence / "RUN.json").read_text())
    audit = json.loads((evidence / "AUDIT.json").read_text())
    if (receipt["status"] != "PASS" or audit["status"] != "PASS"
            or audit["run_sha256"] != digest(evidence / "RUN.json")
            or receipt["plan_sha256"] != digest(PACKAGE / "PLAN.json")):
        raise ValueError("An independently audited, matching preflight is required")
    names = [r["module"] for r in receipt["results"]]
    if len(names) != len(set(names)):
        raise ValueError("Repeated preflight module")
    entries = {r["module"]: r for r in receipt["results"]}
    input_name = case["module_prefix"] + "Inputs"
    membership_name = case["branch"].title() + "Membership"
    for name in [input_name, membership_name]:
        entry = entries[name]
        source = PACKAGE / (name + ".lean")
        if entry["status"] != "PASS" or entry["exit_code"] != 0:
            raise ValueError("Failed preflight module")
        if not digest(source) == entry["source_sha256"] == digest(evidence / source.name):
            raise ValueError("Preflight source changed")
        if digest(evidence / (name + ".log")) != entry["log_sha256"]:
            raise ValueError("Preflight log changed")
    member = entries[membership_name]
    actual = reports((evidence / (membership_name + ".log")).read_text())
    if actual != member["axiom_exports"] or any(set(r["axioms"]) - STANDARD for r in actual):
        raise ValueError("Invalid preflight axiom reports")
    required = {case_name + "_mem", case_name + "_input"}
    if not required <= {r["theorem"] for r in actual}:
        raise ValueError("Selected pair has no verified membership/identity")
    for suffix in ["Inputs", "Certificate", "Consumer"]:
        filename = case["module_prefix"] + suffix + ".lean"
        if digest(PACKAGE / filename) != plan["generated_source_sha256"][filename]:
            raise ValueError("Selected source differs from the prepared census plan")
    return case, digest(evidence / "RUN.json")


def run(command, log, env):
    start = time.monotonic()
    utc = datetime.now(timezone.utc).isoformat()
    with log.open("w") as handle:
        child = subprocess.Popen(command, env=env, stdout=handle, stderr=subprocess.STDOUT)
        _, status, usage = os.wait4(child.pid, 0)
        child.returncode = os.waitstatus_to_exitcode(status)
    return {"command": command, "started_utc": utc, "exit_code": child.returncode,
            "elapsed_seconds": time.monotonic() - start,
            "user_cpu_seconds": usage.ru_utime, "system_cpu_seconds": usage.ru_stime,
            "max_rss_kib": usage.ru_maxrss, "log_sha256": digest(log)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", required=True)
    parser.add_argument("--membership-evidence", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--plan", action="store_true")
    args = parser.parse_args()
    case, preflight_sha = preflight(args.case, args.membership_evidence.resolve())
    if args.plan:
        print(json.dumps({"case": case, "preflight_sha256": preflight_sha}, indent=2))
        return 0
    if not Path("/.dockerenv").exists() or not Path("Proofs").is_dir():
        parser.error("Run inside the cloud Docker environment from proofs")
    if args.output is None:
        parser.error("--output required")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    receipt = {"status": "RUNNING", "case": case, "preflight_sha256": preflight_sha,
               "lean_threads": 1, "results": [],
               "scope": "One complete varied pair; not a full H3 exclusion.",
               "memory_scope": "Linux wait4 maximum RSS of each Lake process and its waited children; not aggregate concurrent memory."}

    def save():
        tmp = output / "RUN.json.tmp"
        tmp.write_text(json.dumps(receipt, indent=2) + "\n")
        tmp.replace(output / "RUN.json")

    save()
    # Copy only the input before its build; certificate and consumer are introduced
    # separately so their object and timing records remain independently recoverable.
    for suffix in ["Inputs", "Certificate", "Consumer"]:
        name = case["module_prefix"] + suffix
        source = PACKAGE / (name + ".lean")
        target = Path("Proofs") / source.name
        shutil.copyfile(source, target)
        shutil.copyfile(source, output / source.name)
        receipt["active_module"] = name
        save()
        log = output / (name + ".log")
        entry = run(["lake", "build", "Proofs." + name], log, env)
        obj = Path(".lake/build/lib/lean/Proofs") / (name + ".olean")
        selected = []
        passed = (entry["exit_code"] == 0 and obj.is_file()
                  and source.read_bytes() == target.read_bytes() == (output / source.name).read_bytes()
                  and "sorry" not in log.read_text().lower())
        if suffix != "Inputs":
            theorem = case["namespace"] + (".rejected" if suffix == "Certificate" else ".no_joint")
            selected = [r for r in reports(log.read_text()) if r["theorem"] == theorem]
            native = case["namespace"] + ".rejected._native.native_decide.ax_1_1"
            passed = passed and len(selected) == 1 and set(selected[0]["axioms"]) == STANDARD | {native}
        entry.update(module=name, status="PASS" if passed else "FAIL",
                     source_sha256=digest(source), olean_sha256=digest(obj) if obj.is_file() else None,
                     axiom_exports=selected)
        (output / (name + ".run.json")).write_text(json.dumps(entry, indent=2) + "\n")
        receipt["results"].append(entry)
        del receipt["active_module"]
        if not passed:
            receipt["status"] = "MODULE_FAILURE"
        save()
        print(json.dumps(entry), flush=True)
        if not passed:
            return 1
    receipt["status"] = "PASS"
    save()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
