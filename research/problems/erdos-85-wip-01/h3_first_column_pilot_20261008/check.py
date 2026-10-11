"""Run one U1/R15 first-column certificate on the cloud, without retries."""

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
RESEARCH = PACKAGE.parent
NAME = "Erdos85ThreeHighFirstColumnPilotCertificate"
THEOREM = "Erdos85.FirstColumnPilot.rejected"
AXIOMS = {"propext", "Classical.choice", "Quot.sound",
          THEOREM + "._native.native_decide.ax_1_1"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def plan():
    evidence = RESEARCH / "h3_first_column_20261008/evidence"
    receipt = json.loads((evidence / "RUN.json").read_text())
    audit = json.loads((evidence / "AUDIT.json").read_text())
    if (receipt["status"] != "PASS" or audit["status"] != "PASS"
            or audit["receipt_sha256"] != digest(evidence / "RUN.json")):
        raise ValueError("Audited candidate inventory is required")
    case, = [row for row in receipt["cases"] if row["case"] == "FullU1R15"]
    if case["static_count"] != 15 or [1, True] not in case["columns_mask_and_prefix_pass"]:
        raise ValueError("Selected first column is not in the audited candidate list")
    original = RESEARCH / "h3_formal_20261007/Erdos85ThreeHighNativeTerminalPilotCertificate.lean"
    source = PACKAGE / (NAME + ".lean")
    pattern = r"def U :.*?(?=\n\ndef S|\n\nset_option)"
    if re.search(pattern, original.read_text(), re.S)[0] != re.search(pattern, source.read_text(), re.S)[0]:
        raise ValueError("Pilot U/R definitions differ from the whole-pair source")
    if "def S : Finset (Fin 15) := {0}" not in source.read_text():
        raise ValueError("Unexpected first-column source")
    return {"case": "FullU1R15", "column_mask": 1,
            "inventory_receipt_sha256": digest(evidence / "RUN.json"),
            "whole_pair_source_sha256": digest(original), "source_sha256": digest(source)}


def run(command, log, env):
    started = time.monotonic()
    utc = datetime.now(timezone.utc).isoformat()
    with log.open("w") as handle:
        child = subprocess.Popen(command, env=env, stdout=handle, stderr=subprocess.STDOUT)
        _, status, usage = os.wait4(child.pid, 0)
        child.returncode = os.waitstatus_to_exitcode(status)
    return {"command": command, "started_utc": utc, "exit_code": child.returncode,
            "elapsed_seconds": time.monotonic() - started,
            "user_cpu_seconds": usage.ru_utime, "system_cpu_seconds": usage.ru_stime,
            "max_rss_kib": usage.ru_maxrss, "log_sha256": digest(log)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    provenance = plan()
    if args.plan:
        print(json.dumps(provenance, indent=2))
        return 0
    if not Path("/.dockerenv").exists() or not Path("Proofs").is_dir():
        parser.error("Run from proofs inside the cloud Docker environment")
    if args.output is None:
        parser.error("--output is required")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = PACKAGE / (NAME + ".lean")
    shutil.copyfile(source, output / source.name)
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    receipt = {"status": "RUNNING", "plan": provenance, "lean_threads": 1,
               "scope": "Only U1/R15 first column {0}; not a whole-pair or H3 exclusion.",
               "memory_scope": "Linux wait4 maximum RSS of Lake and its waited children, not aggregate concurrent container memory."}

    def save():
        temporary = output / "RUN.json.tmp"
        temporary.write_text(json.dumps(receipt, indent=2) + "\n")
        temporary.replace(output / "RUN.json")

    save()
    receipt["dependencies"] = run([
        "lake", "build", "Proofs.Erdos85ThreeHighFirstColumnSearch",
        "Proofs.Erdos85ThreeBlockCompactCodes", "Proofs.Erdos85ThreeHighSecondaryOrbitTable"],
        output / "dependencies.log", env)
    if receipt["dependencies"]["exit_code"]:
        receipt["status"] = "DEPENDENCY_FAILURE"
        save()
        return 1
    save()
    target = Path("Proofs") / source.name
    shutil.copyfile(source, target)
    log = output / (NAME + ".log")
    receipt["certificate"] = run(["lake", "build", "Proofs." + NAME], log, env)
    obj = Path(".lake/build/lib/lean/Proofs") / (NAME + ".olean")
    text = log.read_text()
    reports = re.findall("'" + re.escape(THEOREM) + r"' depends on axioms: \[([^\]]*)\]", text)
    axioms = [a.strip() for a in reports[0].split(",")] if len(reports) == 1 else []
    passed = (receipt["certificate"]["exit_code"] == 0 and obj.is_file()
              and len(reports) == 1 and set(axioms) == AXIOMS and "sorry" not in text.lower()
              and source.read_bytes() == target.read_bytes() == (output / source.name).read_bytes()
              and digest(source) == provenance["source_sha256"])
    receipt.update(status="PASS" if passed else "FAIL", axiom_exports=[{
        "theorem": THEOREM, "axioms": axioms}],
        olean_path=str(obj.resolve()), olean_sha256=digest(obj) if obj.is_file() else None)
    save()
    print(json.dumps(receipt), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
