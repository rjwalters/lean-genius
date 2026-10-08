"""Compile the U1/R15 rejection and its consumer as separate cloud modules.

Retains the rejection object even if the later consumer fails. Does not retry
or launch other pairs. The original failed run is separate evidence.
"""

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
SOURCES = PACKAGE.parent / "h3_formal_20261007"
EXPECTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound",
                   "Erdos85.NativeTerminalPilot.rejected._native.native_decide.ax_1_1"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
    if not Path("/.dockerenv").exists():
        raise SystemExit("Run inside the cloud Docker environment.")
    if not Path("lakefile.lean").is_file() and not Path("lakefile.toml").is_file():
        raise SystemExit("Run from the proofs directory.")
    output = PACKAGE / "_build/split-first"
    output.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    receipt = {"status": "RUNNING", "lean_threads": 1,
               "scope": "One full U1/R15 pair; not a full H3 exclusion.",
               "memory_scope": "Linux wait4 maximum RSS for each Lake process and its waited children; not aggregate concurrent container memory.",
               "results": []}

    def save():
        temporary = output / "RUN.json.tmp"
        temporary.write_text(json.dumps(receipt, indent=2) + "\n")
        temporary.replace(output / "RUN.json")

    save()
    receipt["dependency_build"] = run([
        "lake", "build", "Proofs.Erdos85ThreeHighNativePairSearch",
        "Proofs.Erdos85ThreeBlockCompactCodes", "Proofs.Erdos85ThreeHighSecondaryOrbitTable"],
        output / "dependencies.log", env)
    if receipt["dependency_build"]["exit_code"]:
        receipt["status"] = "DEPENDENCY_FAILURE"
        save()
        return 1
    save()
    for name, theorem in (
            ("Erdos85ThreeHighNativeTerminalPilotCertificate", "Erdos85.NativeTerminalPilot.rejected"),
            ("Erdos85ThreeHighNativeTerminalPilot", "Erdos85.NativeTerminalPilot.no_joint")):
        source = SOURCES / (name + ".lean")
        target = Path("Proofs") / (name + ".lean")
        shutil.copyfile(source, target)
        shutil.copyfile(source, output / (name + ".lean"))
        receipt["active_module"] = name
        save()
        log = output / (name + ".log")
        entry = run(["lake", "build", "Proofs." + name], log, env)
        obj = Path(".lake/build/lib/lean/Proofs") / (name + ".olean")
        text = log.read_text()
        matches = re.findall("'" + re.escape(theorem) + r"' depends on axioms: \[([^\]]*)\]", text)
        axioms = [a.strip() for a in matches[0].split(",")] if len(matches) == 1 else []
        passed = (entry["exit_code"] == 0 and obj.is_file() and len(matches) == 1
                  and set(axioms) == EXPECTED_AXIOMS and "sorry" not in text.lower()
                  and source.read_bytes() == target.read_bytes())
        entry.update({"module": name, "status": "PASS" if passed else "FAIL",
                      "source_sha256": digest(source), "source": str(source),
                      "olean_path": str(obj.resolve()),
                      "olean_sha256": digest(obj) if obj.is_file() else None,
                      "axiom_exports": [{"theorem": theorem, "axioms": axioms}]})
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
