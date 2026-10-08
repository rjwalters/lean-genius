"""Check the failed pilot consumer without rerunning its native search.

Both fixtures take the rejection as an explicit hypothesis. The baseline must
reproduce the recursion-depth failure; Consumer.lean must compile with only
standard axioms. This cannot establish the concrete finite rejection.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

PACKAGE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if not Path("/.dockerenv").exists():
        raise SystemExit("Run in the cloud Docker environment, not on the host.")
    output = PACKAGE / "_build/consumer-first"
    output.mkdir(parents=True, exist_ok=False)
    result = {"status": "RUNNING", "scope": "Conditional consumer only; no finite rejection.",
              "results": []}
    command = ["lake", "build", "Proofs.Erdos85ThreeHighNativePairSearch",
               "Proofs.Erdos85ThreeBlockCompactCodes", "Proofs.Erdos85ThreeHighSecondaryOrbitTable"]
    with (output / "dependencies.log").open("w") as handle:
        build = subprocess.run(command, stdout=handle, stderr=subprocess.STDOUT)
    result["dependency_build"] = {"command": command, "exit_code": build.returncode,
                                   "log_sha256": digest(output / "dependencies.log")}
    if build.returncode:
        result["status"] = "DEPENDENCY_FAILURE"
    else:
        env = os.environ.copy()
        env["LEAN_NUM_THREADS"] = "1"
        for name in ("ConsumerBaseline", "Consumer"):
            source = PACKAGE / (name + ".lean")
            log = output / (name + ".log")
            obj = output / (name + ".olean")
            command = ["lean", "-o", str(obj), str(source)]
            started = time.monotonic()
            timed_out = False
            with log.open("w") as handle:
                try:
                    code = subprocess.run(command, env=env, stdout=handle,
                                          stderr=subprocess.STDOUT, timeout=120).returncode
                except subprocess.TimeoutExpired:
                    timed_out, code = True, 124
            text = log.read_text()
            exports = [{"theorem": theorem, "axioms": [a.strip() for a in axioms.split(",") if a.strip()]}
                       for theorem, axioms in re.findall(
                           r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)]
            passed = (code != 0 and not timed_out and
                      "maximum recursion depth has been reached" in text) if name == "ConsumerBaseline" else (
                      code == 0 and obj.is_file() and "sorry" not in text.lower() and
                      len(exports) == 1 and exports[0]["theorem"] ==
                      "Erdos85.NativeTerminalConsumerProbe.no_joint" and
                      set(exports[0]["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"})
            entry = {"module": name, "source_sha256": digest(source), "command": command,
                     "exit_code": code, "timeout": timed_out,
                     "elapsed_seconds": time.monotonic() - started,
                     "expectation_met": passed, "axiom_exports": exports,
                     "log_sha256": digest(log),
                     "olean_sha256": digest(obj) if obj.is_file() else None}
            (output / (name + ".run.json")).write_text(json.dumps(entry, indent=2) + "\n")
            result["results"].append(entry)
            print(json.dumps(entry), flush=True)
        result["status"] = "PASS" if all(r["expectation_met"] for r in result["results"]) else "FAIL"
    (output / "RUN.json").write_text(json.dumps(result, indent=2) + "\n")
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
