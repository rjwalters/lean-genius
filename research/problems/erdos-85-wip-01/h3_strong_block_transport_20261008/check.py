"""Compile retained block certificates and the strong transport in a fresh directory.

Run through the repository Docker runner, inside `lake env`; never run Lean on
the host Mac. The output directory must be new, so a failed run is preserved.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    package = Path(__file__).resolve().parent
    research = package.parent
    sources = [
        research / "compact_u_orbits/full_coverage/Full_3_3.lean",
        research / "full_block_orbits/Certificate.lean",
        package / "StrongTransport.lean",
    ]
    expected_counts = {"Full_3_3": 2, "Certificate": 7, "StrongTransport": 2}
    standard = {"propext", "Classical.choice", "Quot.sound"}
    env = os.environ.copy()
    env["LEAN_PATH"] = str(output) + os.pathsep + env.get("LEAN_PATH", "")
    receipt = {"status": "RUNNING", "results": []}
    receipt_path = output / "RUN.json"
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    for source in sources:
        target = output / source.name
        shutil.copyfile(source, target)
        log_path = target.with_suffix(".log")
        command = ["lean", "-R", str(output), "-o", str(target.with_suffix(".olean")), str(target)]
        started = time.monotonic()
        with log_path.open("w") as log:
            result = subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT)
        log_text = log_path.read_text()
        exports = [
            {"theorem": theorem, "axioms": [a.strip() for a in axioms.split(",") if a.strip()]}
            for theorem, axioms in re.findall(
                r"'([^']+)' depends on axioms: \[([^\]]*)\]", log_text
            )
        ]
        passed = (
            result.returncode == 0
            and len(exports) == expected_counts[source.stem]
            and all(set(export["axioms"]) <= standard for export in exports)
            and "sorry" not in log_text.lower()
        )
        entry = {
            "source": str(source.relative_to(research)),
            "source_sha256": sha256(source),
            "log_sha256": sha256(log_path),
            "command": command,
            "elapsed_seconds": time.monotonic() - started,
            "exit_code": result.returncode,
            "status": "PASS" if passed else "FAIL",
            "axiom_exports": exports,
        }
        receipt["results"].append(entry)
        receipt["status"] = "RUNNING" if passed else "FAIL"
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
        print(json.dumps(entry), flush=True)
        if not passed:
            print(log_text, flush=True)
            return 1
    receipt["status"] = "PASS"
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
