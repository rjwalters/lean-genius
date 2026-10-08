"""Cloud-only diagnostic: enumerate first columns, without running their DFS."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

PACKAGE = Path(__file__).resolve().parent
CASES = ["FullU1R15", "FullU3R3", "FullU54R20",
         "DeficientU26R2", "DeficientU369R11"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, log, env):
    started = time.monotonic()
    with log.open("w") as handle:
        result = subprocess.run(command, env=env, stdout=handle, stderr=subprocess.STDOUT)
    return {"command": command, "exit_code": result.returncode,
            "elapsed_seconds": time.monotonic() - started, "log_sha256": digest(log)}


def validate(rows):
    if [row["case"] for row in rows] != CASES:
        raise ValueError("Missing, repeated, or unexpected inventory cases")
    for row in rows:
        branches = row["columns_mask_and_prefix_pass"]
        masks = []
        for mask, passed in branches:
            if type(mask) is not int or not 0 <= mask < 2 ** 15 or type(passed) is not bool:
                raise ValueError("Invalid branch encoding")
            masks.append(mask)
        if (len(set(masks)) != len(masks) or row["static_count"] != len(branches)
                or row["prefix_survivors"] != sum(passed for _, passed in branches)):
            raise ValueError("Inconsistent candidate inventory")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not Path("/.dockerenv").exists() or not Path("Proofs").is_dir():
        parser.error("Run from proofs inside the cloud Docker environment")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = PACKAGE / "Inventory.lean"
    copied = output / source.name
    shutil.copyfile(source, copied)
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    receipt = {"status": "RUNNING", "scope": "Diagnostic only; no rejection theorem.",
               "source_sha256": digest(source), "lean_threads": 1}

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
    obj = output / "Inventory.olean"
    log = output / "Inventory.log"
    receipt["inventory"] = run([
        "lean", "-R", str(output), "-o", str(obj), str(copied)], log, env)
    try:
        rows = [json.loads(line) for line in log.read_text().splitlines()
                if line.startswith('{')]
        validate(rows)
        if receipt["inventory"]["exit_code"] or not obj.is_file():
            raise ValueError("Lean inventory compilation failed")
        if source.read_bytes() != copied.read_bytes():
            raise ValueError("Source changed during compilation")
        receipt.update(status="PASS", cases=rows, olean_sha256=digest(obj))
    except (KeyError, TypeError, ValueError) as error:
        receipt.update(status="FAIL", error=str(error))
    save()
    print(json.dumps(receipt), flush=True)
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
