"""Cloud-check one retained cover proof against the generated Lean formula."""

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
PACKAGE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("produce", PACKAGE / "produce.py")
producer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(producer)
require, digest = producer.require, producer.hc.sha_file
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def validate(production):
    receipt = json.loads((production / "PRODUCE.json").read_text())
    require(receipt["status"] == "EXTERNAL_PASS_LEAN_PENDING", "External pilot has not passed")
    require(receipt["cnf_sha256"] == producer.EXPECTED_CNF, "Wrong cover CNF")
    for name, key in [("cover.cnf", "cnf_sha256"), ("proof.lrat", "proof_sha256"),
                      ("proof.lrat7", "packed_sha256"), ("CoverF6T5.lean", "lean_source_sha256")]:
        require(digest(production / name) == receipt[key], "Changed input: " + name)
    packed = Path("/workspace") / (production / "proof.lrat7").relative_to(producer.REPOSITORY)
    require((production / "CoverF6T5.lean").read_text() ==
            producer.lean_source(packed, receipt["proof_bytes"]), "Unexpected generated source")
    return digest(production / "PRODUCE.json")


def run(command, log, env):
    start = time.monotonic()
    with log.open("w") as handle:
        child = subprocess.Popen(command, env=env, stdout=handle, stderr=subprocess.STDOUT)
        _, status, usage = os.wait4(child.pid, 0)
        child.returncode = os.waitstatus_to_exitcode(status)
    return {"command": command, "exit_code": child.returncode,
            "elapsed_seconds": time.monotonic() - start, "user_cpu_seconds": usage.ru_utime,
            "system_cpu_seconds": usage.ru_stime, "max_rss_kib": usage.ru_maxrss,
            "log_sha256": digest(log)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--production", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(Path("/.dockerenv").exists() and Path("Proofs").is_dir(),
            "Run only inside cloud Docker from proofs")
    production, output = args.production.resolve(), args.output.resolve()
    production_sha = validate(production)
    output.mkdir(parents=True, exist_ok=False)
    receipt = {"status": "RUNNING", "production_receipt_sha256": production_sha,
               "lean_num_threads_environment": "1",
               "scope": "One generated cover CNF only; no structural cube or stratum exclusion."}

    def save():
        temp = output / "RUN.json.tmp"
        temp.write_text(json.dumps(receipt, indent=2) + "\n")
        temp.replace(output / "RUN.json")

    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    save()
    receipt["dependencies"] = run(["lake", "build",
        "Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbLrat",
        "Proofs.Erdos85OrderFortyNineLratCertificateBase"], output / "dependencies.log", env)
    if receipt["dependencies"]["exit_code"]:
        receipt["status"] = "DEPENDENCY_FAILURE"
        save()
        return 1
    save()
    target = output / "CoverF6T5.lean"
    shutil.copyfile(production / target.name, target)
    obj, log = target.with_suffix(".olean"), target.with_suffix(".log")
    result = run(["lean", "-R", str(output), "-o", str(obj), str(target)], log, env)
    reports = [{"theorem": n, "axioms": [x.strip() for x in a.split(",")]}
               for n, a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log.read_text())]
    prefix = "Erdos85.HsbCoverPilot.F6T5."
    native = prefix + "check._native.native_decide.ax_1_1"
    passed = (result["exit_code"] == 0 and obj.is_file() and "sorry" not in log.read_text().lower()
              and [r["theorem"] for r in reports] == [prefix + "check", prefix + "checkedCover"]
              and all(set(r["axioms"]) == STANDARD | {native} for r in reports))
    require(validate(production) == production_sha, "Production evidence changed during check")
    require(target.read_bytes() == (production / target.name).read_bytes(), "Compiler source changed")
    result.update(status="PASS" if passed else "FAIL", source_sha256=digest(target),
                  olean_sha256=digest(obj) if obj.is_file() else None, axiom_exports=reports)
    (output / "CoverF6T5.run.json").write_text(json.dumps(result, indent=2) + "\n")
    receipt.update(status=result["status"], result=result)
    save()
    print(json.dumps(receipt), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
