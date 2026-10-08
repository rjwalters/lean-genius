"""Cloud-check the 1553-pair reduction using existing audited native evidence."""

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import sys

sys.dont_write_bytecode = True
PACKAGE = Path(__file__).resolve().parent
VARIED = PACKAGE.parent / "h3_varied_pilot_20261008"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


preflight = load("preflight", VARIED / "check_preflight.py")
timing = load("timing", VARIED / "check_case.py")
digest = timing.digest


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate(prerequisites):
    library = preflight.validate_base(prerequisites / "base")
    timing.preflight("DeficientU26R2", VARIED / "preflight-evidence")
    pilot = VARIED / "DeficientU26R2-evidence"
    audit = json.loads((pilot / "AUDIT.json").read_text())
    receipt = json.loads((pilot / "RUN.json").read_text())
    require(audit["status"] == receipt["status"] == "PASS"
            and digest(pilot / "RUN.json") == audit["run_sha256"], "Unaudited pilot")
    membership = json.loads((VARIED / "preflight-evidence/RUN.json").read_text())
    expected = {}
    for entry in membership["results"]:
        name = entry["module"]
        if name == "DeficientMembership":
            expected["extra/DeficientMembership.olean"] = entry["olean_sha256"]
        elif name in {"Erdos85ThreeHighPilotDeficientU26R2Inputs",
                      "Erdos85ThreeHighPilotDeficientU369R11Inputs"}:
            expected["extra/Proofs/" + name + ".olean"] = entry["olean_sha256"]
    certificate, = [e for e in receipt["results"] if e["module"].endswith("Certificate")]
    require(certificate["status"] == "PASS" and certificate["exit_code"] == 0,
            "Pilot certificate did not pass")
    expected["extra/Proofs/" + certificate["module"] + ".olean"] = certificate["olean_sha256"]
    require(len(expected) == 4, "Incomplete imported evidence inventory")
    for relative, sha in expected.items():
        require(digest(prerequisites / relative) == sha, "Changed imported object: " + relative)
    return library, expected, audit["run_sha256"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prerequisites", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(Path("/.dockerenv").exists() and Path("Proofs").is_dir(),
            "Run only inside cloud Docker from proofs")
    prerequisites, output = args.prerequisites.resolve(), args.output.resolve()
    library, objects, pilot_sha = validate(prerequisites)
    output.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    receipt = {"status": "RUNNING", "lean_threads": 1,
               "base_receipt_sha256": preflight.BASE_SHA, "pilot_receipt_sha256": pilot_sha,
               "imported_object_sha256": objects,
               "scope": "One audited pair removed; 1553 rejection hypotheses remain."}

    def save():
        temp = output / "RUN.json.tmp"
        temp.write_text(json.dumps(receipt, indent=2) + "\n")
        temp.replace(output / "RUN.json")

    save()
    receipt["dependencies"] = timing.run(["lake", "build", *library], output / "dependencies.log", env)
    if receipt["dependencies"]["exit_code"]:
        receipt["status"] = "DEPENDENCY_FAILURE"
        save()
        return 1
    save()
    env["LEAN_PATH"] = os.pathsep.join((str(output), str(prerequisites / "extra"),
        str(prerequisites / "base"), env.get("LEAN_PATH", "")))
    source = PACKAGE / "Deficient1553.lean"
    target = output / source.name
    shutil.copyfile(source, target)
    log, obj = target.with_suffix(".log"), target.with_suffix(".olean")
    result = timing.run(["lean", "-R", str(output), "-o", str(obj), str(target)], log, env)
    reports = timing.reports(log.read_text())
    wanted = re.findall(r"^#print axioms (\S+)\s*$", source.read_text(), re.M)
    native = "Erdos85.VariedPilot.DeficientU26R2.rejected._native.native_decide.ax_1_1"
    passed = (result["exit_code"] == 0 and obj.is_file() and source.read_bytes() == target.read_bytes()
              and "sorry" not in log.read_text().lower()
              and [r["theorem"] for r in reports] == wanted and len(wanted) == 6)
    for index, report in enumerate(reports):
        expected = timing.STANDARD if index < 3 else timing.STANDARD | {native}
        passed = passed and set(report["axioms"]) == expected
    validate(prerequisites)
    result.update(module="Deficient1553", status="PASS" if passed else "FAIL",
                  source_sha256=digest(source), olean_sha256=digest(obj) if obj.exists() else None,
                  axiom_exports=reports)
    (output / "Deficient1553.run.json").write_text(json.dumps(result, indent=2) + "\n")
    receipt["result"] = result
    receipt["status"] = result["status"]
    save()
    print(json.dumps(receipt), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
