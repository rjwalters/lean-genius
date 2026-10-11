"""Compile exactly one retained cover against its Lean formula, inside cloud Docker."""

import argparse
import json
import os
from pathlib import Path
import re
import shutil

import common as c

pilot_check = c.load("cover_pilot_checker", c.PILOT / "check.py")


def validate(production, expected_receipt):
    c.require(c.digest(production / "PRODUCE.json") == expected_receipt,
              "Different production receipt")
    receipt = json.loads((production / "PRODUCE.json").read_text())
    case = c.select(receipt["case"]["cube"])
    c.require(receipt["status"] == "EXTERNAL_PASS_LEAN_PENDING" and receipt["case"] == case,
              "Production did not pass for the selected frozen cube")
    c.require(receipt["input_manifest_sha256"] == c.INPUT_SHA
              and receipt["cnf_sha256"] == case["cover_cnf_sha256"]
              and receipt["binaries"] == c.pilot.BINARIES
              and receipt["source_sha256"] == c.source_hashes(), "Changed production inputs or pipeline")
    for name, key in [("cover.cnf", "cnf_sha256"), ("proof.lrat", "proof_sha256"),
                      ("proof.lrat7", "packed_sha256"), (c.filename(case), "lean_source_sha256")]:
        c.require(c.digest(production / name) == receipt[key], "Changed artifact: " + name)
    for name in ["cadical", "cake_lpr"]:
        result = receipt["solver" if name == "cadical" else "checker"]
        c.require(c.digest(production / (name + ".log")) == result["log_sha256"]
                  and not result["timed_out"], "Changed or timed-out external verification")
    c.require(receipt["solver"]["exit_code"] == 20 and b"s UNSATISFIABLE" in
              (production / "cadical.log").read_bytes().splitlines(), "Missing solver UNSAT")
    c.require(b"s VERIFIED UNSAT" in (production / "cake_lpr.log").read_bytes().splitlines(),
              "Missing external verified-UNSAT line")
    c.require((production / "proof.lrat").stat().st_size == receipt["proof_bytes"] and
              (production / "proof.lrat7").stat().st_size == receipt["packed_bytes"], "Changed proof length")
    packed = Path("/workspace") / (production / "proof.lrat7").relative_to(c.REPOSITORY)
    c.require((production / c.filename(case)).read_text() ==
              c.lean_source(case, packed, receipt["proof_bytes"]), "Unexpected generated source")
    return case


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--production", type=Path, required=True)
    parser.add_argument("--production-receipt-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    c.require(Path("/.dockerenv").exists() and Path("Proofs").is_dir(),
              "Run only inside cloud Docker from proofs")
    production, output = args.production.resolve(), args.output.resolve()
    case = validate(production, args.production_receipt_sha256)
    output.mkdir(parents=True, exist_ok=False)
    receipt = {"status": "RUNNING", "case": case,
               "production_receipt_sha256": args.production_receipt_sha256,
               "lean_num_threads_environment": "1", "source_sha256": c.source_hashes(),
               "scope": "One Lean-constructed cover only; no leaf, cube, or stratum exclusion."}

    def save():
        c.save(output / "RUN.json", receipt)

    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    save()
    receipt["dependencies"] = pilot_check.run(["lake", "build",
        "Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbLrat",
        "Proofs.Erdos85OrderFortyNineLratCertificateBase"], output / "dependencies.log", env)
    if receipt["dependencies"]["exit_code"]:
        receipt["status"] = "DEPENDENCY_FAILURE"
        save()
        return 1
    save()
    target = output / c.filename(case)
    shutil.copyfile(production / target.name, target)
    obj, log = target.with_suffix(".olean"), target.with_suffix(".log")
    result = pilot_check.run(["lean", "-R", str(output), "-o", str(obj), str(target)], log, env)
    reports = [{"theorem": n, "axioms": [x.strip() for x in a.split(",")]}
               for n, a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log.read_text())]
    prefix = c.namespace(case) + "."
    native = prefix + "check._native.native_decide.ax_1_1"
    passed = (result["exit_code"] == 0 and obj.is_file() and "sorry" not in log.read_text().lower()
              and [r["theorem"] for r in reports] == [prefix + "check", prefix + "checkedCover"]
              and all(set(r["axioms"]) == c.STANDARD | {native} for r in reports))
    c.require(validate(production, args.production_receipt_sha256) == case, "Production changed")
    c.require(target.read_bytes() == (production / target.name).read_bytes(), "Compiler source changed")
    result.update(status="PASS" if passed else "FAIL", source_sha256=c.digest(target),
                  olean_sha256=c.digest(obj) if obj.is_file() else None, axiom_exports=reports)
    c.save(target.with_suffix(".run.json"), result)
    receipt.update(status=result["status"], result=result)
    save()
    print(json.dumps(receipt), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
