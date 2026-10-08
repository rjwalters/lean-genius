"""Cloud-check Full260 and full pilot membership using audited existing objects."""

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
RESEARCH = PACKAGE.parent
VARIED = RESEARCH / "h3_varied_pilot_20261008"
BASE_SHA = "9924e45dfa932bae6af3607eb7de97e4b77d590366bf8d4bb9eaaf8de480236f"
PILOT_SHA = "b1dd1f5ec0a48fb8e5261b23a3715ff9942edb596bbe7ce0eacd1673a3b17b21"
PREFLIGHT_SHA = "c0e0517d74016e473049f68646a539901b63412430496ebd0ef0cae736a36ea4"
NATIVE = "Erdos85.NativeTerminalPilot.rejected._native.native_decide.ax_1_1"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


timing = load("timing", VARIED / "check_case.py")
final = load("final_check", RESEARCH / "h3_strong_final_census_20261008/check.py")
audit = load("final_audit", RESEARCH / "h3_strong_final_census_20261008/audit.py")
digest, require = timing.digest, audit.require


def read(path):
    return json.loads(path.read_text())


def census(base, built, expected_sha):
    require(digest(base / "RUN.json") == BASE_SHA, "Different audited base census")
    require(re.fullmatch(r"[0-9a-f]{64}", expected_sha) is not None,
            "An independently audited final receipt hash is required")
    require(digest(built / "RUN.json") == expected_sha, "Different final census receipt")
    base_sources, sources, library = final.plan()
    _, _, base_library = final.census.plan("full")
    base_run, run = read(base / "RUN.json"), read(built / "RUN.json")
    require(base_run["branch"] == "full" and base_run["shard_count"] == 100,
            "Wrong base census")
    require(run["status"] == "PASS" and run["base_receipt_sha256"] == BASE_SHA,
            "Final census is not a verified completion")
    require([r["module"] for r in run["results"]] == [n for n, _ in sources],
            "Final census module order differs")
    recorded_base = Path(run["base_build"])
    recorded_final = Path(run["results"][0]["command"][2])
    require(recorded_base.is_absolute() and recorded_final.is_absolute(),
            "Invalid recorded compiler paths")
    base_audit = audit.audit_build(base, base_sources, base_library, RESEARCH, recorded_base)
    final_audit = audit.audit_build(built, sources, library, RESEARCH, recorded_final)
    require(final_audit["receipt_sha256"] == expected_sha, "Final receipt changed")
    return library, {"base": base_audit, "final": final_audit}


def imported_objects(extra):
    """Check reusable objects against the two immutable, independently audited runs."""
    pilot = RESEARCH / "h3_cloud_u1r15_20261008/split-evidence"
    preflight = VARIED / "preflight-evidence"
    for directory, expected in [(pilot, PILOT_SHA), (preflight, PREFLIGHT_SHA)]:
        require(digest(directory / "RUN.json") == expected, "Changed prerequisite receipt")
        require(read(directory / "RUN.json")["status"] == "PASS"
                and read(directory / "AUDIT.json")["status"] == "PASS"
                and read(directory / "AUDIT.json")["run_sha256"] == expected,
                "Missing independent prerequisite audit")
    plan, old_plan = read(VARIED / "PLAN.json"), read(preflight / "PLAN.json")
    require(read(preflight / "RUN.json")["plan_sha256"] == digest(preflight / "PLAN.json"),
            "Changed original preflight plan")
    require(digest(VARIED / "FullMembership.lean") ==
            plan["generated_source_sha256"]["FullMembership.lean"], "Changed full membership source")
    objects, inputs = {}, []
    for case in [c for c in plan["cases"] if c["branch"] == "full"]:
        require(case in old_plan["cases"], "Changed selected case")
        for suffix in ["Inputs", "Certificate", "Consumer"]:
            name = case["module_prefix"] + suffix + ".lean"
            require(digest(VARIED / name) == plan["generated_source_sha256"][name]
                    == old_plan["generated_source_sha256"][name], "Changed selected source")
        name = case["module_prefix"] + "Inputs"
        entry, = [e for e in read(preflight / "RUN.json")["results"] if e["module"] == name]
        require(entry["status"] == "PASS" and entry["exit_code"] == 0, "Failed input module")
        require(digest(preflight / (name + ".lean")) == entry["source_sha256"]
                == digest(VARIED / (name + ".lean")), "Input source mismatch")
        require(digest(preflight / (name + ".log")) == entry["log_sha256"], "Input log mismatch")
        inputs.append(entry)
        objects[name] = entry["olean_sha256"]
    require(len(inputs) == 2, "Expected exactly two full input modules")
    name = "Erdos85ThreeHighNativeTerminalPilotCertificate"
    entry, = [e for e in read(pilot / "RUN.json")["results"] if e["module"] == name]
    require(entry["status"] == "PASS" and entry["exit_code"] == 0, "Failed native certificate")
    require(digest(pilot / (name + ".lean")) == entry["source_sha256"] ==
            digest(RESEARCH / "h3_formal_20261007" / (name + ".lean")), "Changed pilot source")
    require(digest(pilot / (name + ".log")) == entry["log_sha256"], "Changed pilot log")
    reports = timing.reports((pilot / (name + ".log")).read_text())
    selected = [r for r in reports if r["theorem"] == "Erdos85.NativeTerminalPilot.rejected"]
    require(selected == entry["axiom_exports"] and len(selected) == 1
            and set(selected[0]["axioms"]) == timing.STANDARD | {NATIVE}, "Wrong native axiom set")
    objects[name] = entry["olean_sha256"]
    for name, sha in objects.items():
        require(digest(extra / (name + ".olean")) == sha, "Changed imported object: " + name)
    return objects, inputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-build", type=Path, required=True)
    parser.add_argument("--final-build", type=Path, required=True)
    parser.add_argument("--final-receipt-sha256", required=True)
    parser.add_argument("--extra-objects", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(Path("/.dockerenv").exists() and Path("Proofs").is_dir(),
            "Run only inside cloud Docker from proofs")
    base, built, extra, output = [p.resolve() for p in
        (args.base_build, args.final_build, args.extra_objects, args.output)]
    library, census_audit = census(base, built, args.final_receipt_sha256)
    objects, inputs = imported_objects(extra)
    output.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(VARIED / "PLAN.json", output / "PLAN.json")
    receipt = {"status": "RUNNING", "census_audit": census_audit,
               "pilot_receipt_sha256": PILOT_SHA, "input_receipt_sha256": PREFLIGHT_SHA,
               "plan_sha256": digest(output / "PLAN.json"), "imported_object_sha256": objects,
               "lean_num_threads_environment": "1", "results": [],
               "reused_input_modules": [e["module"] for e in inputs],
               "scope": "Full260 conditional reduction and two full memberships; no native search rerun."}

    def save():
        temp = output / "RUN.json.tmp"
        temp.write_text(json.dumps(receipt, indent=2) + "\n")
        temp.replace(output / "RUN.json")

    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    save()
    library = sorted(set(library) | {"Proofs.Erdos85ThreeHighNativePairSearch",
        "Proofs.Erdos85ThreeBlockCompactCodes", "Proofs.Erdos85ThreeHighSecondaryOrbitTable"})
    require(not set(library) & {"Proofs." + name for name in objects},
            "Refuse to rebuild an imported certificate or input object")
    receipt["dependencies"] = timing.run(["lake", "build", *library], output / "dependencies.log", env)
    if receipt["dependencies"]["exit_code"]:
        receipt["status"] = "DEPENDENCY_FAILURE"
        save()
        return 1
    # Preserve the complete Proofs namespace; never put a partial Proofs root on LEAN_PATH.
    library_root = Path(".lake/build/lib/lean/Proofs").resolve()
    for name, sha in objects.items():
        destination = library_root / (name + ".olean")
        if destination.exists():
            require(digest(destination) == sha, "Refuse to replace a different imported object")
        else:
            shutil.copyfile(extra / destination.name, destination)
        require(digest(destination) == sha, "Imported object copy changed")
    for entry in inputs:
        for suffix in [".lean", ".log"]:
            name = entry["module"] + suffix
            shutil.copyfile(VARIED / "preflight-evidence" / name, output / name)
        receipt["results"].append(entry)
    env["LEAN_PATH"] = os.pathsep.join((str(output), str(built), str(base), env.get("LEAN_PATH", "")))
    save()
    for name, source, count in [("FullMembership", VARIED / "FullMembership.lean", 4),
                                ("Full260", PACKAGE / "Full260.lean", 6)]:
        target = output / source.name
        shutil.copyfile(source, target)
        log, obj = target.with_suffix(".log"), target.with_suffix(".olean")
        result = timing.run(["lean", "-R", str(output), "-o", str(obj), str(target)], log, env)
        reports = timing.reports(log.read_text())
        expected = re.findall(r"^#print axioms (\S+)\s*$", source.read_text(), re.M)
        passed = (result["exit_code"] == 0 and obj.is_file() and source.read_bytes() == target.read_bytes()
                  and "sorry" not in log.read_text().lower()
                  and [r["theorem"] for r in reports] == expected and len(expected) == count)
        for index, report in enumerate(reports):
            axioms = set(report["axioms"])
            passed = passed and (axioms == timing.STANDARD | {NATIVE}
                if name == "Full260" and index >= 3 else axioms <= timing.STANDARD)
        result.update(module=name, status="PASS" if passed else "FAIL",
                      source_sha256=digest(source), olean_sha256=digest(obj) if obj.is_file() else None,
                      axiom_exports=reports)
        (output / (name + ".run.json")).write_text(json.dumps(result, indent=2) + "\n")
        receipt["results"].append(result)
        if not passed:
            receipt["status"] = "MODULE_FAILURE"
        save()
        print(json.dumps(result), flush=True)
        if not passed:
            return 1
    require(census(base, built, args.final_receipt_sha256)[1] == census_audit, "Census changed")
    require(imported_objects(extra) == (objects, inputs), "Imported evidence changed")
    require(digest(VARIED / "PLAN.json") == receipt["plan_sha256"], "Plan changed")
    receipt["status"] = "PASS"
    save()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
