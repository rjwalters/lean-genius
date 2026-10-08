"""Cloud-only input and deficient-census preflight; no native search."""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

PACKAGE = Path(__file__).resolve().parent
RESEARCH = PACKAGE.parent
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
BASE_SHA = "190d7e37c814bd8a7eea54e6ad1bbcba73e092e6e0d77deddc717bab098bfecc"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, log, env):
    start = time.monotonic()
    with log.open("w") as handle:
        result = subprocess.run(command, env=env, stdout=handle, stderr=subprocess.STDOUT)
    return {"command": command, "exit_code": result.returncode,
            "elapsed_seconds": time.monotonic() - start, "log_sha256": digest(log)}


def validate_base(base):
    if digest(base / "RUN.json") != BASE_SHA:
        raise ValueError("Deficient census receipt differs from the audited run")
    receipt = json.loads((base / "RUN.json").read_text())
    spec = importlib.util.spec_from_file_location(
        "census", RESEARCH / "h3_strong_census_20261008/check.py")
    census = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(census)
    sources, _, library = census.plan("deficient")
    assert receipt["status"] == "PASS" and receipt["branch"] == "deficient"
    entries = {r["module"]: r for r in receipt["results"]}
    assert len(entries) == len(receipt["results"])
    assert set(entries) == {n for n, _ in sources}
    for name, source in sources:
        entry = entries[name]
        assert entry["status"] == "PASS" and entry["exit_code"] == 0
        assert digest(source) == entry["source_sha256"]
        expected = re.findall(r"^#print axioms (\S+)\s*$", source.read_text(), re.M)
        assert [e["theorem"] for e in entry["axiom_exports"]] == expected
        assert all(set(e["axioms"]) <= STANDARD for e in entry["axiom_exports"])
        for suffix, key in [(".lean", "source_sha256"), (".log", "log_sha256"),
                            (".olean", "olean_sha256")]:
            assert digest(base / (name + suffix)) == entry[key]
    return library


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deficient-base", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not Path("/.dockerenv").exists() or not Path("Proofs").is_dir():
        parser.error("Run inside the cloud Docker environment from proofs")
    base = args.deficient_base.resolve()
    library = validate_base(base)
    subprocess.run(["python3", str(PACKAGE / "prepare.py")], check=True)
    plan = json.loads((PACKAGE / "PLAN.json").read_text())
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    receipt = {"status": "RUNNING", "scope": "Four input modules and two deficient census memberships; no rejection searches. Full membership pending.",
               "lean_threads": 1, "plan_sha256": digest(PACKAGE / "PLAN.json"),
               "deficient_base_sha256": BASE_SHA, "results": []}

    def save():
        tmp = output / "RUN.json.tmp"
        tmp.write_text(json.dumps(receipt, indent=2) + "\n")
        tmp.replace(output / "RUN.json")

    save()
    library = sorted(set(library) | {"Proofs.Erdos85ThreeHighNativePairSearch",
        "Proofs.Erdos85ThreeBlockCompactCodes", "Proofs.Erdos85ThreeHighSecondaryOrbitTable"})
    receipt["dependencies"] = run(["lake", "build", *library], output / "dependencies.log", env)
    if receipt["dependencies"]["exit_code"]:
        receipt["status"] = "DEPENDENCY_FAILURE"
        save()
        return 1
    save()
    for case in plan["cases"]:
        name = case["module_prefix"] + "Inputs"
        source = PACKAGE / (name + ".lean")
        copied = Path("Proofs") / source.name
        shutil.copyfile(source, copied)
        shutil.copyfile(source, output / source.name)
        log = output / (name + ".log")
        result = run(["lake", "build", "Proofs." + name], log, env)
        obj = Path(".lake/build/lib/lean/Proofs") / (name + ".olean")
        passed = (result["exit_code"] == 0 and obj.is_file()
                  and source.read_bytes() == copied.read_bytes()
                  and "sorry" not in log.read_text().lower())
        result.update(module=name, status="PASS" if passed else "FAIL",
                      source_sha256=digest(source),
                      olean_sha256=digest(obj) if obj.is_file() else None)
        receipt["results"].append(result)
        save()
        if not passed:
            receipt["status"] = "INPUT_FAILURE"
            save()
            return 1
    name = "DeficientMembership"
    source = PACKAGE / (name + ".lean")
    target = output / source.name
    shutil.copyfile(source, target)
    obj = target.with_suffix(".olean")
    log = target.with_suffix(".log")
    env["LEAN_PATH"] = str(output) + os.pathsep + str(base) + os.pathsep + env.get("LEAN_PATH", "")
    result = run(["lean", "-R", str(output), "-o", str(obj), str(target)], log, env)
    reports = [{"theorem": n, "axioms": [x.strip() for x in ax.split(",") if x.strip()]}
               for n, ax in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log.read_text())]
    expected = re.findall(r"^#print axioms (\S+)\s*$", source.read_text(), re.M)
    passed = (result["exit_code"] == 0 and obj.is_file()
              and [r["theorem"] for r in reports] == expected
              and all(set(r["axioms"]) <= STANDARD for r in reports)
              and "sorry" not in log.read_text().lower()
              and source.read_bytes() == target.read_bytes())
    result.update(module=name, status="PASS" if passed else "FAIL",
                  source_sha256=digest(source),
                  olean_sha256=digest(obj) if obj.is_file() else None, axiom_exports=reports)
    receipt["results"].append(result)
    receipt["status"] = "PASS" if passed else "MEMBERSHIP_FAILURE"
    save()
    print(json.dumps(receipt), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
