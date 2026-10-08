"""Read-only artifact audit for a completed Full261 build and its prerequisite.

This does not run Lean. Run on the cloud host, where the original objects are
available. A successful audit validates retained evidence, not the still-open
finite rejection hypotheses in the two new exports.
"""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(
    r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def audit_build(directory, sources, library, research, recorded_directory):
    receipt_path = directory / "RUN.json"
    receipt_hash = digest(receipt_path)
    receipt = read_json(receipt_path)
    require(receipt["status"] == "PASS", f"Build is not PASS: {directory}")
    names = [name for name, _ in sources]
    entries = receipt["results"]
    require(len(names) == len(set(names)), "Duplicate planned module")
    require(len(entries) == len(names), "Incomplete result inventory")
    by_name = {entry["module"]: entry for entry in entries}
    require(set(by_name) == set(names), "Result module inventory mismatch")
    inputs = {name: {"source": str(source.relative_to(research)),
                     "sha256": digest(source)} for name, source in sources}
    require(receipt["inputs"] == inputs, "Input source inventory/hash mismatch")
    require(receipt["dependency_build"] == {
        "command": ["lake", "build", *library], "exit_code": 0,
        "log_sha256": digest(directory / "dependencies.log")},
        "Dependency build evidence mismatch")
    report_count = 0
    empty_modules = 0
    for name, source in sources:
        entry = by_name[name]
        require(entry["status"] == "PASS" and entry["exit_code"] == 0,
                f"Unsuccessful module: {name}")
        require(read_json(directory / (name + ".run.json")) == entry,
                f"Individual receipt mismatch: {name}")
        require(entry["source"] == inputs[name]["source"], f"Source path mismatch: {name}")
        require(entry["source_sha256"] == inputs[name]["sha256"],
                f"Current source mismatch: {name}")
        for suffix, key in ((".lean", "source_sha256"), (".log", "log_sha256"),
                            (".olean", "olean_sha256")):
            require(digest(directory / (name + suffix)) == entry[key],
                    f"Artifact hash mismatch: {name}{suffix}")
        target = recorded_directory / (name + ".lean")
        require(entry["command"] == ["lean", "-R", str(recorded_directory),
                "-o", str(target.with_suffix(".olean")), str(target)],
                f"Compiler command mismatch: {name}")
        log = (directory / (name + ".log")).read_text()
        require("sorry" not in log.lower(), f"Sorry in compiler log: {name}")
        parsed = [{"theorem": match[1], "axioms": [a.strip() for a in
                   (match[2] or "").split(",") if a.strip()]}
                  for match in REPORT.finditer(log)]
        require(parsed == entry["axiom_exports"], f"Compiler report mismatch: {name}")
        expected = re.findall(r"^#print axioms (\S+)\s*$", source.read_text(), re.M)
        require(len(parsed) == len(expected), f"Axiom report count mismatch: {name}")
        for actual, wanted in zip(parsed, expected):
            require(actual["theorem"] == wanted or actual["theorem"].endswith("." + wanted),
                    f"Axiom report name mismatch: {name}: {wanted}")
            require(set(actual["axioms"]) <= STANDARD,
                    f"Nonstandard axioms: {name}: {actual}")
        report_count += len(parsed)
        empty_modules += not parsed
    require(digest(receipt_path) == receipt_hash, "Receipt changed during audit")
    return {"status": "PASS", "receipt_sha256": receipt_hash,
            "modules": len(names), "axiom_reports": report_count,
            "data_only_modules": empty_modules,
            "final_module_exports": by_name[names[-1]]["axiom_exports"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path,
                        default=Path(__file__).resolve().parents[4])
    parser.add_argument("--recorded-repository", type=Path, default=Path("/workspace"))
    parser.add_argument("--base-build", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repository = args.repository.resolve()
    research = repository / "research/problems/erdos-85-wip-01"
    spec = importlib.util.spec_from_file_location(
        "final_check", research / "h3_strong_final_census_20261008/check.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    base, sources, library = checker.plan()
    _, _, base_library = checker.census.plan("full")
    base_build, output = args.base_build.resolve(), args.output.resolve()
    recorded_base = args.recorded_repository / base_build.relative_to(repository)
    recorded_output = args.recorded_repository / output.relative_to(repository)
    base_receipt = read_json(base_build / "RUN.json")
    require(base_receipt["branch"] == "full" and base_receipt["shard_count"] == 100,
            "Wrong prerequisite branch/shard count")
    base_audit = audit_build(base_build, base, base_library, research, recorded_base)
    final_receipt = read_json(output / "RUN.json")
    require(final_receipt["base_build"] == str(recorded_base), "Wrong prerequisite path")
    require(final_receipt["base_receipt_sha256"] == base_audit["receipt_sha256"],
            "Prerequisite receipt hash mismatch")
    require([r["module"] for r in final_receipt["results"]] == [n for n, _ in sources],
            "Final result dependency order mismatch")
    final_audit = audit_build(output, sources, library, research, recorded_output)
    require(digest(base_build / "RUN.json") == base_audit["receipt_sha256"],
            "Prerequisite changed during final audit")
    print(json.dumps({"status": "PASS", "base": base_audit, "final": final_audit,
                      "scope": "Conditional census connection; finite rejections remain open."},
                     indent=2))


if __name__ == "__main__":
    main()
