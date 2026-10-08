"""Read-only audit of a completed first-column proof and diagnostic build.

Run where the cloud objects are readable. This checks retained evidence and
does not invoke Lean or establish any concrete branch/pair rejection.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
MODULE = "Erdos85ThreeHighFirstColumnSearch"
RESEARCH = Path("research/problems/erdos-85-wip-01/h3_first_column_20261008")
REPORT = re.compile(
    r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def audit(repository, output, library):
    package = repository / RESEARCH
    checker = runpy.run_path(str(package / "check_inventory.py"), run_name="inventory_audit")
    receipt_path = output / "RUN.json"
    receipt_hash = digest(receipt_path)
    receipt = json.loads(receipt_path.read_text())
    require(receipt["status"] == "PASS", "Diagnostic build has not passed")
    recorded_output = Path("/workspace") / output.relative_to(repository)
    require(receipt["lean_threads"] == 1, "Unexpected compiler thread setting")
    require(receipt["dependencies"]["command"] == [
        "lake", "build", "Proofs." + MODULE,
        "Proofs.Erdos85ThreeBlockCompactCodes", "Proofs.Erdos85ThreeHighSecondaryOrbitTable"],
        "Dependency command mismatch")
    require(receipt["inventory"]["command"] == [
        "lean", "-R", str(recorded_output), "-o", str(recorded_output / "Inventory.olean"),
        str(recorded_output / "Inventory.lean")], "Diagnostic compiler command mismatch")
    for key, filename in (("dependencies", "dependencies.log"), ("inventory", "Inventory.log")):
        require(receipt[key]["exit_code"] == 0, f"Nonzero exit: {key}")
        require(receipt[key]["log_sha256"] == digest(output / filename), f"Log hash mismatch: {key}")
    require(receipt["source_sha256"] == digest(package / "Inventory.lean")
            == digest(output / "Inventory.lean"), "Diagnostic source mismatch")
    require(receipt["olean_sha256"] == digest(output / "Inventory.olean"),
            "Diagnostic object mismatch")
    inventory_log = (output / "Inventory.log").read_text()
    rows = [json.loads(line) for line in inventory_log.splitlines() if line.startswith("{")]
    checker["validate"](rows)
    require(rows == receipt["cases"], "Compiler inventory differs from receipt")

    source = repository / "proofs/Proofs" / (MODULE + ".lean")
    expected = re.findall(r"^#print axioms (\S+)\s*$", source.read_text(), re.M)
    require(len(expected) == 5, "Unexpected theorem export inventory")
    dependency_log = (output / "dependencies.log").read_text()
    require("sorry" not in dependency_log.lower() and "sorry" not in inventory_log.lower(),
            "Sorry in compiler logs")
    exports = [{"theorem": m[1], "axioms": [a.strip() for a in (m[2] or "").split(",") if a.strip()]}
               for m in REPORT.finditer(dependency_log) if m[1] in expected]
    require([entry["theorem"] for entry in exports] == expected, "Missing or repeated theorem reports")
    require(all(set(entry["axioms"]) <= STANDARD for entry in exports), "Nonstandard theorem axioms")
    obj = library / "Proofs" / (MODULE + ".olean")
    object_hash = digest(obj)
    require(digest(receipt_path) == receipt_hash, "Receipt changed during audit")
    return {"status": "PASS", "receipt_sha256": receipt_hash,
            "theorem_source_sha256": digest(source), "theorem_olean_sha256": object_hash,
            "axiom_exports": exports,
            "cases": [{k: row[k] for k in ("case", "static_count", "prefix_survivors")} for row in rows],
            "scope": "Five structural/conditional exports plus diagnostic counts; no concrete rejection."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--library-build", type=Path, required=True,
                        help="Directory containing Proofs/*.olean in the cloud build volume")
    args = parser.parse_args()
    print(json.dumps(audit(args.repository.resolve(), args.output.resolve(),
                           args.library_build.resolve()), indent=2))


if __name__ == "__main__":
    main()
