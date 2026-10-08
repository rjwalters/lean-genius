"""Check the strong 261-case connection after a verified full census build.

--plan only inventories source files. Compilation requires Docker and a PASS
receipt from h3_strong_census_20261008/check.py's full branch.
"""

import argparse
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
spec = importlib.util.spec_from_file_location(
    "census_check", RESEARCH / "h3_strong_census_20261008/check.py")
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)


def plan():
    base, _, library = census.plan("full")
    index = {}
    for directory in ("fixed_pair_coverage", "fixed_pair_rejections",
                      "zero32_coverage", "full_subset_capacity"):
        for source in sorted((RESEARCH / directory).glob("*.lean")):
            if source.stem in index:
                raise ValueError(f"Ambiguous module {source.stem}")
            index[source.stem] = source
    index.update({
        "TerminalReduction": RESEARCH / "full_terminal_pruning/TerminalReduction.lean",
        "CapacityReduction": RESEARCH / "full_capacity_pruning/CapacityReduction.lean",
        "Full261": PACKAGE / "Full261.lean",
    })
    seen = {name for name, _ in base}
    active = set()
    sources = []
    library = set(library)

    def visit(name):
        if name.startswith("Proofs."):
            library.add(name)
            return
        if name in seen:
            return
        if name in active:
            raise ValueError(f"Import cycle at {name}")
        active.add(name)
        source = index[name]
        text = source.read_text()
        if not re.search(r"^#print axioms ", text, re.M) and re.search(
                r"^(?:theorem|axiom|opaque)\s", text, re.M):
            raise ValueError(f"Module {name} has no explicit axiom audit")
        for dependency in census.imports(source):
            visit(dependency)
        active.remove(name)
        seen.add(name)
        sources.append((name, source))

    visit("Full261")
    return base, sources, sorted(library)


def verify_base(directory, sources):
    receipt = json.loads((directory / "RUN.json").read_text())
    if receipt["status"] != "PASS" or receipt["branch"] != "full":
        raise ValueError("The prerequisite full census has not passed")
    entries = {entry["module"]: entry for entry in receipt["results"]}
    if len(entries) != len(receipt["results"]) or set(entries) != {n for n, _ in sources}:
        raise ValueError("Prerequisite module inventory mismatch")
    for name, source in sources:
        entry = entries[name]
        if entry["status"] != "PASS" or entry["exit_code"] != 0:
            raise ValueError(f"Failed prerequisite {name}")
        expected = re.findall(r"^#print axioms (\S+)\s*$", source.read_text(), re.M)
        exports = entry["axiom_exports"]
        if ([e["theorem"] for e in exports] != expected
                or any(set(e["axioms"]) - census.STANDARD for e in exports)):
            raise ValueError(f"Prerequisite axiom mismatch: {name}")
        for suffix, key in ((".lean", "source_sha256"), (".log", "log_sha256"),
                            (".olean", "olean_sha256")):
            if census.digest(directory / (name + suffix)) != entry[key]:
                raise ValueError(f"Prerequisite artifact mismatch: {name}{suffix}")
        if census.digest(source) != entry["source_sha256"]:
            raise ValueError(f"Prerequisite source changed: {name}")
    return census.digest(directory / "RUN.json")


def compile_one(name, source, output, env):
    # Data-only modules do not contain #print directives; downstream printed
    # theorems audit the axioms of the certificate results that consume them.
    target = output / (name + ".lean")
    shutil.copyfile(source, target)
    log = target.with_suffix(".log")
    olean = target.with_suffix(".olean")
    expected = re.findall(r"^#print axioms (\S+)\s*$", source.read_text(), re.M)
    command = ["lean", "-R", str(output), "-o", str(olean), str(target)]
    start = time.monotonic()
    with log.open("w") as handle:
        result = subprocess.run(command, env=env, stdout=handle, stderr=subprocess.STDOUT)
    text = log.read_text()
    exports = []
    for match in re.finditer(
            r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text):
        exports.append({"theorem": match[1], "axioms": [
            x.strip() for x in (match[2] or "").split(",") if x.strip()]})
    names_match = len(exports) == len(expected) and all(
        actual["theorem"] == wanted or actual["theorem"].endswith("." + wanted)
        for actual, wanted in zip(exports, expected))
    passed = (result.returncode == 0 and olean.is_file()
              and names_match
              and all(set(e["axioms"]) <= census.STANDARD for e in exports)
              and "sorry" not in text.lower() and target.read_bytes() == source.read_bytes())
    entry = {"module": name, "source": str(source.relative_to(RESEARCH)),
             "source_sha256": census.digest(source), "log_sha256": census.digest(log),
             "olean_sha256": census.digest(olean) if olean.is_file() else None,
             "command": command, "elapsed_seconds": time.monotonic() - start,
             "exit_code": result.returncode, "status": "PASS" if passed else "FAIL",
             "axiom_exports": exports}
    target.with_suffix(".run.json").write_text(json.dumps(entry, indent=2) + "\n")
    return entry


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--base-build", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    base, sources, library = plan()
    if args.plan:
        print(json.dumps({"prerequisite_modules": len(base), "new_modules": len(sources),
                          "library_modules": library,
                          "sources": {n: str(p.relative_to(RESEARCH)) for n, p in sources}}, indent=2))
        return 0
    if not Path("/.dockerenv").exists():
        parser.error("compilation must run inside the repository Docker environment")
    if args.base_build is None or args.output is None:
        parser.error("--base-build and --output are required")
    base_build = args.base_build.resolve()
    base_hash = verify_base(base_build, base)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    receipt = {"status": "RUNNING", "base_build": str(base_build),
               "base_receipt_sha256": base_hash, "lean_threads": 1,
               "inputs": {n: {"source": str(p.relative_to(RESEARCH)),
                              "sha256": census.digest(p)} for n, p in sources}, "results": []}

    def save():
        temporary = output / "RUN.json.tmp"
        temporary.write_text(json.dumps(receipt, indent=2) + "\n")
        temporary.replace(output / "RUN.json")

    save()
    with (output / "dependencies.log").open("w") as log:
        result = subprocess.run(["lake", "build", *library], stdout=log, stderr=subprocess.STDOUT)
    receipt["dependency_build"] = {"exit_code": result.returncode,
        "command": ["lake", "build", *library],
        "log_sha256": census.digest(output / "dependencies.log")}
    if result.returncode:
        receipt["status"] = "DEPENDENCY_FAILURE"
        save()
        return 1
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["LEAN_PATH"] = os.pathsep.join((str(output), str(base_build), env.get("LEAN_PATH", "")))
    for name, source in sources:
        entry = compile_one(name, source, output, env)
        receipt["results"].append(entry)
        if entry["status"] != "PASS":
            receipt["status"] = "MODULE_FAILURE"
        save()
        print(json.dumps({"module": name, "status": entry["status"]}), flush=True)
        if entry["status"] != "PASS":
            return 1
    verify_base(base_build, base)
    receipt["status"] = "PASS"
    save()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
