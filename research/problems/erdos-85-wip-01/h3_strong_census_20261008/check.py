"""Rebuild retained coverage and check concrete strong H3 census connections.

Use --plan for a read-only source inventory. Compilation must run inside the
repository's Docker environment. Each branch uses a separate module directory
because both retained coverage packages name their assembly `Assembly`.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import threading
import time


PACKAGE = Path(__file__).resolve().parent
RESEARCH = PACKAGE.parent
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
CODES = [3, 4, 5, 6, 7, 8, 9, 10, 12, 13]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def imports(source):
    return re.findall(r"^import ([A-Za-z0-9_.]+)\s*$", source.read_text(), re.M)


def plan(branch):
    coverage = RESEARCH / "compact_u_orbits" / (branch + "_coverage")
    if branch == "full":
        shard_names = [f"Full_{a}_{b}" for a in CODES for b in CODES]
        extra = [
            ("Transport", RESEARCH / "full_orbit_transport/Transport.lean"),
            ("Pruning", RESEARCH / "full_orbit_pruning/Pruning.lean"),
            ("Certificate", RESEARCH / "full_block_orbits/Certificate.lean"),
            ("StrongTransport", RESEARCH / "h3_strong_block_transport_20261008/StrongTransport.lean"),
            ("FullBlockReduction", RESEARCH / "full_block_pruning/Reduction.lean"),
            ("Full276", PACKAGE / "Full276.lean"),
        ]
    else:
        shard_names = [f"Deficient_{a}_{b}_{d}" for a in CODES for b in CODES for d in (0, 4)]
        extra = [
            ("Pruning", RESEARCH / "deficient_orbit_pruning/Pruning.lean"),
            ("Deficient1554", PACKAGE / "Deficient1554.lean"),
        ]
    assembly = coverage / "Assembly.lean"
    actual_shards = [name for name in imports(assembly) if not name.startswith("Proofs.")]
    if set(actual_shards) != set(shard_names) or len(actual_shards) != len(shard_names):
        raise ValueError(f"Unexpected {branch} assembly shard inventory")
    sources = [(name, coverage / (name + ".lean")) for name in shard_names]
    sources += [("Assembly", assembly), *extra]
    seen = set()
    library = set()
    for name, source in sources:
        if name in seen:
            raise ValueError(f"Duplicate module {name}")
        for dependency in imports(source):
            if dependency.startswith("Proofs."):
                library.add(dependency)
            elif dependency not in seen:
                raise ValueError(f"Missing or out-of-order dependency {name}: {dependency}")
        seen.add(name)
    return sources, len(shard_names), sorted(library)


def compile_one(module, source, output, env):
    target = output / (module + ".lean")
    shutil.copyfile(source, target)
    expected = re.findall(r"^#print axioms ([A-Za-z0-9_.]+)\s*$", source.read_text(), re.M)
    if not expected:
        raise ValueError(f"No explicit axiom exports in {source}")
    log_path = target.with_suffix(".log")
    olean = target.with_suffix(".olean")
    command = ["lean", "-R", str(output), "-o", str(olean), str(target)]
    started = time.monotonic()
    with log_path.open("w") as log:
        result = subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT)
    text = log_path.read_text()
    exports = [
        {"theorem": theorem, "axioms": [x.strip() for x in axioms.split(",") if x.strip()]}
        for theorem, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
    ]
    passed = (
        result.returncode == 0
        and [item["theorem"] for item in exports] == expected
        and all(set(item["axioms"]) <= STANDARD for item in exports)
        and "sorry" not in text.lower()
        and target.read_bytes() == source.read_bytes()
        and olean.is_file()
    )
    entry = {
        "module": module,
        "source": str(source.relative_to(RESEARCH)),
        "source_sha256": digest(source),
        "log_sha256": digest(log_path),
        "olean_sha256": digest(olean) if olean.is_file() else None,
        "command": command,
        "elapsed_seconds": time.monotonic() - started,
        "exit_code": result.returncode,
        "status": "PASS" if passed else "FAIL",
        "axiom_exports": exports,
    }
    target.with_suffix(".run.json").write_text(json.dumps(entry, indent=2) + "\n")
    return entry


def check(branch, output, workers):
    sources, shard_count, library = plan(branch)
    output.mkdir(parents=True, exist_ok=False)
    receipt = {
        "branch": branch,
        "status": "RUNNING",
        "shard_count": shard_count,
        "workers": workers,
        "lean_threads_per_worker": 1,
        "inputs": {name: {"source": str(source.relative_to(RESEARCH)), "sha256": digest(source)}
                   for name, source in sources},
        "results": [],
    }

    def save():
        temporary = output / "RUN.json.tmp"
        temporary.write_text(json.dumps(receipt, indent=2) + "\n")
        temporary.replace(output / "RUN.json")

    save()
    with (output / "dependencies.log").open("w") as log:
        built = subprocess.run(["lake", "build", *library], stdout=log, stderr=subprocess.STDOUT)
    receipt["dependency_build"] = {
        "command": ["lake", "build", *library],
        "exit_code": built.returncode,
        "log_sha256": digest(output / "dependencies.log"),
    }
    if built.returncode:
        receipt["status"] = "DEPENDENCY_FAILURE"
        save()
        return False
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["LEAN_PATH"] = str(output) + os.pathsep + env.get("LEAN_PATH", "")
    stop = threading.Event()

    def shard_check(name, source):
        if stop.is_set():
            return {"module": name, "status": "SKIPPED_AFTER_FAILURE"}
        entry = compile_one(name, source, output, env)
        if entry["status"] != "PASS":
            stop.set()
        return entry

    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(shard_check, name, source)
                   for name, source in sources[:shard_count]]
        for future in as_completed(futures):
            entry = future.result()
            receipt["results"].append(entry)
            save()
            print(json.dumps({"branch": branch, "module": entry["module"], "status": entry["status"]}), flush=True)
    if any(entry["status"] != "PASS" for entry in receipt["results"]):
        receipt["status"] = "SHARD_FAILURE"
        save()
        return False
    for name, source in sources[shard_count:]:
        entry = compile_one(name, source, output, env)
        receipt["results"].append(entry)
        save()
        print(json.dumps({"branch": branch, "module": name, "status": entry["status"]}), flush=True)
        if entry["status"] != "PASS":
            receipt["status"] = "ASSEMBLY_FAILURE"
            save()
            return False
    receipt["status"] = "PASS"
    save()
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--branch", choices=("full", "deficient", "both"), default="both")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--plan", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.workers <= 8:
        parser.error("workers must be between 1 and 8")
    branches = ("full", "deficient") if args.branch == "both" else (args.branch,)
    if args.plan:
        for branch in branches:
            sources, shards, library = plan(branch)
            print(json.dumps({"branch": branch, "shards": shards, "modules": len(sources),
                              "library_modules": library,
                              "new_exports": re.findall(r"^#print axioms (.+)$", sources[-1][1].read_text(), re.M)}))
        return 0
    if not Path("/.dockerenv").exists():
        parser.error("compilation must run inside the repository Docker environment")
    if args.output is None:
        parser.error("--output is required for compilation")
    for branch in branches:
        if not check(branch, args.output.resolve() / branch, args.workers):
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
