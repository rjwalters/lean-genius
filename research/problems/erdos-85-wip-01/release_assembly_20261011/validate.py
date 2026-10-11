"""Check frozen sources locally; rebuild only the two endpoints on the cloud builder."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[3]
ACCEPTED = ROOT.parent / "order49_h3_closed_capstone_20261008"
MODULES = ["Erdos85OrderFortyNineCapstoneH3", "Erdos85FiniteDropCapstone"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    plan = json.loads((ACCEPTED / "PLAN.json").read_text())
    pending = [MODULES[-1]]
    found = {}
    while pending:
        name = pending.pop()
        if name in found:
            continue
        path = REPO / "proofs/Proofs" / (name + ".lean")
        found[name] = sha(path)
        for line in path.read_text().splitlines():
            if line.startswith("import "):
                pending.extend(x[7:] for x in line.split()[1:] if x.startswith("Proofs."))
    assert len(plan["sources"]) == 892
    assert set(found) == set(plan["sources"]) | {MODULES[-1]}
    for name, digest in plan["sources"].items():
        assert found[name] == digest, name
    manifest = json.loads((ROOT / "source-manifest.json").read_text())
    assert manifest["sources"] == found
    assert manifest["accepted_plan_sha256"] == sha(ACCEPTED / "PLAN.json")
    return plan, found


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cloud", action="store_true")
    args = parser.parse_args()
    plan, found = sources()
    if not args.cloud:
        print(json.dumps({"status": "SOURCE_CLOSURE_MATCH", "sources": len(found)}))
        return
    assert Path("/.dockerenv").exists() and Path.cwd() == Path("/workspace/proofs")
    memory = int(Path("/sys/fs/cgroup/memory.max").read_text())
    cpu = Path("/sys/fs/cgroup/cpu.max").read_text().strip()
    quota, period = map(int, cpu.split())
    assert memory == 16 * 1024**3 and quota == 2 * period
    cache = Path(".lake/build/lib/lean/Proofs")

    def check_objects():
        result = {}
        for name, expected in plan["objects"].items():
            path = cache / (name + ".olean")
            row = {"sha256": sha(path), "bytes": path.stat().st_size}
            assert row == {k: expected[k] for k in row}, name
            result[name] = row
        assert len(result) == 891
        return result

    before = check_objects()
    out = ROOT / "run-output-2"
    out.mkdir(exist_ok=False)
    fresh = out / "lean/Proofs"
    fresh.mkdir(parents=True)
    # Lean resolves a package root as a whole; it does not fall through to
    # another LEAN_PATH entry for a missing module within the same root.
    # Populate the isolated Proofs root with links to the verified imports.
    for name in plan["objects"]:
        (fresh / (name + ".olean")).symlink_to((cache / (name + ".olean")).resolve())
    env = os.environ.copy()
    env["LEAN_PATH"] = str(fresh.parent) + os.pathsep + env.get("LEAN_PATH", "")
    runs = []
    for module in MODULES:
        obj = fresh / (module + ".olean")
        log = out / (module + ".log")
        command = ["lean", "-j1", "Proofs/" + module + ".lean", "-o", str(obj)]
        start = time.monotonic()
        with log.open("xb") as stream:
            child = subprocess.Popen(command, env=env, stdout=stream,
                                     stderr=subprocess.STDOUT, start_new_session=True)
            try:
                rc = child.wait(timeout=90)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
                raise RuntimeError("Compile timeout: " + module)
        text = log.read_text()
        assert rc == 0 and not re.search(r"\b(sorry|error)\b", text, re.I), text
        matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
        assert len(matches) == 3
        exports = []
        for (name, raw), expected in zip(matches, plan["exports"]):
            axioms = [x.strip() for x in raw.split(",") if x.strip()]
            assert name == expected["theorem"]
            assert len(axioms) == len(set(axioms)) and sorted(axioms) == expected["axioms"]
            exports.append({"theorem": name, "axioms": sorted(axioms)})
        runs.append({"module": module, "command": command, "returncode": rc,
                     "elapsed_seconds": time.monotonic() - start,
                     "object_sha256": sha(obj), "object_bytes": obj.stat().st_size,
                     "log_sha256": sha(log), "exports": exports})
    assert before == check_objects()
    assert sources()[1] == found
    report = {"status": "CONDITIONAL_RELEASE_ENDPOINTS_VALIDATED", "sources": found,
              "imported_objects": before, "memory_bytes": memory, "cpu_max": cpu,
              "lean_version": subprocess.check_output(["lean", "--version"], text=True).strip(),
              "runs": runs, "unconditional_drop_verified": False,
              "scope": "Fresh endpoint compilation against 891 hash-verified accepted dependency objects; no native certificate reruns or LRAT replay."}
    (out / "validation.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "axiom_counts": [len(x["axioms"]) for x in runs[-1]["exports"]]}))


if __name__ == "__main__":
    main()
