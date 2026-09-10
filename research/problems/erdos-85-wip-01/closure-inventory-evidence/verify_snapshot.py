"""Verify portable metadata identity and H7 coverage joins, never proof validity."""
import hashlib
import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(name):
    return json.loads((ROOT / name).read_text())


def main():
    manifest = read("manifest.json")
    names = [row["name"] for row in manifest["files"]]
    require(len(names) == len(set(names)), "duplicate snapshot filename")
    for row in manifest["files"]:
        require(Path(row["name"]).name == row["name"], "nonlocal filename")
        payload = (ROOT / row["name"]).read_bytes()
        require(len(payload) == row["bytes"], "snapshot length mismatch")
        require(hashlib.sha256(payload).hexdigest() == row["sha256"],
                "snapshot digest mismatch: " + row["name"])
    parent = read("h7-parent.json")
    queue = read("h7-adaptive-queue.json")
    payloads = read("h7-direct-payloads.json")
    slots = {f"cube_F{f}_t{i}" for f, n in [(6, 19), (7, 15), (8, 7), (9, 2)]
             for i in range(n)}
    parents = {row["id"]: row for row in parent["jobs"]}
    require(len(parents) == len(parent["jobs"]) == 43, "parent duplication")
    require(set(parents) == slots, "wrong parent slots")
    require(hashlib.sha256((ROOT / "h7-parent.json").read_bytes()).hexdigest()
            == queue["parent_manifest_sha256"], "queue parent mismatch")
    receipts = payloads["rows"]
    direct = {row["id"] for row in receipts}
    require(len(direct) == len(receipts) == 14, "receipt duplication/count")
    require(direct <= slots, "receipt outside canonical slots")
    for row in receipts:
        p = parents[row["id"]]
        require(row["actual_sha256"] == row["expected_sha256"]
                == p["lrat_gz_sha256"], "recorded payload digest mismatch")
        require(row["actual_bytes"] == row["expected_bytes"]
                == p["lrat_gz_bytes"], "recorded payload length mismatch")
    require(sum(row["actual_bytes"] for row in receipts) == 979052371,
            "receipt byte total mismatch")
    missing = slots - direct
    require(missing == {row["id"] for row in parent["jobs"]
                        if row["status"] == "missing"}, "status partition mismatch")
    jobs = queue["jobs"]
    require(len(jobs) == len({row["id"] for row in jobs}) == 232,
            "adaptive leaf duplication/count")
    require(Counter(row["parent_id"] for row in jobs)
            == Counter({slot: 8 for slot in missing}), "adaptive coverage mismatch")
    for slot in missing:
        require({row["path"] for row in jobs if row["parent_id"] == slot}
                == {f"{i:03b}" for i in range(8)}, "binary leaf path mismatch")
    print("PASS: snapshot hashes and H7 43 = 14 direct + 29 adaptive parents, 232 leaves")
    print("Scope: recorded metadata only; no fresh payload/CNF hashing, LRAT/Lean replay or S3 validation")


if __name__ == "__main__":
    main()
