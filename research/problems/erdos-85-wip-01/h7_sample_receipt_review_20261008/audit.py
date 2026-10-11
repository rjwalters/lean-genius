"""Audit one immutable, unfinished H7 sample receipt snapshot; no proof replay."""

import hashlib
import json
import random
import re
from collections import Counter
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
INPUT_SHA = "f2d2be89aeee6603201649a70a64a6cdf4f20acc6e9268d502f686f0d39dcb6c"
SNAPSHOT_SHA = "f9aeb149a1331f83bd660125fd4319507d2f5ea27900f18d809594b9b4bb86a2"
BINS = {
    "cadical": "fd601b827c2f6e72c255dd27d6bfa9d7f982414181195fe3ea07ec81385772a2",
    "cake_lpr": "4d47ffdd19fc6a80e24025f8c5d27d89c4309c9931bdad6d389d87e35be5464b",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pinned(name, expected):
    data = (HERE / name).read_bytes()
    require(hashlib.sha256(data).hexdigest() == expected, "Changed snapshot: " + name)
    return data


def main():
    meta = json.loads(pinned("inputs.json", INPUT_SHA))
    raw = pinned("results.jsonl", SNAPSHOT_SHA)
    require(raw.endswith(b"\n"), "Incomplete final receipt")
    rows = [json.loads(line) for line in raw.splitlines()]
    require(len(meta["cubes"]) == 28 and meta["total_leaves"] == 377776,
            "Wrong campaign inventory")
    chosen = {name: random.Random(f"20261008:{name}").sample(
        range(cube["leaves"]), min(50, cube["leaves"]))
        for name, cube in meta["cubes"].items()}
    seen, counts, covers = set(), Counter(), set()
    for row in rows:
        name, kind, leaf = row["cube"], row["kind"], row["leaf"]
        key = name, kind, leaf
        require(key not in seen, "Duplicate receipt")
        seen.add(key)
        require(name in meta["cubes"], "Unknown cube")
        require(row["schema"] == "erdos85-h7-hsb-cert-v1" and row["depth"] == 3,
                "Unexpected schema or depth")
        require(row["seed"] == 20261008 and row["cap_seconds"] == 3600,
                "Unexpected sampling configuration")
        require(row["binaries"] == BINS, "Different solver/checker binaries")
        require(row["status"] == "CERTIFIED", "Uncertified receipt in this snapshot")
        require(row["cnf_sha256"] == row["expected_cnf_sha256"]
                and re.fullmatch(r"[0-9a-f]{64}", row["cnf_sha256"]),
                "CNF receipt inconsistency")
        solver, checker, proof = row["solver"], row["checker"], row["proof"]
        require(solver["returncode"] == 20 and solver["unsat_line"] is True,
                "Missing UNSAT evidence")
        require(checker["verified_line"] is True and checker["failure"] is None,
                "Missing verified-UNSAT evidence")
        require(proof["bytes"] > 0 and re.fullmatch(r"[0-9a-f]{64}", proof["sha256"])
                and proof["stored"] is False and proof["checker_closed_early"] is False,
                "Inconsistent proof-stream receipt")
        require(datetime.fromisoformat(row["started_utc"]) <=
                datetime.fromisoformat(row["finished_utc"]), "Reversed timestamps")
        if kind == "cover":
            require(leaf is None and row["sample_index"] is None
                    and row["cnf_sha256"] == meta["cubes"][name]["cover_cnf_sha256"],
                    "Cover differs from pinned input manifest")
            covers.add(name)
        else:
            require(kind == "leaf" and 0 <= row["sample_index"] < 50,
                    "Invalid leaf sample index")
            require(chosen[name][row["sample_index"]] == leaf, "Different fixed-seed selection")
            require(len(row["units"]) == meta["cubes"][name]["leaf_units"]
                    and all(type(u) is int and 0 < u <= meta["variables"] for u in row["units"]),
                    "Invalid leaf units")
            counts[name] += 1
    require(covers == set(meta["cubes"]), "Incomplete cover receipt inventory")
    leaves = [r for r in rows if r["kind"] == "leaf"]
    report = {
        "status": "RECEIPT_CONSISTENCY_PASS",
        "inputs_sha256": INPUT_SHA, "snapshot_sha256": SNAPSHOT_SHA,
        "latest_receipt_utc": max(r["finished_utc"] for r in rows),
        "records": len(rows), "cover_receipts": len(covers), "leaf_receipts": len(leaves),
        "planned_sample_leaves": sum(map(len, chosen.values())),
        "completed_leaves_by_cube": dict(sorted(counts.items())),
        "heap_retries": sum("heap_retry_of" in r for r in rows),
        "completed_leaf_cpu_seconds": sum(r["solver"]["cpu_seconds"] +
                                           r["checker"]["cpu_seconds"] for r in leaves),
        "scope": "Receipt consistency only. No independent proof replay or leaf-CNF reconstruction.",
        "limitation": "Sampler confirmed live at 05:45:32Z. Unfinished outcomes are absent; no campaign cost extrapolation or completeness claim.",
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
