"""Join pinned H1 object metadata to capacity tables; never accept proofs."""
import csv
import hashlib
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "h1-source"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def tsv(name):
    with (SOURCE / name).open() as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    require(len(rows) == len({r["tag"] for r in rows}), name + " duplicate tags")
    return {r["tag"]: r for r in rows}


def reconcile():
    for line in (SOURCE / "MANIFEST.sha256").read_text().splitlines():
        digest, name = line.split(maxsplit=1)
        path = SOURCE / name
        require(path.resolve().is_relative_to(SOURCE.resolve()), "unsafe source path")
        require(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
                "source digest mismatch: " + name)
    mate = (1, 0, 3, 2, 5, 4, 7, 6)
    pairs = [(a, b) for a in range(8) for b in range(a + 1, 8) if mate[a] != b]
    capacity = {}
    ordinals = [0] * 5
    for line in (SOURCE / "capacity-inventory.compact").read_text().splitlines():
        profile, *values = map(int, line.split())
        require(profile in range(5) and len(values) == 24 and min(values) >= 0,
                "malformed capacity row")
        table = sorted((pair, value) for pair, value in zip(pairs, values) if value)
        tag = hashlib.sha1(json.dumps(table).encode()).hexdigest()[:16]
        require(tag not in capacity, "duplicate capacity tag")
        capacity[tag] = (profile, ordinals[profile])
        ordinals[profile] += 1
    require(ordinals == [1485, 3617, 4717, 2693, 839], "capacity profile counts")
    objects = [line.split()[0] for line in
               (SOURCE / "h1_objects_tag_bytes_mtime.txt").read_text().splitlines()]
    require(len(objects) == len(set(objects)), "duplicate object tag")
    objects = set(objects)
    jobs = [line.split() for line in (SOURCE / "freight/jobs.tsv").read_text().splitlines()]
    queue = {r[0] for r in jobs}
    require(len(queue) == len(jobs), "duplicate freight tag")
    require(queue <= capacity.keys(), "freight outside capacity")
    require(all(capacity[r[0]][0] == int(r[1]) for r in jobs), "freight profile mismatch")
    ledger = tsv("v3_ledger_tag_status.tsv")
    failures = tsv("v3_failures_tag_kind.tsv")
    for row in failures.values():
        row["kind"] = row["trim"] if row["upload"] == "-" else row["upload"]
    claims = tsv("v3_claims_tag_mtime.tsv")
    require(set(ledger) <= queue and set(failures) <= queue and set(claims) <= queue,
            "v3 state outside queue")
    missing = capacity.keys() - objects
    rows = []
    for tag in sorted(capacity):
        rows.append({"tag": tag, "capacity_profile": capacity[tag][0],
                     "capacity_local_index": capacity[tag][1],
                     "object_listed": tag in objects, "in_v3_queue": tag in queue,
                     "claim_recorded": tag in claims,
                     "ledger_verdict": ledger.get(tag, {}).get("verdict"),
                     "failure_kind": failures.get(tag, {}).get("kind"),
                     "accepted_current_stack": None})
    summary = {
        "scope": "Pinned asynchronous metadata snapshots; no content validation, live state, Lean acceptance or launch queue",
        "capacity": len(capacity), "objects": len(objects),
        "objects_outside_capacity": sorted(objects - capacity.keys()),
        "missing_listed_objects": len(missing),
        "missing_in_v3": sorted(missing & queue),
        "missing_outside_v3": sorted(missing - queue),
        "v3_with_object": len(queue & objects),
        "freight_capacity_index_mismatches": sum(capacity[r[0]][1] != int(r[3]) for r in jobs),
        "ledger_failure_overlap": sorted(ledger.keys() & failures.keys()),
        "ledger_without_claim": sorted(ledger.keys() - claims.keys()),
        "failure_without_claim": sorted(failures.keys() - claims.keys()),
        "uploaded_ledger_without_object": sorted(tag for tag, row in ledger.items()
                                                  if row["upload"] == "uploaded" and tag not in objects),
        "failure_with_object": sorted(failures.keys() & objects),
        "missing_v3_states": dict(Counter(
            ("ledger:" + ledger[tag]["verdict"] if tag in ledger else
             "failure:" + failures[tag]["kind"] if tag in failures else
             "claim_without_line" if tag in claims else "never_claimed")
            for tag in missing & queue)),
    }
    return {"summary": summary, "rows": rows}


if __name__ == "__main__":
    result = reconcile()
    target = ROOT / "h1-exact-set-join.json"
    if target.exists():
        require(json.loads(target.read_text()) == result, "saved reconciliation differs")
        print("PASS: saved H1 exact set join reproduced from pinned source snapshots")
    else:
        target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: len(v) if isinstance(v, list) else v
                      for k, v in result["summary"].items()}, indent=2))
