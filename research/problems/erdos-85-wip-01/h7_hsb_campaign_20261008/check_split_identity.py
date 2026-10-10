#!/usr/bin/env python3
"""Split-leaf byte identity: the tails printed by EmitSplit.lean (Lean definitions cnfClauseNegUnits,
SevenHighT0Hsb.clause, cnfOfClauseList) against the tails h7_common appends to cube ++ hsb.

    # on the Mac (pinned inputs): write the fixture from split specs (split_leaf.py --specs ...)
    check_split_identity.py fixture --inputs DIR --specs specs.jsonl --out receipts/split_identity_fixture.json
    # in the pinned Lean image, from proofs/ (check_split_identity.sh): run the emitter per split, compare
    check_split_identity.py check --fixture receipts/split_identity_fixture.json --out /tmp/split_identity.json

Per split the fixture holds the leaf rows (outside-vertex lists, from the cover line), the blocking
clauses, and sha256 + line count of: the leaf tail (positive units), each sub-leaf's appended units,
and the sub-cover's appended clauses, all as produced by h7_common.Cube. Together with the receipted
identity of cube ++ hsb and the `rfl` decomposition theorems in EmitSplit.lean, equal tails mean the
sub-leaf / sub-cover DIMACS files are the Lean terms of SevenHighT0CanonicalHsbSub{Leaf,Cover}Checked.
"""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def rows_of_units(units: list, sizes: list) -> list:
    """Positive leaf units (DIMACS) -> rows of outside vertices, inverting edgeVar j v = j*(83-j)/2 + (v-7-j-1)."""
    rows, k = [], 0
    for j, n in enumerate(sizes):
        row = []
        for d in units[k:k + n]:
            v = (d - 1) - j * (83 - j) // 2 + 7 + j + 1
            assert 14 <= v < 49 and j * (83 - j) // 2 + (v - 7 - j - 1) + 1 == d, (j, d, v)
            row.append(v)
        rows.append(row)
        k += n
    assert k == len(units)
    return rows


def fixture(inputs: Path, specs: Path, out: Path) -> int:
    sys.path.insert(0, str(HERE))
    import h7_common as hc
    import leaf_tree
    cubes, items = {}, []
    for line in specs.read_text().splitlines():
        s = json.loads(line)
        cube = cubes.get(s["cube"]) or cubes.setdefault(s["cube"], hc.Cube(inputs, s["cube"]))
        leaf, clauses = s["leaf"], s["clauses"]
        assert hc.split_sha256(cube.name, leaf, cube.leaf_sha256(leaf), clauses) == s["split_sha256"]
        lt = cube.leaf_tail(leaf)
        sub = [cube.subleaf_tail(leaf, c)[len(lt):] for c in clauses]
        cov = cube.subcover_tail(leaf, clauses)[len(lt):]
        rows = rows_of_units(cube.units(leaf), leaf_tree.row_sizes(cube.meta["mask"]))
        items.append({"cube": cube.name, "leaf": leaf, "split_sha256": s["split_sha256"],
                      "args": ["/".join(",".join(map(str, r)) for r in rows)] + [",".join(map(str, c)) for c in clauses],
                      "leaf_tail": {"sha256": sha(lt), "lines": lt.count(b"\n")},
                      "subleaf_tails": [{"sha256": sha(t), "lines": t.count(b"\n")} for t in sub],
                      "subcover_tail": {"sha256": sha(cov), "lines": cov.count(b"\n")},
                      "subleaf_cnf_sha256": [cube.subleaf_sha256(leaf, c) for c in clauses],
                      "subcover_cnf_sha256": cube.subcover_sha256(leaf, clauses),
                      "leaf_cnf_sha256": cube.leaf_sha256(leaf), "prefix_clauses": hc.CUBE_CLAUSES + cube.n_hsb})
    doc = {"schema": "erdos85-h7-split-identity-fixture-v1", "inputs_json_sha256": hc.sha_file(inputs / "inputs.json"),
           "h7_common_py_sha256": hc.sha_file(HERE / "h7_common.py"), "splits": items}
    out.write_text(json.dumps(doc, indent=1, sort_keys=True) + "\n")
    print(json.dumps({"splits": len(items), "fixture": str(out), "sha256": sha(out.read_bytes())}))
    return 0


def segments(text: bytes) -> dict:
    segs, cur = {}, None
    for line in text.splitlines(keepends=True):
        if line.startswith(b"c tail "):
            cur = line[7:].strip().decode()
            segs[cur] = b""
        else:
            segs[cur] += line
    return segs


def check(fx: Path, out: Path, emitter: Path) -> int:
    doc = json.loads(fx.read_text())
    ok, results = True, []
    for it in doc["splits"]:
        p = subprocess.run(["lake", "env", "lean", "--run", str(emitter), *it["args"]], capture_output=True)
        segs = segments(p.stdout) if p.returncode == 0 else {}
        want = [("leaf", it["leaf_tail"])] + [(f"subleaf {k}", t) for k, t in enumerate(it["subleaf_tails"])] + \
               [("subcover", it["subcover_tail"])]
        bad = [name for name, t in want if name not in segs or sha(segs[name]) != t["sha256"]
               or segs[name].count(b"\n") != t["lines"]]
        good = p.returncode == 0 and not bad and len(segs) == len(want)
        ok = ok and good
        rec = {"cube": it["cube"], "leaf": it["leaf"], "split_sha256": it["split_sha256"], "segments": len(segs),
               "expected_segments": len(want), "mismatched": bad[:10], "emitter_returncode": p.returncode,
               "stderr_tail": p.stderr.decode(errors="replace")[-1000:], "identical": good}
        results.append(rec)
        print(json.dumps(rec, sort_keys=True), flush=True)
    summary = {"schema": "erdos85-h7-split-identity-v1", "all_ok": ok, "count": len(results),
               "fixture_sha256": sha(fx.read_bytes()), "emitter_sha256": sha(emitter.read_bytes()),
               "lean_terms": ["SevenHighT0CanonicalHsbSubLeafChecked: leafSatCnf ++ cnfClauseNegUnits c",
                              "SevenHighT0CanonicalHsbSubCoverChecked: leafSatCnf ++ cnfOfClauseList blocking"],
               "results": results}
    out.write_text(json.dumps(summary, indent=1, sort_keys=True) + "\n")
    print("SPLIT_IDENTITY_ALL_OK" if ok else "SPLIT_IDENTITY_MISMATCH", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    f = sub.add_parser("fixture"); f.add_argument("--inputs", type=Path, required=True)
    f.add_argument("--specs", type=Path, required=True); f.add_argument("--out", type=Path, required=True)
    c = sub.add_parser("check"); c.add_argument("--fixture", type=Path, required=True); c.add_argument("--out", type=Path, required=True)
    c.add_argument("--emitter", type=Path, default=HERE / "EmitSplit.lean")
    a = ap.parse_args()
    raise SystemExit(fixture(a.inputs, a.specs, a.out) if a.cmd == "fixture" else check(a.fixture, a.out, a.emitter))
