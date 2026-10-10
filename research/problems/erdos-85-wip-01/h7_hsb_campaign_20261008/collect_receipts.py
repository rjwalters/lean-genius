#!/usr/bin/env python3
"""Fold the campaign's per-batch receipt files into per-cube evidence tables and check completeness.

    collect_receipts.py --inputs DIR --results DIR [--out DIR]

For every structural cube: the cover CNF and every leaf 0..n-1 must have a CERTIFIED receipt whose
cnf_sha256 equals the value recomputed from the pinned inputs, whose checker saw `s VERIFIED UNSAT`
and whose solver AND checker binaries have the approved sha256 (h7_common.PINNED_BINARIES).
A leaf may instead be certified through a SPLIT (split_complete): a good sub-cover receipt plus a good
sub-leaf receipt for every blocking clause of that same split (same split_sha256).
Unknown or empty --cubes selections are rejected; `all_complete` is about the selected cubes,
`full_campaign_complete` is true only when all 28 cubes were selected and are complete. Writes <out>/<cube>.receipts.tsv.zst (one
line per leaf) and <out>/summary.json. Exit 0 only if all 28 cubes are complete.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import h7_common as hc  # noqa: E402

# New linked checker builds require an independently reviewed hash before acceptance
# (codex review 2026-10-08, room 52742-52751; pins live in h7_common).
CADICAL = hc.CADICAL_SHA256
CAKE_LPR = hc.CAKE_LPR_SHA256


def good_receipt(r: dict, want: str | None) -> bool:
    """CERTIFIED by the approved solver and checker on a CNF with the recomputed sha256."""
    return (want is not None and r.get("status") == "CERTIFIED" and r.get("cnf_sha256") == want
            and r.get("binaries", {}).get("cadical") == CADICAL and r.get("binaries", {}).get("cake_lpr") == CAKE_LPR
            and r.get("checker", {}).get("verified_line") is True and r.get("solver", {}).get("returncode") == 20
            and not r.get("proof", {}).get("checker_closed_early"))


def split_complete(cube: hc.Cube, recs: list[dict], certified_leaves: set) -> dict:
    """Leaves certified through a split (Lean: sevenHighT0CanonicalHsbLeafChecked_of_split).

    A leaf n counts iff there is a good SUB-COVER receipt for n whose blocking list B hashes (with the
    leaf's pinned CNF sha256) to its split_sha256, and for EVERY clause c of B a good SUB-LEAF receipt
    of the same leaf and split_sha256 with clause == c. Every CNF sha256 is recomputed here from the
    pinned inputs and the receipt's own clause data; manifests and the split generator are not trusted.
    Leaves with a direct leaf receipt are not looked at. Returns {leaf: {split_sha256, subcover, subleaves}}."""
    covers: dict = {}
    subs: dict = {}
    for r in recs:
        leaf, sha = r.get("leaf"), r.get("split_sha256")
        if not (isinstance(leaf, int) and 0 <= leaf < cube.n_leaves and isinstance(sha, str)) or leaf in certified_leaves:
            continue
        try:
            if r["kind"] == "subcover":
                clauses = r.get("clauses")
                if hc.split_sha256(cube.name, leaf, cube.leaf_sha256(leaf), clauses) != sha:
                    continue
                if good_receipt(r, cube.subcover_sha256(leaf, clauses)):
                    covers.setdefault((leaf, sha), r)
            else:
                clause = r.get("clause")
                if good_receipt(r, cube.subleaf_sha256(leaf, clause)):
                    subs.setdefault((leaf, sha, tuple(clause)), r)
        except (TypeError, ValueError, KeyError):
            continue
    done: dict = {}
    for (leaf, sha), cr in sorted(covers.items()):
        if leaf in done:
            continue
        parts = [subs.get((leaf, sha, tuple(c))) for c in cr["clauses"]]
        if all(parts):
            done[leaf] = {"split_sha256": sha, "subcover": cr, "subleaves": parts}
    return done


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inputs", type=Path, required=True)
    ap.add_argument("--results", type=Path, required=True)
    ap.add_argument("--out", type=Path)
    ap.add_argument("--cubes", default="")
    a = ap.parse_args()
    requested = set(a.cubes.split(",")) if a.cubes else set(hc.CUBES)
    unknown = requested - set(hc.CUBES)
    if unknown:
        ap.error("unknown cube selector(s): " + ", ".join(repr(c) for c in sorted(unknown)))
    names = [c for c in hc.CUBES if c in requested]
    if not names:
        ap.error("at least one known cube must be selected")
    by_cube: dict[str, list[dict]] = {}
    files = sorted(a.results.glob("*.jsonl.zst"))
    for f in files:
        raw = subprocess.run(["zstd", "-dc", str(f)], capture_output=True, check=True).stdout
        for line in raw.decode().splitlines():
            r = json.loads(line)
            r["_file"] = f.name
            by_cube.setdefault(r["cube"], []).append(r)
    summary = {"schema": "erdos85-h7-hsb-campaign-summary-v1", "result_files": len(files), "cubes": {}, "all_complete": True,
               "inputs_json_sha256": hc.sha_file(a.inputs / "inputs.json")}
    summary["selected_cubes"] = names
    cakes = set()
    for name in names:
        cube = hc.Cube(a.inputs, name)
        best: dict = {}
        rejected = other = 0
        split_recs = []
        for r in by_cube.get(name, []):
            if r["kind"] in ("subleaf", "subcover"):
                if r["status"] in ("CHECK_FAILED", "SOLVER_SAT"):
                    rejected += 1
                split_recs.append(r)
                continue
            key = "cover" if r["kind"] == "cover" else r["leaf"]
            want = cube.meta["cover_cnf_sha256"] if key == "cover" else cube.leaf_sha256(key)
            if good_receipt(r, want):
                cakes.add(r["binaries"]["cake_lpr"])
                best.setdefault(key, r)
            elif r["status"] in ("CHECK_FAILED", "SOLVER_SAT"):
                rejected += 1
            else:
                other += 1
        splits = split_complete(cube, split_recs, set(best))
        for sp in splits.values():
            for r in [sp["subcover"]] + sp["subleaves"]:
                cakes.add(r["binaries"]["cake_lpr"])
        missing = [n for n in range(cube.n_leaves) if n not in best and n not in splits]
        rows = [best[n] for n in range(cube.n_leaves) if n in best]
        split_items = [r for sp in splits.values() for r in [sp["subcover"]] + sp["subleaves"]]
        rows_all = rows + split_items
        c = {"leaves": cube.n_leaves, "certified_leaves": len(rows) + len(splits), "split_leaves": len(splits),
             "split_items": len(split_items), "missing_leaves": len(missing), "first_missing": missing[:20],
             "cover_certified": "cover" in best, "alarm_receipts": rejected, "other_non_certified_receipts": other,
             "proof_bytes": sum(r["proof"]["bytes"] for r in rows_all),
             "solver_cpu_hours": round(sum(r["solver"]["cpu_seconds"] for r in rows_all) / 3600, 2),
             "checker_cpu_hours": round(sum(r["checker"]["cpu_seconds"] for r in rows_all) / 3600, 2),
             "max_solver_cpu_seconds": round(max([r["solver"]["cpu_seconds"] for r in rows_all] or [0]), 1),
             "complete": not missing and "cover" in best and rejected == 0}
        summary["cubes"][name] = c
        summary["all_complete"] = summary["all_complete"] and c["complete"]
        if a.out:
            a.out.mkdir(parents=True, exist_ok=True)
            lines = ["cube\tleaf\tcnf_sha256\tproof_sha256\tproof_bytes\tsolver_cpu_s\tchecker_cpu_s\tconflicts\thost\tfile\n"]
            for key in (["cover"] if "cover" in best else []) + [n for n in range(cube.n_leaves) if n in best or n in splits]:
                if key in splits:  # one summary line per split leaf; the items are in <cube>.split-receipts.tsv.zst
                    sp = splits[key]
                    items = [sp["subcover"]] + sp["subleaves"]
                    lines.append("\t".join(str(x) for x in (
                        name, key, cube.leaf_sha256(key), "split:" + sp["split_sha256"], sum(r["proof"]["bytes"] for r in items),
                        round(sum(r["solver"]["cpu_seconds"] for r in items), 2), round(sum(r["checker"]["cpu_seconds"] for r in items), 2),
                        sum(r["solver"].get("conflicts") or 0 for r in items), "split", f"{len(sp['subleaves'])} subleaves + subcover")) + "\n")
                    continue
                r = best[key]
                lines.append("\t".join(str(x) for x in (name, key, r["cnf_sha256"], r["proof"]["sha256"], r["proof"]["bytes"],
                                                        round(r["solver"]["cpu_seconds"], 2), round(r["checker"]["cpu_seconds"], 2),
                                                        r["solver"].get("conflicts"), r["host"], r["_file"])) + "\n")
            subprocess.run(["zstd", "-q", "-19", "-f", "-o", str(a.out / f"{name}.receipts.tsv.zst")], input="".join(lines).encode(), check=True)
            if splits:
                sl = ["cube\tleaf\tsplit_sha256\tkind\tindex\tclause\tcnf_sha256\tproof_sha256\tproof_bytes\tsolver_cpu_s\tchecker_cpu_s\tconflicts\thost\tfile\n"]
                for leaf in sorted(splits):
                    sp = splits[leaf]
                    for i, r in [("cover", sp["subcover"])] + list(enumerate(sp["subleaves"])):
                        sl.append("\t".join(str(x) for x in (
                            name, leaf, sp["split_sha256"], r["kind"], i, " ".join(map(str, r.get("clause") or [])), r["cnf_sha256"],
                            r["proof"]["sha256"], r["proof"]["bytes"], round(r["solver"]["cpu_seconds"], 2),
                            round(r["checker"]["cpu_seconds"], 2), r["solver"].get("conflicts"), r["host"], r["_file"])) + "\n")
                subprocess.run(["zstd", "-q", "-19", "-f", "-o", str(a.out / f"{name}.split-receipts.tsv.zst")],
                               input="".join(sl).encode(), check=True)
    summary["cake_lpr_sha256"] = sorted(cakes)
    summary["full_campaign_complete"] = summary["all_complete"] and set(names) == set(hc.CUBES)
    summary["totals"] = {k: round(sum(c[k] for c in summary["cubes"].values()), 2) for k in
                         ("leaves", "certified_leaves", "split_leaves", "missing_leaves", "proof_bytes", "solver_cpu_hours", "checker_cpu_hours")}
    text = json.dumps(summary, indent=1, sort_keys=True) + "\n"
    if a.out:
        (a.out / "summary.json").write_text(text)
    print(text if len(names) < 6 else json.dumps({"all_complete": summary["all_complete"], "full_campaign_complete": summary["full_campaign_complete"], "selected_cubes": names, "totals": summary["totals"]}))
    return 0 if summary["all_complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
