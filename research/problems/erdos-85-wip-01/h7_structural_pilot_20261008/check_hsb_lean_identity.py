#!/usr/bin/env python3
"""Byte-identity check: Lean `SevenHighT0Hsb.clauses depth mask` (and the leaf
cover clauses) against `gen_pilot.hsb_clauses`.

Run inside the Lean image, from `proofs/`, after `lake build h7hsb`:

    python3 ../research/problems/erdos-85-wip-01/h7_structural_pilot_20261008/check_hsb_lean_identity.py \
        [--depth 3] [--exe .lake/build/bin/h7hsb] [--out receipt.json] cube_F9_t0 cube_F6_t5 ...
    (no roots = all 28 structural cubes)

For every root it also checks that the Python mask equals the Lean
`sevenHighT0CanonicalEmptyRepresentativeMask F i` (parsed from the Lean source).
The Lean executable prints the clause list of the Lean term; the Python side
uses the real `edge_vars` of the reviewed compact CNF generator.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_pilot as gp  # noqa: E402

PROOFS = HERE.parents[3] / "proofs" / "Proofs"
STRUCTURAL = [(6, 5), (6, 8), (6, 14), (6, 15), (6, 16), (6, 17), (6, 18),
              (7, 0), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9),
              (7, 10), (7, 11), (7, 13), (7, 14),
              (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6),
              (9, 0), (9, 1)]


def lean_masks() -> dict[int, list[int]]:
    src = (PROOFS / "Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeCnf.lean").read_text()
    out = {}
    for m in re.finditer(r"\|\s*(\d)\s*=>\s*\[([0-9,\s]+)\]", src):
        out[int(m.group(1))] = [int(x) for x in m.group(2).replace("\n", " ").split(",")]
    return out


def lean_structural() -> list[tuple[int, int]]:
    src = (PROOFS / "Erdos85OrderFortyNineSevenHighT0EmptyCountingCore.lean").read_text()
    body = src[src.index("def sevenHighT0StructuralCubes"):]
    body = body[:body.index("]") + 1]
    return [(int(a), int(b)) for a, b in re.findall(r"\((\d+),\s*(\d+)\)", body)]


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("roots", nargs="*")
    ap.add_argument("--depth", type=int, default=3)
    ap.add_argument("--exe", default=".lake/build/bin/h7hsb")
    ap.add_argument("--out", type=Path)
    args = ap.parse_args()

    assert lean_structural() == STRUCTURAL, "structural cube list drifted from Lean"
    masks = lean_masks()
    roots = gp.roots()
    names = args.roots or [f"cube_F{f}_t{i}" for f, i in STRUCTURAL]
    _, edge_vars, _ = gp.canonical.build_cnf(gp.compact.CompactCnf)

    def ev(a, b):
        return edge_vars[(min(a, b), max(a, b))]

    evmap = {(e, v): ev(e, v) for e in range(7, 14) for v in gp.OUTSIDE}
    results = []
    ok = True
    for name in names:
        f, i = map(int, re.fullmatch(r"cube_F(\d+)_t(\d+)", name).groups())
        mask = roots[name]["mask"]
        rec = {"root": name, "mask": mask, "depth": args.depth,
               "lean_mask_matches": masks[f][i] == mask}
        t0 = time.time()
        clauses, leaves = gp.hsb_clauses(mask, args.depth, evmap, {})
        py_hsb = "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)
        py_cover = "".join(
            " ".join(str(-ev(e, v)) for (e, r) in leaf for v in sorted(r)) + " 0\n"
            for leaf in leaves)
        rec["python_seconds"] = round(time.time() - t0, 1)
        t0 = time.time()
        lean_hsb = subprocess.run([args.exe, "hsb", str(args.depth), str(mask)],
                                  capture_output=True, text=True)
        lean_cover = subprocess.run([args.exe, "cover", str(args.depth), str(mask)],
                                    capture_output=True, text=True)
        rec["lean_seconds"] = round(time.time() - t0, 1)
        rec["lean_hsb_rc"] = lean_hsb.returncode
        rec["lean_hsb_stderr"] = lean_hsb.stderr.strip()
        rec["lean_cover_rc"] = lean_cover.returncode
        rec["hsb_clauses"] = len(clauses)
        rec["leaves"] = len(leaves)
        rec["python_hsb_sha256"] = sha(py_hsb)
        rec["lean_hsb_sha256"] = sha(lean_hsb.stdout)
        rec["python_cover_sha256"] = sha(py_cover)
        rec["lean_cover_sha256"] = sha(lean_cover.stdout)
        rec["hsb_identical"] = py_hsb == lean_hsb.stdout
        rec["cover_identical"] = py_cover == lean_cover.stdout
        rec["ok"] = bool(rec["lean_mask_matches"] and rec["hsb_identical"]
                         and rec["cover_identical"] and lean_hsb.returncode == 0
                         and lean_cover.returncode == 0)
        ok = ok and rec["ok"]
        results.append(rec)
        print(json.dumps(rec, sort_keys=True), flush=True)
    summary = {"all_ok": ok, "count": len(results), "results": results}
    if args.out:
        args.out.write_text(json.dumps(summary, indent=1, sort_keys=True) + "\n")
    print("ALL_OK" if ok else "MISMATCH", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
