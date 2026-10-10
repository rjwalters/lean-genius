#!/usr/bin/env python3
"""Shared definitions for the H7 t=0 hsb3 certificate campaign.

Inputs directory layout (built by build_inputs.py, pinned by inputs.json):

    canonical.body        720,804 clause lines of the compact canonical CNF (no header)
    <cube>.units          the 21 empty-mask unit lines of the cube
    <cube>.hsb            stdout of `h7hsb hsb 3 <mask>`   (SevenHighT0Hsb.clauses 3 mask)
    <cube>.cover          stdout of `h7hsb cover 3 <mask>` (line n = blocking clause of leaf n)
    inputs.json           masks, counts and sha256 of every file and of every derived CNF

Exact DIMACS files (header `p cnf 17633 <clauses>`):

    cube CNF   = canonical.body ++ units                      (Lean: ...EmptyCubeSatCnf F i)
    hsb CNF    = cube ++ hsb                                  (Lean: ...HsbCubeSatCnf 3 F i)
    cover CNF  = cube ++ hsb ++ cover                         (SevenHighT0CanonicalHsbCoverChecked)
    leaf n CNF = cube ++ hsb ++ one POSITIVE unit per literal of cover line n, in line order
                                                              (SevenHighT0CanonicalHsbLeafChecked)
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

DEPTH = 3
VARIABLES = 17633
CANONICAL_CLAUSES = 720804
CUBE_CLAUSES = CANONICAL_CLAUSES + 21
STRUCTURAL = [(6, 5), (6, 8), (6, 14), (6, 15), (6, 16), (6, 17), (6, 18),
              (7, 0), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9),
              (7, 10), (7, 11), (7, 13), (7, 14),
              (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6),
              (9, 0), (9, 1)]
CUBES = [f"cube_F{f}_t{i}" for f, i in STRUCTURAL]
BATCH = 64  # leaves per claim
# The only solver and checker binaries whose receipts count. cake_lpr is the Linux arm64 build of
# tanyongkiam/cake_lpr @ a36874a8 (cake_lpr_arm8.S sha256 95b64883…f00c) made on the builder and
# used for the cost sample and the 28 cover receipts; it is shipped as freight, never rebuilt on a
# node. A different build needs a reviewed hash added here (and in collect_receipts.py) first.
CADICAL_SHA256 = "fd601b827c2f6e72c255dd27d6bfa9d7f982414181195fe3ea07ec81385772a2"
CAKE_LPR_SHA256 = "4d47ffdd19fc6a80e24025f8c5d27d89c4309c9931bdad6d389d87e35be5464b"
PINNED_BINARIES = {"cadical": CADICAL_SHA256, "cake_lpr": CAKE_LPR_SHA256}


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""):
            h.update(b)
    return h.hexdigest()


def header(clauses: int) -> bytes:
    return f"p cnf {VARIABLES} {clauses}\n".encode()


def units_of_cover_line(line: bytes) -> list[int]:
    """Blocking clause `-a -b ... 0` -> the positive literals a, b, ... (same order)."""
    toks = line.split()
    if not toks or toks[-1] != b"0":
        raise ValueError(f"bad cover line {line!r}")
    lits = [int(t) for t in toks[:-1]]
    if not lits or any(l >= 0 for l in lits):
        raise ValueError(f"cover line must be all-negative: {line!r}")
    return [-l for l in lits]


class Cube:
    """One structural cube's pinned inputs, loaded in memory once per process."""

    def __init__(self, inputs: Path, name: str, verify: bool = True):
        self.name = name
        self.meta = json.loads((inputs / "inputs.json").read_text())["cubes"][name]
        body = (inputs / "canonical.body").read_bytes()
        units = (inputs / f"{name}.units").read_bytes()
        hsb = (inputs / f"{name}.hsb").read_bytes()
        cover = (inputs / f"{name}.cover").read_bytes()
        self.cover_lines = cover.splitlines()
        self.n_hsb = hsb.count(b"\n")
        self.n_leaves = len(self.cover_lines)
        self.body = body + units + hsb  # cube ++ hsb, without header
        self.cover = cover
        self.leaf_units = len(units_of_cover_line(self.cover_lines[0]))
        if verify:
            m = self.meta
            assert self.n_hsb == m["hsb_clauses"] and self.n_leaves == m["leaves"], name
            assert sha_bytes(header(CUBE_CLAUSES) + body + units) == m["cube_cnf_sha256"], name
            assert sha_bytes(header(CUBE_CLAUSES + self.n_hsb) + self.body) == m["hsb_cnf_sha256"], name
            assert sha_bytes(hsb) == m["hsb_sha256"] and sha_bytes(cover) == m["cover_sha256"], name
            assert self.leaf_units == m["leaf_units"], name
        self._leaf_header = header(CUBE_CLAUSES + self.n_hsb + self.leaf_units)
        self._leaf_prefix_hash = hashlib.sha256(self._leaf_header + self.body)

    def units(self, leaf: int) -> list[int]:
        u = units_of_cover_line(self.cover_lines[leaf])
        if len(u) != self.leaf_units:
            raise ValueError(f"{self.name} leaf {leaf}: {len(u)} units, expected {self.leaf_units}")
        return u

    def leaf_tail(self, leaf: int) -> bytes:
        return "".join(f"{u} 0\n" for u in self.units(leaf)).encode()

    def leaf_sha256(self, leaf: int) -> str:
        """sha256 of the leaf CNF without materialising it (prefix hash state is reused)."""
        h = self._leaf_prefix_hash.copy()
        h.update(self.leaf_tail(leaf))
        return h.hexdigest()

    def write_leaf(self, leaf: int, path: Path) -> None:
        with open(path, "wb") as f:
            f.write(self._leaf_header)
            f.write(self.body)
            f.write(self.leaf_tail(leaf))

    def cover_cnf(self) -> bytes:
        return header(CUBE_CLAUSES + self.n_hsb + self.n_leaves) + self.body + self.cover

    def write_cover(self, path: Path) -> None:
        path.write_bytes(self.cover_cnf())

    # ---- split leaves (README section 9; Lean: ...HsbLeafSplit.lean) ----------------------------
    # leaf CNF       L = cube ++ hsb ++ positive units of cover line n        (...HsbLeafSatCnf)
    # sub-leaf CNF     = L ++ cnfClauseNegUnits c : one unit `-x 0` per literal x of c, in c's order
    #                                                         (SevenHighT0CanonicalHsbSubLeafChecked)
    # sub-cover CNF    = L ++ cnfOfClauseList blocking : each clause verbatim, in list order
    #                                                         (SevenHighT0CanonicalHsbSubCoverChecked)
    # A blocking clause is a list of DIMACS literals (Lean literal (v, b) <-> DIMACS +-(v + 1)).

    @property
    def leaf_clauses(self) -> int:
        return CUBE_CLAUSES + self.n_hsb + self.leaf_units

    def _prefix_hash(self, clauses: int):
        """sha256 state of header(clauses) ++ cube ++ hsb (cached per clause count)."""
        cache = self.__dict__.setdefault("_prefix_cache", {})
        if clauses not in cache:
            cache[clauses] = hashlib.sha256(header(clauses) + self.body)
        return cache[clauses].copy()

    def subleaf_tail(self, leaf: int, clause: list[int]) -> bytes:
        check_clause(clause)
        return self.leaf_tail(leaf) + "".join(f"{-x} 0\n" for x in clause).encode()

    def subleaf_sha256(self, leaf: int, clause: list[int]) -> str:
        h = self._prefix_hash(self.leaf_clauses + len(clause))
        h.update(self.subleaf_tail(leaf, clause))
        return h.hexdigest()

    def write_subleaf(self, leaf: int, clause: list[int], path: Path) -> None:
        with open(path, "wb") as f:
            f.write(header(self.leaf_clauses + len(clause)))
            f.write(self.body)
            f.write(self.subleaf_tail(leaf, clause))

    def subcover_tail(self, leaf: int, clauses: list[list[int]]) -> bytes:
        if not clauses:
            raise ValueError("empty blocking list")
        for c in clauses:
            check_clause(c)
        return self.leaf_tail(leaf) + "".join(" ".join(str(x) for x in c) + " 0\n" for c in clauses).encode()

    def subcover_sha256(self, leaf: int, clauses: list[list[int]]) -> str:
        h = self._prefix_hash(self.leaf_clauses + len(clauses))
        h.update(self.subcover_tail(leaf, clauses))
        return h.hexdigest()

    def write_subcover(self, leaf: int, clauses: list[list[int]], path: Path) -> None:
        with open(path, "wb") as f:
            f.write(header(self.leaf_clauses + len(clauses)))
            f.write(self.body)
            f.write(self.subcover_tail(leaf, clauses))


def check_clause(clause: list[int]) -> None:
    """A blocking clause of a split: non-empty, DIMACS literals of existing variables, no repeated
    variable. (Lean accepts any clause; this keeps the header's variable count and the CNF sane.)"""
    if not isinstance(clause, list) or not clause:
        raise ValueError(f"bad blocking clause {clause!r}")
    if any(type(x) is not int or x == 0 or abs(x) > VARIABLES for x in clause):
        raise ValueError(f"bad literal in blocking clause {clause!r}")
    if len({abs(x) for x in clause}) != len(clause):
        raise ValueError(f"repeated variable in blocking clause {clause!r}")


SPLIT_SCHEMA = "erdos85-h7-hsb-split-v1"


def split_spec_bytes(cube: str, leaf: int, leaf_cnf_sha256: str, clauses: list[list[int]]) -> bytes:
    """Canonical bytes that the split sha256 is taken of: the leaf (cube, index, CNF sha256) and the
    ordered blocking-clause list. Nothing else (no method, no depth): the split is exactly this list."""
    return json.dumps({"schema": SPLIT_SCHEMA, "cube": cube, "leaf": leaf, "leaf_cnf_sha256": leaf_cnf_sha256,
                       "clauses": clauses}, sort_keys=True, separators=(",", ":")).encode()


def split_sha256(cube: str, leaf: int, leaf_cnf_sha256: str, clauses: list[list[int]]) -> str:
    return sha_bytes(split_spec_bytes(cube, leaf, leaf_cnf_sha256, clauses))


HEAD_LEAVES = 1024  # leaves [0, 1024) of every cube: the hard head (README section 6)
HEAD_BATCH = 4


def batches(inputs_meta: dict, batch: int = BATCH) -> list[dict]:
    """Deterministic claim units (manifest v2, 2026-10-08), in claim order:
      1. the 28 cover rows;
      2. HEAD rows `<cube>-h<k>`: leaves [4k, 4k+4) below index 1024, interleaved over the cubes by k,
         so the hardest leaves (smallest indices) of every cube start first, in short batches;
      3. TAIL rows `<cube>-b<k>`: leaves from 1024 on, 64 per row, cube by cube.
    Only batching and order differ from v1: a leaf is still (cube, leaf index), with the same units and
    the same CNF sha256. IDs contain no '.', because the reviewed controller splits ledger names at the
    first dot. inputs.json is unchanged; its `batches` / `batch_manifest_sha256` fields describe v1."""
    rows = [{"id": f"{c}-cover", "cube": c, "kind": "cover"} for c in CUBES]
    n = {c: inputs_meta["cubes"][c]["leaves"] for c in CUBES}
    for k in range(HEAD_LEAVES // HEAD_BATCH):
        for c in CUBES:
            start = k * HEAD_BATCH
            if start < min(n[c], HEAD_LEAVES):
                rows.append({"id": f"{c}-h{k:04d}", "cube": c, "kind": "leaves", "start": start,
                             "end": min(n[c], HEAD_LEAVES, start + HEAD_BATCH)})
    for c in CUBES:
        for k, start in enumerate(range(HEAD_LEAVES, n[c], batch)):
            rows.append({"id": f"{c}-b{k:04d}", "cube": c, "kind": "leaves", "start": start,
                         "end": min(n[c], start + batch)})
    return rows


# Cloud canary: a pinned MIXED selection of main-manifest rows: 2 covers, 2 head rows of a small
# cube (8 leaves) and 6 tail rows (leaves 1024..1087) of six cubes with small, medium and the largest
# hsb clause sets = 2 + 8 + 6 x 64 = 394 items. Tail rows on purpose: head rows of the big cubes take
# hours each. (The canary that ran on 2026-10-08 used the v1 manifest: b0000 = leaves 0..63.)
CANARY_IDS = ["cube_F6_t14-cover", "cube_F7_t10-cover", "cube_F6_t14-h0000", "cube_F6_t14-h0001",
              "cube_F6_t16-b0000", "cube_F6_t18-b0000", "cube_F7_t10-b0000", "cube_F7_t13-b0000",
              "cube_F8_t0-b0000", "cube_F9_t0-b0000"]


def canary_rows(inputs_meta: dict) -> list[dict]:
    by_id = {r["id"]: r for r in batches(inputs_meta)}
    rows = [by_id[i] for i in CANARY_IDS]  # KeyError if the manifest ever stops containing one
    assert any(r["kind"] == "cover" for r in rows) and any(r["kind"] == "leaves" for r in rows)
    return rows


SINGLE_ITEM_KINDS = ("cover", "subleaf", "subcover")


def row_items(row: dict) -> int:
    return 1 if row["kind"] in SINGLE_ITEM_KINDS else (len(row["leaves"]) if "leaves" in row else row["end"] - row["start"])


def manifest_bytes(inputs_meta: dict, batch: int = BATCH) -> bytes:
    return "".join(json.dumps(r, sort_keys=True) + "\n" for r in batches(inputs_meta, batch)).encode()
