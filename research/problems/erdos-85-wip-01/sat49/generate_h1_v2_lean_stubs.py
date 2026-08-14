#!/usr/bin/env python3
"""Validate cert-root v3 and emit packed exact-v2 Lean certificate stubs.

Only packed LRATs whose source compacts already passed direct Lean replay may
be emitted.  Every packed payload is hash/size checked before source emission.
Operational orbit tags are checked as provenance but never occur in the table
type: each generated theorem is indexed by ``(profile, localIndex)`` into the
authoritative ``oneHighInventoryTables`` list.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import re
from dataclasses import dataclass
from pathlib import Path


PROFILE_NAMES = ("BBBB", "ABBB", "AABB", "AAAB", "AAAA")
EXPECTED_COLUMNS = (
    "orbit",
    "profile",
    "localIndex",
    "compact_lrat_sha256",
    "raw_lrat_sha256",
    "cnf_sha256",
    "lrat_actions",
    "source_cnf_clauses",
    "compact_bytes",
    "stub_ready",
    "binary_lrat_sha256",
    "binary_bytes",
    "lz4_frame_sha256",
    "lz4_frame_bytes",
    "packed_lz4_sha256",
    "packed_lz4_bytes",
)
TABLE_PAIRS = tuple(
    (c, j)
    for c in range(8)
    for j in range(c + 1, 8)
    if j != (c ^ 1)
)


@dataclass(frozen=True)
class IndexRow:
    orbit: str
    profile: int
    local_index: int
    compact_sha: str
    raw_sha: str
    cnf_sha: str
    actions: int | None
    clauses: int
    compact_bytes: int
    stub_ready: bool
    binary_sha: str
    binary_bytes: int
    frame_sha: str
    frame_bytes: int
    packed_sha: str
    packed_bytes: int


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def worker_tag(values: tuple[int, ...]) -> str:
    table = {
        pair: value
        for pair, value in zip(TABLE_PAIRS, values, strict=True)
        if value != 0
    }
    return hashlib.sha1(json.dumps(sorted(table.items())).encode()).hexdigest()[:16]


def read_inventory(path: Path) -> list[list[str]]:
    profiles: list[list[str]] = [[] for _ in PROFILE_NAMES]
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        if not line:
            continue
        try:
            profile, *values = map(int, line.split())
        except ValueError as error:
            raise ValueError(f"{path}:{line_number}: non-integer inventory row") from error
        if profile not in range(5) or len(values) != 24:
            raise ValueError(f"{path}:{line_number}: malformed inventory row")
        profiles[profile].append(worker_tag(tuple(values)))
    expected = (1536, 3662, 4801, 2700, 842)
    if tuple(map(len, profiles)) != expected:
        raise ValueError(f"unexpected inventory profile counts: {tuple(map(len, profiles))}")
    return profiles


def parse_optional_nat(value: str, field: str) -> int | None:
    if value == "":
        return None
    try:
        result = int(value)
    except ValueError as error:
        raise ValueError(f"{field} is not a natural number: {value!r}") from error
    if result < 0:
        raise ValueError(f"{field} is negative")
    return result


def read_index(path: Path) -> list[IndexRow]:
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if tuple(reader.fieldnames or ()) != EXPECTED_COLUMNS:
            raise ValueError(
                f"{path}: expected header {EXPECTED_COLUMNS}, found {reader.fieldnames}"
            )
        rows: list[IndexRow] = []
        for line_number, raw in enumerate(reader, 2):
            if not re.fullmatch(r"[0-9a-f]{16}", raw["orbit"]):
                raise ValueError(f"{path}:{line_number}: invalid orbit tag")
            try:
                profile = PROFILE_NAMES.index(raw["profile"])
                local_index = int(raw["localIndex"])
                clauses = int(raw["source_cnf_clauses"])
                compact_bytes = int(raw["compact_bytes"])
                binary_bytes = int(raw["binary_bytes"])
                frame_bytes = int(raw["lz4_frame_bytes"])
                packed_bytes = int(raw["packed_lz4_bytes"])
            except ValueError as error:
                raise ValueError(f"{path}:{line_number}: invalid numeric/profile field") from error
            if any(value < 0 for value in (
                local_index, clauses, compact_bytes, binary_bytes,
                frame_bytes, packed_bytes,
            )):
                raise ValueError(f"{path}:{line_number}: negative numeric field")
            hashes = (
                raw["compact_lrat_sha256"],
                raw["raw_lrat_sha256"],
                raw["cnf_sha256"],
                raw["binary_lrat_sha256"],
                raw["lz4_frame_sha256"],
                raw["packed_lz4_sha256"],
            )
            if any(not re.fullmatch(r"[0-9a-f]{64}", item) for item in hashes):
                raise ValueError(f"{path}:{line_number}: invalid SHA-256 field")
            if raw["stub_ready"] not in ("0", "1"):
                raise ValueError(f"{path}:{line_number}: stub_ready must be 0 or 1")
            rows.append(
                IndexRow(
                    raw["orbit"], profile, local_index, hashes[0], hashes[1],
                    hashes[2], parse_optional_nat(raw["lrat_actions"], "lrat_actions"),
                    clauses, compact_bytes, raw["stub_ready"] == "1",
                    hashes[3], binary_bytes, hashes[4], frame_bytes,
                    hashes[5], packed_bytes,
                )
            )
    keys = {
        "orbit": [row.orbit for row in rows],
        "compact hash": [row.compact_sha for row in rows],
        "packed hash": [row.packed_sha for row in rows],
        "profile/index": [(row.profile, row.local_index) for row in rows],
    }
    for label, values in keys.items():
        if len(values) != len(set(values)):
            raise ValueError(f"{path}: duplicate {label}")
    if rows != sorted(rows, key=lambda row: (row.profile, row.local_index)):
        raise ValueError(f"{path}: rows are not sorted by profile/localIndex")
    return rows


def payload_path(cert_root: Path, row: IndexRow) -> Path:
    path = (
        cert_root / "packed" / row.packed_sha[:2] /
        f"{row.packed_sha}.lrat.lz4p7"
    )
    if not path.is_file():
        raise ValueError(f"packed payload is missing for {row.orbit}: {path}")
    return path.resolve()


def validate_row(
    row: IndexRow, profiles: list[list[str]], cert_root: Path, verify_hash: bool
) -> Path:
    if not row.stub_ready:
        raise ValueError(f"{row.orbit}: source compact has not passed direct Lean replay")
    if row.local_index not in range(len(profiles[row.profile])):
        raise ValueError(f"{row.orbit}: localIndex is outside its Lean profile")
    expected_tag = profiles[row.profile][row.local_index]
    if row.orbit != expected_tag:
        raise ValueError(
            f"{row.orbit}: profile/localIndex resolves to inventory tag {expected_tag}"
        )
    payload = payload_path(cert_root, row)
    if payload.stat().st_size != row.packed_bytes:
        raise ValueError(f"{row.orbit}: packed byte count mismatch")
    if verify_hash and sha256(payload) != row.packed_sha:
        raise ValueError(f"{row.orbit}: packed SHA-256 mismatch")
    return payload


def lean_source(row: IndexRow, payload: Path) -> str:
    stem = f"h1V2P{row.profile}I{row.local_index:05d}"
    path_literal = json.dumps(str(payload))
    return f'''import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED exact-v2 certificate stub.
    profile={row.profile} localIndex={row.local_index}
    compact_lrat_sha256={row.compact_sha}
    raw_lrat_sha256={row.raw_sha}
    cnf_sha256={row.cnf_sha}
    binary_lrat_sha256={row.binary_sha}
    lz4_frame_sha256={row.frame_sha}
    packed_lz4_sha256={row.packed_sha}
    compact_bytes={row.compact_bytes} binary_bytes={row.binary_bytes}
    lz4_frame_bytes={row.frame_bytes} packed_lz4_bytes={row.packed_bytes}
    source_cnf_clauses={row.clauses} -/

namespace Erdos85

open Std.Tactic.BVDecide

def {stem}Table : OneHighMissTable :=
  (oneHighInventoryTables ({row.profile} : Fin 5)).get
    ⟨{row.local_index}, by native_decide⟩

private def {stem}ProofText : String :=
  include_str {path_literal}

private def {stem}Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof {stem}ProofText
    {row.frame_bytes} {row.binary_bytes}

private theorem {stem}Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses {row.profile} {stem}Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses {row.profile} {stem}Table).clauses.toList.all
      (fun clause => clause.all (fun lit => lit != 0)) = true := by
    native_decide
  intro clause hclause lit hlit
  have hc : clause.all (fun entry => entry != 0) = true :=
    (List.all_eq_true.mp h) clause
      (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem {stem}Check :
    LRAT.check {stem}Proof
      (oneHighFamilyV2SatCnf {row.profile} {stem}Table) := by
  native_decide

theorem {stem}Checked :
    OneHighFamilyV2CheckedUnsat {row.profile} {stem}Table :=
  oneHighFamilyV2CheckedUnsat_of_lrat {stem}Nonzero
    {stem}Proof {stem}Check

def {stem}Entry : OneHighFamilyV2CheckedEntry {row.profile} where
  table := {stem}Table
  checked := {stem}Checked

end Erdos85
'''


def atomic_write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    try:
        temporary.write_text(text)
        os.replace(temporary, path)
    except BaseException:
        if temporary.exists():
            temporary.unlink()
        raise


def main() -> int:
    script = Path(__file__).resolve()
    repo = script.parents[4]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--cert-root", type=Path, required=True)
    parser.add_argument(
        "--inventory",
        type=Path,
        default=repo / "proofs/Proofs/Certificates/h1_orbit_inventory.compact",
    )
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--orbit", action="append", default=[])
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--skip-payload-hash", action="store_true")
    args = parser.parse_args()
    if args.all == bool(args.orbit):
        parser.error("choose exactly one of --all or one/more --orbit arguments")
    if args.output_dir is None:
        parser.error("--output-dir is required")

    profiles = read_inventory(args.inventory)
    rows = read_index(args.index)
    selected = rows if args.all else [row for row in rows if row.orbit in args.orbit]
    if not args.all and len(selected) != len(set(args.orbit)):
        found = {row.orbit for row in selected}
        raise ValueError(f"requested orbit(s) absent from index: {sorted(set(args.orbit) - found)}")

    for row in selected:
        payload = validate_row(row, profiles, args.cert_root, not args.skip_payload_hash)
        destination = args.output_dir / f"Erdos85H1V2CertP{row.profile}I{row.local_index:05d}.lean"
        atomic_write(destination, lean_source(row, payload))
        print(f"{row.orbit}\tprofile={row.profile}\tlocalIndex={row.local_index}\t{destination}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
