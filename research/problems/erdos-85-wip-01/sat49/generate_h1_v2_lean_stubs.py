#!/usr/bin/env python3
"""Validate cert-root v3 and emit packed exact-v2 Lean certificate stubs.

Only packed LRATs whose source compacts already passed direct Lean replay may
be emitted.  Every packed payload is hash/size checked before source emission.
Operational orbit tags are checked as provenance but never occur in the table
type.  By default each generated theorem is indexed by ``(profile,
localIndex)`` into ``oneHighInventoryTables``.  A terminal campaign may also
supply its ordered jobs manifest and terminal table-list definition; emitted
tables then use the corresponding terminal-local index, making an ordered
checked bank definitionally cover that consumer inventory.
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


@dataclass(frozen=True)
class TerminalTableTarget:
    module: str
    definition: str
    index: int
    profile_indexed: bool = False
    raw_inventory_table: bool = False


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


def lean_source(
    row: IndexRow, payload: Path, terminal: TerminalTableTarget | None = None
) -> str:
    stem = f"h1V2P{row.profile}I{row.local_index:05d}"
    path_literal = json.dumps(str(payload))
    terminal_import = f"import {terminal.module}\n" if terminal else ""
    terminal_table_expr = (
        f"({terminal.definition} ({row.profile} : Fin 5))"
        if terminal and terminal.profile_indexed
        else terminal.definition if terminal else ""
    )
    table_source = (
        f"  (oneHighInventoryTables ({row.profile} : Fin 5)).get\n"
        f"    ⟨{row.local_index}, by native_decide⟩"
        if terminal and terminal.raw_inventory_table else
        f"  {terminal_table_expr}.get\n"
        f"    ⟨{terminal.index}, by native_decide⟩"
        if terminal
        else f"  (oneHighInventoryTables ({row.profile} : Fin 5)).get\n"
             f"    ⟨{row.local_index}, by native_decide⟩"
    )
    terminal_metadata = (
        f"    terminal_table={terminal.definition} terminalIndex={terminal.index}"
        f" profileIndexed={str(terminal.profile_indexed).lower()}"
        f" rawInventoryTable={str(terminal.raw_inventory_table).lower()}\n"
        if terminal else ""
    )
    return f'''import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
{terminal_import}

/-! GENERATED exact-v2 certificate stub.
    profile={row.profile} localIndex={row.local_index}
{terminal_metadata}    orbit={row.orbit}
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

set_option maxHeartbeats 0 in
def {stem}Table : OneHighMissTable :=
{table_source}

private def {stem}ProofText : String :=
  include_str {path_literal}

private def {stem}RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof {stem}ProofText
    {row.frame_bytes} {row.binary_bytes}

private def {stem}Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf {row.profile} {stem}Table)
    {stem}RawProof).toOption.get!

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
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf {row.profile} {stem}Table)
        {stem}RawProof) := by
  native_decide

theorem {stem}Checked :
    OneHighFamilyV2CheckedUnsat {row.profile} {stem}Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat {stem}Nonzero
    {stem}RawProof {stem}Proof {stem}Check

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
    parser.add_argument(
        "--batch-size",
        type=int,
        help="emit one deterministic contiguous batch of this many selected rows",
    )
    parser.add_argument(
        "--batch-index",
        type=int,
        help="zero-based batch to emit; requires --batch-size",
    )
    parser.add_argument(
        "--manifest-output",
        type=Path,
        help="atomically write a JSON receipt describing the emitted batch",
    )
    parser.add_argument("--orbit", action="append", default=[])
    parser.add_argument("--all", action="store_true")
    parser.add_argument(
        "--terminal-intersection",
        action="store_true",
        help="emit every indexed certificate whose orbit occurs in terminal jobs",
    )
    parser.add_argument("--skip-payload-hash", action="store_true")
    parser.add_argument(
        "--terminal-jobs",
        type=Path,
        help="ordered seven-field campaign jobs TSV; orbit order becomes terminal-local order",
    )
    parser.add_argument(
        "--terminal-module",
        help="Lean module defining the campaign terminal table list",
    )
    parser.add_argument(
        "--terminal-table-def",
        help="qualified Lean name of the campaign terminal table list",
    )
    parser.add_argument(
        "--terminal-profile-indexed",
        action="store_true",
        help=(
            "the terminal table definition takes `(profile : Fin 5)`; "
            "compute terminal indices independently within each profile"
        ),
    )
    parser.add_argument(
        "--terminal-raw-inventory-table",
        action="store_true",
        help=(
            "record terminal membership/index metadata but define the checked "
            "table by its cheaper authoritative raw-inventory index"
        ),
    )
    args = parser.parse_args()
    selection_modes = int(args.all) + int(bool(args.orbit)) + int(args.terminal_intersection)
    if selection_modes != 1:
        parser.error(
            "choose exactly one of --all, --terminal-intersection, or "
            "one/more --orbit arguments"
        )
    if args.output_dir is None:
        parser.error("--output-dir is required")
    if (args.batch_size is None) != (args.batch_index is None):
        parser.error("--batch-size and --batch-index must be supplied together")
    if args.batch_size is not None and args.batch_size <= 0:
        parser.error("--batch-size must be positive")
    if args.batch_index is not None and args.batch_index < 0:
        parser.error("--batch-index must be nonnegative")
    terminal_options = (
        args.terminal_jobs, args.terminal_module, args.terminal_table_def
    )
    if any(terminal_options) and not all(terminal_options):
        parser.error(
            "--terminal-jobs, --terminal-module, and --terminal-table-def "
            "must be supplied together"
        )
    if args.terminal_profile_indexed and not all(terminal_options):
        parser.error("--terminal-profile-indexed requires the three terminal options")
    if args.terminal_intersection and not all(terminal_options):
        parser.error("--terminal-intersection requires the three terminal options")
    if args.terminal_raw_inventory_table and not all(terminal_options):
        parser.error("--terminal-raw-inventory-table requires the three terminal options")
    lean_name = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
    if args.terminal_module and not lean_name.fullmatch(args.terminal_module):
        parser.error("--terminal-module is not a qualified Lean identifier")
    if args.terminal_table_def and not lean_name.fullmatch(args.terminal_table_def):
        parser.error("--terminal-table-def is not a qualified Lean identifier")

    profiles = read_inventory(args.inventory)
    rows = read_index(args.index)
    selected = rows if args.all else [row for row in rows if row.orbit in args.orbit]
    if not args.all and not args.terminal_intersection and len(selected) != len(set(args.orbit)):
        found = {row.orbit for row in selected}
        raise ValueError(f"requested orbit(s) absent from index: {sorted(set(args.orbit) - found)}")

    terminal_indices: dict[str, int] | None = None
    terminal_profiles: dict[str, int] | None = None
    if args.terminal_jobs:
        terminal_rows: list[tuple[str, int]] = []
        for line_number, line in enumerate(args.terminal_jobs.read_text().splitlines(), 1):
            fields = line.split("\t")
            if len(fields) != 7 or not re.fullmatch(r"[0-9a-f]{16}", fields[0]):
                raise ValueError(
                    f"{args.terminal_jobs}:{line_number}: malformed seven-field job"
                )
            try:
                profile = int(fields[1])
            except ValueError as error:
                raise ValueError(
                    f"{args.terminal_jobs}:{line_number}: invalid profile"
                ) from error
            if profile not in range(5):
                raise ValueError(
                    f"{args.terminal_jobs}:{line_number}: profile outside 0..4"
                )
            terminal_rows.append((fields[0], profile))
        terminal_tags = [tag for tag, _ in terminal_rows]
        if len(terminal_tags) != len(set(terminal_tags)):
            raise ValueError(f"{args.terminal_jobs}: duplicate orbit tag")
        if args.terminal_profile_indexed:
            profile_counts = [0] * 5
            terminal_indices = {}
            for tag, profile in terminal_rows:
                terminal_indices[tag] = profile_counts[profile]
                profile_counts[profile] += 1
        else:
            terminal_indices = {
                tag: index for index, tag in enumerate(terminal_tags)
            }
        terminal_profiles = dict(terminal_rows)
        if args.terminal_intersection:
            selected = [row for row in rows if row.orbit in terminal_indices]
        missing = {row.orbit for row in selected} - terminal_indices.keys()
        if missing:
            raise ValueError(
                "selected certificate orbit(s) absent from terminal jobs: "
                f"{sorted(missing)}"
            )
        mismatched = [
            row.orbit for row in selected
            if terminal_profiles[row.orbit] != row.profile
        ]
        if mismatched:
            raise ValueError(
                "selected certificate profile disagrees with terminal jobs: "
                f"{sorted(mismatched)}"
            )

    selected_total = len(selected)
    batch_count = 1
    if args.batch_size is not None:
        batch_count = (
            selected_total + args.batch_size - 1
        ) // args.batch_size
        if args.batch_index >= batch_count:
            raise ValueError(
                f"--batch-index {args.batch_index} is outside 0..{batch_count - 1} "
                f"for {selected_total} selected rows"
            )
        start = args.batch_index * args.batch_size
        selected = selected[start : start + args.batch_size]

    emitted = []
    for row in selected:
        payload = validate_row(row, profiles, args.cert_root, not args.skip_payload_hash)
        destination = args.output_dir / f"Erdos85H1V2CertP{row.profile}I{row.local_index:05d}.lean"
        terminal = (
            TerminalTableTarget(
                args.terminal_module,
                args.terminal_table_def,
                terminal_indices[row.orbit],
                args.terminal_profile_indexed,
                args.terminal_raw_inventory_table,
            )
            if terminal_indices is not None else None
        )
        atomic_write(destination, lean_source(row, payload, terminal))
        terminal_field = f"\tterminalIndex={terminal.index}" if terminal else ""
        print(
            f"{row.orbit}\tprofile={row.profile}\tlocalIndex={row.local_index}"
            f"{terminal_field}\t{destination}"
        )
        emitted.append({
            "orbit": row.orbit,
            "profile": row.profile,
            "local_index": row.local_index,
            "packed_lz4_sha256": row.packed_sha,
            "packed_lz4_bytes": row.packed_bytes,
            "payload": str(payload),
            "lean_source": str(destination.resolve()),
            "lean_source_sha256": sha256(destination),
            **(
                {"terminal_index": terminal.index}
                if terminal is not None else {}
            ),
        })
    if args.manifest_output is not None:
        receipt = {
            "schema": "erdos85-h1-v2-lean-stub-batch-v1",
            "index": str(args.index.resolve()),
            "index_sha256": sha256(args.index),
            "cert_root": str(args.cert_root.resolve()),
            "selected_total": selected_total,
            "batch_size": args.batch_size,
            "batch_index": args.batch_index,
            "batch_count": batch_count,
            "entries": emitted,
        }
        atomic_write(
            args.manifest_output,
            json.dumps(receipt, indent=2, sort_keys=True) + "\n",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
