#!/usr/bin/env python3
"""Generate the provenance-bound seven-base order-49 drop wrapper."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
from pathlib import Path


LEAN_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+")
SHA256 = re.compile(r"[0-9a-f]{64}")
SCHEMA = "erdos85-order49-seven-base-drop-inputs-v1"
SMALL_HIGH = (
    ("hb1", "h3_b1", "Erdos85.smallHighH3B1Base_unsat"),
    ("hc1", "h3_c1", "Erdos85.smallHighH3C1Base_unsat"),
    ("hc2", "h3_c2", "Erdos85.smallHighH3C2Base_unsat"),
    ("hdist2", "h3_dist2", "Erdos85.smallHighH3Dist2Base_unsat"),
    ("h50", "h5_t0", "Erdos85.smallHighH5T0Base_unsat"),
    ("h51", "h5_t1", "Erdos85.smallHighH5T1Base_unsat"),
    ("h52", "h5_t2", "Erdos85.smallHighH5T2Base_unsat"),
)
EXPECTED_INPUTS = (
    ("h1", "Proofs.Generated.Erdos85OrderFortyNineOneHighCertificates",
     "Erdos85.orderFortyNineStratumExcluded_one_of_generatedCertificates"),
    *((argument, "Proofs.Generated.Erdos85OrderFortyNineSmallHighCertificates", theorem)
      for argument, _, theorem in SMALL_HIGH),
    ("h7", "Proofs.Generated.Erdos85OrderFortyNineSevenHighCertificates",
     "Erdos85.orderFortyNineStratumExcluded_seven_of_generatedCertificates"),
)
CORE_FIELDS = {
    "consumer_argument", "theorem", "source_module", "source_sha256",
    "source_path", "aggregate_receipt_sha256", "aggregate_receipt_path",
}
RECEIPT_SCHEMA = "erdos85-order49-wrapper-provenance-v1"
CELL_RECEIPT_SCHEMA = "erdos85-small-high-cell-aggregate-v1"
CELL_INDEX_SCHEMA = "erdos85-small-high-cell-aggregate-index-v1"
FORBIDDEN_MODULE_PARTS = ("SmallHighDropFrontier", "PartitionedCanonicalDropFrontier")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_receipt(identity: dict) -> bytes:
    return (json.dumps(identity, ensure_ascii=True, allow_nan=False,
                       sort_keys=True, separators=(",", ":")) + "\n").encode()


def _validate_core(row: dict, argument: str, singleton: bool) -> dict:
    if not isinstance(row, dict) or not CORE_FIELDS <= set(row):
        raise ValueError(f"{argument}: missing provenance fields")
    if row["consumer_argument"] != argument:
        raise ValueError(f"expected consumer_argument {argument}")
    for field in ("theorem", "source_module"):
        if not isinstance(row[field], str) or not LEAN_NAME.fullmatch(row[field]):
            raise ValueError(f"{argument}: invalid fully-qualified {field}")
    for field in ("source_sha256", "aggregate_receipt_sha256"):
        if not isinstance(row[field], str) or not SHA256.fullmatch(row[field]):
            raise ValueError(f"{argument}: invalid {field}")
    if any(part in row["source_module"] for part in FORBIDDEN_MODULE_PARTS):
        raise ValueError(f"{argument}: legacy five-check module is forbidden")
    source = Path(row["source_path"])
    receipt_path = Path(row["aggregate_receipt_path"])
    if (not source.is_absolute() or source.is_symlink() or not source.is_file()
            or source.name != row["source_module"].split(".")[-1] + ".lean"):
        raise ValueError(f"{argument}: source path/module mismatch")
    if sha256(source) != row["source_sha256"]:
        raise ValueError(f"{argument}: source hash mismatch")
    if (not receipt_path.is_absolute() or receipt_path.is_symlink()
            or not receipt_path.is_file()
            or sha256(receipt_path) != row["aggregate_receipt_sha256"]):
        raise ValueError(f"{argument}: aggregate receipt hash mismatch")
    receipt = json.loads(receipt_path.read_text())
    if singleton:
        expected = {"schema": RECEIPT_SCHEMA, "consumer_argument": argument,
                    "theorem": row["theorem"], "source_module": row["source_module"],
                    "source_sha256": row["source_sha256"]}
        if receipt != expected or receipt_path.read_bytes() != canonical_receipt(expected):
            raise ValueError(f"{argument}: receipt identity mismatch")
    return receipt


def expected_leaf_ids(cell: str) -> list[str]:
    return [f"{cell}.cover-left", f"{cell}.cover-right",
            *(f"{cell}.cube-{li}-{ri}" for li in range(7) for ri in range(8))]


def load_and_validate(path: Path) -> list[dict]:
    if not path.is_absolute() or path.is_symlink() or not path.is_file():
        raise ValueError("--inputs must be an absolute regular non-symlink file")
    document = json.loads(path.read_text())
    document_fields = {"schema", "inputs", "cell_aggregate_index_path",
                       "cell_aggregate_index_sha256"}
    if not isinstance(document, dict) or set(document) != document_fields or document.get("schema") != SCHEMA:
        raise ValueError("unsupported seven-base wrapper input schema")
    rows = document.get("inputs")
    if not isinstance(rows, list) or len(rows) != 9:
        raise ValueError("inputs must contain exactly H1, seven bases, and H7")
    expected_arguments = ["h1", *(x[0] for x in SMALL_HIGH), "h7"]
    if [row.get("consumer_argument") for row in rows if isinstance(row, dict)] != expected_arguments:
        raise ValueError("inputs are missing, duplicated, or out of consumer order")
    receipts = [_validate_core(row, argument, index in (0, 8))
                for index, (row, argument) in enumerate(
                    zip(rows, expected_arguments, strict=True))]
    identities = tuple((row["consumer_argument"], row["source_module"], row["theorem"])
                       for row in rows)
    if identities != EXPECTED_INPUTS:
        raise ValueError("the nine theorem/module identities do not match the pinned endpoints")
    for ordinal, (row, (argument, cell, theorem)) in enumerate(
            zip(rows[1:8], SMALL_HIGH, strict=True)):
        required = CORE_FIELDS | {"ordinal", "cell", "leaf_evidence_identity_sha256"}
        if set(row) != required:
            raise ValueError(f"{argument}: small-high row has wrong fields")
        if (row["ordinal"], row["cell"], row["theorem"]) != (ordinal, cell, theorem):
            raise ValueError(f"{argument}: small-high identity mismatch")
        if not SHA256.fullmatch(str(row["leaf_evidence_identity_sha256"])):
            raise ValueError(f"{argument}: invalid leaf evidence identity hash")
        receipt = receipts[ordinal + 1]
        receipt_fields = {"base_unsat_theorem", "cell", "consumer_argument",
            "expected_manifest_sha256", "leaf_count", "leaf_evidence_identity_sha256",
            "leaf_job_ids", "ordinal", "root_manifest_sha256", "schema",
            "socket_table_sha256", "socket_validator_identity_sha256",
            "source_module", "source_sha256"}
        if not isinstance(receipt, dict) or set(receipt) != receipt_fields:
            raise ValueError(f"{argument}: wrong cell aggregate receipt fields")
        if (receipt["schema"], receipt["ordinal"], receipt["consumer_argument"],
                receipt["cell"], receipt["base_unsat_theorem"], receipt["leaf_count"],
                receipt["source_module"], receipt["source_sha256"],
                receipt["leaf_evidence_identity_sha256"], receipt["leaf_job_ids"]) != (
                CELL_RECEIPT_SCHEMA, ordinal, argument, cell, theorem, 58,
                row["source_module"], row["source_sha256"],
                row["leaf_evidence_identity_sha256"], expected_leaf_ids(cell)):
            raise ValueError(f"{argument}: cell aggregate receipt identity mismatch")
        for field in ("expected_manifest_sha256", "root_manifest_sha256",
                      "socket_table_sha256", "socket_validator_identity_sha256"):
            if not isinstance(receipt[field], str) or not SHA256.fullmatch(receipt[field]):
                raise ValueError(f"{argument}: invalid aggregate global pin {field}")
        if Path(row["aggregate_receipt_path"]).read_bytes() != canonical_receipt(receipt):
            raise ValueError(f"{argument}: cell receipt bytes are not canonical")
    small_modules = {row["source_module"] for row in rows[1:8]}
    small_paths = {row["source_path"] for row in rows[1:8]}
    small_hashes = {row["source_sha256"] for row in rows[1:8]}
    if len(small_modules) != 1 or len(small_paths) != 1 or len(small_hashes) != 1:
        raise ValueError("the seven bases must come from one generated source")
    if set(rows[0]) != CORE_FIELDS or set(rows[8]) != CORE_FIELDS:
        raise ValueError("H1/H7 rows must contain exactly the singleton provenance fields")
    receipt_hashes = [row["aggregate_receipt_sha256"] for row in rows]
    if len(set(receipt_hashes)) != 9:
        raise ValueError("all nine aggregate receipts must be distinct")
    leaf_identities = [row["leaf_evidence_identity_sha256"] for row in rows[1:8]]
    if len(set(leaf_identities)) != 7:
        raise ValueError("all seven leaf socket identity hashes must be distinct")
    for field in ("expected_manifest_sha256", "root_manifest_sha256",
                  "socket_table_sha256", "socket_validator_identity_sha256"):
        if len({receipt[field] for receipt in receipts[1:8]}) != 1:
            raise ValueError(f"seven cell receipts disagree on {field}")
    index_path = Path(document["cell_aggregate_index_path"])
    index_pin = document["cell_aggregate_index_sha256"]
    if (not index_path.is_absolute() or index_path.is_symlink() or not index_path.is_file()
            or not isinstance(index_pin, str) or not SHA256.fullmatch(index_pin)
            or sha256(index_path) != index_pin):
        raise ValueError("invalid cell aggregate index path/hash")
    index = json.loads(index_path.read_text())
    index_fields = {"cells", "expected_manifest_sha256", "root_manifest_sha256",
        "schema", "socket_table_sha256", "socket_validator_identity_sha256",
        "source_module", "source_sha256"}
    if (not isinstance(index, dict) or set(index) != index_fields
            or index_path.read_bytes() != canonical_receipt(index)
            or index["schema"] != CELL_INDEX_SCHEMA):
        raise ValueError("invalid or noncanonical cell aggregate index")
    expected_cells = []
    for row, (_, cell, _) in zip(rows[1:8], SMALL_HIGH, strict=True):
        receipt_name = f"{cell}.receipt.json"
        expected_path = index_path.parent / receipt_name
        if Path(row["aggregate_receipt_path"]) != expected_path:
            raise ValueError(f"{cell}: row receipt is outside the indexed set")
        expected_cells.append({"cell": cell, "receipt": receipt_name,
                               "receipt_sha256": row["aggregate_receipt_sha256"]})
    if index["cells"] != expected_cells:
        raise ValueError("aggregate index does not bind the exact seven receipts")
    first = receipts[1]
    for field in ("expected_manifest_sha256", "root_manifest_sha256",
                  "socket_table_sha256", "socket_validator_identity_sha256",
                  "source_module", "source_sha256"):
        if index[field] != first[field]:
            raise ValueError(f"aggregate index disagrees on {field}")
    return rows


def render(rows: list[dict]) -> str:
    modules = list(dict.fromkeys(row["source_module"] for row in rows))
    theorems = [row["theorem"] for row in rows]
    lines = [*(f"import {module}" for module in modules),
             "import Proofs.Erdos85OrderFortyNineSmallHighCubeGridTerminal",
             "import Proofs.Erdos85FiniteDropWitnesses", "",
             "/-! GENERATED from nine reviewed provenance inputs; no legacy five-check frontier. -/",
             "", "namespace Erdos85", "",
             "theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_generatedSevenBaseCertificates :",
             "    ¬ C4FreeMinDegreeWitness 49 7 :=",
             "  not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighCubeBaseUnsat"]
    lines.extend(f"    {theorem}" for theorem in theorems)
    lines.extend(["",
        "theorem minDegreeForC4_fortyEight_fortyNine_exact_of_generatedSevenBaseCertificates :",
        "    minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7 :=",
        "  minDegreeForC4_fortyEight_fortyNine_exact_checked",
        "    not_c4FreeMinDegreeWitness_fortyNine_seven_of_generatedSevenBaseCertificates", "",
        "theorem minDegreeForC4_fortyNine_lt_fortyEight_of_generatedSevenBaseCertificates :",
        "    minDegreeForC4 49 < minDegreeForC4 48 :=",
        "  minDegreeForC4_fortyNine_lt_fortyEight_checked",
        "    not_c4FreeMinDegreeWitness_fortyNine_seven_of_generatedSevenBaseCertificates", "",
        "end Erdos85", ""])
    return "\n".join(lines)


def atomic_create(path: Path, source: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    try:
        with temporary.open("x") as stream:
            stream.write(source)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, path)
        directory_fd = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rows = load_and_validate(args.inputs)
    atomic_create(args.output, render(rows))
    print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
