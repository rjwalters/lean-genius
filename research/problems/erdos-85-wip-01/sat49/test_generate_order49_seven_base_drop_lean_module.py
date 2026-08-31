import importlib.util
import json
import hashlib
import subprocess
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "seven_base_drop", HERE / "generate_order49_seven_base_drop_lean_module.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


def valid_document(directory):
    root = Path(directory)
    def core(argument, theorem, index, module="Proofs.Generated.CertificateBank"):
        source = root / (module.split(".")[-1] + ".lean")
        source.write_text("-- synthetic test-only source\n")
        source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
        receipt = root / f"{argument}.receipt.json"
        identity = {"schema": MOD.RECEIPT_SCHEMA,
            "consumer_argument": argument, "theorem": theorem,
            "source_module": module, "source_sha256": source_hash}
        receipt.write_bytes(MOD.canonical_receipt(identity))
        return {"consumer_argument": argument, "theorem": theorem,
                "source_module": module, "source_path": str(source),
                "source_sha256": source_hash, "aggregate_receipt_path": str(receipt),
                "aggregate_receipt_sha256": hashlib.sha256(receipt.read_bytes()).hexdigest()}
    rows = [core(*MOD.EXPECTED_INPUTS[0][::2], 0, MOD.EXPECTED_INPUTS[0][1])]
    for ordinal, (argument, cell, theorem) in enumerate(MOD.SMALL_HIGH):
        row = core(argument, theorem, ordinal + 1, MOD.EXPECTED_INPUTS[ordinal + 1][1])
        row.update(ordinal=ordinal, cell=cell,
                   leaf_evidence_identity_sha256=f"{ordinal + 40:064x}")
        receipt = {"schema": MOD.CELL_RECEIPT_SCHEMA, "ordinal": ordinal,
            "consumer_argument": argument, "cell": cell,
            "base_unsat_theorem": theorem, "source_module": row["source_module"],
            "source_sha256": row["source_sha256"], "leaf_count": 58,
            "leaf_job_ids": MOD.expected_leaf_ids(cell),
            "leaf_evidence_identity_sha256": row["leaf_evidence_identity_sha256"],
            "root_manifest_sha256": f"{100:064x}",
            "socket_table_sha256": f"{101:064x}",
            "expected_manifest_sha256": f"{102:064x}",
            "socket_validator_identity_sha256": f"{103:064x}"}
        receipt_path = root / f"{cell}.receipt.json"
        row["aggregate_receipt_path"] = str(receipt_path)
        receipt_path.write_bytes(MOD.canonical_receipt(receipt))
        row["aggregate_receipt_sha256"] = hashlib.sha256(receipt_path.read_bytes()).hexdigest()
        rows.append(row)
    rows.append(core("h7", MOD.EXPECTED_INPUTS[8][2], 8, MOD.EXPECTED_INPUTS[8][1]))
    first = json.loads(Path(rows[1]["aggregate_receipt_path"]).read_text())
    index = {"schema": MOD.CELL_INDEX_SCHEMA,
        **{field: first[field] for field in ("expected_manifest_sha256",
            "root_manifest_sha256", "socket_table_sha256",
            "socket_validator_identity_sha256", "source_module", "source_sha256")},
        "cells": [{"cell": row["cell"],
                   "receipt": Path(row["aggregate_receipt_path"]).name,
                   "receipt_sha256": row["aggregate_receipt_sha256"]}
                  for row in rows[1:8]]}
    index_path = root / "index.json"
    index_path.write_bytes(MOD.canonical_receipt(index))
    return {"schema": MOD.SCHEMA, "inputs": rows,
            "cell_aggregate_index_path": str(index_path),
            "cell_aggregate_index_sha256": hashlib.sha256(index_path.read_bytes()).hexdigest()}


class SevenBaseDropGeneratorTest(unittest.TestCase):
    def load(self, document, directory):
            path = Path(directory) / "inputs.json"
            path.write_text(json.dumps(document))
            return MOD.load_and_validate(path)

    def test_exact_nine_input_composition_shape(self):
        with tempfile.TemporaryDirectory() as directory:
            rows = self.load(valid_document(directory), directory)
        rendered = MOD.render(rows)
        self.assertIn("of_smallHighCubeBaseUnsat", rendered)
        self.assertNotIn("of_strata\n", rendered)
        self.assertNotIn("SmallHighDropFrontier", rendered)
        positions = [rendered.index(row["theorem"]) for row in rows]
        self.assertEqual(positions, sorted(positions))
        self.assertIn("minDegreeForC4_fortyEight_fortyNine_exact_checked", rendered)
        self.assertIn("minDegreeForC4_fortyNine_lt_fortyEight_checked", rendered)

    def test_rejects_missing_duplicate_reordered_or_mismatched_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            for kind in ("missing", "duplicate", "reordered", "mismatch", "legacy",
                         "mutated", "receipt-whitespace", "module-swap",
                         "cell-leaf-gap", "cell-global-drift", "source-symlink",
                         "index-symlink"):
                document = valid_document(directory)
                if kind == "missing": document["inputs"].pop()
                elif kind == "duplicate": document["inputs"][8]["aggregate_receipt_sha256"] = document["inputs"][0]["aggregate_receipt_sha256"]
                elif kind == "reordered": document["inputs"][1], document["inputs"][2] = document["inputs"][2], document["inputs"][1]
                elif kind == "mismatch": document["inputs"][1]["theorem"] = "Erdos85.wrong"
                elif kind == "legacy": document["inputs"][0]["source_module"] = "Proofs.Erdos85OrderFortyNineSmallHighDropFrontier"
                elif kind == "mutated": Path(document["inputs"][0]["source_path"]).write_text("mutated")
                elif kind == "receipt-whitespace":
                    receipt = Path(document["inputs"][0]["aggregate_receipt_path"])
                    receipt.write_bytes(receipt.read_bytes() + b"\n")
                    document["inputs"][0]["aggregate_receipt_sha256"] = hashlib.sha256(receipt.read_bytes()).hexdigest()
                elif kind == "module-swap": document["inputs"][0]["source_module"] = document["inputs"][8]["source_module"]
                elif kind in ("cell-leaf-gap", "cell-global-drift"):
                    row = document["inputs"][1 if kind == "cell-leaf-gap" else 2]
                    receipt = Path(row["aggregate_receipt_path"])
                    value = json.loads(receipt.read_text())
                    if kind == "cell-leaf-gap": value["leaf_job_ids"].pop()
                    else: value["root_manifest_sha256"] = f"{999:064x}"
                    receipt.write_bytes(MOD.canonical_receipt(value))
                    row["aggregate_receipt_sha256"] = hashlib.sha256(receipt.read_bytes()).hexdigest()
                elif kind == "source-symlink":
                    row = document["inputs"][0]
                    link_dir = Path(directory) / "links"; link_dir.mkdir(exist_ok=True)
                    link = link_dir / Path(row["source_path"]).name
                    link.symlink_to(row["source_path"])
                    row["source_path"] = str(link)
                else:
                    target = Path(document["cell_aggregate_index_path"])
                    link = Path(directory) / "index-link.json"; link.symlink_to(target)
                    document["cell_aggregate_index_path"] = str(link)
                with self.subTest(kind=kind), self.assertRaises(ValueError):
                    self.load(document, directory)

    def test_create_only_publication_refuses_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "Generated.lean"
            MOD.atomic_create(output, "first")
            with self.assertRaises(FileExistsError):
                MOD.atomic_create(output, "second")
            self.assertEqual(output.read_text(), "first")

    def test_synthetic_test_only_stubs_compile_composition(self):
        with tempfile.TemporaryDirectory() as directory:
            rows = self.load(valid_document(directory), directory)
            rendered = MOD.render(rows)
            body = rendered[rendered.index("namespace Erdos85"):]
            declarations = ["/- Synthetic test-only sockets; never emitted. -/",
                "namespace Erdos85", "axiom C4FreeMinDegreeWitness : Nat → Nat → Prop",
                "axiom minDegreeForC4 : Nat → Nat",
                *(f"axiom P{i} : Prop" for i in range(9)),
                "axiom orderFortyNineStratumExcluded_one_of_generatedCertificates : P0",
                *(f"axiom {theorem.split('.')[-1]} : P{i}" for i, (_, _, theorem) in enumerate(MOD.EXPECTED_INPUTS[1:8], 1)),
                "axiom orderFortyNineStratumExcluded_seven_of_generatedCertificates : P8",
                "axiom not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighCubeBaseUnsat : P0 → P1 → P2 → P3 → P4 → P5 → P6 → P7 → P8 → ¬ C4FreeMinDegreeWitness 49 7",
                "axiom minDegreeForC4_fortyEight_fortyNine_exact_checked : (¬ C4FreeMinDegreeWitness 49 7) → minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7",
                "axiom minDegreeForC4_fortyNine_lt_fortyEight_checked : (¬ C4FreeMinDegreeWitness 49 7) → minDegreeForC4 49 < minDegreeForC4 48",
                "end Erdos85", "", body]
            source = Path(directory) / "SyntheticSevenBaseWrapper.lean"
            source.write_text("\n".join(declarations))
            subprocess.run(["lake", "env", "lean", str(source)],
                           cwd=HERE.parents[3] / "proofs", check=True,
                           text=True)


if __name__ == "__main__":
    unittest.main()
