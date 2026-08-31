import importlib.util
import json
import hashlib
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "seven_base_drop", HERE / "generate_order49_seven_base_drop_lean_module.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


def valid_document(directory):
    root = Path(directory).resolve()
    root.mkdir(parents=True, exist_ok=True)
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
    repo = root / "repo"
    producer = repo / MOD.FINALIZER_PRODUCER_PATH
    producer.parent.mkdir(parents=True, exist_ok=True); producer.write_text("# synthetic finalizer producer\n")
    producer_sha = MOD.sha256(producer); MOD.FINALIZER_PRODUCER_SHA256 = producer_sha
    original = repo / "proofs/Proofs/Generated/Erdos85OrderFortyNineOneHighCertificates.lean"
    original.parent.mkdir(parents=True, exist_ok=True)
    original.write_text("theorem orderFortyNineStratumExcluded_one_of_generatedCertificates : True := trivial\n")
    final_root = root / "h1-final"; final_root.mkdir(exist_ok=True)
    retained_source = final_root / "evidence/endpoint/Erdos85OrderFortyNineOneHighCertificates.lean"
    retained_olean = final_root / "evidence/endpoint/Erdos85OrderFortyNineOneHighCertificates.olean"
    projection_path = final_root / "evidence/consumer/h1-provenance.json"
    retained_source.parent.mkdir(parents=True, exist_ok=True); retained_olean.write_bytes(b"olean\n"); projection_path.parent.mkdir(parents=True, exist_ok=True)
    retained_source.write_bytes(original.read_bytes())
    h1 = rows[0]; h1["source_path"] = str(retained_source); h1["source_sha256"] = MOD.sha256(retained_source)
    projection = {"schema": MOD.RECEIPT_SCHEMA, "consumer_argument": "h1", "theorem": h1["theorem"],
                  "source_module": h1["source_module"], "source_sha256": h1["source_sha256"]}
    projection_path.write_bytes(MOD.canonical_receipt(projection)); h1["aggregate_receipt_path"] = str(projection_path)
    h1["aggregate_receipt_sha256"] = MOD.sha256(projection_path)
    control_rows = []
    for path in ("proofs/lean-toolchain","proofs/lakefile.toml","proofs/lake-manifest.json"):
        target = repo / path; target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(b"x")
        control_rows.append({"blob_oid":"a"*40,"bytes":1,"path":path,"sha256":MOD.sha256(target)})
    tool_identities = {"python_sha256":"7"*64,"lean_sha256":"8"*64,"lake_sha256":"9"*64}
    source_commit = "b" * 40; review_id = "123"
    artifact_paths = [retained_source, retained_olean, projection_path]
    def retained(relative, value, contract):
        value = {key: value.get(key) for key in MOD.RETAINED_FIELDS[contract]}
        target = final_root / relative; target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(MOD.canonical_receipt(value)); artifact_paths.append(target); return target
    cache_entries = [{"bytes": 1, "path": "cache-entry", "sha256": "d" * 64}]
    cache_identity = hashlib.sha256(MOD.canonical_receipt(cache_entries)).hexdigest()
    cache_path = retained("evidence/cache/cache-manifest.json", {"schema": MOD.UPSTREAM_SCHEMAS["cache_manifest"],
        "entries": cache_entries, "identity_sha256": cache_identity, "root": str(root / "cache")}, "cache_manifest")
    snapshot_path = retained("evidence/receipts/cache-snapshot.json", {"schema": MOD.UPSTREAM_SCHEMAS["cache_snapshot"],
        "cache_manifest_sha256": MOD.sha256(cache_path), "control_files": control_rows,
        "source_commit": source_commit}, "cache_snapshot")
    payload_rows = [{"packed_lz4_bytes": 1, "packed_lz4_path": f"payload/{index}",
                     "packed_lz4_sha256": f"{index + 1:064x}"} for index in range(13351)]
    payload_path = retained("evidence/post-chain/payload-index.json", {
        "schema": "erdos85-h1-capacity-payload-index-v1", "profile_counts": MOD.PROFILE_COUNTS, "rows": payload_rows}, "payload")
    replay_rows = [{"tag": f"{index:016x}"} for index in range(13351)]
    replay_identity = hashlib.sha256(MOD.canonical_receipt(replay_rows)).hexdigest()
    replay_path = retained("evidence/post-chain/replay-audit.json", {
        "schema": "erdos85-h1-capacity-replay-audit-v1", "profile_counts": MOD.PROFILE_COUNTS,
        "replay_evidence_identity_sha256": replay_identity, "rows": replay_rows}, "replay")
    coverage_path = retained("evidence/post-chain/coverage/receipt.json", {
        "schema": "erdos85-h1-coverage-audit-snapshot-v1", "summary": dict(MOD.TERMINAL_COUNTS)}, "coverage")
    evidence_path = retained("evidence/post/leaf-evidence.json", {
        "schema": "erdos85-h1-committed-leaf-evidence-v1", "leaf_count": 13351,
        "profile_counts": MOD.PROFILE_COUNTS, "generated_tree_identity_sha256": "1" * 64,
        "review_id": review_id, "reviewed_commit": source_commit}, "evidence")
    payload_identity = hashlib.sha256(MOD.canonical_receipt([{"bytes": item["packed_lz4_bytes"],
        "path": item["packed_lz4_path"], "sha256": item["packed_lz4_sha256"]} for item in payload_rows])).hexdigest()
    bank_path = retained("evidence/post-chain/bank-receipt.json", {
        "schema": "erdos85-h1-capacity-payload-bank-v1", "leaf_count": 13351,
        "profile_counts": MOD.PROFILE_COUNTS, "coverage_terminal_counts": MOD.TERMINAL_COUNTS,
        "payload_identity_sha256": payload_identity, "payload_index_sha256": MOD.sha256(payload_path),
        "replay_audit_sha256": MOD.sha256(replay_path), "coverage_receipt_sha256": MOD.sha256(coverage_path)}, "bank")
    post_values = {key: f"{number:064x}" for number, key in enumerate(("adapter_receipt_sha256",
        "aggregate_layout_sha256", "capacity_reindex_receipt_sha256", "leaf_module_index_sha256"), 20)}
    post_path = retained("evidence/receipts/post-module.json", {"schema": MOD.UPSTREAM_SCHEMAS["post_module"],
        **post_values, "bank_receipt_sha256": MOD.sha256(bank_path), "evidence_sha256": MOD.sha256(evidence_path),
        "leaf_count": 13351, "profile_counts": MOD.PROFILE_COUNTS, "generated_tree_identity_sha256": "1" * 64,
        "review_id": review_id, "reviewed_commit": source_commit, "commit_object_oid": source_commit}, "post_module")
    compiled = [{"artifact_path": "a", "build_path": "a.olean", "bytes": 1, "sha256": "a" * 64},
                {"artifact_path": "b", "build_path": "a.ilean", "bytes": 1, "sha256": "b" * 64}]
    cold_path = retained("evidence/receipts/cold.json", {"schema": MOD.UPSTREAM_SCHEMAS["cold"],
        "retained_generated_artifacts": compiled, "cache_identity_sha256": cache_identity,
        "cache_manifest_sha256": MOD.sha256(cache_path), "post_module_receipt_sha256": MOD.sha256(post_path),
        "reviewed_control_files": control_rows, "image": MOD.H1_IMAGE, "source_commit": source_commit,
        "review_id": review_id}, "cold")
    project_sources = [{"path": original.relative_to(repo).as_posix(), "sha256": MOD.sha256(original)}]
    axiom_path = retained("evidence/receipts/axiom.json", {"schema": MOD.UPSTREAM_SCHEMAS["axiom"],
        "producer_sha256": MOD.AXIOM_PRODUCER_SHA256, "foundational_axioms": ["Classical.choice", "Quot.sound", "propext"],
        "native_root_count": 1, "theorem_count": 1,
        "tool_identities": tool_identities, "image": MOD.H1_IMAGE, "source_commit": source_commit,
        "project_cone_source_identities": project_sources, "cold_receipt_sha256": MOD.sha256(cold_path),
        "cache_manifest_sha256": MOD.sha256(cache_path), "cache_snapshot_receipt_sha256": MOD.sha256(snapshot_path)}, "axiom")
    retained_upstream = {"axiom": axiom_path, "cache_manifest": cache_path, "cache_snapshot": snapshot_path,
                         "cold": cold_path, "post_module": post_path}
    upstream = {name: {"bytes": target.stat().st_size, "path": target.relative_to(final_root).as_posix(),
                       "schema": MOD.UPSTREAM_SCHEMAS[name], "sha256": MOD.sha256(target)}
                for name, target in retained_upstream.items()}
    artifacts = sorted(({"bytes": path.stat().st_size, "path": path.relative_to(final_root).as_posix(),
                         "sha256": MOD.sha256(path)} for path in artifact_paths), key=lambda row: row["path"])
    hashes = {**post_values, "bank_receipt_sha256": MOD.sha256(bank_path),
        "evidence_sha256": MOD.sha256(evidence_path), "payload_identity_sha256": payload_identity,
        "payload_index_sha256": MOD.sha256(payload_path), "replay_audit_sha256": MOD.sha256(replay_path),
        "coverage_receipt_sha256": MOD.sha256(coverage_path), "replay_evidence_identity_sha256": replay_identity}
    final = {"schema": MOD.FINAL_RECEIPT_SCHEMA, "repo": str(repo), "source_commit": source_commit,
        "producer_path": str(producer), "producer_sha256": producer_sha,
        "producer_identity": {"blob_oid":"a"*40, "bytes":producer.stat().st_size, "commit":"b"*40,
                              "path":MOD.FINALIZER_PRODUCER_PATH, "sha256":producer_sha},
        "artifacts": artifacts, "endpoint_identity": {"generated_tree_identity_sha256":"1"*64,
            "module":h1["source_module"], "theorem":h1["theorem"], "source_path":retained_source.relative_to(final_root).as_posix(),
            "source_sha256":h1["source_sha256"], "source_bytes":retained_source.stat().st_size, "source_blob_oid":"a"*40,
            "original_source_path":original.relative_to(repo).as_posix(), "olean_path":retained_olean.relative_to(final_root).as_posix(),
            "olean_sha256":MOD.sha256(retained_olean), "olean_bytes":retained_olean.stat().st_size},
        "consumer_projection_identity":{"bytes":projection_path.stat().st_size,"path":projection_path.relative_to(final_root).as_posix(),
            "schema":MOD.RECEIPT_SCHEMA,"sha256":MOD.sha256(projection_path)},
        "terminal_capacity":{**hashes,"status":"PASS","leaf_count":13351,"profile_counts":MOD.PROFILE_COUNTS,
                             "terminal_counts":MOD.TERMINAL_COUNTS},
        "audit_identity":{"foundational_axioms":["Classical.choice","Quot.sound","propext"],"native_root_count":1,
            "producer_sha256":MOD.AXIOM_PRODUCER_SHA256,
            "project_cone_identity_sha256":hashlib.sha256(MOD.canonical_receipt(project_sources)).hexdigest(),"status":"PASS","theorem_count":1},
        "upstream_receipts":upstream,"cache_identity_sha256":cache_identity,
        "compiled_cone_identity_sha256":hashlib.sha256(MOD.canonical_receipt(compiled)).hexdigest(),
        "compiled_cone_size":2,"control_identities":control_rows,
        "image":MOD.H1_IMAGE,"review_id":review_id,
        "tool_identities":tool_identities}
    final_path = final_root / "receipt.json"; final_path.write_bytes(MOD.canonical_receipt(final))
    h1["final_receipt_path"] = str(final_path); h1["final_receipt_sha256"] = MOD.sha256(final_path)
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

def fake_git(args, repo):
    if args[0] in ("rev-parse", "hash-object"): return ["a"*40] * 5
    raise AssertionError(args)


class SevenBaseDropGeneratorTest(unittest.TestCase):
    def load(self, document, directory):
            path = Path(directory) / "inputs.json"
            path.write_text(json.dumps(document))
            return MOD.load_and_validate(path.resolve(), runner=fake_git)

    def test_axiom_auditor_producer_pin_matches_disk(self):
        producer = HERE / "audit_h1_endpoint_axioms.py"
        self.assertEqual(hashlib.sha256(producer.read_bytes()).hexdigest(),
                         MOD.AXIOM_PRODUCER_SHA256)

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
            output = Path(directory).resolve() / "Generated.lean"
            MOD.atomic_create(output, "first")
            with self.assertRaises(FileExistsError):
                MOD.atomic_create(output, "second")
            self.assertEqual(output.read_text(), "first")

    def test_h1_final_receipt_semantic_spoofs_and_deferred_sha(self):
        mutations = {
            "extra": lambda value: value.update(extra=True),
            "terminal": lambda value: value["terminal_capacity"]["terminal_counts"].update(pending=1, certified=13350),
            "terminal-payload": lambda value: value["terminal_capacity"].update(payload_identity_sha256="0"*64),
            "compiled-identity": lambda value: value.update(compiled_cone_identity_sha256="0"*64),
            "cache-identity": lambda value: value.update(cache_identity_sha256="0"*64),
            "audit-identity": lambda value: value["audit_identity"].update(project_cone_identity_sha256="0"*64),
            "producer": lambda value: value.update(producer_sha256="0"*64),
            "producer-commit": lambda value: value["producer_identity"].update(commit="c"*40),
            "projection": lambda value: value["consumer_projection_identity"].update(sha256="0"*64),
            "endpoint-module": lambda value: value["endpoint_identity"].update(module="Proofs.Generated.Wrong"),
            "endpoint-escape": lambda value: value["endpoint_identity"].update(source_path="../outside.lean"),
            "endpoint-olean": lambda value: value["endpoint_identity"].update(olean_sha256="0"*64),
            "audit": lambda value: value["audit_identity"].update(status="FAIL"),
            "image": lambda value: value.update(image="wrong"),
            "upstream": lambda value: value["upstream_receipts"]["cold"].update(schema="wrong"),
            "control": lambda value: value["control_identities"].pop(),
            "tool": lambda value: value["tool_identities"].update(python_sha256="0"),
        }
        for name, mutate in mutations.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                document = valid_document(directory); row = document["inputs"][0]; path = Path(row["final_receipt_path"])
                value = json.loads(path.read_text()); mutate(value); path.write_bytes(MOD.canonical_receipt(value))
                row["final_receipt_sha256"] = MOD.sha256(path)
                with self.assertRaises(ValueError): self.load(document, directory)
        with tempfile.TemporaryDirectory() as directory:
            document = valid_document(directory)
            with mock.patch.object(MOD, "FINALIZER_PRODUCER_SHA256", None), self.assertRaisesRegex(ValueError, "not banked"):
                self.load(document, directory)

    def test_h1_rejects_rehashed_nested_receipt_semantic_spoofs(self):
        cases = {
            "bank": ("evidence/post-chain/bank-receipt.json",
                     lambda value: value.update(payload_identity_sha256="0" * 64)),
            "cold": ("evidence/receipts/cold.json",
                     lambda value: value["retained_generated_artifacts"][0].update(sha256="0" * 64)),
            "cache": ("evidence/cache/cache-manifest.json",
                      lambda value: value.update(identity_sha256="0" * 64)),
            "axiom": ("evidence/receipts/axiom.json",
                      lambda value: value.update(theorem_count=2)),
            "axiom-extra-field": ("evidence/receipts/axiom.json",
                                  lambda value: value.update(extra="forged")),
            "cold-missing-field": ("evidence/receipts/cold.json",
                                   lambda value: value.pop("commands")),
            "axiom-foundational": ("evidence/receipts/axiom.json",
                                   lambda value: value.update(foundational_axioms=["Classical.choice"])),
            "axiom-tool": ("evidence/receipts/axiom.json",
                           lambda value: value["tool_identities"].update(python_sha256="0" * 64)),
            "snapshot-control": ("evidence/receipts/cache-snapshot.json",
                                 lambda value: value["control_files"].pop()),
            "cold-image": ("evidence/receipts/cold.json",
                           lambda value: value.update(image="forged")),
            "axiom-commit": ("evidence/receipts/axiom.json",
                            lambda value: value.update(source_commit="c" * 40)),
            "evidence-commit": ("evidence/post/leaf-evidence.json",
                                lambda value: value.update(reviewed_commit="c" * 40)),
            "cold-review": ("evidence/receipts/cold.json",
                            lambda value: value.update(review_id="456")),
        }
        for name, (relative, mutate) in cases.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                document = valid_document(directory); row = document["inputs"][0]
                final_path = Path(row["final_receipt_path"]); final = json.loads(final_path.read_text())
                nested_path = final_path.parent / relative; nested = json.loads(nested_path.read_text()); mutate(nested)
                nested_path.write_bytes(MOD.canonical_receipt(nested)); nested_sha = MOD.sha256(nested_path)
                artifact = next(item for item in final["artifacts"] if item["path"] == relative)
                artifact.update(bytes=nested_path.stat().st_size, sha256=nested_sha)
                for identity in final["upstream_receipts"].values():
                    if identity["path"] == relative: identity.update(bytes=nested_path.stat().st_size, sha256=nested_sha)
                final_path.write_bytes(MOD.canonical_receipt(final)); row["final_receipt_sha256"] = MOD.sha256(final_path)
                with self.assertRaises(ValueError): self.load(document, directory)

    def test_h1_final_tree_rejects_whitespace_extra_dirs_aliases_and_specials(self):
        for name in ("whitespace", "extra-dir", "hardlink", "external-hardlink", "final-external-hardlink", "fifo", "final-symlink"):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                document = valid_document(directory); row = document["inputs"][0]; final_path = Path(row["final_receipt_path"])
                value = json.loads(final_path.read_text()); root = final_path.parent
                if name == "whitespace":
                    final_path.write_bytes(final_path.read_bytes() + b"\n"); row["final_receipt_sha256"] = MOD.sha256(final_path)
                elif name == "extra-dir": (root / "unlisted-empty").mkdir()
                elif name in ("hardlink", "fifo"):
                    olean = root / value["endpoint_identity"]["olean_path"]
                    olean.unlink()
                    if name == "hardlink": os.link(Path(row["source_path"]), olean)
                    else: os.mkfifo(olean)
                    item = next(item for item in value["artifacts"] if item["path"] == value["endpoint_identity"]["olean_path"])
                    if name == "hardlink":
                        item.update(bytes=olean.stat().st_size, sha256=MOD.sha256(olean))
                        value["endpoint_identity"].update(olean_bytes=olean.stat().st_size, olean_sha256=MOD.sha256(olean))
                        final_path.write_bytes(MOD.canonical_receipt(value)); row["final_receipt_sha256"] = MOD.sha256(final_path)
                elif name == "external-hardlink":
                    source = root / value["endpoint_identity"]["source_path"]
                    os.link(source, Path(directory) / "outside-publication-alias")
                elif name == "final-external-hardlink":
                    os.link(final_path, Path(directory) / "outside-final-receipt-alias")
                else:
                    target = final_path.with_name("real-receipt.json"); final_path.rename(target); final_path.symlink_to(target)
                with self.assertRaises(ValueError): self.load(document, directory)

    def test_h1_rejects_mixed_final_projection_and_source_roots(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); first = valid_document(root / "first"); second = valid_document(root / "second")
            first_row, second_row = first["inputs"][0], second["inputs"][0]
            first_row["final_receipt_path"] = second_row["final_receipt_path"]
            first_row["final_receipt_sha256"] = second_row["final_receipt_sha256"]
            path = root / "first" / "inputs.json"; path.write_text(json.dumps(first))
            with self.assertRaises(ValueError): MOD.load_and_validate(path.resolve(), runner=fake_git)

    def test_toctou_rechecks_all_h1_layers_and_legacy_inputs(self):
        selectors = {
            "inputs": lambda doc, path: path,
            "final": lambda doc, path: Path(doc["inputs"][0]["final_receipt_path"]),
            "projection": lambda doc, path: Path(doc["inputs"][0]["aggregate_receipt_path"]),
            "source": lambda doc, path: Path(doc["inputs"][0]["source_path"]),
            "olean": lambda doc, path: Path(doc["inputs"][0]["final_receipt_path"]).parent / json.loads(Path(doc["inputs"][0]["final_receipt_path"]).read_text())["endpoint_identity"]["olean_path"],
            "cell-index": lambda doc, path: Path(doc["cell_aggregate_index_path"]),
            "cell-receipt": lambda doc, path: Path(doc["inputs"][1]["aggregate_receipt_path"]),
            "h7-receipt": lambda doc, path: Path(doc["inputs"][8]["aggregate_receipt_path"]),
        }
        for name, select in selectors.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve(); document = valid_document(root); path = root / "inputs.json"; path.write_text(json.dumps(document))
                target = select(document, path)
                def mutate(target=target): target.write_bytes(target.read_bytes() + b"x")
                with self.assertRaisesRegex(ValueError, "drift"):
                    MOD.load_and_validate(path, runner=fake_git, before_return=mutate)

    def test_publish_rechecks_before_output_and_rejects_output_race(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); document = valid_document(root); inputs = root / "inputs.json"; inputs.write_text(json.dumps(document))
            output = root / "Generated.lean"
            def mutate(): Path(document["inputs"][0]["source_path"]).write_bytes(b"changed")
            with self.assertRaisesRegex(ValueError, "drift"):
                MOD.publish(inputs, output, runner=fake_git, before_output=mutate)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); document = valid_document(root); inputs = root / "inputs.json"; inputs.write_text(json.dumps(document)); output = root / "Generated.lean"
            def race(): output.write_text("racer")
            with self.assertRaises(FileExistsError): MOD.publish(inputs, output, runner=fake_git, before_output=race)

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
