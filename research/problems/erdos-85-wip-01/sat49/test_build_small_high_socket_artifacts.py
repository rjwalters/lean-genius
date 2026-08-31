import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "socket_builder", HERE / "build_small_high_socket_artifacts.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


def fixture(root: Path):
    cells = {}
    for _, cell, _ in MOD.AGGREGATES.CELLS:
        jobs = [{"id": f"{cell}.cover-left", "kind": "cover-left"},
                {"id": f"{cell}.cover-right", "kind": "cover-right"}]
        jobs.extend({"id": f"{cell}.cube-{li}-{ri}", "kind": "cube",
                     "left_index": li, "right_index": ri}
                    for li in range(7) for ri in range(8))
        cells[cell] = {"jobs": jobs}
    manifest = root / "manifest.json"
    manifest.write_bytes(MOD.canonical({"schema": "erdos85-small-high-cube-jobs-v1",
                                        "cells": cells}))
    pins = {"root_manifest_sha256": MOD.sha256(manifest),
            "queue_receipt_sha256": "1" * 64, "queue_sha256": "2" * 64,
            "worker_receipt_sha256": "3" * 64, "worker_sha256": "4" * 64}
    MOD.APPROVED_PINS = pins.copy()  # Synthetic fixture only; production constants stay in source.
    commit = "a" * 40
    final = root / "final"; final.mkdir()
    evidence = final / "leaf-receipts"; evidence.mkdir()
    replay_dir = final / "replay-receipts"; replay_dir.mkdir()
    index_rows = []
    for job in MOD.exact_jobs(json.loads(manifest.read_text())):
        theorem = MOD.theorem_for(job)
        cnf, lrat = "5" * 64, "6" * 64
        rich = {"materializer_receipt_sha256":"7"*64,"module_receipt_sha256":"8"*64,
                "replay_audit_sha256":"9"*64,
                "replay_evidence_sha256":MOD.hashlib.sha256(job.encode()).hexdigest()}
        replay = replay_dir / f"{job}.json"
        replay.write_bytes(MOD.canonical({"cnf_sha256": cnf, "commit": commit,
            "compact_lrat_sha256": lrat, "job_id": job,"image":"lean4-arm64@sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6",
            "lratreplay_sha256":"37aad1d5c64a75fcb68e1ea587b2080b06c157a19c883b01d145b28b891c428c",
            "materializer_receipt_sha256":rich["materializer_receipt_sha256"],
            "replay_audit_sha256":rich["replay_audit_sha256"],"replay_evidence_sha256":rich["replay_evidence_sha256"],
            "replay_verdict": "VERIFIED", "schema": MOD.REPLAY_SCHEMA,
            "source_module": MOD.SOURCE_MODULE, "theorem": theorem}))
        leaf = {"schema": MOD.LEAF_SCHEMA, "job_id": job,
            **pins, "hypothesis": theorem, "theorem": theorem,
            "source_module": MOD.SOURCE_MODULE, "commit": commit,
            "cnf_sha256": cnf, "compact_lrat_sha256": lrat,
            "replay_receipt_path": str(replay),
            "replay_receipt_sha256": MOD.sha256(replay), "review_id": "1215",**rich}
        leaf_path = evidence / f"{job}.receipt.json"
        leaf_path.write_bytes(MOD.canonical(leaf))
        index_rows.append({"job_id": job, "leaf_receipt_sha256": MOD.sha256(leaf_path),
                           "replay_receipt_sha256": MOD.sha256(replay)})
    index = final / "index.json"
    index.write_bytes(MOD.canonical({"jobs": index_rows, "schema": MOD.FINALIZER_SCHEMA}))
    finalizer_receipt = final / "receipt.json"
    finalizer_receipt.write_bytes(MOD.canonical({"bank_receipt_sha256": "7"*64,
        "finalizer_sha256": "c"*64, "index_sha256": MOD.sha256(index), "jobs": 406,
        "leaf_receipts": str(evidence), "module_commit": commit,
        "module_receipt_sha256": "8"*64, "module_sha256": "d"*64,
        "replay_receipts": str(replay_dir), "review_id": "1215",
        "schema": MOD.FINALIZER_SCHEMA}))
    return manifest, pins, evidence, finalizer_receipt, MOD.sha256(finalizer_receipt), commit


class SocketArtifactsTest(unittest.TestCase):
    def test_exact_406_build_validates_and_publishes_receipt_last(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest, pins, evidence, finalizer, finalizer_sha, commit = fixture(root)
            artifacts = MOD.build(manifest, pins, evidence, finalizer, finalizer_sha, commit)
            output = root / "output"
            MOD.publish(output, artifacts)
            self.assertEqual(MOD.SOCKETS.validate(
                output / "sockets.tsv", output / "expected-sockets.json"), 406)
            self.assertEqual(set(path.name for path in output.iterdir()), {
                "sockets.tsv", "expected-sockets.json",
                "socket-validation.receipt", "receipt.json"})
            receipt = json.loads((output / "receipt.json").read_text())
            self.assertEqual(receipt["socket_count"], 406)
            self.assertEqual(receipt["root_manifest_sha256"], pins["root_manifest_sha256"])
            with self.assertRaises(FileExistsError): MOD.publish(output, artifacts)

    def test_missing_or_mutated_leaf_fails_before_output_creation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest, pins, evidence, finalizer, finalizer_sha, commit = fixture(root)
            victim = next(evidence.iterdir()); victim.unlink()
            output = root / "output"
            with self.assertRaises(ValueError): MOD.build(manifest, pins, evidence, finalizer, finalizer_sha, commit)
            self.assertFalse(output.exists())
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest, pins, evidence, finalizer, finalizer_sha, commit = fixture(root)
            victim = next(evidence.iterdir()); victim.write_bytes(victim.read_bytes() + b"\n")
            with self.assertRaises(ValueError): MOD.build(manifest, pins, evidence, finalizer, finalizer_sha, commit)

    def test_replay_symlink_and_lineage_drift_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest, pins, evidence, finalizer, finalizer_sha, commit = fixture(root)
            victim = next(evidence.iterdir()); leaf = json.loads(victim.read_text())
            target = Path(leaf["replay_receipt_path"])
            link = root / "replay-link.json"; link.symlink_to(target)
            leaf["replay_receipt_path"] = str(link)
            victim.write_bytes(MOD.canonical(leaf))
            with self.assertRaises(ValueError): MOD.build(manifest, pins, evidence, finalizer, finalizer_sha, commit)

    def test_check_or_divergent_lean_identity_is_rejected(self):
        for field, suffix in (("theorem", "_check"), ("hypothesis", "_other")):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                manifest, pins, evidence, finalizer, finalizer_sha, commit = fixture(root)
                victim = next(evidence.iterdir()); leaf = json.loads(victim.read_text())
                leaf[field] = leaf[field].removesuffix("_unsat") + suffix
                victim.write_bytes(MOD.canonical(leaf))
                with self.assertRaises(ValueError): MOD.build(manifest, pins, evidence, finalizer, finalizer_sha, commit)

    def test_reviewed_production_pin_drift_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest, pins, evidence, finalizer, finalizer_sha, commit = fixture(root)
            MOD.APPROVED_PINS = {**pins, "queue_sha256": "8" * 64}
            with self.assertRaisesRegex(ValueError, "reviewed production constants"):
                MOD.build(manifest, pins, evidence, finalizer, finalizer_sha, commit)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest, pins, evidence, finalizer, finalizer_sha, commit = fixture(root)
            victim = next(evidence.iterdir()); leaf = json.loads(victim.read_text())
            leaf["queue_sha256"] = "9" * 64
            victim.write_bytes(MOD.canonical(leaf))
            with self.assertRaises(ValueError): MOD.build(manifest, pins, evidence, finalizer, finalizer_sha, commit)

    def test_finalizer_receipt_and_index_binding_are_revalidated(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest, pins, evidence, finalizer, finalizer_sha, commit = fixture(root)
            index = finalizer.parent / "index.json"
            index.write_bytes(index.read_bytes() + b"\n")
            with self.assertRaises(ValueError):
                MOD.build(manifest, pins, evidence, finalizer, finalizer_sha, commit)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest, pins, evidence, finalizer, finalizer_sha, commit = fixture(root)
            value = json.loads(finalizer.read_text())
            value["leaf_receipts"] = str(root / "elsewhere")
            finalizer.write_bytes(MOD.canonical(value))
            with self.assertRaises(ValueError):
                MOD.build(manifest, pins, evidence, finalizer, MOD.sha256(finalizer), commit)

    def test_divergent_replay_audit_pin_is_rejected_even_when_reindexed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest, pins, evidence, finalizer, finalizer_sha, commit = fixture(root)
            leaf_path = next(evidence.iterdir()); leaf = json.loads(leaf_path.read_text())
            replay_path = Path(leaf["replay_receipt_path"]); replay = json.loads(replay_path.read_text())
            leaf["replay_audit_sha256"] = "e" * 64
            replay["replay_audit_sha256"] = "e" * 64
            replay_path.write_bytes(MOD.canonical(replay))
            leaf["replay_receipt_sha256"] = MOD.sha256(replay_path)
            leaf_path.write_bytes(MOD.canonical(leaf))
            index_path = finalizer.parent / "index.json"; index = json.loads(index_path.read_text())
            row = next(item for item in index["jobs"] if item["job_id"] == leaf["job_id"])
            row["leaf_receipt_sha256"] = MOD.sha256(leaf_path)
            row["replay_receipt_sha256"] = MOD.sha256(replay_path)
            index_path.write_bytes(MOD.canonical(index))
            receipt = json.loads(finalizer.read_text()); receipt["index_sha256"] = MOD.sha256(index_path)
            finalizer.write_bytes(MOD.canonical(receipt))
            with self.assertRaisesRegex(ValueError,"finalizer provenance"):
                MOD.build(manifest, pins, evidence, finalizer, MOD.sha256(finalizer), commit)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest, pins, evidence, finalizer, finalizer_sha, commit = fixture(root)
            index = finalizer.parent / "index.json"; value = json.loads(index.read_text())
            value["jobs"][0]["leaf_receipt_sha256"] = "0" * 64
            index.write_bytes(MOD.canonical(value))
            receipt = json.loads(finalizer.read_text()); receipt["index_sha256"] = MOD.sha256(index)
            finalizer.write_bytes(MOD.canonical(receipt))
            with self.assertRaises(ValueError):
                MOD.build(manifest, pins, evidence, finalizer, MOD.sha256(finalizer), commit)


if __name__ == "__main__":
    unittest.main()
