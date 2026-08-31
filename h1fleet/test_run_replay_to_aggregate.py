import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("pipeline", HERE / "run_replay_to_aggregate.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)
COMMIT = "a" * 40


def write(path: Path, raw: bytes) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return path.resolve()


class Fixture:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.repo = (self.root / "repo").resolve()
        (self.repo / "proofs/Proofs/Generated").mkdir(parents=True)
        (self.repo / "proofs/.lake/build/lib/lean/Proofs/Generated").mkdir(parents=True)
        self.producers = [write(self.repo / rel, f"# {rel}\n".encode()) for rel in
                          (MOD.MATERIALIZER_REL, MOD.AGGREGATOR_REL, MOD.ADAPTER_REL_PRODUCER)]
        self.manifest = write(self.root / "manifest.json", b"{}\n")
        self.queue = write(self.root / "queue.jsonl", b"{}\n")
        self.index = write(self.root / "capacity.tsv", b"header\n")
        self.inventory = write(self.root / "inventory.txt", b"inventory\n")
        self.reindex = write(self.root / "reindex.json", b"{}\n")
        self.store = (self.root / "store").resolve(); self.store.mkdir()
        self.leaf_index = (self.root / "leaf-index.json").resolve()
        self.evidence = (self.root / "materialization.json").resolve()
        self.transcript = (self.root / "transcript.json").resolve()
        self.fail_kind = None
        self.malformed_materialization = False
        self.wrong_crosslink = False
        self.tracked_drift = False
        self.calls = []

    def runner(self, kind, argv, cwd):
        self.calls.append((kind, argv, cwd))
        if kind == self.fail_kind:
            return {"rc": 7, "stdout": b"", "stderr": b"failed\n"}
        if kind in ("git_head_value", "git_head_final"):
            return {"rc": 0, "stdout": (COMMIT + "\n").encode(), "stderr": b""}
        if kind == "git_head":
            return {"rc": 0, "stdout": (COMMIT + "\n").encode(), "stderr": b""}
        if kind == "git_status":
            return {"rc": 0, "stdout": b"", "stderr": b""}
        if kind in ("git_tracked_diff", "git_staged_diff"):
            return {"rc": 1 if self.tracked_drift else 0, "stdout": b"", "stderr": b""}
        if kind == "materialize":
            leaf = self.repo / MOD.LEAF_REL; olean = self.repo / MOD.OLEAN_REL
            leaf.mkdir(); olean.mkdir()
            source = write(leaf / "Erdos85H1V2CertP0I00000.lean", b"theorem leaf : True := by trivial\n")
            compact = write(leaf / "Erdos85H1V2CertP0I00000.compact.lrat", b"0\n")
            olean_path = write(olean / "Erdos85H1V2CertP0I00000.olean", b"olean\n")
            capacity_sha = MOD.sha256_file(self.index)
            tag = "0123456789abcdef"
            module = {"local_index": 0, "orbit": tag, "packed_lrat_sha256": "1" * 64,
                "profile": 0, "source_bytes": source.stat().st_size,
                "source_module": MOD.LEAF_PREFIX + ".Erdos85H1V2CertP0I00000",
                "source_path": str(source), "source_sha256": MOD.sha256_file(source)}
            evidence = {key: None for key in MOD.MATERIALIZATION_FIELDS}
            evidence.update({"certificate_gzip_bytes": 1, "certificate_gzip_sha256": "2" * 64,
                "certificate_key": "campaign/cert.gz", "compact_lrat_bytes": compact.stat().st_size,
                "compact_lrat_path": str(compact), "compact_lrat_sha256": MOD.sha256_file(compact),
                "local_index": 0, "module": module["source_module"],
                "olean_artifact_key": f"campaign/oleans/{tag}.olean.zst",
                "olean_bytes": olean_path.stat().st_size, "olean_path": str(olean_path),
                "olean_sha256": MOD.sha256_file(olean_path), "orbit": tag, "profile": 0,
                "recompilable_from_tree": True,
                "replay_ready_key": f"campaign/replay-ready/{tag}.json",
                "replay_ready_sha256": "3" * 64, "receipt_key": f"campaign/receipts/{tag}.json",
                "receipt_sha256": "4" * 64, "source_artifact_key": f"campaign/sources/{tag}.lean.zst",
                "source_bytes": source.stat().st_size, "source_path": str(source),
                "source_sha256": MOD.sha256_file(source),
                "theorem": "Erdos85.h1V2P0I00000Checked"})
            write(self.leaf_index, MOD.canonical({"capacity_index_sha256": capacity_sha,
                "leaf_count": MOD.EXPECTED_LEAVES, "modules": [module],
                "schema": MOD.LEAF_INDEX_SCHEMA}))
            write(self.evidence, MOD.canonical({"capacity_index_sha256": capacity_sha,
                "leaf_count": MOD.EXPECTED_LEAVES, "module_prefix": MOD.LEAF_PREFIX,
                "manifest_sha256": MOD.sha256_file(self.manifest),
                "profile_counts": MOD.PROFILE_COUNTS,
                "queue_sha256": ("8" * 64 if self.wrong_crosslink else MOD.sha256_file(self.queue)),
                "recompilable_from_tree": True, "rows": [evidence],
                "schema": ("wrong" if self.malformed_materialization
                           else MOD.MATERIALIZATION_SCHEMA)}))
        elif kind == "aggregate":
            aggregate = self.repo / MOD.AGGREGATE_REL; aggregate.mkdir()
            write(aggregate / "Erdos85H1V2Complete.lean", b"theorem aggregate : True := by trivial\n")
            module = {key: None for key in MOD.LAYOUT_MODULE_FIELDS}
            source = aggregate / "Erdos85H1V2Complete.lean"
            module.update({"direct_import_count": 1, "direct_imports": [MOD.LEAF_PREFIX + ".Erdos85H1V2CertP0I00000"],
                "file": source.name, "kind": "top", "members": ["0123456789abcdef"],
                "module": MOD.AGGREGATE_PREFIX + ".Erdos85H1V2Complete",
                "source_bytes": source.stat().st_size, "source_sha256": MOD.sha256_file(source),
                "theorem": "Erdos85.h1V2AllCapacityCertified"})
            value = {"bank_size": 128, "inputs": {"index": MOD.file_id(self.index),
                "inventory": MOD.file_id(self.inventory)}, "inventory_contract": {},
                "leaf_count": MOD.EXPECTED_LEAVES, "leaf_members_sha256": "5" * 64,
                "modules": [module], "profile_bank_counts": [1],
                "prefixes": {"aggregate_modules": MOD.AGGREGATE_PREFIX,
                             "leaf_modules": MOD.LEAF_PREFIX}, "schema": MOD.LAYOUT_SCHEMA,
                "top_module": module["module"]}
            raw = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
            write(aggregate / "aggregate-layout.json", raw)
            write(aggregate / "aggregate-layout.sha256", (MOD.hashlib.sha256(raw).hexdigest() + "\n").encode())
        elif kind == "adapter":
            adapter = self.repo / MOD.ADAPTER_REL
            write(adapter, b"theorem endpoint : True := by trivial\n")
            aggregate = self.repo / MOD.AGGREGATE_REL / "aggregate-layout.json"
            receipt = {key: None for key in MOD.ADAPTER_FIELDS}
            receipt.update({"aggregate_layout_path": str(aggregate),
                "aggregate_layout_sha256": MOD.sha256_file(aggregate),
                "aggregate_source_root": str(aggregate.parent), "aggregate_sources_identity_sha256": "6" * 64,
                "capacity_index_path": str(self.index), "capacity_index_sha256": MOD.sha256_file(self.index),
                "capacity_reindex_receipt_path": str(self.reindex),
                "capacity_reindex_receipt_sha256": MOD.sha256_file(self.reindex),
                "generator_sha256": "7" * 64, "generator_source": str(MOD.ADAPTER_REL_PRODUCER),
                "input_top_module": MOD.AGGREGATE_PREFIX + ".Erdos85H1V2Complete",
                "input_top_path": str(aggregate.parent / "Erdos85H1V2Complete.lean"),
                "input_top_repo_path": str(MOD.AGGREGATE_REL / "Erdos85H1V2Complete.lean"),
                "input_top_sha256": MOD.sha256_file(aggregate.parent / "Erdos85H1V2Complete.lean"),
                "input_top_theorem": "Erdos85.h1V2AllCapacityCertified", "leaf_count": MOD.EXPECTED_LEAVES,
                "leaf_module_index_path": str(self.leaf_index),
                "leaf_module_index_sha256": MOD.sha256_file(self.leaf_index),
                "output_bytes": adapter.stat().st_size, "output_path": str(adapter),
                "output_sha256": MOD.sha256_file(adapter),
                "output_source_module": "Proofs.Generated.Erdos85OrderFortyNineOneHighCertificates",
                "output_theorem": "Erdos85.orderFortyNineStratumExcluded_one_of_generatedCertificates",
                "repo": str(self.repo), "schema": MOD.ADAPTER_SCHEMA})
            write(Path(str(adapter) + ".receipt.json"), MOD.canonical(receipt))
        return {"rc": 0, "stdout": f"{kind} ok\n".encode(), "stderr": b""}

    def args(self):
        return dict(repo=self.repo, source_commit=COMMIT, manifest=self.manifest,
                    queue=self.queue, capacity_index=self.index,
                    capacity_inventory=self.inventory, reindex_receipt=self.reindex,
                    leaf_index=self.leaf_index, materialization_evidence=self.evidence,
                    transcript=self.transcript, object_store_root=self.store,
                    s3_bucket=None, aws="aws", zstd="zstd", runner=self.runner)


class ReplayToAggregateTest(unittest.TestCase):
    def setUp(self):
        self.count = patch.object(MOD, "EXPECTED_LEAVES", 1)
        self.profiles = patch.object(MOD, "PROFILE_COUNTS", [1])
        self.count.start(); self.profiles.start()
        self.addCleanup(self.count.stop); self.addCleanup(self.profiles.stop)
    def test_exact_create_only_chain_and_review_stop(self):
        with tempfile.TemporaryDirectory() as raw:
            fixture = Fixture(Path(raw)); value = MOD.build(**fixture.args())
            self.assertEqual([row["kind"] for row in value["commands"]],
                             ["git_head", "materialize", "aggregate", "adapter"])
            self.assertEqual(value["next_required_action"],
                             "human-review-and-commit-generated-lean-sources-only")
            self.assertEqual(value["outputs"]["leaf_source_tree"]["file_count"], 2)
            self.assertEqual(value["outputs"]["olean_tree"]["file_count"], 1)
            self.assertEqual(value["producer_identities"][0]["sha256"],
                             MOD.sha256_file(Path(MOD.__file__).resolve()))
            transcript = json.loads(fixture.transcript.read_text())
            rendered = json.dumps(transcript)
            for forbidden in ("finalize_h1_leaf", "cold_build", "run-instances", "git commit"):
                self.assertNotIn(forbidden, rendered)
            materialize = next(argv for kind, argv, _ in fixture.calls if kind == "materialize")
            self.assertIn(MOD.LEAF_PREFIX, materialize)
            aggregate = next(argv for kind, argv, _ in fixture.calls if kind == "aggregate")
            self.assertIn(MOD.AGGREGATE_PREFIX, aggregate)

    def test_freshness_failure_and_child_failure_do_not_publish_transcript(self):
        with tempfile.TemporaryDirectory() as raw:
            fixture = Fixture(Path(raw)); (fixture.repo / MOD.AGGREGATE_REL).mkdir()
            with self.assertRaisesRegex(MOD.PipelineError, "aggregate directory.*absent"):
                MOD.build(**fixture.args())
            self.assertFalse(fixture.transcript.exists())
        with tempfile.TemporaryDirectory() as raw:
            fixture = Fixture(Path(raw)); fixture.fail_kind = "aggregate"
            with self.assertRaisesRegex(MOD.PipelineError, "aggregate command failed"):
                MOD.build(**fixture.args())
            self.assertFalse(fixture.transcript.exists())

    def test_tracked_drift_fails_after_outputs(self):
        with tempfile.TemporaryDirectory() as raw:
            fixture = Fixture(Path(raw)); fixture.tracked_drift = True
            with self.assertRaisesRegex(MOD.PipelineError, "tracked repository state drifted"):
                MOD.build(**fixture.args())
            self.assertFalse(fixture.transcript.exists())

    def test_zero_exit_with_malformed_child_contract_fails(self):
        with tempfile.TemporaryDirectory() as raw:
            fixture = Fixture(Path(raw)); fixture.malformed_materialization = True
            with self.assertRaisesRegex(MOD.PipelineError, "materialized leaf/index contract"):
                MOD.build(**fixture.args())
            self.assertFalse(fixture.transcript.exists())

        with tempfile.TemporaryDirectory() as raw:
            fixture = Fixture(Path(raw)); fixture.wrong_crosslink = True
            with self.assertRaisesRegex(MOD.PipelineError, "materialized leaf/index contract"):
                MOD.build(**fixture.args())
            self.assertFalse(fixture.transcript.exists())

    def test_output_drift_and_partial_transcript_publication_fail_cleanly(self):
        with tempfile.TemporaryDirectory() as raw:
            fixture = Fixture(Path(raw)); args = fixture.args()
            args["before_transcript"] = lambda: (fixture.repo / MOD.ADAPTER_REL).write_bytes(b"drift\n")
            with self.assertRaisesRegex(MOD.PipelineError, "output drift before transcript"):
                MOD.build(**args)
            self.assertFalse(fixture.transcript.exists())
        with tempfile.TemporaryDirectory() as raw:
            fixture = Fixture(Path(raw)); args = fixture.args()
            args["after_publish"] = lambda: (fixture.repo / MOD.ADAPTER_REL).write_bytes(b"late drift\n")
            with self.assertRaisesRegex(MOD.PipelineError, "output drift after transcript publication"):
                MOD.build(**args)
            self.assertFalse(fixture.transcript.exists())
        with tempfile.TemporaryDirectory() as raw:
            fixture = Fixture(Path(raw)); args = fixture.args()
            def partial(path, raw_value):
                path.write_bytes(raw_value[:17])
                raise OSError("simulated publication failure")
            args["transcript_writer"] = partial
            with self.assertRaisesRegex(OSError, "simulated publication failure"):
                MOD.build(**args)
            self.assertFalse(fixture.transcript.exists())

    def test_concurrent_final_publication_is_never_deleted(self):
        with tempfile.TemporaryDirectory() as raw:
            fixture = Fixture(Path(raw)); args = fixture.args(); sentinel = b"other publisher\n"
            args["before_link"] = lambda: fixture.transcript.write_bytes(sentinel)
            with self.assertRaises(FileExistsError):
                MOD.build(**args)
            self.assertEqual(fixture.transcript.read_bytes(), sentinel)


if __name__ == "__main__":
    unittest.main()
