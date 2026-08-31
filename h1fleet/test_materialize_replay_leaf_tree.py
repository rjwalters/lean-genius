import gzip
import hashlib
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from replay_common import ObjectInfo, ReplayError, atomic_write, sha256_bytes

import materialize_replay_leaf_tree as target


class FakeStore:
    def __init__(self, values):
        self.values = values

    def download(self, key, destination):
        if key not in self.values:
            raise ReplayError(f"missing object: {key}")
        atomic_write(destination, self.values[key])
        digest = sha256_bytes(self.values[key])
        return ObjectInfo(key, len(self.values[key]), digest, digest, "test", {},
                          {"replay": "consumed"} if key.endswith(".gz") else {},
                          None, None)


def zstd(value: bytes, root: Path, name: str) -> bytes:
    raw, packed = root / name, root / f"{name}.zst"
    raw.write_bytes(value)
    result = subprocess.run(
        ["zstd", "-q", "-f", str(raw), "-o", str(packed)],
        capture_output=True, check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.decode())
    return packed.read_bytes()


class MaterializeReplayLeafTreeTests(unittest.TestCase):
    def test_require_raw_rejects_receipt_size_mismatch(self):
        with tempfile.TemporaryDirectory() as raw:
            compact = Path(raw) / "leaf.compact.lrat"
            compact.write_bytes(b"1 0 0\n")
            with self.assertRaisesRegex(ReplayError, "raw identity mismatch"):
                target.require_raw(compact, {
                    "size": compact.stat().st_size + 1,
                    "sha256": target.sha256_file(compact),
                }, "compact LRAT")

    def test_complete_capacity_contract_rejects_missing_extra_duplicate_and_wrong_slot(self):
        capacity = {}
        jobs = []
        rows = []
        ordinal = 0
        for profile, count in enumerate(target.CAPACITY_PROFILE_COUNTS):
            for local_index in range(count):
                tag = f"{ordinal:016x}"
                capacity[tag] = (profile, local_index)
                jobs.append({"tag": tag, "profile": profile, "local_index": local_index})
                rows.append({"tag": tag, "profile": profile, "local_index": local_index})
                ordinal += 1
        selected, _, counts = target.select_exact_rows(rows, jobs, capacity, True)
        self.assertEqual(len(selected), 13351)
        self.assertEqual(tuple(counts), target.CAPACITY_PROFILE_COUNTS)
        mutations = (
            (rows[:-1], jobs, capacity),
            (rows, jobs[:-1], capacity),
            (rows, jobs + [jobs[0]], capacity),
            (rows, jobs + [{**jobs[0], "tag": "ffffffffffffffff"}], capacity),
            (rows, jobs[:-1] + [{**jobs[-1], "local_index": jobs[-1]["local_index"] - 1}], capacity),
        )
        for changed_rows, changed_jobs, changed_capacity in mutations:
            with self.subTest(lengths=(len(changed_rows), len(changed_jobs))), self.assertRaises(ReplayError):
                target.select_exact_rows(changed_rows, changed_jobs, changed_capacity, True)

    def test_source_contract_requires_exact_unique_proof_name_and_slot(self):
        with tempfile.TemporaryDirectory() as raw:
            compact = Path(raw) / "Erdos85H1V2CertP2I00017.compact.lrat"
            compact.write_bytes(b"1 0 0\n")
            rendered = target.render_replay_leaf(
                tag="0123456789abcdef", profile=2, local_index=17,
                compact_lrat=compact,
            ) + "\n#print axioms Erdos85.h1V2P2I00017Checked\n"
            target.require_source_contract(
                rendered.encode(), "0123456789abcdef", 2, 17, compact,
            )
            with self.assertRaisesRegex(ReplayError, "source/module identity"):
                target.require_source_contract(
                    ("-- spoof\n" + rendered).encode(),
                    "0123456789abcdef", 2, 17, compact,
                )
            with self.assertRaisesRegex(ReplayError, "cannot regenerate canonical source"):
                target.require_source_contract(
                    rendered.encode(), "0123456789abcdef", 2, 18, compact,
                )

    def test_materializes_authenticated_source_olean_compact_and_legacy_index(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            manifest_path, queue_path = root / "manifest.json", root / "queue.jsonl"
            capacity_path, reindex_path = root / "capacity.tsv", root / "reindex.json"
            for path, value in ((manifest_path, b"manifest\n"), (queue_path, b"queue\n"),
                                (capacity_path, b"capacity\n"), (reindex_path, b"reindex\n")):
                path.write_bytes(value)
            tag, profile, local_index = "0123456789abcdef", 2, 17
            module = "Erdos85H1V2CertP2I00017"
            proof_name = f"{module}.compact.lrat"
            olean, compact = b"olean-bytes\n", b"1 0 0\n"
            compact_path = root / proof_name
            compact_path.write_bytes(compact)
            source = (target.render_replay_leaf(
                tag=tag, profile=profile, local_index=local_index,
                compact_lrat=compact_path,
            ) + "\n#print axioms Erdos85.h1V2P2I00017Checked\n").encode()
            compact_path.unlink()
            certificate = gzip.compress(compact)
            source_key, olean_key = "prefix/sources/tag.lean.zst", "prefix/oleans/tag.olean.zst"
            receipt_key = f"prefix/receipts/{tag}.json"
            certificate_key = f"sat49/campaign-20260825/h1/{tag}.compact.lrat.gz"
            table = "table"
            job = {"tag": tag, "profile": profile, "local_index": local_index,
                   "certificate_key": certificate_key,
                   "certificate_gzip_sha256": sha256_bytes(certificate),
                   "compact_lrat_sha256": sha256_bytes(compact), "cnf_sha256": "c" * 64,
                   "table_serialization": table, "table_sha256": sha256_bytes(table.encode())}
            manifest = {"campaign_prefix": "prefix/", "inventory_sha256": "i" * 64,
                        "coverage_sha256": "v" * 64, "queue_sha256": sha256_bytes(queue_path.read_bytes()),
                        "capacity_index_sha256": sha256_bytes(capacity_path.read_bytes()),
                        "capacity_reindex_receipt_sha256": sha256_bytes(reindex_path.read_bytes())}
            def identity(key, value, tags=None):
                digest = sha256_bytes(value)
                return {"key": key, "size": len(value), "sha256": digest,
                        "etag": digest, "last_modified": "test", "version_id": None,
                        "metadata": {}, "tags": tags or {}}
            source_packed, olean_packed = zstd(source, root, "source"), zstd(olean, root, "olean")
            receipt = {"tag": tag, "job_sha256": sha256_bytes(target.canonical_json(job)),
                "job_identity": {
                "profile": profile, "local_index": local_index, "table_serialization": table,
                "table_sha256": job["table_sha256"], "cnf_sha256": job["cnf_sha256"],
                "inventory_sha256": manifest["inventory_sha256"],
                "coverage_sha256": manifest["coverage_sha256"]},
                "module": {"name": module, "theorem": "Erdos85.h1V2P2I00017Checked"},
                "artifacts": {"source": identity(source_key, source_packed),
                              "olean": identity(olean_key, olean_packed)},
                "source_raw": {"size": len(source), "sha256": sha256_bytes(source)},
                "olean_raw": {"size": len(olean), "sha256": sha256_bytes(olean)},
                "compact_lrat": {"size": len(compact), "sha256": sha256_bytes(compact)},
                "replay_ready": {"key": f"prefix/replay-ready/{tag}.json"},
                "replay_ready_sha256": "r" * 64,
                "certificate_after_tagging": identity(
                    certificate_key, certificate, {"replay": "consumed"})}
            store = FakeStore({receipt_key: target.canonical_json(receipt),
                               source_key: source_packed,
                               olean_key: olean_packed,
                               certificate_key: certificate})
            suffix = Path("Proofs/Generated/H1V2Leaves")
            source_dir, olean_dir = root / "sources" / suffix, root / "oleans" / suffix
            leaf_index, evidence = root / "leaf-index.json", root / "evidence.json"
            validator_calls = []
            with mock.patch.object(target, "load_manifest", return_value=manifest), \
                 mock.patch.object(target, "validate_reindex_receipt"), \
                 mock.patch.object(target, "load_capacity_index", return_value={tag: (profile, local_index)}), \
                 mock.patch.object(target, "read_capacity_rows", return_value=[{
                     "tag": tag, "profile": profile, "local_index": local_index,
                     "packed_sha256": "p" * 64}]), \
                 mock.patch.object(target, "read_queue", return_value=[job]):
                target.materialize(
                    manifest_path=manifest_path, queue_path=queue_path,
                    capacity_index=capacity_path, reindex_receipt=reindex_path,
                    source_dir=source_dir, olean_dir=olean_dir,
                    leaf_index_path=leaf_index, evidence_path=evidence,
                    module_prefix="Proofs.Generated.H1V2Leaves", store=store, zstd="zstd",
                    validate_one=lambda args: validator_calls.append(args.receipt),
                    validator_backend={"object_store_root": root, "s3_bucket": None, "aws": "aws"},
                    require_complete=False,
                )
            self.assertEqual(len(validator_calls), 1)
            self.assertEqual((source_dir / f"{module}.lean").read_bytes(), source)
            self.assertEqual((source_dir / proof_name).read_bytes(), compact)
            self.assertEqual((olean_dir / f"{module}.olean").read_bytes(), olean)
            index = target.load_json(leaf_index)
            self.assertEqual(index["schema"], target.LEAF_INDEX_SCHEMA)
            self.assertEqual(index["modules"][0]["source_module"],
                             f"Proofs.Generated.H1V2Leaves.{module}")
            evidence_value = target.load_json(evidence)
            self.assertIs(evidence_value["recompilable_from_tree"], True)
            proof = evidence_value["rows"][0]
            self.assertEqual(proof["compact_lrat_sha256"], job["compact_lrat_sha256"])
            self.assertEqual(proof["compact_lrat_bytes"], len(compact))
            self.assertEqual(proof["olean_sha256"], sha256_bytes(olean))


if __name__ == "__main__":
    unittest.main()
