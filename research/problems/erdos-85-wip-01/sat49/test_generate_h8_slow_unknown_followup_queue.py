#!/usr/bin/env python3

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "h8queue", HERE / "generate_h8_slow_unknown_followup_queue.py")
assert SPEC and SPEC.loader
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


class FollowupQueueTests(unittest.TestCase):
    def test_exact_extension_and_marker_binding(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            queue, worker, spec = root / "queue", root / "worker", root / "spec"
            queue.write_text("queue")
            worker.write_text("worker")
            spec.write_text(json.dumps({"schema": "test", "nodes": {}}))
            common = {
                "schema": MOD.MANIFEST_SCHEMA, "parent_manifest_sha256": "p",
                "base_sha256": "b", "variables": 17, "base_clauses": 20,
                "parent_id": "cube_F6_t14", "parent_units": [1],
            }
            old = {**common, "internal_node_count": 1, "leaf_count": 2,
                   "leaves": [
                       {"id": "cube_F6_t14.adaptive.leaf-000", "path": "000", "units": [1, -2]},
                       {"id": "keep", "path": "111", "units": [1, 3]}]}
            new = {**common, "tree_spec_sha256": MOD.sha256(spec),
                   "internal_node_count": 2, "leaf_count": 3,
                   "leaves": [old["leaves"][1],
                       {"id": "cube_F6_t14.adaptive.leaf-0000", "path": "0000", "units": [1, -2, -7]},
                       {"id": "cube_F6_t14.adaptive.leaf-0001", "path": "0001", "units": [1, -2, 7]}]}
            old_path, new_path = root / "old", root / "new"
            old_path.write_text(json.dumps(old)); new_path.write_text(json.dumps(new))
            marker = root / "unknown.line"
            marker.write_text(
                "2026-01-01T00:00:00Z cube_F6_t14.adaptive.leaf-000 SLOW-UNKNOWN "
                f"schema={MOD.UNKNOWN_SCHEMA} rc=0 cap_s=60 "
                f"queue_sha256={MOD.sha256(queue)} cadical_sha256={'a'*64} "
                f"worker_sha256={MOD.sha256(worker)}\n")
            result = MOD.build_queue(
                job="cube_F6_t14.adaptive.leaf-000", marker=marker,
                old_manifest=old_path, new_manifest=new_path, new_spec=spec,
                source_queue=queue, source_worker=worker,
                cadical_sha="a" * 64, cap=60)
            self.assertEqual(result["split_variable"], 7)
            self.assertEqual([x["path"] for x in result["jobs"]], ["0000", "0001"])

    def test_rejects_wrong_marker_cap(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            marker = Path(raw) / "marker"
            marker.write_text(
                "t cube_F6_t14.adaptive.leaf-000 SLOW-UNKNOWN "
                f"schema={MOD.UNKNOWN_SCHEMA} rc=0 cap_s=59 queue_sha256=q "
                "cadical_sha256=c worker_sha256=w\n")
            with self.assertRaisesRegex(ValueError, "authentication mismatch"):
                MOD.parse_marker(marker, "cube_F6_t14.adaptive.leaf-000", 60, "q", "w", "c")


if __name__ == "__main__":
    unittest.main()
