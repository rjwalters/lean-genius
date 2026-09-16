import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import dispatch_capacity34 as target


class Capacity34DispatchTests(unittest.TestCase):
    @staticmethod
    def fake_binding(row, destination, *, claimed_hash=None):
        raw = b"p cnf 1 1\n1 0\n"
        (destination / "native").mkdir(parents=True)
        (destination / "native/input.cnf").write_bytes(raw)
        return {
            "status": "materialized", "id": row["id"], "tag": row["tag"],
            "profile": row["profile"],
            "capacity_local_index": row["capacity_local_index"],
            "gap130_sha256": target.adapter.MANIFEST_SHA256,
            "one_row_source_sha256": target.adapter.sha(target.adapter.one_row_manifest(row)),
            "native_materializer_sha256": target.adapter.NATIVE_SHA256,
            "adapter_source_sha256": target.runner.sha256(Path(target.adapter.__file__)),
            "freeze_source_sha256": target.runner.sha256(target.HERE / "freeze.py"),
            "native_receipt_sha256": "a" * 64, "solver_launched": False,
            "cnf_sha256": claimed_hash or target.hashlib.sha256(raw).hexdigest(),
            "cnf_bytes": len(raw),
        }

    def test_exact_34_separate_from_phase_b_and_dual_policy(self):
        plan, rows = target.select()
        self.assertEqual(len(rows), 34)
        self.assertEqual(target.id_digest(r["id"] for r in rows), target.SELECTED_IDS_SHA256)
        self.assertFalse({r["id"] for r in rows} & {c["id"] for c in plan["cases"]})
        self.assertEqual(plan["config"]["policies"]["H1"], target.POLICY)

    def test_dry_run_does_not_materialize_or_solve(self):
        with patch.object(target.adapter, "materialize", side_effect=AssertionError("materialized")):
            with patch.object(target.runner, "run_case", side_effect=AssertionError("solver")):
                with patch.object(target.sys, "argv", ["wrapper"]), contextlib.redirect_stdout(io.StringIO()) as output:
                    self.assertEqual(target.main(), 0)
        report = json.loads(output.getvalue())
        self.assertEqual(report["selected_cases"], 34)
        self.assertFalse(report["proof_logging"])
        self.assertFalse(report["solver_launched"])

    def test_hash_mismatch_stops_before_solver(self):
        _, rows = target.select()
        def fake_materialize(_case_id, destination):
            return self.fake_binding(rows[0], destination, claimed_hash="0" * 64)
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            with patch.object(target.adapter, "materialize", side_effect=fake_materialize), \
                 patch.object(target.dispatch, "check_sources"), \
                 patch.object(target.dispatch, "RESERVE", 0), \
                 patch.object(target.runner, "run_case", side_effect=AssertionError("solver called")):
                result = target.run_one(rows[0], {}, base, Path("kissat"), Path("cadical"))
            self.assertEqual(result["status"], "ERROR")
            self.assertIn("binding or CNF changed", result["error"])
            self.assertEqual(json.loads((base / rows[0]["id"] / "result.json").read_text())["status"], "ERROR")

    def test_success_passes_exact_dual_policy_without_proof(self):
        _, rows = target.select()
        raw = b"p cnf 1 1\n1 0\n"
        def fake_materialize(_case_id, destination):
            return self.fake_binding(rows[0], destination)
        seen = []
        def fake_run(case, _output, _kissat, _cadical):
            seen.append(case)
            return {"status": "UNSAT_CROSSCHECKED"}
        with tempfile.TemporaryDirectory() as temp:
            with patch.object(target.adapter, "materialize", side_effect=fake_materialize), \
                 patch.object(target.dispatch, "check_sources"), \
                 patch.object(target.dispatch, "RESERVE", 0), \
                 patch.object(target.runner, "run_case", side_effect=fake_run):
                result = target.run_one(rows[0], {"config": {"h1_generator_commit": "b" * 40}},
                                        Path(temp), Path("kissat"), Path("cadical"))
        self.assertEqual(result["status"], "UNSAT_CROSSCHECKED")
        self.assertEqual(len(seen), 1)
        self.assertEqual({key: seen[0][key] for key in target.POLICY}, target.POLICY)
        self.assertEqual(seen[0]["sector"], "H1")
        self.assertEqual(seen[0]["cnf_sha256"], target.hashlib.sha256(raw).hexdigest())
        self.assertEqual(seen[0]["generator_commit"], "b" * 40)

    def test_primary_only_unsat_is_rejected(self):
        _, rows = target.select()
        with tempfile.TemporaryDirectory() as temp:
            with patch.object(target.adapter, "materialize",
                              side_effect=lambda _id, path: self.fake_binding(rows[0], path)), \
                 patch.object(target.dispatch, "check_sources"), \
                 patch.object(target.dispatch, "RESERVE", 0), \
                 patch.object(target.runner, "run_case", return_value={"status": "UNSAT_PRIMARY"}):
                result = target.run_one(rows[0], {"config": {"h1_generator_commit": "b" * 40}},
                                        Path(temp), Path("kissat"), Path("cadical"))
        self.assertEqual(result["status"], "ERROR")
        self.assertIn("Primary-only UNSAT", result["error"])

    def test_wrong_binding_identity_stops_before_solver(self):
        _, rows = target.select()
        def wrong(_id, path):
            binding = self.fake_binding(rows[0], path)
            binding["id"] = "h1_wrong"
            return binding
        with tempfile.TemporaryDirectory() as temp:
            with patch.object(target.adapter, "materialize", side_effect=wrong), \
                 patch.object(target.dispatch, "check_sources"), \
                 patch.object(target.dispatch, "RESERVE", 0), \
                 patch.object(target.runner, "run_case", side_effect=AssertionError("solver called")):
                result = target.run_one(rows[0], {}, Path(temp), Path("kissat"), Path("cadical"))
        self.assertEqual(result["status"], "ERROR")
        self.assertIn("binding or CNF changed", result["error"])


if __name__ == "__main__":
    unittest.main()
