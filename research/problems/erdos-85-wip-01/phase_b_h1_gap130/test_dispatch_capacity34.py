import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import dispatch_capacity34 as target


class Capacity34DispatchTests(unittest.TestCase):
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
            (destination / "native").mkdir(parents=True)
            (destination / "native/input.cnf").write_bytes(b"p cnf 1 1\n1 0\n")
            return {"status": "materialized", "cnf_sha256": "0" * 64,
                    "cnf_bytes": 14}
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            with patch.object(target.adapter, "materialize", side_effect=fake_materialize), \
                 patch.object(target.dispatch, "check_sources"), \
                 patch.object(target.dispatch, "RESERVE", 0), \
                 patch.object(target.runner, "run_case", side_effect=AssertionError("solver called")):
                result = target.run_one(rows[0], {}, base, Path("kissat"), Path("cadical"), "a" * 40)
            self.assertEqual(result["status"], "ERROR")
            self.assertIn("CNF changed before solver dispatch", result["error"])
            self.assertEqual(json.loads((base / rows[0]["id"] / "result.json").read_text())["status"], "ERROR")

    def test_success_passes_exact_dual_policy_without_proof(self):
        _, rows = target.select()
        raw = b"p cnf 1 1\n1 0\n"
        def fake_materialize(_case_id, destination):
            (destination / "native").mkdir(parents=True)
            (destination / "native/input.cnf").write_bytes(raw)
            return {"status": "materialized", "cnf_sha256": target.runner.sha256(destination / "native/input.cnf"),
                    "cnf_bytes": len(raw)}
        seen = []
        def fake_run(case, _output, _kissat, _cadical):
            seen.append(case)
            return {"status": "UNSAT_CROSSCHECKED"}
        with tempfile.TemporaryDirectory() as temp:
            with patch.object(target.adapter, "materialize", side_effect=fake_materialize), \
                 patch.object(target.dispatch, "check_sources"), \
                 patch.object(target.dispatch, "RESERVE", 0), \
                 patch.object(target.runner, "run_case", side_effect=fake_run):
                result = target.run_one(rows[0], {}, Path(temp), Path("kissat"), Path("cadical"), "a" * 40)
        self.assertEqual(result["status"], "UNSAT_CROSSCHECKED")
        self.assertEqual(len(seen), 1)
        self.assertEqual({key: seen[0][key] for key in target.POLICY}, target.POLICY)
        self.assertEqual(seen[0]["sector"], "H1")
        self.assertEqual(seen[0]["cnf_sha256"], target.hashlib.sha256(raw).hexdigest())


if __name__ == "__main__":
    unittest.main()
