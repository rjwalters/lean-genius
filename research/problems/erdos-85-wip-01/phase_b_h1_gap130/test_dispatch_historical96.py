import contextlib
import io
import json
import sys
import unittest
from unittest.mock import patch

import dispatch_historical96 as target


class Historical96DispatchTests(unittest.TestCase):
    def test_exact_gap_scope_and_dual_solver_policy(self):
        plan, selected = target.select()
        self.assertEqual(len(selected), 96)
        self.assertEqual({case["id"] for case in selected},
                         {row["id"] for row in plan["historical"]})
        self.assertEqual(target.id_digest(case["id"] for case in selected),
                         target.HISTORICAL_IDS_SHA256)
        self.assertTrue(all(case["sector"] == "H1" and case["policy"] ==
            {"crosscheck": True, "primary_cap_seconds": 14400,
             "crosscheck_cap_seconds": 14400} for case in selected))

    def test_full_dry_run_and_residual_rejection(self):
        output = io.StringIO()
        with patch.object(sys, "argv", ["wrapper", "--workers", "4"]), contextlib.redirect_stdout(output):
            self.assertEqual(target.main(), 0)
        summary = json.loads(output.getvalue())
        self.assertEqual((summary["selected_cases"], summary["historical_evidence_cases"]), (96, 96))
        self.assertEqual(summary["historical_skipped"], [])
        _, fresh = target.residual.select(target.CONFIG)
        with patch.object(sys, "argv", ["wrapper", "--case-id", fresh[0]["id"]]):
            with self.assertRaises(SystemExit):
                target.main()

    def test_execute_requires_banked_commits(self):
        with patch.object(sys, "argv", ["wrapper", "--execute"]):
            with self.assertRaises(SystemExit):
                target.main()

    def test_reviewed_overlay_hash_guards_preparation_before_solver(self):
        plan, selected = target.select()
        case = selected[0]
        expected = next(row["cnf_sha256"] for row in plan["historical"]
                        if row["id"] == case["id"])
        source = {row["id"]: row["cnf_sha256"] for row in plan["historical"]}
        prepared = target.prepare_with_overlay_hash(
            case, plan, None, lambda *_: {"cnf_sha256": expected}, source)
        self.assertTrue(prepared["historical_overlay_verified"])
        self.assertEqual(prepared["historical_overlay_expected_cnf_sha256"], expected)
        with self.assertRaisesRegex(ValueError, "differs from reviewed historical overlay"):
            target.prepare_with_overlay_hash(case, plan, None,
                lambda *_: {"cnf_sha256": "0" * 64}, source)
        with self.assertRaisesRegex(ValueError, "lacks a reviewed"):
            target.prepare_with_overlay_hash(case, plan, None,
                lambda *_: {"cnf_sha256": expected}, {})
        changed = dict(plan)
        changed["historical"] = [{**row, "cnf_sha256": "0" * 64}
                                 if row["id"] == case["id"] else row
                                 for row in plan["historical"]]
        with self.assertRaisesRegex(ValueError, "overlay or two-solver policy drifted"):
            target.prepare_with_overlay_hash(case, changed, None,
                lambda *_: {"cnf_sha256": expected}, source)


if __name__ == "__main__":
    unittest.main()
