import unittest
from unittest.mock import patch

import audit_h1_gap_verdicts as target


class H1GapVerdictAuditTests(unittest.TestCase):
    def test_dated_exact_join_is_1158_plus_96_plus_34(self):
        plan, _ = target.outside.select()
        gaps, residual, historical, outside = target.dated_gap_ids(
            plan, target.adapter.freeze()["rows"])
        self.assertEqual((len(gaps), len(residual), len(historical), len(outside)),
                         (1288, 1158, 96, 34))
        self.assertEqual(gaps, residual | historical | outside)

    def test_historical_evidence_does_not_count_as_fresh_dual_verdict(self):
        plan, _ = target.outside.select()
        _, residual, historical, outside = target.dated_gap_ids(
            plan, target.adapter.freeze()["rows"])
        phase_rows = [{"id": case["id"], "status":
                       "HISTORICAL_VERIFIED_UNSAT" if case["id"] in historical
                       else "UNSAT_CROSSCHECKED" if case["id"] in residual
                       else "NOT_RUN"} for case in plan["cases"]]
        base = {"rows": phase_rows, "runs": []}
        extra = {case_id: "UNSAT_CROSSCHECKED" for case_id in outside}
        with patch.object(target.summary, "summarize", return_value=base), \
             patch.object(target, "summarize_outside", return_value=(extra, [])):
            report = target.audit([], [])
        self.assertEqual(report["crosschecked_unsat"], 1192)
        self.assertEqual(report["open"], 96)
        self.assertFalse(report["computational_gap_census_complete"])


if __name__ == "__main__":
    unittest.main()
