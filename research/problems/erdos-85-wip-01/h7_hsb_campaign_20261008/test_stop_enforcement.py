"""Offline regressions. Run with PYTHONPATH pointing at the campaign under review."""
import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import cert_controller as cc

# AWS CLI delete-fleets, Example 1 (not a hand-designed response schema):
# https://docs.aws.amazon.com/cli/latest/reference/ec2/delete-fleets.html
SUCCESS_FIXTURE = Path(__file__).with_name("fixtures") / "delete_fleets_success.json"
FLEET_ID = "fleet-12a34b55-67cd-8ef9-ba9b-9208dEXAMPLE"


def successful_deletion():
    return json.loads(SUCCESS_FIXTURE.read_text())


class StopEnforcement(unittest.TestCase):
    def setUp(self):
        self.stack = contextlib.ExitStack()
        self.addCleanup(self.stack.close)
        self.calls = []
        self.response = successful_deletion()
        self.stack.enter_context(patch.object(cc.vc, "aws", self.aws))
        self.stack.enter_context(patch.object(cc.vc, "instances", return_value=[{"id": "i-mine", "state": "running"}]))
        tmp = self.stack.enter_context(tempfile.TemporaryDirectory())
        self.stack.enter_context(patch.object(cc.vc, "STRIPE", Path(tmp)))
        self.stack.enter_context(contextlib.redirect_stdout(io.StringIO()))

    def aws(self, *args, **kwargs):
        self.calls.append(args)
        if args[:2] == ("ec2", "describe-fleets"):
            return json.dumps({"Fleets": [
                {"FleetId": FLEET_ID, "Tags": [{"Key": "project", "Value": cc.vc.TAG}]},
                {"FleetId": "fleet-other", "Tags": [{"Key": "project", "Value": "another-pass"}]},
            ]})
        if args[:2] == ("ec2", "delete-fleets"):
            return json.dumps(self.response)
        return "{}"

    def fail_delete(self):
        self.response = {"SuccessfulFleetDeletions": [], "UnsuccessfulFleetDeletions": [
            {"FleetId": FLEET_ID, "Error": {"Code": "unexpectedError", "Message": "injected deletion failure"}}
        ]}

    def test_success_deletes_only_selected_pass(self):
        result = cc.terminate_pass_fleet()
        self.assertEqual(result, {"deleted_fleets": [FLEET_ID], "terminated": ["i-mine"]})
        deletion = next(c for c in self.calls if c[:2] == ("ec2", "delete-fleets"))
        self.assertNotIn("fleet-other", deletion)
        self.assertFalse(any(c[:2] == ("s3", "cp") for c in self.calls))

    def test_partial_failure_does_not_report_deleted(self):
        self.fail_delete()
        with self.assertRaisesRegex(RuntimeError, "unexpectedError"):
            cc.terminate_pass_fleet()

    def test_failure_array_is_checked_even_with_success_acknowledgement(self):
        self.response["UnsuccessfulFleetDeletions"] = [
            {"FleetId": FLEET_ID, "Error": {"Code": "fleetNotInDeletableState", "Message": "conflicting reply"}}
        ]
        with self.assertRaisesRegex(RuntimeError, "fleetNotInDeletableState"):
            cc.terminate_pass_fleet()

    def test_old_invented_response_keys_are_not_success(self):
        self.response = {"Successful": [{"FleetId": FLEET_ID}], "Unsuccessful": []}
        with self.assertRaises(RuntimeError):
            cc.terminate_pass_fleet()

    def test_missing_success_acknowledgement_is_retried(self):
        self.response = {"SuccessfulFleetDeletions": [], "UnsuccessfulFleetDeletions": []}
        with self.assertRaises(RuntimeError):
            cc.terminate_pass_fleet()

    def test_operator_and_inherited_budget_stop_use_checked_deletion(self):
        self.fail_delete()
        with self.assertRaises(RuntimeError):
            cc.vc.stop(None)

    def test_real_budget_branch_cannot_exit_after_delete_failure(self):
        self.fail_delete()
        with patch.object(cc.vc, "listing", return_value=[]), patch.object(cc.vc, "instances", return_value=[]), \
                patch.object(cc.vc, "HARD_STOP_USD", 0), patch.object(cc, "ledgers", return_value=[]), \
                patch.object(cc, "MANIFEST", [{"id": "x"}]):
            with self.assertRaises(RuntimeError):
                cc.one_pass({"instances": {}, "claims": {}}, True)

    def test_foreign_stop_cannot_exit_after_delete_failure(self):
        self.fail_delete()
        with patch.object(cc, "_reviewed_one_pass", return_value={"utc": "t", "control": ["STOP", "ALARM-x"]}), \
                patch.object(cc, "ledgers", return_value=[]), patch.object(cc, "MANIFEST", [{"id": "x"}]), \
                patch.object(cc, "put_json") as put:
            with self.assertRaises(RuntimeError):
                cc.one_pass({}, True)
            put.assert_not_called()

    def test_completion_cannot_exit_after_delete_failure(self):
        self.fail_delete()
        with patch.object(cc, "_reviewed_one_pass", return_value={"utc": "t", "control": []}), \
                patch.object(cc, "ledgers", return_value=[{"id": "x", "status": "CERTIFIED"}]), \
                patch.object(cc, "MANIFEST", [{"id": "x"}]), patch.object(cc, "put_json") as put:
            with self.assertRaises(RuntimeError):
                cc.one_pass({}, True)
            put.assert_not_called()

    def test_watch_retries_failed_deletion_before_returning(self):
        self.fail_delete()

        def next_attempt(_seconds):
            self.response = successful_deletion()

        with patch.object(cc, "_reviewed_one_pass", side_effect=lambda *a: {"utc": "t", "control": ["STOP"]}), \
                patch.object(cc, "ledgers", return_value=[]), patch.object(cc, "MANIFEST", [{"id": "x"}]), \
                patch.object(cc.vc.time, "sleep", side_effect=next_attempt) as sleep:
            cc.vc.watch(SimpleNamespace(dry=False, once=False))
            sleep.assert_called_once_with(300)
            self.assertEqual(sum(c[:2] == ("ec2", "delete-fleets") for c in self.calls), 2)

    def test_successful_stop_writes_marker_before_deletion(self):
        cc.vc.stop(None)
        upload = next(i for i, c in enumerate(self.calls) if c[:2] == ("s3", "cp"))
        deletion = next(i for i, c in enumerate(self.calls) if c[:2] == ("ec2", "delete-fleets"))
        self.assertLess(upload, deletion)


if __name__ == "__main__":
    unittest.main(verbosity=2)
