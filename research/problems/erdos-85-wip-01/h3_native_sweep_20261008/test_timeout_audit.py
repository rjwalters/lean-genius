"""Regression for a normal child exit racing the full timeout; no computation credit."""
import unittest
from audit_cloud import validate_full_timeout

class TimeoutAuditChecks(unittest.TestCase):
    def setUp(self):
        self.step={'stop_reason':'TIMEOUT','timeout_seconds':90,
                   'effective_timeout_seconds':90,'elapsed_seconds':90.139596547,
                   'returncode':0}
    def test_exit_zero_after_timer_remains_unresolved(self):
        validate_full_timeout(self.step)
    def test_killed_child_is_full_timeout(self):
        self.step['returncode']=-9;validate_full_timeout(self.step)
    def test_success_without_timeout_rejected(self):
        self.step['stop_reason']=None
        with self.assertRaises(AssertionError):validate_full_timeout(self.step)
    def test_deadline_shortened_timeout_rejected(self):
        self.step['effective_timeout_seconds']=12
        with self.assertRaises(AssertionError):validate_full_timeout(self.step)
    def test_early_stop_rejected(self):
        self.step['elapsed_seconds']=89.9
        with self.assertRaises(AssertionError):validate_full_timeout(self.step)
    def test_different_cap_rejected(self):
        self.step['timeout_seconds']=1800
        with self.assertRaises(AssertionError):validate_full_timeout(self.step)
    def test_missing_child_result_rejected(self):
        self.step['returncode']=None
        with self.assertRaises(AssertionError):validate_full_timeout(self.step)
    def test_stop_file_is_not_timeout(self):
        self.step['stop_reason']='STOP'
        with self.assertRaises(AssertionError):validate_full_timeout(self.step)

if __name__=='__main__':unittest.main()
