"""Exercise native-role opt-in and ownership through local replay transactions."""

import copy
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import test_replay_transaction as fixtures
from replay_common import (
    FOUNDATIONAL_AXIOMS, GENERATED_LEAF_AXIOM_PATTERN, NATIVE_AXIOM_PATTERN,
    ReplayError, canonical_json, info_record, load_manifest, sha256_file,
)
from replay_worker import validate_ready


class NativeLeafContractTests(unittest.TestCase):
    stem = "Erdos85.h1V2P0I00003"

    def fixture(self, pattern, axioms):
        case = fixtures.ReplayTransactionTest()
        case.setUp()
        self.addCleanup(case.tearDown)
        manifest = json.loads(case.manifest.read_text())
        if pattern is not None:
            manifest["allowed_axiom_patterns"] = [pattern]
        case.manifest.write_bytes(canonical_json(manifest))
        case.helper.write_text(case.helper.read_text().replace(
            '["propext", "Classical.choice", "Quot.sound"]',
            repr(list(FOUNDATIONAL_AXIOMS) + axioms)))
        return case

    def native(self, role, stem=None):
        return (stem or self.stem) + role + "._native.native_decide.ax_1_1"

    def test_opt_in_accepts_three_roles_resume_and_independent_validation(self):
        case = self.fixture(GENERATED_LEAF_AXIOM_PATTERN,
                            [self.native(role) for role in ("Table", "Nonzero", "Check")])
        result = case.worker()
        self.assertEqual(result.returncode, 0, result.stderr)
        result = case.validate_receipt()
        self.assertEqual(result.returncode, 0, result.stderr)
        result = case.worker()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("ALREADY_ACCEPTED", result.stdout)
        ready = json.loads((case.store.objects /
            f"sat49/campaign-20260825/h1-replay/replay-ready/{case.tag}.json").read_text())
        self.assertEqual(ready["native_axiom_prefix"], self.stem)

    def test_legacy_contract_still_accepts_check_only(self):
        case = self.fixture(NATIVE_AXIOM_PATTERN, [self.native("Check")])
        result = case.worker()
        self.assertEqual(result.returncode, 0, result.stderr)
        result = case.validate_receipt()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_no_implicit_opt_in_or_unreviewed_roles(self):
        cases = [(None, self.native("Check")),
                 (NATIVE_AXIOM_PATTERN, self.native("Table")),
                 (NATIVE_AXIOM_PATTERN, self.native("Nonzero")),
                 (GENERATED_LEAF_AXIOM_PATTERN, self.native("Entry")),
                 (GENERATED_LEAF_AXIOM_PATTERN, self.native("Check", "Erdos85.h1V2P1I00003")),
                 (GENERATED_LEAF_AXIOM_PATTERN, self.native("Table", "Erdos85.h1V2P0I00004")),
                 (GENERATED_LEAF_AXIOM_PATTERN, self.native("Nonzero").replace("ax_1_1", "ax__"))]
        for pattern, axiom in cases:
            with self.subTest(pattern=pattern, axiom=axiom):
                case = self.fixture(pattern, [axiom])
                result = case.worker()
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertFalse(case.receipt_path().exists())
                self.assertNotIn("replay", case.store.head(case.certificate_key).tags)

    def test_manifest_rejects_mixed_or_widened_patterns(self):
        case = self.fixture(GENERATED_LEAF_AXIOM_PATTERN, [])
        manifest = load_manifest(case.manifest)
        for patterns in ([NATIVE_AXIOM_PATTERN, GENERATED_LEAF_AXIOM_PATTERN],
                         [GENERATED_LEAF_AXIOM_PATTERN] * 2,
                         [GENERATED_LEAF_AXIOM_PATTERN.replace("Table|Nonzero|Check", ".*")]):
            with self.subTest(patterns=patterns):
                case.manifest.write_bytes(canonical_json(dict(
                    manifest, allowed_axiom_patterns=patterns)))
                with self.assertRaisesRegex(ReplayError, "allowed_axiom_patterns"):
                    load_manifest(case.manifest)

    def test_resume_revalidates_ready_axioms(self):
        case = self.fixture(GENERATED_LEAF_AXIOM_PATTERN, [self.native("Check")])
        self.assertEqual(case.worker().returncode, 0)
        manifest = load_manifest(case.manifest)
        manifest["manifest_sha256"] = sha256_file(case.manifest)
        job = json.loads(case.job.read_text())
        job["job_sha256"] = sha256_file(case.job)
        ready = json.loads((case.store.objects /
            f"sat49/campaign-20260825/h1-replay/replay-ready/{case.tag}.json").read_text())
        for axiom in (self.native("Table", "Erdos85.h1V2P0I00004"), "evil.axiom"):
            forged = copy.deepcopy(ready)
            forged["axiom_audit"]["axioms"].append(axiom)
            with self.subTest(axiom=axiom), self.assertRaises(ReplayError):
                validate_ready(forged, manifest, job, case.store)

    def test_independent_validator_rejects_changed_receipt_audit(self):
        case = self.fixture(GENERATED_LEAF_AXIOM_PATTERN, [self.native("Check")])
        self.assertEqual(case.worker().returncode, 0)
        receipt = json.loads(case.receipt_path().read_text())
        # Even another permitted same-leaf role must agree with hashed ready evidence.
        receipt["axiom_audit"]["axioms"].append(self.native("Table"))
        case.rewrite_receipt_and_rebind_ledger(receipt)
        result = case.validate_receipt()
        self.assertEqual(result.returncode, 2)
        self.assertIn("axiom_audit differs", result.stderr)

    def test_independent_validator_rejects_shortened_ready_prefix(self):
        for pattern in (NATIVE_AXIOM_PATTERN, GENERATED_LEAF_AXIOM_PATTERN):
            with self.subTest(pattern=pattern):
                case = self.fixture(pattern, [self.native("Check")])
                self.assertEqual(case.worker().returncode, 0)
                key = f"sat49/campaign-20260825/h1-replay/replay-ready/{case.tag}.json"
                ready = json.loads((case.store.objects / key).read_text())
                ready["native_axiom_prefix"] = "Erdos85.h1V2P"
                case.rewrite_store_json(key, ready)
                receipt = json.loads(case.receipt_path().read_text())
                receipt["replay_ready"] = info_record(case.store.head(key))
                receipt["replay_ready_sha256"] = receipt["replay_ready"]["sha256"]
                case.rewrite_receipt_and_rebind_ledger(receipt)
                result = case.validate_receipt()
                self.assertEqual(result.returncode, 2, result.stdout)
                self.assertIn("ownership prefix mismatch", result.stderr)


if __name__ == "__main__":
    unittest.main()
