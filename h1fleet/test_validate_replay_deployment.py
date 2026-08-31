import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "deployment", HERE / "validate_replay_deployment.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class ValidateReplayDeploymentTest(unittest.TestCase):
    bucket = MOD.BUCKET
    input_prefix = MOD.INPUT_PREFIX
    output_prefix = MOD.OUTPUT_PREFIX
    freight_prefix = MOD.FREIGHT_PREFIX

    def iam(self):
        bucket_arn = "arn:aws:s3:::" + self.bucket
        inp = bucket_arn + "/" + self.input_prefix + "__replay_audit_input__"
        out = bucket_arn + "/" + self.output_prefix + "__replay_audit_output__"
        freight = bucket_arn + "/" + self.freight_prefix + "__replay_audit_freight__"
        allowed = [
            ("s3:ListBucket", bucket_arn),
            ("s3:GetObject", inp), ("s3:GetObjectTagging", inp),
            ("s3:PutObjectTagging", inp),
            ("s3:GetObject", out), ("s3:PutObject", out),
            ("s3:GetObject", freight), ("s3:PutObject", freight),
        ]
        denied = [("s3:PutObject", inp)] + [
            (action, resource)
            for resource in (inp, out, freight)
            for action in ("s3:DeleteObject", "s3:DeleteObjectVersion")
        ]
        return {"EvaluationResults": [
            {"EvalActionName": action, "EvalResourceName": resource,
             "EvalDecision": "allowed"}
            for action, resource in allowed
        ] + [
            {"EvalActionName": action, "EvalResourceName": resource,
             "EvalDecision": "implicitDeny"}
            for action, resource in denied
        ]}

    def lifecycle(self):
        return {"Rules": [{
            "ID": MOD.LIFECYCLE_RULE_ID,
            "Status": "Enabled",
            "Filter": {"And": {"Prefix": self.input_prefix,
                                "Tags": [{"Key": "replay", "Value": "consumed"}]}},
            "Transitions": [{"Days": 7, "StorageClass": "GLACIER_IR"}],
        }]}

    def validate_iam(self, document):
        return MOD.validate_iam(document, self.bucket, self.input_prefix,
                                self.output_prefix, self.freight_prefix)

    def test_accepts_exact_evidence(self):
        self.assertIn("launch_gate_discharged=false", MOD.APPROVAL_NOTICE)
        self.assertIn("pending_editor_approval", MOD.APPROVAL_NOTICE)
        self.assertEqual(self.validate_iam(self.iam()), 15)
        self.assertEqual(MOD.validate_lifecycle(
            self.lifecycle(), self.input_prefix,
            MOD.LIFECYCLE_RULE_ID), 1)

    def test_rejects_unrelated_or_malformed_deployment_identity(self):
        cases = (
            ("other", self.input_prefix, self.output_prefix, self.freight_prefix),
            (self.bucket, "", self.output_prefix, self.freight_prefix),
            (self.bucket, self.input_prefix.rstrip("/"), self.output_prefix,
             self.freight_prefix),
            (self.bucket, self.input_prefix, self.input_prefix, self.freight_prefix),
            (self.bucket, self.input_prefix, self.input_prefix + "nested/",
             self.freight_prefix),
        )
        for bucket, inp, out, freight in cases:
            with self.subTest(bucket=bucket, inp=inp, out=out):
                with self.assertRaises(MOD.DeploymentEvidenceError):
                    MOD.validate_identity(bucket, inp, out, freight,
                                          MOD.LIFECYCLE_RULE_ID)

    def test_rejects_missing_allow_and_allowed_dangerous_action(self):
        for mutate in ("missing", "dangerous"):
            with self.subTest(mutate=mutate):
                evidence = self.iam()
                if mutate == "missing":
                    evidence["EvaluationResults"] = evidence["EvaluationResults"][1:]
                else:
                    next(item for item in evidence["EvaluationResults"]
                         if item["EvalActionName"] == "s3:PutObject" and
                         "/h1/" in item["EvalResourceName"])["EvalDecision"] = "allowed"
                with self.assertRaises(MOD.DeploymentEvidenceError):
                    self.validate_iam(evidence)

    def test_rejects_duplicate_iam_result(self):
        evidence = self.iam()
        evidence["EvaluationResults"].append(dict(evidence["EvaluationResults"][0]))
        with self.assertRaisesRegex(MOD.DeploymentEvidenceError, "duplicate"):
            self.validate_iam(evidence)

    def test_rejects_wrong_filter_transition_and_extra_action(self):
        for mutate in ("tag", "days", "expiration"):
            with self.subTest(mutate=mutate):
                evidence = self.lifecycle()
                rule = evidence["Rules"][0]
                if mutate == "tag":
                    rule["Filter"]["And"]["Tags"][0]["Value"] = "ready"
                elif mutate == "days":
                    rule["Transitions"][0]["Days"] = 1
                else:
                    rule["Expiration"] = {"Days": 30}
                with self.assertRaises(MOD.DeploymentEvidenceError):
                    MOD.validate_lifecycle(evidence, self.input_prefix,
                                           MOD.LIFECYCLE_RULE_ID)

    def test_rejects_overlapping_unconditional_rule(self):
        evidence = self.lifecycle()
        evidence["Rules"].append({
            "ID": "bad", "Status": "Enabled",
            "Filter": {"Prefix": "sat49/campaign-20260825/"},
            "Expiration": {"Days": 2},
        })
        with self.assertRaisesRegex(MOD.DeploymentEvidenceError, "unconsumed"):
            MOD.validate_lifecycle(evidence, self.input_prefix,
                                   MOD.LIFECYCLE_RULE_ID)

    def test_evidence_hashes_bind_bytes_and_normalized_identity(self):
        identity = MOD.validate_identity(
            self.bucket, self.input_prefix, self.output_prefix,
            self.freight_prefix, MOD.LIFECYCLE_RULE_ID)
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            iam = root / "iam.json"
            lifecycle = root / "lifecycle.json"
            iam.write_text(json.dumps(self.iam()))
            lifecycle.write_text(json.dumps(self.lifecycle()))
            hashes = MOD.evidence_hashes(iam, lifecycle, identity)
            self.assertEqual(len(hashes), 3)
            self.assertTrue(all(len(value) == 64 for value in hashes))
            iam.write_text(iam.read_text() + "\n")
            changed = MOD.evidence_hashes(iam, lifecycle, identity)
            self.assertNotEqual(hashes[0], changed[0])
            self.assertEqual(hashes[1:], changed[1:])


if __name__ == "__main__":
    unittest.main()
