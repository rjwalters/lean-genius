#!/usr/bin/env python3

import gzip
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import execute_h1_conflict_readback as mod


def job(tag="0000000000000001"):
    return {"certificate_key": mod.queue_format.certificate_key(tag), "family": "BBBB",
            "local_index": 0, "profile": 0, "tag": tag}


class FakeStore:
    def __init__(self, payload: bytes | None, *, mismatch=False, error=None):
        self.payload, self.mismatch, self.error = payload, mismatch, error

    def download(self, key, destination):
        if self.error:
            raise self.error
        if self.payload is None:
            raise mod.ObjectMissing(key)
        destination.write_bytes(self.payload)
        digest = mod.sha256_bytes(self.payload)
        return mod.Download(key if not self.mismatch else "wrong/key", len(self.payload),
                            digest, '"etag"', "time", "version")


class FakeValidator:
    def __init__(self, *, accepted=True, rc=0, malformed=False):
        self.accepted, self.rc, self.malformed = accepted, rc, malformed

    def validate(self, _job, _inventory, _compact, _work):
        if self.malformed:
            return {}
        return {"cnf_bytes": 10, "cnf_clauses": 1, "cnf_sha256": "a" * 64,
                "replay_accepted": self.accepted, "replay_rc": self.rc,
                "replay_stderr_sha256": "b" * 64, "replay_stdout_sha256": "c" * 64,
                "table_sha256": "d" * 64, "v2cnf_check": "MATCH (1 clauses, top 1)"}


def compressed(value=b"1 0 0\n"):
    import io
    output = io.BytesIO()
    with gzip.GzipFile(fileobj=output, mode="wb", mtime=0) as stream:
        stream.write(value)
    return output.getvalue()


class ExecuteConflictReadbackTest(unittest.TestCase):
    def run_execute(self, store, validator):
        with tempfile.TemporaryDirectory() as directory:
            return mod.execute(jobs=[job()], inventory={job()["tag"]: {
                "profile": 0, "local_index": 0, "values": (0,) * 24}},
                store=store, validator=validator, work=Path(directory))

    def test_valid_invalid_and_missing_are_exact_terminal_classes(self):
        valid = self.run_execute(FakeStore(compressed()), FakeValidator())[0]
        self.assertEqual(valid["classification"], "canonical-valid")
        self.assertEqual(valid["compact_lrat_sha256"], mod.sha256_bytes(b"1 0 0\n"))
        rejected = self.run_execute(FakeStore(compressed()), FakeValidator(accepted=False))[0]
        self.assertEqual((rejected["classification"], rejected["failure_stage"]),
                         ("canonical-invalid", "semantic-replay"))
        rejected_rc_one = self.run_execute(
            FakeStore(compressed()), FakeValidator(accepted=False, rc=1))[0]
        self.assertEqual((rejected_rc_one["classification"],
                          rejected_rc_one["failure_stage"]),
                         ("canonical-invalid", "semantic-replay"))
        missing = self.run_execute(FakeStore(None), FakeValidator())[0]
        self.assertEqual(missing, {"classification": "canonical-missing", "job": job(),
            "job_sha256": mod.sha256_bytes(mod.canonical(job())),
            "reason": "confirmed-not-found"})

    def test_stable_deterministic_gzip_and_syntax_failures_are_invalid(self):
        for payload in (b"not gzip", compressed(b""), compressed(b"text\n"),
                        compressed(b"1 2\n"), compressed(b"1 2 0\n")):
            result = self.run_execute(FakeStore(payload), FakeValidator())[0]
            self.assertEqual(result["classification"], "canonical-invalid")
            self.assertEqual(result["failure_stage"], "gzip-or-compact-syntax")

    def test_compact_syntax_accepts_deletions_and_rejects_malformed_lines(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            valid = root / "valid.lrat"
            valid.write_text(
                "610405 -184 -201 -501 0 1 4568 0\n"
                "610405 d 4568 0\n"
                "610406 0 610405 0\n"
            )
            mod.validate_compact_syntax(valid)
            for index, contents in enumerate((
                "1 d\n2 0 1 0\n",
                "1 d not-an-id 0\n2 0 1 0\n",
                "1 d 7\n2 0 1 0\n",
                "1 x 7 0\n2 0 1 0\n",
            )):
                malformed = root / f"malformed-{index}.lrat"
                malformed.write_text(contents)
                with self.subTest(contents=contents), self.assertRaises(ValueError):
                    mod.validate_compact_syntax(malformed)

    def test_indeterminate_store_runtime_and_identity_fail_without_result(self):
        for store, validator in (
            (FakeStore(compressed(), mismatch=True), FakeValidator()),
            (FakeStore(compressed(), error=mod.AuditError("network")), FakeValidator()),
            (FakeStore(compressed()), FakeValidator(accepted=None, rc=1)),
            (FakeStore(compressed()), FakeValidator(rc=137)),
            (FakeStore(compressed()), FakeValidator(malformed=True)),
        ):
            with self.subTest(store=store, validator=validator), self.assertRaises(mod.AuditError):
                self.run_execute(store, validator)

    def test_compact_replay_false_positive_requires_boolean_and_rc_zero(self):
        with self.assertRaises(mod.AuditError):
            self.run_execute(FakeStore(compressed()), FakeValidator(accepted="true"))

    def test_parse_queue_receipt_audit_and_capacity_crosslinks(self):
        values = (0,) * len(mod.capacity.TABLE_PAIRS)
        tag = mod.capacity.worker_tag(values)
        item = job(tag)
        queue_data = mod.canonical(item)
        audit_value = {"aws": {"bucket": "bucket", "profile": "profile",
                                "s3_prefix": "sat49/campaign-20260825"},
                       "schema": mod.queue_format.AUDIT_SCHEMA}
        audit_data = mod.canonical(audit_value)
        inventory_data = ("0 " + " ".join("0" for _ in values) + "\n").encode()
        receipt = {"audit_receipt_sha256": mod.sha256_bytes(audit_data),
            "capacity_inventory_sha256": mod.sha256_bytes(inventory_data),
            "certificate_prefix": mod.queue_format.CERTIFICATE_PREFIX,
            "conflict_tags": [tag], "coverage_sha256": "e" * 64,
            "output_sha256": mod.sha256_bytes(queue_data), "profile_counts": [1, 0, 0, 0, 0],
            "rows": 1, "schema": mod.queue_format.QUEUE_SCHEMA,
            "selection_status": "certificate-key-conflict"}
        snap = lambda data: mod.Snapshot(data, (1, 2, len(data), 3), mod.sha256_bytes(data))
        with mock.patch.object(mod, "EXPECTED_COUNTS", (1, 0, 0, 0, 0)), \
                mock.patch.object(mod, "EXPECTED_TOTAL", 1):
            jobs, inventory, aws = mod.parse_inputs(
                snap(queue_data), snap(mod.canonical(receipt)), snap(audit_data), snap(inventory_data))
        self.assertEqual(jobs, [item]); self.assertIn(tag, inventory)
        self.assertEqual(aws["bucket"], "bucket")
        for changed in (
            mod.canonical({**receipt, "output_sha256": "0" * 64}),
            mod.canonical({**receipt, "rows": 2}),
        ):
            with mock.patch.object(mod, "EXPECTED_COUNTS", (1, 0, 0, 0, 0)), \
                    mock.patch.object(mod, "EXPECTED_TOTAL", 1), \
                    self.assertRaises(mod.AuditError):
                mod.parse_inputs(snap(queue_data), snap(changed), snap(audit_data), snap(inventory_data))

    def test_snapshot_revalidation_and_create_only_publication(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); source = root / "input"; source.write_bytes(b"input")
            value = mod.snapshot(source, mod.sha256_bytes(b"input"), "input")
            original = source.stat()
            source.write_bytes(b"other")
            os.utime(source, ns=(original.st_atime_ns, original.st_mtime_ns))
            with self.assertRaisesRegex(mod.AuditError, "changed before publication"):
                mod.revalidate(source, value, "input")
            output = root / "receipt.json"; mod.create_only(output, b"first\n")
            with self.assertRaises(FileExistsError):
                mod.create_only(output, b"second\n")

    def test_hostile_temp_symlink_and_final_link_race_cannot_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); victim = root / "victim"; victim.write_bytes(b"safe")
            (root / ".receipt.tmp.hostile").symlink_to(victim)
            output = root / "receipt"
            mod.create_only(output, b"result")
            self.assertEqual(victim.read_bytes(), b"safe")
            raced = root / "raced"
            real_link = mod.os.link
            def race_link(source, destination):
                Path(destination).write_bytes(b"winner")
                return real_link(source, destination)
            with mock.patch.object(mod.os, "link", side_effect=race_link), \
                    self.assertRaises(FileExistsError):
                mod.create_only(raced, b"loser")
            self.assertEqual(raced.read_bytes(), b"winner")

    def test_aws_missing_is_exact_but_auth_and_metadata_drift_abort(self):
        store = mod.AwsCliReadOnlyStore(Path("/aws"), "profile", "bucket")
        missing = mock.Mock(returncode=1, stdout="", stderr=(
            "An error occurred (404) when calling the HeadObject operation: Not Found"))
        with mock.patch.object(store, "_run", return_value=missing), self.assertRaises(mod.ObjectMissing):
            store.download(job()["certificate_key"], Path("unused"))
        denied = mock.Mock(returncode=1, stdout="", stderr=(
            "An error occurred (AccessDenied) when calling the HeadObject operation: denied"))
        with mock.patch.object(store, "_run", return_value=denied), self.assertRaises(mod.AuditError):
            store.download(job()["certificate_key"], Path("unused"))
        first = {"ContentLength": len(compressed()), "ETag": '"a"',
                 "LastModified": "one", "VersionId": "v"}
        second = {**first, "ETag": '"b"'}
        destination = Path(tempfile.mkdtemp()) / "proof.gz"
        def responses(arguments):
            if arguments[1] == "head-object":
                value = first if not hasattr(responses, "seen") else second
                responses.seen = True
                return mock.Mock(returncode=0, stdout=json.dumps(value), stderr="")
            destination.write_bytes(compressed())
            return mock.Mock(returncode=0, stdout="{}", stderr="")
        with mock.patch.object(store, "_run", side_effect=responses), self.assertRaises(mod.AuditError):
            store.download(job()["certificate_key"], destination)

    def test_aws_authentication_environments_are_explicit_and_sealed(self):
        hostile = {"AWS_ACCESS_KEY_ID": "leak", "AWS_SECRET_ACCESS_KEY": "leak",
                   "AWS_SESSION_TOKEN": "leak", "AWS_PROFILE": "wrong",
                   "NO_PROXY": "localhost"}
        with mock.patch.dict(mod.os.environ, hostile, clear=True):
            profile = mod.AwsCliReadOnlyStore(Path("/aws"), "audit-profile", "bucket")
            profile_env = profile._environment()
            role = mod.AwsCliReadOnlyStore(
                Path("/aws"), "audit-profile", "bucket", "instance-role", "us-east-1")
            role_env = role._environment()
        self.assertEqual(profile_env["AWS_PROFILE"], "audit-profile")
        self.assertEqual(profile_env["AWS_EC2_METADATA_DISABLED"], "true")
        self.assertNotIn("AWS_ACCESS_KEY_ID", profile_env)
        self.assertNotIn("AWS_SECRET_ACCESS_KEY", profile_env)
        self.assertNotIn("AWS_SESSION_TOKEN", profile_env)
        self.assertNotIn("AWS_PROFILE", role_env)
        self.assertEqual(role_env["AWS_EC2_METADATA_DISABLED"], "false")
        self.assertEqual(role_env["AWS_SHARED_CREDENTIALS_FILE"], "/dev/null")
        self.assertEqual(role_env["AWS_CONFIG_FILE"], "/dev/null")
        self.assertEqual(role_env["AWS_REGION"], "us-east-1")
        self.assertIn("169.254.169.254", role_env["NO_PROXY"].split(","))
        with self.assertRaises(mod.AuditError):
            mod.AwsCliReadOnlyStore(Path("/aws"), "p", "b", "ambient")
        with self.assertRaises(mod.AuditError):
            mod.AwsCliReadOnlyStore(Path("/aws"), "p", "b", "instance-role", "us-west-2")

    def test_local_validator_uses_exact_offline_container_contract_and_pins(self):
        values = (0,) * len(mod.capacity.TABLE_PAIRS)
        tag = mod.capacity.worker_tag(values)
        item = job(tag)
        calls = []
        def fake_run(argv, **kwargs):
            calls.append(argv)
            if argv[1:3] == ["image", "inspect"]:
                return mock.Mock(
                    returncode=0, stdout=mod.IMAGE_CONFIG_ID + "\n", stderr="")
            if "/usr/bin/sha256sum" in argv:
                target = argv[-1]
                digest = mod.V2CNF_SHA256 if target.endswith("v2cnf") else mod.LRATREPLAY_SHA256
                return mock.Mock(returncode=0, stdout=f"{digest}  {target}\n", stderr="")
            if argv[-3:] == ["emit", "0", "/data/table.json"]:
                kwargs["stdout"].write(b"p cnf 1 1\n1 0\n")
                return mock.Mock(returncode=0, stderr=b"")
            if "check" in argv:
                return mock.Mock(returncode=0, stdout="MATCH (1 clauses, top 1)\n", stderr="")
            return mock.Mock(returncode=0, stdout="LRAT accepted: true\n", stderr="")
        with tempfile.TemporaryDirectory() as directory, \
                mock.patch.object(mod.subprocess, "run", side_effect=fake_run):
            root = Path(directory); compact = root / "proof.lrat"; compact.write_text("1 0 0\n")
            validator = mod.LocalValidator(Path("/docker"), mod.IMAGE, mod.CACHE_VOLUME)
            validator.preflight()
            evidence = validator.validate(item, {"values": values}, compact, root)
        self.assertTrue(evidence["replay_accepted"])
        self.assertEqual(evidence["cnf_sha256"], mod.sha256_bytes(b"p cnf 1 1\n1 0\n"))
        self.assertTrue(all("--network=none" in call for call in calls[1:]))
        self.assertTrue(all(
            ["-v", f"{mod.CACHE_VOLUME}:/cache:ro"] == call[4:6]
            for call in calls[1:]))
        self.assertTrue(any("/cache/bin/lratreplay" in call for call in calls))
        self.assertEqual(calls[0], [
            "/docker", "image", "inspect", mod.IMAGE,
            "--format", "{{.Id}}"])
        self.assertIn("/usr/bin/sha256sum", calls[1])
        self.assertIn("/usr/bin/sha256sum", calls[2])

    def test_local_validator_rejects_missing_or_wrong_runtime_image_config(self):
        validator = mod.LocalValidator(Path("/docker"), mod.IMAGE, mod.CACHE_VOLUME)
        for result in (
            mock.Mock(returncode=1, stdout="", stderr="missing"),
            mock.Mock(returncode=0, stdout="sha256:" + "0" * 64 + "\n", stderr=""),
        ):
            with self.subTest(result=result), \
                    mock.patch.object(mod.subprocess, "run", return_value=result), \
                    self.assertRaisesRegex(mod.AuditError, "runtime image config"):
                validator.preflight()

    def test_image_identity_requires_reviewed_bridge_receipt(self):
        exact = (mod.IMAGE, mod.IMAGE_CONFIG_ID, mod.REVIEWED_IMAGE_OCI_DIGEST,
                 mod.IMAGE_EVIDENCE_RECEIPT_SHA256)
        self.assertEqual(mod.image_identity(*exact), {
            "runtime_tag": mod.IMAGE,
            "runtime_config_id": mod.IMAGE_CONFIG_ID,
            "reviewed_oci_digest": mod.REVIEWED_IMAGE_OCI_DIGEST,
            "evidence_receipt_sha256": mod.IMAGE_EVIDENCE_RECEIPT_SHA256,
        })
        for index in range(len(exact)):
            changed = list(exact)
            changed[index] = "drift"
            with self.subTest(index=index), self.assertRaisesRegex(
                    mod.AuditError, "image identity or evidence bridge"):
                mod.image_identity(*changed)


if __name__ == "__main__":
    unittest.main()
