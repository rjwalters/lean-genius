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

    def manifest(self):
        value = {
            "commands": {"compile": list(MOD.PRODUCTION_COMPILE_COMMAND)},
            "environment_allowlist": ["HOME", "LEAN_PATH"],
            "worker_image_digest": MOD.IMAGE_OCI_DIGEST,
        }
        for index, field in enumerate(MOD.OVERLAY_HASH_VARIABLES, 1):
            value[field] = format(index, "x") * 64
        return value

    def bootstrap(self):
        manifest = self.manifest()
        assignments = "\n".join(
            f"{variable}={manifest[field]}"
            for field, variable in MOD.OVERLAY_HASH_VARIABLES.items()
        )
        image_assignments = "\n".join(
            f"{variable}={value}"
            for variable, value in MOD.IMAGE_HASHES.items()
        )
        objects = " ".join(MOD.OVERLAY_OBJECTS)
        reads = "\n".join(
            f"assert manifest['{field}'] == sys.argv[{index}]"
            for index, field in enumerate(MOD.OVERLAY_HASH_VARIABLES, 2)
        )
        return f'''#!/usr/bin/env bash
set -euo pipefail
ROOT=/opt/replay
APT_MIRROR_SOURCE={MOD.APT_MIRROR_SOURCE}
APT_MIRROR_TARGET={MOD.APT_MIRROR_TARGET}
APT_RETRIES={MOD.APT_RETRIES}
export AWS_RETRY_MODE={MOD.AWS_RETRY_MODE}
export AWS_MAX_ATTEMPTS={MOD.AWS_MAX_ATTEMPTS}
sed -i "s|$APT_MIRROR_SOURCE|$APT_MIRROR_TARGET|g" /etc/apt/sources.list.d/ubuntu.sources
apt-get -o Acquire::Retries="$APT_RETRIES" update
apt-get -o Acquire::Retries="$APT_RETRIES" install -y zstd
{assignments}
{image_assignments}
IMAGE_CONFIG_ID={MOD.IMAGE_CONFIG_ID}
IMAGE_OCI_DIGEST={manifest['worker_image_digest']}
for name in {objects}; do
  /usr/local/bin/aws s3api get-object --bucket "$BUCKET" --key "$PREFIX/freight/p1/$name" "$ROOT/freight/$name" --output json
done
printf '%s  %s\n' "$IMAGE_ARCHIVE_SHA" "$ROOT/freight/lean4-arm64-a5ca.docker.tar.zst" \
  "$IMAGE_EVIDENCE_RECEIPT_SHA" "$ROOT/freight/image-evidence/receipt.json" \
  "$IMAGE_EVIDENCE_PRODUCER_SHA" "$ROOT/freight/image-evidence/capture-image-identity.py" | sha256sum -c -
zstd -dc "$ROOT/freight/lean4-arm64-a5ca.docker.tar.zst" | docker load
LOADED_CONFIG_ID=$(docker image inspect {MOD.IMAGE_TAG} --format '{{{{.Id}}}}')
test "$LOADED_CONFIG_ID" = "$IMAGE_CONFIG_ID"
LOADED_ROOTFS=$(docker image inspect {MOD.IMAGE_TAG} --format '{{{{json .RootFS.Layers}}}}')
python3 - "$ROOT/freight/image-evidence" "$IMAGE_ARCHIVE_SHA" "$LOADED_CONFIG_ID" "$IMAGE_OCI_DIGEST" "$LOADED_ROOTFS" <<'IMAGEPY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1]); receipt = json.load(open(root / "receipt.json"))
assert receipt["schema"] == "{MOD.IMAGE_EVIDENCE_SCHEMA}"
assert receipt["archive_sha256"] == sys.argv[2]
assert receipt["archive_config_digest"] == sys.argv[3]
assert receipt["live_repo_digest"] == sys.argv[4]
for row in receipt["files"]:
    data = (root / row["path"]).read_bytes()
    assert hashlib.sha256(data).hexdigest() == row["sha256"]
producer = (root / "capture-image-identity.py").read_bytes()
assert hashlib.sha256(producer).hexdigest() == receipt["producer_sha256"]
live = json.load(open(root / "live-inspect.json"))[0]
fresh_manifest = json.load(open(root / "fresh-save-manifest.json"))
archive_manifest = json.load(open(root / "archive-manifest.json"))
fresh_config = json.load(open(root / "fresh-save-config.json"))
archive_config = json.load(open(root / "archive-config.json"))
assert fresh_manifest == archive_manifest == receipt["fresh_archive_manifest"]
assert fresh_config == archive_config
assert live["RepoTags"] == [receipt["image"]]
assert live["RepoDigests"] == [receipt["live_repo_digest"]]
assert live["RootFS"]["Layers"] == fresh_config["rootfs"]["diff_ids"]
assert live["RootFS"]["Layers"] == json.loads(sys.argv[5])
IMAGEPY
printf '%s  %s\n' "$OVERLAY_ARCHIVE_SHA" "$ROOT/freight/complete-overlay.tar.zst" \\
  "$OVERLAY_MANIFEST_SHA" "$ROOT/freight/complete-overlay-manifest.json" \\
  "$OVERLAY_RECEIPT_SHA" "$ROOT/freight/complete-overlay-receipt.json" \\
  "$OVERLAY_PROJECT_MANIFEST_SHA" "$ROOT/freight/complete-overlay-project.sha256.tsv" \\
  "$OVERLAY_BUILDER_SHA" "$ROOT/repo/h1fleet/build_replay_overlay.py" | sha256sum -c -
mkdir -p "$ROOT/overlay-publication"
zstd -dc "$ROOT/freight/complete-overlay.tar.zst" | tar -C "$ROOT/overlay-publication" -xf -
cmp -s "$ROOT/overlay-publication/manifest.json" "$ROOT/freight/complete-overlay-manifest.json"
cmp -s "$ROOT/overlay-publication/receipt.json" "$ROOT/freight/complete-overlay-receipt.json"
/usr/bin/python3 "$ROOT/repo/h1fleet/build_replay_overlay.py" --verify "$ROOT/overlay-publication"
test ! -e "$ROOT/repo/proofs/.lake/packages"
mv "$ROOT/overlay-publication/overlay" "$ROOT/overlay"
export LEAN_PATH=/opt/replay/overlay
test "$LEAN_PATH" = /opt/replay/overlay
mkdir -p /etc/systemd/system/erdos85-replay.service.d
cat > /etc/systemd/system/erdos85-replay.service.d/environment.conf <<'EOF'
[Service]
Environment=HOME=/root
Environment=LEAN_PATH=/opt/replay/overlay
EOF
systemctl daemon-reload
systemctl start erdos85-replay.service
test "$(systemctl show erdos85-replay.service --property Environment --value)" = "HOME=/root LEAN_PATH=/opt/replay/overlay"
python3 - "$ROOT/manifest.json" "$OVERLAY_BUILDER_SHA" "$OVERLAY_PROJECT_MANIFEST_SHA" "$OVERLAY_RECEIPT_SHA" "$OVERLAY_MANIFEST_SHA" "$OVERLAY_IDENTITY_SHA" "$OVERLAY_ARCHIVE_SHA" <<'PY'
import json, sys
manifest = json.load(open(sys.argv[1]))
receipt = json.load(open('/opt/replay/freight/complete-overlay-receipt.json'))
overlay = json.load(open('/opt/replay/freight/complete-overlay-manifest.json'))
{reads}
{chr(10).join(MOD.OVERLAY_CROSSLINK_ASSERTIONS)}
PY
'''

    def test_bootstrap_rejects_missing_launch_safety_contract(self):
        original = self.bootstrap()
        fragments = (
            f"APT_MIRROR_SOURCE={MOD.APT_MIRROR_SOURCE}",
            f"APT_MIRROR_TARGET={MOD.APT_MIRROR_TARGET}",
            f"APT_RETRIES={MOD.APT_RETRIES}",
            f"export AWS_RETRY_MODE={MOD.AWS_RETRY_MODE}",
            f"export AWS_MAX_ATTEMPTS={MOD.AWS_MAX_ATTEMPTS}",
            'sed -i "s|$APT_MIRROR_SOURCE|$APT_MIRROR_TARGET|g"',
            'apt-get -o Acquire::Retries="$APT_RETRIES" update',
            'apt-get -o Acquire::Retries="$APT_RETRIES" install',
        )
        for fragment in fragments:
            with self.subTest(fragment=fragment), self.assertRaisesRegex(
                    MOD.DeploymentEvidenceError, "launch-safety"):
                MOD.validate_bootstrap_realization(
                    self.manifest(), original.replace(fragment, "omitted", 1))

    def test_bootstrap_rejects_launch_safety_ordering_drift(self):
        original = self.bootstrap()
        cases = (
            original.replace(
                'sed -i "s|$APT_MIRROR_SOURCE|$APT_MIRROR_TARGET|g" '
                "/etc/apt/sources.list.d/ubuntu.sources\n",
                "", 1) +
            '\nsed -i "s|$APT_MIRROR_SOURCE|$APT_MIRROR_TARGET|g" '
            "/etc/apt/sources.list.d/ubuntu.sources\n",
        )
        for changed in cases:
            with self.assertRaisesRegex(
                    MOD.DeploymentEvidenceError, "launch-safety ordering"):
                MOD.validate_bootstrap_realization(self.manifest(), changed)

    def test_bootstrap_rejects_image_evidence_drift(self):
        original = self.bootstrap()
        fragments = (
            'assert receipt["archive_config_digest"] == sys.argv[3]',
            'assert hashlib.sha256(data).hexdigest() == row["sha256"]',
            'assert hashlib.sha256(producer).hexdigest() == receipt["producer_sha256"]',
            'assert fresh_manifest == archive_manifest == receipt["fresh_archive_manifest"]',
            'assert fresh_config == archive_config',
            'assert live["RepoDigests"] == [receipt["live_repo_digest"]]',
            'assert live["RootFS"]["Layers"] == fresh_config["rootfs"]["diff_ids"]',
            'assert live["RootFS"]["Layers"] == json.loads(sys.argv[5])',
        )
        for fragment in fragments:
            with self.subTest(fragment=fragment), self.assertRaisesRegex(
                    MOD.DeploymentEvidenceError, "primary image-evidence"):
                MOD.validate_bootstrap_realization(
                    self.manifest(), original.replace(fragment, "assert True", 1))

        for fragment in fragments:
            moved = original.replace(fragment + "\n", "", 1) + "\n" + fragment + "\n"
            with self.subTest(moved=fragment), self.assertRaisesRegex(
                    MOD.DeploymentEvidenceError, "image verification before service"):
                MOD.validate_bootstrap_realization(self.manifest(), moved)

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
        self.assertEqual(MOD.validate_bootstrap_realization(
            self.manifest(), self.bootstrap()), 82)

    def test_image_evidence_does_not_invent_frozen_manifest_fields(self):
        manifest = self.manifest()
        self.assertNotIn("worker_image_config_id", manifest)
        self.assertNotIn("worker_image_archive_sha256", manifest)
        self.assertNotIn("worker_image_evidence_receipt_sha256", manifest)
        self.assertNotIn("worker_image_evidence_producer_sha256", manifest)
        self.assertEqual(
            MOD.validate_bootstrap_realization(manifest, self.bootstrap()), 82)

    def test_bootstrap_rejects_manifest_identity_and_compile_drift(self):
        cases = []
        manifest = self.manifest()
        manifest["commands"]["compile"] = ["/root/.elan/bin/lake", "env", "lean"]
        cases.append(manifest)
        manifest = self.manifest()
        manifest["environment_allowlist"] = ["HOME"]
        cases.append(manifest)
        manifest = self.manifest()
        manifest["overlay_sha256"] = "f" * 64
        cases.append(manifest)
        for field in MOD.OVERLAY_HASH_VARIABLES:
            manifest = self.manifest()
            manifest[field] = "bad"
            cases.append(manifest)
        manifest = self.manifest()
        manifest["worker_image_digest"] = "lean4-arm64@sha256:" + "a" * 64
        cases.append(manifest)
        for index, manifest in enumerate(cases):
            with self.subTest(index=index), self.assertRaises(
                    MOD.DeploymentEvidenceError):
                MOD.validate_bootstrap_realization(manifest, self.bootstrap())

    def test_bootstrap_rejects_legacy_objects_and_project_only_roots(self):
        for token in (
            "overlay-oleans.tar.zst", "proofs/.lake/build/lib/lean",
            "/root/.elan/bin/lake", " lake env lean",
        ):
            with self.subTest(token=token), self.assertRaisesRegex(
                    MOD.DeploymentEvidenceError, "forbidden legacy"):
                MOD.validate_bootstrap_realization(
                    self.manifest(), self.bootstrap() + "\n# " + token)
        for extraction in (
            'zstd -dc "$ROOT/freight/complete-overlay.tar.zst" | '
            'tar -C "$ROOT/repo/overlay" -xf -',
            'mv "$ROOT/overlay-publication/overlay" "$ROOT/repo/proofs/overlay"',
        ):
            with self.subTest(extraction=extraction), self.assertRaisesRegex(
                    MOD.DeploymentEvidenceError, "into the repository"):
                MOD.validate_bootstrap_realization(
                    self.manifest(), self.bootstrap() + "\n" + extraction)

    def test_bootstrap_rejects_missing_or_tampered_overlay_realization(self):
        original = self.bootstrap()
        for label, changed in (
            ("echo-only", original.replace(
                "/usr/local/bin/aws s3api get-object", "echo", 1)),
            ("wrong-local", original.replace(
                '"$ROOT/freight/$name" --output json',
                '"$ROOT/freight/wrong-name" --output json', 1)),
        ):
            with self.subTest(download=label), self.assertRaisesRegex(
                    MOD.DeploymentEvidenceError, "download loop/mapping"):
                MOD.validate_bootstrap_realization(self.manifest(), changed)
        for name in MOD.OVERLAY_OBJECTS:
            changed = original.replace(name, "missing-object")
            with self.subTest(object=name), self.assertRaisesRegex(
                    MOD.DeploymentEvidenceError, "exact object"):
                MOD.validate_bootstrap_realization(self.manifest(), changed)
        for field, variable in MOD.OVERLAY_HASH_VARIABLES.items():
            changed = original.replace(
                f"{variable}={self.manifest()[field]}", f"{variable}={'f' * 64}", 1)
            with self.subTest(hash=field), self.assertRaisesRegex(
                    MOD.DeploymentEvidenceError, variable):
                MOD.validate_bootstrap_realization(self.manifest(), changed)
            changed = original.replace(f"manifest['{field}']", "manifest['omitted']")
            with self.subTest(readback=field), self.assertRaisesRegex(
                    MOD.DeploymentEvidenceError, "readback omits"):
                MOD.validate_bootstrap_realization(self.manifest(), changed)
        for assertion in MOD.OVERLAY_CROSSLINK_ASSERTIONS:
            changed = original.replace(assertion, "assert True", 1)
            with self.subTest(crosslink=assertion), self.assertRaisesRegex(
                    MOD.DeploymentEvidenceError, "receipt crosslink"):
                MOD.validate_bootstrap_realization(self.manifest(), changed)
        for variable, target in MOD.OVERLAY_HASH_TARGETS.items():
            changed = original.replace(
                f'"${variable}" "{target}"', f'"${variable}" "/wrong-target"', 1)
            with self.subTest(target=variable), self.assertRaises(
                    MOD.DeploymentEvidenceError):
                MOD.validate_bootstrap_realization(self.manifest(), changed)
        manifest_cmp = ('cmp -s "$ROOT/overlay-publication/manifest.json" '
                        '"$ROOT/freight/complete-overlay-manifest.json"')
        receipt_cmp = ('cmp -s "$ROOT/overlay-publication/receipt.json" '
                       '"$ROOT/freight/complete-overlay-receipt.json"')
        swapped_metadata = original.replace(
            manifest_cmp,
            'cmp -s "$ROOT/overlay-publication/manifest.json" '
            '"$ROOT/freight/complete-overlay-receipt.json"', 1,
        ).replace(
            receipt_cmp,
            'cmp -s "$ROOT/overlay-publication/receipt.json" '
            '"$ROOT/freight/complete-overlay-manifest.json"', 1,
        )
        with self.assertRaises(MOD.DeploymentEvidenceError):
            MOD.validate_bootstrap_realization(self.manifest(), swapped_metadata)
        for fragment in (
            'mkdir -p "$ROOT/overlay-publication"',
            'tar -C "$ROOT/overlay-publication" -xf -',
            '/usr/bin/python3 "$ROOT/repo/h1fleet/build_replay_overlay.py" --verify '
            '"$ROOT/overlay-publication"',
            'mv "$ROOT/overlay-publication/overlay" "$ROOT/overlay"',
            "export LEAN_PATH=/opt/replay/overlay",
            'test "$LEAN_PATH" = /opt/replay/overlay',
            "sha256sum -c -",
            'cmp -s "$ROOT/overlay-publication/manifest.json" '
            '"$ROOT/freight/complete-overlay-manifest.json"',
            'cmp -s "$ROOT/overlay-publication/receipt.json" '
            '"$ROOT/freight/complete-overlay-receipt.json"',
            "manifest = json.load(open(sys.argv[1]))",
            "receipt = json.load(open('/opt/replay/freight/complete-overlay-receipt.json'))",
            "overlay = json.load(open('/opt/replay/freight/complete-overlay-manifest.json'))",
            "mkdir -p /etc/systemd/system/erdos85-replay.service.d",
            "cat > /etc/systemd/system/erdos85-replay.service.d/environment.conf <<'EOF'",
            "Environment=HOME=/root",
            "Environment=LEAN_PATH=/opt/replay/overlay",
            "systemctl daemon-reload",
            "systemctl start erdos85-replay.service",
            'test "$(systemctl show erdos85-replay.service --property Environment --value)" '
            '= "HOME=/root LEAN_PATH=/opt/replay/overlay"',
            'test ! -e "$ROOT/repo/proofs/.lake/packages"',
        ):
            changed = original.replace(fragment, "omitted", 1)
            with self.subTest(fragment=fragment), self.assertRaisesRegex(
                    MOD.DeploymentEvidenceError, "required realization"):
                MOD.validate_bootstrap_realization(self.manifest(), changed)
        reordered = original.replace(
            "systemctl daemon-reload\nsystemctl start erdos85-replay.service",
            "systemctl start erdos85-replay.service\nsystemctl daemon-reload", 1)
        with self.assertRaisesRegex(
                MOD.DeploymentEvidenceError, "ordering is not exact"):
            MOD.validate_bootstrap_realization(self.manifest(), reordered)
        wrong_service = original.replace(
            "systemctl start erdos85-replay.service",
            "systemctl start unrelated.service", 1)
        with self.assertRaises(MOD.DeploymentEvidenceError):
            MOD.validate_bootstrap_realization(self.manifest(), wrong_service)
        poisoned_service = original.replace(
            "Environment=LEAN_PATH=/opt/replay/overlay",
            "Environment=LEAN_PATH=/poison", 1)
        with self.assertRaises(MOD.DeploymentEvidenceError):
            MOD.validate_bootstrap_realization(self.manifest(), poisoned_service)
        for package_line in (
            'test -e "$ROOT/repo/proofs/.lake/packages"',
            'test ! -e "$ROOT/repo/proofs/.lake/packages" || true',
        ):
            changed = original.replace(
                'test ! -e "$ROOT/repo/proofs/.lake/packages"', package_line, 1)
            with self.subTest(package=package_line), self.assertRaises(
                    MOD.DeploymentEvidenceError):
                MOD.validate_bootstrap_realization(self.manifest(), changed)
        for line in (
            "ROOT=/opt/replay",
            "export LEAN_PATH=/opt/replay/overlay",
            'test "$LEAN_PATH" = /opt/replay/overlay',
        ):
            changed = original.replace(line, line + "-poison", 1)
            with self.subTest(exact_line=line), self.assertRaises(
                    MOD.DeploymentEvidenceError):
                MOD.validate_bootstrap_realization(self.manifest(), changed)

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
            manifest = root / "manifest.json"
            bootstrap = root / "bootstrap.sh"
            iam.write_text(json.dumps(self.iam()))
            lifecycle.write_text(json.dumps(self.lifecycle()))
            manifest.write_text(json.dumps(self.manifest()))
            bootstrap.write_text(self.bootstrap())
            hashes = MOD.evidence_hashes(
                iam, lifecycle, manifest, bootstrap, identity)
            self.assertEqual(len(hashes), 5)
            self.assertTrue(all(len(value) == 64 for value in hashes))
            iam.write_text(iam.read_text() + "\n")
            changed = MOD.evidence_hashes(
                iam, lifecycle, manifest, bootstrap, identity)
            self.assertNotEqual(hashes[0], changed[0])
            self.assertEqual(hashes[1:], changed[1:])
            bootstrap.write_text(bootstrap.read_text() + "\n")
            changed_bootstrap = MOD.evidence_hashes(
                iam, lifecycle, manifest, bootstrap, identity)
            self.assertNotEqual(changed[3], changed_bootstrap[3])
            self.assertEqual(changed[:3] + changed[4:],
                             changed_bootstrap[:3] + changed_bootstrap[4:])


if __name__ == "__main__":
    unittest.main()
