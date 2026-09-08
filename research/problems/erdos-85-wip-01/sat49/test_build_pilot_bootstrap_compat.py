#!/usr/bin/env python3
"""Exercise isolated generated shell blocks; never launch the bootstrap."""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "pilot_bootstrap_compat", HERE / "build_pilot_bootstrap_compat.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)
CONFIG = "sha256:39a805ad21da2e79dbd2e446c1333e4cdb975e44d401af95a29f7ca6b5a2995e"
OCI = "sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"


class PilotBootstrapCompatTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = (HERE / "pilot-bootstrap-reviewed-v3.sh").read_bytes()
        cls.generated = MOD.render(cls.original).decode()

    def run_shell(self, script, **variables):
        env = os.environ.copy()
        env.update(variables)
        return subprocess.run(
            ["bash", "-c", script], env=env, text=True,
            capture_output=True, timeout=10)

    def test_pinned_original_and_shell_syntax(self):
        self.assertEqual(hashlib.sha256(self.original).hexdigest(),
                         "f48a6c4222ca9cf517b6a2a969fbddfeb64cb96fa58901dfe02435fb49b025c3")
        syntax = subprocess.run(["bash", "-n"], input=self.generated,
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(syntax.returncode, 0, syntax.stderr)
        self.assertEqual(MOD.render(self.original), self.generated.encode())

    def test_modified_original_rejected(self):
        for source in (self.original + b"\n", self.original.replace(
                b"PHASE=initializing", b"PHASE=changed", 1), b""):
            with self.subTest(source_length=len(source)):
                with self.assertRaises(ValueError):
                    MOD.render(source)

    def inspect_image(self, value, status=0):
        block = self.generated.split("LOADED_IMAGE_ID=$(docker", 1)[1]
        block = "LOADED_IMAGE_ID=$(docker" + block.split("LOADED_ROOTFS=", 1)[0]
        script = """set -euo pipefail
docker() { printf '%s' "$FAKE_IMAGE_ID"; return "$FAKE_STATUS"; }
""" + block + '\nprintf "%s|%s" "$LOADED_IMAGE_ID" "$LOADED_IMAGE_ID_KIND"\n'
        return self.run_shell(script, FAKE_IMAGE_ID=value,
                              FAKE_STATUS=str(status), IMAGE_CONFIG_ID=CONFIG,
                              IMAGE_OCI_DIGEST="lean4-arm64@" + OCI)

    def test_accepts_only_exact_config_or_raw_oci(self):
        for value, kind in ((CONFIG, "config"), (OCI, "oci")):
            with self.subTest(kind=kind):
                result = self.inspect_image(value)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(f"loaded image identity kind={kind} id={value}\n", result.stdout)
                self.assertEqual(result.stdout.splitlines()[-1], f"{value}|{kind}")

    def test_bad_inspect_output_rejected(self):
        for value in ("", "sha256:" + "0" * 64, "lean4-arm64@" + OCI,
                      CONFIG + "\n" + OCI, OCI + "\n" + OCI,
                      " " + CONFIG, CONFIG + " "):
            with self.subTest(value=value):
                self.assertNotEqual(self.inspect_image(value).returncode, 0)

    def test_inspect_failure_rejected_even_with_valid_output(self):
        for value in (CONFIG, OCI):
            with self.subTest(value=value):
                self.assertNotEqual(self.inspect_image(value, status=19).returncode, 0)

    def test_evidence_receives_pinned_config(self):
        arguments = self.generated.split(
            'python3 - "$ROOT/freight/image-evidence"', 1)[1].split("<<'PY'", 1)[0]
        self.assertIn('"$IMAGE_CONFIG_ID"', arguments)
        self.assertNotIn('"$LOADED_IMAGE_ID"', arguments)
        self.assertNotIn('"$LOADED_CONFIG_ID"', arguments)

    @unittest.skipUnless(shutil.which("jq"), "jq required for identity serialization")
    def test_identity_distinguishes_pinned_config_from_observation(self):
        block = self.generated.split("PHASE=publishing-identity\n", 1)[1]
        block = block.split("/usr/local/bin/aws", 1)[0]
        for observed, kind in ((CONFIG, "config"), (OCI, "oci")):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as root:
                variables = dict.fromkeys((
                    "INSTANCE_ID", "AMI_ID", "INSTANCE_TYPE", "REGION", "AWS_ID",
                    "ZSTD_ID", "DOCKER_ID", "PYTHON_ID", "IMAGE_ARCHIVE_SHA",
                    "IMAGE_EVIDENCE_RECEIPT_SHA"), "fixture")
                variables.update(ROOT=root, IMAGE_CONFIG_ID=CONFIG,
                                 IMAGE_OCI_DIGEST="lean4-arm64@" + OCI,
                                 LOADED_IMAGE_ID=observed, LOADED_IMAGE_ID_KIND=kind)
                result = self.run_shell("set -euo pipefail\n" + block, **variables)
                self.assertEqual(result.returncode, 0, result.stderr)
                identity = json.loads((Path(root) / "bootstrap-identity.json").read_text())
                self.assertEqual(identity["image_config_id"], CONFIG)
                self.assertEqual(identity["loaded_image_id"], observed)
                self.assertEqual(identity["loaded_image_id_kind"], kind)

    def test_cli_create_only_and_receipt(self):
        with tempfile.TemporaryDirectory() as root:
            output = Path(root) / "bootstrap.sh"
            command = [sys.executable, str(HERE / "build_pilot_bootstrap_compat.py"),
                       "--output", str(output)]
            result = subprocess.run(command, capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            receipt = json.loads(result.stdout)
            self.assertEqual(output.read_bytes(), self.generated.encode())
            self.assertEqual(receipt["output_sha256"],
                             hashlib.sha256(output.read_bytes()).hexdigest())
            self.assertEqual(receipt["output_bytes"], output.stat().st_size)
            self.assertTrue(receipt["freight_review_required"])
            output.write_bytes(b"existing reviewed artifact")
            result = subprocess.run(command, capture_output=True, text=True, timeout=10)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_bytes(), b"existing reviewed artifact")

    def test_dispatcher_and_child_inherit_frozen_overlay(self):
        # Reproduce the production preflight failure with a real subprocess
        # boundary, without downloading freight or running Docker/AWS.
        preamble = 'export DEBIAN_FRONTEND=noninteractive HOME=/root AWS_PAGER='
        self.assertIn(preamble, self.original.decode().splitlines())
        self.assertIn(preamble, self.generated.splitlines())
        original_exports = {line for line in self.original.decode().splitlines()
                            if line.startswith('export ')}
        generated_exports = {line for line in self.generated.splitlines()
                             if line.startswith('export ')}
        self.assertEqual(generated_exports - original_exports,
                         {'export LEAN_PATH="$ROOT/overlay"'})
        self.assertFalse(original_exports - generated_exports)
        with tempfile.TemporaryDirectory(prefix="pilot env ") as root:
            dispatcher = Path(root) / "repo/h1fleet/run_replay_queue.py"
            dispatcher.parent.mkdir(parents=True)
            dispatcher.write_text("""import os, subprocess, sys
if os.environ.get('LEAN_PATH') != os.environ['EXPECTED_OVERLAY']:
    sys.exit(91)
if os.environ.get('HOME') != '/root':
    sys.exit(92)
subprocess.run([sys.executable, '-c',
               'import os, json; print(json.dumps([os.environ["HOME"], os.environ["LEAN_PATH"]]))'], check=True)
sys.exit(int(os.environ['FAKE_RETURN_CODE']))
""")
            def dispatch(text, initial, status):
                block = "PHASE=running-dispatcher\n" + text.split(
                    "PHASE=running-dispatcher\n", 1)[1]
                block = block.replace("/usr/bin/python3", shlex.quote(sys.executable))
                return self.run_shell(
                    "set -euo pipefail\n" + preamble + "\n" + initial + block,
                    ROOT=root, BUCKET="fixture", EXPECTED_OVERLAY=root + "/overlay",
                    FAKE_RETURN_CODE=str(status))
            for initial in ("unset LEAN_PATH\n", "export LEAN_PATH=/wrong\n"):
                with self.subTest(initial=initial):
                    self.assertEqual(dispatch(self.original.decode(), initial, 0).returncode, 91)
                    for status in (0, 23):
                        result = dispatch(self.generated, initial, status)
                        self.assertEqual(result.returncode, status, result.stderr)
                        self.assertEqual(json.loads(result.stdout),
                                         ['/root', root + '/overlay'])

    def test_finish_drains_log_before_upload_and_preserves_exit_status(self):
        # Execute only the EXIT handler and its logging setup. Every absolute
        # external command/path in that block is redirected to a temp fixture.
        finish = "finish() {" + self.generated.split("finish() {", 1)[1].split(
            "\ntrap finish EXIT", 1)[0]
        for status, aws_status, shutdown_status in ((0, 0, 0), (23, 0, 0), (23, 9, 8)):
            with self.subTest(status=status, aws_status=aws_status), \
                    tempfile.TemporaryDirectory() as root:
                root = Path(root)
                aws = root / "aws"
                aws.write_text("""#!/usr/bin/env bash
set -eu
body=
while test "$#" -gt 0; do
  if test "$1" = --body; then body=$2; shift; fi
  shift
done
case "$body" in
  *.log) printf 'upload-log\\n' >> "$EVENTS"; cp "$body" "$CAPTURED_LOG" ;;
  *.json) printf 'upload-terminal\\n' >> "$EVENTS"; cp "$body" "$CAPTURED_TERMINAL" ;;
  *) exit 99 ;;
esac
exit "$AWS_STATUS"
""")
                aws.chmod(0o700)
                shutdown = root / "shutdown"
                shutdown.write_text('#!/usr/bin/env bash\nprintf "shutdown\\n" >> "$EVENTS"\nexit "$SHUTDOWN_STATUS"\n')
                shutdown.chmod(0o700)
                systemctl = root / "systemctl"
                systemctl.write_text('#!/usr/bin/env bash\nprintf "poweroff\\n" >> "$EVENTS"\n')
                systemctl.chmod(0o700)
                mapped = finish
                for original, replacement in (
                    ("/usr/bin/python3", sys.executable),
                    ("/usr/local/bin/aws", str(aws)),
                    ("/usr/sbin/shutdown", str(shutdown)),
                    ("/usr/bin/systemctl", str(systemctl)),
                    ("/tmp/erdos85-replay-bootstrap-terminal.json", str(root / "terminal.json")),
                    ("/var/log/erdos85-replay-bootstrap.log", str(root / "bootstrap.log")),
                ):
                    mapped = mapped.replace(original, shlex.quote(replacement))
                script = """set -euo pipefail
exec 3>&1 4>&2
LOG_TEE_PID=
""" + mapped + """
trap finish EXIT
exec > >(tee -a "$BOOTSTRAP_LOG"; printf 'tee-drained\\n' >> "$EVENTS") 2>&1
LOG_TEE_PID=$!
printf 'dispatcher-final-line\\n'
exit "$FINAL_STATUS"
"""
                result = self.run_shell(
                    script, INSTANCE_ID="i-test", PHASE="dispatcher-complete",
                    BUCKET="fixture", PREFIX="fixture", FINAL_STATUS=str(status),
                    AWS_STATUS=str(aws_status), SHUTDOWN_STATUS=str(shutdown_status),
                    EVENTS=str(root / "events"), BOOTSTRAP_LOG=str(root / "bootstrap.log"),
                    CAPTURED_LOG=str(root / "captured.log"),
                    CAPTURED_TERMINAL=str(root / "captured.json"))
                self.assertEqual(result.returncode, status, result.stderr)
                expected = ["tee-drained", "upload-log", "upload-terminal", "shutdown"]
                if shutdown_status:
                    expected.append("poweroff")
                self.assertEqual((root / "events").read_text().splitlines(), expected)
                self.assertEqual((root / "captured.log").read_text(),
                                 "dispatcher-final-line\nbootstrap terminal "
                                 f"phase=dispatcher-complete returncode={status}\n")
                terminal = json.loads((root / "captured.json").read_text())
                self.assertEqual(terminal["returncode"], status)
                self.assertEqual(terminal["phase"], "dispatcher-complete")


if __name__ == "__main__":
    unittest.main()
