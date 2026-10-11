"""Offline residual-pass isolation checks and reproduction of the manifest-expansion hazard."""
import base64
import contextlib
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

import cert_controller as cc


cc.select_pass("residual")
assert cc.vc.PREFIX == cc.RESIDUAL_PREFIX != cc.MAIN_PREFIX
assert cc.vc.TAG == cc.vc.LT_NAME == cc.RESIDUAL_TAG != cc.MAIN_TAG
assert cc.vc.STRIPE == cc.STRIPE / "run-residual"
assert cc.vc.HARD_STOP_USD == 100
with patch.object(cc, "hosts", return_value=[
        {"id": "i-main", "name": cc.HOST_TAG + "-main"},
        {"id": "i-residual", "name": cc.HOST_TAG + "-residual"}]), \
        patch.object(cc.vc, "aws") as aws, contextlib.redirect_stdout(io.StringIO()):
    cc.host_stop(None)
    aws.assert_called_once_with("ec2", "terminate-instances", "--instance-ids", "i-residual")

with patch.object(cc, "inputs_sha", return_value="input-pin"), \
        patch.object(cc, "manifest_sha", return_value="manifest-pin"):
    script = base64.b64decode(cc.host_user_data(SimpleNamespace(commit="commit", hard_stop_usd=0))).decode()
    assert script.index("manifest-pin") < script.index("while true; do")
    assert "residual-pass-manifest.jsonl" not in script.split("while true; do", 1)[1]

with tempfile.TemporaryDirectory() as tmp:
    manifest = Path(tmp) / "manifest.jsonl"
    old = {"id": "old", "kind": "leaves", "cube": "cube_a", "leaves": [0]}
    new = {"id": "new", "kind": "leaves", "cube": "cube_a", "leaves": [1]}
    manifest.write_text(json.dumps(old) + "\n")
    snapshot = cc.manifest_rows(str(manifest))
    manifest.write_text(json.dumps(old) + "\n" + json.dumps(new) + "\n")
    assert len(cc.manifest_rows(str(manifest))) == 2
    with patch.object(cc, "MANIFEST", snapshot), patch.object(cc.vc, "STRIPE", Path(tmp)), \
            patch.object(cc, "_reviewed_one_pass", return_value={"utc": "t", "control": [], "claimed": 2}), \
            patch.object(cc, "ledgers", return_value=[{"id": "old", "status": "CERTIFIED"}]), \
            patch.object(cc.vc, "stop") as stop, patch.object(cc, "put_json"), patch.object(cc.vc, "aws"):
        report = cc.one_pass({}, True)
        stop.assert_called_once_with(None)
        assert report["action"] == "all batches CERTIFIED; stopping"

print(json.dumps({"pass_isolation": "passed", "host_stop_isolation": "passed",
                  "host_fetches_manifest_once": True, "expanded_manifest_rows": 2,
                  "running_controller_manifest_rows": len(snapshot),
                  "stale_manifest_stop_reproduced": report["action"]}))
