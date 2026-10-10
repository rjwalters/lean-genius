"""Reproduce host replacement's missing-checkpoint behavior without cloud calls."""
import base64
import contextlib
import io
import json
import subprocess
from types import SimpleNamespace
from unittest.mock import patch

import cert_controller as cc

calls = []
args = SimpleNamespace(type="t4g.small", commit="fixture", hard_stop_usd=0, dry_run=False, replace=True)
host = {"id": "i-old", "name": cc.HOST_TAG + "-" + cc.PASS_NAME}
with patch.object(cc, "hosts", return_value=[host]), patch.object(cc, "host_user_data", return_value=""), \
        patch.object(cc.vc, "aws", side_effect=lambda *a, **k: calls.append(a) or "x"), \
        patch.object(cc.vc, "aws_json", return_value={"SecurityGroups": [{"GroupId": "sg"}], "Instances": [{"InstanceId": "i-new"}]}), \
        patch("time.sleep"), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
    cc.host_launch(args)
assert calls[0][:2] == ("ec2", "terminate-instances")
assert not any(a[0] in ("s3", "s3api") for a in calls)

with patch.object(cc, "inputs_sha", return_value="fixture"):
    data = base64.b64decode(cc.host_user_data(args)).decode()
restore = next(line for line in data.splitlines() if line.startswith("if aws s3 cp") and cc.HOST_STATE_KEY in line)
# Test the actual generated restore condition. A mock shell function returns a
# failed download; no aws binary, writes, deployment or watch loop is invoked.
r = subprocess.run(["bash", "-c", 'aws() { return 42; }\n' + restore + '\nprintf "REACHED_WATCH\\n"\n'], capture_output=True, text=True)
assert r.returncode == 0 and r.stdout == "REACHED_WATCH\n"
print(json.dumps({"old_host_terminated_without_checkpoint_preflight": True,
                  "failed_state_download_reaches_watch": True,
                  "cloud_mutations": False,
                  "recommendation": "Do not use --replace until state transfer is verified and fails closed. A fresh pass with an explicitly reduced remaining budget is a separate operational workaround."}))
