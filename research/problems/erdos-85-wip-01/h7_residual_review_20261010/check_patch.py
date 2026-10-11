"""Build and test an apply-ready patch from immutable git objects; no AWS calls.

Run: python3 -B check_patch.py
Writes stop_enforcement.patch and results.json beside this script.
"""
import difflib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
COMMIT = "bda60d921326f904ab143e0ad197c81c4bc3874e"
BASE = "research/problems/erdos-85-wip-01/"
CAMPAIGN = BASE + "h7_hsb_campaign_20261008/"
OLD = '''    if ids:
        vc.aws("ec2", "delete-fleets", "--fleet-ids", *ids, "--terminate-instances")
'''
NEW = '''    if ids:
        reply = vc.aws_json("ec2", "delete-fleets", "--fleet-ids", *ids, "--terminate-instances")
        # EC2 can return HTTP success with per-fleet failures. Keep the watch alive
        # to retry; killing instances alone lets a maintain fleet replace them.
        succeeded = {f["FleetId"] for f in reply.get("Successful", [])}
        missing = sorted(set(ids) - succeeded)
        if reply.get("Unsuccessful") or missing:
            raise RuntimeError(f"fleet deletion incomplete: missing={missing}, errors={reply.get('Unsuccessful', [])}")
'''
STOP = '''

def stop_pass(_args) -> None:
    """Checked shutdown for operator, budget and completion stops of this H7 pass."""
    vc.STRIPE.mkdir(parents=True, exist_ok=True)
    marker = vc.STRIPE / "STOP.txt"
    marker.write_text(f"controller stop {vc.now().isoformat()}\\n")
    vc.aws("s3", "cp", "--only-show-errors", str(marker), f"s3://{vc.BUCKET}/{vc.PREFIX}/control/STOP")
    print(json.dumps(terminate_pass_fleet()))


# The inherited one_pass resolves stop in vc's globals, so budget stops also
# use the checked path without changing other campaigns' source files.
vc.stop = stop_pass
'''


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args])


def run(script, directory):
    env = dict(os.environ, PYTHONPATH=str(directory), PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run([sys.executable, "-B", str(script)], env=env, capture_output=True, text=True)
    return {"exit_code": result.returncode, "output": result.stdout + result.stderr}


def main():
    with tempfile.TemporaryDirectory(prefix="h7-stop-review-") as tmp:
        root = Path(tmp)
        paths = git("ls-tree", "-r", "--name-only", COMMIT, CAMPAIGN).decode().splitlines()
        paths += [BASE + "phase_b_h1_verdict_cloud_20260921/controller.py", BASE + "h1_cert_full_20261001/cert_row.py"]
        for name in paths:
            dest = root / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(git("show", COMMIT + ":" + name))
        campaign = root / CAMPAIGN
        original = run(HERE / "test_stop_enforcement.py", campaign)
        changes = {}
        controller = campaign / "cert_controller.py"
        before = controller.read_text()
        assert before.count(OLD) == 1
        after = before.replace(OLD, NEW).replace("\n\ndef launch(a) -> None:", STOP + "\n\ndef launch(a) -> None:")
        controller.write_text(after)
        changes[CAMPAIGN + "cert_controller.py"] = (before, after)
        suite = campaign / "test_campaign.py"
        before = suite.read_text()
        old_mock = 'lambda *a: {"Fleets": [{"FleetId": "fleet-1", "Tags": [{"Key": "project", "Value": cc.vc.TAG}]}]}'
        new_mock = 'lambda *a: calls.append(("aws",) + a) or ({"Successful": [{"FleetId": "fleet-1"}], "Unsuccessful": []} if a[1] == "delete-fleets" else {"Fleets": [{"FleetId": "fleet-1", "Tags": [{"Key": "project", "Value": cc.vc.TAG}]}]})'
        assert before.count(old_mock) == 1
        after = before.replace(old_mock, new_mock)
        suite.write_text(after)
        changes[CAMPAIGN + "test_campaign.py"] = (before, after)
        regression = (HERE / "test_stop_enforcement.py").read_text()
        changes[CAMPAIGN + "test_stop_enforcement.py"] = ("", regression)
        diff = "".join("".join(difflib.unified_diff(a.splitlines(True), b.splitlines(True),
                         fromfile="a/" + name if a else "/dev/null", tofile="b/" + name))
                       for name, (a, b) in changes.items())
        (HERE / "stop_enforcement.patch").write_text(diff)
        result = {"commit": COMMIT, "original_stop_regressions": original,
                  "patched_stop_regressions": run(HERE / "test_stop_enforcement.py", campaign),
                  "patched_existing_suite": run(suite, campaign),
                  "residual_probe": run(HERE / "probe_residual.py", campaign), "cloud_mutations": False}
        (HERE / "results.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps({k: v["exit_code"] for k, v in result.items() if isinstance(v, dict)}, indent=2))
        assert original["exit_code"] != 0
        assert result["patched_stop_regressions"]["exit_code"] == 0
        assert result["patched_existing_suite"]["exit_code"] == 0
        assert result["residual_probe"]["exit_code"] == 0


if __name__ == "__main__":
    main()
