"""Collect a terminal cold-build bundle without restarting a stopped builder.

This collector runs locally. It does not start/stop the host or retry a build.
It retains failed evidence too, but only exit-zero bundles reach the auditor.
"""
import argparse
import json
import os
import re
import shlex
import subprocess
import tarfile
from pathlib import Path

from audit import audit
from prepare import ROOT, sha


def remote(*args):
    return subprocess.run(["e85-remote", "ssh", shlex.join(map(str, args))],
                          env=dict(os.environ, E85_NO_AUTOSTART="1"),
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)


def safe_extract(archive, destination):
    """Only regular files/directories beneath the single run-output root."""
    with tarfile.open(archive, "r:gz") as tar:
        members = tar.getmembers()
        for item in members:
            path = Path(item.name)
            if path.is_absolute() or ".." in path.parts or not path.parts or path.parts[0] != "run-output":
                raise ValueError("Unexpected archive path: " + item.name)
            if not (item.isfile() or item.isdir()):
                raise ValueError("Archive contains link/special file: " + item.name)
        tar.extractall(destination, members=members)


def collect(job, commit, output):
    if not re.fullmatch(r"\d{8}T\d{6}-commit-[0-9a-f]{12}-\d+", job):
        raise ValueError("Expected a full-SHA worktree job identifier")
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("Full execution commit required")
    jobdir = Path("/opt/e85/jobs") / job
    # Missing exit is not failure/permission to restart. The caller must wait
    # on the same live job or establish its terminal state separately.
    try:
        exit_code = int(remote("cat", jobdir / "exit").stdout.strip())
    except subprocess.CalledProcessError as exc:
        raise RuntimeError("No terminal exit receipt retrieved; do not restart the job") from exc
    actual_commit = remote("cat", jobdir / "sha").stdout.decode().strip()
    if actual_commit != commit:
        raise ValueError("Host execution commit differs from requested commit")
    remote_root = Path("/opt/e85/wt") / ("commit-" + commit[:12])
    folder = Path("research/problems/erdos-85-wip-01/release_cold_build_20261011")
    remote_output = remote_root / folder / "run-output"
    # These are unmodified host receipts, not reconstructed summaries.
    for name in ("sha", "spec", "log", "exit"):
        remote("cp", jobdir / name, remote_output / ("job." + name))
    output.mkdir(parents=True, exist_ok=False)
    archive = output / "run-output.tar.gz"
    command = shlex.join(["tar", "-C", str(remote_root / folder), "-czf", "-", "run-output"])
    with archive.open("xb") as stream:
        child = subprocess.run(["e85-remote", "ssh", command],
                               env=dict(os.environ, E85_NO_AUTOSTART="1"),
                               stdout=stream, stderr=subprocess.PIPE)
    (output / "transfer.stderr").write_bytes(child.stderr)
    if child.returncode:
        raise RuntimeError("Evidence transfer failed; partial archive preserved; no build retry")
    safe_extract(archive, output)
    bundle = output / "run-output"
    if (bundle / "job.sha").read_text().strip() != commit or int((bundle / "job.exit").read_text()) != exit_code:
        raise ValueError("Transferred host receipts differ")
    plan = json.loads((bundle / "plan.json").read_text())
    expected_plan = ROOT / folder / "PLAN.json"
    if (bundle / "plan.json").read_bytes() != expected_plan.read_bytes():
        raise ValueError("Transferred plan is not the frozen local plan")
    result = {"job": job, "execution_commit": commit, "authoritative_exit": exit_code,
              "archive_sha256": sha(archive), "archive_bytes": archive.stat().st_size,
              "plan_sha256": sha(expected_plan), "status": "FAILED_EVIDENCE_RETAINED"}
    if exit_code == 0:
        result["audit"] = audit(plan, bundle)
        result["status"] = "COLD_PROJECT_BUILD_ACCEPTED"
    (output / "CAPTURE.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--job", required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(collect(args.job, args.commit, args.output.resolve()), indent=2))
