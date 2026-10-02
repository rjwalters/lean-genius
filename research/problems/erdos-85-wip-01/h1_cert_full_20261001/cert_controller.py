#!/usr/bin/env python3
"""Mac-side controller for the H1 CERTIFIED census (board goal #48, check-then-discard).

A thin layer over the reviewed verdict-pass controller (../phase_b_h1_verdict_cloud_20260921/controller.py):
its watch loop (receipt sync to Stripe, orphan-claim release, spend estimate, budget stop), status and stop
are reused unchanged by repointing that module's globals at the cert prefix, tag and launch template.
New here: a separate IAM role (read the verdict pass's freight, read/write only the cert prefix), the cert
launch template (user data runs cert_bootstrap.sh), and the cert freight upload.

Subcommands: setup --commit C | freight | launch N [--types ...] | watch | status | stop
Budget: operator ceiling $300 (goal #48); hard stop at HARD_STOP_USD on the controller's own estimate.
Backstops: fleet request expiry, per-node poweroff after E85_LIFETIME, poweroff when idle.
"""
from __future__ import annotations

import argparse, base64, hashlib, json, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "phase_b_h1_verdict_cloud_20260921"))
import controller as vc  # noqa: E402  (reviewed verdict-pass controller)

FREIGHT = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-cert-full-freight")
ROLE = "Erdos85CertWorker"
VERDICT_PREFIX = vc.BASE_PREFIX  # shared freight: image, v2cnf, CaDiCaL build
vc.PREFIX = vc.BASE_PREFIX = "sat49/cert-20261001"
vc.TAG = vc.LT_NAME = "e85-cert-20261001"
vc.STRIPE = vc.BASE_STRIPE = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-cert-full-20261001")
vc.HARD_STOP_USD = 250.0
vc.TYPES = ["r7g.16xlarge", "r8g.16xlarge", "r6g.16xlarge"]  # 512 GiB / 64 vCPU: memory-bound slots fill every core
vc.MAX_SPOT_PRICE = "1.60"
vc.ON_DEMAND_USD_PER_HOUR.update({"r7g.16xlarge": 3.4272, "r8g.16xlarge": 3.7699, "r6g.16xlarge": 3.2256})
vc.EBS_GIB = 100
LIFETIME = 129600  # 36 h
vc.PASS.update(name="cert", lifetime=LIFETIME)
SPARSE = ["/research/problems/erdos-85-wip-01/h1_cert_full_20261001/*"]


def manifest_sha() -> str:
    return hashlib.sha256((FREIGHT / "manifest.jsonl").read_bytes()).hexdigest()


def user_data(commit: str, only: str) -> str:
    sparse = " ".join(f"'{p}'" for p in SPARSE)
    env = f"export E85_MANIFEST_SHA='{manifest_sha()}' E85_LIFETIME='{LIFETIME}' E85_ONLY='{only}'"
    script = f"""#!/bin/bash
exec >> /var/log/e85-userdata.log 2>&1
set -u
export HOME=/root AWS_DEFAULT_REGION={vc.REGION}
{env}
TOKEN=$(curl -s -X PUT http://169.254.169.254/latest/api/token -H 'X-aws-ec2-metadata-token-ttl-seconds: 600')
IID=$(curl -s -H "X-aws-ec2-metadata-token: $TOKEN" http://169.254.169.254/latest/meta-data/instance-id)
die() {{ echo "USERDATA-FAIL: $*"; aws s3 cp --only-show-errors /var/log/e85-userdata.log s3://{vc.BUCKET}/{vc.PREFIX}/nodes/$IID/userdata-FAILED.log; /usr/sbin/poweroff; exit 1; }}
for t in 1 2 3 4 5; do dnf -y install git && break; sleep 30; done
command -v git || die "git install"
mkdir -p /opt/e85 && cd /opt/e85
for t in 1 2 3; do git clone --filter=blob:none --no-checkout --depth 50 --single-branch -b erdos85/cert-pilot-20261001 https://github.com/rjwalters/lean-genius repo && break; rm -rf repo; sleep 30; done
cd /opt/e85/repo || die "clone"
git sparse-checkout set --no-cone {sparse} || die "sparse"
git checkout --detach {commit} || die "checkout {commit}"
exec bash research/problems/erdos-85-wip-01/h1_cert_full_20261001/cert_bootstrap.sh
"""
    return base64.b64encode(script.encode()).decode()


def setup(args) -> None:
    trust = {"Version": "2012-10-17", "Statement": [{"Effect": "Allow", "Principal": {"Service": "ec2.amazonaws.com"},
                                                     "Action": "sts:AssumeRole"}]}
    policy = {"Version": "2012-10-17", "Statement": [
        {"Sid": "VerdictFreightRead", "Effect": "Allow", "Action": ["s3:GetObject"],
         "Resource": f"arn:aws:s3:::{vc.BUCKET}/{VERDICT_PREFIX}/freight/*"},
        {"Sid": "CertPrefix", "Effect": "Allow", "Action": ["s3:GetObject", "s3:PutObject"],
         "Resource": f"arn:aws:s3:::{vc.BUCKET}/{vc.PREFIX}/*"},
        {"Sid": "CertList", "Effect": "Allow", "Action": "s3:ListBucket", "Resource": f"arn:aws:s3:::{vc.BUCKET}",
         "Condition": {"StringLike": {"s3:prefix": [f"{vc.PREFIX}/*"]}}}]}
    vc.aws("iam", "create-role", "--role-name", ROLE, "--assume-role-policy-document", json.dumps(trust),
           "--tags", f"Key=project,Value={vc.TAG}", check=False)
    vc.aws("iam", "put-role-policy", "--role-name", ROLE, "--policy-name", "CertPrefixOnly", "--policy-document", json.dumps(policy))
    vc.aws("iam", "create-instance-profile", "--instance-profile-name", ROLE, check=False)
    vc.aws("iam", "add-role-to-instance-profile", "--instance-profile-name", ROLE, "--role-name", ROLE, check=False)
    vpc = vc.aws("ec2", "describe-vpcs", "--filters", "Name=is-default,Values=true", "--query", "Vpcs[0].VpcId", "--output", "text").strip()
    sg = vc.aws_json("ec2", "describe-security-groups", "--filters", f"Name=group-name,Values={vc.SG_NAME}",
                     f"Name=vpc-id,Values={vpc}")["SecurityGroups"][0]["GroupId"]
    ami = vc.aws("ssm", "get-parameter", "--name", vc.AMI_PARAM, "--query", "Parameter.Value", "--output", "text").strip()
    data = {"ImageId": ami, "IamInstanceProfile": {"Name": ROLE}, "SecurityGroupIds": [sg],
            "InstanceInitiatedShutdownBehavior": "terminate",
            "MetadataOptions": {"HttpTokens": "required", "HttpEndpoint": "enabled"},
            "BlockDeviceMappings": [{"DeviceName": "/dev/xvda", "Ebs": {"VolumeSize": vc.EBS_GIB, "VolumeType": "gp3",
                                                                       "DeleteOnTermination": True}}],
            "TagSpecifications": [{"ResourceType": kind, "Tags": [{"Key": "project", "Value": vc.TAG}, {"Key": "Name", "Value": vc.TAG}]}
                                  for kind in ("instance", "volume")],
            "UserData": user_data(args.commit, args.only)}
    existing = vc.aws_json("ec2", "describe-launch-templates", "--filters", f"Name=launch-template-name,Values={vc.LT_NAME}")
    if existing["LaunchTemplates"]:
        version = vc.aws_json("ec2", "create-launch-template-version", "--launch-template-name", vc.LT_NAME,
                              "--launch-template-data", json.dumps(data))["LaunchTemplateVersion"]["VersionNumber"]
    else:
        vc.aws("ec2", "create-launch-template", "--launch-template-name", vc.LT_NAME, "--launch-template-data", json.dumps(data))
        version = 1
    print(json.dumps({"role": ROLE, "security_group": sg, "ami": ami, "launch_template": vc.LT_NAME, "version": version,
                      "pinned_commit": args.commit, "manifest_sha256": manifest_sha(), "only": args.only}))


def freight(_args) -> None:
    out = FREIGHT.parent / "cert-freight.tar.zst"
    tar = subprocess.Popen(["tar", "-C", str(FREIGHT.parent), "-cf", "-", "-s", f"|^{FREIGHT.name}|cert|", FREIGHT.name], stdout=subprocess.PIPE)
    with out.open("wb") as dst:
        subprocess.run(["zstd", "-q", "-19", "-c"], stdin=tar.stdout, stdout=dst, check=True)
    tar.stdout.close()
    if tar.wait() != 0:
        raise SystemExit("tar failed")
    vc.aws("s3", "cp", "--only-show-errors", str(out), f"s3://{vc.BUCKET}/{vc.PREFIX}/freight/cert-freight.tar.zst")
    print(json.dumps({"freight": out.name, "bytes": out.stat().st_size, "manifest_sha256": manifest_sha()}))
    print(vc.aws("s3", "ls", f"s3://{vc.BUCKET}/{vc.PREFIX}/freight/"))


def main() -> int:
    vc.PASS["size"] = sum(1 for l in (FREIGHT / "manifest.jsonl").read_text().splitlines() if l.strip())
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    s = sub.add_parser("setup"); s.add_argument("--commit", required=True); s.add_argument("--only", default=""); s.set_defaults(run=setup)
    s = sub.add_parser("freight"); s.set_defaults(run=freight)
    s = sub.add_parser("launch"); s.add_argument("count", type=int, choices=range(1, 5)); s.add_argument("--types", nargs="*"); s.set_defaults(run=vc.launch)
    s = sub.add_parser("watch"); s.add_argument("--dry", action="store_true"); s.add_argument("--once", action="store_true"); s.set_defaults(run=vc.watch)
    s = sub.add_parser("status"); s.set_defaults(run=lambda a: vc.watch(argparse.Namespace(dry=True, once=True)))
    s = sub.add_parser("stop"); s.set_defaults(run=vc.stop)
    a = p.parse_args()
    a.run(a)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
