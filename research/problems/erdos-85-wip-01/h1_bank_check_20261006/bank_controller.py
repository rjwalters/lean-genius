#!/usr/bin/env python3
"""Mac-side controller for the H1 certificate-BANK re-validation (2026-10-06). Adapted from
../h1_cert_full_20261001/cert_controller.py (same reused verdict-controller core and both 10-05 fixes).

Original docstring follows.


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

FREIGHT = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-bank-freight")
IMAGE_ARCHIVE = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-verdict-cloud-20260921/freight/lean4-arm64-v4.31.0.oci.tar.zst")
V2CNF_ZST = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-verdict-cloud-20260921/freight/v2cnf.zst")
BANK_PREFIX = "sat49/campaign-20260825/h1"
ROLE = "Erdos85BankWorker"
SG_NAME = "erdos85-bank-noingress"
VERDICT_PREFIX = vc.BASE_PREFIX  # shared freight: image, v2cnf, CaDiCaL build
vc.PREFIX = vc.BASE_PREFIX = "sat49/bankcheck-20261006"
vc.TAG = vc.LT_NAME = "e85-bank-20261006"
vc.STRIPE = vc.BASE_STRIPE = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-bank-check-20261006")
vc.HARD_STOP_USD = 80.0  # remaining room under the $300 goal ceiling after the ~$204 census
vc.TYPES = ["r7g.16xlarge", "r8g.16xlarge"]  # 512 GiB / 64 vCPU: memory-bound slots fill every core
vc.MAX_SPOT_PRICE = "1.60"
vc.ON_DEMAND_USD_PER_HOUR.update({"r7g.2xlarge": 0.4284, "r7g.4xlarge": 0.8568, "r7g.16xlarge": 3.4272, "r8g.16xlarge": 3.7699, "r6g.16xlarge": 3.2256})
vc.EBS_GIB = 100
LIFETIME = 43200  # 12 h
vc.PASS.update(name="bank", lifetime=LIFETIME)
SPARSE = ["/research/problems/erdos-85-wip-01/h1_bank_check_20261006/*", "/proofs/Proofs/Certificates/h1_orbit_inventory.compact"]


def manifest_sha() -> str:
    return hashlib.sha256((FREIGHT / "bank_manifest.jsonl").read_bytes()).hexdigest()


def user_data(commit: str, only: str, heap_mb: int = 4000, cap: int = 86400, lifetime: int = LIFETIME) -> str:
    sparse = " ".join(f"'{p}'" for p in SPARSE)
    env = f"export E85_MANIFEST_SHA='{manifest_sha()}' E85_LIFETIME='{lifetime}' E85_ONLY='{only}' E85_HEAP_MB='{heap_mb}' E85_CAP='{cap}'"
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
for t in 1 2 3; do git clone --filter=blob:none --no-checkout --depth 50 --single-branch -b erdos85/paper-v6 https://github.com/rjwalters/lean-genius repo && break; rm -rf repo; sleep 30; done
cd /opt/e85/repo || die "clone"
git sparse-checkout set --no-cone {sparse} || die "sparse"
git checkout --detach {commit} || die "checkout {commit}"
exec bash research/problems/erdos-85-wip-01/h1_bank_check_20261006/bank_bootstrap.sh
"""
    return base64.b64encode(script.encode()).decode()


def setup(args) -> None:
    trust = {"Version": "2012-10-17", "Statement": [{"Effect": "Allow", "Principal": {"Service": "ec2.amazonaws.com"},
                                                     "Action": "sts:AssumeRole"}]}
    policy = {"Version": "2012-10-17", "Statement": [
        {"Sid": "BankRead", "Effect": "Allow", "Action": ["s3:GetObject"],
         "Resource": f"arn:aws:s3:::{vc.BUCKET}/{BANK_PREFIX}/*"},
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
    groups = vc.aws_json("ec2", "describe-security-groups", "--filters", f"Name=group-name,Values={SG_NAME}",
                         f"Name=vpc-id,Values={vpc}")["SecurityGroups"]
    sg = groups[0]["GroupId"] if groups else vc.aws_json("ec2", "create-security-group", "--group-name", SG_NAME, "--vpc-id", vpc,
                                                         "--description", "Erdos 85 bank re-validation workers: no ingress")["GroupId"]
    ami = vc.aws("ssm", "get-parameter", "--name", vc.AMI_PARAM, "--query", "Parameter.Value", "--output", "text").strip()
    data = {"ImageId": ami, "IamInstanceProfile": {"Name": ROLE}, "SecurityGroupIds": [sg],
            "InstanceInitiatedShutdownBehavior": "terminate",
            "MetadataOptions": {"HttpTokens": "required", "HttpEndpoint": "enabled"},
            "BlockDeviceMappings": [{"DeviceName": "/dev/xvda", "Ebs": {"VolumeSize": vc.EBS_GIB, "VolumeType": "gp3",
                                                                       "DeleteOnTermination": True}}],
            "TagSpecifications": [{"ResourceType": kind, "Tags": [{"Key": "project", "Value": vc.TAG}, {"Key": "Name", "Value": vc.TAG}]}
                                  for kind in ("instance", "volume")],
            "UserData": user_data(args.commit, args.only, args.heap_mb, args.cap, args.lifetime)}
    existing = vc.aws_json("ec2", "describe-launch-templates", "--filters", f"Name=launch-template-name,Values={vc.LT_NAME}")
    if existing["LaunchTemplates"]:
        version = vc.aws_json("ec2", "create-launch-template-version", "--launch-template-name", vc.LT_NAME,
                              "--launch-template-data", json.dumps(data))["LaunchTemplateVersion"]["VersionNumber"]
    else:
        vc.aws("ec2", "create-launch-template", "--launch-template-name", vc.LT_NAME, "--launch-template-data", json.dumps(data))
        version = 1
    print(json.dumps({"role": ROLE, "security_group": sg, "ami": ami, "launch_template": vc.LT_NAME, "version": version,
                      "pinned_commit": args.commit, "manifest_sha256": manifest_sha(), "only": args.only}))


def launch(args) -> None:
    """vc.launch with an AZ exclusion and a bid ceiling override (2026-10-04: 7 spot reclaims, all in us-east-1d)."""
    if args.max_price:
        vc.MAX_SPOT_PRICE = args.max_price
    if args.exclude_az:
        real = vc.aws_json

        def filtered(*a):
            out = real(*a)
            if a[:2] == ("ec2", "describe-subnets"):
                out["Subnets"] = [s for s in out["Subnets"] if s["AvailabilityZone"] not in args.exclude_az]
            return out
        vc.aws_json = filtered
    vc.launch(args)


def freight(_args) -> None:
    for src, name in ((IMAGE_ARCHIVE, IMAGE_ARCHIVE.name), (V2CNF_ZST, "v2cnf.zst"), (FREIGHT / "bank_manifest.jsonl", "bank_manifest.jsonl")):
        vc.aws("s3", "cp", "--only-show-errors", str(src), f"s3://{vc.BUCKET}/{vc.PREFIX}/freight/{name}", timeout=6 * 3600)
    print(json.dumps({"manifest_sha256": manifest_sha()}))
    print(vc.aws("s3", "ls", f"s3://{vc.BUCKET}/{vc.PREFIX}/freight/"))


def certified_ids() -> set[str]:
    out = set()
    for p in (vc.STRIPE / "ledger").glob("*.json"):
        try:
            l = json.loads(p.read_text())
        except Exception:  # noqa: BLE001
            continue
        if l.get("status") == "VERIFIED":
            out.add(l["id"])
    return out


_reviewed_one_pass = vc.one_pass


def one_pass(state: dict, act: bool) -> dict:
    """Reviewed pass with two cert-run fixes (2026-10-05 incidents):
    (1) claim owners are re-read from S3 every pass (a stale cached owner released live claims);
    (2) "queue complete" requires a CERTIFIED ledger for every manifest row — an ERROR or
        SOLVER_NOT_UNSAT ledger is not completion (the reviewed check stopped a node mid-rerun).
    The reviewed budget stop is untouched."""
    state["claims"] = {}
    size = vc.PASS["size"]
    vc.PASS["size"] = 10**9  # disable the reviewed ledger-count completion; decided below
    try:
        report = _reviewed_one_pass(state, act)
    finally:
        vc.PASS["size"] = size
    done = len(certified_ids() & MANIFEST_IDS)
    report["queue"], report["verified"] = size, done
    if act and not report.get("action") and done >= len(MANIFEST_IDS):
        report["action"] = "all rows VERIFIED; stopping"
        vc.stop(None)
    return report


vc.one_pass = one_pass
MANIFEST_IDS: set[str] = set()


def main() -> int:
    MANIFEST_IDS.update(json.loads(l)["tag"] for l in (FREIGHT / "bank_manifest.jsonl").read_text().splitlines() if l.strip())
    vc.PASS["size"] = len(MANIFEST_IDS)
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    s = sub.add_parser("setup"); s.add_argument("--commit", required=True); s.add_argument("--only", default=""); s.add_argument("--heap-mb", type=int, default=4000)
    s.add_argument("--cap", type=int, default=86400); s.add_argument("--lifetime", type=int, default=LIFETIME); s.set_defaults(run=setup)
    s = sub.add_parser("launch-ondemand"); s.add_argument("type"); s.add_argument("--az", default="us-east-1b"); s.set_defaults(run=vc.launch_ondemand)
    s = sub.add_parser("freight"); s.set_defaults(run=freight)
    s = sub.add_parser("launch"); s.add_argument("count", type=int, choices=range(1, 5)); s.add_argument("--types", nargs="*")
    s.add_argument("--exclude-az", nargs="*", default=[]); s.add_argument("--max-price", default=""); s.set_defaults(run=launch)
    s = sub.add_parser("watch"); s.add_argument("--dry", action="store_true"); s.add_argument("--once", action="store_true"); s.set_defaults(run=vc.watch)
    s = sub.add_parser("status"); s.set_defaults(run=lambda a: vc.watch(argparse.Namespace(dry=True, once=True)))
    s = sub.add_parser("stop"); s.set_defaults(run=vc.stop)
    a = p.parse_args()
    a.run(a)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
