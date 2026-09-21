#!/usr/bin/env python3
"""Mac-side controller for the H1 verdict-only cloud census (board goal #44). SINGLE-SEAT.

Subcommands
  setup            create the scoped IAM role/profile, a no-ingress security group and the launch template
  freight          upload the pinned Docker image archive and the pinned emitter
  launch N         request N spot instances (one-time request fleet, 30 h expiry, terminate on expiry)
  watch            loop: sync receipts to Stripe, release orphaned claims, estimate spend, enforce the budget
  status           one pass of the watch report, no changes
  stop             write control/STOP, terminate every tagged instance, delete the fleets

Budget: operator ceiling is $200 for the whole effort. This controller stops everything when its
own estimate reaches HARD_STOP_USD. Independent backstops: the fleet request expires after 30 h and
terminates its instances; every node powers itself off after 30 h; nodes power off when idle.
"""
from __future__ import annotations

import argparse
import base64
import datetime as dt
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

PROFILE = "2am-admin"
REGION = "us-east-1"
BUCKET = "2am-erdos85-certs"
PREFIX = "sat49/verdict-only-20260921"
TAG = "e85-verdict-20260921"
ROLE = "Erdos85VerdictWorker"
SG_NAME = "erdos85-verdict-noingress"
LT_NAME = "e85-verdict-20260921"
AMI_PARAM = "/aws/service/ami-amazon-linux-latest/al2023-ami-kernel-default-arm64"
TYPES = ["c8g.16xlarge", "c7g.16xlarge", "m8g.16xlarge", "m7g.16xlarge", "r8g.16xlarge", "r7g.16xlarge"]
MAX_SPOT_PRICE = "1.30"
HARD_STOP_USD = 170.0
EBS_GIB = 60
EBS_USD_PER_GIB_HOUR = 0.08 / 730
HERE = Path(__file__).resolve().parent
STRIPE = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-verdict-cloud-20260921")
IMAGE_ARCHIVE = STRIPE / "freight/lean4-arm64-v4.31.0.oci.tar.zst"
EMITTER = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/campaign-20260825.noindex/h1fleet/"
               "v3freight-rebuild-20260905/stage/freight/v2cnf")
EMITTER_SHA = "4bd9604c6d670ad65a8ca332a26dbf35132418634a3b0678c177c8b2cfff4bf6"
SPARSE = ["/research/problems/erdos-85-wip-01/sat49/*.py",
          "/research/problems/erdos-85-wip-01/phase_b_h1_verdict_20260916/*",
          "/research/problems/erdos-85-wip-01/phase_b_h1_verdict_cloud_20260921/*"]


def aws(*args: str, check: bool = True, timeout: int = 3600) -> str:
    result = subprocess.run(["aws", "--profile", PROFILE, "--region", REGION, *args],
                            capture_output=True, text=True, timeout=timeout)
    if check and result.returncode != 0:
        raise RuntimeError(f"aws {' '.join(args[:3])}: {result.stderr.strip()[:500]}")
    return result.stdout


def aws_json(*args: str):
    out = aws(*args, "--output", "json")
    return json.loads(out) if out.strip() else None


def now() -> dt.datetime:
    return dt.datetime.now(dt.timezone.utc)


def user_data(commit: str) -> str:
    sparse = " ".join(f"'{p}'" for p in SPARSE + ["/" + line for line in
                      (HERE / "captured-paths.txt").read_text().split()])
    script = f"""#!/bin/bash
exec >> /var/log/e85-userdata.log 2>&1
set -u
export HOME=/root AWS_DEFAULT_REGION={REGION}
TOKEN=$(curl -s -X PUT http://169.254.169.254/latest/api/token -H 'X-aws-ec2-metadata-token-ttl-seconds: 600')
IID=$(curl -s -H "X-aws-ec2-metadata-token: $TOKEN" http://169.254.169.254/latest/meta-data/instance-id)
die() {{ echo "USERDATA-FAIL: $*"; aws s3 cp --only-show-errors /var/log/e85-userdata.log s3://{BUCKET}/{PREFIX}/nodes/$IID/userdata-FAILED.log; /usr/sbin/poweroff; exit 1; }}
for t in 1 2 3 4 5; do dnf -y install git && break; sleep 30; done
command -v git || die "git install"
mkdir -p /opt/e85 && cd /opt/e85
for t in 1 2 3; do git clone --filter=blob:none --no-checkout --depth 400 --single-branch -b erdos85/integration https://github.com/rjwalters/lean-genius repo && break; rm -rf repo; sleep 30; done
cd /opt/e85/repo || die "clone"
git sparse-checkout set --no-cone {sparse} || die "sparse"
git checkout --detach {commit} || die "checkout {commit}"
exec bash research/problems/erdos-85-wip-01/phase_b_h1_verdict_cloud_20260921/node_bootstrap.sh
"""
    return base64.b64encode(script.encode()).decode()


def setup(args) -> None:
    trust = {"Version": "2012-10-17", "Statement": [{"Effect": "Allow", "Principal": {"Service": "ec2.amazonaws.com"},
                                                     "Action": "sts:AssumeRole"}]}
    policy = {"Version": "2012-10-17", "Statement": [
        {"Sid": "PrefixObjects", "Effect": "Allow", "Action": ["s3:GetObject", "s3:PutObject"],
         "Resource": f"arn:aws:s3:::{BUCKET}/{PREFIX}/*"},
        {"Sid": "PrefixList", "Effect": "Allow", "Action": "s3:ListBucket", "Resource": f"arn:aws:s3:::{BUCKET}",
         "Condition": {"StringLike": {"s3:prefix": [f"{PREFIX}/*"]}}}]}
    aws("iam", "create-role", "--role-name", ROLE, "--assume-role-policy-document", json.dumps(trust),
        "--tags", f"Key=project,Value={TAG}", check=False)
    aws("iam", "put-role-policy", "--role-name", ROLE, "--policy-name", "VerdictPrefixOnly",
        "--policy-document", json.dumps(policy))
    aws("iam", "create-instance-profile", "--instance-profile-name", ROLE, check=False)
    aws("iam", "add-role-to-instance-profile", "--instance-profile-name", ROLE, "--role-name", ROLE, check=False)
    vpc = aws("ec2", "describe-vpcs", "--filters", "Name=is-default,Values=true",
              "--query", "Vpcs[0].VpcId", "--output", "text").strip()
    groups = aws_json("ec2", "describe-security-groups", "--filters", f"Name=group-name,Values={SG_NAME}",
                      f"Name=vpc-id,Values={vpc}")["SecurityGroups"]
    if groups:
        sg = groups[0]["GroupId"]
    else:
        sg = aws_json("ec2", "create-security-group", "--group-name", SG_NAME, "--vpc-id", vpc,
                      "--description", "Erdos 85 verdict-only workers: no ingress, default egress")["GroupId"]
    ami = aws("ssm", "get-parameter", "--name", AMI_PARAM, "--query", "Parameter.Value", "--output", "text").strip()
    data = {"ImageId": ami, "IamInstanceProfile": {"Name": ROLE}, "SecurityGroupIds": [sg],
            "InstanceInitiatedShutdownBehavior": "terminate",
            "MetadataOptions": {"HttpTokens": "required", "HttpEndpoint": "enabled"},
            "BlockDeviceMappings": [{"DeviceName": "/dev/xvda", "Ebs": {"VolumeSize": EBS_GIB, "VolumeType": "gp3",
                                                                       "DeleteOnTermination": True}}],
            "TagSpecifications": [{"ResourceType": kind, "Tags": [{"Key": "project", "Value": TAG},
                                                                   {"Key": "Name", "Value": TAG}]}
                                  for kind in ("instance", "volume")],
            "UserData": user_data(args.commit)}
    existing = aws_json("ec2", "describe-launch-templates", "--filters", f"Name=launch-template-name,Values={LT_NAME}")
    if existing["LaunchTemplates"]:
        version = aws_json("ec2", "create-launch-template-version", "--launch-template-name", LT_NAME,
                           "--launch-template-data", json.dumps(data))["LaunchTemplateVersion"]["VersionNumber"]
    else:
        aws("ec2", "create-launch-template", "--launch-template-name", LT_NAME,
            "--launch-template-data", json.dumps(data))
        version = 1
    print(json.dumps({"role": ROLE, "security_group": sg, "ami": ami, "launch_template": LT_NAME,
                      "version": version, "pinned_commit": args.commit}))


def freight(_args) -> None:
    raw = EMITTER.read_bytes()
    if hashlib.sha256(raw).hexdigest() != EMITTER_SHA:
        raise SystemExit("emitter identity mismatch")
    packed = STRIPE / "freight/v2cnf.zst"
    if not packed.exists():
        subprocess.run(["zstd", "-q", "-19", "-T0", str(EMITTER), "-o", str(packed)], check=True)
    for path in (packed, IMAGE_ARCHIVE):
        print("uploading", path.name, path.stat().st_size, flush=True)
        aws("s3", "cp", "--only-show-errors", str(path), f"s3://{BUCKET}/{PREFIX}/freight/{path.name}", timeout=6 * 3600)
    print(aws("s3", "ls", f"s3://{BUCKET}/{PREFIX}/freight/"))


def launch(args) -> None:
    version = aws("ec2", "describe-launch-templates", "--launch-template-names", LT_NAME,
                  "--query", "LaunchTemplates[0].LatestVersionNumber", "--output", "text").strip()
    subnets = aws_json("ec2", "describe-subnets", "--filters", "Name=default-for-az,Values=true")["Subnets"]
    overrides = [{"InstanceType": kind, "SubnetId": subnet["SubnetId"], "MaxPrice": MAX_SPOT_PRICE}
                 for kind in (args.types or TYPES) for subnet in subnets]
    request = {"Type": "request", "TerminateInstancesWithExpiration": True,
               "ValidUntil": (now() + dt.timedelta(hours=30)).strftime("%Y-%m-%dT%H:%M:%SZ"),
               "SpotOptions": {"AllocationStrategy": "price-capacity-optimized",
                               "InstanceInterruptionBehavior": "terminate"},
               "LaunchTemplateConfigs": [{"LaunchTemplateSpecification": {"LaunchTemplateName": LT_NAME,
                                                                           "Version": version},
                                          "Overrides": overrides}],
               "TargetCapacitySpecification": {"TotalTargetCapacity": args.count, "DefaultTargetCapacityType": "spot"},
               "TagSpecifications": [{"ResourceType": "fleet", "Tags": [{"Key": "project", "Value": TAG}]}]}
    print(json.dumps(aws_json("ec2", "create-fleet", "--cli-input-json", json.dumps(request))))


def instances() -> list[dict]:
    data = aws_json("ec2", "describe-instances", "--filters", f"Name=tag:project,Values={TAG}")
    rows = []
    for reservation in data["Reservations"]:
        for item in reservation["Instances"]:
            rows.append({"id": item["InstanceId"], "type": item["InstanceType"], "state": item["State"]["Name"],
                         "az": item["Placement"]["AvailabilityZone"], "launch": item["LaunchTime"]})
    return rows


def spot_price(kind: str, az: str, cache: dict) -> float:
    if (kind, az) not in cache:
        out = aws_json("ec2", "describe-spot-price-history", "--instance-types", kind, "--availability-zone", az,
                       "--product-descriptions", "Linux/UNIX", "--start-time", now().strftime("%Y-%m-%dT%H:%M:%SZ"))
        prices = [float(row["SpotPrice"]) for row in out["SpotPriceHistory"]]
        cache[(kind, az)] = max(prices) if prices else float(MAX_SPOT_PRICE)
    return cache[(kind, az)]


def listing(sub: str) -> list[str]:
    out = aws_json("s3api", "list-objects-v2", "--bucket", BUCKET, "--prefix", f"{PREFIX}/{sub}/",
                   "--query", "Contents[].Key")
    return [key.rsplit("/", 1)[1] for key in (out or [])]


def one_pass(state: dict, act: bool) -> dict:
    rows = instances()
    live = {row["id"] for row in row_filter(rows, {"pending", "running"})}
    prices: dict = {}
    for row in rows:
        seen = state["instances"].setdefault(row["id"], {"type": row["type"], "az": row["az"],
                                                          "launch": row["launch"], "end": None, "price": None})
        if row["state"] in ("pending", "running"):
            seen["price"] = max(seen["price"] or 0.0, spot_price(row["type"], row["az"], prices))
        elif seen["end"] is None:
            seen["end"] = now().isoformat()
    spend = 0.0
    for seen in state["instances"].values():
        start = dt.datetime.fromisoformat(seen["launch"].replace("Z", "+00:00"))
        end = dt.datetime.fromisoformat(seen["end"]) if seen["end"] else now()
        hours = max(0.0, (end - start).total_seconds() / 3600)
        spend += hours * ((seen["price"] or float(MAX_SPOT_PRICE)) + EBS_GIB * EBS_USD_PER_GIB_HOUR + 0.005)
    spend *= 1.10  # margin for price drift, S3 requests and transfer
    claims = set(listing("claims"))
    ledgers = listing("ledger")
    finished: dict[str, list[str]] = {}
    for name in ledgers:
        finished.setdefault(name.split(".", 1)[0], []).append(name)
    control = listing("control")
    if act:
        for sub in ("ledger", "results", "nodes", "control"):
            (STRIPE / sub).mkdir(parents=True, exist_ok=True)
            aws("s3", "sync", "--only-show-errors", f"s3://{BUCKET}/{PREFIX}/{sub}/", str(STRIPE / sub))
    statuses: dict[str, int] = {}
    for case_id in finished:
        best = None
        for name in finished[case_id]:
            path = STRIPE / "ledger" / name
            if path.is_file():
                best = json.loads(path.read_text()).get("status", "?")
        statuses[best or "unsynced"] = statuses.get(best or "unsynced", 0) + 1
    released = []
    for case_id in sorted(claims - set(finished)):
        owner = state["claims"].get(case_id)
        if owner is None:
            owner = aws("s3", "cp", f"s3://{BUCKET}/{PREFIX}/claims/{case_id}", "-", check=False).strip()
            state["claims"][case_id] = owner
        if owner and owner not in live and owner in state["instances"]:
            if act:
                aws("s3api", "delete-object", "--bucket", BUCKET, "--key", f"{PREFIX}/claims/{case_id}")
                state["claims"].pop(case_id, None)
            released.append(case_id)
    report = {"utc": now().strftime("%Y-%m-%dT%H:%M:%SZ"), "live_instances": len(live),
              "instances_seen": len(state["instances"]), "estimated_spend_usd": round(spend, 2),
              "queue": 1137, "claimed": len(claims), "finished": len(finished), "statuses": statuses,
              "orphans_released": len(released), "control": control}
    if act and spend >= HARD_STOP_USD:
        report["action"] = "HARD BUDGET STOP"
        stop(None)
    elif act and live and len(finished) >= 1137 and not (claims - set(finished)):
        report["action"] = "queue complete; stopping"
        stop(None)
    return report


def row_filter(rows: list[dict], states: set[str]) -> list[dict]:
    return [row for row in rows if row["state"] in states]


def stop(_args) -> None:
    marker = STRIPE / "STOP.txt"
    STRIPE.mkdir(parents=True, exist_ok=True)
    marker.write_text(f"controller stop {now().isoformat()}\n")
    aws("s3", "cp", "--only-show-errors", str(marker), f"s3://{BUCKET}/{PREFIX}/control/STOP", check=False)
    fleets = aws_json("ec2", "describe-fleets", "--filters", "Name=fleet-state,Values=submitted,active,modifying")
    ids = [f["FleetId"] for f in fleets["Fleets"] if any(t["Key"] == "project" and t["Value"] == TAG for t in f.get("Tags", []))]
    if ids:
        aws("ec2", "delete-fleets", "--fleet-ids", *ids, "--terminate-instances")
    live = [row["id"] for row in row_filter(instances(), {"pending", "running", "stopping", "stopped"})]
    if live:
        aws("ec2", "terminate-instances", "--instance-ids", *live)
    print(json.dumps({"stopped_fleets": ids, "terminated": live}))


def watch(args) -> None:
    STRIPE.mkdir(parents=True, exist_ok=True)
    state_path = STRIPE / "controller-state.json"
    state = json.loads(state_path.read_text()) if state_path.exists() else {"instances": {}, "claims": {}}
    while True:
        try:
            report = one_pass(state, act=not args.dry)
            state_path.write_text(json.dumps(state, indent=1) + "\n")
            with (STRIPE / "controller.log").open("a") as out:
                out.write(json.dumps(report) + "\n")
            print(json.dumps(report), flush=True)
            if report.get("action") or args.once:
                return
        except Exception as error:  # noqa: BLE001
            print(f"{now().isoformat()} controller pass failed: {error}", flush=True)
        time.sleep(300)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("setup"); p.add_argument("--commit", required=True); p.set_defaults(run=setup)
    p = sub.add_parser("freight"); p.set_defaults(run=freight)
    p = sub.add_parser("launch"); p.add_argument("count", type=int, choices=range(1, 5))
    p.add_argument("--types", nargs="*"); p.set_defaults(run=launch)
    p = sub.add_parser("watch"); p.add_argument("--dry", action="store_true"); p.add_argument("--once", action="store_true")
    p.set_defaults(run=watch)
    p = sub.add_parser("status"); p.set_defaults(run=lambda a: watch(argparse.Namespace(dry=True, once=True)))
    p = sub.add_parser("stop"); p.set_defaults(run=stop)
    args = parser.parse_args()
    args.run(args)
    return 0


if __name__ == "__main__":
    sys.exit(main())
