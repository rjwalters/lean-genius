#!/usr/bin/env python3
"""Launch the H3/H5 cube-and-conquer pilot on ONE self-terminating spot instance.

No IAM role, no new security group, no launch template: inputs are fetched and outputs pushed with
presigned S3 URLs (IAM-user credentials, 12 h expiry) under s3://2am-erdos85-certs/sat49/h35-pilot-20261007/.
Hard stop: `shutdown -P +LIFETIME` and a systemd poweroff timer, with InstanceInitiatedShutdownBehavior
= terminate and a one-time spot request (max price below). AMI = the public H1 checker AMI
(CaDiCaL 3.0.1 + cake_lpr + python3.12 preinstalled).
usage: launch_pilot.py upload | launch [--az us-east-1a] [--type r8g.16xlarge]
"""
import argparse, base64, json, subprocess, sys, tarfile, io
from pathlib import Path
import boto3

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
R = "research/problems/erdos-85-wip-01"
B, P = "2am-erdos85-certs", "sat49/h35-pilot-20261007"
AMI, SG_NAME, TAG = "ami-05697724475f2e748", "e85-h35-pilot-20261007-noingress", "e85-h35-pilot-20261007"
LEAN = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h35-probe-20261007/lean")
CELLS = {"h5_t0": "02ccdc18", "h5_t1": "078a3618", "h3_t0": "b5d073a8"}
CODE = [f"{R}/h35_pilot_20261007/pilot_node.py", f"{R}/h35_pilot_20261007/sample_walks.py",
        f"{R}/phase_b_h1_verdict_cloud_20260921/cube_split.py", f"{R}/phase_b_h1_verdict_cloud_20260921/cube_verdict.py",
        f"{R}/sat49/run_verdict_only.py", f"{R}/h1_cert_full_20261001/cert_row.py"]
PLAN = {"cap": 1800, "slots": 64, "cert_n": 2, "heap_mb": 32000, "cells": [
    {"cell": "h5_t0", "walks": 16, "walk_depth": 22, "depths": [19, 16, 13, 10, 7]},
    {"cell": "h3_t0", "walks": 8, "walk_depth": 22, "depths": [18, 14, 10]},
    {"cell": "h5_t1", "walks": 8, "walk_depth": 22, "depths": [19, 16, 13]}]}
LIFETIME_MIN = 170
MAX_PRICE = "1.50"
sess = boto3.Session(profile_name="2am-admin", region_name="us-east-1")
s3, ec2 = sess.client("s3"), sess.client("ec2")


def upload():
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz") as t:
        for f in CODE:
            t.add(REPO / f, arcname=f)
    s3.put_object(Bucket=B, Key=f"{P}/in/code.tar.gz", Body=buf.getvalue())
    for c in CELLS:
        s3.upload_file(str(LEAN / f"{c}.canonical.lean-exact.cnf"), B, f"{P}/in/{c}.cnf")
    print(subprocess.run(["aws", "--profile", "2am-admin", "s3", "ls", f"s3://{B}/{P}/in/"], capture_output=True, text=True).stdout)


def url(method, key):
    return s3.generate_presigned_url(method, Params={"Bucket": B, "Key": f"{P}/{key}"}, ExpiresIn=43200)


def user_data():
    sha = {c: subprocess.run(["shasum", "-a", "256", str(LEAN / f"{c}.canonical.lean-exact.cnf")], capture_output=True, text=True).stdout.split()[0] for c in CELLS}
    for c, pre in CELLS.items():
        assert sha[c].startswith(pre), (c, sha[c])
    outs = {n: url("put_object", f"out/{n}") for n in ("results.jsonl", "node.log", "bootstrap.log", "out.tar.gz")}
    node_urls = {k: outs[k] for k in ("results.jsonl", "node.log")}
    gets = "\n".join(f'curl -fsS -o /scratch/w/bases/{c}.cnf "{url("get_object", f"in/{c}.cnf")}" && '
                     f'[ "$(sha256sum /scratch/w/bases/{c}.cnf | cut -d" " -f1)" = {sha[c]} ] || fail "base {c}"' for c in CELLS)
    return f"""#!/bin/bash
exec > /var/log/e85-pilot.log 2>&1
export PATH=/usr/local/bin:/usr/bin:/usr/sbin:/bin
shutdown -P +{LIFETIME_MIN}
systemd-run --on-active={LIFETIME_MIN * 60 + 300} --unit=e85-hardstop /usr/sbin/poweroff
up() {{ curl -s -X PUT -T /var/log/e85-pilot.log "{outs['bootstrap.log']}"; }}
fail() {{ echo "FAIL: $*"; up; /usr/sbin/poweroff; exit 1; }}
date -u; uname -m; nproc; free -g
mkdir -p /scratch/w/bases /scratch/code
curl -fsS -o /scratch/code.tar.gz "{url('get_object', 'in/code.tar.gz')}" && tar xzf /scratch/code.tar.gz -C /scratch/code || fail code
{gets}
[ "$(cadical --version)" = "3.0.1" ] || fail cadical
printf 'p cnf 2 4\\n1 2 0\\n-1 2 0\\n1 -2 0\\n-1 -2 0\\n' > /scratch/u.cnf
cadical --lrat=true --binary=true /scratch/u.cnf /scratch/u.lrat | grep -qx 's UNSATISFIABLE' || fail "cadical preflight"
cake_lpr /scratch/u.cnf /scratch/u.lrat | grep -qx 's VERIFIED UNSAT' || fail "cake_lpr accept"
head -c 3 /scratch/u.lrat > /scratch/bad.lrat; cake_lpr /scratch/u.cnf /scratch/bad.lrat | grep -q VERIFIED && fail "cake_lpr accepted bad"
cat > /scratch/w/plan.json <<'EOF'
{json.dumps(PLAN)}
EOF
cat > /scratch/w/urls.json <<'EOF'
{json.dumps(node_urls)}
EOF
echo "bootstrap ok $(date -u)"; up
python3.12 -B /scratch/code/{R}/h35_pilot_20261007/pilot_node.py /scratch/w
echo "node exited rc=$? $(date -u)"
tar czf /scratch/out.tar.gz -C /scratch/w out
curl -s -X PUT -T /scratch/out.tar.gz "{outs['out.tar.gz']}"
up; sync; /usr/sbin/poweroff
"""


def launch(a):
    ud = user_data()
    assert len(ud) < 16000, len(ud)
    vpc = ec2.describe_vpcs(Filters=[{"Name": "is-default", "Values": ["true"]}])["Vpcs"][0]["VpcId"]
    found = ec2.describe_security_groups(Filters=[{"Name": "group-name", "Values": [SG_NAME]}, {"Name": "vpc-id", "Values": [vpc]}])["SecurityGroups"]
    sg = found[0]["GroupId"] if found else ec2.create_security_group(  # pilot-owned; deleted by `cleanup`
        GroupName=SG_NAME, Description="e85 h35 pilot: no ingress, default egress", VpcId=vpc,
        TagSpecifications=[{"ResourceType": "security-group", "Tags": [{"Key": "project", "Value": TAG}]}])["GroupId"]
    sub = [s for s in ec2.describe_subnets(Filters=[{"Name": "vpc-id", "Values": [vpc]}, {"Name": "default-for-az", "Values": ["true"]}])["Subnets"]
           if s["AvailabilityZone"] == a.az][0]["SubnetId"]
    r = ec2.run_instances(ImageId=AMI, InstanceType=a.type, MinCount=1, MaxCount=1, SubnetId=sub, SecurityGroupIds=[sg],
                          InstanceInitiatedShutdownBehavior="terminate", UserData=ud,
                          InstanceMarketOptions={"MarketType": "spot", "SpotOptions": {"MaxPrice": MAX_PRICE, "SpotInstanceType": "one-time",
                                                                                       "InstanceInterruptionBehavior": "terminate"}},
                          MetadataOptions={"HttpTokens": "required", "HttpEndpoint": "enabled"},
                          BlockDeviceMappings=[{"DeviceName": "/dev/xvda", "Ebs": {"VolumeSize": 80, "VolumeType": "gp3", "DeleteOnTermination": True}}],
                          TagSpecifications=[{"ResourceType": k, "Tags": [{"Key": "project", "Value": TAG}, {"Key": "Name", "Value": TAG}]}
                                             for k in ("instance", "volume", "spot-instances-request")])
    i = r["Instances"][0]
    print(json.dumps({"instance": i["InstanceId"], "type": a.type, "az": a.az, "launch": str(i["LaunchTime"]), "max_price": MAX_PRICE,
                      "lifetime_min": LIFETIME_MIN, "plan": PLAN}))


def cleanup():
    live = ec2.describe_instances(Filters=[{"Name": "tag:project", "Values": [TAG]},
                                           {"Name": "instance-state-name", "Values": ["pending", "running", "stopping", "stopped", "shutting-down"]}])
    ids = [i["InstanceId"] for r in live["Reservations"] for i in r["Instances"]]
    if ids:
        raise SystemExit(f"instances still alive: {ids}")
    for g in ec2.describe_security_groups(Filters=[{"Name": "group-name", "Values": [SG_NAME]}])["SecurityGroups"]:
        ec2.delete_security_group(GroupId=g["GroupId"]); print("deleted", g["GroupId"])


if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("cmd"); ap.add_argument("--az", default="us-east-1a"); ap.add_argument("--type", default="r8g.16xlarge")
    a = ap.parse_args()
    {"upload": upload, "launch": lambda: launch(a), "cleanup": cleanup}[a.cmd]()
