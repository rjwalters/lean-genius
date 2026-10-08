#!/usr/bin/env python3
"""Mac-side controller for the H7 t=0 hsb3 certificate campaign (check-then-discard). SINGLE-SEAT.

Same construction as ../h1_cert_full_20261001/cert_controller.py: a thin layer over the reviewed
verdict-pass controller (../phase_b_h1_verdict_cloud_20260921/controller.py). Its watch loop
(receipt sync to Stripe, orphan-claim release by instance id, spend estimate, budget stop), status
and stop are reused by repointing that module's globals at this campaign's prefix, tag and launch
template. The two H1 fixes are kept: claim owners are re-read from S3 on every pass, and
"complete" means a CERTIFIED ledger for every manifest row.

Subcommands
  plan                          print manifest size, identities and the fleet request (touches nothing)
  setup --commit C [...]        IAM role (own prefix rw, verdict freight read), launch template
  freight                       pack + upload the pinned inputs directory
  launch N [--dry-run] [...]    request N spot instances (us-east-1d excluded by default)
  watch [--dry] [--once]        sync receipts, release dead nodes' claims, estimate spend, budget stop
  status                        one dry pass
  residual                      list items without a CERTIFIED receipt (from synced ledgers)
  release-errors [--yes]        release the claims of batches whose only ledgers are ERROR
  stop                          write control/STOP, terminate every tagged instance, delete the fleets

Budget: HARD_STOP_USD below on the controller's own estimate (override: --hard-stop-usd on watch).
Backstops: fleet request expiry, per-node poweroff after the lifetime, poweroff when idle.
"""
from __future__ import annotations

import argparse
import base64
import datetime as dt
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "phase_b_h1_verdict_cloud_20260921"))
import controller as vc  # noqa: E402  (reviewed verdict-pass controller)
import h7_common as hc  # noqa: E402

STRIPE = Path(os.environ.get("E85_H7_STRIPE", "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h7-hsb-campaign-20261008"))
INPUTS = STRIPE / "inputs"
ROLE = "Erdos85H7HsbWorker"
BRANCH = "erdos85/h7t0-formal-20261007"
VERDICT_PREFIX = vc.BASE_PREFIX  # shared freight: pinned CaDiCaL 3.0.1 build
vc.PREFIX = vc.BASE_PREFIX = "sat49/h7hsb-20261008"
vc.TAG = vc.LT_NAME = "e85-h7hsb-20261008"
vc.STRIPE = vc.BASE_STRIPE = STRIPE / "run"
vc.HARD_STOP_USD = 160.0  # estimate: 50-90 USD at 0.0147 USD/vCPU-h (README section 3); 3 nodes x 36 h at the bid ceiling is 143
# 8 GiB/vCPU: 64 slots x (2 GB checker heap + 1.5 GB) fits with a wide margin. 16xlarge only, so that
# slots = vCPUs = 64 and the spot quota (384 vCPU on 2026-10-08) is 6 nodes.
vc.TYPES = ["r8g.16xlarge", "r7g.16xlarge", "m8g.16xlarge", "m7g.16xlarge"]
vc.MAX_SPOT_PRICE = "1.20"
vc.ON_DEMAND_USD_PER_HOUR.update({"r7g.4xlarge": 0.8568, "r7g.16xlarge": 3.4272, "r8g.16xlarge": 3.7699,
                                  "m7g.16xlarge": 2.6112, "m8g.16xlarge": 2.8723})
vc.EBS_GIB = 40
LIFETIME = 129600  # 36 h per node (3 nodes x 36 h x 64 slots covers the 95% estimate)
vc.PASS.update(name="h7hsb", lifetime=LIFETIME)
EXCLUDE_AZ = ["us-east-1d"]  # 2026-10-04: every one of the 7 H1 spot reclaims was in us-east-1d
MAX_NODES = 6  # 384 spot vCPU quota / 64; the quota is SHARED with CI and other spot jobs (see README)
SPARSE = ["/research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/*",
          "/research/problems/erdos-85-wip-01/h1_cert_full_20261001/cert_row.py"]


def inputs_meta() -> dict:
    return json.loads((INPUTS / "inputs.json").read_text())


def inputs_sha() -> str:
    return hc.sha_file(INPUTS / "inputs.json")


def manifest_rows(manifest: str = "") -> list[dict]:
    raw = Path(manifest).read_bytes() if manifest else hc.manifest_bytes(inputs_meta())
    return [json.loads(l) for l in raw.decode().splitlines() if l.strip()]


def manifest_sha(manifest: str = "") -> str:
    raw = Path(manifest).read_bytes() if manifest else hc.manifest_bytes(inputs_meta())
    return hashlib.sha256(raw).hexdigest()


def user_data(a) -> str:
    sparse = " ".join(f"'{p}'" for p in SPARSE)
    env = (f"export E85_INPUTS_SHA='{inputs_sha()}' E85_MANIFEST_SHA='{manifest_sha(a.manifest)}' "
           f"E85_MANIFEST_KEY='{('freight/' + Path(a.manifest).name) if a.manifest else ''}' "
           f"E85_LIFETIME='{a.lifetime}' E85_ONLY='{a.only}' E85_HEAP_MB='{a.heap_mb}' E85_CAP='{a.cap}' "
           f"E85_MAX_BATCHES='{a.max_batches}' E85_PARTIAL_SECONDS='{a.partial_seconds}'")
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
for t in 1 2 3; do git clone --filter=blob:none --no-checkout --depth 300 --single-branch -b {BRANCH} https://github.com/rjwalters/lean-genius repo && break; rm -rf repo; sleep 30; done
cd /opt/e85/repo || die "clone"
git sparse-checkout set --no-cone {sparse} || die "sparse"
git checkout --detach {a.commit} || die "checkout {a.commit}"
exec bash research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/cert_bootstrap.sh
"""
    return base64.b64encode(script.encode()).decode()


def setup(a) -> None:
    if a.canary:
        if a.only or a.manifest:
            raise SystemExit("--canary selects its own pinned rows; do not combine it with --only/--manifest")
        rows = hc.canary_rows(inputs_meta())
        a.only, a.partial_seconds = ",".join(r["id"] for r in rows), 120
        print(json.dumps({"canary_rows": [r["id"] for r in rows], "canary_items": sum(hc.row_items(r) for r in rows),
                          "partial_seconds": a.partial_seconds}), file=sys.stderr)
    trust = {"Version": "2012-10-17", "Statement": [{"Effect": "Allow", "Principal": {"Service": "ec2.amazonaws.com"},
                                                     "Action": "sts:AssumeRole"}]}
    policy = {"Version": "2012-10-17", "Statement": [
        {"Sid": "VerdictFreightRead", "Effect": "Allow", "Action": ["s3:GetObject"],
         "Resource": f"arn:aws:s3:::{vc.BUCKET}/{VERDICT_PREFIX}/freight/*"},
        {"Sid": "CampaignPrefix", "Effect": "Allow", "Action": ["s3:GetObject", "s3:PutObject"],
         "Resource": f"arn:aws:s3:::{vc.BUCKET}/{vc.PREFIX}/*"},
        {"Sid": "CampaignList", "Effect": "Allow", "Action": "s3:ListBucket", "Resource": f"arn:aws:s3:::{vc.BUCKET}",
         "Condition": {"StringLike": {"s3:prefix": [f"{vc.PREFIX}/*"]}}}]}
    data = {"IamInstanceProfile": {"Name": ROLE}, "InstanceInitiatedShutdownBehavior": "terminate",
            "MetadataOptions": {"HttpTokens": "required", "HttpEndpoint": "enabled"},
            "BlockDeviceMappings": [{"DeviceName": "/dev/xvda", "Ebs": {"VolumeSize": vc.EBS_GIB, "VolumeType": "gp3",
                                                                       "DeleteOnTermination": True}}],
            "TagSpecifications": [{"ResourceType": kind, "Tags": [{"Key": "project", "Value": vc.TAG}, {"Key": "Name", "Value": vc.TAG}]}
                                  for kind in ("instance", "volume")],
            "UserData": user_data(a)}
    if a.dry_run:
        shown = dict(data, UserData=base64.b64decode(data["UserData"]).decode())
        print(json.dumps({"dry_run": True, "role": ROLE, "policy": policy, "launch_template": vc.LT_NAME, "data": shown}, indent=1))
        return
    vc.aws("iam", "create-role", "--role-name", ROLE, "--assume-role-policy-document", json.dumps(trust),
           "--tags", f"Key=project,Value={vc.TAG}", check=False)
    vc.aws("iam", "put-role-policy", "--role-name", ROLE, "--policy-name", "H7HsbPrefixOnly", "--policy-document", json.dumps(policy))
    vc.aws("iam", "create-instance-profile", "--instance-profile-name", ROLE, check=False)
    vc.aws("iam", "add-role-to-instance-profile", "--instance-profile-name", ROLE, "--role-name", ROLE, check=False)
    vpc = vc.aws("ec2", "describe-vpcs", "--filters", "Name=is-default,Values=true", "--query", "Vpcs[0].VpcId", "--output", "text").strip()
    groups = vc.aws_json("ec2", "describe-security-groups", "--filters", f"Name=group-name,Values={vc.SG_NAME}",
                         f"Name=vpc-id,Values={vpc}")["SecurityGroups"]
    if groups:
        sg = groups[0]["GroupId"]
    else:  # absent on 2026-10-08: recreate it exactly as the reviewed verdict-pass setup does (no ingress rules)
        sg = vc.aws_json("ec2", "create-security-group", "--group-name", vc.SG_NAME, "--vpc-id", vpc,
                         "--description", "Erdos 85 workers: no ingress, default egress")["GroupId"]
    ami = vc.aws("ssm", "get-parameter", "--name", vc.AMI_PARAM, "--query", "Parameter.Value", "--output", "text").strip()
    data.update(ImageId=ami, SecurityGroupIds=[sg])
    existing = vc.aws_json("ec2", "describe-launch-templates", "--filters", f"Name=launch-template-name,Values={vc.LT_NAME}")
    if existing["LaunchTemplates"]:
        version = vc.aws_json("ec2", "create-launch-template-version", "--launch-template-name", vc.LT_NAME,
                              "--launch-template-data", json.dumps(data))["LaunchTemplateVersion"]["VersionNumber"]
    else:
        vc.aws("ec2", "create-launch-template", "--launch-template-name", vc.LT_NAME, "--launch-template-data", json.dumps(data))
        version = 1
    print(json.dumps({"role": ROLE, "security_group": sg, "ami": ami, "launch_template": vc.LT_NAME, "version": version,
                      "pinned_commit": a.commit, "inputs_json_sha256": inputs_sha(), "manifest_sha256": manifest_sha(a.manifest),
                      "only": a.only, "cap": a.cap, "heap_mb": a.heap_mb, "lifetime": a.lifetime}))


def fleet_request(a, version: str) -> dict:
    subnets = vc.aws_json("ec2", "describe-subnets", "--filters", "Name=default-for-az,Values=true")["Subnets"]
    subnets = [s for s in subnets if s["AvailabilityZone"] not in a.exclude_az]
    overrides = [{"InstanceType": kind, "SubnetId": s["SubnetId"], "MaxPrice": a.max_price or vc.MAX_SPOT_PRICE}
                 for kind in (a.types or vc.TYPES) for s in subnets]
    return {"Type": "request", "TerminateInstancesWithExpiration": True,
            "ValidUntil": (vc.now() + dt.timedelta(seconds=LIFETIME + 3600)).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "SpotOptions": {"AllocationStrategy": "price-capacity-optimized", "InstanceInterruptionBehavior": "terminate"},
            "LaunchTemplateConfigs": [{"LaunchTemplateSpecification": {"LaunchTemplateName": vc.LT_NAME, "Version": version},
                                       "Overrides": overrides}],
            "TargetCapacitySpecification": {"TotalTargetCapacity": a.count, "DefaultTargetCapacityType": "spot"},
            "TagSpecifications": [{"ResourceType": "fleet", "Tags": [{"Key": "project", "Value": vc.TAG}]}]}


def launch(a) -> None:
    if not 1 <= a.count <= MAX_NODES:
        raise SystemExit(f"count must be 1..{MAX_NODES}")
    version = vc.aws("ec2", "describe-launch-templates", "--launch-template-names", vc.LT_NAME,
                     "--query", "LaunchTemplates[0].LatestVersionNumber", "--output", "text", check=False).strip()
    request = fleet_request(a, version or "<launch template not created: run setup>")
    if a.dry_run:
        print(json.dumps({"dry_run": True, "request": request}, indent=1))
        return
    if not version:
        raise SystemExit("launch template missing: run setup first")
    print(json.dumps(vc.aws_json("ec2", "create-fleet", "--cli-input-json", json.dumps(request))))


def freight(a) -> None:
    meta = inputs_meta()
    names = ["inputs.json", "canonical.body"] + [f"{c}.{ext}" for c in hc.CUBES for ext in ("units", "hsb", "cover")]
    for c in hc.CUBES:
        hc.Cube(INPUTS, c)  # verify every pinned hash before shipping
    out = STRIPE / "h7-inputs.tar.zst"
    tar = subprocess.Popen(["tar", "-C", str(INPUTS), "-cf", "-", *names], stdout=subprocess.PIPE)
    with out.open("wb") as dst:
        subprocess.run(["zstd", "-q", "-19", "-T0", "-c"], stdin=tar.stdout, stdout=dst, check=True)
    tar.stdout.close()
    if tar.wait() != 0:
        raise SystemExit("tar failed")
    cake = STRIPE / "tools" / "cake_lpr"  # the approved checker build, copied from the builder
    if hc.sha_file(cake) != hc.CAKE_LPR_SHA256:
        raise SystemExit(f"{cake} is not the approved cake_lpr build")
    report = {"cake_lpr_sha256": hc.CAKE_LPR_SHA256, "freight": out.name, "bytes": out.stat().st_size, "inputs_json_sha256": inputs_sha(),
              "manifest_sha256": manifest_sha(), "batches": meta["batches"], "leaves": meta["total_leaves"]}
    if a.dry_run:
        print(json.dumps(dict(report, dry_run=True)))
        return
    vc.aws("s3", "cp", "--only-show-errors", str(out), f"s3://{vc.BUCKET}/{vc.PREFIX}/freight/h7-inputs.tar.zst")
    vc.aws("s3", "cp", "--only-show-errors", str(cake), f"s3://{vc.BUCKET}/{vc.PREFIX}/freight/cake_lpr")
    if a.manifest:
        vc.aws("s3", "cp", "--only-show-errors", a.manifest, f"s3://{vc.BUCKET}/{vc.PREFIX}/freight/{Path(a.manifest).name}")
    print(json.dumps(report))
    print(vc.aws("s3", "ls", f"s3://{vc.BUCKET}/{vc.PREFIX}/freight/"))


def ledgers() -> list[dict]:
    out = []
    for p in sorted((vc.STRIPE / "ledger").glob("*.json")):
        try:
            out.append(json.loads(p.read_text()))
        except Exception:  # noqa: BLE001
            continue
    return out


def certified_ids() -> set[str]:
    return {l["id"] for l in ledgers() if l.get("status") == "CERTIFIED"}


_reviewed_one_pass = vc.one_pass
MANIFEST: list[dict] = []


def one_pass(state: dict, act: bool) -> dict:
    """Reviewed pass plus the two H1 cert-run fixes (2026-10-05): claim owners are re-read from S3
    every pass, and completion needs a CERTIFIED ledger for every manifest row. Budget stop untouched."""
    state["claims"] = {}
    size = vc.PASS["size"]
    vc.PASS["size"] = 10**9  # disable the reviewed ledger-count completion; decided below
    try:
        report = _reviewed_one_pass(state, act)
    finally:
        vc.PASS["size"] = size
    ids = {r["id"] for r in MANIFEST}
    ls = ledgers()
    done = {l["id"] for l in ls if l.get("status") == "CERTIFIED"} & ids
    report["queue"], report["certified_batches"] = size, len(done)
    report["certified_items"] = sum(l.get("items", 0) for l in {l["id"]: l for l in ls if l["id"] in done}.values())
    report["solver_cpu_hours"] = round(sum(l.get("solver_cpu_seconds", 0) for l in ls) / 3600, 1)
    report["proof_tb"] = round(sum(l.get("proof_bytes", 0) for l in ls) / 1e12, 3)
    report["hard_stop_usd"] = vc.HARD_STOP_USD
    if act and not report.get("action") and len(done) >= len(ids):
        report["action"] = "all batches CERTIFIED; stopping"
        vc.stop(None)
    return report


vc.one_pass = one_pass


def residual(a) -> None:
    """Items that have no CERTIFIED receipt in any synced ledger; writes a single-leaf-per-row manifest."""
    best: dict[str, dict] = {}
    for l in ledgers():
        if l["id"] not in best or l.get("status") == "CERTIFIED":
            best[l["id"]] = l
    rows, missing = [], []
    for r in MANIFEST:
        l = best.get(r["id"])
        if l is None:
            missing.append(r["id"])
        elif l.get("status") != "CERTIFIED":
            for item in l.get("not_certified", []):
                if r["kind"] == "cover":
                    rows.append({"id": f"{r['cube']}-cover-r", "cube": r["cube"], "kind": "cover"})
                else:
                    rows.append({"id": f"{r['cube']}-r{item['leaf']:05d}", "cube": r["cube"], "kind": "leaves",
                                 "leaves": [item["leaf"]], "previous": item["status"]})
            if l.get("ran", 0) < l.get("items", 0):
                missing.append(r["id"])
    out = STRIPE / "residual-manifest.jsonl"
    out.write_text("".join(json.dumps(r, sort_keys=True) + "\n" for r in rows))
    print(json.dumps({"batches_without_ledger_or_incomplete": len(missing), "first": missing[:10], "residual_items": len(rows),
                      "residual_manifest": str(out), "sha256": hashlib.sha256(out.read_bytes()).hexdigest()}))


def release_errors(a) -> None:
    """Delete the claims of batches whose only ledgers are ERROR (infrastructure failures), so that a
    live node re-claims them. The reviewed pass releases claims of dead nodes only when no ledger exists."""
    by: dict[str, set] = {}
    for l in ledgers():
        by.setdefault(l["id"], set()).add(l.get("status"))
    ids = sorted(i for i, st in by.items() if st == {"ERROR"} and i in {r["id"] for r in MANIFEST})
    claims = set(vc.listing("claims"))
    todo = [i for i in ids if i in claims]
    if a.yes:
        for i in todo:
            vc.aws("s3api", "delete-object", "--bucket", vc.BUCKET, "--key", f"{vc.PREFIX}/claims/{i}")
    print(json.dumps({"error_only_batches": len(ids), "claims_released" if a.yes else "claims_to_release (--yes to act)": todo}))


def plan(a) -> None:
    meta = inputs_meta()
    rows = manifest_rows()
    a.count, a.exclude_az, a.types, a.max_price = a.count or MAX_NODES, EXCLUDE_AZ, None, ""
    print(json.dumps({"inputs_json_sha256": inputs_sha(), "manifest_sha256": manifest_sha(), "batches": len(rows),
                      "cover_rows": sum(r["kind"] == "cover" for r in rows), "leaves": meta["total_leaves"],
                      "hsb_clauses": meta["total_hsb_clauses"], "prefix": f"s3://{vc.BUCKET}/{vc.PREFIX}",
                      "hard_stop_usd": vc.HARD_STOP_USD, "types": vc.TYPES, "max_spot_price": vc.MAX_SPOT_PRICE,
                      "node_lifetime_s": LIFETIME, "exclude_az": EXCLUDE_AZ, "max_nodes": MAX_NODES,
                      "canary_rows": hc.CANARY_IDS, "canary_items": sum(hc.row_items(r) for r in hc.canary_rows(meta))}, indent=1))


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    s = sub.add_parser("plan"); s.add_argument("--count", type=int, default=0); s.set_defaults(run=plan)
    s = sub.add_parser("setup"); s.add_argument("--commit", required=True); s.add_argument("--only", default="")
    s.add_argument("--heap-mb", type=int, default=2000); s.add_argument("--cap", type=int, default=3600)
    s.add_argument("--lifetime", type=int, default=LIFETIME); s.add_argument("--max-batches", type=int, default=0)
    s.add_argument("--manifest", default="", help="alternative manifest file (residual pass)")
    s.add_argument("--partial-seconds", type=int, default=600)
    s.add_argument("--canary", action="store_true", help="pinned mixed canary: 2 covers + 6 leaf batches (386 items), partials every 120 s")
    s.add_argument("--dry-run", action="store_true"); s.set_defaults(run=setup)
    s = sub.add_parser("freight"); s.add_argument("--manifest", default=""); s.add_argument("--dry-run", action="store_true"); s.set_defaults(run=freight)
    s = sub.add_parser("launch"); s.add_argument("count", type=int); s.add_argument("--types", nargs="*")
    s.add_argument("--exclude-az", nargs="*", default=EXCLUDE_AZ); s.add_argument("--max-price", default="")
    s.add_argument("--dry-run", action="store_true"); s.set_defaults(run=launch)
    s = sub.add_parser("launch-ondemand"); s.add_argument("type"); s.add_argument("--az", default="us-east-1a"); s.set_defaults(run=vc.launch_ondemand)
    s = sub.add_parser("watch"); s.add_argument("--dry", action="store_true"); s.add_argument("--once", action="store_true")
    s.add_argument("--hard-stop-usd", type=float, default=0); s.add_argument("--manifest", default=""); s.set_defaults(run=vc.watch)
    s = sub.add_parser("status"); s.add_argument("--manifest", default=""); s.set_defaults(run=lambda a: vc.watch(argparse.Namespace(dry=True, once=True)))
    s = sub.add_parser("residual"); s.add_argument("--manifest", default=""); s.set_defaults(run=residual)
    s = sub.add_parser("release-errors"); s.add_argument("--manifest", default=""); s.add_argument("--yes", action="store_true"); s.set_defaults(run=release_errors)
    s = sub.add_parser("stop"); s.set_defaults(run=vc.stop)
    a = p.parse_args()
    if a.command not in ("stop",):
        MANIFEST.extend(manifest_rows(getattr(a, "manifest", "")))
        vc.PASS["size"] = len(MANIFEST)
    if getattr(a, "hard_stop_usd", 0):
        vc.HARD_STOP_USD = a.hard_stop_usd
    a.run(a)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
