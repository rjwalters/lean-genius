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
  status                        read-only: the detached controller's last report, controller host, live nodes
  local-pass                    one dry pass of the watch loop from this machine
  host-launch --commit C        start the detached controller host (t4g.small, watches until it acts)
  host-stop                     terminate the controller host
  (--pass canary before the subcommand selects the canary's own prefix, tag and launch template)
  residual                      list items without a CERTIFIED receipt (from synced ledgers)
  release-errors [--yes]        release the claims of batches whose only ledgers are ERROR
  transition                    (--pass canary) canary -> main record: markers, terminal fleet, receipt reconciliation
  markers                       control/ objects and the recorded STOP cause
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
MAIN_PREFIX, MAIN_TAG = vc.PREFIX, vc.TAG
CANARY_PREFIX, CANARY_TAG = MAIN_PREFIX + "-canary", MAIN_TAG + "-canary"
PASS_NAME = "main"
HOST_ROLE = "Erdos85H7HsbController"
HOST_TAG = "e85-h7hsb-controller"  # NOT the fleet tag: `stop` terminates fleet-tagged instances only
HOST_LIFETIME = 72 * 3600


def select_pass(name: str) -> None:
    """The canary runs under its own S3 prefix, tag, launch template and Stripe directory, so the
    persistent control/STOP that ends it can never drain the main run (codex, room 52854). Nothing is
    ever cleared: a STOP or ALARM in either prefix stays there."""
    global PASS_NAME, LIFETIME
    PASS_NAME = name
    if name == "canary":
        vc.PREFIX = vc.BASE_PREFIX = CANARY_PREFIX
        vc.TAG = vc.LT_NAME = CANARY_TAG
        vc.STRIPE = vc.BASE_STRIPE = STRIPE / "run-canary"
        vc.HARD_STOP_USD = 10.0
        LIFETIME = 5 * 3600
        vc.PASS.update(name="h7hsb-canary", lifetime=LIFETIME)


if os.environ.get("E85_AWS_NO_PROFILE"):  # on the controller host: instance role, no named profile
    def _aws(*args: str, check: bool = True, timeout: int = 3600) -> str:
        result = subprocess.run(["aws", "--region", vc.REGION, *args], capture_output=True, text=True, timeout=timeout)
        if check and result.returncode != 0:
            raise RuntimeError(f"aws {' '.join(args[:3])}: {result.stderr.strip()[:500]}")
        return result.stdout
    vc.aws = _aws
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
           f"E85_MAX_BATCHES='{a.max_batches}' E85_PARTIAL_SECONDS='{a.partial_seconds}' E85_PREFIX='{vc.PREFIX}'")
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
    a.lifetime = a.lifetime or LIFETIME
    if PASS_NAME == "canary":
        if a.only or a.manifest:
            raise SystemExit("the canary pass selects its own pinned rows; do not combine it with --only/--manifest")
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
         "Resource": [f"arn:aws:s3:::{vc.BUCKET}/{MAIN_PREFIX}/*", f"arn:aws:s3:::{vc.BUCKET}/{CANARY_PREFIX}/*"]},
        {"Sid": "CampaignList", "Effect": "Allow", "Action": "s3:ListBucket", "Resource": f"arn:aws:s3:::{vc.BUCKET}",
         "Condition": {"StringLike": {"s3:prefix": [f"{MAIN_PREFIX}/*", f"{CANARY_PREFIX}/*"]}}}]}
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


def put_json(key: str, obj: dict) -> None:
    p = vc.STRIPE / "tmp-put.json"
    vc.STRIPE.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=1, sort_keys=True) + "\n")
    vc.aws("s3", "cp", "--only-show-errors", str(p), f"s3://{vc.BUCKET}/{vc.PREFIX}/{key}")


def get_json(key: str, prefix: str = ""):
    raw = vc.aws("s3", "cp", f"s3://{vc.BUCKET}/{prefix or vc.PREFIX}/{key}", "-", check=False)
    try:
        return json.loads(raw) if raw.strip() else None
    except ValueError:
        return {"unparsed": raw[:300]}


CLEARABLE = ("all batches CERTIFIED; stopping", "operator stop")  # never: budget stop, ALARM, unknown cause


def marker_state() -> dict:
    control = sorted(vc.listing("control"))
    return {"prefix": vc.PREFIX, "control_objects": control, "stop": "STOP" in control,
            "alarms": [c for c in control if c.startswith("ALARM")], "stop_cause": get_json("control/STOP-CAUSE") if "STOP" in control else None}


def fleet_state() -> dict:
    fleets = vc.aws_json("ec2", "describe-fleets")["Fleets"]
    mine = [{"id": f["FleetId"], "state": f["FleetState"]} for f in fleets
            if any(t["Key"] == "project" and t["Value"] == vc.TAG for t in f.get("Tags", []))]
    inst = [{"id": r["id"], "state": r["state"], "type": r["type"], "lifecycle": r["lifecycle"]} for r in vc.instances()]
    live = [i for i in inst if i["state"] not in ("terminated", "shutting-down")]
    active = [f for f in mine if f["state"] not in ("deleted", "deleted_terminating", "deleted_running", "failed")]
    return {"tag": vc.TAG, "fleets": mine, "instances": inst, "terminal": not live and not active}


def reconcile() -> dict:
    """Receipts against the pass manifest, from S3 (not from a local mirror): every row needs a CERTIFIED
    ledger whose results object exists; item counts must add up."""
    names = vc.listing("ledger")
    results = set(vc.listing("results"))
    best: dict[str, dict] = {}
    for n in sorted(names):
        l = get_json(f"ledger/{n}")
        if l and (l["id"] not in best or l.get("status") == "CERTIFIED"):
            best[l["id"]] = l
    rows = []
    for r in MANIFEST:
        l = best.get(r["id"])
        rows.append({"id": r["id"], "items": hc.row_items(r), "status": l.get("status") if l else None,
                     "certified": l.get("certified") if l else 0, "node": l.get("node") if l else None,
                     "results_present": bool(l) and l["results_key"].rsplit("/", 1)[1] in results,
                     "results_sha256": l.get("results_sha256") if l else None, "retained": l.get("retained") if l else None})
    ok = all(x["status"] == "CERTIFIED" and x["certified"] == x["items"] and x["results_present"] for x in rows)
    return {"rows": rows, "manifest_rows": len(rows), "items": sum(x["items"] for x in rows),
            "certified_items": sum(x["certified"] or 0 for x in rows if x["status"] == "CERTIFIED"), "all_certified": ok}


def transition(a) -> None:
    """Canary -> full transition record (codex, room 53123), written under the MAIN prefix and locally.
    The canary lives under its own prefix, so its STOP is never cleared and never seen by the main run;
    this record states the marker state of both prefixes, that the canary's instances and fleets are
    terminal, and the canary receipt reconciliation. `--pass main launch` refuses to start without an ok record."""
    if PASS_NAME != "canary":
        raise SystemExit("run as: --pass canary transition")
    canary = {"markers": marker_state(), "fleet": fleet_state(), "receipts": reconcile()}
    cause = (canary["markers"]["stop_cause"] or {}).get("action")
    main_control = sorted(k.rsplit("/", 1)[1] for k in (vc.aws_json(
        "s3api", "list-objects-v2", "--bucket", vc.BUCKET, "--prefix", f"{MAIN_PREFIX}/control/", "--query", "Contents[].Key") or []))
    record = {"schema": "erdos85-h7-hsb-transition-v1", "utc": vc.now().strftime("%Y-%m-%dT%H:%M:%SZ"), "from": CANARY_PREFIX,
              "to": MAIN_PREFIX, "canary": canary, "main_control_objects_before_launch": main_control,
              "canary_stop_cleared": False, "note": a.note,
              "ok": bool(canary["receipts"]["all_certified"] and canary["fleet"]["terminal"] and not canary["markers"]["alarms"]
                         and cause == CLEARABLE[0] and not main_control)}
    (STRIPE / "transition-canary-to-main.json").write_text(json.dumps(record, indent=1, sort_keys=True) + "\n")
    select_pass_main = (vc.PREFIX, vc.STRIPE)
    vc.PREFIX = MAIN_PREFIX
    try:
        put_json("transitions/canary-to-main.json", record)
    finally:
        vc.PREFIX = select_pass_main[0]
    print(json.dumps({k: record[k] for k in ("ok", "utc", "canary_stop_cleared", "main_control_objects_before_launch")}
                     | {"canary_cause": cause, "canary_terminal": canary["fleet"]["terminal"],
                        "canary_certified_items": canary["receipts"]["certified_items"], "canary_items": canary["receipts"]["items"]}))


def stop_cmd(a) -> None:
    """Operator stop: record the cause next to the marker, then the reviewed stop."""
    vc.STRIPE.mkdir(parents=True, exist_ok=True)
    put_json("control/STOP-CAUSE", {"action": "operator stop", "utc": vc.now().strftime("%Y-%m-%dT%H:%M:%SZ"), "note": a.note})
    vc.stop(None)


def launch(a) -> None:
    if not 1 <= a.count <= MAX_NODES:
        raise SystemExit(f"count must be 1..{MAX_NODES}")
    # A fleet is never started into a prefix that carries a STOP or an ALARM (codex, room 53123).
    m = marker_state()
    if m["alarms"]:
        raise SystemExit(f"REFUSED: ALARM marker(s) present in {vc.PREFIX}: {m['alarms']}. An alarm is never cleared by launch.")
    if m["stop"]:
        cause = (m["stop_cause"] or {}).get("action")
        if not a.clear_stop:
            raise SystemExit(f"REFUSED: control/STOP is present in {vc.PREFIX} (cause: {cause!r}). "
                             "Workers would drain at once. See --clear-stop.")
        if cause not in CLEARABLE:
            raise SystemExit(f"REFUSED: STOP cause {cause!r} is not clearable (budget stops and unknown causes are never cleared).")
        if a.dry_run:
            print(json.dumps({"dry_run": True, "would_clear_stop": True, "cause": cause, "reason": a.clear_stop}))
        else:
            stamp = vc.now().strftime("%Y%m%dT%H%M%SZ")
            fs = fleet_state()
            if not fs["terminal"]:
                raise SystemExit("REFUSED: instances or fleets of this pass are still live; STOP stays.")
            for name in ("STOP", "STOP-CAUSE"):  # archived, not destroyed
                vc.aws("s3", "cp", "--only-show-errors", f"s3://{vc.BUCKET}/{vc.PREFIX}/control/{name}",
                       f"s3://{vc.BUCKET}/{vc.PREFIX}/control-history/{name}.{stamp}", check=False)
                vc.aws("s3api", "delete-object", "--bucket", vc.BUCKET, "--key", f"{vc.PREFIX}/control/{name}")
            put_json(f"transitions/clear-stop.{stamp}.json", {"utc": stamp, "reason": a.clear_stop, "cause": cause,
                                                               "markers_before": m, "fleet": fs, "markers_after": marker_state()})
    if PASS_NAME == "main" and not a.manifest_pass:
        rec = get_json("transitions/canary-to-main.json")
        if not (rec and rec.get("ok")) and a.dry_run:
            print(json.dumps({"dry_run": True, "would_refuse": "no ok canary->main transition record"}), file=sys.stderr)
        elif not (rec and rec.get("ok")):
            raise SystemExit("REFUSED: no ok canary->main transition record (run: --pass canary transition). "
                             "For a residual or top-up launch pass --manifest-pass.")
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
    report["prefix"] = vc.PREFIX
    if act and not report.get("action") and len(done) >= len(ids):
        report["action"] = "all batches CERTIFIED; stopping"
        vc.stop(None)
    if act and report.get("action"):  # why the persistent STOP exists; launch reads this and never clears a budget stop
        try:
            put_json("control/STOP-CAUSE", {"action": report["action"], "utc": report["utc"],
                                            "estimated_spend_usd": report.get("estimated_spend_usd")})
        except Exception:  # noqa: BLE001
            pass
    if act:  # what `status` on the Mac reads when the controller runs on the controller host
        try:
            p = vc.STRIPE / "last_report.json"
            p.write_text(json.dumps(report, indent=1) + "\n")
            vc.aws("s3", "cp", "--only-show-errors", str(p), f"s3://{vc.BUCKET}/{vc.PREFIX}/host/last_report.json", check=False)
        except Exception:  # noqa: BLE001
            pass
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


def host_policy() -> dict:
    """Least privilege for the detached controller: watch, release orphans, budget stop. It cannot launch."""
    tagged = {"StringEquals": {"aws:ResourceTag/project": [MAIN_TAG, CANARY_TAG]}}
    objects = [f"arn:aws:s3:::{vc.BUCKET}/{p}/*" for p in (MAIN_PREFIX, CANARY_PREFIX)]
    return {"Version": "2012-10-17", "Statement": [
        {"Sid": "Describe", "Effect": "Allow", "Resource": "*",
         "Action": ["ec2:DescribeInstances", "ec2:DescribeSpotPriceHistory", "ec2:DescribeFleets"]},
        {"Sid": "StopTaggedOnly", "Effect": "Allow", "Action": ["ec2:TerminateInstances", "ec2:DeleteFleets"],
         "Resource": "*", "Condition": tagged},
        {"Sid": "Objects", "Effect": "Allow", "Action": ["s3:GetObject", "s3:PutObject", "s3:DeleteObject"], "Resource": objects},
        {"Sid": "List", "Effect": "Allow", "Action": "s3:ListBucket", "Resource": f"arn:aws:s3:::{vc.BUCKET}",
         "Condition": {"StringLike": {"s3:prefix": [f"{MAIN_PREFIX}/*", f"{CANARY_PREFIX}/*"]}}}]}


def host_user_data(a) -> str:
    sparse = " ".join(f"'{p}'" for p in ["/research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/*",
                                         "/research/problems/erdos-85-wip-01/phase_b_h1_verdict_cloud_20260921/controller.py"])
    extra = f"--hard-stop-usd {a.hard_stop_usd}" if a.hard_stop_usd else ""
    script = f"""#!/bin/bash
exec >> /var/log/e85-host.log 2>&1
set -u
export HOME=/root AWS_DEFAULT_REGION={vc.REGION} E85_AWS_NO_PROFILE=1 E85_H7_STRIPE=/opt/e85/stripe PYTHONUNBUFFERED=1
P=s3://{vc.BUCKET}/{vc.PREFIX}
up() {{ aws s3 cp --only-show-errors /var/log/e85-host.log $P/host/host.log; }}
die() {{ echo "HOST-FAIL: $*"; up; /usr/sbin/poweroff; exit 1; }}
systemd-run --on-active={HOST_LIFETIME} --unit=e85-host-lifetime /usr/sbin/poweroff   # hard stop of the host itself
for t in 1 2 3 4 5; do dnf -y install git python3.12 zstd tar && break; sleep 30; done
command -v git && command -v python3.12 && command -v zstd || die "packages"
mkdir -p /opt/e85/stripe/inputs && cd /opt/e85
for t in 1 2 3; do git clone --filter=blob:none --no-checkout --depth 300 --single-branch -b {BRANCH} https://github.com/rjwalters/lean-genius repo && break; rm -rf repo; sleep 30; done
cd /opt/e85/repo || die "clone"
git sparse-checkout set --no-cone {sparse} || die "sparse"
git checkout --detach {a.commit} || die "checkout"
aws s3 cp --only-show-errors $P/freight/h7-inputs.tar.zst /opt/e85/ && zstd -dc /opt/e85/h7-inputs.tar.zst | tar -C /opt/e85/stripe/inputs -xf - || die "inputs"
[ "$(sha256sum /opt/e85/stripe/inputs/inputs.json | cut -d' ' -f1)" = "{inputs_sha()}" ] || die "inputs.json sha"
cd research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008
echo "$(date -u +%FT%TZ) controller host watching {vc.PREFIX} at {a.commit}"; up
# watch returns when it has acted (budget stop or everything CERTIFIED); any crash is retried.
while true; do
  python3.12 -B cert_controller.py --pass {PASS_NAME} watch {extra} >> /var/log/e85-watch.log 2>&1; rc=$?
  aws s3 cp --only-show-errors /var/log/e85-watch.log $P/host/watch.log
  tail -1 /var/log/e85-watch.log | grep -q '"action"' && break
  echo "$(date -u +%FT%TZ) watch exited rc=$rc without an action; restarting in 60 s"; up; sleep 60
done
echo "$(date -u +%FT%TZ) watch finished with an action; host powers off"; up
/usr/sbin/poweroff
"""
    return base64.b64encode(script.encode()).decode()


def host_launch(a) -> None:
    """A small on-demand instance that runs `watch` detached from the Mac: receipts sync, orphan release,
    spend estimate and the hard budget stop keep working without any session. Self-terminates when the
    watch acts, or after HOST_LIFETIME."""
    trust = {"Version": "2012-10-17", "Statement": [{"Effect": "Allow", "Principal": {"Service": "ec2.amazonaws.com"},
                                                     "Action": "sts:AssumeRole"}]}
    request = {"InstanceType": a.type, "MinCount": 1, "MaxCount": 1, "IamInstanceProfile": {"Name": HOST_ROLE},
               "InstanceInitiatedShutdownBehavior": "terminate",
               "MetadataOptions": {"HttpTokens": "required", "HttpEndpoint": "enabled"},
               "BlockDeviceMappings": [{"DeviceName": "/dev/xvda", "Ebs": {"VolumeSize": 20, "VolumeType": "gp3", "DeleteOnTermination": True}}],
               "TagSpecifications": [{"ResourceType": kind, "Tags": [{"Key": "project", "Value": HOST_TAG}, {"Key": "Name", "Value": f"{HOST_TAG}-{PASS_NAME}"}]}
                                     for kind in ("instance", "volume")],
               "UserData": host_user_data(a)}
    if a.dry_run:
        print(json.dumps({"dry_run": True, "role": HOST_ROLE, "policy": host_policy(),
                          "run_instances": dict(request, UserData=base64.b64decode(request["UserData"]).decode())}, indent=1))
        return
    vc.aws("iam", "create-role", "--role-name", HOST_ROLE, "--assume-role-policy-document", json.dumps(trust),
           "--tags", f"Key=project,Value={HOST_TAG}", check=False)
    vc.aws("iam", "put-role-policy", "--role-name", HOST_ROLE, "--policy-name", "H7HsbWatchAndStop", "--policy-document", json.dumps(host_policy()))
    vc.aws("iam", "create-instance-profile", "--instance-profile-name", HOST_ROLE, check=False)
    vc.aws("iam", "add-role-to-instance-profile", "--instance-profile-name", HOST_ROLE, "--role-name", HOST_ROLE, check=False)
    vpc = vc.aws("ec2", "describe-vpcs", "--filters", "Name=is-default,Values=true", "--query", "Vpcs[0].VpcId", "--output", "text").strip()
    sg = vc.aws_json("ec2", "describe-security-groups", "--filters", f"Name=group-name,Values={vc.SG_NAME}",
                     f"Name=vpc-id,Values={vpc}")["SecurityGroups"][0]["GroupId"]  # created by `setup`
    request.update(ImageId=vc.aws("ssm", "get-parameter", "--name", vc.AMI_PARAM, "--query", "Parameter.Value", "--output", "text").strip(),
                   SecurityGroupIds=[sg])
    import time
    time.sleep(15)  # instance-profile propagation
    out = vc.aws_json("ec2", "run-instances", "--cli-input-json", json.dumps(request))
    print(json.dumps({"controller_host": out["Instances"][0]["InstanceId"], "type": a.type, "pass": PASS_NAME, "prefix": vc.PREFIX}))


def hosts() -> list[dict]:
    data = vc.aws_json("ec2", "describe-instances", "--filters", f"Name=tag:project,Values={HOST_TAG}",
                       "Name=instance-state-name,Values=pending,running,stopping,stopped")
    return [{"id": i["InstanceId"], "state": i["State"]["Name"], "launch": i["LaunchTime"],
             "name": next((t["Value"] for t in i.get("Tags", []) if t["Key"] == "Name"), "")}
            for r in data["Reservations"] for i in r["Instances"]]


def host_stop(a) -> None:
    ids = [h["id"] for h in hosts()]
    if ids:
        vc.aws("ec2", "terminate-instances", "--instance-ids", *ids)
    print(json.dumps({"terminated_controller_hosts": ids}))


def status(a) -> None:
    """Read-only, from anywhere with the 2am-admin profile: the detached controller's last report
    (authoritative for spend, it has seen every instance), its age, the controller host, live nodes."""
    raw = vc.aws("s3", "cp", f"s3://{vc.BUCKET}/{vc.PREFIX}/host/last_report.json", "-", check=False)
    last = json.loads(raw) if raw.strip() else None
    nodes = [r for r in vc.instances() if r["state"] in ("pending", "running")]
    control = vc.listing("control")
    out = {"pass": PASS_NAME, "prefix": vc.PREFIX, "now_utc": vc.now().strftime("%Y-%m-%dT%H:%M:%SZ"),
           "controller_hosts": hosts(), "live_nodes": [{k: str(r[k]) for k in ("id", "type", "az", "lifecycle")} for r in nodes],
           "control_objects": control, "alarm": any(c.startswith("ALARM") for c in control), "stop_written": "STOP" in control,
           "last_controller_report": last}
    if last:
        out["percent_batches_certified"] = round(100 * last.get("certified_batches", 0) / max(1, last.get("queue", 1)), 1)
    print(json.dumps(out, indent=1))


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
    p.add_argument("--pass", dest="pass_name", choices=["main", "canary"], default="main",
                   help="canary: own S3 prefix / tag / launch template, the 8 pinned rows (386 items), $10 hard stop")
    sub = p.add_subparsers(dest="command", required=True)
    s = sub.add_parser("plan"); s.add_argument("--count", type=int, default=0); s.set_defaults(run=plan)
    s = sub.add_parser("setup"); s.add_argument("--commit", required=True); s.add_argument("--only", default="")
    s.add_argument("--heap-mb", type=int, default=2000); s.add_argument("--cap", type=int, default=7200)
    s.add_argument("--lifetime", type=int, default=0); s.add_argument("--max-batches", type=int, default=0)
    s.add_argument("--manifest", default="", help="alternative manifest file (residual pass)")
    s.add_argument("--partial-seconds", type=int, default=600)

    s.add_argument("--dry-run", action="store_true"); s.set_defaults(run=setup)
    s = sub.add_parser("freight"); s.add_argument("--manifest", default=""); s.add_argument("--dry-run", action="store_true"); s.set_defaults(run=freight)
    s = sub.add_parser("launch"); s.add_argument("count", type=int); s.add_argument("--types", nargs="*")
    s.add_argument("--exclude-az", nargs="*", default=EXCLUDE_AZ); s.add_argument("--max-price", default="")
    s.add_argument("--clear-stop", default="", metavar="REASON",
                   help="archive a clearable control/STOP (completion or operator stop only) and log the reason")
    s.add_argument("--manifest-pass", action="store_true", help="residual / top-up launch: skip the canary-record check")
    s.add_argument("--dry-run", action="store_true"); s.set_defaults(run=launch)
    s = sub.add_parser("transition"); s.add_argument("--note", default=""); s.set_defaults(run=transition)
    s = sub.add_parser("markers"); s.set_defaults(run=lambda a: print(json.dumps(marker_state(), indent=1)))
    s = sub.add_parser("launch-ondemand"); s.add_argument("type"); s.add_argument("--az", default="us-east-1a"); s.set_defaults(run=vc.launch_ondemand)
    s = sub.add_parser("watch"); s.add_argument("--dry", action="store_true"); s.add_argument("--once", action="store_true")
    s.add_argument("--hard-stop-usd", type=float, default=0); s.add_argument("--manifest", default=""); s.set_defaults(run=vc.watch)
    s = sub.add_parser("status"); s.add_argument("--manifest", default=""); s.set_defaults(run=status)
    s = sub.add_parser("local-pass"); s.add_argument("--manifest", default=""); s.set_defaults(run=lambda a: vc.watch(argparse.Namespace(dry=True, once=True)))
    s = sub.add_parser("host-launch"); s.add_argument("--commit", required=True); s.add_argument("--type", default="t4g.small")
    s.add_argument("--hard-stop-usd", type=float, default=0); s.add_argument("--dry-run", action="store_true"); s.set_defaults(run=host_launch)
    s = sub.add_parser("host-stop"); s.set_defaults(run=host_stop)
    s = sub.add_parser("residual"); s.add_argument("--manifest", default=""); s.set_defaults(run=residual)
    s = sub.add_parser("release-errors"); s.add_argument("--manifest", default=""); s.add_argument("--yes", action="store_true"); s.set_defaults(run=release_errors)
    s = sub.add_parser("stop"); s.add_argument("--note", default=""); s.set_defaults(run=stop_cmd)
    a = p.parse_args()
    select_pass(a.pass_name)
    if a.command not in ("stop", "host-stop"):
        MANIFEST.extend(hc.canary_rows(inputs_meta()) if PASS_NAME == "canary" else manifest_rows(getattr(a, "manifest", "")))
        vc.PASS["size"] = len(MANIFEST)
    if getattr(a, "hard_stop_usd", 0):
        vc.HARD_STOP_USD = a.hard_stop_usd
    a.run(a)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
