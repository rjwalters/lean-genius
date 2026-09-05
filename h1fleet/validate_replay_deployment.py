#!/usr/bin/env python3
"""Validate offline IAM, lifecycle, manifest, and bootstrap evidence for H1 replay.

This tool makes no AWS calls.  An authorized operator must capture the complete
JSON outputs first.  A candidate PASS is evidence about those byte-exact inputs
and the named sentinel resources only.  It does not replace review of the
complete identity/resource policy set, and cannot discharge the launch gate
until the editor approves the proposed freight prefix and lifecycle-rule ID.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


# Exact candidate identity.  BUCKET/INPUT_PREFIX/OUTPUT_PREFIX are established
# campaign names; FREIGHT_PREFIX and LIFECYCLE_RULE_ID still require the editor
# approval named in APPROVAL_NOTICE before this can be release evidence.
BUCKET = "2am-erdos85-certs"
INPUT_PREFIX = "sat49/campaign-20260825/h1/"
OUTPUT_PREFIX = "sat49/campaign-20260825/h1-replay/"
FREIGHT_PREFIX = "sat49/campaign-20260825/h1-replay-freight/"
LIFECYCLE_RULE_ID = "erdos85-h1-replay-consumed-glacier-ir"
APPROVAL_NOTICE = (
    "candidate_only=true launch_gate_discharged=false "
    "pending_editor_approval=freight-prefix+lifecycle-rule-id"
)
OVERLAY_OBJECTS = (
    "complete-overlay.tar.zst",
    "complete-overlay-manifest.json",
    "complete-overlay-receipt.json",
    "complete-overlay-project.sha256.tsv",
)
OVERLAY_HASH_VARIABLES = {
    "overlay_builder_sha256": "OVERLAY_BUILDER_SHA",
    "overlay_project_manifest_sha256": "OVERLAY_PROJECT_MANIFEST_SHA",
    "overlay_build_receipt_sha256": "OVERLAY_RECEIPT_SHA",
    "overlay_manifest_sha256": "OVERLAY_MANIFEST_SHA",
    "overlay_identity_sha256": "OVERLAY_IDENTITY_SHA",
    "overlay_archive_sha256": "OVERLAY_ARCHIVE_SHA",
}
OVERLAY_HASH_TARGETS = {
    "OVERLAY_BUILDER_SHA": "$ROOT/repo/h1fleet/build_replay_overlay.py",
    "OVERLAY_PROJECT_MANIFEST_SHA": "$ROOT/freight/complete-overlay-project.sha256.tsv",
    "OVERLAY_RECEIPT_SHA": "$ROOT/freight/complete-overlay-receipt.json",
    "OVERLAY_MANIFEST_SHA": "$ROOT/freight/complete-overlay-manifest.json",
    "OVERLAY_ARCHIVE_SHA": "$ROOT/freight/complete-overlay.tar.zst",
}
OVERLAY_CROSSLINK_ASSERTIONS = (
    "assert receipt['producer_sha256'] == manifest['overlay_builder_sha256']",
    "assert receipt['project_manifest_sha256'] == manifest['overlay_project_manifest_sha256']",
    "assert receipt['manifest_sha256'] == manifest['overlay_manifest_sha256']",
    "assert receipt['overlay_identity_sha256'] == manifest['overlay_identity_sha256']",
    "assert overlay['identity_sha256'] == manifest['overlay_identity_sha256']",
)
APT_MIRROR_SOURCE = "us-east-1.ec2.ports.ubuntu.com"
APT_MIRROR_TARGET = "ports.ubuntu.com"
APT_RETRIES = "5"
AWS_RETRY_MODE = "standard"
AWS_MAX_ATTEMPTS = "5"
PRODUCTION_COMPILE_COMMAND = [
    "/usr/bin/docker", "run", "--rm", "--network", "none",
    "--mount", "type=bind,src=/opt/replay/repo,dst=/opt/replay/repo,readonly",
    "--mount", "type=bind,src=/opt/replay/state,dst=/opt/replay/state",
    "--mount", "type=bind,src=/opt/replay/overlay,dst=/opt/replay/overlay,readonly",
    "--env", "LEAN_PATH=/opt/replay/overlay",
    "lean4-arm64:v4.31.0", "/root/.elan/bin/lean",
    "-R", "{work}", "-o", "{olean}", "{source}",
]


class DeploymentEvidenceError(ValueError):
    pass


def _load(path: Path) -> object:
    try:
        return json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        raise DeploymentEvidenceError(f"{path}: invalid JSON: {exc.msg}") from exc


def _object_arn(bucket: str, key: str) -> str:
    return f"arn:aws:s3:::{bucket}/{key}"


def validate_identity(bucket: str, input_prefix: str, output_prefix: str,
                      freight_prefix: str, rule_id: str) -> dict[str, str]:
    identity = {
        "bucket": bucket,
        "input_prefix": input_prefix,
        "output_prefix": output_prefix,
        "freight_prefix": freight_prefix,
        "lifecycle_rule_id": rule_id,
    }
    frozen = {
        "bucket": BUCKET,
        "input_prefix": INPUT_PREFIX,
        "output_prefix": OUTPUT_PREFIX,
        "freight_prefix": FREIGHT_PREFIX,
        "lifecycle_rule_id": LIFECYCLE_RULE_ID,
    }
    if identity != frozen:
        raise DeploymentEvidenceError("deployment identity differs from exact candidate")
    prefixes = (input_prefix, output_prefix, freight_prefix)
    if any(not value or not value.endswith("/") for value in prefixes):
        raise DeploymentEvidenceError("deployment prefixes must be nonempty and end in slash")
    if any(_prefixes_overlap(left, right) for index, left in enumerate(prefixes)
           for right in prefixes[index + 1:]):
        raise DeploymentEvidenceError("deployment prefixes must be distinct and non-overlapping")
    return identity


def validate_iam(document: object, bucket: str, input_prefix: str,
                 output_prefix: str, freight_prefix: str) -> int:
    validate_identity(bucket, input_prefix, output_prefix, freight_prefix,
                      LIFECYCLE_RULE_ID)
    if not isinstance(document, dict) or not isinstance(
            document.get("EvaluationResults"), list):
        raise DeploymentEvidenceError("IAM evidence lacks EvaluationResults")
    decisions: dict[tuple[str, str], str] = {}
    for number, result in enumerate(document["EvaluationResults"]):
        if not isinstance(result, dict):
            raise DeploymentEvidenceError(f"IAM result {number} is not an object")
        action = result.get("EvalActionName")
        resource = result.get("EvalResourceName")
        decision = result.get("EvalDecision")
        if not all(isinstance(value, str) for value in (action, resource, decision)):
            raise DeploymentEvidenceError(f"IAM result {number} has malformed identity")
        key = (action.lower(), resource)
        if key in decisions:
            raise DeploymentEvidenceError(f"duplicate IAM result: {key}")
        decisions[key] = decision.lower()

    bucket_arn = f"arn:aws:s3:::{bucket}"
    input_arn = _object_arn(bucket, input_prefix + "__replay_audit_input__")
    output_arn = _object_arn(bucket, output_prefix + "__replay_audit_output__")
    freight_arn = _object_arn(bucket, freight_prefix + "__replay_audit_freight__")
    required = {
        ("s3:listbucket", bucket_arn): "allowed",
        ("s3:getobject", input_arn): "allowed",
        ("s3:getobjecttagging", input_arn): "allowed",
        ("s3:putobjecttagging", input_arn): "allowed",
        ("s3:getobject", output_arn): "allowed",
        ("s3:putobject", output_arn): "allowed",
        ("s3:getobject", freight_arn): "allowed",
        ("s3:putobject", freight_arn): "allowed",
        ("s3:putobject", input_arn): "denied",
    }
    for resource in (input_arn, output_arn, freight_arn):
        required[("s3:deleteobject", resource)] = "denied"
        required[("s3:deleteobjectversion", resource)] = "denied"
    for key, wanted in required.items():
        actual = decisions.get(key)
        if wanted == "allowed" and actual != "allowed":
            raise DeploymentEvidenceError(
                f"IAM simulation must allow {key}, got {actual!r}")
        if wanted == "denied" and actual not in {"implicitdeny", "explicitdeny"}:
            raise DeploymentEvidenceError(
                f"IAM simulation must deny {key}, got {actual!r}")
    return len(required)


def _filter(rule: dict) -> tuple[str, dict[str, str]]:
    value = rule.get("Filter")
    if not isinstance(value, dict):
        raise DeploymentEvidenceError("lifecycle rule lacks an object Filter")
    if set(value) == {"And"} and isinstance(value["And"], dict):
        inner = value["And"]
        prefix = inner.get("Prefix")
        tags = inner.get("Tags")
        if not isinstance(prefix, str) or not isinstance(tags, list):
            raise DeploymentEvidenceError("lifecycle And filter is malformed")
        parsed: dict[str, str] = {}
        for tag in tags:
            if (not isinstance(tag, dict) or set(tag) != {"Key", "Value"} or
                    not all(isinstance(tag[k], str) for k in ("Key", "Value")) or
                    tag["Key"] in parsed):
                raise DeploymentEvidenceError("lifecycle filter tags are malformed")
            parsed[tag["Key"]] = tag["Value"]
        return prefix, parsed
    if set(value) == {"Prefix"} and isinstance(value["Prefix"], str):
        return value["Prefix"], {}
    raise DeploymentEvidenceError("unsupported lifecycle Filter shape")


def _prefixes_overlap(left: str, right: str) -> bool:
    return left.startswith(right) or right.startswith(left)


def evidence_hashes(iam_path: Path, lifecycle_path: Path, manifest_path: Path,
                    bootstrap_path: Path, identity: dict[str, str]) -> tuple[str, ...]:
    return (
        hashlib.sha256(iam_path.read_bytes()).hexdigest(),
        hashlib.sha256(lifecycle_path.read_bytes()).hexdigest(),
        hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
        hashlib.sha256(bootstrap_path.read_bytes()).hexdigest(),
        hashlib.sha256(json.dumps(
            identity, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
    )


def validate_lifecycle(document: object, input_prefix: str, rule_id: str) -> int:
    validate_identity(BUCKET, input_prefix, OUTPUT_PREFIX, FREIGHT_PREFIX, rule_id)
    if not isinstance(document, dict) or set(document) != {"Rules"} or not isinstance(
            document["Rules"], list):
        raise DeploymentEvidenceError("lifecycle evidence must contain exactly Rules")
    matches = [rule for rule in document["Rules"]
               if isinstance(rule, dict) and rule.get("ID") == rule_id]
    if len(matches) != 1:
        raise DeploymentEvidenceError("expected exactly one named lifecycle rule")
    target = matches[0]
    if target.get("Status") != "Enabled":
        raise DeploymentEvidenceError("replay lifecycle rule is not enabled")
    prefix, tags = _filter(target)
    if prefix != input_prefix or tags != {"replay": "consumed"}:
        raise DeploymentEvidenceError("replay lifecycle filter is not exact")
    allowed_keys = {"ID", "Status", "Filter", "Transitions"}
    if set(target) != allowed_keys:
        raise DeploymentEvidenceError("replay lifecycle rule has extra actions/fields")
    if target.get("Transitions") != [{"Days": 7, "StorageClass": "GLACIER_IR"}]:
        raise DeploymentEvidenceError("replay lifecycle transition is not exact")

    for rule in document["Rules"]:
        if rule is target or not isinstance(rule, dict) or rule.get("Status") != "Enabled":
            continue
        other_prefix, other_tags = _filter(rule)
        destructive = any(key in rule for key in (
            "Transitions", "Expiration", "NoncurrentVersionTransitions",
            "NoncurrentVersionExpiration"))
        if (destructive and _prefixes_overlap(other_prefix, input_prefix) and
                other_tags.get("replay") != "consumed"):
            raise DeploymentEvidenceError(
                f"enabled lifecycle rule {rule.get('ID')!r} can affect unconsumed H1 inputs")
    return len(document["Rules"])


def validate_bootstrap_realization(manifest: object, bootstrap: str) -> int:
    """Statically admit only the reviewed combined-overlay bootstrap shape."""
    if not isinstance(manifest, dict):
        raise DeploymentEvidenceError("replay manifest draft must be an object")
    if manifest.get("commands", {}).get("compile") != PRODUCTION_COMPILE_COMMAND:
        raise DeploymentEvidenceError("manifest compile command is not exact direct offline Lean")
    if manifest.get("environment_allowlist") != ["HOME", "LEAN_PATH"]:
        raise DeploymentEvidenceError("manifest environment allowlist is not exact")
    if "overlay_sha256" in manifest:
        raise DeploymentEvidenceError("manifest uses ambiguous legacy overlay identity")
    hashes: dict[str, str] = {}
    for field in OVERLAY_HASH_VARIABLES:
        value = manifest.get(field)
        if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
            raise DeploymentEvidenceError(f"manifest.{field} is not a lowercase SHA-256")
        hashes[field] = value
    image_digest = manifest.get("worker_image_digest")
    if (not isinstance(image_digest, str) or re.fullmatch(
            r"[^@\s]+@sha256:[0-9a-f]{64}", image_digest) is None):
        raise DeploymentEvidenceError(
            "manifest.worker_image_digest is not a named repository digest")
    image_config_id = "sha256:" + image_digest.rsplit("@sha256:", 1)[1]
    active_bootstrap = "\n".join(
        line for line in bootstrap.splitlines()
        if not line.lstrip().startswith("#")
    )

    forbidden = (
        "overlay-oleans", "proofs/.lake/build/lib/lean",
        "/root/.elan/bin/lake", " lake env lean",
    )
    for token in forbidden:
        if token in bootstrap:
            raise DeploymentEvidenceError(f"bootstrap retains forbidden legacy token {token!r}")
    if re.search(
        r"complete-overlay\.tar\.zst[\s\S]{0,256}tar\s+-C\s+\"\$ROOT/repo(?:/|\")",
        active_bootstrap,
    ) is not None or re.search(
        r"overlay-publication/overlay[^\n]*(?:repo/proofs|\$ROOT/repo)",
        active_bootstrap,
    ) is not None:
        raise DeploymentEvidenceError(
            "combined overlay may not be extracted or moved into the repository")
    for name in OVERLAY_OBJECTS:
        if active_bootstrap.count(name) < 2:
            raise DeploymentEvidenceError(
                f"bootstrap does not download and verify exact object {name}")
    normalized = " ".join(active_bootstrap.split())
    bootstrap_safety = (
        f"APT_MIRROR_SOURCE={APT_MIRROR_SOURCE}",
        f"APT_MIRROR_TARGET={APT_MIRROR_TARGET}",
        f"APT_RETRIES={APT_RETRIES}",
        f"export AWS_RETRY_MODE={AWS_RETRY_MODE}",
        f"export AWS_MAX_ATTEMPTS={AWS_MAX_ATTEMPTS}",
        'sed -i "s|$APT_MIRROR_SOURCE|$APT_MIRROR_TARGET|g" '
        "/etc/apt/sources.list.d/ubuntu.sources",
        'apt-get -o Acquire::Retries="$APT_RETRIES" update',
        'apt-get -o Acquire::Retries="$APT_RETRIES" install',
        f"IMAGE_DIGEST={image_digest}",
        f"IMAGE_CONFIG_ID={image_config_id}",
        "LOADED_CONFIG_ID=$(docker image inspect lean4-arm64:v4.31.0 --format '{{.Id}}')",
        'test "$LOADED_CONFIG_ID" = "$IMAGE_CONFIG_ID"',
        "assert manifest['worker_image_digest'] == sys.argv[8]",
    )
    for fragment in bootstrap_safety:
        if fragment not in active_bootstrap:
            raise DeploymentEvidenceError(
                f"bootstrap omits launch-safety contract {fragment!r}")
    if re.search(
        r"python3\s+-\s+\"\$ROOT/manifest\.json\"[^\n]*\s+\"\$IMAGE_DIGEST\"\s+<<'PY'",
        active_bootstrap,
    ) is None:
        raise DeploymentEvidenceError(
            "bootstrap manifest readback omits repository digest argument")
    exact_download = (
        f"for name in {' '.join(OVERLAY_OBJECTS)}; do "
        "/usr/local/bin/aws s3api get-object --bucket \"$BUCKET\" "
        "--key \"$PREFIX/freight/p1/$name\" \"$ROOT/freight/$name\" "
        "--output json done"
    )
    if exact_download not in normalized:
        raise DeploymentEvidenceError(
            "bootstrap combined-overlay download loop/mapping is not exact")
    safety_order = (
        ("APT_MIRROR_SOURCE=", 'sed -i "s|$APT_MIRROR_SOURCE|'),
        ('sed -i "s|$APT_MIRROR_SOURCE|',
         'apt-get -o Acquire::Retries="$APT_RETRIES" update'),
        ('apt-get -o Acquire::Retries="$APT_RETRIES" update',
         'apt-get -o Acquire::Retries="$APT_RETRIES" install'),
        (f"export AWS_MAX_ATTEMPTS={AWS_MAX_ATTEMPTS}",
         "/usr/local/bin/aws s3api"),
        ("docker load", "LOADED_CONFIG_ID=$(docker image inspect lean4-arm64:v4.31.0"),
        (f"IMAGE_CONFIG_ID={image_config_id}",
         "LOADED_CONFIG_ID=$(docker image inspect lean4-arm64:v4.31.0"),
    )
    for earlier, later in safety_order:
        if (earlier not in active_bootstrap or later not in active_bootstrap
                or active_bootstrap.index(earlier) >= active_bootstrap.index(later)):
            raise DeploymentEvidenceError(
                f"bootstrap launch-safety ordering is invalid: {earlier!r} before {later!r}")
    image_loads = re.findall(
        r'(?m)^zstd -dc "\$ROOT/freight/[^"\n]+\.docker\.tar\.zst" \| docker load$',
        active_bootstrap,
    )
    if len(image_loads) != 1:
        raise DeploymentEvidenceError(
            "bootstrap must load exactly one pinned Docker-save freight archive")
    for index, (field, variable) in enumerate(OVERLAY_HASH_VARIABLES.items(), 2):
        assignment = re.compile(
            rf"(?m)^{re.escape(variable)}={re.escape(hashes[field])}$")
        if assignment.search(active_bootstrap) is None:
            raise DeploymentEvidenceError(
                f"bootstrap {variable} does not equal manifest.{field}")
        if active_bootstrap.count(variable) < 2:
            raise DeploymentEvidenceError(f"bootstrap never verifies {variable}")
        if f"assert manifest['{field}'] == sys.argv[{index}]" not in active_bootstrap:
            raise DeploymentEvidenceError(
                f"bootstrap manifest readback omits {field}")

    invocation = r"python3\s+-\s+\"\$ROOT/manifest\.json\""
    for variable in OVERLAY_HASH_VARIABLES.values():
        invocation += rf"\s+\"\${re.escape(variable)}\""
    invocation += r"\s+\"\$IMAGE_DIGEST\""
    invocation += r"\s+<<'PY'"
    if re.search(invocation, active_bootstrap) is None:
        raise DeploymentEvidenceError(
            "bootstrap manifest readback argument order is not exact")
    for assertion in OVERLAY_CROSSLINK_ASSERTIONS:
        if assertion not in active_bootstrap:
            raise DeploymentEvidenceError(
                f"bootstrap omits overlay receipt crosslink {assertion!r}")
    for variable, target in OVERLAY_HASH_TARGETS.items():
        if f'"${variable}" "{target}"' not in active_bootstrap:
            raise DeploymentEvidenceError(
                f"bootstrap hash verification target for {variable} is not exact")

    required = (
        'mkdir -p "$ROOT/overlay-publication"',
        'tar -C "$ROOT/overlay-publication" -xf -',
        '/usr/bin/python3 "$ROOT/repo/h1fleet/build_replay_overlay.py" --verify '
        '"$ROOT/overlay-publication"',
        'mv "$ROOT/overlay-publication/overlay" "$ROOT/overlay"',
        "export LEAN_PATH=/opt/replay/overlay",
        'test "$LEAN_PATH" = /opt/replay/overlay',
        "sha256sum -c -",
        'cmp -s "$ROOT/overlay-publication/manifest.json" '
        '"$ROOT/freight/complete-overlay-manifest.json"',
        'cmp -s "$ROOT/overlay-publication/receipt.json" '
        '"$ROOT/freight/complete-overlay-receipt.json"',
        "import json, sys",
        "manifest = json.load(open(sys.argv[1]))",
        "receipt = json.load(open('/opt/replay/freight/complete-overlay-receipt.json'))",
        "overlay = json.load(open('/opt/replay/freight/complete-overlay-manifest.json'))",
        "mkdir -p /etc/systemd/system/erdos85-replay.service.d",
        "cat > /etc/systemd/system/erdos85-replay.service.d/environment.conf <<'EOF'",
        "[Service]",
        "Environment=HOME=/root",
        "Environment=LEAN_PATH=/opt/replay/overlay",
        "systemctl daemon-reload",
        "systemctl start erdos85-replay.service",
        'test "$(systemctl show erdos85-replay.service --property Environment --value)" '
        '= "HOME=/root LEAN_PATH=/opt/replay/overlay"',
        'test ! -e "$ROOT/repo/proofs/.lake/packages"',
    )
    for fragment in required:
        if fragment not in active_bootstrap:
            raise DeploymentEvidenceError(
                f"bootstrap lacks required realization fragment {fragment!r}")
    service_start = "systemctl start erdos85-replay.service"
    for image_check in (
        "LOADED_CONFIG_ID=$(docker image inspect lean4-arm64:v4.31.0",
        'test "$LOADED_CONFIG_ID" = "$IMAGE_CONFIG_ID"',
    ):
        if active_bootstrap.index(image_check) >= active_bootstrap.index(service_start):
            raise DeploymentEvidenceError(
                "bootstrap launch-safety ordering requires image verification before service start")
    for exact_line, label in (
        ("ROOT=/opt/replay", "root"),
        ("export LEAN_PATH=/opt/replay/overlay", "ambient LEAN_PATH"),
        ('test "$LEAN_PATH" = /opt/replay/overlay', "LEAN_PATH assertion"),
    ):
        if re.search(rf"(?m)^{re.escape(exact_line)}$", active_bootstrap) is None:
            raise DeploymentEvidenceError(f"bootstrap {label} line is not exact")
    service_sequence = (
        "systemctl daemon-reload systemctl start erdos85-replay.service "
        'test "$(systemctl show erdos85-replay.service --property Environment --value)" '
        '= "HOME=/root LEAN_PATH=/opt/replay/overlay"'
    )
    if service_sequence not in normalized:
        raise DeploymentEvidenceError(
            "bootstrap service daemon-reload/start/environment-check ordering is not exact")
    package_assertion = 'test ! -e "$ROOT/repo/proofs/.lake/packages"'
    if active_bootstrap.count(".lake/packages") != 1 or re.search(
            rf"(?m)^{re.escape(package_assertion)}$", active_bootstrap) is None:
        raise DeploymentEvidenceError(
            "bootstrap package-cache absence assertion is not exact")
    return (len(OVERLAY_HASH_VARIABLES) + len(OVERLAY_OBJECTS) + len(required)
            + len(OVERLAY_CROSSLINK_ASSERTIONS) + len(OVERLAY_HASH_TARGETS)
            + len(bootstrap_safety) + 8)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--iam-simulation", type=Path, required=True)
    parser.add_argument("--lifecycle", type=Path, required=True)
    parser.add_argument("--bucket", required=True)
    parser.add_argument("--input-prefix", required=True)
    parser.add_argument("--output-prefix", required=True)
    parser.add_argument("--freight-prefix", required=True)
    parser.add_argument("--lifecycle-rule-id", required=True)
    parser.add_argument("--manifest-draft", type=Path, required=True)
    parser.add_argument("--bootstrap", type=Path, required=True)
    args = parser.parse_args()
    try:
        identity = validate_identity(
            args.bucket, args.input_prefix, args.output_prefix,
            args.freight_prefix, args.lifecycle_rule_id)
        checks = validate_iam(_load(args.iam_simulation), args.bucket,
                              args.input_prefix, args.output_prefix,
                              args.freight_prefix)
        rules = validate_lifecycle(_load(args.lifecycle), args.input_prefix,
                                   args.lifecycle_rule_id)
        bootstrap_checks = validate_bootstrap_realization(
            _load(args.manifest_draft), args.bootstrap.read_text())
    except (OSError, DeploymentEvidenceError) as exc:
        parser.error(str(exc))
    iam_sha, lifecycle_sha, manifest_sha, bootstrap_sha, identity_sha = evidence_hashes(
        args.iam_simulation, args.lifecycle, args.manifest_draft, args.bootstrap, identity)
    print(f"CANDIDATE_PASS {APPROVAL_NOTICE} "
          f"evidence_scope=sentinel-actions+lifecycle "
          f"iam_checks={checks} lifecycle_rules={rules} "
          f"bootstrap_checks={bootstrap_checks} "
          f"iam_sha256={iam_sha} lifecycle_sha256={lifecycle_sha} "
          f"manifest_draft_sha256={manifest_sha} bootstrap_sha256={bootstrap_sha} "
          f"deployment_identity_sha256={identity_sha}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
