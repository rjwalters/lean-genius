#!/usr/bin/env python3
"""Validate offline IAM-simulation and S3-lifecycle evidence for H1 replay.

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


def evidence_hashes(iam_path: Path, lifecycle_path: Path,
                    identity: dict[str, str]) -> tuple[str, str, str]:
    return (
        hashlib.sha256(iam_path.read_bytes()).hexdigest(),
        hashlib.sha256(lifecycle_path.read_bytes()).hexdigest(),
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--iam-simulation", type=Path, required=True)
    parser.add_argument("--lifecycle", type=Path, required=True)
    parser.add_argument("--bucket", required=True)
    parser.add_argument("--input-prefix", required=True)
    parser.add_argument("--output-prefix", required=True)
    parser.add_argument("--freight-prefix", required=True)
    parser.add_argument("--lifecycle-rule-id", required=True)
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
    except (OSError, DeploymentEvidenceError) as exc:
        parser.error(str(exc))
    iam_sha, lifecycle_sha, identity_sha = evidence_hashes(
        args.iam_simulation, args.lifecycle, identity)
    print(f"CANDIDATE_PASS {APPROVAL_NOTICE} "
          f"evidence_scope=sentinel-actions+lifecycle "
          f"iam_checks={checks} lifecycle_rules={rules} "
          f"iam_sha256={iam_sha} lifecycle_sha256={lifecycle_sha} "
          f"deployment_identity_sha256={identity_sha}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
