#!/usr/bin/env python3
"""Reproduce the pilot bootstrap's identity, logging and replay-env repairs.

Input is the immutable #1357 bootstrap, shipped alongside this generator.
Output is create-only and must receive its own freight review before use.
This command only writes local files; it never uploads or launches workers.
"""

import argparse
import hashlib
import json
import os
import re
from pathlib import Path


BASE_SHA = "f48a6c4222ca9cf517b6a2a969fbddfeb64cb96fa58901dfe02435fb49b025c3"
BASE_RECEIPT_SHA = "387849c5685838f674d037d9e9040a4628a4e125906b6880153af2f67dece472"
DEFAULT_SOURCE = Path(__file__).with_name("pilot-bootstrap-reviewed-v3.sh")
REFREEZE_HASHES = {
    "repo_archive_sha256": "REPO_SHA",
    "overlay_archive_sha256": "OVERLAY_SHA",
    "manifest_sha256": "MANIFEST_SHA",
    "overlay_manifest_sha256": "OVERLAY_MANIFEST_SHA",
    "overlay_receipt_sha256": "OVERLAY_RECEIPT_SHA",
    "overlay_identity_sha256": "OVERLAY_IDENTITY_SHA",
}


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"expected exactly one reviewed block: {old[:70]!r}")
    return text.replace(old, new, 1)


def apply_refreeze(text: str, pins: dict) -> str:
    fields = set(REFREEZE_HASHES) | {
        "schema", "freight_prefix", "repository_commit", "repo_archive", "overlay_archive"}
    if not isinstance(pins, dict) or set(pins) != fields:
        raise ValueError("refreeze fields must match the complete schema")
    if pins["schema"] != "erdos85-pilot-bootstrap-refreeze-v1":
        raise ValueError("unsupported refreeze schema")
    patterns = {field: r"[0-9a-f]{64}" for field in REFREEZE_HASHES}
    patterns.update(repository_commit=r"[0-9a-f]{40}",
                    freight_prefix=r"[A-Za-z0-9_-]+(?:/[A-Za-z0-9_-]+)+",
                    repo_archive=r"[A-Za-z0-9][A-Za-z0-9_-]*\.tar\.zst",
                    overlay_archive=r"[A-Za-z0-9][A-Za-z0-9_-]*\.tar\.zst")
    for field, pattern in patterns.items():
        if not isinstance(pins[field], str) or not re.fullmatch(pattern, pins[field]):
            raise ValueError(f"invalid refreeze {field}")
    if pins["repo_archive"] == pins["overlay_archive"]:
        raise ValueError("repo and overlay archive names must differ")
    for field, variable in REFREEZE_HASHES.items():
        old = re.findall(rf"^{variable}=([0-9a-f]{{64}})$", text, re.MULTILINE)
        if len(old) != 1:
            raise ValueError(f"missing reviewed {variable} pin")
        text = replace_once(text, f"{variable}={old[0]}\n", f"{variable}={pins[field]}\n")
        if variable == "OVERLAY_SHA":
            text = replace_once(text,
                                f'assert manifest["overlay_archive_sha256"] == "{old[0]}"',
                                f'assert manifest["overlay_archive_sha256"] == "{pins[field]}"')
    text = replace_once(text, 'FREIGHT_PREFIX="$PREFIX/freight/pilot-4c7cbb5159"',
                        f'FREIGHT_PREFIX="{pins["freight_prefix"]}"')
    text = replace_once(text,
                        'assert manifest["repository_commit"] == "4c7cbb515934254e0795916001617150587559f5"',
                        f'assert manifest["repository_commit"] == "{pins["repository_commit"]}"')
    for field, old, count in (
        ("repo_archive", "repo-4c7cbb5159.tar.zst", 3),
        ("overlay_archive", "complete-overlay-4c7cbb5159-import-data.tar.zst", 4),
    ):
        if text.count(old) != count:
            raise ValueError(f"unexpected reviewed {field} references")
        text = text.replace(old, pins[field])
    return text


def render(source: bytes, *, full_tool_identities: bool = False,
           refreeze: dict | None = None) -> bytes:
    if hashlib.sha256(source).hexdigest() != BASE_SHA:
        raise ValueError("reviewed bootstrap SHA mismatch")
    text = source.decode("utf-8")
    text = replace_once(text, "INSTANCE_ID=unknown\n", """INSTANCE_ID=unknown
LOG_TEE_PID=
# Preserve the original streams so the EXIT trap can drain tee before upload.
exec 3>&1 4>&2
""")
    text = replace_once(text,
                        "  if test \"$INSTANCE_ID\" != unknown && test -x /usr/local/bin/aws; then\n",
                        """  printf 'bootstrap terminal phase=%s returncode=%s\\n' "$PHASE" "$rc"
  exec 1>&3 2>&4
  if test -n "$LOG_TEE_PID"; then
    wait "$LOG_TEE_PID" || true
  fi
  if test "$INSTANCE_ID" != unknown && test -x /usr/local/bin/aws; then
    if test -f /var/log/erdos85-replay-bootstrap.log; then
      /usr/local/bin/aws s3api put-object --bucket "$BUCKET" \\
        --key "$PREFIX/bootstrap-terminal/$INSTANCE_ID.log" \\
        --body /var/log/erdos85-replay-bootstrap.log \\
        --if-none-match '*' --output json || true
    fi
""")
    text = replace_once(text,
                        "exec > >(tee -a /var/log/erdos85-replay-bootstrap.log) 2>&1\n",
                        "exec > >(tee -a /var/log/erdos85-replay-bootstrap.log) 2>&1\nLOG_TEE_PID=$!\n")
    text = replace_once(text,
                        "LOADED_CONFIG_ID=$(docker image inspect lean4-arm64:v4.31.0 --format '{{.Id}}')\n"
                        'test "$LOADED_CONFIG_ID" = "$IMAGE_CONFIG_ID"\n',
                        """LOADED_IMAGE_ID=$(docker image inspect lean4-arm64:v4.31.0 --format '{{.Id}}')
case "$LOADED_IMAGE_ID" in
  "$IMAGE_CONFIG_ID") LOADED_IMAGE_ID_KIND=config ;;
  "${IMAGE_OCI_DIGEST#*@}") LOADED_IMAGE_ID_KIND=oci ;;
  *) printf 'unreviewed loaded image identity: %s\\n' "$LOADED_IMAGE_ID" >&2; exit 1 ;;
esac
printf 'loaded image identity kind=%s id=%s\\n' "$LOADED_IMAGE_ID_KIND" "$LOADED_IMAGE_ID"
""")
    text = replace_once(text,
                        '  "$LOADED_CONFIG_ID" "$IMAGE_OCI_DIGEST" "$LOADED_ROOTFS"',
                        '  "$IMAGE_CONFIG_ID" "$IMAGE_OCI_DIGEST" "$LOADED_ROOTFS"')
    text = replace_once(text,
                        '  --arg image_config_id "$LOADED_CONFIG_ID" --arg image_oci_digest "$IMAGE_OCI_DIGEST" \\\n',
                        '  --arg image_config_id "$IMAGE_CONFIG_ID" --arg image_oci_digest "$IMAGE_OCI_DIGEST" \\\n'
                        '  --arg loaded_image_id "$LOADED_IMAGE_ID" --arg loaded_image_id_kind "$LOADED_IMAGE_ID_KIND" \\\n')
    text = replace_once(text, 'schema:"erdos85-h1-replay-bootstrap-identity-v2"',
                        'schema:"erdos85-h1-replay-bootstrap-identity-v3"')
    text = replace_once(text, '    image_config_id:$image_config_id,\n',
                        '    image_config_id:$image_config_id,\n'
                        '    loaded_image_id:$loaded_image_id,loaded_image_id_kind:$loaded_image_id_kind,\n')
    text = replace_once(text, 'PHASE=running-dispatcher\n',
                        'PHASE=running-dispatcher\n'
                        '# The production worker validates this inherited environment.\n'
                        'export LEAN_PATH="$ROOT/overlay"\n')
    if full_tool_identities:
        text = replace_once(text,
                            '  "$IMAGE_OCI_DIGEST" <<\'PY\'\n',
                            '  "$IMAGE_OCI_DIGEST" "$DOCKER_ID" "$PYTHON_ID" <<\'PY\'\n')
        text = replace_once(text,
                            'assert manifest["zstd_identity"] == sys.argv[3]\n',
                            'assert manifest["zstd_identity"] == sys.argv[3]\n'
                            'assert manifest["docker_identity"] == sys.argv[5]\n'
                            'assert manifest["python_identity"] == sys.argv[6]\n')
    if "LOADED_CONFIG_ID" in text:
        raise ValueError("ambiguous legacy loaded-config field remains")
    if refreeze is not None:
        if not full_tool_identities:
            raise ValueError("refreeze requires full tool identity checks")
        text = apply_refreeze(text, refreeze)
    return text.encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--full-tool-identities", action="store_true",
                        help="require exact Docker/Python pins in the new manifest")
    parser.add_argument("--refreeze", type=Path,
                        help="complete reviewed JSON pin set; requires --full-tool-identities")
    args = parser.parse_args()
    refreeze_bytes = args.refreeze.read_bytes() if args.refreeze else None
    refreeze = json.loads(refreeze_bytes) if refreeze_bytes is not None else None
    if refreeze_bytes is not None and not isinstance(refreeze, dict):
        raise ValueError("refreeze input must be a JSON object")
    output = render(args.source.read_bytes(), full_tool_identities=args.full_tool_identities,
                    refreeze=refreeze)
    # Exclusive creation protects previously reviewed or uploaded artifacts.
    with args.output.open("xb") as stream:
        stream.write(output)
        stream.flush()
        os.fsync(stream.fileno())
    print(json.dumps({
        "schema": "erdos85-pilot-bootstrap-compat-build-v1",
        "source_sha256": BASE_SHA,
        "prior_freight_receipt_sha256": BASE_RECEIPT_SHA,
        "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "output_path": str(args.output.resolve()),
        "output_sha256": hashlib.sha256(output).hexdigest(),
        "output_bytes": len(output),
        "full_tool_identities": args.full_tool_identities,
        "refreeze_sha256": (hashlib.sha256(refreeze_bytes).hexdigest()
                            if refreeze_bytes is not None else None),
        "freight_review_required": True,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
