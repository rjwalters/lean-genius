#!/usr/bin/env python3
"""Reproduce the reviewed pilot bootstrap's Docker identity/logging repair.

Input is the immutable #1357 bootstrap, shipped alongside this generator.
Output is create-only and must receive its own freight review before use.
This command only writes local files; it never uploads or launches workers.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path


BASE_SHA = "f48a6c4222ca9cf517b6a2a969fbddfeb64cb96fa58901dfe02435fb49b025c3"
BASE_RECEIPT_SHA = "387849c5685838f674d037d9e9040a4628a4e125906b6880153af2f67dece472"
DEFAULT_SOURCE = Path(__file__).with_name("pilot-bootstrap-reviewed-v3.sh")


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"expected exactly one reviewed block: {old[:70]!r}")
    return text.replace(old, new, 1)


def render(source: bytes) -> bytes:
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
    if "LOADED_CONFIG_ID" in text:
        raise ValueError("ambiguous legacy loaded-config field remains")
    return text.encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = render(args.source.read_bytes())
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
        "freight_review_required": True,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
